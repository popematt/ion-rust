//! Path filter AST and compiled FSM for selective value extraction.
//!
//! A `PathQuery` describes a path from the document root down to a target
//! value. Multiple queries are compiled into a `FilterFsm` (a trie-shaped
//! finite state machine) that enables O(1) per-value matching decisions during
//! bytecode generation.
//!
//! The v2 AST separates navigation (`Select`) from filtering (`Predicate`),
//! following the same principle as JSONPath, XPath, and jq.

use std::collections::HashMap;
use std::fmt;

use crate::IonType;

// ─── Public AST types ─────────────────────────────────────────────────

/// A compiled set of path queries ready for execution.
///
/// Created by `PathQuerySet::compile(queries, flatten)` which validates
/// the queries and builds the FSM. Returns an error if any query is
/// invalid.
#[derive(Clone, Debug)]
pub struct PathQuerySet {
    queries: Vec<PathQuery>,
    /// If true, intermediate struct containers along the path are
    /// collapsed -- terminal values are placed directly into the
    /// outermost struct. Only struct navigation is flattened; sequences
    /// cannot be flattened.
    pub(crate) flatten: bool,
}

/// A complete path query: a sequence of steps from the top level down
/// to the target value.
///
/// Steps are consumed left-to-right:
/// - `Step::Select` advances depth (navigates into a child).
/// - `Step::Match` gates the current position without advancing depth.
///   If the predicate fails, the value is skipped.
/// - `Step::NotMatch` gates with negation. If the predicate passes,
///   the value is skipped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PathQuery {
    steps: Vec<Step>,
}

/// A single step in a path query.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Step {
    /// Navigate into a child value (advances depth).
    Select(Select),
    /// Filter: the predicate must be satisfied to proceed.
    /// If it fails, the value (and its subtree) is skipped.
    Match(Predicate),
    /// Negated filter: the predicate must NOT be satisfied.
    /// If it passes, the value is skipped.
    NotMatch(Predicate),
}

/// A navigation/descent step. Each Select consumes one level of depth
/// when matched.
///
/// Selects implicitly constrain the container type:
/// - `Field` and `AnyField` imply the current container is a struct.
/// - `Index` and `AnyIndex` imply the current container is a sequence
///   (list or sexp).
/// - `Any` matches regardless of container type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Select {
    /// Descend into a struct field by name (exact text match,
    /// case-sensitive). Implies the current container is a struct.
    Field(String),

    /// Descend into a sequence element by zero-based index. Implies
    /// the current container is a sequence (list or sexp).
    Index(usize),

    /// Descend into any struct field (wildcard in struct context).
    /// Implies the current container is a struct.
    AnyField,

    /// Descend into any sequence element (wildcard in sequence
    /// context). Implies the current container is a sequence.
    AnyIndex,

    /// Descend into any child value regardless of container type.
    /// Matches fields in structs, elements in lists/sexps.
    Any,
}

/// A predicate that filters the current value without advancing depth.
///
/// All predicates are O(1) -- type descriptor byte or annotation
/// wrapper (already parsed when processing annotated values).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Predicate {
    /// Accept only values of the specified Ion type.
    Type(IonType),

    /// Accept only values that carry the specified annotation (exact
    /// text match, case-sensitive).
    HasAnnotation(String),

    /// Accept only values that have at least one annotation.
    IsAnnotated,

    /// Matches typed nulls (e.g., `null.int`, `null.string`). O(1) --
    /// encoded in the type descriptor.
    IsNull,
}

// ─── Error type ───────────────────────────────────────────────────────

/// Errors produced during path query validation/compilation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PathQueryError {
    /// A Select step follows a Match(Type(T)) predicate where T is a
    /// scalar type. Scalars cannot have children.
    SelectAfterScalarType { scalar_type: IonType },
    /// A Select step is incompatible with a preceding type predicate.
    /// E.g., `Match(Type(List))` followed by `Select(Field(...))`.
    ContainerTypeMismatch {
        constrained_type: IonType,
        select: Select,
    },
}

impl fmt::Display for PathQueryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SelectAfterScalarType { scalar_type } => {
                write!(
                    f,
                    "Select step after scalar type predicate \
                     (Type({scalar_type})) is unreachable"
                )
            }
            Self::ContainerTypeMismatch {
                constrained_type,
                select,
            } => {
                write!(
                    f,
                    "Select step {select:?} is incompatible with \
                     preceding type predicate Type({constrained_type})"
                )
            }
        }
    }
}

impl std::error::Error for PathQueryError {}

// ─── Convenience constructors ─────────────────────────────────────────

impl PathQuery {
    /// Full constructor.
    pub fn new(steps: Vec<Step>) -> Self {
        Self { steps }
    }

    /// Single field selection (most common case).
    pub fn field(name: impl Into<String>) -> Self {
        Self::new(vec![Step::Select(Select::Field(name.into()))])
    }

    /// Nested field path.
    pub fn fields(names: &[&str]) -> Self {
        Self::new(
            names
                .iter()
                .map(|n| Step::Select(Select::Field((*n).to_owned())))
                .collect(),
        )
    }

    /// Match all top-level values.
    pub fn all() -> Self {
        Self::new(vec![])
    }

    pub fn steps(&self) -> &[Step] {
        &self.steps
    }
}

impl PathQuerySet {
    /// Compile a set of queries into an executable FSM. Returns an
    /// error if any query is invalid.
    pub fn compile(queries: Vec<PathQuery>, flatten: bool) -> Result<Self, PathQueryError> {
        // Validate each query
        for query in &queries {
            validate_query(query)?;
        }
        Ok(Self { queries, flatten })
    }

    pub fn queries(&self) -> &[PathQuery] {
        &self.queries
    }

    pub fn flatten(&self) -> bool {
        self.flatten
    }
}

/// Validate a single path query for semantic correctness.
fn validate_query(query: &PathQuery) -> Result<(), PathQueryError> {
    // Track the most recent type constraint from Match(Type(T))
    let mut constrained_type: Option<IonType> = None;

    for step in &query.steps {
        match step {
            Step::Select(select) => {
                if let Some(ct) = constrained_type {
                    if is_scalar_type(ct) {
                        return Err(PathQueryError::SelectAfterScalarType { scalar_type: ct });
                    }
                    // Check container-type mismatch
                    if !is_select_compatible_with_container(select, ct) {
                        return Err(PathQueryError::ContainerTypeMismatch {
                            constrained_type: ct,
                            select: select.clone(),
                        });
                    }
                }
                // Select resets the constraint (we've navigated deeper)
                constrained_type = None;
            }
            Step::Match(Predicate::Type(ion_type)) => {
                constrained_type = Some(*ion_type);
            }
            Step::Match(_) => {
                // Non-type predicates don't constrain navigation
            }
            Step::NotMatch(_) => {
                // NotMatch never constrains subsequent steps
            }
        }
    }
    Ok(())
}

fn is_scalar_type(t: IonType) -> bool {
    matches!(
        t,
        IonType::Bool
            | IonType::Int
            | IonType::Float
            | IonType::Decimal
            | IonType::Timestamp
            | IonType::Symbol
            | IonType::String
            | IonType::Blob
            | IonType::Clob
            | IonType::Null
    )
}

fn is_select_compatible_with_container(select: &Select, container_type: IonType) -> bool {
    match select {
        Select::Any => true, // always valid
        Select::Field(_) | Select::AnyField => container_type == IonType::Struct,
        Select::Index(_) | Select::AnyIndex => {
            container_type == IonType::List || container_type == IonType::SExp
        }
    }
}

// ─── Compiled FSM ─────────────────────────────────────────────────────

/// A node in the compiled filter trie.
#[derive(Debug)]
struct FsmNode {
    /// If true, values reaching this node are "matched" and their
    /// bytecode should be emitted in full.
    is_terminal: bool,
    /// Predicates to check at this node. Each entry is (predicate,
    /// negated). All must pass.
    predicates: Vec<(Predicate, bool)>,
    /// Transition on struct field name (text).
    field_children: HashMap<String, usize>,
    /// Transition on SID.
    sid_children: HashMap<usize, usize>,
    /// Transition on sequence index.
    index_children: HashMap<usize, usize>,
    /// Wildcard field transition (matches any struct field).
    wildcard_field_child: Option<usize>,
    /// Wildcard index transition (matches any sequence element).
    wildcard_index_child: Option<usize>,
}

impl FsmNode {
    fn new() -> Self {
        Self {
            is_terminal: false,
            predicates: Vec::new(),
            field_children: HashMap::new(),
            sid_children: HashMap::new(),
            index_children: HashMap::new(),
            wildcard_field_child: None,
            wildcard_index_child: None,
        }
    }

    fn has_transitions(&self) -> bool {
        !self.field_children.is_empty()
            || !self.sid_children.is_empty()
            || !self.index_children.is_empty()
            || self.wildcard_field_child.is_some()
            || self.wildcard_index_child.is_some()
    }
}

/// The compiled FSM for a set of path queries.
#[derive(Debug)]
pub(crate) struct FilterFsm {
    /// Arena of FSM nodes. Index 0 is the root.
    nodes: Vec<FsmNode>,
}

impl FilterFsm {
    /// Compile a set of path queries into an FSM.
    pub fn compile(queries: &[PathQuery]) -> Self {
        let mut fsm = Self {
            nodes: vec![FsmNode::new()],
        };

        for query in queries {
            let mut current = 0;
            // Collect predicates that appear before the first Select or
            // trailing after the last Select.
            let mut pending_predicates: Vec<(Predicate, bool)> = Vec::new();

            for step in query.steps() {
                match step {
                    Step::Select(select) => {
                        // Attach pending predicates to the current node
                        // (leading/intermediate predicates gate this node).
                        if !pending_predicates.is_empty() {
                            fsm.nodes[current]
                                .predicates
                                .append(&mut pending_predicates);
                        }
                        current = fsm.get_or_create_child(current, select);
                    }
                    Step::Match(predicate) => {
                        pending_predicates.push((predicate.clone(), false));
                    }
                    Step::NotMatch(predicate) => {
                        pending_predicates.push((predicate.clone(), true));
                    }
                }
            }

            // Attach any trailing predicates to the terminal node.
            if !pending_predicates.is_empty() {
                fsm.nodes[current]
                    .predicates
                    .append(&mut pending_predicates);
            }

            // Mark the final node as terminal.
            fsm.nodes[current].is_terminal = true;
        }

        fsm
    }

    /// Gets or creates a child node for the given select step from the
    /// given parent node.
    fn get_or_create_child(&mut self, parent: usize, select: &Select) -> usize {
        match select {
            Select::Field(name) => {
                if let Some(&child) = self.nodes[parent].field_children.get(name) {
                    child
                } else {
                    let child_idx = self.nodes.len();
                    self.nodes.push(FsmNode::new());
                    self.nodes[parent]
                        .field_children
                        .insert(name.clone(), child_idx);
                    child_idx
                }
            }
            Select::Index(idx) => {
                if let Some(&child) = self.nodes[parent].index_children.get(idx) {
                    child
                } else {
                    let child_idx = self.nodes.len();
                    self.nodes.push(FsmNode::new());
                    self.nodes[parent].index_children.insert(*idx, child_idx);
                    child_idx
                }
            }
            Select::AnyField => {
                if let Some(child) = self.nodes[parent].wildcard_field_child {
                    child
                } else {
                    let child_idx = self.nodes.len();
                    self.nodes.push(FsmNode::new());
                    self.nodes[parent].wildcard_field_child = Some(child_idx);
                    child_idx
                }
            }
            Select::AnyIndex => {
                if let Some(child) = self.nodes[parent].wildcard_index_child {
                    child
                } else {
                    let child_idx = self.nodes.len();
                    self.nodes.push(FsmNode::new());
                    self.nodes[parent].wildcard_index_child = Some(child_idx);
                    child_idx
                }
            }
            Select::Any => {
                // Any populates both wildcard_field and wildcard_index
                // pointing to the same child node.
                if let Some(child) = self.nodes[parent].wildcard_field_child {
                    // Ensure wildcard_index also points to the same node
                    self.nodes[parent].wildcard_index_child = Some(child);
                    child
                } else if let Some(child) = self.nodes[parent].wildcard_index_child {
                    self.nodes[parent].wildcard_field_child = Some(child);
                    child
                } else {
                    let child_idx = self.nodes.len();
                    self.nodes.push(FsmNode::new());
                    self.nodes[parent].wildcard_field_child = Some(child_idx);
                    self.nodes[parent].wildcard_index_child = Some(child_idx);
                    child_idx
                }
            }
        }
    }

    /// From a given node, attempt to transition on a struct field name.
    /// Returns the child node index, or None.
    pub fn transition_field(&self, node: usize, field_name: &str) -> Option<usize> {
        let n = &self.nodes[node];
        if let Some(&child) = n.field_children.get(field_name) {
            return Some(child);
        }
        n.wildcard_field_child
    }

    /// Transition on a SID (for binary data where field names are
    /// encoded as symbol IDs).
    pub fn transition_sid(&self, node: usize, sid: usize) -> Option<usize> {
        let n = &self.nodes[node];
        if let Some(&child) = n.sid_children.get(&sid) {
            return Some(child);
        }
        n.wildcard_field_child
    }

    /// Transition on a sequence index.
    pub fn transition_index(&self, node: usize, index: usize) -> Option<usize> {
        let n = &self.nodes[node];
        if let Some(&child) = n.index_children.get(&index) {
            return Some(child);
        }
        n.wildcard_index_child
    }

    /// Whether the given node is a terminal (matched) state.
    pub fn is_terminal(&self, node: usize) -> bool {
        self.nodes[node].is_terminal
    }

    /// Whether the given node has any possible child transitions
    /// (i.e., we should step into the container).
    pub fn has_transitions(&self, node: usize) -> bool {
        self.nodes[node].has_transitions()
    }

    /// Returns the predicates for the given node.
    pub fn predicates(&self, node: usize) -> &[(Predicate, bool)] {
        &self.nodes[node].predicates
    }

    /// Whether the given node has field-based transitions (struct
    /// navigation). Used by flatten logic to determine if a child node
    /// navigates through a struct (flattenable) vs a sequence (not).
    pub fn has_field_transitions(&self, node: usize) -> bool {
        let n = &self.nodes[node];
        !n.field_children.is_empty() || n.wildcard_field_child.is_some()
    }
}

// ─── Deprecated v1 types (for backwards compatibility) ────────────────

/// A single step in a path filter.
#[deprecated(note = "Use `Step` and `Select` from the v2 API instead")]
#[allow(deprecated)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PathStep {
    /// Match a struct field by name.
    Field(FieldMatcher),
    /// Match an element at a specific ordinal position in a sequence
    /// (list or sexp). Zero-based.
    Index(usize),
    /// Match any field or index at this depth.
    Wildcard,
}

/// How to match a struct field name.
#[deprecated(note = "Use `Select::Field(String)` from the v2 API instead")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FieldMatcher {
    /// Match by UTF-8 field name text (exact, case-sensitive).
    Text(String),
    /// Match by symbol ID (for data with known symbol tables).
    Sid(usize),
}

/// A complete path filter: a sequence of steps from the top level down
/// to the target value.
///
/// Deprecated: Use `PathQuery` instead.
#[deprecated(note = "Use `PathQuery` from the v2 API instead")]
#[allow(deprecated)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PathFilter {
    steps: Vec<PathStep>,
}

#[allow(deprecated)]
impl PathFilter {
    pub fn new(steps: Vec<PathStep>) -> Self {
        Self { steps }
    }

    /// Convenience: single field name filter.
    pub fn field(name: impl Into<String>) -> Self {
        Self {
            steps: vec![PathStep::Field(FieldMatcher::Text(name.into()))],
        }
    }

    /// Convenience: nested field path.
    pub fn fields(names: &[&str]) -> Self {
        Self {
            steps: names
                .iter()
                .map(|n| PathStep::Field(FieldMatcher::Text((*n).to_owned())))
                .collect(),
        }
    }

    pub fn steps(&self) -> &[PathStep] {
        &self.steps
    }

    /// Convert this v1 PathFilter to a v2 PathQuery.
    pub fn to_query(&self) -> PathQuery {
        let steps = self
            .steps
            .iter()
            .map(|step| match step {
                PathStep::Field(FieldMatcher::Text(name)) => {
                    Step::Select(Select::Field(name.clone()))
                }
                PathStep::Field(FieldMatcher::Sid(_)) => {
                    // SID matching is internal; treat as Any for public API
                    Step::Select(Select::Any)
                }
                PathStep::Index(idx) => Step::Select(Select::Index(*idx)),
                PathStep::Wildcard => Step::Select(Select::Any),
            })
            .collect();
        PathQuery::new(steps)
    }
}

#[allow(deprecated)]
impl From<&str> for FieldMatcher {
    fn from(s: &str) -> Self {
        FieldMatcher::Text(s.to_owned())
    }
}

#[allow(deprecated)]
impl From<String> for FieldMatcher {
    fn from(s: String) -> Self {
        FieldMatcher::Text(s)
    }
}

// ─── Legacy FilterFsm::compile for v1 PathFilter ─────────────────────

impl FilterFsm {
    /// Compile a set of v1 path filters into an FSM (legacy API).
    #[allow(deprecated)]
    pub fn compile_legacy(filters: &[PathFilter]) -> Self {
        let queries: Vec<PathQuery> = filters.iter().map(|f| f.to_query()).collect();
        Self::compile(&queries)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_field_query_compiles() {
        let queries = [PathQuery::field("foo")];
        let fsm = FilterFsm::compile(&queries);

        // Root has a transition on "foo"
        let child = fsm.transition_field(0, "foo");
        assert!(child.is_some());
        let child = child.unwrap();
        assert!(fsm.is_terminal(child));

        // No transition on "bar"
        assert!(fsm.transition_field(0, "bar").is_none());
    }

    #[test]
    fn nested_field_query_compiles() {
        let queries = [PathQuery::fields(&["foo", "bar"])];
        let fsm = FilterFsm::compile(&queries);

        let first = fsm.transition_field(0, "foo").unwrap();
        assert!(!fsm.is_terminal(first));
        assert!(fsm.has_transitions(first));

        let second = fsm.transition_field(first, "bar").unwrap();
        assert!(fsm.is_terminal(second));
    }

    #[test]
    fn any_wildcard_compiles() {
        let queries = [PathQuery::new(vec![
            Step::Select(Select::Any),
            Step::Select(Select::Field("name".into())),
        ])];
        let fsm = FilterFsm::compile(&queries);

        // Any matches any field
        let first = fsm.transition_field(0, "anything").unwrap();
        assert!(!fsm.is_terminal(first));

        let second = fsm.transition_field(first, "name").unwrap();
        assert!(fsm.is_terminal(second));
    }

    #[test]
    fn any_field_wildcard_compiles() {
        let queries = [PathQuery::new(vec![
            Step::Select(Select::AnyField),
            Step::Select(Select::Field("name".into())),
        ])];
        let fsm = FilterFsm::compile(&queries);

        // AnyField matches struct fields
        let first = fsm.transition_field(0, "anything").unwrap();
        assert!(!fsm.is_terminal(first));

        // But does NOT match sequence indices
        assert!(fsm.transition_index(0, 0).is_none());

        let second = fsm.transition_field(first, "name").unwrap();
        assert!(fsm.is_terminal(second));
    }

    #[test]
    fn any_index_wildcard_compiles() {
        let queries = [PathQuery::new(vec![
            Step::Select(Select::Field("items".into())),
            Step::Select(Select::AnyIndex),
        ])];
        let fsm = FilterFsm::compile(&queries);

        let first = fsm.transition_field(0, "items").unwrap();
        assert!(!fsm.is_terminal(first));

        // AnyIndex matches any index
        let second = fsm.transition_index(first, 0).unwrap();
        assert!(fsm.is_terminal(second));
        let third = fsm.transition_index(first, 99).unwrap();
        assert!(fsm.is_terminal(third));
        assert_eq!(second, third); // same node

        // But does NOT match fields
        assert!(fsm.transition_field(first, "x").is_none());
    }

    #[test]
    fn index_query_compiles() {
        let queries = [PathQuery::new(vec![
            Step::Select(Select::Field("items".into())),
            Step::Select(Select::Index(0)),
        ])];
        let fsm = FilterFsm::compile(&queries);

        let first = fsm.transition_field(0, "items").unwrap();
        assert!(!fsm.is_terminal(first));

        let second = fsm.transition_index(first, 0).unwrap();
        assert!(fsm.is_terminal(second));

        // Index 1 should not match
        assert!(fsm.transition_index(first, 1).is_none());
    }

    #[test]
    fn multiple_queries_share_prefix() {
        let queries = [
            PathQuery::fields(&["a", "b"]),
            PathQuery::fields(&["a", "c"]),
        ];
        let fsm = FilterFsm::compile(&queries);

        let a = fsm.transition_field(0, "a").unwrap();
        assert!(!fsm.is_terminal(a));

        let b = fsm.transition_field(a, "b").unwrap();
        assert!(fsm.is_terminal(b));

        let c = fsm.transition_field(a, "c").unwrap();
        assert!(fsm.is_terminal(c));
    }

    #[test]
    fn root_has_no_transitions_when_empty() {
        let queries: [PathQuery; 0] = [];
        let fsm = FilterFsm::compile(&queries);

        assert!(!fsm.has_transitions(0));
        assert!(!fsm.is_terminal(0));
    }

    #[test]
    fn empty_steps_makes_root_terminal() {
        let queries = [PathQuery::all()];
        let fsm = FilterFsm::compile(&queries);

        // Root is terminal — matches all top-level values
        assert!(fsm.is_terminal(0));
    }

    #[test]
    fn trailing_predicate_on_terminal() {
        let queries = [PathQuery::new(vec![
            Step::Select(Select::Field("foo".into())),
            Step::Match(Predicate::Type(IonType::Int)),
        ])];
        let fsm = FilterFsm::compile(&queries);

        let child = fsm.transition_field(0, "foo").unwrap();
        assert!(fsm.is_terminal(child));
        assert_eq!(fsm.predicates(child).len(), 1);
        assert_eq!(
            fsm.predicates(child)[0],
            (Predicate::Type(IonType::Int), false)
        );
    }

    #[test]
    fn leading_predicate_on_root() {
        let queries = [PathQuery::new(vec![
            Step::Match(Predicate::HasAnnotation("abc".into())),
            Step::Select(Select::Field("x".into())),
        ])];
        let fsm = FilterFsm::compile(&queries);

        // Root has a predicate
        assert_eq!(fsm.predicates(0).len(), 1);
        assert_eq!(
            fsm.predicates(0)[0],
            (Predicate::HasAnnotation("abc".into()), false)
        );
        assert!(!fsm.is_terminal(0));

        let child = fsm.transition_field(0, "x").unwrap();
        assert!(fsm.is_terminal(child));
    }

    #[test]
    fn conjunction_predicates() {
        let queries = [PathQuery::new(vec![
            Step::Select(Select::Field("foo".into())),
            Step::Match(Predicate::Type(IonType::Int)),
            Step::NotMatch(Predicate::IsNull),
        ])];
        let fsm = FilterFsm::compile(&queries);

        let child = fsm.transition_field(0, "foo").unwrap();
        assert!(fsm.is_terminal(child));
        let preds = fsm.predicates(child);
        assert_eq!(preds.len(), 2);
        assert_eq!(preds[0], (Predicate::Type(IonType::Int), false));
        assert_eq!(preds[1], (Predicate::IsNull, true));
    }

    #[test]
    fn validation_rejects_select_after_scalar_type() {
        let result = PathQuerySet::compile(
            vec![PathQuery::new(vec![
                Step::Match(Predicate::Type(IonType::Int)),
                Step::Select(Select::Field("foo".into())),
            ])],
            false,
        );
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            PathQueryError::SelectAfterScalarType { .. }
        ));
    }

    #[test]
    fn validation_rejects_struct_nav_after_list_type() {
        let result = PathQuerySet::compile(
            vec![PathQuery::new(vec![
                Step::Match(Predicate::Type(IonType::List)),
                Step::Select(Select::Field("foo".into())),
            ])],
            false,
        );
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            PathQueryError::ContainerTypeMismatch { .. }
        ));
    }

    #[test]
    fn validation_rejects_list_nav_after_struct_type() {
        let result = PathQuerySet::compile(
            vec![PathQuery::new(vec![
                Step::Match(Predicate::Type(IonType::Struct)),
                Step::Select(Select::Index(0)),
            ])],
            false,
        );
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            PathQueryError::ContainerTypeMismatch { .. }
        ));
    }

    #[test]
    fn validation_accepts_not_match_before_select() {
        let result = PathQuerySet::compile(
            vec![PathQuery::new(vec![
                Step::NotMatch(Predicate::IsNull),
                Step::Select(Select::Field("foo".into())),
            ])],
            false,
        );
        assert!(result.is_ok());
    }

    #[test]
    fn validation_accepts_empty_query_set() {
        let result = PathQuerySet::compile(vec![], false);
        assert!(result.is_ok());
    }

    #[test]
    fn validation_accepts_empty_steps_with_flatten() {
        let result = PathQuerySet::compile(vec![PathQuery::all()], true);
        assert!(result.is_ok());
    }

    #[test]
    fn validation_accepts_any_after_list_type() {
        let result = PathQuerySet::compile(
            vec![PathQuery::new(vec![
                Step::Match(Predicate::Type(IonType::List)),
                Step::Select(Select::Any),
            ])],
            false,
        );
        assert!(result.is_ok());
    }

    #[test]
    fn validation_accepts_any_index_after_list_type() {
        let result = PathQuerySet::compile(
            vec![PathQuery::new(vec![
                Step::Match(Predicate::Type(IonType::List)),
                Step::Select(Select::AnyIndex),
            ])],
            false,
        );
        assert!(result.is_ok());
    }

    #[test]
    fn any_populates_both_wildcards() {
        let queries = [PathQuery::new(vec![Step::Select(Select::Any)])];
        let fsm = FilterFsm::compile(&queries);

        // Should match both struct fields and sequence indices
        let field_child = fsm.transition_field(0, "foo").unwrap();
        let index_child = fsm.transition_index(0, 0).unwrap();
        assert_eq!(field_child, index_child);
        assert!(fsm.is_terminal(field_child));
    }
}
