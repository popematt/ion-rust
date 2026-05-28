//! Path filter AST and compiled FSM for selective value extraction.
//!
//! A `PathFilter` describes a path from the document root down to a target
//! value. Multiple filters are compiled into a `FilterFsm` (a trie-shaped
//! finite state machine) that enables O(1) per-value matching decisions during
//! bytecode generation.

use std::collections::HashMap;

/// A single step in a path filter.
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FieldMatcher {
    /// Match by UTF-8 field name text (exact, case-sensitive).
    Text(String),
    /// Match by symbol ID (for data with known symbol tables).
    Sid(usize),
}

/// A complete path filter: a sequence of steps from the top level down to
/// the target value.
///
/// Example: `PathFilter::new(vec![PathStep::Field("foo".into()),
/// PathStep::Index(0)])` matches the first element of the list/sexp in
/// field "foo" of any top-level struct.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PathFilter {
    steps: Vec<PathStep>,
}

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
}

impl From<&str> for FieldMatcher {
    fn from(s: &str) -> Self {
        FieldMatcher::Text(s.to_owned())
    }
}

impl From<String> for FieldMatcher {
    fn from(s: String) -> Self {
        FieldMatcher::Text(s)
    }
}

/// A node in the compiled filter trie.
#[derive(Debug)]
struct FsmNode {
    /// If true, values reaching this node are "matched" and their
    /// bytecode should be emitted in full.
    is_terminal: bool,
    /// Transition on struct field name (text).
    field_children: HashMap<String, usize>,
    /// Transition on SID.
    sid_children: HashMap<usize, usize>,
    /// Transition on sequence index.
    index_children: HashMap<usize, usize>,
    /// Wildcard transition (if present). Matches any field/index at
    /// this depth.
    wildcard_child: Option<usize>,
}

impl FsmNode {
    fn new() -> Self {
        Self {
            is_terminal: false,
            field_children: HashMap::new(),
            sid_children: HashMap::new(),
            index_children: HashMap::new(),
            wildcard_child: None,
        }
    }

    fn has_transitions(&self) -> bool {
        !self.field_children.is_empty()
            || !self.sid_children.is_empty()
            || !self.index_children.is_empty()
            || self.wildcard_child.is_some()
    }
}

/// The compiled FSM for a set of path filters.
#[derive(Debug)]
pub(crate) struct FilterFsm {
    /// Arena of FSM nodes. Index 0 is the root.
    nodes: Vec<FsmNode>,
}

impl FilterFsm {
    /// Compile a set of path filters into an FSM.
    pub fn compile(filters: &[PathFilter]) -> Self {
        let mut fsm = Self {
            nodes: vec![FsmNode::new()],
        };

        for filter in filters {
            let mut current = 0;
            for step in filter.steps() {
                current = fsm.get_or_create_child(current, step);
            }
            // Mark the final node as terminal.
            fsm.nodes[current].is_terminal = true;
        }

        fsm
    }

    /// Gets or creates a child node for the given step from the given
    /// parent node.
    fn get_or_create_child(&mut self, parent: usize, step: &PathStep) -> usize {
        match step {
            PathStep::Field(FieldMatcher::Text(name)) => {
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
            PathStep::Field(FieldMatcher::Sid(sid)) => {
                if let Some(&child) = self.nodes[parent].sid_children.get(sid) {
                    child
                } else {
                    let child_idx = self.nodes.len();
                    self.nodes.push(FsmNode::new());
                    self.nodes[parent].sid_children.insert(*sid, child_idx);
                    child_idx
                }
            }
            PathStep::Index(idx) => {
                if let Some(&child) = self.nodes[parent].index_children.get(idx) {
                    child
                } else {
                    let child_idx = self.nodes.len();
                    self.nodes.push(FsmNode::new());
                    self.nodes[parent].index_children.insert(*idx, child_idx);
                    child_idx
                }
            }
            PathStep::Wildcard => {
                if let Some(child) = self.nodes[parent].wildcard_child {
                    child
                } else {
                    let child_idx = self.nodes.len();
                    self.nodes.push(FsmNode::new());
                    self.nodes[parent].wildcard_child = Some(child_idx);
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
        n.wildcard_child
    }

    /// Transition on a SID (for binary data where field names are encoded
    /// as symbol IDs).
    pub fn transition_sid(&self, node: usize, sid: usize) -> Option<usize> {
        let n = &self.nodes[node];
        if let Some(&child) = n.sid_children.get(&sid) {
            return Some(child);
        }
        n.wildcard_child
    }

    /// Transition on a sequence index.
    pub fn transition_index(&self, node: usize, index: usize) -> Option<usize> {
        let n = &self.nodes[node];
        if let Some(&child) = n.index_children.get(&index) {
            return Some(child);
        }
        n.wildcard_child
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_field_filter_compiles() {
        let filters = [PathFilter::field("foo")];
        let fsm = FilterFsm::compile(&filters);

        // Root has a transition on "foo"
        let child = fsm.transition_field(0, "foo");
        assert!(child.is_some());
        let child = child.unwrap();
        assert!(fsm.is_terminal(child));

        // No transition on "bar"
        assert!(fsm.transition_field(0, "bar").is_none());
    }

    #[test]
    fn nested_field_filter_compiles() {
        let filters = [PathFilter::fields(&["foo", "bar"])];
        let fsm = FilterFsm::compile(&filters);

        let first = fsm.transition_field(0, "foo").unwrap();
        assert!(!fsm.is_terminal(first));
        assert!(fsm.has_transitions(first));

        let second = fsm.transition_field(first, "bar").unwrap();
        assert!(fsm.is_terminal(second));
    }

    #[test]
    fn wildcard_filter_compiles() {
        let filters = [PathFilter::new(vec![
            PathStep::Wildcard,
            PathStep::Field("name".into()),
        ])];
        let fsm = FilterFsm::compile(&filters);

        // Wildcard matches any field
        let first = fsm.transition_field(0, "anything").unwrap();
        assert!(!fsm.is_terminal(first));

        let second = fsm.transition_field(first, "name").unwrap();
        assert!(fsm.is_terminal(second));
    }

    #[test]
    fn index_filter_compiles() {
        let filters = [PathFilter::new(vec![
            PathStep::Field("items".into()),
            PathStep::Index(0),
        ])];
        let fsm = FilterFsm::compile(&filters);

        let first = fsm.transition_field(0, "items").unwrap();
        assert!(!fsm.is_terminal(first));

        let second = fsm.transition_index(first, 0).unwrap();
        assert!(fsm.is_terminal(second));

        // Index 1 should not match
        assert!(fsm.transition_index(first, 1).is_none());
    }

    #[test]
    fn multiple_filters_share_prefix() {
        let filters = [
            PathFilter::fields(&["a", "b"]),
            PathFilter::fields(&["a", "c"]),
        ];
        let fsm = FilterFsm::compile(&filters);

        let a = fsm.transition_field(0, "a").unwrap();
        assert!(!fsm.is_terminal(a));

        let b = fsm.transition_field(a, "b").unwrap();
        assert!(fsm.is_terminal(b));

        let c = fsm.transition_field(a, "c").unwrap();
        assert!(fsm.is_terminal(c));
    }

    #[test]
    fn sid_filter_compiles() {
        let filters = [PathFilter::new(vec![PathStep::Field(FieldMatcher::Sid(
            10,
        ))])];
        let fsm = FilterFsm::compile(&filters);

        let child = fsm.transition_sid(0, 10).unwrap();
        assert!(fsm.is_terminal(child));

        assert!(fsm.transition_sid(0, 11).is_none());
    }

    #[test]
    fn root_has_no_transitions_when_empty() {
        let filters: [PathFilter; 0] = [];
        let fsm = FilterFsm::compile(&filters);

        assert!(!fsm.has_transitions(0));
        assert!(!fsm.is_terminal(0));
    }
}
