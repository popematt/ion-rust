//! Filter policy trait for selective value emission.
//!
//! The `FilterPolicy` trait enables the binary generator to be parameterized
//! over whether (and how) values are filtered during bytecode generation.
//!
//! `NoFilter` is a zero-sized type whose methods are `#[inline(always)]` and
//! return constants. After monomorphization, the compiler eliminates all
//! filter-related branches and the generator produces identical code to a
//! hand-written unfiltered generator.

/// Determines whether values should be emitted or skipped during generation.
///
/// Implementations are monomorphized, so `NoFilter` (a ZST) compiles to zero
/// overhead -- all its methods become no-ops that the optimizer eliminates.
pub trait FilterPolicy {
    /// Called when entering a struct field. Returns the child FSM node index
    /// if this field should be descended into, or `None` to skip.
    fn on_field(&mut self, field_sid: u32, field_text: Option<&str>) -> Option<usize>;

    /// Called when entering a sequence element by index. Returns the child
    /// FSM node index if this element should be descended into, or `None`
    /// to skip.
    fn on_index(&mut self, index: usize) -> Option<usize>;

    /// Called when entering a container. The policy may update internal
    /// state (e.g., push FSM stack).
    fn on_container_enter(&mut self, node: usize);

    /// Called when exiting a container.
    fn on_container_exit(&mut self);

    /// Whether the current node is terminal (value should be emitted).
    fn is_terminal(&self) -> bool;

    /// Whether the current node has any child transitions (should we step
    /// into a container to check children?).
    fn has_transitions(&self) -> bool;

    /// Whether the policy requires maintaining an internal symbol table
    /// (for SID-to-text resolution).
    const NEEDS_SYMBOL_TABLE: bool;
}

/// No-op filter policy. All values are emitted unconditionally.
///
/// This is a zero-sized type; all methods are `#[inline(always)]` and return
/// constants. After monomorphization, the compiler eliminates all
/// filter-related code paths, producing identical machine code to a generator
/// without any filter parameter.
pub struct NoFilter;

impl FilterPolicy for NoFilter {
    #[inline(always)]
    fn on_field(&mut self, _field_sid: u32, _field_text: Option<&str>) -> Option<usize> {
        Some(0)
    }

    #[inline(always)]
    fn on_index(&mut self, _index: usize) -> Option<usize> {
        Some(0)
    }

    #[inline(always)]
    fn on_container_enter(&mut self, _node: usize) {}

    #[inline(always)]
    fn on_container_exit(&mut self) {}

    #[inline(always)]
    fn is_terminal(&self) -> bool {
        true
    }

    #[inline(always)]
    fn has_transitions(&self) -> bool {
        true
    }

    const NEEDS_SYMBOL_TABLE: bool = false;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_filter_is_zero_sized() {
        assert_eq!(std::mem::size_of::<NoFilter>(), 0);
    }

    #[test]
    fn no_filter_always_emits() {
        let mut filter = NoFilter;
        assert_eq!(filter.on_field(42, None), Some(0));
        assert_eq!(filter.on_field(0, Some("anything")), Some(0));
        assert_eq!(filter.on_index(0), Some(0));
        assert_eq!(filter.on_index(999), Some(0));
        assert!(filter.is_terminal());
        assert!(filter.has_transitions());
    }

    #[test]
    fn no_filter_container_ops_are_noop() {
        let mut filter = NoFilter;
        // These should compile to nothing and not panic.
        filter.on_container_enter(0);
        filter.on_container_enter(42);
        filter.on_container_exit();
    }
}
