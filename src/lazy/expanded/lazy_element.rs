use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::span::Span;
use crate::lazy::streaming_raw_reader::IoBuffer;
use crate::result::IonFailure;
use crate::{
    Annotations, AnyEncoding, Decoder, Element, EncodingContext, ExpandedValueSource, IonEncoding,
    IonError, IonResult, IonType, LazyExpandedValue, LazyValue, Value,
};
use std::cell::OnceCell;
use std::marker::PhantomData;
use std::ops::Range;
use std::rc::Rc;

/// The facts about a value that a [`LazyElement`] can record when it is created, sparing it from
/// having to re-parse the value in order to answer them later.
///
/// Every field is `Copy` and is already known to the [`LazyValue`] the `LazyElement` is made from,
/// so capturing them costs nothing.
#[derive(Copy, Clone, Debug)]
pub(crate) struct ValueMetadata {
    ion_type: IonType,
    is_null: bool,
    has_annotations: bool,
}

impl ValueMetadata {
    /// Records the header facts of `value`.
    pub(crate) fn of<Encoding: Decoder>(value: &LazyValue<'_, Encoding>) -> Self {
        Self {
            ion_type: value.ion_type(),
            is_null: value.is_null(),
            has_annotations: value.has_annotations(),
        }
    }
}

/// A (potentially annotated) value in an Ion data stream.
///
/// Unlike an [`Element`], a `LazyElement` does not eagerly read the value's contents or materialize
/// its data, making it comparatively lightweight.
///
/// Unlike a [`LazyValue`], a `LazyElement` shares ownership of its backing resources with the `Reader`.
/// This requires a small amount of bookkeeping overhead, but eliminates the need for lifetimes.
/// `LazyElement` instances can be stored indefinitely.
/// Note, however, that storing `LazyElement`s will also prevent their backing resources from being freed.
///
/// # Implementation
///
/// A `LazyElement` stores no borrowed data. Instead, it records *where* its value is--the range of
/// stream offsets the value occupies and the encoding it was written in--along with shared handles
/// to the resources needed to interpret those bytes.
///
/// Inspecting the value's header (its [type](Self::ion_type), whether it is
/// [null](Self::is_null), whether it has [annotations](Self::has_annotations)) never touches those
/// bytes; those facts are captured as owned, `Copy` state when the `LazyElement` is created.
///
/// Reading the value's data is different: it requires re-parsing the recorded bytes, and the
/// re-parsed representation is allocated in the shared arena the `LazyElement` holds a handle to.
/// That arena is not reclaimed until the last handle to it is dropped, so re-parsing on every read
/// would grow memory in proportion to the value's size times the number of reads. To avoid that,
/// the first read materializes the value into an owned [`Element`] and caches it. Subsequent reads
/// borrow the cached `Element`: they neither re-parse nor allocate. The consequence is that the
/// first read of a large container is comparatively expensive, and that a `LazyElement` which has
/// been read retains a materialized copy of its value for as long as it lives.
pub struct LazyElement<Encoding: Decoder = AnyEncoding> {
    // Shared ownership of the resources needed to interpret the value: the symbol table used to
    // resolve its symbol tokens and the bump allocator that re-parsing allocates in.
    //
    // NB: holding this `Rc` is also what keeps the reader from recycling the arena. See the
    // copy-on-write guard in `EncodingContext::make_allocator_mut`.
    context: Rc<EncodingContext>,
    // Shared ownership of the input buffer holding the value's serialized bytes.
    //
    // The `EncodingContext` above holds an `IoBuffer` of its own, but its bytes are only reachable
    // through an `UnsafeCell`. Keeping a handle here lets each read borrow them safely.
    io_buffer: IoBuffer,
    // The value's location in the stream. Note that this range includes the value's annotations,
    // if it has any.
    value_range: Range<usize>,
    // The encoding in which the value was serialized. `Encoding` may support more than one (see
    // [`AnyEncoding`]), in which case re-parsing needs to be told which one to use.
    encoding: IonEncoding,
    // The value's header facts, copied from the `LazyValue` this `LazyElement` was made from so that
    // the corresponding accessors can be infallible, allocation-free field reads.
    metadata: ValueMetadata,
    // The memoized result of materializing this value; see the type-level docs.
    //
    // NB: this must remain an *owned* representation. Caching anything that borrows from
    // `io_buffer` or from the arena in `context` would make `LazyElement` self-referential.
    read_cache: OnceCell<Element>,
    // `LazyElement` is generic over the decoder that produced it, but stores no decoder-specific
    // data of its own.
    decoder: PhantomData<Encoding>,
}

impl<Encoding: Decoder> LazyElement<Encoding> {
    /// Constructs a `LazyElement` for the value occupying `value_range` of the stream.
    ///
    /// `io_buffer` must contain the bytes in `value_range`, and `encoding` must be the encoding in
    /// which they were written. `context` must be a clone of the `EncodingContext` that was active
    /// when the value was read, so that its symbol table can resolve the value's symbol tokens.
    /// `metadata` must describe the same value that `value_range` locates.
    pub(crate) fn new(
        context: Rc<EncodingContext>,
        io_buffer: IoBuffer,
        value_range: Range<usize>,
        encoding: IonEncoding,
        metadata: ValueMetadata,
    ) -> Self {
        debug_assert!(
            value_range.start >= io_buffer.stream_offset()
                && value_range.end <= io_buffer.stream_offset() + io_buffer.all_bytes().len(),
            "value range {value_range:?} is not contained by the buffer it was read from"
        );
        Self {
            context,
            io_buffer,
            value_range,
            encoding,
            metadata,
            read_cache: OnceCell::new(),
            decoder: PhantomData,
        }
    }

    /// Returns the value's serialized bytes.
    ///
    /// The containment invariant documented on [`Self::new`] guarantees that this succeeds; it is
    /// checked rather than assumed because `as_lazy_value` already has an error channel and a
    /// violated invariant should not panic in a release build.
    fn value_bytes(&self) -> IonResult<&[u8]> {
        let all_bytes = self.io_buffer.all_bytes();
        self.value_range
            .start
            .checked_sub(self.io_buffer.stream_offset())
            .and_then(|local_start| {
                let local_end = local_start.checked_add(self.value_range.len())?;
                all_bytes.get(local_start..local_end)
            })
            .ok_or_else(|| {
                IonError::decoding_error(format!(
                    "value range {:?} is not contained by the buffer it was read from \
                     (stream offset {}, {} bytes)",
                    self.value_range,
                    self.io_buffer.stream_offset(),
                    all_bytes.len(),
                ))
            })
    }

    /// Re-parses the value from the bytes this `LazyElement` holds, returning a borrowed view of it.
    ///
    /// The returned `LazyValue` borrows `self`, so the resources it references cannot be released
    /// while it is alive.
    ///
    /// NB: the re-parsed value is allocated in the shared arena, which is not reclaimed until the
    /// last handle to it drops. Callers should invoke this at most once per `LazyElement` where
    /// possible; [`Self::element`] memoizes an owned materialization for that reason.
    pub(crate) fn as_lazy_value(&self) -> IonResult<LazyValue<'_, Encoding>> {
        let context = self.context.get_ref();
        let bytes = self.value_bytes()?;
        let span = Span::with_offset(self.value_range.start, bytes);
        let raw_value = Encoding::value_from_span(context, span, self.encoding)?;
        let expanded = LazyExpandedValue {
            context,
            source: ExpandedValueSource::ValueLiteral(raw_value),
        };
        Ok(LazyValue::new(expanded))
    }

    /// Returns this value as a fully materialized [`Element`], parsing it on the first call and
    /// serving the cached result on every call thereafter.
    fn element(&self) -> IonResult<&Element> {
        if let Some(element) = self.read_cache.get() {
            return Ok(element);
        }
        let element = Element::try_from(self.as_lazy_value()?)?;
        // The cache was empty when it was checked above and a `&self` borrow cannot be shared
        // across threads, so the closure below is guaranteed to run. Initializing through
        // `get_or_init` (rather than `set` followed by `get`) avoids having to handle an
        // impossible `Err`/`None`.
        Ok(self.read_cache.get_or_init(|| element))
    }
}

impl<Encoding: Decoder> LazyElement<Encoding> {
    // Each of the methods below answers from state that was recorded when this `LazyElement` was
    // created, so all of them are infallible and none of them allocates.

    /// Returns the [`IonType`] of this `LazyElement`.
    pub fn ion_type(&self) -> IonType {
        self.metadata.ion_type
    }

    /// Returns `true` if this `LazyElement` is any form of `null`.
    pub fn is_null(&self) -> bool {
        self.metadata.is_null
    }

    /// Returns `true` if this `LazyElement` is a list, s-expression, or struct.
    pub fn is_container(&self) -> bool {
        matches!(
            self.ion_type(),
            IonType::List | IonType::SExp | IonType::Struct
        )
    }

    /// Returns `true` if this `LazyElement` is not a container.
    pub fn is_scalar(&self) -> bool {
        !self.is_container()
    }

    /// Returns `true` if this `LazyElement` has one or more annotations.
    pub fn has_annotations(&self) -> bool {
        self.metadata.has_annotations
    }

    // The methods below need the value's data, so the first one to be called materializes it. Both
    // return a reference into that cached materialization; see the type-level docs.

    /// Reads the value portion of this `LazyElement`.
    ///
    /// The first call materializes the value; later calls are cheap borrows of the cached result.
    pub fn read(&self) -> IonResult<&Value> {
        Ok(self.element()?.value())
    }

    /// Returns the annotations on this `LazyElement`.
    ///
    /// The first call materializes the value; later calls are cheap borrows of the cached result.
    pub fn annotations(&self) -> IonResult<&Annotations> {
        Ok(self.element()?.annotations())
    }

    /// Returns the encoding context that this `LazyElement` uses to read its data.
    // Only the unit tests (which inspect the shared arena) call this today.
    #[allow(dead_code)]
    pub(crate) fn context(&self) -> EncodingContextRef<'_> {
        self.context.get_ref()
    }
}

impl<'top, Encoding: Decoder> From<LazyValue<'top, Encoding>> for LazyElement<Encoding> {
    fn from(value: LazyValue<'top, Encoding>) -> Self {
        value.to_owned()
    }
}

impl<Encoding: Decoder> TryFrom<LazyElement<Encoding>> for Element {
    type Error = IonError;

    fn try_from(mut lazy_element: LazyElement<Encoding>) -> Result<Self, Self::Error> {
        // If an earlier read already materialized this value, hand over the cached `Element`
        // instead of copying it.
        if let Some(element) = lazy_element.read_cache.take() {
            return Ok(element);
        }
        // Otherwise, materialize the value directly. Populating the cache first would only mean
        // cloning out of a cache that is about to be dropped along with `lazy_element`.
        Element::try_from(lazy_element.as_lazy_value()?)
    }
}

impl<Encoding: Decoder> TryFrom<&LazyElement<Encoding>> for Element {
    type Error = IonError;

    fn try_from(lazy_element: &LazyElement<Encoding>) -> Result<Self, Self::Error> {
        // `lazy_element` may be read again, so materialize into its cache and copy out of it. This
        // trades a clone for the guarantee that repeated conversions do not re-parse the value or
        // allocate in the shared arena again.
        Ok(lazy_element.element()?.clone())
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::any_encoding::IonEncoding;
    use crate::lazy::expanded::lazy_element::LazyElement;
    use crate::{
        v1_0, AnyEncoding, Decoder, Element, IonResult, IonType, LazyValue, Reader, Sequence,
        Value, ValueRef,
    };
    use rstest::rstest;

    fn test_data() -> &'static str {
        r#"
            $ion_1_0

            // === Scalars ===
            null
            null.string
            true
            false
            0
            -9223372036854775808
            0xBEEF
            1e0
            3.14159
            -6d+5
            2025T
            2025-09-18T12:34:56.789-07:00
            foo
            'quoted symbol'
            "Hello"
            '''long''' ''' string'''
            {{aGVsbG8=}}
            {{"clob"}}

            // === Containers ===
            []
            ()
            {}
            [(), {}, ()]
            (a b (c d) [e, f] {g: h})
            {a: 1, b: [2, 3], c: {d: 4}}
            // A symbol whose bytes would be read as an IVM if they began a stream
            [$ion_1_0]

            // === Annotations ===
            baz::5
            a::b::c::[1, 2, 3]
            a::{b: c::d}
         "#
    }

    /// Serializes `ion_text` in `format`, leaving it untouched if `format` is already text.
    fn encode(format: IonEncoding, ion_text: &str) -> IonResult<Vec<u8>> {
        if format.is_text() {
            Ok(ion_text.as_bytes().to_vec())
        } else {
            Element::read_all(ion_text)?.encode_as(v1_0::Binary)
        }
    }

    fn test_input(format: IonEncoding) -> IonResult<Vec<u8>> {
        encode(format, test_data())
    }

    /// Reads the output of `test_data()` twice, once using the `Element` API and again using
    /// the `LazyElement` API. The output is passed to `TestFn` to make assertions.
    fn lazy_element_test<TestFn>(format: IonEncoding, test: TestFn) -> IonResult<()>
    where
        TestFn: FnOnce(Sequence, &mut dyn Iterator<Item = IonResult<LazyElement>>) -> IonResult<()>,
    {
        let test_data = test_input(format)?;
        let expected = Element::read_all(test_data.as_slice())?;
        let mut reader = Reader::new(AnyEncoding, test_data.as_slice())?;
        test(expected, &mut reader)
    }

    #[rstest]
    fn equivalent_to_lazy_value_when_reading_forward(
        #[values(IonEncoding::Text_1_0, IonEncoding::Binary_1_0)] format: IonEncoding,
    ) -> IonResult<()> {
        lazy_element_test(format, |expected, reader| {
            // Fully read each LazyElement as it's encountered and compare it to the corresponding
            // expected element. Only one LazyElement exists at a time.
            let actual = reader
                .map(|result| result.and_then(Element::try_from))
                .collect::<IonResult<Vec<Element>>>()?;
            assert!(expected.iter().eq(&actual));
            Ok(())
        })
    }

    #[rstest]
    fn equivalent_to_lazy_value_when_read_backward(
        #[values(IonEncoding::Text_1_0, IonEncoding::Binary_1_0)] format: IonEncoding,
    ) -> IonResult<()> {
        lazy_element_test(format, |expected, reader| {
            // Store the LazyElements in a Vec without reading them.
            let lazy_elements_vec = reader.collect::<IonResult<Vec<LazyElement>>>()?;
            // Read the collected LazyElements in reverse order and store them in another Vec,
            // demonstrating that it's safe/correct to read them in an order that differs from their
            // order in the input stream.
            let actual = lazy_elements_vec
                .iter()
                .rev()
                .map(Element::try_from)
                .collect::<IonResult<Vec<Element>>>()?;
            assert!(expected.into_iter().rev().eq(actual));
            Ok(())
        })
    }

    #[test]
    fn values_survive_after_reader_drops() -> IonResult<()> {
        let mut reader = Reader::new(AnyEncoding, "foo")?;
        let lazy_element = reader.expect_next()?.to_owned();
        // Even though we have a `LazyElement`, we can safely drop the `Reader`.
        drop(reader);
        // The `LazyElement` is still valid/usable.
        assert_eq!(Element::symbol("foo"), Element::try_from(lazy_element)?);
        Ok(())
    }

    /// Collects a container's children as `LazyElement`s.
    ///
    /// This is the `LazyValue::to_owned` path for values that are *not* at the top level of the
    /// stream, which is the only way `Decoder::value_from_span` can be handed a span whose first
    /// bytes are those of an Ion version marker.
    fn owned_children<E: Decoder>(parent: &LazyElement<E>) -> IonResult<Vec<LazyElement<E>>> {
        let lazy_value = parent.as_lazy_value()?;
        match lazy_value.read()? {
            ValueRef::List(list) => list
                .iter()
                .map(|child| child.map(LazyValue::to_owned))
                .collect(),
            ValueRef::SExp(sexp) => sexp
                .iter()
                .map(|child| child.map(LazyValue::to_owned))
                .collect(),
            ValueRef::Struct(strukt) => strukt
                .iter()
                .map(|field| field.map(|f| f.value().to_owned()))
                .collect(),
            _ => Ok(Vec::new()),
        }
    }

    /// A child value whose bytes are `$ion_1_0` must be read as a symbol, not as an Ion version
    /// marker.
    ///
    /// `to_owned()`ing the *enclosing* container does not exercise this: the span handed to
    /// `Decoder::value_from_span` then begins with `[`, `(`, or `{`. Only owning the child puts the
    /// ambiguous bytes at the start of the span.
    #[rstest]
    fn container_children_can_be_owned(
        #[values(IonEncoding::Text_1_0, IonEncoding::Binary_1_0)] format: IonEncoding,
        #[values(
            "[$ion_1_0]",
            "($ion_1_0)",
            "{a: $ion_1_0}",
            "[a::$ion_1_0, $ion_1_0, foo]"
        )]
        ion_text: &str,
    ) -> IonResult<()> {
        let expected_children: Vec<Element> = match Element::read_one(ion_text)?.value() {
            Value::List(seq) | Value::SExp(seq) => seq.elements().cloned().collect(),
            Value::Struct(strukt) => strukt.fields().map(|(_, value)| value.clone()).collect(),
            _ => Vec::new(),
        };
        assert!(
            !expected_children.is_empty(),
            "each case must be a non-empty container"
        );

        let input = encode(format, ion_text)?;
        let mut reader = Reader::new(AnyEncoding, input.as_slice())?;
        let parent = reader.expect_next()?.to_owned();
        // Dropping the reader shows that the children can be owned from the stored parent alone.
        drop(reader);

        let actual_children = owned_children(&parent)?
            .iter()
            .map(Element::try_from)
            .collect::<IonResult<Vec<Element>>>()?;
        assert_eq!(expected_children, actual_children);
        Ok(())
    }

    /// The first read materializes the value and caches it. Later reads must not re-parse it;
    /// re-parsing allocates in the shared arena, which is not reclaimed while the `LazyElement`
    /// lives, so an un-memoized read would grow memory in proportion to reads × value size.
    #[rstest]
    fn repeated_reads_do_not_grow_the_arena(
        #[values(IonEncoding::Text_1_0, IonEncoding::Binary_1_0)] format: IonEncoding,
    ) -> IonResult<()> {
        let input = encode(
            format,
            r#"{a: [1, 2, 3], b: {c: (d e f)}, g: "hello", h: [[[1]]]}"#,
        )?;
        let mut reader = Reader::new(AnyEncoding, input.as_slice())?;
        let lazy_element = reader.expect_next()?.to_owned();
        drop(reader);

        // The first read parses the value into the arena and caches the materialized result.
        let first_read = lazy_element.read()?.clone();
        let allocated_after_first_read = lazy_element.context().allocator().allocated_bytes();

        for _ in 0..1_000 {
            assert_eq!(&first_read, lazy_element.read()?);
            assert_eq!(IonType::Struct, lazy_element.ion_type());
            assert!(lazy_element.is_container());
            assert!(!lazy_element.is_scalar());
            assert!(!lazy_element.is_null());
            assert!(!lazy_element.has_annotations());
            assert!(lazy_element.annotations()?.is_empty());
        }

        assert_eq!(
            allocated_after_first_read,
            lazy_element.context().allocator().allocated_bytes(),
            "repeated reads allocated in the shared arena; is `read()` still memoized?"
        );
        Ok(())
    }
}
