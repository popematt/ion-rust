// Copyright Amazon.com, Inc. or its affiliates.

//! An experimental feature for computing the difference between two Ion values or Ion streams.
//!
//! ## Limitations
//!
//! * Current implementation does not handle repeated field names in structs correctly.
//!   Sometimes, it may detect no change, and other times, it may detect an incorrect change.
//!

// TODO: Deal with duplicate field names—see 'FIXME' test cases below
// The problem is that the diff between two structs is currently determined by modeling as an
// associative array with one (unique) key for one value. We can fix this by modelling it as an
// associative array with one (unique) key for a bag of values, or by relaxing the uniqueness
// requirement (i.e. use a bag of key-value pairs).
// TODO: Better diff for sequences–see 'FIXME' test cases below
// https://crates.io/crates/similar is a mature library with multiple diff algorithms.
// It might be possible to use it directly, or we may need to be inspired by it and write our own.


mod diff;
mod key;
mod recorder;
mod traits;
mod ord_element;

use crate::ion_diff::recorder::DefaultChangeListener;

pub use traits::*;
pub use key::Key;
pub use recorder::ChangeType;





#[cfg(test)]
mod diff_tests {
    use super::*;
    use crate::ion_diff::recorder::ChangeType::Unchanged;
    use rstest::*;
    use crate::Element;

    #[rstest]
    #[case::change_container_type("[A, B]", "(A B)", "value_modified::{path: (), old: [A, B], new: (A B)}")]
    #[case::add_list_element("[a, b]", "[a, b, c]", "added::{ path: (2), new: c }")]
    #[case::remove_list_element("[a, b, c]", "[a, b]", "removed::{ path: (2), old: c }")]
    #[case::add_sexp_element("(a b)", "(a  b  c)", "added::{ path: (2), new: c }")]
    #[case::add_sexp_element("(a b c)", "(a  b)", "removed::{ path: (2), old: c }")]
    #[case::add_struct_element(
        "{ a: A, b: B }",
        "{ a: A, b: B, c: C }",
        "added::{ path: (c), new: C }"
    )]
    #[case::remove_struct_element(
        "{ a: A, b: B, c: C }",
        "{ a: A, b: B }",
        "removed::{ path: (c), old: C }"
    )]
    #[case::change_annotations(
        "a::1",
        "b::1",
        "annotations_modified::{ path: (), old: a::null, new: b::null }"
    )]
    #[case::change_value("a::1", "a::2", "value_modified::{ path: (), old: 1, new: 2 }")]
    #[case::change_nested_list_element(
        "[a, [b, c], d]",
        "[a, [b, e], d]",
        "value_modified::{ path: (1 1), old: c, new: e }"
    )]
    #[case::change_nested_list_element_and_annotations(
        "[a, [b, c], d]",
        "[a, foo::[b, e], d]",
        r"
        annotations_modified::{path: (1), old: null, new: foo::null}
        value_modified::{ path: (1 1), old: c, new: e }
        "
    )]
    #[case::modify_field(
    "{ a: B }",
    "{ a: C }",
    r"
    value_modified::{path: (a), old: B, new: C}
    "
    )]
    #[case::modify_field_annotations(
    "{ a: c::B }",
    "{ a: d::B }",
    r"
    annotations_modified::{path: (a), old: c::null, new: d::null}
    "
    )]
    #[case::duplicate_field_names(
        "{ a: A, a: B }",
        "{ a: C, a: A }",
        r"
        removed::{path: (a), old: B}
        added::{path: (a), new: C}
        "
    )]
    #[case::duplicate_field_names(
    "{ a: A, a: B }",
    "{ a: B, a: A }",
    ""
    )]
    #[case::duplicate_field_names(
    "{ a: A, a: B }",
    "{ a: A, a: C }",
    r"
        removed::{path: (a), old: B}
        added::{path: (a), new: C}
    "
    )]
    #[case::duplicate_field_names(
        "{ a: A }",
        "{ a: A, a: A }",
        "added::{ path: (a), new: A }"
    )]
    #[case::remove_at_start_of_seq(
    "(a b c)",
    "(b c)",
    r"
    removed::{path: (0), old: a}
    moved::{old_path: (1), new_path: (0), value: b}
    moved::{old_path: (2), new_path: (1), value: c}
    "
    )]
    #[case::remove_at_start_of_seq_and_modify_later_value(
    "(a b c d e)",
    "(b c foo::d e)",
    r"
    removed::{path: (0), old: a}
    moved::{old_path: (1), new_path: (0), value: b}
    moved::{old_path: (2), new_path: (1), value: c}
    annotations_modified::{ path: (3), old: null, new: foo::null}
    moved::{old_path: (3), new_path: (2), value: foo::d}
    moved::{old_path: (4), new_path: (3), value: e}
    "
    )]
    #[case::complicated_nesting(
    r#"
    {
      name: "Fido",
      age: years::4,
      birthday: 2012-03-01T,
      toys: [
        ball::{ type: rubber, size: cm::25 },
        rope,
        ball::{ type: squeaky, size: cm::15 },
      ],
      weight: pounds::41.2,
      buzz: {{VG8gaW5maW5pdHkuLi4gYW5kIGJleW9uZCE=}},
    }
    "#,
    r#"
    {
      name: "Fido",
      age: years::5,
      birthday: 2012-03-01T,
      toys: [
        rope,
        ball::{ type: squeaky, size: cm::20 },
      ],
      weight: kg::41.2,
      buzz: {{VG8gaW5maW5pdHkuLi4gYW5kIGJleW9uZCE=}},
    }
    "#,
    r#"
      value_modified::{path: (age), old: 4, new: 5}
      removed::{path: (toys 0), old: ball::{type: rubber, size: cm::25}}
      moved::{old_path: (toys 1), new_path: (toys 0), value: rope}
      value_modified::{path: (toys 2 size), old: 15, new: 20}
      moved::{old_path: (toys 2), new_path: (toys 1), value: ball::{type: squeaky, size: cm::20}}
      annotations_modified::{path: (weight), old: pounds::null, new: kg::null}
    "#
    )]
    fn test_element_diffs(#[case] old: &str, #[case] new: &str, #[case] diff: &str) {
        let e1 = Element::read_one(old).unwrap();
        let e2 = Element::read_one(new).unwrap();

        let expected_diff_ion = Element::read_all(diff).unwrap();

        let mut d = DefaultChangeListener::default();
        Element::diff_with_delegate(&mut d, &e1, &e2, );
        let actual_diff_ion: Vec<Element> = d
            .calls
            .iter()
            .filter(|x| !matches!(x, Unchanged(_, _)))
            .map(|x| x.into())
            .collect::<Vec<_>>();
        let actual_diff_ion_for_display: Vec<Element> = d
            .calls
            .iter()
            .map(|x| x.into())
            .collect::<Vec<_>>();

        assert_eq!(
            expected_diff_ion,
            actual_diff_ion,
            "Expected: {}\n Actual: {}",
            display_for_assertion(&expected_diff_ion),
            display_for_assertion(&actual_diff_ion_for_display)
        )
    }

    fn display_for_assertion(elements: &Vec<Element>) -> String {
        let mut s = String::new();
        for e in elements {
            s.push_str(&*format!("\n  {e}"));
        }
        s
    }
}
