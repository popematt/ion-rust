// Copyright Amazon.com, Inc. or its affiliates.

use std::cmp::Ordering;
use crate::ion_diff::{ChangeListener, Diffable, Key};
use crate::{Element, IonType, Symbol};
use std::collections::{BTreeMap, BTreeSet};
use crate::ion_diff::diff::patience::{Diff, Equal, Unequal};
use crate::ion_diff::ord_element::OrdElement;

impl Diffable for Element {
    fn diff_with_delegate<'a, D: ChangeListener<'a>>(d: &mut D, left: &'a Self, right: &'a Self) {
        diff_element(left, right, d);
    }
}

impl Diffable for Vec<&Element> {
    fn diff_with_delegate<'a, D: ChangeListener<'a>>(d: &mut D, left: &'a Self, right: &'a Self) {
        diff_sequence(&left, &right, d);
    }
}


fn diff_element<'a, D>(l: &'a Element, r: &'a Element, d: &mut D)
    where
        D: ChangeListener<'a>,
{
    diff_annotations(l, r, d);
    match (l.ion_type(), r.ion_type()) {
        // two equal
        (_, _) if l == r => d.unchanged(l),
        (IonType::SExp, IonType::SExp) |
        (IonType::List, IonType::List) => {
            diff_sequence(&l.as_sequence().unwrap().elements().collect(), &r.as_sequence().unwrap().elements().collect(), d);
        }
        (IonType::Struct, IonType::Struct) => {
            diff_fields(l.as_struct().unwrap().fields(), r.as_struct().unwrap().fields(), d);
        }
        // Two unequal, at least one is a scalar OR they are different container types
        (_, _) => {
            if l.value() != r.value() {
                d.value_modified(l.value(), r.value())
            }
        }
    }
}

fn diff_annotations<'a, D: ChangeListener<'a>>(l: &'a Element, r: &'a Element, d: &mut D) {
    let la: Vec<_> = l.annotations().cloned().collect();
    let ra: Vec<_> = r.annotations().cloned().collect();
    if la != ra {
        d.annotations_modified(la, ra);
    }
}

fn diff_fields<'a, I: Iterator<Item = (&'a Symbol, &'a Element)> + 'a, D: ChangeListener<'a>>(
    li: I,
    ri: I,
    d: &mut D,
) {
    let mut sl: BTreeMap<&Symbol, Vec<OrdElement>> = BTreeMap::new();
    for (k, element) in li {
        sl.entry(k).or_insert_with(Vec::new).push(element.into());
    }
    sl.iter_mut().for_each(|(_, vec)| vec.sort());
    let mut sr: BTreeMap<&Symbol, Vec<OrdElement>> = BTreeMap::new();
    for (k, element) in ri {
        sr.entry(k).or_insert_with(Vec::new).push(element.into());
    }
    sr.iter_mut().for_each(|(_, vec)| vec.sort());

    let mut all_keys : BTreeSet<&Symbol> = BTreeSet::new();
    all_keys.extend(sl.keys());
    all_keys.extend(sr.keys());

    for field_name in all_keys {
        let k: Key = field_name.into();
        match (sl.remove(field_name), sr.remove(field_name)) {
            (Some(mut lv), Some(mut rv)) => {
                if lv.len() == 1 && rv.len() == 1 {
                    d.push(&k);
                    diff_element(lv.pop().unwrap().into(), rv.pop().unwrap().into(), d);
                    d.pop();
                } else {
                    diff_for_repeated_field_name(field_name, &lv, &rv, d);
                }
            }
            (Some(lv), None) => {
                for x in lv {
                    d.removed(&k, x.into());
                }
            }
            (None, Some(rv)) => {
                for x in rv {
                    d.added(&k, x.into());
                }
            }
            (None, None) => unreachable!("The key must be in at least one of the maps")
        }
    }
}

fn diff_for_repeated_field_name<'a, 'b, D: ChangeListener<'a>>(field_name: &'a Symbol, lv: &'b Vec<OrdElement<'a>>, rv: &'b Vec<OrdElement<'a>>, d: &mut D) {
    let k: Key = field_name.into();
    let mut l_iter = lv.iter();
    let mut r_iter = rv.iter();
    let mut l_curr = l_iter.next();
    let mut r_curr = r_iter.next();
    loop {
        match (l_curr, r_curr) {
            (None, None) => { return; }
            (Some(&v), None) => { d.removed(&k, v.into()); break; }
            (None, Some(&v)) => { d.added(&k, v.into()); break; }
            (Some(&l), Some(&r)) => {
                let o = l.cmp(&r);
                match o {
                    Ordering::Less => {
                        d.removed(&k, l.into());
                        l_curr = l_iter.next();
                    }
                    Ordering::Equal => {
                        d.push(&k);
                        d.unchanged(r.into());
                        d.pop();
                        r_curr = r_iter.next();
                        l_curr = l_iter.next();
                    }
                    Ordering::Greater => {
                        d.added(&k, r.into());
                        r_curr = r_iter.next();
                    }
                }
            }
        }
    }

    // Only one of these iterators can still have anything left at this point.

    while let Some (&l) = l_iter.next() {
        d.removed(&k, l.into())
    }
    while let Some (&r) = r_iter.next() {
        d.added(&k, r.into())
    }
}

fn diff_sequence<'a, D: ChangeListener<'a>>(
    li: &Vec<&'a Element>,
    ri: &Vec<&'a Element>,
    d: &mut D,
) {
    let l_ord_elements: Vec<OrdElement> = li.iter().map(OrdElement::from).collect();
    let r_ord_elements: Vec<OrdElement> = ri.iter().map(OrdElement::from).collect();

    let diff_chunks = patience::patience_diff(l_ord_elements.as_slice(), r_ord_elements.as_slice());

    for chunk in diff_chunks {
        match chunk {
            Diff::Equal(Equal { l_start, r_start, len }) => {
                if l_start == r_start {
                    for i in 0..len {
                        d.push(&i.into());
                        d.unchanged(li.get(l_start + i).unwrap());
                        d.pop()
                    }
                } else {
                    for i in 0..len {
                        d.moved(&(i + l_start).into(), &(i + r_start).into(), li.get(i + l_start).unwrap());
                    }
                }
            }
            Diff::Unequal(Unequal { l_start, l_len, r_start, r_len }) => {
                // TODO: heuristics (maybe _another_ patience-style diff) to see if there are similar
                // items (i.e. only the annotations have changed, or a single field was added to a nested struct)
                if l_len != r_len {
                    for i in l_start..(l_start + l_len) {
                        d.removed(&i.into(), li.get(i).unwrap());
                    }
                    for i in r_start..(r_start + r_len) {
                        d.added(&i.into(), ri.get(i).unwrap());
                    }
                } else {
                    for i in 0..l_len {
                        d.push(&(i + l_start).into());
                        diff_element(li.get(i + l_start).unwrap(), ri.get(i + r_start).unwrap(), d);
                        d.pop();
                        if l_start != r_start {
                            d.moved(&(i + l_start).into(), &(i + r_start).into(), ri.get(i + r_start).unwrap())
                        }
                    }
                }

            }
        }
    }
}


// 1. Match the first lines of both if they're identical, then match the second, third, etc. until a pair doesn't match.
// 2. Match the last lines of both if they're identical, then match the next to last, second to last, etc. until a pair doesn't match.
// 3. Find all lines which occur exactly once on both sides, then do longest common subsequence on those lines, matching them up.
// 4. Do steps 1-2 on each section between matched lines
mod patience {
    use std::cmp::{max, min, Ordering};
    use std::collections::BTreeMap;

    #[derive(Default, Debug)]
    struct MatchCounts {
        l_count: usize,
        r_count: usize,
        l_line: Option<usize>,
        r_line: Option<usize>,
    }

    #[derive(PartialEq, Debug, Clone, Copy)]
    struct MatchedIndices(usize, usize);
    impl PartialOrd for MatchedIndices {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            match (self.0.cmp(&other.0), self.1.cmp(&other.1)) {
                (x, y) if x == y => Some(x),
                (_, _) => None,
            }
        }
    }

    #[derive(PartialEq, PartialOrd, Ord,Eq, Debug, Copy, Clone)]
    pub struct Equal {
        pub l_start: usize,
        pub r_start: usize,
        pub len: usize,
    }
    #[derive(PartialEq, Debug, Copy, Clone)]
    pub struct Unequal {
        pub l_start: usize,
        pub l_len: usize,
        pub r_start: usize,
        pub r_len: usize,
    }
    #[derive(PartialEq, Debug, Copy, Clone)]
    pub enum Diff {
        Equal(Equal),
        Unequal(Unequal),
    }

    pub fn patience_diff<T: Ord>(l: &[T], r: &[T]) -> Vec<Diff> {

        // Deal with some trivial cases
        // Both empty
        if l.is_empty() && r.is_empty() {
            return vec![]
        }
        // One empty
        if l.is_empty() || r.is_empty() {
            return vec![
                Diff::Unequal(Unequal {
                    l_start: 0,
                    l_len: l.len(),
                    r_start: 0,
                    r_len: r.len(),
                })
            ]
        }

        let mut equal_sections: Vec<Equal> = vec![];
        if l[0] == r[0] {
            // Find longest common subsequence from start
            let start_lcs = find_longest_common_subsequence_for_position((0, 0), l, r);
            let Equal { len: start_lcs_len, .. } = start_lcs.clone();

            // If both sides equal, return now.
            if start_lcs_len == r.len() && start_lcs_len == l.len() {
                return vec![Diff::Equal(start_lcs)];
            }

            // If one side is append only at end, add Unequal and return
            if start_lcs_len == r.len() || start_lcs_len == l.len() {
                return vec![
                    Diff::Equal(start_lcs),
                    Diff::Unequal(Unequal {
                        l_start: start_lcs_len,
                        l_len: l.len() - start_lcs_len,
                        r_start: start_lcs_len,
                        r_len: r.len() - start_lcs_len,
                    })
                ];
            }

            equal_sections.push(start_lcs)
        }
        if l[l.len() - 1] == r[r.len() - 1] {
            let end_lcs = find_longest_common_subsequence_for_position((l.len() - 1, r.len() - 1), l, r);
            equal_sections.push(end_lcs);
        }

        // Find unique matches
        let unique_matches = find_unique_matching_elements(l, r);
        // This is the patience part of the patience diff -- find the longest increasing subsequence of unique matches
        let longest_increasing_unique_matches = longest_increasing_subsequence(unique_matches);

        // Turn the unique matches into longest matching subsequence
        for m in longest_increasing_unique_matches {
            if !is_in_any_diff_range(&m, &equal_sections) {
                let MatchedIndices(a, b) = m;
                equal_sections.push(find_longest_common_subsequence_for_position((a, b), l, r))
            }
        }
        equal_sections.sort();

        if equal_sections.is_empty() {
            return vec![
                Diff::Unequal(Unequal {
                    l_start: 0,
                    l_len: l.len(),
                    r_start: 0,
                    r_len: r.len(),
                })
            ]
        }

        // Now we go and create the [Unequal]s to fill in the gaps between the [Equal]s.
        // Also clean up any overlapping equal sequences. (E.g. "abcde" and "abcd_bcde")
        let mut chunks_iter = equal_sections.iter();
        let mut previous = Equal { l_start: 0, r_start: 0, len: 0 };
        let mut diffs: Vec<Diff> = vec![];
        while let Some(current) = chunks_iter.next() {
            let l_unequal_len: isize = (current.l_start - (previous.l_start + previous.len)) as isize;
            let r_unequal_len: isize = (current.r_start - (previous.r_start + previous.len)) as isize;
            if previous.len > 0 {
                diffs.push(Diff::Equal(previous.clone()));
            }
            if l_unequal_len > 0 || r_unequal_len > 0 {
                diffs.push(Diff::Unequal(Unequal{
                    l_start: previous.l_start + previous.len,
                    l_len: max(l_unequal_len, 0) as usize,
                    r_start: previous.r_start + previous.len,
                    r_len: max(r_unequal_len, 0) as usize,
                }))
            }
            previous = if l_unequal_len < 0 || r_unequal_len < 0 {
                let overlap_correction = min(l_unequal_len, r_unequal_len).abs() as usize;
                let Equal { l_start, r_start, len }  = current;
                Equal {
                    l_start: l_start + overlap_correction,
                    r_start: r_start + overlap_correction,
                    len: len - overlap_correction,
                }
            } else {
                *current
            };
        }
        let l_unequal_len = l.len() - (previous.l_start + previous.len);
        let r_unequal_len = r.len() - (previous.r_start + previous.len);
        diffs.push(Diff::Equal(previous));
        if l_unequal_len > 0 || r_unequal_len > 0 {
            diffs.push(Diff::Unequal(Unequal{
                l_start: previous.l_start + previous.len,
                l_len: max(l_unequal_len, 0),
                r_start: previous.r_start + previous.len,
                r_len: max(r_unequal_len, 0),
            }))
        }
        diffs
    }

    fn is_in_any_diff_range(m: &MatchedIndices, diffs: &Vec<Equal>) -> bool {
        for d in diffs {
            if d.l_start <= m.0 && m.0 < d.l_start + d.len {
                return true;
            }
            if d.r_start <= m.1 && m.1 < d.r_start + d.len {
                return true;
            }
        }
        false
    }

    mod test_patience_diff {
            use rstest::*;
            use crate::ion_diff::diff::patience::{Diff, Equal, patience_diff, Unequal};

        #[rstest]
        #[case::empty("", "", "\n")]
        #[case::equal("abc", "abc", "abc\nabc")]
        #[case::entirely_unequal("abc", "def", "abc   \n   def")]
        #[case::add_in_middle("abcd", "abXcd", "ab cd\nabXcd")]
        #[case::append("abcd", "abcdefg", "abcd   \nabcdefg")]
        #[case::prepend("defg", "abcdefg", "   defg\nabcdefg")]
        #[case::add_all("", "abcdefg", "       \nabcdefg")]
        #[case::delete_beginning("abcdefg", "defg", "abcdefg\n   defg")]
        #[case::delete_end("abcdefg", "abcd", "abcdefg\nabcd   ")]
        #[case::delete_middle("abcdefg", "abfg", "abcdefg\nab   fg")]
        #[case::delete_all("abcde", "", "abcde\n     ")]
        fn test_p_diff(#[case] left: &str, #[case] right: &str, #[case] expected: &str) {
            let result = patience_diff(left.as_bytes(), right.as_bytes());

            println!("{result:?}");

            let o = left.chars().collect::<Vec<_>>();
            let n = right.chars().collect::<Vec<_>>();
            let mut old = String::new();
            let mut new = String::new();
            let mut d = String::new();
            for chunk in result {
                match chunk {
                    Diff::Equal(Equal { l_start, r_start, len }) => {
                        for i in 0..len {
                            old.push(*o.get(l_start + i).unwrap());
                            new.push(*n.get(r_start + i).unwrap());
                            d.push(' ');
                        }
                    }
                    Diff::Unequal(Unequal { l_start, l_len, r_start, r_len }) => {
                        for i in 0..l_len {
                            old.push(*o.get(l_start + i).unwrap());
                            new.push(' ');
                            d.push('-');
                        }
                        for i in 0..r_len {
                            new.push(*n.get(r_start + i).unwrap());
                            old.push(' ');
                            d.push('+');
                        }
                    }
                }
            }

            // println!("\x1b[93mError\x1b[0m");

            println!("{old}\n{d}\n{new}");
            assert_eq!(expected, format!("{old}\n{new}"));
        }
    }


    fn longest_increasing_subsequence<T: PartialOrd + Clone, I: IntoIterator<Item = T>>(vals: I) -> Vec<T> {
        let mut vals_iter = vals.into_iter();
        let mut stacks : Vec<Vec<(T, usize)>> = if let Some(x) = vals_iter.next() {
            vec![vec![(x, 0)]]
        } else {
            return vec![];
        };
        'outer: for x in vals_iter {
            let mut p = 0;
            for s in &mut stacks {
                let (top, _) = s.last().unwrap();
                if &x < top {
                    s.push((x.clone(), p));
                    continue 'outer;
                }
                p = s.len() - 1;
            }
            stacks.push(vec![(x, p)]);
        }

        let mut sub_sequence = vec![];
        let mut stacks_iter = stacks.iter().rev();
        let (value, mut p) = stacks_iter.next().unwrap().last().cloned().unwrap();
        sub_sequence.push(value);
        for s in stacks_iter {
            let (value, p0) = s.get(p).unwrap();
            p = *p0;
            sub_sequence.push(value.clone());
        }
        sub_sequence.reverse();
        sub_sequence
    }

    mod test_longest_increasing_subsequence {
        use rstest::*;
        use crate::ion_diff::diff::patience::longest_increasing_subsequence;

        #[rstest]
        #[case::foo(&[], vec![])]
        #[case::foo(&[1], vec![1])]
        #[case::foo(&[1, 2], vec![1, 2])]
        #[case::foo(&[1, 3, 2], vec![1, 2])]
        #[case::foo(&[1, 3, 2, 8, 0, 9, 5, 4, 6, 7], vec![1, 2, 4, 6, 7])]
        #[case::foo(
            &[9, 4, 6, 12, 8, 7, 1, 5, 10, 11, 3, 2, 13],
            vec![4, 6, 7, 10, 11, 13]
        )]
        fn test_lis(#[case] vals: &[u8], #[case] expected: Vec<u8>) {
            let result = longest_increasing_subsequence::<u8, _>(vals.to_owned());
            assert_eq!(expected, result);
        }
    }


    fn build_patience_sort_stacks<T: PartialOrd + Clone, I: IntoIterator<Item = T>>(vals: I) -> Vec<Vec<T>> {
        let mut vals_iter = vals.into_iter();
        let mut stacks : Vec<Vec<T>> = if let Some(x) = vals_iter.next() {
            vec![vec![x]]
        } else {
            return vec![];
        };
        'outer: for m in vals_iter {
            for s in &mut stacks {
                if &m < s.last().unwrap() {
                    s.push(m.clone());
                    continue 'outer;
                }
            }
            stacks.push(vec![m]);
        }
        return stacks;
    }

    mod test_patience_sort_stacks {
        use rstest::*;
        use crate::ion_diff::diff::patience::build_patience_sort_stacks;

        #[rstest]
        #[case::foo(&[], vec![])]
        #[case::foo(&[1], vec![vec![1]])]
        #[case::foo(&[1, 2], vec![vec![1], vec![2]])]
        #[case::foo(&[1, 3, 2], vec![vec![1], vec![3, 2]])]
        #[case::foo(&[1, 3, 2, 8, 0, 9, 5, 4, 6, 7], vec![vec![1, 0], vec![3, 2], vec![8, 5, 4], vec![9, 6], vec![7]])]
        #[case::foo(
            &[9, 4, 6, 12, 8, 7, 1, 5, 10, 11, 3, 2, 13],
            vec![vec![9, 4, 1], vec![6, 5, 3, 2], vec![12, 8, 7], vec![10], vec![11], vec![13]]
        )]
        fn test_patience(#[case] vals: &[u8], #[case] expected: Vec<Vec<u8>>) {
            let result = build_patience_sort_stacks::<u8, _>(vals.to_owned());
            assert_eq!(expected, result);
        }
    }

    fn find_longest_common_subsequence_for_position<T: Ord>(pos: (usize, usize), l: &[T], r: &[T]) -> Equal {
        let (mut l_start, mut r_start) = pos;
        if  l[l_start] != r[r_start] {
            panic!("Precondition not met! l[l_start] != r[r_start]")
        }

        let mut len = 1usize;
        while l_start > 0 && r_start > 0 {
            if  l[l_start - 1] == r[r_start - 1] {
                l_start -= 1;
                r_start -= 1;
                len += 1;
            } else {
                break;
            }
        }
        while l_start + len < l.len() && r_start + len < r.len() {
            if  l[l_start + len] == r[r_start + len] {
                len += 1;
            } else {
                break;
            }
        }
        Equal { l_start, r_start, len }
    }

    mod lcs_tests {
        use crate::ion_diff::diff::patience::{Equal, find_longest_common_subsequence_for_position};
        use rstest::*;

        #[rstest]
        #[case::foo(4, 1, 4, (4, 1), "----abcd--", "_abcd__")]
        #[case::foo(4, 1, 4, (5, 2), "----abcd--", "_abcd__")]
        #[case::foo(4, 1, 4, (6, 3), "----abcd--", "_abcd__")]
        #[case::foo(4, 1, 4, (7, 4), "----abcd--", "_abcd__")]
        #[case::foo(0, 1, 4, (0, 1), "abcd--", "_abcd__")]
        #[case::foo(2, 1, 4, (2, 1), "--abcd", "_abcd__")]
        #[case::foo(2, 3, 4, (3, 4), "--abcd-", "___abcd")]
        #[case::foo(2, 0, 4, (3, 1), "--abcd-", "abcd___")]
        fn test_lcs(#[case] l_start: usize, #[case] r_start: usize, #[case] len: usize, #[case] pos: (usize, usize), #[case] l: &str, #[case] r: &str) {
            let a = l.as_bytes();
            let b = r.as_bytes();
            let d1 = find_longest_common_subsequence_for_position(pos, a, b);
            let expected = Equal { l_start, r_start, len, };
            assert_eq!(expected, d1);
        }
    }

    fn find_unique_matching_elements<T: Ord>(l: &[T], r: &[T]) -> Vec<MatchedIndices> {
        let mut counts = BTreeMap::<&T, MatchCounts>::new();

        for (i, e) in l.iter().enumerate() {
            let mut match_info = counts.entry(e).or_default();
            match_info.l_count += 1;
            if match_info.l_line.is_none() {
                match_info.l_line = Some(i);
            }
        }

        for (i, e) in r.iter().enumerate() {
            let mut match_info = counts.entry(e).or_default();
            match_info.r_count += 1;
            if match_info.r_line.is_none() {
                match_info.r_line = Some(i);
            }
        }

        counts.into_iter()
            .filter(|(_, c)| c.l_count == 1 && c.r_count == 1)
            .map(|(_, c)| MatchedIndices(c.l_line.unwrap(), c.r_line.unwrap()))
            .collect()
    }
}


/// A struct that allows us to use a BTreeSet as an associative array but still take advantage of
/// the `intersect()` and `difference()` functions of Sets.
#[derive(Ord, PartialOrd, Eq, PartialEq)]
pub(crate) struct OrdByKey<'a>(pub Key, pub OrdElement<'a>);

impl<'a> From<(Key, &'a Element)> for OrdByKey<'a> {
    fn from(src: (Key, &'a Element)) -> Self {
        OrdByKey(src.0, OrdElement::from(src.1))
    }
}

#[derive(Ord, PartialOrd, Eq, PartialEq)]
pub(crate) struct GroupedFieldValues<'a>(pub Key, pub Vec<OrdElement<'a>>);

