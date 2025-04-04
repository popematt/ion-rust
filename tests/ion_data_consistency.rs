// Copyright Amazon.com, Inc. or its affiliates.

use ion_rs::{Element, IonData, Sequence};
use std::cmp::Ordering;
use std::fmt::Debug;

use std::fs::read;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::path::MAIN_SEPARATOR_STR as PATH_SEPARATOR;
use test_generator::test_resources;

/// Determines if the given file name is in the paths list.  This deals with platform
/// path separator differences from '/' separators in the path list.
#[inline]
fn contains_path(paths: &[&str], file_name: &str) -> bool {
    paths
        .iter()
        // TODO construct the paths in a not so hacky way
        .map(|p| p.replace('/', PATH_SEPARATOR))
        .any(|p| p == file_name)
}

const SKIP_LIST: &[&str] = &[
    "ion-tests/iontestdata/good/equivs/localSymbolTableAppend.ion",
    "ion-tests/iontestdata/good/equivs/localSymbolTableNullSlots.ion",
    "ion-tests/iontestdata/good/equivs/nonIVMNoOps.ion",
    // Integers outside the i128 range
    "ion-tests/iontestdata/good/intBigSize16.10n",
    "ion-tests/iontestdata/good/intBigSize256.ion",
    "ion-tests/iontestdata/good/intBigSize256.10n",
    "ion-tests/iontestdata/good/intBigSize512.ion",
    "ion-tests/iontestdata/good/intBigSize1201.10n",
    "ion-tests/iontestdata/good/equivs/bigInts.ion",
    "ion-tests/iontestdata/good/subfieldVarInt.ion",
    "ion-tests/iontestdata/good/equivs/intsLargePositive3.10n",
    "ion-tests/iontestdata/good/equivs/intsLargeNegative3.10n",
];

#[test_resources("ion-tests/iontestdata/good/equivs/**/*.ion")]
#[test_resources("ion-tests/iontestdata/good/equivs/**/*.10n")]
fn ion_data_eq_ord_consistency(file_name: &str) {
    // Best-effort tests to check that Eq and Ord are consistent.

    if contains_path(SKIP_LIST, file_name) {
        println!("IGNORING: {file_name}");
        return;
    }
    let data = Element::read_all(read(file_name).unwrap()).unwrap();

    for (group_index, equiv_group) in data.iter().enumerate() {
        let sequence = equiv_group.as_sequence().unwrap();
        if equiv_group.annotations().contains("embedded_documents") {
            check_group(group_index, sequence, |el| {
                Element::read_all(el.as_string().unwrap())
                    .unwrap()
                    .into_iter()
                    .map(IonData::from)
                    .collect::<Vec<_>>()
            })
        } else {
            check_group(group_index, sequence, |el| IonData::from(el.clone()))
        }
    }
}

fn check_group<T: Ord + Debug + Hash>(
    group_index: usize,
    sequence: &Sequence,
    lifter_fn: impl Fn(&Element) -> T,
) {
    for (this_index, a) in sequence.into_iter().enumerate() {
        let this = lifter_fn(a);
        let this_hash = {
            let mut h = DefaultHasher::new();
            this.hash(&mut h);
            h.finish()
        };
        for (that_index, b) in sequence.into_iter().enumerate() {
            let that = lifter_fn(b);
            let that_hash = {
                let mut h = DefaultHasher::new();
                that.hash(&mut h);
                h.finish()
            };
            assert_eq!(this, that,
                       "in group {group_index}, index {this_index} ({this:?}) was not IonData::eq to index {that_index} ({that:?})"
            );
            assert_eq!(this.cmp(&that), Ordering::Equal,
                       "in group {group_index}, index {this_index} ({this:?}) was not Ordering::Equal to index {that_index} ({that:?})"
            );
            assert_eq!(this_hash, that_hash,
                       "in group {group_index}, index {this_index} ({this:?}) did not produce the same IonData::hash as index {that_index} ({that:?})"
            );
        }
    }
}
