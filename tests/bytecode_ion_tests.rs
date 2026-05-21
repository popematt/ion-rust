//! Integration tests running the bytecode reader against the ion-tests corpus.
//!
//! Uses `test_resources` to generate one test per file. Each test reads the
//! file with both the existing `Element::read_all` and the bytecode reader,
//! then compares the results.

use ion_rs::bytecode::materialize::{read_all_v2, read_all_v3};
use ion_rs::{Element, IonData};
use std::fs;

/// Files that are known to fail (e.g., use features not yet supported).
/// Add entries here as needed with a comment explaining why.
const SKIP_LIST: &[&str] = &[
    // LST-append (imports: $ion_symbol_table) not yet supported
    "ion-tests/iontestdata/good/localSymbolTableAppend.10n",
    "ion-tests/iontestdata/good/testfile37.10n",
    // Shared symbol table imports not supported
    "ion-tests/iontestdata/good/subfieldInt.10n",
    "ion-tests/iontestdata/good/subfieldVarInt.10n",
    "ion-tests/iontestdata/good/subfieldVarUInt.10n",
    "ion-tests/iontestdata/good/subfieldVarUInt32bit.10n",
    "ion-tests/iontestdata/good/subfieldVarUInt15bit.10n",
    "ion-tests/iontestdata/good/subfieldVarUInt16bit.10n",
];

fn should_skip(file_name: &str) -> bool {
    SKIP_LIST
        .iter()
        .any(|s| file_name.contains(s) || file_name.ends_with(s))
}

fn test_file_v2(file_name: &str) {
    if should_skip(file_name) {
        return;
    }

    let data = fs::read(file_name).unwrap();

    // Read with existing reader
    let expected = match Element::read_all(&data) {
        Ok(seq) => seq,
        Err(_) => return, // skip files the existing reader can't handle
    };

    // Read with bytecode v2
    match read_all_v2(&data) {
        Ok(actual) => {
            assert!(
                IonData::eq(&expected, &actual),
                "v2 output mismatch for {file_name}"
            );
        }
        Err(e) => {
            panic!("v2 error for {file_name}: {e}");
        }
    }
}

fn test_file_v3(file_name: &str) {
    if should_skip(file_name) {
        return;
    }

    let data = fs::read(file_name).unwrap();

    let expected = match Element::read_all(&data) {
        Ok(seq) => seq,
        Err(_) => return,
    };

    match read_all_v3(&data) {
        Ok(actual) => {
            assert!(
                IonData::eq(&expected, &actual),
                "v3 output mismatch for {file_name}"
            );
        }
        Err(e) => {
            panic!("v3 error for {file_name}: {e}");
        }
    }
}

mod binary {
    use super::*;
    use test_generator::test_resources;

    #[test_resources("ion-tests/iontestdata/good/**/*.10n")]
    fn v2(file_name: &str) {
        test_file_v2(file_name);
    }

    #[test_resources("ion-tests/iontestdata/good/**/*.10n")]
    fn v3(file_name: &str) {
        test_file_v3(file_name);
    }
}
