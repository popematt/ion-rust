use std::fs;
use std::hint::black_box;

fn main() {
    let data = fs::read("service_log_legacy.10n").unwrap();
    for _ in 0..20 {
        let result = ion_rs::bytecode::materialize::read_all_v3(&data).unwrap();
        black_box(&result);
    }
}
