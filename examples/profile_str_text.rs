use ion_rs::bytecode::materialize::read_all_v3_str_text;

fn main() {
    let data = std::fs::read("fma_common_filter.ion").unwrap();
    for _ in 0..50000 {
        let result = read_all_v3_str_text(&data).unwrap();
        std::hint::black_box(&result);
    }
}
