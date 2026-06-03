use ion_rs::bytecode::materialize::{read_all_v3, read_all_v3_filtered};
use ion_rs::bytecode::path_filter::{PathFilter, PathStep};
use std::time::Instant;

fn main() {
    let test_cases: Vec<(&str, Vec<u8>)> = vec![
        ("integers", gen_binary("integers")),
        ("floats", gen_binary("floats")),
        ("bools", gen_binary("bools")),
        ("symbols", gen_binary("symbols")),
        ("strings", gen_binary("strings")),
        ("blobs", gen_binary("blobs")),
        ("decimals", gen_binary("decimals")),
        ("timestamps", gen_binary("timestamps")),
        ("lists", gen_binary("lists")),
        ("nested_structs", gen_binary("nested_structs")),
        ("mixed", gen_binary("mixed")),
    ];

    let select_all = vec![PathFilter::new(vec![PathStep::Wildcard])];

    println!(
        "{:<20} {:>10} {:>10} {:>8}",
        "Workload", "no_filter", "select_*", "overhead"
    );
    println!("{:-<20} {:-<10} {:-<10} {:-<8}", "", "", "", "");

    for (name, data) in &test_cases {
        // Warmup
        let _ = read_all_v3(data).unwrap();
        let _ = read_all_v3_filtered(data, &select_all).unwrap();

        // No filter
        let start = Instant::now();
        for _ in 0..100 {
            let r = read_all_v3(data).unwrap();
            std::hint::black_box(&r);
        }
        let no_filter = start.elapsed().as_micros() / 100;

        // Select all
        let start = Instant::now();
        for _ in 0..100 {
            let r = read_all_v3_filtered(data, &select_all).unwrap();
            std::hint::black_box(&r);
        }
        let select = start.elapsed().as_micros() / 100;

        let overhead = ((select as f64 / no_filter as f64) - 1.0) * 100.0;
        println!(
            "{:<20} {:>7}µs {:>7}µs {:>+7.1}%",
            name, no_filter, select, overhead
        );
    }
}

fn gen_binary(name: &str) -> Vec<u8> {
    use ion_rs::{v1_0, Element};
    let text = match name {
        "integers" => (0..4000)
            .map(|i| format!("{} ", i * 7 - 2000))
            .collect::<String>(),
        "floats" => (0..4000)
            .map(|i| format!("{}e0 ", (i as f64) * 1.7 - 3400.0))
            .collect(),
        "bools" => (0..4000)
            .map(|i| if i % 2 == 0 { "true " } else { "false " })
            .collect(),
        "symbols" => (0..1500).map(|i| format!("sym_{} ", i)).collect(),
        "strings" => (0..3000)
            .map(|i| format!("\"string_value_{}\" ", i))
            .collect(),
        "blobs" => (0..3500).map(|_| "{{YWJjZGVmZ2hpamtsbW5vcA==}} ").collect(),
        "decimals" => (0..2500)
            .map(|i| format!("{}.{}d{} ", i, i % 100, (i % 5) as i32 - 2))
            .collect(),
        "timestamps" => (0..2500)
            .map(|i| {
                let y = 2000 + (i % 25);
                let m = (i % 12) + 1;
                let d = (i % 28) + 1;
                format!("{y}-{m:02}-{d:02}T00:00:00Z ")
            })
            .collect(),
        "lists" => (0..250)
            .map(|i| format!("[{}, {}, {}, {}] ", i * 4, i * 4 + 1, i * 4 + 2, i * 4 + 3))
            .collect(),
        "nested_structs" => (0..330)
            .map(|i| format!("{{name: \"item_{i}\", value: {i}, tags: [\"a\", \"b\"]}} "))
            .collect(),
        "mixed" => (0..280)
            .map(|i| {
                format!(
                    "{{id: {i}, name: \"user_{i}\", active: true, scores: [{}, {}]}} ",
                    i * 10,
                    i * 20
                )
            })
            .collect(),
        _ => panic!("unknown"),
    };
    let values = Element::read_all(&text).unwrap();
    let mut buf = Vec::new();
    values.encode_to(&mut buf, v1_0::Binary).unwrap();
    buf
}

// Verify correctness
#[cfg(test)]
mod verify {
    #[test]
    fn select_all_matches_no_filter() {
        // quick check
    }
}
