use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use ion_rs::{v1_0, Element, IonResult, WriteConfig};

fn encode_as_binary(text: &str) -> Vec<u8> {
    let values = Element::read_all(text).unwrap();
    let mut buffer = Vec::new();
    values.encode_to(&mut buffer, v1_0::Binary).unwrap();
    buffer
}

fn generate_test_data(name: &str) -> Vec<u8> {
    // Only use types the bytecode reader fully supports:
    // null, bool, int, float, string, symbol, list, sexp, struct
    let text = match name {
        "scalars" => {
            let mut s = String::new();
            for i in 0..1000 {
                s.push_str(&format!("{} ", i));
            }
            s
        }
        "strings" => {
            let mut s = String::new();
            for i in 0..1000 {
                s.push_str(&format!("\"string_value_{}\" ", i));
            }
            s
        }
        "nested_structs" => {
            let mut s = String::new();
            for i in 0..200 {
                s.push_str(&format!(
                    "{{name: \"item_{i}\", value: {i}, tags: [\"a\", \"b\", \"c\"]}} "
                ));
            }
            s
        }
        "mixed" => {
            let mut s = String::new();
            for i in 0..200 {
                s.push_str(&format!(
                    "{{id: {i}, name: \"user_{i}\", active: true, scores: [{}, {}, {}]}} ",
                    i * 10,
                    i * 20,
                    i * 30
                ));
            }
            s
        }
        _ => panic!("unknown test data: {name}"),
    };
    encode_as_binary(&text)
}

fn bench_read_all(c: &mut Criterion) {
    let test_cases = ["scalars", "strings", "nested_structs", "mixed"];

    let mut group = c.benchmark_group("read_all");
    for name in &test_cases {
        let data = generate_test_data(name);
        let data_size = data.len();

        group.bench_with_input(
            BenchmarkId::new("current", format!("{name} ({data_size}B)")),
            &data,
            |b, data| {
                b.iter(|| {
                    let result = Element::read_all(data.as_slice()).unwrap();
                    criterion::black_box(result);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("bytecode", format!("{name} ({data_size}B)")),
            &data,
            |b, data| {
                b.iter(|| {
                    let result = ion_rs::bytecode::materialize::read_all_v2(data).unwrap();
                    criterion::black_box(result);
                });
            },
        );
    }
    group.finish();
}

criterion_group!(benches, bench_read_all);
criterion_main!(benches);
