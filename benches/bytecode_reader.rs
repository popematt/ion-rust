use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use ion_rs::{v1_0, Element};

fn encode_as_binary(text: &str) -> Vec<u8> {
    let values = Element::read_all(text).unwrap();
    let mut buffer = Vec::new();
    values.encode_to(&mut buffer, v1_0::Binary).unwrap();
    buffer
}

fn generate_test_data(name: &str) -> Vec<u8> {
    let text = match name {
        "integers" => {
            let mut s = String::new();
            for i in 0..1000 {
                s.push_str(&format!("{} ", i * 7 - 500));
            }
            s
        }
        "floats" => {
            let mut s = String::new();
            for i in 0..1000 {
                s.push_str(&format!("{}e0 ", (i as f64) * 1.7 - 500.0));
            }
            s
        }
        "bools" => {
            let mut s = String::new();
            for i in 0..1000 {
                s.push_str(if i % 2 == 0 { "true " } else { "false " });
            }
            s
        }
        "nulls" => {
            let mut s = String::new();
            let null_types = [
                "null",
                "null.bool",
                "null.int",
                "null.float",
                "null.decimal",
                "null.timestamp",
                "null.symbol",
                "null.string",
                "null.blob",
                "null.clob",
                "null.list",
                "null.sexp",
                "null.struct",
            ];
            for i in 0..1000 {
                s.push_str(null_types[i % null_types.len()]);
                s.push(' ');
            }
            s
        }
        "symbols" => {
            let mut s = String::new();
            for i in 0..1000 {
                s.push_str(&format!("sym_{} ", i));
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
        "blobs" => {
            let mut s = String::new();
            // Each blob is 16 bytes of base64-encoded data
            for _i in 0..500 {
                s.push_str("{{YWJjZGVmZ2hpamtsbW5vcA==}} ");
            }
            s
        }
        "decimals" => {
            let mut s = String::new();
            for i in 0..1000 {
                s.push_str(&format!("{}.{}d{} ", i, i % 100, (i % 5) as i32 - 2));
            }
            s
        }
        "timestamps" => {
            let mut s = String::new();
            for i in 0..500 {
                let year = 2000 + (i % 25);
                let month = (i % 12) + 1;
                let day = (i % 28) + 1;
                let hour = i % 24;
                let minute = i % 60;
                let second = i % 60;
                s.push_str(&format!(
                    "{year}-{month:02}-{day:02}T{hour:02}:{minute:02}:{second:02}Z "
                ));
            }
            s
        }
        "lists" => {
            // Heavily nested lists of small integers
            let mut s = String::new();
            for i in 0..200 {
                s.push_str(&format!(
                    "[[{}, {}], [{}, {}], [{}, {}], [{}, {}]] ",
                    i * 8,
                    i * 8 + 1,
                    i * 8 + 2,
                    i * 8 + 3,
                    i * 8 + 4,
                    i * 8 + 5,
                    i * 8 + 6,
                    i * 8 + 7,
                ));
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
        "symbol_table_churn" => {
            // Alternates between a new local symbol table and a single
            // symbol value using that table, stressing LST handling.
            let mut s = String::new();
            for i in 0..200 {
                // Each value uses a unique symbol that forces a new LST
                s.push_str(&format!("unique_symbol_{i} "));
            }
            s
        }
        "realistic_log" => {
            let mut s = String::new();
            for i in 0..100 {
                s.push_str(&format!(
                    concat!(
                        "{{",
                        "timestamp: 2024-01-15T10:30:{sec:02}.{ms:03}Z, ",
                        "level: INFO, ",
                        "thread_id: {tid}, ",
                        "hostname: 'ec2-127-0-0-1.us-west-2.compute.amazonaws.com', ",
                        "message: \"Processing request {i}\", ",
                        "duration_ms: {dur}.{frac}, ",
                        "tags: [\"service\", \"api\", \"prod\"], ",
                        "metadata: {{request_id: \"req_{i}\", status: 200}}",
                        "}} "
                    ),
                    sec = i % 60,
                    ms = (i * 7) % 1000,
                    tid = i % 8,
                    i = i,
                    dur = i * 3,
                    frac = (i * 17) % 100,
                ));
            }
            s
        }
        _ => panic!("unknown test data: {name}"),
    };
    encode_as_binary(&text)
}

fn bench_read_all(c: &mut Criterion) {
    let test_cases = [
        "integers",
        "floats",
        "bools",
        "nulls",
        "symbols",
        "strings",
        "blobs",
        "decimals",
        "timestamps",
        "lists",
        "nested_structs",
        "mixed",
        "symbol_table_churn",
        "realistic_log",
    ];

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
            BenchmarkId::new("bytecode_v2", format!("{name} ({data_size}B)")),
            &data,
            |b, data| {
                b.iter(|| {
                    let result = ion_rs::bytecode::materialize::read_all_v2(data).unwrap();
                    criterion::black_box(result);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("bytecode_v3", format!("{name} ({data_size}B)")),
            &data,
            |b, data| {
                b.iter(|| {
                    let result = ion_rs::bytecode::materialize::read_all_v3(data).unwrap();
                    criterion::black_box(result);
                });
            },
        );
    }
    group.finish();
}

fn bench_next_only(c: &mut Criterion) {
    use ion_rs::bytecode::ion10::BinaryIon10Generator;
    use ion_rs::bytecode::reader::BytecodeReader;

    let test_cases = ["integers", "nested_structs", "mixed"];

    let mut group = c.benchmark_group("next_only");
    for name in &test_cases {
        let data = generate_test_data(name);
        let data_size = data.len();

        group.bench_with_input(
            BenchmarkId::new("bytecode", format!("{name} ({data_size}B)")),
            &data,
            |b, data| {
                b.iter(|| {
                    let generator = BinaryIon10Generator::new(data.as_slice());
                    let mut reader = BytecodeReader::with_generator(generator);
                    while reader.next().unwrap().is_some() {}
                });
            },
        );
    }
    group.finish();
}

fn bench_traverse(c: &mut Criterion) {
    use ion_rs::bytecode::ion10::BinaryIon10Generator;
    use ion_rs::bytecode::reader::BytecodeReader;

    let data = generate_test_data("nested_structs");
    let data_size = data.len();

    let mut group = c.benchmark_group("traverse");

    group.bench_with_input(
        BenchmarkId::new("skip_containers", format!("nested_structs ({data_size}B)")),
        &data,
        |b, data| {
            b.iter(|| {
                let generator = BinaryIon10Generator::new(data.to_vec());
                let mut reader = BytecodeReader::with_generator(generator);
                while reader.next().unwrap().is_some() {}
            });
        },
    );

    group.bench_with_input(
        BenchmarkId::new("step_into_all", format!("nested_structs ({data_size}B)")),
        &data,
        |b, data| {
            b.iter(|| {
                let generator = BinaryIon10Generator::new(data.to_vec());
                let mut reader = BytecodeReader::with_generator(generator);
                fn walk<G: ion_rs::bytecode::generator::BytecodeGenerator>(
                    reader: &mut BytecodeReader<G>,
                ) {
                    use ion_rs::IonType;
                    while let Some(ion_type) = reader.next().unwrap() {
                        match ion_type {
                            IonType::List | IonType::SExp | IonType::Struct => {
                                if !reader.is_null() {
                                    reader.step_in().unwrap();
                                    walk(reader);
                                    reader.step_out().unwrap();
                                }
                            }
                            _ => {}
                        }
                    }
                }
                walk(&mut reader);
            });
        },
    );

    group.finish();
}

criterion_group!(benches, bench_read_all, bench_next_only, bench_traverse);
criterion_main!(benches);
