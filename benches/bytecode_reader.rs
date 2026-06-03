use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use ion_rs::{v1_0, Element};

fn encode_as_binary(text: &str) -> Vec<u8> {
    let values = Element::read_all(text).unwrap();
    let mut buffer = Vec::new();
    values.encode_to(&mut buffer, v1_0::Binary).unwrap();
    buffer
}

fn generate_binary_data(name: &str) -> Vec<u8> {
    let text = match name {
        "integers" => {
            let mut s = String::new();
            for i in 0..4000 {
                s.push_str(&format!("{} ", i * 7 - 2000));
            }
            s
        }
        "floats" => {
            let mut s = String::new();
            for i in 0..4000 {
                s.push_str(&format!("{}e0 ", (i as f64) * 1.7 - 3400.0));
            }
            s
        }
        "bools" => {
            let mut s = String::new();
            for i in 0..4000 {
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
            for i in 0..4000 {
                s.push_str(null_types[i % null_types.len()]);
                s.push(' ');
            }
            s
        }
        "symbols" => {
            let mut s = String::new();
            for i in 0..1500 {
                s.push_str(&format!("sym_{} ", i));
            }
            s
        }
        "strings" => {
            let mut s = String::new();
            for i in 0..3000 {
                s.push_str(&format!("\"string_value_{}\" ", i));
            }
            s
        }
        "blobs" => {
            let mut s = String::new();
            for _i in 0..3500 {
                s.push_str("{{YWJjZGVmZ2hpamtsbW5vcA==}} ");
            }
            s
        }
        "decimals" => {
            let mut s = String::new();
            for i in 0..2500 {
                s.push_str(&format!("{}.{}d{} ", i, i % 100, (i % 5) as i32 - 2));
            }
            s
        }
        "timestamps" => {
            let mut s = String::new();
            for i in 0..2500 {
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
            let mut s = String::new();
            for i in 0..250 {
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
            for i in 0..330 {
                s.push_str(&format!(
                    "{{name: \"item_{i}\", value: {i}, tags: [\"a\", \"b\", \"c\"]}} "
                ));
            }
            s
        }
        "mixed" => {
            let mut s = String::new();
            for i in 0..280 {
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
            let mut s = String::new();
            for i in 0..1500 {
                s.push_str(&format!("unique_symbol_{i} "));
            }
            s
        }
        _ => panic!("unknown binary test data: {name}"),
    };
    encode_as_binary(&text)
}

fn bench_binary(c: &mut Criterion) {
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
    ];

    let mut group = c.benchmark_group("binary");
    for name in &test_cases {
        let data = generate_binary_data(name);
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
            BenchmarkId::new("bytecode_v3", format!("{name} ({data_size}B)")),
            &data,
            |b, data| {
                b.iter(|| {
                    let result = ion_rs::bytecode::materialize::read_all_v3(data).unwrap();
                    criterion::black_box(result);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("bytecode_v3_nofilter", format!("{name} ({data_size}B)")),
            &data,
            |b, data| {
                b.iter(|| {
                    let result =
                        ion_rs::bytecode::materialize::read_all_v3_with_no_filter(data).unwrap();
                    criterion::black_box(result);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new(
                "bytecode_v3_streaming_binary",
                format!("{name} ({data_size}B)"),
            ),
            &data,
            |b, data| {
                b.iter(|| {
                    let result =
                        ion_rs::bytecode::materialize::read_all_v3_streaming_binary(data).unwrap();
                    criterion::black_box(result);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("bytecode_v3_arena", format!("{name} ({data_size}B)")),
            &data,
            |b, data| {
                b.iter(|| {
                    use ion_rs::bytecode::arena_reader::ArenaReader;
                    use ion_rs::bytecode::ion10::BinaryIon10Generator;
                    let generator = BinaryIon10Generator::new(data);
                    let mut reader = ArenaReader::new(generator).unwrap();
                    while let Some(result) = reader.next() {
                        let element = result.unwrap();
                        criterion::black_box(element);
                    }
                });
            },
        );
    }
    group.finish();
}

fn bench_service_log(c: &mut Criterion) {
    let data = std::fs::read(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("service_log_legacy.10n"),
    )
    .expect("service_log_legacy.10n not found");
    let data_size = data.len();

    let mut group = c.benchmark_group("service_log");
    group.measurement_time(std::time::Duration::from_secs(10));
    group.sample_size(20);

    group.bench_with_input(
        BenchmarkId::new("current", format!("{data_size}B")),
        &data,
        |b, data| {
            b.iter(|| {
                let result = Element::read_all(data.as_slice()).unwrap();
                criterion::black_box(result);
            });
        },
    );

    group.bench_with_input(
        BenchmarkId::new("current_no_drop", format!("{data_size}B")),
        &data,
        |b, data| {
            b.iter_with_large_drop(|| Element::read_all(data.as_slice()).unwrap());
        },
    );

    group.bench_with_input(
        BenchmarkId::new("bytecode_v3", format!("{data_size}B")),
        &data,
        |b, data| {
            b.iter(|| {
                let result = ion_rs::bytecode::materialize::read_all_v3(data).unwrap();
                criterion::black_box(result);
            });
        },
    );

    group.bench_with_input(
        BenchmarkId::new("bytecode_v3_no_drop", format!("{data_size}B")),
        &data,
        |b, data| {
            b.iter_with_large_drop(|| ion_rs::bytecode::materialize::read_all_v3(data).unwrap());
        },
    );

    group.bench_with_input(
        BenchmarkId::new("bytecode_v3_streaming_binary", format!("{data_size}B")),
        &data,
        |b, data| {
            b.iter(|| {
                let result =
                    ion_rs::bytecode::materialize::read_all_v3_streaming_binary(data).unwrap();
                criterion::black_box(result);
            });
        },
    );

    group.bench_with_input(
        BenchmarkId::new("bytecode_v3_streaming_binary_no_drop", format!("{data_size}B")),
        &data,
        |b, data| {
            b.iter_with_large_drop(|| {
                ion_rs::bytecode::materialize::read_all_v3_streaming_binary(data).unwrap()
            });
        },
    );

    group.bench_with_input(
        BenchmarkId::new("bytecode_v3_arena", format!("{data_size}B")),
        &data,
        |b, data| {
            b.iter(|| {
                use ion_rs::bytecode::arena_reader::ArenaReader;
                use ion_rs::bytecode::ion10::BinaryIon10Generator;
                let generator = BinaryIon10Generator::new(data);
                let mut reader = ArenaReader::new(generator).unwrap();
                while let Some(result) = reader.next() {
                    let element = result.unwrap();
                    criterion::black_box(element);
                }
            });
        },
    );

    group.finish();
}

fn bench_service_log_filtered(c: &mut Criterion) {
    use ion_rs::bytecode::materialize::{read_all_v3, read_all_v3_query};
    use ion_rs::bytecode::path_filter::PathQuery;

    let data = std::fs::read(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("service_log_legacy.10n"),
    )
    .expect("service_log_legacy.10n not found");
    let data_size = data.len();

    let mut group = c.benchmark_group("service_log_filtered");
    group.sample_size(20);

    // Baseline: read everything with "select all" (PathQuery::all())
    let select_all = vec![PathQuery::all()];
    group.bench_with_input(
        BenchmarkId::new("path_filter_select_all", format!("{data_size}B")),
        &data,
        |b, data| {
            b.iter(|| {
                let result = read_all_v3_query(data, &select_all, false).unwrap();
                criterion::black_box(result);
            });
        },
    );

    // Baseline: standard BinaryIon10Generator (no filtering)
    group.bench_with_input(
        BenchmarkId::new("no_filter", format!("{data_size}B")),
        &data,
        |b, data| {
            b.iter(|| {
                let result = read_all_v3(data).unwrap();
                criterion::black_box(result);
            });
        },
    );

    // Selective: StartTime, Operation, Metrics.Tokens, Metrics.TotalTime.Value
    let selective_queries = vec![
        PathQuery::field("StartTime"),
        PathQuery::field("Operation"),
        PathQuery::fields(&["Metrics", "Tokens"]),
        PathQuery::fields(&["Metrics", "TotalTime", "Value"]),
    ];
    group.bench_with_input(
        BenchmarkId::new("select_4_fields", format!("{data_size}B")),
        &data,
        |b, data| {
            b.iter(|| {
                let result = read_all_v3_query(data, &selective_queries, false).unwrap();
                criterion::black_box(result);
            });
        },
    );

    // Selective + arena: path filter generator with arena materializer
    group.bench_with_input(
        BenchmarkId::new("select_4_fields_arena", format!("{data_size}B")),
        &data,
        |b, data| {
            b.iter(|| {
                use ion_rs::bytecode::arena_reader::ArenaReader;
                use ion_rs::bytecode::path_filter_generator::PathFilterGenerator;
                let generator = PathFilterGenerator::new_v2(data, &selective_queries, false);
                let mut reader = ArenaReader::new(generator).unwrap();
                while let Some(result) = reader.next() {
                    let element = result.unwrap();
                    criterion::black_box(element);
                }
            });
        },
    );

    group.finish();
}

fn bench_binary_filtered(c: &mut Criterion) {
    use ion_rs::bytecode::materialize::{read_all_v3, read_all_v3_query};
    use ion_rs::bytecode::path_filter::PathQuery;

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
    ];

    let mut group = c.benchmark_group("binary_filtered");
    group.sample_size(20);

    let select_all = vec![PathQuery::all()];

    for name in &test_cases {
        let data = generate_binary_data(name);
        let data_size = data.len();

        // PathFilterGenerator with "select all" — measures FSM overhead
        group.bench_with_input(
            BenchmarkId::new("select_all", format!("{name} ({data_size}B)")),
            &data,
            |b, data| {
                b.iter(|| {
                    let result = read_all_v3_query(data, &select_all, false).unwrap();
                    criterion::black_box(result);
                });
            },
        );

        // BinaryIon10Generator (no filter) — baseline
        group.bench_with_input(
            BenchmarkId::new("no_filter", format!("{name} ({data_size}B)")),
            &data,
            |b, data| {
                b.iter(|| {
                    let result = read_all_v3(data).unwrap();
                    criterion::black_box(result);
                });
            },
        );
    }
    group.finish();
}

fn bench_text(c: &mut Criterion) {
    let text_cases: Vec<(&str, String)> = vec![
        (
            "integers",
            (0..4000).map(|i| format!("{} ", i * 7 - 2000)).collect(),
        ),
        (
            "floats",
            (0..4000)
                .map(|i| format!("{}e0 ", (i as f64) * 1.7 - 3400.0))
                .collect(),
        ),
        (
            "bools",
            (0..4000)
                .map(|i| if i % 2 == 0 { "true " } else { "false " })
                .collect(),
        ),
        ("nulls", {
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
            (0..4000)
                .map(|i| format!("{} ", null_types[i % null_types.len()]))
                .collect()
        }),
        (
            "symbols",
            (0..1500).map(|i| format!("sym_{} ", i)).collect(),
        ),
        (
            "strings",
            (0..3000)
                .map(|i| format!("\"string_value_{}\" ", i))
                .collect(),
        ),
        (
            "decimals",
            (0..2500)
                .map(|i| format!("{}.{}d{} ", i, i % 100, (i % 5) as i32 - 2))
                .collect(),
        ),
        (
            "timestamps",
            (0..2500)
                .map(|i| {
                    let year = 2000 + (i % 25);
                    let month = (i % 12) + 1;
                    let day = (i % 28) + 1;
                    let hour = i % 24;
                    let minute = i % 60;
                    let second = i % 60;
                    format!("{year}-{month:02}-{day:02}T{hour:02}:{minute:02}:{second:02}Z ")
                })
                .collect(),
        ),
        (
            "lists",
            (0..250)
                .map(|i| {
                    format!(
                        "[[{}, {}], [{}, {}], [{}, {}], [{}, {}]] ",
                        i * 8,
                        i * 8 + 1,
                        i * 8 + 2,
                        i * 8 + 3,
                        i * 8 + 4,
                        i * 8 + 5,
                        i * 8 + 6,
                        i * 8 + 7,
                    )
                })
                .collect(),
        ),
        (
            "nested_structs",
            (0..330)
                .map(|i| {
                    format!("{{name: \"item_{i}\", value: {i}, tags: [\"a\", \"b\", \"c\"]}} ")
                })
                .collect(),
        ),
        (
            "mixed",
            (0..280)
                .map(|i| {
                    format!(
                        "{{id: {i}, name: \"user_{i}\", active: true, scores: [{}, {}, {}]}} ",
                        i * 10,
                        i * 20,
                        i * 30
                    )
                })
                .collect(),
        ),
    ];

    let mut group = c.benchmark_group("text");
    for (name, text) in &text_cases {
        let data = text.as_bytes();
        let data_size = data.len();

        group.bench_with_input(
            BenchmarkId::new("current", format!("{name} ({data_size}B)")),
            data,
            |b, data| {
                b.iter(|| {
                    let result = Element::read_all(data).unwrap();
                    criterion::black_box(result);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("bytecode_v3_str", format!("{name} ({data_size}B)")),
            data,
            |b, data| {
                b.iter(|| {
                    let result = ion_rs::bytecode::materialize::read_all_v3_str_text(data).unwrap();
                    criterion::black_box(result);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("bytecode_v3_streaming", format!("{name} ({data_size}B)")),
            data,
            |b, data| {
                b.iter(|| {
                    let result =
                        ion_rs::bytecode::materialize::read_all_v3_streaming_text(data).unwrap();
                    criterion::black_box(result);
                });
            },
        );
    }
    group.finish();
}

fn bench_fma_common_filter(c: &mut Criterion) {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("fma_common_filter.ion");
    let text_data = std::fs::read(&path).expect("fma_common_filter.ion not found");
    let text_size = text_data.len();

    let binary_data = encode_as_binary(
        std::str::from_utf8(&text_data).expect("fma_common_filter.ion is not valid UTF-8"),
    );
    let binary_size = binary_data.len();

    let mut group = c.benchmark_group("fma_common_filter");

    group.bench_with_input(
        BenchmarkId::new("current_text", format!("{text_size}B")),
        &text_data,
        |b, data| {
            b.iter(|| {
                let result = Element::read_all(data.as_slice()).unwrap();
                criterion::black_box(result);
            });
        },
    );

    group.bench_with_input(
        BenchmarkId::new("current_text_no_drop", format!("{text_size}B")),
        &text_data,
        |b, data| {
            b.iter_with_large_drop(|| Element::read_all(data.as_slice()).unwrap());
        },
    );

    group.bench_with_input(
        BenchmarkId::new("bytecode_v3_str", format!("{text_size}B")),
        &text_data,
        |b, data| {
            b.iter(|| {
                let result = ion_rs::bytecode::materialize::read_all_v3_str_text(data).unwrap();
                criterion::black_box(result);
            });
        },
    );

    group.bench_with_input(
        BenchmarkId::new("bytecode_v3_str_no_drop", format!("{text_size}B")),
        &text_data,
        |b, data| {
            b.iter_with_large_drop(|| {
                ion_rs::bytecode::materialize::read_all_v3_str_text(data).unwrap()
            });
        },
    );

    group.bench_with_input(
        BenchmarkId::new("bytecode_v3_streaming", format!("{text_size}B")),
        &text_data,
        |b, data| {
            b.iter(|| {
                let result =
                    ion_rs::bytecode::materialize::read_all_v3_streaming_text(data).unwrap();
                criterion::black_box(result);
            });
        },
    );

    group.bench_with_input(
        BenchmarkId::new("bytecode_v3_streaming_no_drop", format!("{text_size}B")),
        &text_data,
        |b, data| {
            b.iter_with_large_drop(|| {
                ion_rs::bytecode::materialize::read_all_v3_streaming_text(data).unwrap()
            });
        },
    );

    group.bench_with_input(
        BenchmarkId::new("current_binary", format!("{binary_size}B")),
        &binary_data,
        |b, data| {
            b.iter(|| {
                let result = Element::read_all(data.as_slice()).unwrap();
                criterion::black_box(result);
            });
        },
    );

    group.bench_with_input(
        BenchmarkId::new("current_binary_no_drop", format!("{binary_size}B")),
        &binary_data,
        |b, data| {
            b.iter_with_large_drop(|| Element::read_all(data.as_slice()).unwrap());
        },
    );

    group.bench_with_input(
        BenchmarkId::new("bytecode_v3_binary", format!("{binary_size}B")),
        &binary_data,
        |b, data| {
            b.iter(|| {
                let result = ion_rs::bytecode::materialize::read_all_v3(data).unwrap();
                criterion::black_box(result);
            });
        },
    );

    group.bench_with_input(
        BenchmarkId::new("bytecode_v3_binary_no_drop", format!("{binary_size}B")),
        &binary_data,
        |b, data| {
            b.iter_with_large_drop(|| ion_rs::bytecode::materialize::read_all_v3(data).unwrap());
        },
    );

    group.bench_with_input(
        BenchmarkId::new("bytecode_v3_streaming_binary", format!("{binary_size}B")),
        &binary_data,
        |b, data| {
            b.iter(|| {
                let result =
                    ion_rs::bytecode::materialize::read_all_v3_streaming_binary(data).unwrap();
                criterion::black_box(result);
            });
        },
    );

    group.bench_with_input(
        BenchmarkId::new("bytecode_v3_streaming_binary_no_drop", format!("{binary_size}B")),
        &binary_data,
        |b, data| {
            b.iter_with_large_drop(|| {
                ion_rs::bytecode::materialize::read_all_v3_streaming_binary(data).unwrap()
            });
        },
    );

    group.bench_with_input(
        BenchmarkId::new("bytecode_v3_arena", format!("{binary_size}B")),
        &binary_data,
        |b, data| {
            b.iter(|| {
                use ion_rs::bytecode::arena_reader::ArenaReader;
                use ion_rs::bytecode::ion10::BinaryIon10Generator;
                let generator = BinaryIon10Generator::new(data);
                let mut reader = ArenaReader::new(generator).unwrap();
                while let Some(result) = reader.next() {
                    let element = result.unwrap();
                    criterion::black_box(element);
                }
            });
        },
    );

    group.finish();
}

fn bench_unified_binary(c: &mut Criterion) {
    let test_cases = ["integers", "floats", "strings", "mixed", "nested_structs"];

    let mut group = c.benchmark_group("unified_binary");
    for name in &test_cases {
        let data = generate_binary_data(name);
        let data_size = data.len();

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

        group.bench_with_input(
            BenchmarkId::new("unified_in_memory", format!("{name} ({data_size}B)")),
            &data,
            |b, data| {
                b.iter(|| {
                    let result =
                        ion_rs::bytecode::materialize::read_all_v3_unified_binary(data).unwrap();
                    criterion::black_box(result);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new(
                "bytecode_v3_streaming_binary",
                format!("{name} ({data_size}B)"),
            ),
            &data,
            |b, data| {
                b.iter(|| {
                    let result =
                        ion_rs::bytecode::materialize::read_all_v3_streaming_binary(data).unwrap();
                    criterion::black_box(result);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("unified_streaming", format!("{name} ({data_size}B)")),
            &data,
            |b, data| {
                b.iter(|| {
                    let result =
                        ion_rs::bytecode::materialize::read_all_v3_unified_streaming_binary(data)
                            .unwrap();
                    criterion::black_box(result);
                });
            },
        );
    }

    // Also test with service_log if available
    let service_log_path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("service_log_legacy.10n");
    if service_log_path.exists() {
        let data = std::fs::read(&service_log_path).unwrap();
        let data_size = data.len();

        group.bench_with_input(
            BenchmarkId::new("bytecode_v3", format!("service_log ({data_size}B)")),
            &data,
            |b, data| {
                b.iter(|| {
                    let result = ion_rs::bytecode::materialize::read_all_v3(data).unwrap();
                    criterion::black_box(result);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("unified_in_memory", format!("service_log ({data_size}B)")),
            &data,
            |b, data| {
                b.iter(|| {
                    let result =
                        ion_rs::bytecode::materialize::read_all_v3_unified_binary(data).unwrap();
                    criterion::black_box(result);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new(
                "bytecode_v3_streaming_binary",
                format!("service_log ({data_size}B)"),
            ),
            &data,
            |b, data| {
                b.iter(|| {
                    let result =
                        ion_rs::bytecode::materialize::read_all_v3_streaming_binary(data).unwrap();
                    criterion::black_box(result);
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("unified_streaming", format!("service_log ({data_size}B)")),
            &data,
            |b, data| {
                b.iter(|| {
                    let result =
                        ion_rs::bytecode::materialize::read_all_v3_unified_streaming_binary(data)
                            .unwrap();
                    criterion::black_box(result);
                });
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_binary,
    bench_service_log,
    bench_service_log_filtered,
    bench_binary_filtered,
    bench_text,
    bench_fma_common_filter,
    bench_unified_binary
);
criterion_main!(benches);
