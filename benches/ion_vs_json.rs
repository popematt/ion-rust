//! Benchmark comparing Ion binary (bytecode reader) vs JSON (serde_json + simd-json).
//!
//! Two datasets:
//! - "log_1000": 1000 identical 7-field structs (compiled in via include_bytes)
//! - "service_log": ~59K real-world 28-field structs (loaded at runtime)
//!
//! Dimensions:
//! - Owned DOM: serde_json::Value vs simd_json::OwnedValue vs bytecode→Element
//! - Arena DOM: simd_json::BorrowedValue vs bytecode ArenaReader
//! - Path filter: parse-all + get field vs bytecode path filter (skip at source)

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use simd_json::prelude::*;

static ION_SMALL: &[u8] = include_bytes!("data/log_1000.10n");
static JSON_SMALL: &str = include_str!("data/log_1000.json");
static ION_NESTED: &[u8] = include_bytes!("data/nested_structs_1000.10n");
static JSON_NESTED: &str = include_str!("data/nested_structs_1000.json");
static ION_EMF: &[u8] = include_bytes!("data/emf_1000.10n");
static JSON_EMF: &str = include_str!("data/emf_1000.json");

fn load_service_log() -> (Vec<u8>, String) {
    let ion_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("service_log_legacy.10n");
    let json_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("benches/data/service_log_legacy.json");
    let ion = std::fs::read(&ion_path).expect("service_log_legacy.10n not found");
    let json = std::fs::read_to_string(&json_path)
        .expect("benches/data/service_log_legacy.json not found");
    (ion, json)
}

/// Count newline-delimited JSON values.
fn json_line_count(json: &str) -> usize {
    json.lines().count()
}

// ─── Owned DOM ───────────────────────────────────────────────────────────────

fn bench_owned_dom(c: &mut Criterion) {
    let (ion_large, json_large) = load_service_log();
    let large_count = json_line_count(&json_large);

    let mut group = c.benchmark_group("owned_dom");

    // Small dataset
    group.throughput(Throughput::Bytes(JSON_SMALL.len() as u64));
    group.bench_function("serde_json [log_1000]", |b| {
        b.iter(|| {
            let mut count = 0usize;
            for line in JSON_SMALL.lines() {
                let v: serde_json::Value = serde_json::from_str(line).unwrap();
                black_box(&v);
                count += 1;
            }
            assert_eq!(count, 1000);
        })
    });

    group.throughput(Throughput::Bytes(JSON_SMALL.len() as u64));
    group.bench_function("simd_json [log_1000]", |b| {
        b.iter(|| {
            let mut count = 0usize;
            for line in JSON_SMALL.lines() {
                let mut bytes = line.as_bytes().to_vec();
                let v: simd_json::OwnedValue = simd_json::to_owned_value(&mut bytes).unwrap();
                black_box(&v);
                count += 1;
            }
            assert_eq!(count, 1000);
        })
    });

    group.throughput(Throughput::Bytes(ION_SMALL.len() as u64));
    group.bench_function("ion bytecode [log_1000]", |b| {
        b.iter(|| {
            let seq = ion_rs::bytecode::materialize::read_all_v3(ION_SMALL).unwrap();
            assert_eq!(seq.len(), 1000);
            black_box(&seq);
        })
    });

    // Large dataset (service_log)
    group.sample_size(10);

    group.throughput(Throughput::Bytes(json_large.len() as u64));
    group.bench_function("serde_json [service_log]", |b| {
        b.iter(|| {
            let mut count = 0usize;
            for line in json_large.lines() {
                let v: serde_json::Value = serde_json::from_str(line).unwrap();
                black_box(&v);
                count += 1;
            }
            assert_eq!(count, large_count);
        })
    });

    group.throughput(Throughput::Bytes(json_large.len() as u64));
    group.bench_function("simd_json [service_log]", |b| {
        b.iter(|| {
            let mut count = 0usize;
            for line in json_large.lines() {
                let mut bytes = line.as_bytes().to_vec();
                let v: simd_json::OwnedValue = simd_json::to_owned_value(&mut bytes).unwrap();
                black_box(&v);
                count += 1;
            }
            assert_eq!(count, large_count);
        })
    });

    group.throughput(Throughput::Bytes(ion_large.len() as u64));
    group.bench_function("ion bytecode [service_log]", |b| {
        b.iter(|| {
            let seq = ion_rs::bytecode::materialize::read_all_v3(ion_large.as_slice()).unwrap();
            black_box(&seq);
        })
    });

    // FMA dataset (deeply nested, 1000 values)
    group.sample_size(100);

    group.throughput(Throughput::Bytes(JSON_NESTED.len() as u64));
    group.bench_function("serde_json [nested]", |b| {
        b.iter(|| {
            let mut count = 0usize;
            for line in JSON_NESTED.lines() {
                let v: serde_json::Value = serde_json::from_str(line).unwrap();
                black_box(&v);
                count += 1;
            }
            assert_eq!(count, 1000);
        })
    });

    group.throughput(Throughput::Bytes(JSON_NESTED.len() as u64));
    group.bench_function("simd_json [nested]", |b| {
        b.iter(|| {
            let mut count = 0usize;
            for line in JSON_NESTED.lines() {
                let mut bytes = line.as_bytes().to_vec();
                let v: simd_json::OwnedValue =
                    simd_json::to_owned_value(&mut bytes).unwrap();
                black_box(&v);
                count += 1;
            }
            assert_eq!(count, 1000);
        })
    });

    group.throughput(Throughput::Bytes(ION_NESTED.len() as u64));
    group.bench_function("ion bytecode [nested]", |b| {
        b.iter(|| {
            let seq = ion_rs::bytecode::materialize::read_all_v3(ION_NESTED).unwrap();
            assert_eq!(seq.len(), 1000);
            black_box(&seq);
        })
    });

    // EMF dataset (CloudWatch embedded metrics, 1000 values)
    group.throughput(Throughput::Bytes(JSON_EMF.len() as u64));
    group.bench_function("serde_json [emf]", |b| {
        b.iter(|| {
            let mut count = 0usize;
            for line in JSON_EMF.lines() {
                let v: serde_json::Value = serde_json::from_str(line).unwrap();
                black_box(&v);
                count += 1;
            }
            assert_eq!(count, 1000);
        })
    });

    group.throughput(Throughput::Bytes(JSON_EMF.len() as u64));
    group.bench_function("simd_json [emf]", |b| {
        b.iter(|| {
            let mut count = 0usize;
            for line in JSON_EMF.lines() {
                let mut bytes = line.as_bytes().to_vec();
                let v: simd_json::OwnedValue =
                    simd_json::to_owned_value(&mut bytes).unwrap();
                black_box(&v);
                count += 1;
            }
            assert_eq!(count, 1000);
        })
    });

    group.throughput(Throughput::Bytes(ION_EMF.len() as u64));
    group.bench_function("ion bytecode [emf]", |b| {
        b.iter(|| {
            let seq = ion_rs::bytecode::materialize::read_all_v3(ION_EMF).unwrap();
            assert_eq!(seq.len(), 1000);
            black_box(&seq);
        })
    });

    group.finish();
}

// ─── Arena DOM ───────────────────────────────────────────────────────────────

fn bench_arena_dom(c: &mut Criterion) {
    use ion_rs::bytecode::arena_reader::ArenaReader;
    use ion_rs::bytecode::ion10::BinaryIon10Generator;

    let (ion_large, json_large) = load_service_log();
    let large_count = json_line_count(&json_large);

    let mut group = c.benchmark_group("arena_dom");

    // Small dataset
    group.throughput(Throughput::Bytes(JSON_SMALL.len() as u64));
    group.bench_function("simd_json::BorrowedValue [log_1000]", |b| {
        b.iter(|| {
            let mut count = 0usize;
            for line in JSON_SMALL.lines() {
                let mut bytes = line.as_bytes().to_vec();
                let v: simd_json::BorrowedValue = simd_json::to_borrowed_value(&mut bytes).unwrap();
                black_box(&v);
                count += 1;
            }
            assert_eq!(count, 1000);
        })
    });

    group.throughput(Throughput::Bytes(ION_SMALL.len() as u64));
    group.bench_function("ion ArenaReader [log_1000]", |b| {
        b.iter(|| {
            let generator = BinaryIon10Generator::new(ION_SMALL);
            let mut reader = ArenaReader::new(generator).unwrap();
            let mut count = 0usize;
            while let Some(result) = reader.next() {
                black_box(result.unwrap());
                count += 1;
            }
            assert_eq!(count, 1000);
        })
    });

    // Large dataset (service_log)
    group.sample_size(10);

    group.throughput(Throughput::Bytes(json_large.len() as u64));
    group.bench_function("simd_json::BorrowedValue [service_log]", |b| {
        b.iter(|| {
            let mut count = 0usize;
            for line in json_large.lines() {
                let mut bytes = line.as_bytes().to_vec();
                let v: simd_json::BorrowedValue = simd_json::to_borrowed_value(&mut bytes).unwrap();
                black_box(&v);
                count += 1;
            }
            assert_eq!(count, large_count);
        })
    });

    group.throughput(Throughput::Bytes(ion_large.len() as u64));
    group.bench_function("ion ArenaReader [service_log]", |b| {
        b.iter(|| {
            let generator = BinaryIon10Generator::new(ion_large.as_slice());
            let mut reader = ArenaReader::new(generator).unwrap();
            let mut count = 0usize;
            while let Some(result) = reader.next() {
                black_box(result.unwrap());
                count += 1;
            }
            black_box(count);
        })
    });

    // FMA dataset
    group.sample_size(100);

    group.throughput(Throughput::Bytes(JSON_NESTED.len() as u64));
    group.bench_function("simd_json::BorrowedValue [nested]", |b| {
        b.iter(|| {
            let mut count = 0usize;
            for line in JSON_NESTED.lines() {
                let mut bytes = line.as_bytes().to_vec();
                let v: simd_json::BorrowedValue =
                    simd_json::to_borrowed_value(&mut bytes).unwrap();
                black_box(&v);
                count += 1;
            }
            assert_eq!(count, 1000);
        })
    });

    group.throughput(Throughput::Bytes(ION_NESTED.len() as u64));
    group.bench_function("ion ArenaReader [nested]", |b| {
        b.iter(|| {
            let generator = BinaryIon10Generator::new(ION_NESTED);
            let mut reader = ArenaReader::new(generator).unwrap();
            let mut count = 0usize;
            while let Some(result) = reader.next() {
                black_box(result.unwrap());
                count += 1;
            }
            assert_eq!(count, 1000);
        })
    });

    // EMF dataset
    group.throughput(Throughput::Bytes(JSON_EMF.len() as u64));
    group.bench_function("simd_json::BorrowedValue [emf]", |b| {
        b.iter(|| {
            let mut count = 0usize;
            for line in JSON_EMF.lines() {
                let mut bytes = line.as_bytes().to_vec();
                let v: simd_json::BorrowedValue =
                    simd_json::to_borrowed_value(&mut bytes).unwrap();
                black_box(&v);
                count += 1;
            }
            assert_eq!(count, 1000);
        })
    });

    group.throughput(Throughput::Bytes(ION_EMF.len() as u64));
    group.bench_function("ion ArenaReader [emf]", |b| {
        b.iter(|| {
            let generator = BinaryIon10Generator::new(ION_EMF);
            let mut reader = ArenaReader::new(generator).unwrap();
            let mut count = 0usize;
            while let Some(result) = reader.next() {
                black_box(result.unwrap());
                count += 1;
            }
            assert_eq!(count, 1000);
        })
    });

    group.finish();
}

// ─── Single / Multi Field Access ─────────────────────────────────────────────

fn bench_field_access(c: &mut Criterion) {
    use ion_rs::bytecode::path_filter::PathQuery;

    let (ion_large, json_large) = load_service_log();
    let large_count = json_line_count(&json_large);

    let mut group = c.benchmark_group("field_access");

    // --- Small: single field "format" ---

    group.throughput(Throughput::Bytes(JSON_SMALL.len() as u64));
    group.bench_function("serde_json 1 field [log_1000]", |b| {
        b.iter(|| {
            let mut count = 0usize;
            for line in JSON_SMALL.lines() {
                let v: serde_json::Value = serde_json::from_str(line).unwrap();
                black_box(v.get("format").unwrap());
                count += 1;
            }
            assert_eq!(count, 1000);
        })
    });

    group.throughput(Throughput::Bytes(JSON_SMALL.len() as u64));
    group.bench_function("simd_json 1 field [log_1000]", |b| {
        b.iter(|| {
            let mut count = 0usize;
            for line in JSON_SMALL.lines() {
                let mut bytes = line.as_bytes().to_vec();
                let v: simd_json::OwnedValue = simd_json::to_owned_value(&mut bytes).unwrap();
                black_box(v.get("format").unwrap());
                count += 1;
            }
            assert_eq!(count, 1000);
        })
    });

    let query_small = vec![PathQuery::field("format")];
    group.throughput(Throughput::Bytes(ION_SMALL.len() as u64));
    group.bench_function("ion path filter 1 field [log_1000]", |b| {
        b.iter(|| {
            let seq =
                ion_rs::bytecode::materialize::read_all_v3_query(ION_SMALL, &query_small, false)
                    .unwrap();
            assert_eq!(seq.len(), 1000);
            black_box(&seq);
        })
    });

    // --- Large: 4 fields (including nested) from service_log ---
    group.sample_size(10);

    let queries = vec![
        PathQuery::field("StartTime"),
        PathQuery::field("Operation"),
        PathQuery::fields(&["Metrics", "Tokens"]),
        PathQuery::fields(&["Metrics", "TotalTime", "Value"]),
    ];

    group.throughput(Throughput::Bytes(json_large.len() as u64));
    group.bench_function("serde_json 4 fields [service_log]", |b| {
        b.iter(|| {
            let mut count = 0usize;
            for line in json_large.lines() {
                let v: serde_json::Value = serde_json::from_str(line).unwrap();
                black_box(v.get("StartTime"));
                black_box(v.get("Operation"));
                if let Some(m) = v.get("Metrics") {
                    black_box(m.get("Tokens"));
                    if let Some(tt) = m.get("TotalTime") {
                        black_box(tt.get("Value"));
                    }
                }
                count += 1;
            }
            assert_eq!(count, large_count);
        })
    });

    group.throughput(Throughput::Bytes(json_large.len() as u64));
    group.bench_function("simd_json 4 fields [service_log]", |b| {
        b.iter(|| {
            let mut count = 0usize;
            for line in json_large.lines() {
                let mut bytes = line.as_bytes().to_vec();
                let v: simd_json::OwnedValue = simd_json::to_owned_value(&mut bytes).unwrap();
                black_box(v.get("StartTime"));
                black_box(v.get("Operation"));
                if let Some(m) = v.get("Metrics") {
                    black_box(m.get("Tokens"));
                    if let Some(tt) = m.get("TotalTime") {
                        black_box(tt.get("Value"));
                    }
                }
                count += 1;
            }
            assert_eq!(count, large_count);
        })
    });

    group.throughput(Throughput::Bytes(ion_large.len() as u64));
    group.bench_function("ion path filter 4 fields [service_log]", |b| {
        b.iter(|| {
            let seq = ion_rs::bytecode::materialize::read_all_v3_query(
                ion_large.as_slice(),
                &queries,
                false,
            )
            .unwrap();
            black_box(&seq);
        })
    });

    // Ion path filter + arena for service_log
    group.throughput(Throughput::Bytes(ion_large.len() as u64));
    group.bench_function("ion path filter + arena 4 fields [service_log]", |b| {
        use ion_rs::bytecode::arena_reader::ArenaReader;
        use ion_rs::bytecode::path_filter_generator::PathFilterGenerator;
        b.iter(|| {
            let generator = PathFilterGenerator::new_v2(ion_large.as_slice(), &queries, false);
            let mut reader = ArenaReader::new(generator).unwrap();
            while let Some(result) = reader.next() {
                black_box(result.unwrap());
            }
        })
    });

    group.finish();
}

// ─── Tape / Scan (no DOM construction) ───────────────────────────────────────

fn bench_tape_scan(c: &mut Criterion) {
    use ion_rs::bytecode::ion10::BinaryIon10Generator;
    use ion_rs::bytecode::reader::BytecodeReader;

    let (ion_large, json_large) = load_service_log();

    let mut group = c.benchmark_group("tape_scan");

    // Small dataset
    group.throughput(Throughput::Bytes(JSON_SMALL.len() as u64));
    group.bench_function("simd_json tape [log_1000]", |b| {
        b.iter(|| {
            let mut count = 0usize;
            for line in JSON_SMALL.lines() {
                let mut bytes = line.as_bytes().to_vec();
                let tape = simd_json::to_tape(&mut bytes).unwrap();
                black_box(&tape);
                count += 1;
            }
            assert_eq!(count, 1000);
        })
    });

    group.throughput(Throughput::Bytes(ION_SMALL.len() as u64));
    group.bench_function("ion bytecode scan [log_1000]", |b| {
        b.iter(|| {
            let generator = BinaryIon10Generator::new(ION_SMALL);
            let mut reader = BytecodeReader::with_generator(generator);
            let mut count = 0usize;
            while reader.next().unwrap().is_some() {
                count += 1;
            }
            assert_eq!(count, 1000);
            black_box(count);
        })
    });

    // Large dataset
    group.sample_size(10);

    group.throughput(Throughput::Bytes(json_large.len() as u64));
    group.bench_function("simd_json tape [service_log]", |b| {
        b.iter(|| {
            let mut count = 0usize;
            for line in json_large.lines() {
                let mut bytes = line.as_bytes().to_vec();
                let tape = simd_json::to_tape(&mut bytes).unwrap();
                black_box(&tape);
                count += 1;
            }
            black_box(count);
        })
    });

    group.throughput(Throughput::Bytes(ion_large.len() as u64));
    group.bench_function("ion bytecode scan [service_log]", |b| {
        b.iter(|| {
            let generator = BinaryIon10Generator::new(ion_large.as_slice());
            let mut reader = BytecodeReader::with_generator(generator);
            let mut count = 0usize;
            while reader.next().unwrap().is_some() {
                count += 1;
            }
            black_box(count);
        })
    });

    // FMA dataset
    group.sample_size(100);

    group.throughput(Throughput::Bytes(JSON_NESTED.len() as u64));
    group.bench_function("simd_json tape [nested]", |b| {
        b.iter(|| {
            let mut count = 0usize;
            for line in JSON_NESTED.lines() {
                let mut bytes = line.as_bytes().to_vec();
                let tape = simd_json::to_tape(&mut bytes).unwrap();
                black_box(&tape);
                count += 1;
            }
            assert_eq!(count, 1000);
        })
    });

    group.throughput(Throughput::Bytes(ION_NESTED.len() as u64));
    group.bench_function("ion bytecode scan [nested]", |b| {
        b.iter(|| {
            let generator = BinaryIon10Generator::new(ION_NESTED);
            let mut reader = BytecodeReader::with_generator(generator);
            let mut count = 0usize;
            while reader.next().unwrap().is_some() {
                count += 1;
            }
            assert_eq!(count, 1000);
            black_box(count);
        })
    });

    // EMF dataset
    group.throughput(Throughput::Bytes(JSON_EMF.len() as u64));
    group.bench_function("simd_json tape [emf]", |b| {
        b.iter(|| {
            let mut count = 0usize;
            for line in JSON_EMF.lines() {
                let mut bytes = line.as_bytes().to_vec();
                let tape = simd_json::to_tape(&mut bytes).unwrap();
                black_box(&tape);
                count += 1;
            }
            assert_eq!(count, 1000);
        })
    });

    group.throughput(Throughput::Bytes(ION_EMF.len() as u64));
    group.bench_function("ion bytecode scan [emf]", |b| {
        b.iter(|| {
            let generator = BinaryIon10Generator::new(ION_EMF);
            let mut reader = BytecodeReader::with_generator(generator);
            let mut count = 0usize;
            while reader.next().unwrap().is_some() {
                count += 1;
            }
            assert_eq!(count, 1000);
            black_box(count);
        })
    });

    group.finish();
}

// ─── Write / Serialize ───────────────────────────────────────────────────────

fn bench_write(c: &mut Criterion) {
    use ion_rs::{v1_0, Element, Sequence};

    // Pre-parse the data into DOM form so we're only measuring write speed.
    let emf_elements: Sequence =
        ion_rs::bytecode::materialize::read_all_v3(ION_EMF).unwrap();
    let emf_json_values: Vec<serde_json::Value> = JSON_EMF
        .lines()
        .map(|l| serde_json::from_str(l).unwrap())
        .collect();

    let log_elements: Sequence =
        ion_rs::bytecode::materialize::read_all_v3(ION_SMALL).unwrap();
    let log_json_values: Vec<serde_json::Value> = JSON_SMALL
        .lines()
        .map(|l| serde_json::from_str(l).unwrap())
        .collect();

    let mut group = c.benchmark_group("write");

    // --- log_1000 ---
    group.throughput(Throughput::Elements(1000));
    group.bench_function("serde_json [log_1000]", |b| {
        b.iter(|| {
            let mut buf = Vec::with_capacity(384_000);
            for v in &log_json_values {
                serde_json::to_writer(&mut buf, v).unwrap();
                buf.push(b'\n');
            }
            black_box(buf.len());
        })
    });

    group.bench_function("ion binary [log_1000]", |b| {
        b.iter(|| {
            let mut buf = Vec::with_capacity(270_000);
            log_elements.encode_to(&mut buf, v1_0::Binary).unwrap();
            black_box(buf.len());
        })
    });

    // --- EMF ---
    group.bench_function("serde_json [emf]", |b| {
        b.iter(|| {
            let mut buf = Vec::with_capacity(372_000);
            for v in &emf_json_values {
                serde_json::to_writer(&mut buf, v).unwrap();
                buf.push(b'\n');
            }
            black_box(buf.len());
        })
    });

    group.bench_function("ion binary [emf]", |b| {
        b.iter(|| {
            let mut buf = Vec::with_capacity(164_000);
            emf_elements.encode_to(&mut buf, v1_0::Binary).unwrap();
            black_box(buf.len());
        })
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_owned_dom,
    bench_arena_dom,
    bench_field_access,
    bench_tape_scan,
    bench_write,
);
criterion_main!(benches);
