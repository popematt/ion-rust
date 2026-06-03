use std::fs;
use std::hint::black_box;
use std::time::Instant;

fn main() {
    let data = fs::read("service_log_legacy.ion").unwrap();
    eprintln!("Data size: {} bytes ({:.1} MB)", data.len(), data.len() as f64 / 1_000_000.0);

    // Warmup + get element count
    let result = ion_rs::bytecode::materialize::read_all_v3_str_text(&data).unwrap();
    eprintln!("Elements: {}", result.len());
    drop(result);

    // Measure full pipeline (with drop)
    let iterations = 3u32;
    let start = Instant::now();
    for _ in 0..iterations {
        let result = ion_rs::bytecode::materialize::read_all_v3_str_text(&data).unwrap();
        black_box(&result);
    }
    let elapsed_full = start.elapsed();
    let per_iter_full = elapsed_full / iterations;

    // Measure full pipeline (without drop)
    let mut results = Vec::with_capacity(iterations as usize);
    let start = Instant::now();
    for _ in 0..iterations {
        let result = ion_rs::bytecode::materialize::read_all_v3_str_text(&data).unwrap();
        results.push(result);
    }
    let elapsed_no_drop = start.elapsed();
    let per_iter_no_drop = elapsed_no_drop / iterations;
    black_box(&results);
    drop(results);

    let drop_time = per_iter_full.saturating_sub(per_iter_no_drop);

    eprintln!("\n=== Timing ===");
    eprintln!("With drop:    {:.3}s ({:.1} MB/s)", per_iter_full.as_secs_f64(), data.len() as f64 / per_iter_full.as_secs_f64() / 1_000_000.0);
    eprintln!("Without drop: {:.3}s ({:.1} MB/s)", per_iter_no_drop.as_secs_f64(), data.len() as f64 / per_iter_no_drop.as_secs_f64() / 1_000_000.0);
    eprintln!("Drop cost:    {:.3}s ({:.1}%)", drop_time.as_secs_f64(), drop_time.as_secs_f64() / per_iter_full.as_secs_f64() * 100.0);

    // Compare with binary reader for context
    let binary_data = fs::read("service_log_legacy.10n").unwrap();
    eprintln!("\n=== Binary comparison ===");
    eprintln!("Binary data size: {} bytes ({:.1} MB)", binary_data.len(), binary_data.len() as f64 / 1_000_000.0);

    let start = Instant::now();
    for _ in 0..iterations {
        let result = ion_rs::bytecode::materialize::read_all_v3(&binary_data).unwrap();
        black_box(&result);
    }
    let elapsed_binary = start.elapsed();
    let per_iter_binary = elapsed_binary / iterations;
    eprintln!("Binary with drop: {:.3}s ({:.1} MB/s text-equivalent)", per_iter_binary.as_secs_f64(), data.len() as f64 / per_iter_binary.as_secs_f64() / 1_000_000.0);
    eprintln!("Text/Binary ratio: {:.2}x", per_iter_full.as_secs_f64() / per_iter_binary.as_secs_f64());
}
