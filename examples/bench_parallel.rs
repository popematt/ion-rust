use ion_rs::bytecode::materialize::read_all_v3;
#[cfg(feature = "parallel")]
use ion_rs::bytecode::parallel_materialize::read_all_v3_parallel;

fn main() {
    let data = std::fs::read("service_log_legacy.10n").unwrap();

    // Warmup
    let _ = read_all_v3(&data).unwrap();
    #[cfg(feature = "parallel")]
    let _ = read_all_v3_parallel(&data).unwrap();

    // Sequential
    let start = std::time::Instant::now();
    for _ in 0..5 {
        let result = read_all_v3(&data).unwrap();
        std::hint::black_box(&result);
    }
    let seq_time = start.elapsed() / 5;
    println!("Sequential: {:?}", seq_time);

    // Parallel
    #[cfg(feature = "parallel")]
    {
        let start = std::time::Instant::now();
        for _ in 0..5 {
            let result = read_all_v3_parallel(&data).unwrap();
            std::hint::black_box(&result);
        }
        let par_time = start.elapsed() / 5;
        println!("Parallel:   {:?}", par_time);
        println!("Speedup:    {:.2}x", seq_time.as_secs_f64() / par_time.as_secs_f64());
    }
}
