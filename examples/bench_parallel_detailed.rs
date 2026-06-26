use ion_rs::bytecode::materialize::read_all_v3;
#[cfg(feature = "parallel")]
use ion_rs::bytecode::parallel_materialize::read_all_v3_parallel;

fn main() {
    let data = std::fs::read("service_log_legacy.10n").unwrap();

    // Warmup
    let _ = read_all_v3(&data).unwrap();
    #[cfg(feature = "parallel")]
    let _ = read_all_v3_parallel(&data).unwrap();

    // Sequential no-drop (measure pure materialization)
    let start = std::time::Instant::now();
    for _ in 0..5 {
        let result = read_all_v3(&data).unwrap();
        std::mem::forget(result);
    }
    let seq_no_drop = start.elapsed() / 5;
    println!("Sequential (no drop): {:?}", seq_no_drop);

    // Sequential with drop
    let start = std::time::Instant::now();
    for _ in 0..5 {
        let result = read_all_v3(&data).unwrap();
        std::hint::black_box(&result);
    }
    let seq_time = start.elapsed() / 5;
    println!("Sequential (w/ drop): {:?}", seq_time);

    // Parallel no-drop
    #[cfg(feature = "parallel")]
    {
        let start = std::time::Instant::now();
        for _ in 0..5 {
            let result = read_all_v3_parallel(&data).unwrap();
            std::mem::forget(result);
        }
        let par_no_drop = start.elapsed() / 5;
        println!("Parallel   (no drop): {:?}", par_no_drop);

        // Parallel with drop
        let start = std::time::Instant::now();
        for _ in 0..5 {
            let result = read_all_v3_parallel(&data).unwrap();
            std::hint::black_box(&result);
        }
        let par_time = start.elapsed() / 5;
        println!("Parallel   (w/ drop): {:?}", par_time);

        println!(
            "\nSpeedup (w/ drop):  {:.2}x",
            seq_time.as_secs_f64() / par_time.as_secs_f64()
        );
        println!(
            "Speedup (no drop):  {:.2}x",
            seq_no_drop.as_secs_f64() / par_no_drop.as_secs_f64()
        );
    }
}
