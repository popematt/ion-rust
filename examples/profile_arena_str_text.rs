use ion_rs::bytecode::arena_reader::ArenaReader;
use ion_rs::bytecode::str_text10::StrTextIon10Generator;

fn main() {
    let data = std::fs::read("service_log_legacy.ion").unwrap();
    let text = std::str::from_utf8(&data).unwrap();

    // Warmup
    {
        let gen = StrTextIon10Generator::new(text);
        let mut reader = ArenaReader::new(gen).unwrap();
        while let Some(result) = reader.next() {
            let _ = result.unwrap();
        }
    }

    // Timed
    let start = std::time::Instant::now();
    let iterations = 10;
    for _ in 0..iterations {
        let gen = StrTextIon10Generator::new(text);
        let mut reader = ArenaReader::new(gen).unwrap();
        while let Some(result) = reader.next() {
            let _ = result.unwrap();
        }
    }
    let elapsed = start.elapsed() / iterations;
    let throughput = data.len() as f64 / elapsed.as_secs_f64() / 1_000_000.0;
    println!("Arena + str text: {:?} ({:.1} MB/s)", elapsed, throughput);
}
