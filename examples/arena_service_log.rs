use ion_rs::bytecode::arena_reader::ArenaReader;
use ion_rs::bytecode::ion10::BinaryIon10Generator;

fn main() {
    let data = std::fs::read("service_log_legacy.10n").unwrap();

    // Arena materializer — just read, no clone
    let generator = BinaryIon10Generator::new(&data);
    let mut reader = ArenaReader::new(generator).unwrap();
    let mut count = 0usize;
    while let Some(result) = reader.next() {
        let _element = result.unwrap();
        count += 1;
    }
    println!("Arena: {count} values");

    // Print arena stats
    println!("Arena chunks: {}", reader.arena_chunk_count());
    println!("Arena total bytes: {}", reader.arena_total_bytes());

    std::thread::sleep(std::time::Duration::from_secs(2));
    drop(reader);
    println!("After reader drop");
    std::thread::sleep(std::time::Duration::from_secs(3));
}
