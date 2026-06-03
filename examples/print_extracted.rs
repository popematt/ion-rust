use ion_rs::bytecode::materialize::read_all_v3_filtered;
use ion_rs::bytecode::path_filter::PathFilter;

fn main() {
    let data = std::fs::read("service_log_legacy.10n").unwrap();
    let filters = vec![
        PathFilter::field("StartTime"),
        PathFilter::field("Operation"),
        PathFilter::fields(&["Metrics", "Tokens"]),
        PathFilter::fields(&["Metrics", "TotalTime", "Value"]),
    ];
    let result = read_all_v3_filtered(&data, &filters).unwrap();
    println!("Total top-level values: {}", result.len());
    println!();
    for (i, element) in result.iter().take(5).enumerate() {
        println!("--- Value {i} ---");
        println!("{element}");
        println!();
    }
}
