pub fn time<A, F>(label: &str, f: F) -> A
where
    F: FnOnce() -> A,
{
    let start = std::time::Instant::now();
    let x = f();
    println!("{} ({:?})", label, start.elapsed());
    x
}

pub fn time_batch<A, F>(label: &str, item_label: &str, batch_size: usize, f: F) -> A
where
    F: FnOnce() -> A,
{
    let start = std::time::Instant::now();
    let x = f();
    let elapsed = start.elapsed();
    let per_item = elapsed / (batch_size as u32);
    println!(
        "{} ({:?} for {} {}s, {:?} per {})",
        label, elapsed, batch_size, item_label, per_item, item_label
    );
    x
}
