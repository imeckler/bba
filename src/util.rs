pub fn time<A, F>(label: &str, f : F) -> A where F: FnOnce() -> A {
    let start = std::time::Instant::now();
    let x = f();
    println!("{}: {:?}", label, start.elapsed());
    x
}


