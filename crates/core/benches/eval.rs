use criterion::{Criterion, criterion_group, criterion_main};
use rowscript_core::State;

fn criterion_benchmark(c: &mut Criterion) {
    let state = State::parse(include_str!("fibonacci.rows"))
        .unwrap()
        .resolve()
        .unwrap()
        .check()
        .unwrap();
    c.bench_function("fibonacci", |b| b.iter(|| state.eval()));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
