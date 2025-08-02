use criterion::{Criterion, criterion_group, criterion_main};
use rowscript_core::Ctx;

fn criterion_benchmark(c: &mut Criterion) {
    let ctx = Ctx::new(include_str!("fibonacci.rows"))
        .parse()
        .unwrap()
        .resolve()
        .unwrap()
        .check()
        .unwrap();
    c.bench_function("fibonacci", |b| b.iter(|| ctx.eval()));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
