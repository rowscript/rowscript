use criterion::{Criterion, criterion_group, criterion_main};
use rowscript_core::State;
use rowscript_core::syntax::Expr;

fn criterion_benchmark(c: &mut Criterion) {
    let state = State::parse(include_str!("fibonacci.rows"))
        .unwrap()
        .resolve()
        .unwrap()
        .check()
        .unwrap();
    c.bench_function("fibonacci", |b| {
        b.iter(|| state.eval_nth(0, Expr::Number(20.)))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
