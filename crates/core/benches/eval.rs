use criterion::{Criterion, criterion_group, criterion_main};
use rowscript_core::State;
use rowscript_core::semantics::Integer;
use rowscript_core::syntax::Expr;

fn criterion_benchmark(c: &mut Criterion) {
    let mut s = State::default();
    s.parse(include_str!("fibonacci.rows")).unwrap();
    s.resolve().unwrap();
    s.check().unwrap();
    c.bench_function("fibonacci", |b| {
        b.iter(|| s.eval_nth(0, Expr::Integer(Integer::U32(20))))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
