use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use keytrans::log_tree::{LogEntry, LogTree};
use std::hint::black_box;

fn tree_with(n: usize) -> LogTree {
    let mut tree = LogTree::new(LogEntry::new(1, [1u8; 32]));
    for t in 2..=n as u64 {
        tree.append(LogEntry::new(t, [t as u8; 32]));
    }
    tree
}

fn bench_prove_combined(c: &mut Criterion) {
    let mut group = c.benchmark_group("prove_combined");
    for n in [100usize, 1_000, 10_000, 100_000] {
        let tree = tree_with(n);
        group.bench_with_input(BenchmarkId::new("n_sweep", n), &n, |b, _| {
            b.iter(|| tree.prove_combined(black_box(n / 2), black_box(n / 2)))
        });
    }
    group.finish();
}

criterion_group!(benches, bench_prove_combined);
criterion_main!(benches);
