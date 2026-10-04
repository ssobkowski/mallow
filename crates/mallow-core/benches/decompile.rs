//! Decompilation benchmarks over a directory of Luau bytecode files.
//!
//! Set `MALLOW_BENCH_CORPUS` to a directory containing `*.bin` bytecode files
//! (e.g. produced with `luau-compile --binary`).

use std::fs;
use std::hint::black_box;
use std::path::PathBuf;

use criterion::{Criterion, Throughput, criterion_group, criterion_main};
use mallow_core::{DecompileOptions, decompile_bytecode};

fn load_corpus() -> Vec<(String, Vec<u8>)> {
    let dir = PathBuf::from(
        std::env::var_os("MALLOW_BENCH_CORPUS").expect("set MALLOW_BENCH_CORPUS to a bytecode dir"),
    );
    let mut files: Vec<_> = fs::read_dir(dir)
        .expect("read corpus dir")
        .filter_map(|entry| {
            let path = entry.ok()?.path();
            (path.extension()? == "bin").then(|| {
                let name = path.file_stem()?.to_string_lossy().into_owned();
                Some((name, fs::read(&path).ok()?))
            })?
        })
        .filter(|(_, bytes)| decompile_bytecode(bytes, DecompileOptions::default()).is_ok())
        .collect();
    files.sort_by(|a, b| a.0.cmp(&b.0));
    files
}

fn bench_decompile(c: &mut Criterion) {
    let corpus = load_corpus();
    let total: usize = corpus.iter().map(|(_, b)| b.len()).sum();

    let mut group = c.benchmark_group("decompile");
    group.throughput(Throughput::Bytes(total as u64));
    group.bench_function("corpus", |b| {
        b.iter(|| {
            for (_, bytes) in &corpus {
                black_box(decompile_bytecode(black_box(bytes), DecompileOptions::default()).ok());
            }
        })
    });
    group.finish();

    let mut largest: Vec<_> = corpus.iter().collect();
    largest.sort_by_key(|(_, b)| std::cmp::Reverse(b.len()));
    let mut group = c.benchmark_group("decompile_large");
    for (name, bytes) in largest.into_iter().take(3) {
        group.throughput(Throughput::Bytes(bytes.len() as u64));
        group.bench_function(name, |b| {
            b.iter(|| decompile_bytecode(black_box(bytes), DecompileOptions::default()).ok())
        });
    }
    group.finish();
}

criterion_group!(benches, bench_decompile);
criterion_main!(benches);
