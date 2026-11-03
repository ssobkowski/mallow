//! Generator tests.
//!
//! The Luau test runs only when the managed `bc9` toolchain is already
//! installed, for example by `just toolchain install bc9`. It never downloads.

use mallow_fuzzer::harness::{Harness, Outcome};
use mallow_fuzzer::{Config, Weights, generate_source};
use mallow_luau_toolchain::{BytecodeVersion, Manager};

#[test]
fn same_seed_same_program() {
    let config = Config::default();
    for seed in 0..50 {
        assert_eq!(
            generate_source(seed, &config),
            generate_source(seed, &config)
        );
    }
}

#[test]
fn different_seeds_differ() {
    let config = Config::default();
    assert_ne!(generate_source(1, &config), generate_source(2, &config));
}

#[test]
fn generates_many_without_panicking() {
    let config = Config::default();
    for seed in 0..300 {
        let source = generate_source(seed, &config);
        assert!(!source.trim().is_empty());
    }
}

#[test]
fn every_weight_can_be_disabled() {
    for name in Weights::NAMES {
        let mut config = Config::default();
        config.weights.set(&format!("{name}=0")).unwrap();
        for seed in 0..20 {
            generate_source(seed, &config);
        }
    }
}

#[test]
fn programs_run_cleanly_under_luau() {
    let installation = Manager::new()
        .ok()
        .and_then(|manager| manager.installed(BytecodeVersion::V9).ok().flatten());
    let Some(installation) = installation else {
        eprintln!("managed bc9 toolchain is not installed, skipping");
        return;
    };
    let harness = Harness {
        luau: installation.luau_path(),
        compiler: installation.compiler_path(),
        decompiler: "unused".into(),
        opt_levels: Vec::new(),
        timeout: std::time::Duration::from_secs(5),
        decompile: false,
    };
    let work = std::env::temp_dir().join(format!("mallow-fuzzer-test-{}", std::process::id()));
    std::fs::create_dir_all(&work).unwrap();
    let config = Config::default();
    for seed in 0..300 {
        let (source, outcome) = harness.check(seed, &config, &work).unwrap();
        assert_eq!(outcome, Outcome::Ok, "seed {seed}:\n{source}");
    }
    let _ = std::fs::remove_dir_all(&work);
}
