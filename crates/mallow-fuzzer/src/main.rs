//! Command line for generating programs and running the differential check.

use std::collections::BTreeMap;
use std::fmt::Write;
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use anyhow::{Context, Result};
use clap::{Args, Parser, Subcommand};
use mallow_core::{DecompileOptions, Diagnostics};
use mallow_fuzzer::harness::{Harness, Outcome};
use mallow_fuzzer::{Config, Weights, generate_source};
use mallow_luau_toolchain::{LuauSelector, Manager};

#[derive(Parser)]
#[command(about = "Random Luau program generator for testing the mallow decompiler")]
struct Cli {
    #[command(subcommand)]
    command: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Print generated programs.
    Gen {
        /// Seed of the first program.
        #[arg(long, default_value_t = 0)]
        seed: u64,
        /// Number of programs, with seeds counting up from `--seed`.
        #[arg(long, default_value_t = 1)]
        count: u64,
        /// Write `<seed>.luau` files into this directory.
        #[arg(long)]
        out: Option<PathBuf>,
        #[command(flatten)]
        generation: Generation,
    },
    /// Generate programs, run them with Luau and compare against mallow.
    Check {
        /// Seed of the first program.
        #[arg(long, default_value_t = 0)]
        seed: u64,
        /// Number of programs, with seeds counting up from `--seed`.
        #[arg(long, default_value_t = 100)]
        count: u64,
        /// Parallel workers.
        #[arg(long, short, default_value_t = std::thread::available_parallelism().map_or(1, |n| n.get()))]
        jobs: usize,
        /// Managed Luau release, either an exact version such as `0.700` or
        /// `bc<N>` for the newest release emitting bytecode version N.
        #[arg(long, default_value = "bc9")]
        luau: LuauSelector,
        /// Optimization levels to compile with before decompiling.
        #[arg(long, short = 'O', value_delimiter = ',', default_value = "0,1,2")]
        opt: Vec<u8>,
        /// Timeout in seconds for each process and each decompilation.
        #[arg(long, default_value_t = 5.0)]
        timeout: f64,
        /// Only check that generated programs run cleanly.
        #[arg(long)]
        no_decompile: bool,
        /// Directory for failing cases.
        #[arg(long, default_value = "findings")]
        out: PathBuf,
        #[command(flatten)]
        generation: Generation,
    },
    /// Decompile a bytecode file and print the source. `check` runs this in a
    /// child process for every case.
    #[command(hide = true)]
    Decompile { bytecode: PathBuf },
}

/// Flags that shape generated programs.
#[derive(Args, Clone)]
struct Generation {
    /// Approximate statements per program.
    #[arg(long)]
    stmts: Option<u32>,
    /// Deepest block nesting.
    #[arg(long)]
    block_depth: Option<u32>,
    /// Deepest expression nesting.
    #[arg(long)]
    expr_depth: Option<u32>,
    /// Statement weight such as `while_loop=20`. Repeatable.
    #[arg(long = "weight", value_name = "NAME=N")]
    weights: Vec<String>,
}

impl Generation {
    fn config(&self) -> Result<Config> {
        let mut config = Config::default();
        if let Some(stmts) = self.stmts {
            config.max_stmts = stmts;
        }
        if let Some(depth) = self.block_depth {
            config.max_block_depth = depth;
        }
        if let Some(depth) = self.expr_depth {
            config.max_expr_depth = depth.max(1);
        }
        let mut weights = Weights::default();
        for spec in &self.weights {
            weights.set(spec)?;
        }
        config.weights = weights;
        Ok(config)
    }

    /// The same flags, written for a reproduction command line.
    fn flags(&self) -> String {
        let mut out = String::new();
        if let Some(stmts) = self.stmts {
            let _ = write!(out, " --stmts {stmts}");
        }
        if let Some(depth) = self.block_depth {
            let _ = write!(out, " --block-depth {depth}");
        }
        if let Some(depth) = self.expr_depth {
            let _ = write!(out, " --expr-depth {depth}");
        }
        for weight in &self.weights {
            let _ = write!(out, " --weight {weight}");
        }
        out
    }
}

fn main() -> Result<()> {
    match Cli::parse().command {
        Cmd::Gen {
            seed,
            count,
            out,
            generation,
        } => {
            let config = generation.config()?;
            if let Some(dir) = &out {
                std::fs::create_dir_all(dir)?;
            }
            for seed in seed..seed + count {
                let source = generate_source(seed, &config);
                match &out {
                    Some(dir) => std::fs::write(dir.join(format!("{seed}.luau")), source)?,
                    None => {
                        if count > 1 {
                            println!("-- seed {seed}");
                        }
                        print!("{source}");
                    }
                }
            }
            Ok(())
        }
        Cmd::Check {
            seed,
            count,
            jobs,
            luau,
            opt,
            timeout,
            no_decompile,
            out,
            generation,
        } => {
            let installation = Manager::new()?
                .install(&luau)
                .with_context(|| format!("installing Luau {luau}"))?;
            let harness = Harness {
                luau: installation.luau_path(),
                compiler: installation.compiler_path(),
                decompiler: std::env::current_exe()?,
                opt_levels: opt,
                timeout: Duration::from_secs_f64(timeout),
                decompile: !no_decompile,
            };
            let campaign = Campaign {
                harness,
                config: generation.config()?,
                out,
                flags: generation.flags(),
            };
            campaign.run(seed, count, jobs.max(1))
        }
        Cmd::Decompile { bytecode } => {
            let bytecode = std::fs::read(&bytecode)
                .with_context(|| format!("reading {}", bytecode.display()))?;
            let source = mallow_core::decompile_source(
                &bytecode,
                DecompileOptions::default(),
                &Diagnostics::default(),
            )?;
            print!("{}", source.print());
            Ok(())
        }
    }
}

/// A batch of seeds checked in parallel.
struct Campaign {
    harness: Harness,
    config: Config,
    /// Directory for failing cases.
    out: PathBuf,
    /// Generation flags for reproduction command lines.
    flags: String,
}

impl Campaign {
    fn run(&self, first: u64, count: u64, jobs: usize) -> Result<()> {
        let next = AtomicU64::new(first);
        let end = first + count;
        let results: Mutex<BTreeMap<String, Vec<u64>>> = Mutex::default();
        let started = Instant::now();
        let work_root = self.out.join(".work");

        std::thread::scope(|scope| -> Result<()> {
            let workers: Vec<_> = (0..jobs)
                .map(|worker| {
                    let (next, results) = (&next, &results);
                    let work = work_root.join(worker.to_string());
                    scope.spawn(move || -> Result<()> {
                        std::fs::create_dir_all(&work)?;
                        loop {
                            let seed = next.fetch_add(1, Ordering::Relaxed);
                            if seed >= end {
                                return Ok(());
                            }
                            let outcome = self.check(seed, &work)?;
                            results
                                .lock()
                                .expect("no worker panics while holding the lock")
                                .entry(outcome.label())
                                .or_default()
                                .push(seed);
                        }
                    })
                })
                .collect();
            for worker in workers {
                worker.join().expect("worker panicked")?;
            }
            Ok(())
        })?;
        let _ = std::fs::remove_dir_all(&work_root);

        println!(
            "checked {count} programs in {:.1}s",
            started.elapsed().as_secs_f64()
        );
        let results = results.into_inner().expect("every worker has finished");
        print_summary(&results);
        Ok(())
    }

    /// Checks one seed and saves it when it fails.
    fn check(&self, seed: u64, work: &Path) -> Result<Outcome> {
        let (source, outcome) = self.harness.check(seed, &self.config, work)?;
        if outcome != Outcome::Ok {
            let reproduce = format!(
                "cargo run -p mallow-fuzzer -- gen --seed {seed}{}",
                self.flags
            );
            let dir = outcome.save(&self.out, seed, &source, &reproduce)?;
            eprintln!("seed {seed}: {} -> {}", outcome.label(), dir.display());
        }
        Ok(outcome)
    }
}

/// Prints one line per outcome label with its count and a few seeds.
fn print_summary(results: &BTreeMap<String, Vec<u64>>) {
    for (label, seeds) in results {
        if label == "ok" {
            println!("  {label:<40} {}", seeds.len());
            continue;
        }
        let mut seeds = seeds.clone();
        seeds.sort_unstable();
        let preview: Vec<String> = seeds.iter().take(8).map(u64::to_string).collect();
        let more = if seeds.len() > 8 { ", ..." } else { "" };
        println!(
            "  {label:<40} {}  (seeds {}{more})",
            seeds.len(),
            preview.join(", ")
        );
    }
}
