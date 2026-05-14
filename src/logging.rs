use std::io::IsTerminal;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

static VERBOSE_ENABLED: AtomicBool = AtomicBool::new(false);
static START: OnceLock<Instant> = OnceLock::new();

const TARGET_WIDTH: usize = 7;

pub fn set_verbose(enabled: bool) {
    START.get_or_init(Instant::now); // anchor T+0 at first call
    VERBOSE_ENABLED.store(enabled, Ordering::Relaxed);
}

pub fn is_verbose() -> bool {
    VERBOSE_ENABLED.load(Ordering::Relaxed)
}

pub fn elapsed_ms() -> u128 {
    START.get_or_init(Instant::now).elapsed().as_millis()
}

pub fn use_color() -> bool {
    std::io::stderr().is_terminal() && std::env::var_os("NO_COLOR").is_none()
}

fn short_module_path(path: &'static str) -> &'static str {
    path.rsplit("::").next().unwrap_or("?")
}

fn fit_target(target: &'static str) -> &'static str {
    if target.len() <= TARGET_WIDTH {
        return target;
    }

    // `module_path!()` is made from Rust identifiers and `::`, so the final
    // segment is ASCII. Byte slicing is fine here.
    &target[target.len() - TARGET_WIDTH..]
}

pub fn log_args(target: &'static str, indent: usize, args: std::fmt::Arguments<'_>) {
    let target = fit_target(short_module_path(target));
    let indent_width = indent * 2;

    if use_color() {
        eprintln!(
            "\x1b[2mT+{:>4}ms\x1b[0m \x1b[36m[{:<TARGET_WIDTH$}]\x1b[0m {:indent_width$}{}",
            elapsed_ms(),
            target,
            "",
            args,
        );
    } else {
        eprintln!(
            "T+{:>4}ms [{:<TARGET_WIDTH$}] {:indent_width$}{}",
            elapsed_ms(),
            target,
            "",
            args,
        );
    }
}

macro_rules! verbose {
    // verbose!(indent: 2, "resolving {}", name)
    (indent: $n:expr, $($arg:tt)*) => {{
        if $crate::logging::is_verbose() {
            $crate::logging::log_args(
                module_path!(),
                $n,
                format_args!($($arg)*),
            );
        }
    }};

    // verbose!("hello {}", world)
    ($($arg:tt)*) => {{
        if $crate::logging::is_verbose() {
            $crate::logging::log_args(
                module_path!(),
                0,
                format_args!($($arg)*),
            );
        }
    }};
}

pub(crate) use verbose;
