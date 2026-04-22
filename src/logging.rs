use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

static VERBOSE_ENABLED: AtomicBool = AtomicBool::new(false);
static START: OnceLock<Instant> = OnceLock::new();

pub fn set_verbose(enabled: bool) {
    START.get_or_init(Instant::now); // anchor T+0 at first call
    VERBOSE_ENABLED.store(enabled, Ordering::Release);
}

pub fn is_verbose() -> bool {
    VERBOSE_ENABLED.load(Ordering::Acquire)
}

pub fn elapsed_ms() -> u128 {
    START.get_or_init(Instant::now).elapsed().as_millis()
}

macro_rules! verbose {
    // verbose!(indent: 2, "resolving {}", name)
    (indent: $n:expr, $($arg:tt)*) => {
        if $crate::logging::is_verbose() {
            eprintln!(
                "\x1b[2mT+{:>5}ms\x1b[0m \x1b[36m[{}]\x1b[0m {}{}",
                $crate::logging::elapsed_ms(),
                module_path!().split("::").last().unwrap_or("?"),
                "  ".repeat($n),
                format_args!($($arg)*)
            );
        }
    };
    // verbose!("hello {}", world)
    ($($arg:tt)*) => {
        if $crate::logging::is_verbose() {
            eprintln!(
                "\x1b[2mT+{:>5}ms\x1b[0m \x1b[36m[{}]\x1b[0m {}",
                $crate::logging::elapsed_ms(),
                module_path!().split("::").last().unwrap_or("?"),
                format_args!($($arg)*)
            );
        }
    };
}

pub(crate) use verbose;
