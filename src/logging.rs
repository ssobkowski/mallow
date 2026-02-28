use std::sync::atomic::{AtomicBool, Ordering};

static VERBOSE: AtomicBool = AtomicBool::new(false);

pub fn set_verbose(enabled: bool) {
    VERBOSE.store(enabled, Ordering::Relaxed);
}

#[inline]
pub fn verbose_enabled() -> bool {
    VERBOSE.load(Ordering::Relaxed)
}
