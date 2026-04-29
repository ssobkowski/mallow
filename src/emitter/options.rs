#[derive(Default)]
pub struct EmitterOptions {
    /// Spill emitter-introduced locals into a table once Luau's local limit would be
    /// exceeded. This keeps the output runnable, but can be slower and semantically
    /// less accurate than pure local-based emission.
    pub spill_locals: bool,
}
