//! The random source behind every generator decision.

use std::ops::RangeInclusive;

use rand::distr::uniform::SampleUniform;
use rand::rngs::Xoshiro256PlusPlus;
use rand::seq::IteratorRandom;
use rand::{RngExt, SeedableRng};

/// A seeded random source.
///
/// It uses xoshiro256++ by name, so one seed always gives the same program
/// regardless of what `rand` picks as its default small generator.
pub struct Dice(Xoshiro256PlusPlus);

impl Dice {
    pub fn new(seed: u64) -> Self {
        Self(Xoshiro256PlusPlus::seed_from_u64(seed))
    }

    /// Returns `true` with probability `p`.
    pub fn chance(&mut self, p: f64) -> bool {
        self.0.random_bool(p)
    }

    /// Returns a uniform value in `range`.
    pub fn range<T: SampleUniform + PartialOrd>(&mut self, range: RangeInclusive<T>) -> T {
        self.0.random_range(range)
    }

    /// Returns a uniform element of `items`, which must be non-empty.
    pub fn pick<T: Copy>(&mut self, items: &[T]) -> T {
        items[self.0.random_range(0..items.len())]
    }

    /// Returns a uniform element of `items`, or `None` when it is empty.
    ///
    /// This consumes the iterator in one pass and allocates nothing.
    pub fn choose<T>(&mut self, items: impl Iterator<Item = T>) -> Option<T> {
        items.choose(&mut self.0)
    }

    /// Returns an index into `weights`, chosen in proportion to its weight.
    ///
    /// A zero weight is never chosen. At least one weight must be positive.
    pub fn weighted(&mut self, weights: &[u32]) -> usize {
        let total: u32 = weights.iter().sum();
        assert!(total > 0, "every weight is zero");
        let mut roll = self.0.random_range(0..total);
        for (index, &weight) in weights.iter().enumerate() {
            if roll < weight {
                return index;
            }
            roll -= weight;
        }
        unreachable!("the roll is below the total")
    }
}
