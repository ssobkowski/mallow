#[derive(Clone, Default, PartialEq, Eq)]
pub struct RegSet([u64; 4]);

impl RegSet {
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn set(&mut self, reg: u8) {
        self.0[reg as usize / 64] |= 1u64 << (reg % 64);
    }

    #[inline]
    pub fn contains(&self, reg: u8) -> bool {
        self.0[reg as usize / 64] & (1u64 << (reg % 64)) != 0
    }

    pub fn iter(&self) -> impl Iterator<Item = u8> + '_ {
        self.0.iter().enumerate().flat_map(|(i, &word)| {
            let base = i * 64;
            let mut w = word;
            std::iter::from_fn(move || {
                if w == 0 {
                    return None;
                }
                let bit = w.trailing_zeros() as usize;
                w &= w - 1; // clear lowest set bit
                Some((base + bit) as u8)
            })
        })
    }

    pub fn extend<I: IntoIterator<Item = u8>>(&mut self, other: I) {
        for reg in other {
            self.set(reg);
        }
    }
}

impl std::ops::BitOrAssign<&RegSet> for RegSet {
    fn bitor_assign(&mut self, rhs: &RegSet) {
        for (a, b) in self.0.iter_mut().zip(rhs.0.iter()) {
            *a |= b;
        }
    }
}

impl std::ops::BitAndAssign<&RegSet> for RegSet {
    fn bitand_assign(&mut self, rhs: &RegSet) {
        for (a, b) in self.0.iter_mut().zip(rhs.0.iter()) {
            *a &= b;
        }
    }
}
