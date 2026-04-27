use std::collections::HashSet;

use smol_str::{SmolStr, format_smolstr};

use crate::ast::Identifier;

#[derive(Default)]
pub struct NameAllocator {
    used: HashSet<SmolStr>,
    next_param: usize,
    next_local: usize,
}

impl NameAllocator {
    pub fn reserve_exact(&mut self, preferred: SmolStr) -> Identifier {
        if self.used.insert(preferred.clone()) {
            return Identifier::new(preferred);
        }

        let mut counter = 0usize;
        loop {
            let candidate = format_smolstr!("{preferred}__{counter}");
            if self.used.insert(candidate.clone()) {
                return Identifier::new(candidate);
            }
            counter += 1;
        }
    }

    pub fn fresh_param(&mut self) -> Identifier {
        loop {
            let candidate = format_smolstr!("p{}", self.next_param);
            self.next_param += 1;
            if self.used.insert(candidate.clone()) {
                return Identifier::new(candidate);
            }
        }
    }

    pub fn fresh_local(&mut self) -> Identifier {
        loop {
            let candidate = format_smolstr!("v{}", self.next_local);
            self.next_local += 1;
            if self.used.insert(candidate.clone()) {
                return Identifier::new(candidate);
            }
        }
    }
}
