pub(crate) mod fir;
pub(crate) mod nir;

pub(crate) mod graph;
mod union_find;

use std::ops::Index;

use crate::common::ByteString;
use crate::il::ProtoId;

/// A program represented by a fixed set of functions.
#[derive(Debug, Clone)]
pub struct Unit<F> {
    /// Function selected as the program entry point.
    entry: ProtoId,
    /// Functions stored in prototype identifier order.
    functions: Box<[F]>,
    /// Names assigned to tagged userdata indices by the bytecode producer.
    userdata_names: Option<Box<[UserdataTypeMapping]>>,
}

impl<F> Unit<F> {
    /// Creates a unit from boxed slices.
    pub(crate) fn new(
        entry: ProtoId,
        functions: Box<[F]>,
        userdata_names: Option<Box<[UserdataTypeMapping]>>,
    ) -> Self {
        Self {
            entry,
            functions,
            userdata_names,
        }
    }

    /// Convenience constructor when building from dynamically sized `Vec`s.
    pub(crate) fn from_vec(
        entry: ProtoId,
        functions: Vec<F>,
        userdata_names: Option<Vec<UserdataTypeMapping>>,
    ) -> Self {
        Self::new(
            entry,
            functions.into_boxed_slice(),
            userdata_names.map(Vec::into_boxed_slice),
        )
    }

    /// Returns the entry function identifier.
    pub const fn entry(&self) -> ProtoId {
        self.entry
    }

    /// Returns all functions in prototype identifier order.
    pub fn functions(&self) -> impl Iterator<Item = &F> {
        self.functions.iter()
    }

    /// Returns all functions mutably in prototype identifier order.
    pub(crate) fn functions_mut(&mut self) -> impl Iterator<Item = &mut F> {
        self.functions.iter_mut()
    }

    /// Resolves one function by prototype identifier.
    pub fn get(&self, id: ProtoId) -> Option<&F> {
        self.functions.get(id.0 as usize)
    }

    /// Returns the tagged userdata names supplied by the bytecode producer.
    pub(crate) fn userdata_names(&self) -> Option<&[UserdataTypeMapping]> {
        self.userdata_names.as_deref()
    }

    /// Converts every function while preserving program metadata.
    pub(crate) fn map_functions<U, E>(
        self,
        mut map: impl FnMut(F) -> Result<U, E>,
    ) -> Result<Unit<U>, E> {
        let functions = self
            .functions
            .into_iter()
            .map(&mut map)
            .collect::<Result<_, _>>()?;
        Ok(Unit::new(self.entry, functions, self.userdata_names))
    }
}

impl<F> Index<ProtoId> for Unit<F> {
    type Output = F;

    /// Resolves one function by its dense prototype identifier.
    fn index(&self, id: ProtoId) -> &Self::Output {
        self.functions.index(id.0 as usize)
    }
}

impl<F> IntoIterator for Unit<F> {
    type Item = F;
    type IntoIter = <Vec<F> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.functions.into_iter()
    }
}

/// Tagged userdata name detached from the bytecode string table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UserdataTypeMapping {
    /// Bytecode tag index.
    pub index: u8,
    /// Userdata name when the bytecode supplied one.
    pub name: Option<ByteString>,
}

/// Source information for a function.
#[derive(Debug, Clone, Default)]
pub struct Debug {
    /// Function name when the bytecode supplied one.
    pub name: Option<ByteString>,
    /// Named local declarations and their bytecode lifetimes.
    pub locals: Vec<DebugLocal>,
    /// Upvalue names in slot order.
    pub upvalues: Vec<Option<ByteString>>,
}

/// Named source declaration from bytecode debug information.
#[derive(Debug, Clone)]
pub struct DebugLocal {
    /// Source name of the declaration.
    pub name: ByteString,
    /// Physical register occupied by the declaration.
    pub register: u8,
    /// First bytecode program counter covered by the declaration.
    pub start_pc: u32,
    /// First bytecode program counter after the declaration.
    pub end_pc: u32,
}
