use std::{fmt, rc::Rc};

use anyhow::{Result, ensure};
use smallvec::{SmallVec, smallvec};

use crate::common::Spanned;

/// An index into the constant table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ConstId(pub u32);

/// An index into the proto table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ProtoId(pub u16);

impl std::fmt::Display for ProtoId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// An index into the child proto table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ChildProtoId(pub u16);

/// An index into the string table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StringId(pub u32);

/// An encoded import.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ImportPath(pub u32);

impl ImportPath {
    /// Returns an iterator over the [`ConstId`]s referenced by this import path.
    #[inline]
    pub fn const_ids(self) -> Result<impl Iterator<Item = ConstId>> {
        let path = self.0;
        let count = (path >> 30) as usize;
        ensure!((1..=3).contains(&count), "invalid import path");

        let ids = [
            ConstId((path >> 20) & 0x3ff),
            ConstId((path >> 10) & 0x3ff),
            ConstId(path & 0x3ff),
        ];

        Ok(ids.into_iter().take(count))
    }
}

/// A free-standing Luau string.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct LuauString(pub Rc<[u8]>);

impl LuauString {
    /// Returns the byte-exact string contents stored in bytecode.
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}

impl std::fmt::Display for LuauString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for &byte in self.as_bytes() {
            write!(f, "{}", char::from(byte))?;
        }
        Ok(())
    }
}

/// Represents the types of values that can be present in the constant table.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum Constant {
    Nil,
    Boolean(bool),
    Number(f64),
    String(StringId),
    Import(ImportPath),
    Table,
    Closure(ProtoId),
    Vector { x: f32, y: f32, z: f32, w: f32 },
    TableWithConstants(Vec<(ConstId, Option<ConstId>)>), // LBC7+
    Integer(i64),                                        // LBC8+
                                                         // ClassShape(Box<[u8]>), // LBC10+
}

/// Represents a Luau count.
#[derive(Debug, PartialEq, Eq)]
pub enum Count {
    Number(u8),
    Variadic,
}

impl Count {
    #[inline]
    #[must_use]
    pub const fn new(encoded: u8) -> Self {
        match encoded {
            0 => Count::Variadic,
            n => Count::Number(n - 1),
        }
    }
}

impl From<u8> for Count {
    #[inline]
    fn from(encoded: u8) -> Self {
        Count::new(encoded)
    }
}

/// Represents a Luau instruction.
#[derive(Debug, Clone, Copy)]
pub enum Instr {
    // Keep variant order in sync with LuauOpcode in Bytecode.h.
    // 0..6: basic loads/moves
    /// No operation.
    Nop,
    /// Debugger break.
    Break,
    /// Load nil into a register.
    LoadNil { reg: u8 },
    /// Load a boolean into a register and jumps to a given short offset.
    LoadB { reg: u8, value: bool, jump: u8 },
    /// Load an integer immediate into a register.
    LoadN { reg: u8, value: i16 },
    /// Load a constant into a register.
    LoadK { reg: u8, index: u16 },
    /// Move a value between registers.
    Move { dest: u8, src: u8 },

    // 7..12: globals/upvalues/imports
    /// Get a global variable by constant-string key.
    GetGlobal { dest: u8, slot: u8, key: u32 },
    /// Set a global variable by constant-string key.
    SetGlobal { src: u8, slot: u8, key: u32 },
    /// Get an upvalue into a register.
    GetUpval { dest: u8, upval: u8 },
    /// Set an upvalue from a register.
    SetUpval { src: u8, upval: u8 },
    /// Close upvalues at or above a register.
    CloseUpvals { reg: u8 },
    /// Get an imported value.
    GetImport { dest: u8, index: u16, path: u32 },

    // 13..20: table access and call setup
    /// Table read: dest = table\[key\]
    GetTable { dest: u8, table: u8, key: u8 },
    /// Table write: table\[key\] = src
    SetTable { src: u8, table: u8, key: u8 },
    /// Table read with constant string key.
    GetTableKS {
        dest: u8,
        table: u8,
        slot: u8,
        key: u32,
    },
    /// Table write with constant string key.
    SetTableKS {
        src: u8,
        table: u8,
        slot: u8,
        key: u32,
    },
    /// Table read with immediate integer key (1-indexed, range 1..=256).
    GetTableN { dest: u8, table: u8, index: u16 },
    /// Table write with immediate integer key (1-indexed, range 1..=256).
    SetTableN { src: u8, table: u8, index: u16 },
    /// Create a new closure from a proto.
    NewClosure { dest: u8, proto: u16 },
    /// Method call setup: dest+1 = object, dest = object\[method\]
    NameCall {
        dest: u8,
        object: u8,
        slot: u8,
        method: u32,
    },

    // 21..32: calls, returns, and branches
    /// Call a function: func(args...) -> results
    Call {
        func: u8,
        arg_count: u8,
        ret_count: u8,
    },
    /// Return from a function.
    Return { base: u8, count: u8 },
    /// Unconditional forward jump.
    Jump { offset: i16 },
    /// Unconditional backward jump (triggers interrupt hook).
    JumpBack { offset: i16 },
    /// Jump if register is truthy.
    JumpIf { reg: u8, offset: i16 },
    /// Jump if register is falsy.
    JumpIfNot { reg: u8, offset: i16 },
    /// Jump if reg == aux.
    JumpIfEq { reg: u8, aux: u8, offset: i16 },
    /// Jump if reg <= aux.
    JumpIfLe { reg: u8, aux: u8, offset: i16 },
    /// Jump if reg < aux.
    JumpIfLt { reg: u8, aux: u8, offset: i16 },
    /// Jump if reg ~= aux.
    JumpIfNotEq { reg: u8, aux: u8, offset: i16 },
    /// Jump if not (reg <= aux).
    JumpIfNotLe { reg: u8, aux: u8, offset: i16 },
    /// Jump if not (reg < aux).
    JumpIfNotLt { reg: u8, aux: u8, offset: i16 },

    // 33..52: arithmetic/logical/unary ops
    /// dest = a + b
    Add { dest: u8, a: u8, b: u8 },
    /// dest = a - b
    Sub { dest: u8, a: u8, b: u8 },
    /// dest = a * b
    Mul { dest: u8, a: u8, b: u8 },
    /// dest = a / b
    Div { dest: u8, a: u8, b: u8 },
    /// dest = a % b
    Mod { dest: u8, a: u8, b: u8 },
    /// dest = a ^ b
    Pow { dest: u8, a: u8, b: u8 },
    /// dest = reg + const
    AddK { dest: u8, reg: u8, k: u8 },
    /// dest = reg - const
    SubK { dest: u8, reg: u8, k: u8 },
    /// dest = reg * const
    MulK { dest: u8, reg: u8, k: u8 },
    /// dest = reg / const
    DivK { dest: u8, reg: u8, k: u8 },
    /// dest = reg % const
    ModK { dest: u8, reg: u8, k: u8 },
    /// dest = reg ^ const
    PowK { dest: u8, reg: u8, k: u8 },
    /// dest = a and b
    And { dest: u8, a: u8, b: u8 },
    /// dest = a or b
    Or { dest: u8, a: u8, b: u8 },
    /// dest = reg and const
    AndK { dest: u8, reg: u8, k: u8 },
    /// dest = reg or const
    OrK { dest: u8, reg: u8, k: u8 },
    /// dest = a .. b
    Concat { dest: u8, a: u8, b: u8 },
    /// dest = not reg
    Not { dest: u8, reg: u8 },
    /// dest = -reg
    Minus { dest: u8, reg: u8 },
    /// dest = #reg
    Length { dest: u8, reg: u8 },

    // 53..59: table construction and loop core ops
    /// Create a new table.
    NewTable {
        dest: u8,
        hash_size: u8,
        array_size: u32,
    },
    /// Duplicate a table template from the constant table.
    DupTable { dest: u8, k: u16 },
    /// Populate a table with values from registers.
    SetList {
        table: u8,
        base: u8,
        count: u8,
        index: u32,
    },
    /// Numeric for loop prep: validate and potentially skip.
    FornPrep { base: u8, offset: i16 },
    /// Numeric for loop step.
    FornLoop { base: u8, offset: i16 },
    /// Generic for loop iteration.
    ForgLoop {
        base: u8,
        offset: i16,
        var_count: u8,
        ipairs: bool,
    },
    /// Prep for ipairs-style iteration.
    ForgPrepInext { base: u8, offset: i16 },

    // 60..75: fastcall, varargs, closure helpers, extended jumps
    /// Perform a fast call of a built-in function using 3 register arguments.
    FastCall3 {
        builtin: u8,
        arg1: u8,
        arg2: u8,
        arg3: u8,
        jump: u8,
    },
    /// Prep for next()-style iteration.
    ForgPrepNext { base: u8, offset: i16 },
    /// Start executing a function in native code (runtime pseudo-instruction).
    NativeCall,
    /// Get variadic arguments into registers.
    GetVarArgs { dest: u8, count: u8 },
    /// Duplicate a closure from the constant table.
    DupClosure { dest: u8, k: u16 },
    /// Prepare variadic function frame.
    PrepVarArgs { nparams: u8 },
    /// Load extended constant.
    LoadKX { reg: u8, index: u32 },
    /// Extended unconditional jump.
    JumpX { offset: i32 },
    /// Fast path for a builtin call (skipped, falls through to CALL).
    FastCall { builtin: u8, jump: u8 },
    /// Increment coverage counter.
    Coverage,
    /// Capture an upvalue (used inside NEWCLOSURE sequences).
    Capture { capture_type: u8, reg: u8 },
    /// dest = const - reg
    SubRK { dest: u8, k: u8, reg: u8 },
    /// dest = const / reg
    DivRK { dest: u8, k: u8, reg: u8 },
    /// Fast path for single-arg builtin (skipped).
    FastCall1 { builtin: u8, arg: u8, jump: u8 },
    /// Fast path for two-arg builtin (skipped).
    FastCall2 {
        builtin: u8,
        arg1: u8,
        arg2: u8,
        jump: u8,
    },
    /// Fast path for builtin with one register + one constant arg (skipped).
    FastCall2K {
        builtin: u8,
        arg: u8,
        k: u32,
        jump: u8,
    },

    // 76..82: extended loop/constant comparisons and floor division
    /// Generic for loop prep (handles generalized iteration).
    ForgPrep { base: u8, offset: i16 },
    /// Jump if reg == nil, with optional inversion.
    JumpXEqKNil { reg: u8, invert: bool, offset: i16 },
    /// Jump if reg == bool constant, with optional inversion.
    JumpXEqKB {
        reg: u8,
        k: bool,
        invert: bool,
        offset: i16,
    },
    /// Jump if reg == number constant, with optional inversion.
    JumpXEqKN {
        reg: u8,
        k: u32,
        invert: bool,
        offset: i16,
    },
    /// Jump if reg == string constant, with optional inversion.
    JumpXEqKS {
        reg: u8,
        k: u32,
        invert: bool,
        offset: i16,
    },
    /// dest = a // b (integer division)
    IDiv { dest: u8, a: u8, b: u8 },
    /// dest = reg // const (integer division)
    IDivK { dest: u8, reg: u8, k: u8 },

    // 83..85: atom-based userdata field access acceleration
    /// Userdata field read with constant string key.
    GetUDataKS {
        dest: u8,
        userdata: u8,
        slot: u16,
        key: u16,
    },
    /// Userdata field write with constant string key.
    SetUDataKS {
        src: u8,
        userdata: u8,
        slot: u16,
        key: u16,
    },
    /// Userdata method call setup: dest+1 = object, dest = object\[method\]
    NameCallUData {
        dest: u8,
        object: u8,
        slot: u16,
        method: u16,
    },
}

impl Instr {
    pub const LOP_COUNT: u8 = 86; // LOP__COUNT (not a valid opcode)

    /// Returns whether the given opcode requires an auxiliary register.
    #[must_use]
    pub const fn opcode_requires_aux(opcode: u8) -> bool {
        matches!(
            opcode,
            7 | 8
                | 12
                | 15
                | 16
                | 20
                | 27
                | 28
                | 29
                | 30
                | 31
                | 32
                | 53
                | 55
                | 58
                | 60
                | 66
                | 74
                | 75
                | 77
                | 78
                | 79
                | 80
                | 83
                | 84
                | 85
        )
    }

    /// Returns whether one instruction must terminate its basic block.
    ///
    /// Note: This does not cover LoadB.
    #[must_use]
    pub const fn is_branch_exit(&self) -> bool {
        matches!(
            self,
            Instr::Jump { .. }
                | Instr::JumpX { .. }
                | Instr::JumpBack { .. }
                | Instr::JumpIf { .. }
                | Instr::JumpIfNot { .. }
                | Instr::JumpIfEq { .. }
                | Instr::JumpIfLe { .. }
                | Instr::JumpIfLt { .. }
                | Instr::JumpIfNotEq { .. }
                | Instr::JumpIfNotLe { .. }
                | Instr::JumpIfNotLt { .. }
                | Instr::JumpXEqKNil { .. }
                | Instr::JumpXEqKB { .. }
                | Instr::JumpXEqKN { .. }
                | Instr::JumpXEqKS { .. }
                | Instr::FornPrep { .. }
                | Instr::FornLoop { .. }
                | Instr::ForgPrep { .. }
                | Instr::ForgPrepInext { .. }
                | Instr::ForgPrepNext { .. }
                | Instr::ForgLoop { .. }
                | Instr::Return { .. }
        )
    }

    /// Returns the indices of a physical register this instruction
    /// writes to, if any.
    pub fn written_registers(&self) -> SmallVec<[u8; 4]> {
        match &self {
            Instr::LoadNil { reg }
            | Instr::LoadB { reg, .. }
            | Instr::LoadN { reg, .. }
            | Instr::LoadK { reg, .. }
            | Instr::Move { dest: reg, .. }
            | Instr::GetGlobal { dest: reg, .. }
            | Instr::GetUpval { dest: reg, .. }
            | Instr::GetImport { dest: reg, .. }
            | Instr::GetTable { dest: reg, .. }
            | Instr::GetTableKS { dest: reg, .. }
            | Instr::GetUDataKS { dest: reg, .. }
            | Instr::NewClosure { dest: reg, .. }
            | Instr::Add { dest: reg, .. }
            | Instr::Sub { dest: reg, .. }
            | Instr::Mul { dest: reg, .. }
            | Instr::Div { dest: reg, .. }
            | Instr::Mod { dest: reg, .. }
            | Instr::Pow { dest: reg, .. }
            | Instr::AddK { dest: reg, .. }
            | Instr::SubK { dest: reg, .. }
            | Instr::MulK { dest: reg, .. }
            | Instr::DivK { dest: reg, .. }
            | Instr::ModK { dest: reg, .. }
            | Instr::PowK { dest: reg, .. }
            | Instr::And { dest: reg, .. }
            | Instr::Or { dest: reg, .. }
            | Instr::AndK { dest: reg, .. }
            | Instr::OrK { dest: reg, .. }
            | Instr::Concat { dest: reg, .. }
            | Instr::Not { dest: reg, .. }
            | Instr::Minus { dest: reg, .. }
            | Instr::Length { dest: reg, .. }
            | Instr::NewTable { dest: reg, .. }
            | Instr::DupTable { dest: reg, .. }
            | Instr::SetList { table: reg, .. }
            | Instr::DupClosure { dest: reg, .. }
            | Instr::SubRK { dest: reg, .. }
            | Instr::DivRK { dest: reg, .. }
            | Instr::IDiv { dest: reg, .. }
            | Instr::IDivK { dest: reg, .. } => smallvec![*reg],

            Instr::ForgLoop {
                base, var_count, ..
            } => {
                let base = *base + 3;
                debug_assert!(
                    base.checked_add(*var_count).is_some(),
                    "CALL return register overflow"
                );
                (base..base + *var_count).collect()
            }
            Instr::FornLoop { base, .. } => {
                let reg = *base + 2;
                smallvec![reg]
            }

            Instr::Call {
                func, ret_count, ..
            } => match Count::from(*ret_count) {
                Count::Number(n) => reg_range(*func, n).collect(),
                // TODO: how do you even determine this?
                Count::Variadic => smallvec![],
            },

            Instr::GetVarArgs { dest, count } => match Count::from(*count) {
                Count::Number(n) => reg_range(*dest, n).collect(),
                Count::Variadic => unreachable!(),
            },

            _ => smallvec![],
        }
    }

    pub fn new(value: u32, aux: Option<u32>) -> Result<Self> {
        let opcode = (value & 0xff) as u8;
        ensure!(
            opcode < Self::LOP_COUNT,
            "invalid Luau opcode {} in header word 0x{value:08x}",
            opcode
        );

        // ABC encoding
        let a = ((value >> 8) & 0xff) as u8;
        let b = ((value >> 16) & 0xff) as u8;
        let c = ((value >> 24) & 0xff) as u8;

        // AD encoding (sign-extended 16-bit D)
        let d = ((value as i32) >> 16) as i16;

        // E encoding (sign-extended 24-bit E)
        let e = (value as i32) >> 8;

        let d_index = u16::try_from(d).unwrap_or(0);

        let aux_word = aux.unwrap_or(0);
        let aux_a = (aux_word & 0xff) as u8;
        let aux_b = ((aux_word >> 8) & 0xff) as u8;
        let aux_kv = aux_word & 0x00ff_ffff;
        let aux_kv16 = (aux_word & 0xffff) as u16;
        let aux_slot = (aux_word >> 16) as u16;
        let aux_not = (aux_word >> 31) != 0;

        let instr = match opcode {
            0 => Instr::Nop,
            1 => Instr::Break,
            2 => Instr::LoadNil { reg: a },
            3 => Instr::LoadB {
                reg: a,
                value: b != 0,
                jump: c,
            },
            4 => Instr::LoadN { reg: a, value: d },
            5 => Instr::LoadK {
                reg: a,
                index: d_index,
            },
            6 => Instr::Move { dest: a, src: b },
            7 => Instr::GetGlobal {
                dest: a,
                slot: c,
                key: aux_word,
            },
            8 => Instr::SetGlobal {
                src: a,
                slot: c,
                key: aux_word,
            },
            9 => Instr::GetUpval { dest: a, upval: b },
            10 => Instr::SetUpval { src: a, upval: b },
            11 => Instr::CloseUpvals { reg: a },
            12 => Instr::GetImport {
                dest: a,
                index: d_index,
                path: aux_word,
            },
            13 => Instr::GetTable {
                dest: a,
                table: b,
                key: c,
            },
            14 => Instr::SetTable {
                src: a,
                table: b,
                key: c,
            },
            15 => Instr::GetTableKS {
                dest: a,
                table: b,
                slot: c,
                key: aux_word,
            },
            16 => Instr::SetTableKS {
                src: a,
                table: b,
                slot: c,
                key: aux_word,
            },
            17 => Instr::GetTableN {
                dest: a,
                table: b,
                index: u16::from(c) + 1,
            },
            18 => Instr::SetTableN {
                src: a,
                table: b,
                index: u16::from(c) + 1,
            },
            19 => Instr::NewClosure {
                dest: a,
                proto: d_index,
            },
            20 => Instr::NameCall {
                dest: a,
                object: b,
                slot: c,
                method: aux_word,
            },
            21 => Instr::Call {
                func: a,
                arg_count: b,
                ret_count: c,
            },
            22 => Instr::Return { base: a, count: b },
            23 => Instr::Jump { offset: d },
            24 => Instr::JumpBack { offset: d },
            25 => Instr::JumpIf { reg: a, offset: d },
            26 => Instr::JumpIfNot { reg: a, offset: d },
            27 => Instr::JumpIfEq {
                reg: a,
                aux: aux_a,
                offset: d,
            },
            28 => Instr::JumpIfLe {
                reg: a,
                aux: aux_a,
                offset: d,
            },
            29 => Instr::JumpIfLt {
                reg: a,
                aux: aux_a,
                offset: d,
            },
            30 => Instr::JumpIfNotEq {
                reg: a,
                aux: aux_a,
                offset: d,
            },
            31 => Instr::JumpIfNotLe {
                reg: a,
                aux: aux_a,
                offset: d,
            },
            32 => Instr::JumpIfNotLt {
                reg: a,
                aux: aux_a,
                offset: d,
            },
            33 => Instr::Add {
                dest: a,
                a: b,
                b: c,
            },
            34 => Instr::Sub {
                dest: a,
                a: b,
                b: c,
            },
            35 => Instr::Mul {
                dest: a,
                a: b,
                b: c,
            },
            36 => Instr::Div {
                dest: a,
                a: b,
                b: c,
            },
            37 => Instr::Mod {
                dest: a,
                a: b,
                b: c,
            },
            38 => Instr::Pow {
                dest: a,
                a: b,
                b: c,
            },
            39 => Instr::AddK {
                dest: a,
                reg: b,
                k: c,
            },
            40 => Instr::SubK {
                dest: a,
                reg: b,
                k: c,
            },
            41 => Instr::MulK {
                dest: a,
                reg: b,
                k: c,
            },
            42 => Instr::DivK {
                dest: a,
                reg: b,
                k: c,
            },
            43 => Instr::ModK {
                dest: a,
                reg: b,
                k: c,
            },
            44 => Instr::PowK {
                dest: a,
                reg: b,
                k: c,
            },
            45 => Instr::And {
                dest: a,
                a: b,
                b: c,
            },
            46 => Instr::Or {
                dest: a,
                a: b,
                b: c,
            },
            47 => Instr::AndK {
                dest: a,
                reg: b,
                k: c,
            },
            48 => Instr::OrK {
                dest: a,
                reg: b,
                k: c,
            },
            49 => Instr::Concat {
                dest: a,
                a: b,
                b: c,
            },
            50 => Instr::Not { dest: a, reg: b },
            51 => Instr::Minus { dest: a, reg: b },
            52 => Instr::Length { dest: a, reg: b },
            53 => Instr::NewTable {
                dest: a,
                hash_size: b,
                array_size: aux_word,
            },
            54 => Instr::DupTable {
                dest: a,
                k: d_index,
            },
            55 => Instr::SetList {
                table: a,
                base: b,
                count: c,
                index: aux_word,
            },
            56 => Instr::FornPrep { base: a, offset: d },
            57 => Instr::FornLoop { base: a, offset: d },
            58 => Instr::ForgLoop {
                base: a,
                offset: d,
                var_count: aux_a,
                ipairs: aux_not,
            },
            59 => Instr::ForgPrepInext { base: a, offset: d },
            60 => Instr::FastCall3 {
                builtin: a,
                arg1: b,
                arg2: aux_a,
                arg3: aux_b,
                jump: c,
            },
            61 => Instr::ForgPrepNext { base: a, offset: d },
            62 => Instr::NativeCall,
            63 => Instr::GetVarArgs { dest: a, count: b },
            64 => Instr::DupClosure {
                dest: a,
                k: d_index,
            },
            65 => Instr::PrepVarArgs { nparams: a },
            66 => Instr::LoadKX {
                reg: a,
                index: aux_word,
            },
            67 => Instr::JumpX { offset: e },
            68 => Instr::FastCall {
                builtin: a,
                jump: c,
            },
            69 => Instr::Coverage,
            70 => Instr::Capture {
                capture_type: a,
                reg: b,
            },
            71 => Instr::SubRK {
                dest: a,
                k: b,
                reg: c,
            },
            72 => Instr::DivRK {
                dest: a,
                k: b,
                reg: c,
            },
            73 => Instr::FastCall1 {
                builtin: a,
                arg: b,
                jump: c,
            },
            74 => Instr::FastCall2 {
                builtin: a,
                arg1: b,
                arg2: aux_a,
                jump: c,
            },
            75 => Instr::FastCall2K {
                builtin: a,
                arg: b,
                k: aux_word,
                jump: c,
            },
            76 => Instr::ForgPrep { base: a, offset: d },
            77 => Instr::JumpXEqKNil {
                reg: a,
                invert: aux_not,
                offset: d,
            },
            78 => Instr::JumpXEqKB {
                reg: a,
                k: (aux_word & 0x1) != 0,
                invert: aux_not,
                offset: d,
            },
            79 => Instr::JumpXEqKN {
                reg: a,
                k: aux_kv,
                invert: aux_not,
                offset: d,
            },
            80 => Instr::JumpXEqKS {
                reg: a,
                k: aux_kv,
                invert: aux_not,
                offset: d,
            },
            81 => Instr::IDiv {
                dest: a,
                a: b,
                b: c,
            },
            82 => Instr::IDivK {
                dest: a,
                reg: b,
                k: c,
            },
            83 => Instr::GetUDataKS {
                dest: a,
                userdata: b,
                slot: aux_slot,
                key: aux_kv16,
            },
            84 => Instr::SetUDataKS {
                src: a,
                userdata: b,
                slot: aux_slot,
                key: aux_kv16,
            },
            85 => Instr::NameCallUData {
                dest: a,
                object: b,
                slot: aux_slot,
                method: aux_kv16,
            },
            _ => unreachable!("opcode range was validated"),
        };

        Ok(instr)
    }
}

impl fmt::Display for Instr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // basic loads/moves
            Instr::Nop => write!(f, "NOP"),
            Instr::Break => write!(f, "BREAK"),
            Instr::LoadNil { reg } => write!(f, "LOADNIL R{reg}"),
            Instr::LoadB { reg, value, jump } => write!(f, "LOADB R{reg} {value} +{jump}"),
            Instr::LoadN { reg, value } => write!(f, "LOADN R{reg} {value}"),
            Instr::LoadK { reg, index } => write!(f, "LOADK R{reg} K{index}"),
            Instr::Move { dest, src } => write!(f, "MOVE R{dest} R{src}"),

            // globals/upvalues/imports
            // `slot` is a runtime cache hint, not meaningful in disassembly
            Instr::GetGlobal { dest, key, .. } => write!(f, "GETGLOBAL R{dest} K{key}"),
            Instr::SetGlobal { src, key, .. } => write!(f, "SETGLOBAL R{src} K{key}"),
            Instr::GetUpval { dest, upval } => write!(f, "GETUPVAL R{dest} U{upval}"),
            Instr::SetUpval { src, upval } => write!(f, "SETUPVAL R{src} U{upval}"),
            Instr::CloseUpvals { reg } => write!(f, "CLOSEUPVALS R{reg}"),
            // `path` is the aux word encoding the import chain, shown separately if needed
            Instr::GetImport { dest, index, .. } => write!(f, "GETIMPORT R{dest} {index}"),

            // table access
            Instr::GetTable { dest, table, key } => write!(f, "GETTABLE R{dest} R{table} R{key}"),
            Instr::SetTable { src, table, key } => write!(f, "SETTABLE R{src} R{table} R{key}"),
            Instr::GetTableKS {
                dest, table, key, ..
            } => write!(f, "GETTABLEKS R{dest} R{table} K{key}"),
            Instr::SetTableKS {
                src, table, key, ..
            } => write!(f, "SETTABLEKS R{src} R{table} K{key}"),
            Instr::GetUDataKS {
                dest,
                userdata,
                key,
                ..
            } => write!(f, "GETUDATAKS R{dest} R{userdata} K{key}"),
            Instr::SetUDataKS {
                src, userdata, key, ..
            } => write!(f, "SETUDATAKS R{src} R{userdata} K{key}"),
            Instr::GetTableN { dest, table, index } => {
                write!(f, "GETTABLEN R{dest} R{table} {index}")
            }
            Instr::SetTableN { src, table, index } => {
                write!(f, "SETTABLEN R{src} R{table} {index}")
            }
            Instr::NewClosure { dest, proto } => write!(f, "NEWCLOSURE R{dest} P{proto}"),
            Instr::NameCall {
                dest,
                object,
                method,
                ..
            } => write!(f, "NAMECALL R{dest} R{object} K{method}"),
            Instr::NameCallUData {
                dest,
                object,
                method,
                ..
            } => write!(f, "NAMECALLUDATA R{dest} R{object} K{method}"),

            // calls, returns, branches
            Instr::Call {
                func,
                arg_count,
                ret_count,
            } => write!(f, "CALL R{func} {arg_count} {ret_count}"),
            Instr::Return { base, count } => write!(f, "RETURN R{base} {count}"),
            Instr::Jump { offset } => write!(f, "JUMP {offset:+}"),
            Instr::JumpBack { offset } => write!(f, "JUMPBACK {offset:+}"),
            Instr::JumpIf { reg, offset } => write!(f, "JUMPIF R{reg} {offset:+}"),
            Instr::JumpIfNot { reg, offset } => write!(f, "JUMPIFNOT R{reg} {offset:+}"),
            Instr::JumpIfEq { reg, aux, offset } => write!(f, "JUMPIFEQ R{reg} R{aux} {offset:+}"),
            Instr::JumpIfLe { reg, aux, offset } => write!(f, "JUMPIFLE R{reg} R{aux} {offset:+}"),
            Instr::JumpIfLt { reg, aux, offset } => write!(f, "JUMPIFLT R{reg} R{aux} {offset:+}"),
            Instr::JumpIfNotEq { reg, aux, offset } => {
                write!(f, "JUMPIFNOTEQ R{reg} R{aux} {offset:+}")
            }
            Instr::JumpIfNotLe { reg, aux, offset } => {
                write!(f, "JUMPIFNOTLE R{reg} R{aux} {offset:+}")
            }
            Instr::JumpIfNotLt { reg, aux, offset } => {
                write!(f, "JUMPIFNOTLT R{reg} R{aux} {offset:+}")
            }

            // arithmetic/logical/unary
            Instr::Add { dest, a, b } => write!(f, "ADD R{dest} R{a} R{b}"),
            Instr::Sub { dest, a, b } => write!(f, "SUB R{dest} R{a} R{b}"),
            Instr::Mul { dest, a, b } => write!(f, "MUL R{dest} R{a} R{b}"),
            Instr::Div { dest, a, b } => write!(f, "DIV R{dest} R{a} R{b}"),
            Instr::Mod { dest, a, b } => write!(f, "MOD R{dest} R{a} R{b}"),
            Instr::Pow { dest, a, b } => write!(f, "POW R{dest} R{a} R{b}"),
            Instr::AddK { dest, reg, k } => write!(f, "ADDK R{dest} R{reg} K{k}"),
            Instr::SubK { dest, reg, k } => write!(f, "SUBK R{dest} R{reg} K{k}"),
            Instr::MulK { dest, reg, k } => write!(f, "MULK R{dest} R{reg} K{k}"),
            Instr::DivK { dest, reg, k } => write!(f, "DIVK R{dest} R{reg} K{k}"),
            Instr::ModK { dest, reg, k } => write!(f, "MODK R{dest} R{reg} K{k}"),
            Instr::PowK { dest, reg, k } => write!(f, "POWK R{dest} R{reg} K{k}"),
            Instr::And { dest, a, b } => write!(f, "AND R{dest} R{a} R{b}"),
            Instr::Or { dest, a, b } => write!(f, "OR R{dest} R{a} R{b}"),
            Instr::AndK { dest, reg, k } => write!(f, "ANDK R{dest} R{reg} K{k}"),
            Instr::OrK { dest, reg, k } => write!(f, "ORK R{dest} R{reg} K{k}"),
            Instr::Concat { dest, a, b } => write!(f, "CONCAT R{dest} R{a} R{b}"),
            Instr::Not { dest, reg } => write!(f, "NOT R{dest} R{reg}"),
            Instr::Minus { dest, reg } => write!(f, "MINUS R{dest} R{reg}"),
            Instr::Length { dest, reg } => write!(f, "LENGTH R{dest} R{reg}"),

            // table construction and loop ops
            Instr::NewTable {
                dest,
                hash_size,
                array_size,
            } => write!(f, "NEWTABLE R{dest} {hash_size} {array_size}"),
            Instr::DupTable { dest, k } => write!(f, "DUPTABLE R{dest} K{k}"),
            Instr::SetList {
                table,
                base,
                count,
                index,
            } => write!(f, "SETLIST R{table} R{base} {count} {index}"),
            Instr::FornPrep { base, offset } => write!(f, "FORNPREP R{base} {offset:+}"),
            Instr::FornLoop { base, offset } => write!(f, "FORNLOOP R{base} {offset:+}"),
            Instr::ForgLoop {
                base,
                offset,
                var_count,
                ..
            } => write!(f, "FORGLOOP R{base} {offset:+} {var_count}"),
            Instr::ForgPrepInext { base, offset } => write!(f, "FORGPREP_INEXT R{base} {offset:+}"),
            Instr::ForgPrepNext { base, offset } => write!(f, "FORGPREP_NEXT R{base} {offset:+}"),
            Instr::ForgPrep { base, offset } => write!(f, "FORGPREP R{base} {offset:+}"),

            // fastcall, varargs, closure helpers, extended ops
            Instr::FastCall { builtin, jump } => write!(f, "FASTCALL {builtin} {jump:+}"),
            Instr::FastCall1 { builtin, arg, jump } => {
                write!(f, "FASTCALL1 {builtin} R{arg} {jump:+}")
            }
            Instr::FastCall2 {
                builtin,
                arg1,
                arg2,
                jump,
            } => write!(f, "FASTCALL2 {builtin} R{arg1} R{arg2} {jump:+}"),
            Instr::FastCall2K {
                builtin,
                arg,
                k,
                jump,
            } => write!(f, "FASTCALL2K {builtin} R{arg} K{k} {jump:+}"),
            Instr::FastCall3 {
                builtin,
                arg1,
                arg2,
                arg3,
                jump,
            } => write!(f, "FASTCALL3 {builtin} R{arg1} R{arg2} R{arg3} {jump:+}"),
            Instr::NativeCall => write!(f, "NATIVECALL"),
            Instr::GetVarArgs { dest, count } => write!(f, "GETVARARGS R{dest} {count}"),
            Instr::PrepVarArgs { nparams } => write!(f, "PREPVARARGS {nparams}"),
            Instr::DupClosure { dest, k } => write!(f, "DUPCLOSURE R{dest} K{k}"),
            Instr::Capture { capture_type, reg } => write!(f, "CAPTURE {capture_type} R{reg}"),
            Instr::LoadKX { reg, index } => write!(f, "LOADKX R{reg} K{index}"),
            Instr::JumpX { offset } => write!(f, "JUMPX {offset:+}"),
            Instr::Coverage => write!(f, "COVERAGE"),
            Instr::SubRK { dest, k, reg } => write!(f, "SUBRK R{dest} K{k} R{reg}"),
            Instr::DivRK { dest, k, reg } => write!(f, "DIVRK R{dest} K{k} R{reg}"),

            // extended comparisons — invert flag shown as trailing `!`
            Instr::JumpXEqKNil {
                reg,
                invert,
                offset,
            } => {
                write!(f, "JUMPXEQKNIL R{reg} {offset:+}")?;
                if *invert { write!(f, " !") } else { Ok(()) }
            }
            Instr::JumpXEqKB {
                reg,
                k,
                invert,
                offset,
            } => {
                write!(f, "JUMPXEQKB R{reg} {k} {offset:+}")?;
                if *invert { write!(f, " !") } else { Ok(()) }
            }
            Instr::JumpXEqKN {
                reg,
                k,
                invert,
                offset,
            } => {
                write!(f, "JUMPXEQKN R{reg} K{k} {offset:+}")?;
                if *invert { write!(f, " !") } else { Ok(()) }
            }
            Instr::JumpXEqKS {
                reg,
                k,
                invert,
                offset,
            } => {
                write!(f, "JUMPXEQKS R{reg} K{k} {offset:+}")?;
                if *invert { write!(f, " !") } else { Ok(()) }
            }

            // floor division
            Instr::IDiv { dest, a, b } => write!(f, "IDIV R{dest} R{a} R{b}"),
            Instr::IDivK { dest, reg, k } => write!(f, "IDIVK R{dest} R{reg} K{k}"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct LocalDebug {
    pub name: StringId,
    pub start_pc: usize,
    pub end_pc: usize,
    pub register: u8,
}

/// A free-standing representation of value's type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BytecodeType {
    Nil,
    Boolean,
    Number,
    String,
    Table,
    Function,
    Thread,
    Userdata,
    Vector,
    Buffer,
    Integer,
    Any,
    TaggedUserdata(u8),
    Unknown(u8),
}

impl BytecodeType {
    const OPTIONAL: u8 = 0x80;

    const fn from_byte(value: u8) -> Self {
        match value & !Self::OPTIONAL {
            0 => Self::Nil,
            1 => Self::Boolean,
            2 => Self::Number,
            3 => Self::String,
            4 => Self::Table,
            5 => Self::Function,
            6 => Self::Thread,
            7 => Self::Userdata,
            8 => Self::Vector,
            9 => Self::Buffer,
            10 => Self::Integer,
            15 => Self::Any,
            tag @ 64..=95 => Self::TaggedUserdata(tag - 64),
            other => Self::Unknown(other),
        }
    }
}

impl fmt::Display for BytecodeType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Nil => write!(f, "nil"),
            Self::Boolean => write!(f, "boolean"),
            Self::Number => write!(f, "number"),
            Self::String => write!(f, "string"),
            Self::Table => write!(f, "table"),
            Self::Function => write!(f, "function"),
            Self::Thread => write!(f, "thread"),
            Self::Userdata => write!(f, "userdata"),
            Self::Vector => write!(f, "vector"),
            Self::Buffer => write!(f, "buffer"),
            Self::Integer => write!(f, "integer"),
            Self::Any => write!(f, "any"),
            Self::TaggedUserdata(index) => write!(f, "tagged-userdata[{index}]"),
            Self::Unknown(value) => write!(f, "unknown-type({value})"),
        }
    }
}

/// A type tag of a symbol.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TypeTag {
    pub ty: BytecodeType,
    pub optional: bool,
    pub raw: u8,
}

impl TypeTag {
    pub const fn from_byte(value: u8) -> Self {
        Self {
            ty: BytecodeType::from_byte(value),
            optional: value & BytecodeType::OPTIONAL != 0,
            raw: value,
        }
    }
}

impl fmt::Display for TypeTag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.ty)?;

        if self.optional {
            write!(f, "?")?;
        }

        Ok(())
    }
}

#[derive(Debug, Default, Clone)]
pub struct FunctionTypeInfo {
    pub num_params: u8,
    pub params: Vec<TypeTag>,
}

#[derive(Debug, Clone)]
pub struct LocalTypeInfo {
    pub ty: TypeTag,
    pub register: u8,
    pub start_pc: usize,
    pub end_pc: usize,
}

#[derive(Debug, Default, Clone)]
pub struct ProtoTypeInfo {
    pub function: Option<FunctionTypeInfo>,
    pub upvalues: Vec<TypeTag>,
    pub locals: Vec<LocalTypeInfo>,
}

#[derive(Debug, Clone)]
pub struct UserdataTypeMapping {
    pub index: u8,
    pub name: Option<StringId>,
}

#[derive(Debug, Clone)]
pub struct Proto {
    pub id: ProtoId,
    pub max_stack_size: u8,
    pub num_params: u8,
    pub num_upvals: u8,
    pub is_vararg: bool,
    pub flags: u8,
    pub type_info: ProtoTypeInfo,
    pub instrs: Vec<Spanned<Instr>>,
    pub consts: Vec<Constant>,
    pub child_protos: Vec<ProtoId>,
    pub debug_name: Option<StringId>,
    pub locals: Vec<LocalDebug>,
}

impl Proto {
    /// Resolves a constant by its index.
    #[inline]
    pub fn get_constant(&self, id: ConstId) -> Option<&Constant> {
        self.consts.get(id.0 as usize)
    }

    /// Resolves a proto by its index.
    #[inline]
    pub fn get_child_proto(&self, id: ChildProtoId) -> Option<ProtoId> {
        self.child_protos.get(id.0 as usize).copied()
    }
}

/// Adds an offset to a register.
///
/// # Panics
///
/// Panics if the register overflow occurs.
pub const fn reg_add(reg: u8, offset: u8) -> u8 {
    reg.checked_add(offset).expect("register overflow")
}

/// Returns an iterator over a range of registers.
///
/// # Panics
///
/// Panics if the register range overflow occurs.
pub const fn reg_range(start: u8, count: u8) -> impl Iterator<Item = u8> {
    let end = start.checked_add(count).expect("register range overflow");
    start..end
}
