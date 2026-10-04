use std::fmt;

use anyhow::{Result, ensure};
use smallvec::{SmallVec, smallvec};

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
    pub const fn new(encoded: u8) -> Self {
        match encoded {
            0 => Count::Variadic,
            n => Count::Number(n - 1),
        }
    }

    /// Returns whether this count is variadic.
    pub const fn is_variadic(&self) -> bool {
        matches!(self, Count::Variadic)
    }
}

impl From<u8> for Count {
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
    /// dest = concat(R(a), R(a+1), ..., R(b))
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

/// A decoded Luau instruction paired with its header word position.
///
/// Instruction indices cannot stand in for word positions because instructions
/// that consume an AUX word advance the bytecode program counter by two words.
#[derive(Debug, Clone, Copy)]
pub struct DecodedInstr {
    /// The decoded instruction payload.
    pub instr: Instr,
    /// The zero-based word position of the instruction header in the bytecode stream.
    pub word_pc: u32,
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

/// One operand of an instruction, as it appears in a listing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Operand {
    /// A register.
    Reg(u8),
    /// An upvalue slot.
    Upval(u8),
    /// An index into the constant table.
    Const(u32),
    /// An index into the constant table holding an import path.
    Import(u16),
    /// An index into the child proto table.
    ChildProto(u16),
    /// An immediate integer.
    Int(i64),
    /// An immediate boolean.
    Bool(bool),
    /// An encoded count, where zero means "up to the top of the stack".
    Count(u8),
    /// An encoded table hash size, `0` or `ceil(log2(size)) + 1`.
    HashSize(u8),
    /// A branch offset in words, relative to the next instruction word.
    Jump(i32),
    /// A fastcall skip distance in instructions.
    Skip(u8),
    /// A fastcall builtin function id.
    Builtin(u8),
    /// A CAPTURE kind.
    Capture(u8),
    /// The inversion flag of a `JUMPXEQK*` instruction.
    Not,
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operand::Reg(reg) => write!(f, "R{reg}"),
            Operand::Upval(upval) => write!(f, "U{upval}"),
            Operand::Const(k) => write!(f, "K{k}"),
            Operand::Import(k) => write!(f, "{k}"),
            Operand::ChildProto(proto) => write!(f, "P{proto}"),
            Operand::Int(value) => write!(f, "{value}"),
            Operand::Bool(value) => write!(f, "{value}"),
            Operand::Count(count) | Operand::HashSize(count) => write!(f, "{count}"),
            Operand::Jump(offset) => write!(f, "{offset:+}"),
            Operand::Skip(skip) => write!(f, "+{skip}"),
            Operand::Builtin(builtin) | Operand::Capture(builtin) => write!(f, "{builtin}"),
            Operand::Not => write!(f, "!"),
        }
    }
}

/// The operands of one instruction, in listing order.
pub type Operands = SmallVec<[Operand; 4]>;

impl Instr {
    /// Returns the assembly mnemonic of this instruction.
    #[must_use]
    pub const fn mnemonic(&self) -> &'static str {
        match self {
            Instr::Nop => "NOP",
            Instr::Break => "BREAK",
            Instr::LoadNil { .. } => "LOADNIL",
            Instr::LoadB { .. } => "LOADB",
            Instr::LoadN { .. } => "LOADN",
            Instr::LoadK { .. } => "LOADK",
            Instr::Move { .. } => "MOVE",
            Instr::GetGlobal { .. } => "GETGLOBAL",
            Instr::SetGlobal { .. } => "SETGLOBAL",
            Instr::GetUpval { .. } => "GETUPVAL",
            Instr::SetUpval { .. } => "SETUPVAL",
            Instr::CloseUpvals { .. } => "CLOSEUPVALS",
            Instr::GetImport { .. } => "GETIMPORT",
            Instr::GetTable { .. } => "GETTABLE",
            Instr::SetTable { .. } => "SETTABLE",
            Instr::GetTableKS { .. } => "GETTABLEKS",
            Instr::SetTableKS { .. } => "SETTABLEKS",
            Instr::GetTableN { .. } => "GETTABLEN",
            Instr::SetTableN { .. } => "SETTABLEN",
            Instr::NewClosure { .. } => "NEWCLOSURE",
            Instr::NameCall { .. } => "NAMECALL",
            Instr::Call { .. } => "CALL",
            Instr::Return { .. } => "RETURN",
            Instr::Jump { .. } => "JUMP",
            Instr::JumpBack { .. } => "JUMPBACK",
            Instr::JumpIf { .. } => "JUMPIF",
            Instr::JumpIfNot { .. } => "JUMPIFNOT",
            Instr::JumpIfEq { .. } => "JUMPIFEQ",
            Instr::JumpIfLe { .. } => "JUMPIFLE",
            Instr::JumpIfLt { .. } => "JUMPIFLT",
            Instr::JumpIfNotEq { .. } => "JUMPIFNOTEQ",
            Instr::JumpIfNotLe { .. } => "JUMPIFNOTLE",
            Instr::JumpIfNotLt { .. } => "JUMPIFNOTLT",
            Instr::Add { .. } => "ADD",
            Instr::Sub { .. } => "SUB",
            Instr::Mul { .. } => "MUL",
            Instr::Div { .. } => "DIV",
            Instr::Mod { .. } => "MOD",
            Instr::Pow { .. } => "POW",
            Instr::AddK { .. } => "ADDK",
            Instr::SubK { .. } => "SUBK",
            Instr::MulK { .. } => "MULK",
            Instr::DivK { .. } => "DIVK",
            Instr::ModK { .. } => "MODK",
            Instr::PowK { .. } => "POWK",
            Instr::And { .. } => "AND",
            Instr::Or { .. } => "OR",
            Instr::AndK { .. } => "ANDK",
            Instr::OrK { .. } => "ORK",
            Instr::Concat { .. } => "CONCAT",
            Instr::Not { .. } => "NOT",
            Instr::Minus { .. } => "MINUS",
            Instr::Length { .. } => "LENGTH",
            Instr::NewTable { .. } => "NEWTABLE",
            Instr::DupTable { .. } => "DUPTABLE",
            Instr::SetList { .. } => "SETLIST",
            Instr::FornPrep { .. } => "FORNPREP",
            Instr::FornLoop { .. } => "FORNLOOP",
            Instr::ForgLoop { .. } => "FORGLOOP",
            Instr::ForgPrepInext { .. } => "FORGPREP_INEXT",
            Instr::FastCall3 { .. } => "FASTCALL3",
            Instr::ForgPrepNext { .. } => "FORGPREP_NEXT",
            Instr::NativeCall => "NATIVECALL",
            Instr::GetVarArgs { .. } => "GETVARARGS",
            Instr::DupClosure { .. } => "DUPCLOSURE",
            Instr::PrepVarArgs { .. } => "PREPVARARGS",
            Instr::LoadKX { .. } => "LOADKX",
            Instr::JumpX { .. } => "JUMPX",
            Instr::FastCall { .. } => "FASTCALL",
            Instr::Coverage => "COVERAGE",
            Instr::Capture { .. } => "CAPTURE",
            Instr::SubRK { .. } => "SUBRK",
            Instr::DivRK { .. } => "DIVRK",
            Instr::FastCall1 { .. } => "FASTCALL1",
            Instr::FastCall2 { .. } => "FASTCALL2",
            Instr::FastCall2K { .. } => "FASTCALL2K",
            Instr::ForgPrep { .. } => "FORGPREP",
            Instr::JumpXEqKNil { .. } => "JUMPXEQKNIL",
            Instr::JumpXEqKB { .. } => "JUMPXEQKB",
            Instr::JumpXEqKN { .. } => "JUMPXEQKN",
            Instr::JumpXEqKS { .. } => "JUMPXEQKS",
            Instr::IDiv { .. } => "IDIV",
            Instr::IDivK { .. } => "IDIVK",
            Instr::GetUDataKS { .. } => "GETUDATAKS",
            Instr::SetUDataKS { .. } => "SETUDATAKS",
            Instr::NameCallUData { .. } => "NAMECALLUDATA",
        }
    }

    /// Returns the operands of this instruction in listing order.
    ///
    /// Runtime cache hints (`slot` fields) and aux words already folded into
    /// another operand are left out.
    #[must_use]
    pub fn operands(&self) -> Operands {
        use Operand::{
            Bool, Builtin, ChildProto, Const, Count, HashSize, Import, Int, Jump, Reg, Skip, Upval,
        };

        let mut ops: Operands = match *self {
            Instr::Nop | Instr::Break | Instr::NativeCall | Instr::Coverage => smallvec![],

            Instr::LoadNil { reg } => smallvec![Reg(reg)],
            Instr::LoadB { reg, value, jump } if jump > 0 => {
                smallvec![Reg(reg), Bool(value), Jump(jump.into())]
            }
            Instr::LoadB { reg, value, .. } => smallvec![Reg(reg), Bool(value)],
            Instr::LoadN { reg, value } => smallvec![Reg(reg), Int(value.into())],
            Instr::LoadK { reg, index } => smallvec![Reg(reg), Const(index.into())],
            Instr::LoadKX { reg, index } => smallvec![Reg(reg), Const(index)],
            Instr::Move { dest, src } => smallvec![Reg(dest), Reg(src)],

            Instr::GetGlobal { dest: reg, key, .. } | Instr::SetGlobal { src: reg, key, .. } => {
                smallvec![Reg(reg), Const(key)]
            }
            Instr::GetUpval { dest: reg, upval } | Instr::SetUpval { src: reg, upval } => {
                smallvec![Reg(reg), Upval(upval)]
            }
            Instr::CloseUpvals { reg } => smallvec![Reg(reg)],
            Instr::GetImport { dest, index, .. } => smallvec![Reg(dest), Import(index)],

            Instr::GetTable {
                dest: a,
                table,
                key,
            }
            | Instr::SetTable { src: a, table, key } => smallvec![Reg(a), Reg(table), Reg(key)],
            Instr::GetTableKS {
                dest: a,
                table,
                key,
                ..
            }
            | Instr::SetTableKS {
                src: a, table, key, ..
            }
            | Instr::NameCall {
                dest: a,
                object: table,
                method: key,
                ..
            } => smallvec![Reg(a), Reg(table), Const(key)],
            Instr::GetUDataKS {
                dest: a,
                userdata: table,
                key,
                ..
            }
            | Instr::SetUDataKS {
                src: a,
                userdata: table,
                key,
                ..
            }
            | Instr::NameCallUData {
                dest: a,
                object: table,
                method: key,
                ..
            } => smallvec![Reg(a), Reg(table), Const(key.into())],
            Instr::GetTableN {
                dest: a,
                table,
                index,
            }
            | Instr::SetTableN {
                src: a,
                table,
                index,
            } => {
                smallvec![Reg(a), Reg(table), Int(index.into())]
            }
            Instr::NewClosure { dest, proto } => smallvec![Reg(dest), ChildProto(proto)],

            Instr::Call {
                func,
                arg_count,
                ret_count,
            } => smallvec![Reg(func), Count(arg_count), Count(ret_count)],
            Instr::Return { base, count } => smallvec![Reg(base), Count(count)],
            Instr::Jump { offset } | Instr::JumpBack { offset } => smallvec![Jump(offset.into())],
            Instr::JumpX { offset } => smallvec![Jump(offset)],
            Instr::JumpIf { reg, offset } | Instr::JumpIfNot { reg, offset } => {
                smallvec![Reg(reg), Jump(offset.into())]
            }
            Instr::JumpIfEq { reg, aux, offset }
            | Instr::JumpIfLe { reg, aux, offset }
            | Instr::JumpIfLt { reg, aux, offset }
            | Instr::JumpIfNotEq { reg, aux, offset }
            | Instr::JumpIfNotLe { reg, aux, offset }
            | Instr::JumpIfNotLt { reg, aux, offset } => {
                smallvec![Reg(reg), Reg(aux), Jump(offset.into())]
            }

            Instr::Add { dest, a, b }
            | Instr::Sub { dest, a, b }
            | Instr::Mul { dest, a, b }
            | Instr::Div { dest, a, b }
            | Instr::Mod { dest, a, b }
            | Instr::Pow { dest, a, b }
            | Instr::IDiv { dest, a, b }
            | Instr::And { dest, a, b }
            | Instr::Or { dest, a, b }
            | Instr::Concat { dest, a, b } => smallvec![Reg(dest), Reg(a), Reg(b)],
            Instr::AddK { dest, reg, k }
            | Instr::SubK { dest, reg, k }
            | Instr::MulK { dest, reg, k }
            | Instr::DivK { dest, reg, k }
            | Instr::ModK { dest, reg, k }
            | Instr::PowK { dest, reg, k }
            | Instr::IDivK { dest, reg, k }
            | Instr::AndK { dest, reg, k }
            | Instr::OrK { dest, reg, k } => smallvec![Reg(dest), Reg(reg), Const(k.into())],
            Instr::SubRK { dest, k, reg } | Instr::DivRK { dest, k, reg } => {
                smallvec![Reg(dest), Const(k.into()), Reg(reg)]
            }
            Instr::Not { dest, reg } | Instr::Minus { dest, reg } | Instr::Length { dest, reg } => {
                smallvec![Reg(dest), Reg(reg)]
            }

            Instr::NewTable {
                dest,
                hash_size,
                array_size,
            } => smallvec![Reg(dest), HashSize(hash_size), Int(array_size.into())],
            Instr::DupTable { dest, k } => smallvec![Reg(dest), Const(k.into())],
            Instr::SetList {
                table,
                base,
                count,
                index,
            } => smallvec![Reg(table), Reg(base), Count(count), Int(index.into())],
            Instr::FornPrep { base, offset }
            | Instr::FornLoop { base, offset }
            | Instr::ForgPrep { base, offset }
            | Instr::ForgPrepInext { base, offset }
            | Instr::ForgPrepNext { base, offset } => smallvec![Reg(base), Jump(offset.into())],
            Instr::ForgLoop {
                base,
                offset,
                var_count,
                ..
            } => smallvec![Reg(base), Jump(offset.into()), Int(var_count.into())],

            Instr::FastCall { builtin, jump } => smallvec![Builtin(builtin), Skip(jump)],
            Instr::FastCall1 { builtin, arg, jump } => {
                smallvec![Builtin(builtin), Reg(arg), Skip(jump)]
            }
            Instr::FastCall2 {
                builtin,
                arg1,
                arg2,
                jump,
            } => smallvec![Builtin(builtin), Reg(arg1), Reg(arg2), Skip(jump)],
            Instr::FastCall2K {
                builtin,
                arg,
                k,
                jump,
            } => smallvec![Builtin(builtin), Reg(arg), Const(k), Skip(jump)],
            Instr::FastCall3 {
                builtin,
                arg1,
                arg2,
                arg3,
                jump,
            } => {
                let mut ops = smallvec![Builtin(builtin), Reg(arg1), Reg(arg2), Reg(arg3)];
                ops.push(Skip(jump));
                ops
            }
            Instr::GetVarArgs { dest, count } => smallvec![Reg(dest), Count(count)],
            Instr::PrepVarArgs { nparams } => smallvec![Int(nparams.into())],
            Instr::DupClosure { dest, k } => smallvec![Reg(dest), Const(k.into())],
            // CAPTURE UPVAL names an upvalue of the enclosing function, not a register.
            Instr::Capture { capture_type, reg } if capture_type == 2 => {
                smallvec![Operand::Capture(capture_type), Upval(reg)]
            }
            Instr::Capture { capture_type, reg } => {
                smallvec![Operand::Capture(capture_type), Reg(reg)]
            }

            Instr::JumpXEqKNil { reg, offset, .. } => smallvec![Reg(reg), Jump(offset.into())],
            Instr::JumpXEqKB { reg, k, offset, .. } => {
                smallvec![Reg(reg), Bool(k), Jump(offset.into())]
            }
            Instr::JumpXEqKN { reg, k, offset, .. } | Instr::JumpXEqKS { reg, k, offset, .. } => {
                smallvec![Reg(reg), Const(k), Jump(offset.into())]
            }
        };

        if let Instr::JumpXEqKNil { invert: true, .. }
        | Instr::JumpXEqKB { invert: true, .. }
        | Instr::JumpXEqKN { invert: true, .. }
        | Instr::JumpXEqKS { invert: true, .. } = self
        {
            ops.push(Operand::Not);
        }

        ops
    }

    /// Returns the branch offset of this instruction in words, relative to the
    /// word after the instruction header.
    ///
    /// Fastcall skips are not branches: the CALL they skip is always lifted.
    #[must_use]
    pub fn branch_offset(&self) -> Option<i32> {
        match *self {
            Instr::Jump { offset }
            | Instr::JumpBack { offset }
            | Instr::JumpIf { offset, .. }
            | Instr::JumpIfNot { offset, .. }
            | Instr::JumpIfEq { offset, .. }
            | Instr::JumpIfLe { offset, .. }
            | Instr::JumpIfLt { offset, .. }
            | Instr::JumpIfNotEq { offset, .. }
            | Instr::JumpIfNotLe { offset, .. }
            | Instr::JumpIfNotLt { offset, .. }
            | Instr::JumpXEqKNil { offset, .. }
            | Instr::JumpXEqKB { offset, .. }
            | Instr::JumpXEqKN { offset, .. }
            | Instr::JumpXEqKS { offset, .. }
            | Instr::FornPrep { offset, .. }
            | Instr::FornLoop { offset, .. }
            | Instr::ForgPrep { offset, .. }
            | Instr::ForgPrepInext { offset, .. }
            | Instr::ForgPrepNext { offset, .. }
            | Instr::ForgLoop { offset, .. } => Some(offset.into()),
            Instr::JumpX { offset } => Some(offset),
            Instr::LoadB { jump, .. } if jump > 0 => Some(jump.into()),
            _ => None,
        }
    }
}

impl DecodedInstr {
    /// Returns the word position this instruction branches to, if it branches.
    #[must_use]
    pub fn branch_target(&self) -> Option<u32> {
        let offset = self.instr.branch_offset()?;
        self.word_pc.checked_add(1)?.checked_add_signed(offset)
    }
}

impl fmt::Display for Instr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.mnemonic())?;
        for operand in self.operands() {
            write!(f, " {operand}")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct LocalDebug {
    pub name: StringId,
    pub start_pc: u32,
    pub end_pc: u32,
    pub register: u8,
}

#[derive(Debug, Clone)]
pub struct LineInfo {
    pub interval_log2: u8,
    pub deltas: Vec<u8>,
    pub anchors: Vec<i32>,
}

impl LineInfo {
    /// Decodes the source line of every instruction word.
    #[must_use]
    pub fn lines(&self) -> Vec<i32> {
        // Each line is the anchor if its interval plus a byte offset.

        let mut offset = 0u8;
        let mut anchor = 0i32;
        let anchors: Vec<_> = self
            .anchors
            .iter()
            .map(|delta| {
                anchor = anchor.wrapping_add(*delta);
                anchor
            })
            .collect();

        self.deltas
            .iter()
            .enumerate()
            .map(|(pc, delta)| {
                offset = offset.wrapping_add(*delta);
                let anchor = anchors.get(pc >> self.interval_log2).copied().unwrap_or(0);
                anchor + offset as i32
            })
            .collect()
    }
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
}

impl TypeTag {
    pub const fn from_byte(value: u8) -> Self {
        Self {
            ty: BytecodeType::from_byte(value),
            optional: value & BytecodeType::OPTIONAL != 0,
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
    pub start_pc: u32,
    pub end_pc: u32,
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
    pub instrs: Vec<DecodedInstr>,
    pub consts: Vec<Constant>,
    pub child_protos: Vec<ProtoId>,
    pub debug_name: Option<StringId>,
    pub line_defined: u64,
    pub line_info: Option<LineInfo>,
    pub locals: Vec<LocalDebug>,
    pub upvalue_names: Vec<Option<StringId>>,
}

impl Proto {
    /// Resolves a constant by its index.
    pub fn get_constant(&self, id: ConstId) -> Option<&Constant> {
        self.consts.get(id.0 as usize)
    }

    /// Resolves a proto by its index.
    pub fn get_child_proto(&self, id: ChildProtoId) -> Option<ProtoId> {
        self.child_protos.get(id.0 as usize).copied()
    }

    /// Returns the debug-local index active for `register` at `pc`.
    pub fn local_index_at(&self, register: u8, pc: u32) -> Option<usize> {
        self.locals
            .iter()
            .enumerate()
            .filter(|(_, local)| {
                local.register == register && pc >= local.start_pc && pc < local.end_pc
            })
            .max_by_key(|(_, local)| local.start_pc)
            .map(|(index, _)| index)
    }

    /// Returns the debug-local index visible after the instruction at `pc`.
    pub fn local_index_after(&self, register: u8, pc: u32) -> Option<usize> {
        // Instructions are stored in ascending `word_pc` order.
        let next = self.instrs.partition_point(|instr| instr.word_pc <= pc);
        let next_pc = self
            .instrs
            .get(next)
            .map_or(pc.saturating_add(1), |instr| instr.word_pc);
        self.local_index_at(register, next_pc)
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
