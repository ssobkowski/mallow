use std::{
    fmt,
    io::{Cursor, Read},
};

use thiserror::Error;

use crate::{
    common::Spanned,
    il::{Constant, Instr, decode_stream_with_word_pcs},
};

const CONST_NIL: u8 = 0;
const CONST_BOOL: u8 = 1;
const CONST_NUMBER: u8 = 2;
const CONST_STRING: u8 = 3;
const CONST_IMPORT: u8 = 4;
const CONST_TABLE: u8 = 5;
const CONST_CLOSURE: u8 = 6;
const CONST_VECTOR: u8 = 7;

pub trait FromLeBytes: Sized {
    fn from_le_bytes_read(cursor: &mut std::io::Cursor<&[u8]>) -> Result<Self, DisasmError>;
}

macro_rules! impl_from_le_bytes {
    ($($t:ty),*) => {
        $(
            impl FromLeBytes for $t {
                #[inline]
                fn from_le_bytes_read(cursor: &mut std::io::Cursor<&[u8]>) -> Result<Self, DisasmError> {
                    let mut buf = [0u8; std::mem::size_of::<$t>()];
                    cursor.read_exact(&mut buf).map_err(DisasmError::IoError)?;
                    Ok(<$t>::from_le_bytes(buf))
                }
            }
        )*
    };
}

impl_from_le_bytes!(u8, u16, u32, u64, i8, i16, i32, i64, f32, f64);
impl FromLeBytes for String {
    #[inline]
    fn from_le_bytes_read(cursor: &mut std::io::Cursor<&[u8]>) -> Result<Self, DisasmError> {
        let mut len_buf = [0u8; 1];
        let mut len = 0u64;
        let mut shift = 0;
        loop {
            cursor
                .read_exact(&mut len_buf)
                .map_err(DisasmError::IoError)?;
            let byte = len_buf[0];
            len |= ((byte & 0x7F) as u64) << shift;
            if byte & 0x80 == 0 {
                break;
            }
            shift += 7;
        }

        let len = len as usize;
        if len == 0 {
            return Ok(String::new());
        }

        let mut buf = vec![0; len];
        cursor.read_exact(&mut buf).map_err(DisasmError::IoError)?;
        Ok(buf.into_iter().map(char::from).collect())
    }
}

#[allow(dead_code)]
#[derive(Debug, Default, Clone)]
pub struct LocalDebug {
    pub name: String,
    pub start_pc: usize,
    pub end_pc: usize,
    pub register: u8,
}

#[derive(Debug, Default, Clone)]
pub struct Proto {
    pub index: u64,
    #[allow(dead_code)]
    pub max_stack_size: u8,
    pub num_params: u8,
    pub num_upvals: u8,
    pub is_vararg: bool,
    #[allow(dead_code)]
    pub flags: u8,
    #[allow(dead_code)]
    pub type_info: Vec<u8>,
    pub instrs: Vec<Spanned<Instr>>,
    pub consts: Vec<Constant>,
    pub protos: Vec<usize>,
    pub debug_name: Option<String>,
    #[allow(dead_code)]
    pub locals: Vec<LocalDebug>,
}

#[derive(Debug, Error)]
pub enum DisasmError {
    #[error("I/O error: {0}")]
    IoError(#[from] std::io::Error),
    #[error("Unsupported bytecode version: {0}. Expected version 5 or 6.")]
    UnsupportedVersion(u8),
    #[error("Unknown constant type: {0} at position {1}.")]
    UnknownConstant(u8, u64),
    #[error("Invalid types version: {0}. Expected 1, 2, or 3.")]
    InvalidTypesVersion(u8),
    #[error("Invalid string index: {0}. String table has {1} entries.")]
    InvalidStringIndex(u64, usize),
}

#[derive(Debug)]
pub struct Disassembly {
    pub version: u8,
    pub protos: Vec<Proto>,
    pub entry_proto: u64,
}

struct Disassembler<'a> {
    cursor: Cursor<&'a [u8]>,
}

impl<'a> Disassembler<'a> {
    fn new(bytecode: &'a [u8]) -> Self {
        Self {
            cursor: Cursor::new(bytecode),
        }
    }

    fn parse(mut self) -> Result<Disassembly, DisasmError> {
        let version = self.read::<u8>()?;
        if version != 6 {
            return Err(DisasmError::UnsupportedVersion(version));
        }

        let types_version = self.read::<u8>()?;
        if types_version != 1 && types_version != 2 && types_version != 3 {
            return Err(DisasmError::InvalidTypesVersion(types_version));
        }

        let strings: Vec<String> = self.read_vec()?;

        if types_version == 3 {
            while self.read::<u8>()? != 0 {}
        }

        let num_protos = self.read_varint()?;
        let mut protos = Vec::with_capacity(num_protos as usize);
        for i in 0..num_protos {
            let mut proto = self.read_proto(&strings)?;
            proto.index = i;
            protos.push(proto);
        }

        let entry_proto = self.read_varint()?;

        Ok(Disassembly {
            version,
            protos,
            entry_proto,
        })
    }

    fn read_proto(&mut self, strings: &[String]) -> Result<Proto, DisasmError> {
        let max_stack_size = self.read()?;
        let num_params = self.read()?;
        let num_upvals = self.read()?;
        let is_vararg = self.read::<u8>()? != 0;
        let flags = self.read()?;

        let type_info = self.read_vec()?;

        let code_table: Vec<u32> = self.read_vec()?;
        let code_word_count = code_table.len();
        let instrs = decode_stream_with_word_pcs(&code_table);

        let num_consts = self.read_varint()?;
        let mut consts = Vec::with_capacity(num_consts as usize);
        for _ in 0..num_consts {
            consts.push(self.read_const(strings)?);
        }

        let num_protos = self.read_varint()?;
        let mut protos = Vec::with_capacity(num_protos as usize);
        for _ in 0..num_protos {
            let index = self.read_varint()? as usize;
            protos.push(index);
        }

        self.read_varint()?; // line defined
        let debug_name = self.read_string(strings)?;

        // line info
        if self.read::<u8>()? == 1 {
            let line_info_comp_key = self.read::<u8>()?;
            let line_interval = 1usize << line_info_comp_key;

            for _ in 0..code_word_count {
                self.read::<u8>()?; // small line info
            }

            let intervals = if code_word_count == 0 {
                0
            } else {
                (code_word_count - 1) / line_interval + 1
            };
            for _ in 0..intervals {
                self.read::<i32>()?; // large line info
            }
        }

        // local variables and upvalues
        let locals = if self.read::<u8>()? == 1 {
            let num_locals = self.read_varint()?;
            let mut locals = Vec::with_capacity(num_locals as usize);

            for _ in 0..num_locals {
                let name_idx = self.read_varint()?;
                let start_pc = self.read_varint()? as usize;
                let end_pc = self.read_varint()? as usize;
                let register = self.read::<u8>()?;
                let name = strings
                    .get(name_idx.saturating_sub(1) as usize)
                    .cloned()
                    .unwrap_or_default();
                locals.push(LocalDebug {
                    name,
                    start_pc,
                    end_pc,
                    register,
                });
            }

            let num_upvals = self.read_varint()?;
            for _ in 0..num_upvals {
                self.read_varint()?; // upval name index
            }

            locals
        } else {
            Vec::new()
        };

        Ok(Proto {
            index: 0,
            max_stack_size,
            num_params,
            num_upvals,
            is_vararg,
            flags,
            type_info,
            instrs,
            consts,
            protos,
            debug_name,
            locals,
        })
    }

    fn read_const(&mut self, strings: &[String]) -> Result<Constant, DisasmError> {
        let ty = self.read::<u8>()?;
        match ty {
            CONST_NIL => Ok(Constant::Nil),
            CONST_BOOL => {
                let value = self.read::<u8>()?;
                Ok(Constant::Boolean(value != 0))
            }
            CONST_NUMBER => {
                let value = self.read()?;
                Ok(Constant::Number(value))
            }
            CONST_STRING => {
                let index = self.read_varint()?;
                if index == 0 || index > strings.len() as u64 {
                    return Err(DisasmError::InvalidStringIndex(index, strings.len()));
                }
                Ok(Constant::String(strings[index as usize - 1].clone()))
            }
            CONST_IMPORT => {
                let value = self.read::<u32>()?;
                Ok(Constant::Import(value))
            }
            CONST_TABLE => {
                let size_hint = self.read_varint()?;
                let mut list = Vec::with_capacity(size_hint as usize);
                for _ in 0..size_hint {
                    let value = self.read_varint()?;
                    list.push(value as usize);
                }
                Ok(Constant::Table(list))
            }
            CONST_CLOSURE => {
                let proto_index = self.read_varint()?;
                Ok(Constant::Closure(proto_index))
            }
            CONST_VECTOR => {
                let x = self.read()?;
                let y = self.read()?;
                let z = self.read()?;
                let w = self.read()?;
                Ok(Constant::Vector { x, y, z, w })
            }
            other => Err(DisasmError::UnknownConstant(other, self.cursor.position())),
        }
    }

    /// Read a varint-encoded 1-based string table index. Returns `None` for index 0 (null).
    #[inline]
    fn read_string(&mut self, strings: &[String]) -> Result<Option<String>, DisasmError> {
        let idx = self.read_varint()?;
        if idx == 0 {
            return Ok(None);
        }

        Ok(Some(
            strings
                .get(idx.saturating_sub(1) as usize)
                .cloned()
                .unwrap_or_default(),
        ))
    }

    #[inline]
    fn read_varint(&mut self) -> Result<u64, DisasmError> {
        let mut result = 0u64;
        let mut shift = 0;

        loop {
            let byte = self.read::<u8>()?;
            result |= ((byte & 0x7F) as u64) << shift;
            if byte & 0x80 == 0 {
                break;
            }
            shift += 7;
        }

        Ok(result)
    }

    #[inline]
    fn read<T: FromLeBytes>(&mut self) -> Result<T, DisasmError> {
        T::from_le_bytes_read(&mut self.cursor)
    }

    #[inline]
    fn read_vec<T: FromLeBytes>(&mut self) -> Result<Vec<T>, DisasmError> {
        let len = self.read_varint()? as usize;
        (0..len).map(|_| self.read::<T>()).collect()
    }
}

impl fmt::Display for Disassembly {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for proto in &self.protos {
            let name_suffix = proto
                .debug_name
                .as_ref()
                .map(|n| format!(" (\"{n}\")"))
                .unwrap_or_default();
            writeln!(
                f,
                "Proto {}{} ({} params, {} upvalues)",
                proto.index, name_suffix, proto.num_params, proto.num_upvals
            )?;

            for sd in &proto.instrs {
                writeln!(f, "{}: {}", sd.pc, sd.node)?;
            }

            writeln!(f)?;
        }

        Ok(())
    }
}

pub fn disassemble(bytecode: &[u8]) -> Result<Disassembly, DisasmError> {
    Disassembler::new(bytecode).parse()
}
