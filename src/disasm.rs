use std::io::{Cursor, Read};

use thiserror::Error;

use crate::il::{Constant, Instr, Table, Value};

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
        String::from_utf8(buf).map_err(|err| {
            DisasmError::IoError(std::io::Error::new(std::io::ErrorKind::InvalidData, err))
        })
    }
}

#[derive(Debug, Default, Clone)]
pub struct Proto {
    pub index: u64,
    pub max_stack_size: u8,
    pub num_params: u8,
    pub num_upvals: u8,
    pub is_vararg: bool,
    pub flags: u8,
    pub type_info: Vec<u8>,
    pub instrs: Vec<Instr>,
    pub instr_word_pcs: Vec<usize>,
    pub consts: Vec<Constant>,
    pub protos: Vec<usize>,
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
    #[error("Invalid instruction stream: {0}")]
    InvalidInstructionStream(String),
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
        if version != 5 && version != 6 {
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
        let mut proto = Proto::default();
        proto.max_stack_size = self.read()?;
        proto.num_params = self.read()?;
        proto.num_upvals = self.read()?;
        proto.is_vararg = self.read::<u8>()? != 0;
        proto.flags = self.read()?;

        proto.type_info = self.read_vec()?;

        let code_table: Vec<u32> = self.read_vec()?;
        let code_word_count = code_table.len();
        let (instrs, instr_word_pcs) = Instr::decode_stream_with_word_pcs(&code_table)
            .map_err(DisasmError::InvalidInstructionStream)?;
        proto.instrs = instrs;
        proto.instr_word_pcs = instr_word_pcs;

        let num_consts = self.read_varint()?;
        proto.consts = Vec::with_capacity(num_consts as usize);
        for _ in 0..num_consts {
            proto.consts.push(self.read_const(strings)?);
        }

        let num_protos = self.read_varint()?;
        proto.protos = Vec::with_capacity(num_protos as usize);
        for _ in 0..num_protos {
            let index = self.read_varint()? as usize;
            proto.protos.push(index);
        }

        self.read_varint()?; // line defined
        self.read_varint()?; // source index (1-based string table index)

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
        if self.read::<u8>()? == 1 {
            let num_locals = self.read_varint()?;

            for _ in 0..num_locals {
                self.read_varint()?; // var name index
                self.read_varint()?; // start pc
                self.read_varint()?; // end pc
                self.read::<u8>()?; // register
            }

            let num_upvals = self.read_varint()?;
            for _ in 0..num_upvals {
                self.read_varint()?; // upval name index
            }
        }

        Ok(proto)
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
                    list.push(Value::ConstantIndex(value as usize));
                }
                Ok(Constant::Table(Table::Array(list)))
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

pub fn disassemble(bytecode: &[u8]) -> Result<Disassembly, DisasmError> {
    Disassembler::new(bytecode).parse()
}
