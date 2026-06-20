use std::rc::Rc;

use crate::{
    common::Spanned,
    disasm::Chunk,
    il::{
        ConstId, Constant, FunctionTypeInfo, ImportPath, Instr, LocalDebug, LocalTypeInfo,
        LuauString, Proto, ProtoId, ProtoTypeInfo, StringId, TypeTag, UserdataTypeMapping,
    },
};

use anyhow::{Context, Result, bail, ensure};

pub trait FromLeBytes: Sized {
    const SIZE: usize = std::mem::size_of::<Self>();
    fn from_le_slice(bytes: &[u8]) -> Self;
}

macro_rules! impl_from_le_bytes {
    ($($t:ty),*) => {
        $(
            impl FromLeBytes for $t {
                #[inline]
                fn from_le_slice(bytes: &[u8]) -> Self {
                    let mut arr = [0u8; Self::SIZE];
                    arr.copy_from_slice(bytes);
                    <$t>::from_le_bytes(arr)
                }
            }
        )*
    };
}

impl_from_le_bytes!(u8, u16, u32, u64, i8, i16, i32, i64, f32, f64);

pub struct BytecodeReader<'b> {
    bytes: &'b [u8],
    pos: usize,
}

impl<'b> BytecodeReader<'b> {
    pub fn new(bytes: &'b [u8]) -> Self {
        Self { bytes, pos: 0 }
    }

    #[inline]
    pub fn read_bytes(&mut self, len: usize) -> Result<&'b [u8]> {
        let end = self.pos.checked_add(len).context("byte length overflow")?;

        let slice = self
            .bytes
            .get(self.pos..end)
            .context("unexpected end of bytecode")?;

        self.pos = end;
        Ok(slice)
    }

    #[inline]
    fn read<T: FromLeBytes>(&mut self) -> Result<T> {
        let slice = self.read_bytes(T::SIZE)?;
        Ok(T::from_le_slice(slice))
    }

    fn read_varint<T>(&mut self) -> Result<T>
    where
        T: TryFrom<u64>,
    {
        let mut result = 0u64;
        let mut shift = 0;

        loop {
            let byte: u8 = self.read()?;
            result |= ((byte & 0x7F) as u64) << shift;
            if byte & 0x80 == 0 {
                break;
            }

            shift += 7;
            if shift >= const { std::mem::size_of::<T>() * 8 } {
                bail!("malformed or overflowing varint");
            }
        }

        T::try_from(result).map_err(|_| anyhow::anyhow!("malformed or overflowing varint"))
    }

    pub fn read_chunk(&mut self) -> Result<Chunk> {
        let version = self.read::<u8>()?;
        ensure!(
            (5..=8).contains(&version),
            "unsupported bytecode version {version}; expected version 5, 6, 7, or 8",
        );

        let types_version = self.read::<u8>()?;
        ensure!(
            matches!(types_version, 1..=3),
            "invalid types version {types_version}; expected 1, 2, or 3",
        );

        let strings = self.read_string_table()?;
        let userdata_type_mappings = if types_version == 3 {
            Some(self.read_userdata_type_mappings()?)
        } else {
            None
        };

        let proto_count = self.read_varint()?;
        ensure!(proto_count <= 2 << 15, "proto count exceeds 2^15 limit");

        let mut protos = Vec::with_capacity(proto_count);
        for proto_idx in 0..proto_count {
            protos.push(self.read_proto(version, types_version, ProtoId(proto_idx as u16))?);
        }

        let entry_proto = ProtoId(self.read_varint()?);

        ensure!(
            self.pos == self.bytes.len(),
            "trailing bytecode data starts at byte {}; input has {} bytes",
            self.pos,
            self.bytes.len(),
        );

        Ok(Chunk {
            version,
            types_version,
            strings,
            userdata_type_mappings,
            protos,
            entry_proto,
        })
    }

    fn read_string_table(&mut self) -> Result<Vec<LuauString>> {
        let len: usize = self.read_varint()?;
        let mut strings = Vec::with_capacity(len);
        for _ in 0..len {
            strings.push(self.read_luau_string()?);
        }
        Ok(strings)
    }

    fn read_userdata_type_mappings(&mut self) -> Result<Vec<UserdataTypeMapping>> {
        let mut mappings = Vec::new();

        loop {
            let encoded_index = self.read::<u8>()?;
            if encoded_index == 0 {
                break;
            }

            let name = self.read_string_id()?;
            mappings.push(UserdataTypeMapping {
                index: encoded_index - 1,
                name,
            });
        }

        Ok(mappings)
    }

    #[inline]
    fn read_luau_string(&mut self) -> Result<LuauString> {
        let len = self.read_varint()?;
        if len == 0 {
            return Ok(LuauString::default());
        }

        let str_bytes = self.read_bytes(len)?;
        Ok(LuauString(Rc::from(str_bytes)))
    }

    #[inline]
    fn read_string_id(&mut self) -> Result<Option<StringId>> {
        let id = self.read_varint()?;
        Ok((id != 0).then_some(StringId(id)))
    }

    fn read_vec<T>(&mut self) -> Result<Vec<T>>
    where
        T: FromLeBytes,
    {
        let len: usize = self.read_varint()?;
        let mut vec = Vec::with_capacity(len);
        for _ in 0..len {
            vec.push(self.read()?);
        }
        Ok(vec)
    }

    fn read_const(&mut self, version: u8) -> Result<Constant> {
        let tag: u8 = self.read()?;
        match tag {
            0 => Ok(Constant::Nil),
            1 => {
                let value: u8 = self.read()?;
                match value {
                    0 => Ok(Constant::Boolean(false)),
                    1 => Ok(Constant::Boolean(true)),
                    other => bail!("invalid boolean constant {other}; expected 0 or 1"),
                }
            }
            2 => {
                let value = self.read()?;
                Ok(Constant::Number(value))
            }
            3 => {
                let index = self.read_varint()?;
                Ok(Constant::String(StringId(index)))
            }
            4 => {
                let path = self.read()?;
                Ok(Constant::Import(ImportPath(path)))
            }
            5 => {
                let len = self.read_varint()?;
                // Plain table constants only store template keys for DUPTABLE.
                // The runtime initializes these keys with placeholders and real
                // values are supplied by later SETTABLE/SETLIST instructions.
                for _ in 0..len {
                    self.read_varint::<u32>()?;
                }
                Ok(Constant::Table)
            }
            6 => Ok(Constant::Closure(ProtoId(self.read_varint()?))),
            7 => {
                if version < 5 {
                    bail!("constant {tag} not allowed in version {version}");
                }

                Ok(Constant::Vector {
                    x: self.read()?,
                    y: self.read()?,
                    z: self.read()?,
                    w: self.read()?,
                })
            }
            8 => {
                ensure!(
                    version >= 7,
                    "constant {tag} not allowed in version {version}"
                );

                let len: usize = self.read_varint()?;
                let mut entries = Vec::with_capacity(len);
                for _ in 0..len {
                    let key = ConstId(self.read_varint()?);
                    let value = self.read::<i32>()?;
                    let value = (value >= 0).then_some(ConstId(value as u32));
                    entries.push((key, value));
                }

                Ok(Constant::TableWithConstants(entries))
            }
            9 => {
                ensure!(
                    version >= 8,
                    "constant {tag} not allowed in version {version}"
                );

                let is_negative = self.read::<u8>()? != 0;
                let magnitude: u64 = self.read_varint()?;
                let value = decode_integer_constant(is_negative, magnitude)?;
                Ok(Constant::Integer(value))
            }

            other => bail!("unknown constant type {other} at byte {}", self.pos),
        }
    }

    fn read_proto(&mut self, version: u8, types_version: u8, proto_id: ProtoId) -> Result<Proto> {
        let max_stack_size = self.read()?;
        let num_params = self.read()?;
        let num_upvals = self.read()?;
        let is_vararg = self.read::<u8>()? != 0;
        let flags = self.read()?;

        let type_info = TypeReader::read_type_info(self, types_version, proto_id)?;

        let code_table: Vec<u32> = self.read_vec()?;
        let instrs = decode_stream_with_word_pcs(&code_table)?;

        let num_consts = self.read_varint()?;
        ensure!(num_consts <= 2 << 23, "constant count exceeds 2^23 limit");

        let mut consts = Vec::with_capacity(num_consts);
        for _ in 0..num_consts {
            consts.push(self.read_const(version)?);
        }

        let num_protos = self.read_varint()?;
        ensure!(num_protos <= 2 << 15, "proto count exceeds 2^15 limit");

        let mut child_protos = Vec::with_capacity(num_protos);
        for _ in 0..num_protos {
            child_protos.push(ProtoId(self.read_varint()?));
        }

        self.read_varint::<u64>()?; // line defined
        let debug_name = self.read_string_id()?;

        if self.read::<u8>()? == 1 {
            let line_info_comp_key: u8 = self.read()?;
            let line_interval = 1usize << line_info_comp_key;

            for _ in 0..code_table.len() {
                self.read::<u8>()?; // small line info
            }

            let intervals = if code_table.is_empty() {
                0
            } else {
                (code_table.len() - 1) / line_interval + 1
            };
            for _ in 0..intervals {
                self.read::<i32>()?; // large line info
            }
        }

        // local variables and upvalues
        let locals = if self.read::<u8>()? == 1 {
            let num_locals = self.read_varint()?;
            let mut locals = Vec::with_capacity(num_locals);

            for _ in 0..num_locals {
                let name_idx = self.read_varint()?;
                let start_pc = self.read_varint()?;
                let end_pc = self.read_varint()?;
                let register = self.read()?;
                locals.push(LocalDebug {
                    name: StringId(name_idx),
                    start_pc,
                    end_pc,
                    register,
                });
            }

            let num_upvals = self.read_varint()?;
            for _ in 0..num_upvals {
                self.read_string_id()?; // upval name index
            }

            locals
        } else {
            Vec::new()
        };

        Ok(Proto {
            id: proto_id,
            max_stack_size,
            num_params,
            num_upvals,
            is_vararg,
            flags,
            type_info,
            instrs,
            consts,
            child_protos,
            debug_name,
            locals,
        })
    }
}

struct TypeReader<'b> {
    reader: BytecodeReader<'b>,
    len: usize,
    proto_id: ProtoId,
}

impl<'b> TypeReader<'b> {
    fn read_type_info(
        reader: &mut BytecodeReader<'b>,
        types_version: u8,
        proto_id: ProtoId,
    ) -> Result<ProtoTypeInfo> {
        let len: usize = reader.read_varint()?;
        if len == 0 {
            return Ok(ProtoTypeInfo::default());
        }

        let bytes = reader.read_bytes(len)?;
        let mut type_reader = Self {
            reader: BytecodeReader::new(bytes),
            len,
            proto_id,
        };

        let info = match types_version {
            1 => type_reader.read_v1()?,
            2 | 3 => type_reader.read_v2_or_v3()?,
            _ => bail!("invalid types version {types_version}; expected 1, 2, or 3"),
        };

        ensure!(
            type_reader.reader.pos == type_reader.reader.bytes.len(),
            "invalid type info for proto {}: trailing type info bytes",
            proto_id.0
        );

        Ok(info)
    }

    fn read_v1(&mut self) -> Result<ProtoTypeInfo> {
        let function = self.read_function_type(self.len)?;

        Ok(ProtoTypeInfo {
            function: Some(function),
            upvalues: Vec::new(),
            locals: Vec::new(),
        })
    }

    fn read_v2_or_v3(&mut self) -> Result<ProtoTypeInfo> {
        let function_size: usize = self.reader.read_varint()?;
        let upvalue_count: usize = self.reader.read_varint()?;
        let local_count: usize = self.reader.read_varint()?;

        let function = if function_size == 0 {
            None
        } else {
            Some(self.read_function_type(function_size)?)
        };

        let mut upvalues = Vec::with_capacity(upvalue_count);
        for _ in 0..upvalue_count {
            upvalues.push(self.read_type_tag()?);
        }

        let mut locals = Vec::with_capacity(local_count);
        for _ in 0..local_count {
            let ty = self.read_type_tag()?;
            let register: u8 = self.reader.read()?;
            let start_pc = self.reader.read_varint()?;
            let pc_len: usize = self.reader.read_varint()?;
            locals.push(LocalTypeInfo {
                ty,
                register,
                start_pc,
                end_pc: start_pc + pc_len,
            });
        }

        Ok(ProtoTypeInfo {
            function,
            upvalues,
            locals,
        })
    }

    fn read_type_tag(&mut self) -> Result<TypeTag> {
        Ok(TypeTag::from_byte(self.reader.read()?))
    }

    fn read_function_type(&mut self, size: usize) -> Result<FunctionTypeInfo> {
        if size < 2 {
            bail!("unexpected end of bytecode");
        }

        let tag: u8 = self.reader.read()?;
        if tag != 5 {
            bail!(
                "invalid type info for proto {}: expected function type tag 5, got {tag}",
                self.proto_id.0,
            );
        }

        let num_params: u8 = self.reader.read()?;
        let expected_size = 2 + usize::from(num_params);
        if expected_size != size {
            bail!(
                "invalid type info for proto {}: function type size {size} does not match {expected_size}",
                self.proto_id.0,
            );
        }

        let mut params = Vec::with_capacity(num_params as usize);
        for _ in 0..num_params {
            params.push(self.read_type_tag()?);
        }

        Ok(FunctionTypeInfo { num_params, params })
    }
}

#[inline]
fn decode_integer_constant(is_negative: bool, magnitude: u64) -> Result<i64> {
    if !is_negative {
        return i64::try_from(magnitude).context("integer constant exceeds i64::MAX");
    }

    const MIN_MAGNITUDE: u64 = 1u64 << 63;
    if magnitude > MIN_MAGNITUDE {
        bail!("negative integer constant magnitude exceeds i64::MIN");
    }

    if magnitude == MIN_MAGNITUDE {
        Ok(i64::MIN)
    } else {
        Ok(-(magnitude as i64))
    }
}

fn decode_stream_with_word_pcs(words: &[u32]) -> Result<Vec<Spanned<Instr>>> {
    let mut out = Vec::new();
    let mut pc = 0;

    while pc < words.len() {
        ensure!(pc < u32::MAX as usize, "pc overflow at word pc {pc}");

        let header_pc = pc;
        let header = words[header_pc];
        let opcode = (header & 0xff) as u8;

        ensure!(
            opcode < Instr::LOP_COUNT,
            "invalid Luau opcode {opcode} at word pc {header_pc} in header word 0x{header:08x}",
        );

        let aux = if Instr::opcode_requires_aux(opcode) {
            pc += 1;
            ensure!(
                pc < words.len(),
                "truncated bytecode: opcode {opcode} at word pc {header_pc} requires AUX word",
            );
            Some(words[pc])
        } else {
            None
        };

        out.push(Spanned::new(
            Instr::new(header, aux).map_err(|e| {
                anyhow::anyhow!("failed to decode instruction at word pc {header_pc}: {e}")
            })?,
            header_pc as u32,
        ));
        pc += 1;
    }

    Ok(out)
}
