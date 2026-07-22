//! Canonical fixed-record encoding for the typed [`EffectVmDescriptor2`] algebra.
//!
//! Descriptor JSON is a convenient Lean-to-Rust build artifact, not a protocol
//! identity.  This module starts *after* JSON parsing and encodes the closed
//! typed algebra directly.  The record has a versioned magic header, fixed
//! field order, explicit one-byte enum tags, little-endian fixed-width integers,
//! and `u64`-length-prefixed UTF-8 strings and vectors.  It has no maps, floats,
//! serde data model, postcard layout, platform-width integers, or ignored
//! fields.  Match arms and struct destructuring are deliberately exhaustive so
//! adding a descriptor constructor or field makes this module fail to compile
//! until a new schema version is designed.

use std::fmt;

use crate::descriptor_ir2::{
    EffectVmDescriptor2, LookupSpec, MapKind, MapOpSpec, MemKind, MemOpSpec, ProofBindSpec,
    TableDef2, TableSem, UMemOpSpec, VmConstraint2, WindowExpr, WindowGateSpec,
};
use crate::lean_descriptor_air::{HashInput, LeanExpr, RangeSpec, VmConstraint, VmHashSite, VmRow};

/// Eight-byte discriminator for canonical DescriptorIR-v2 records.
pub const EFFECT_VM_DESCRIPTOR2_CANONICAL_MAGIC: [u8; 8] = *b"DREGGIR2";
/// Schema version of the fixed record defined in this module.
pub const EFFECT_VM_DESCRIPTOR2_CANONICAL_VERSION: u16 = 1;
/// BLAKE3 derive-key context for semantic relation fingerprints.
pub const EFFECT_VM_DESCRIPTOR2_FINGERPRINT_CONTEXT: &str =
    "dregg.effect-vm-descriptor2.semantic-relation.v1";
/// Hard boundary for a recoverable canonical relation program.  The largest
/// production descriptors are far below this; the cap prevents an externally
/// supplied record from causing an unbounded second allocation during decode.
pub const MAX_CANONICAL_EFFECT_VM_DESCRIPTOR2_BYTES: usize = 64 * 1024 * 1024;

/// Failure to represent or decode the canonical fixed record.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CanonicalDescriptorError {
    /// A platform index cannot be represented by the fixed `u64` wire width.
    IndexOutOfRange { field: &'static str, value: usize },
    /// A canonical `u64` index cannot be represented by this host's `usize`.
    WireIndexOutOfRange { field: &'static str, value: u64 },
    /// Input ended before the current fixed-width field was complete.
    UnexpectedEof { needed: usize, remaining: usize },
    /// The eight-byte record discriminator is wrong.
    BadMagic,
    /// The record version is not implemented by this decoder.
    UnsupportedVersion(u16),
    /// An enum tag is not assigned in this schema version.
    UnknownTag { family: &'static str, tag: u8 },
    /// A boolean byte is neither zero nor one.
    InvalidBool(u8),
    /// A length cannot fit the host or exceeds the bytes still available.
    InvalidLength { field: &'static str, value: u64 },
    /// A string field is not valid UTF-8.
    InvalidUtf8 { field: &'static str },
    /// Allocation for a declared sequence failed.
    AllocationFailed { field: &'static str, len: usize },
    /// A recursive expression exceeded the defensive decoder depth bound.
    NestingTooDeep,
    /// The complete record exceeds the protocol's explicit allocation bound.
    RecordTooLarge { len: usize, max: usize },
    /// A valid record was followed by unconsumed bytes.
    TrailingBytes(usize),
}

impl fmt::Display for CanonicalDescriptorError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IndexOutOfRange { field, value } => {
                write!(f, "{field} value {value} does not fit canonical u64")
            }
            Self::WireIndexOutOfRange { field, value } => {
                write!(f, "canonical {field} value {value} does not fit host usize")
            }
            Self::UnexpectedEof { needed, remaining } => {
                write!(
                    f,
                    "canonical descriptor needs {needed} bytes, only {remaining} remain"
                )
            }
            Self::BadMagic => write!(f, "bad canonical DescriptorIR-v2 magic"),
            Self::UnsupportedVersion(version) => {
                write!(f, "unsupported canonical DescriptorIR-v2 version {version}")
            }
            Self::UnknownTag { family, tag } => {
                write!(f, "unknown {family} tag {tag}")
            }
            Self::InvalidBool(value) => write!(f, "non-canonical boolean byte {value}"),
            Self::InvalidLength { field, value } => {
                write!(f, "invalid canonical length {value} for {field}")
            }
            Self::InvalidUtf8 { field } => write!(f, "invalid UTF-8 in {field}"),
            Self::AllocationFailed { field, len } => {
                write!(f, "cannot allocate {len} elements for {field}")
            }
            Self::NestingTooDeep => write!(f, "canonical descriptor expression nesting too deep"),
            Self::RecordTooLarge { len, max } => {
                write!(f, "canonical descriptor has {len} bytes, maximum is {max}")
            }
            Self::TrailingBytes(count) => write!(f, "{count} trailing canonical descriptor bytes"),
        }
    }
}

impl std::error::Error for CanonicalDescriptorError {}

#[derive(Default)]
struct Writer {
    bytes: Vec<u8>,
}

impl Writer {
    fn u8(&mut self, value: u8) {
        self.bytes.push(value);
    }

    fn u16(&mut self, value: u16) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn u32(&mut self, value: u32) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn u64(&mut self, value: u64) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn i64(&mut self, value: i64) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn index(&mut self, field: &'static str, value: usize) -> Result<(), CanonicalDescriptorError> {
        let value = u64::try_from(value)
            .map_err(|_| CanonicalDescriptorError::IndexOutOfRange { field, value })?;
        self.u64(value);
        Ok(())
    }

    fn string(&mut self, field: &'static str, value: &str) -> Result<(), CanonicalDescriptorError> {
        self.index(field, value.len())?;
        self.bytes.extend_from_slice(value.as_bytes());
        Ok(())
    }

    fn sequence<T>(
        &mut self,
        field: &'static str,
        values: &[T],
        mut write: impl FnMut(&mut Self, &T) -> Result<(), CanonicalDescriptorError>,
    ) -> Result<(), CanonicalDescriptorError> {
        self.index(field, values.len())?;
        for value in values {
            write(self, value)?;
        }
        Ok(())
    }
}

const MAX_EXPRESSION_DEPTH: usize = 1_024;

fn next_depth(depth: usize) -> Result<usize, CanonicalDescriptorError> {
    if depth >= MAX_EXPRESSION_DEPTH {
        Err(CanonicalDescriptorError::NestingTooDeep)
    } else {
        Ok(depth + 1)
    }
}

fn write_lean_expr(
    writer: &mut Writer,
    expression: &LeanExpr,
    depth: usize,
) -> Result<(), CanonicalDescriptorError> {
    let child_depth = next_depth(depth)?;
    match expression {
        LeanExpr::Var(column) => {
            writer.u8(0);
            writer.index("LeanExpr::Var.column", *column)
        }
        LeanExpr::Const(value) => {
            writer.u8(1);
            writer.i64(*value);
            Ok(())
        }
        LeanExpr::Add(left, right) => {
            writer.u8(2);
            write_lean_expr(writer, left, child_depth)?;
            write_lean_expr(writer, right, child_depth)
        }
        LeanExpr::Mul(left, right) => {
            writer.u8(3);
            write_lean_expr(writer, left, child_depth)?;
            write_lean_expr(writer, right, child_depth)
        }
    }
}

fn write_vm_row(writer: &mut Writer, row: VmRow) {
    writer.u8(match row {
        VmRow::First => 0,
        VmRow::Last => 1,
    });
}

fn write_vm_constraint(
    writer: &mut Writer,
    constraint: &VmConstraint,
) -> Result<(), CanonicalDescriptorError> {
    match constraint {
        VmConstraint::Gate(body) => {
            writer.u8(0);
            write_lean_expr(writer, body, 0)
        }
        VmConstraint::Transition { hi, lo } => {
            writer.u8(1);
            writer.index("VmConstraint::Transition.hi", *hi)?;
            writer.index("VmConstraint::Transition.lo", *lo)
        }
        VmConstraint::Boundary { row, body } => {
            writer.u8(2);
            write_vm_row(writer, *row);
            write_lean_expr(writer, body, 0)
        }
        VmConstraint::PiBinding { row, col, pi_index } => {
            writer.u8(3);
            write_vm_row(writer, *row);
            writer.index("VmConstraint::PiBinding.col", *col)?;
            writer.index("VmConstraint::PiBinding.pi_index", *pi_index)
        }
    }
}

fn write_table_semantics(
    writer: &mut Writer,
    semantics: &TableSem,
) -> Result<(), CanonicalDescriptorError> {
    match semantics {
        TableSem::Main => writer.u8(0),
        TableSem::Poseidon2Chip => writer.u8(1),
        TableSem::Range { bits } => {
            writer.u8(2);
            writer.index("TableSem::Range.bits", *bits)?;
        }
        TableSem::Memory => writer.u8(3),
        TableSem::MapOps => writer.u8(4),
        TableSem::UMemory => writer.u8(5),
        TableSem::UMemBoundary => writer.u8(6),
        TableSem::UMemBoundaryCohort => writer.u8(7),
    }
    Ok(())
}

fn write_table(writer: &mut Writer, table: &TableDef2) -> Result<(), CanonicalDescriptorError> {
    let TableDef2 {
        id,
        name,
        arity,
        sem,
    } = table;
    writer.index("TableDef2.id", *id)?;
    writer.string("TableDef2.name", name)?;
    writer.index("TableDef2.arity", *arity)?;
    write_table_semantics(writer, sem)
}

fn write_mem_kind(writer: &mut Writer, kind: MemKind) {
    writer.u8(match kind {
        MemKind::Read => 0,
        MemKind::Write => 1,
    });
}

fn write_map_kind(writer: &mut Writer, kind: MapKind) {
    writer.u8(match kind {
        MapKind::Read => 0,
        MapKind::Write => 1,
        MapKind::Absent => 2,
        MapKind::Insert => 3,
        MapKind::AafiInsert => 4,
    });
}

fn write_window_expr(
    writer: &mut Writer,
    expression: &WindowExpr,
    depth: usize,
) -> Result<(), CanonicalDescriptorError> {
    let child_depth = next_depth(depth)?;
    match expression {
        WindowExpr::Loc(column) => {
            writer.u8(0);
            writer.index("WindowExpr::Loc.column", *column)
        }
        WindowExpr::Nxt(column) => {
            writer.u8(1);
            writer.index("WindowExpr::Nxt.column", *column)
        }
        WindowExpr::Const(value) => {
            writer.u8(2);
            writer.i64(*value);
            Ok(())
        }
        WindowExpr::Add(left, right) => {
            writer.u8(3);
            write_window_expr(writer, left, child_depth)?;
            write_window_expr(writer, right, child_depth)
        }
        WindowExpr::Mul(left, right) => {
            writer.u8(4);
            write_window_expr(writer, left, child_depth)?;
            write_window_expr(writer, right, child_depth)
        }
    }
}

fn write_constraint(
    writer: &mut Writer,
    constraint: &VmConstraint2,
) -> Result<(), CanonicalDescriptorError> {
    match constraint {
        VmConstraint2::Base(base) => {
            writer.u8(0);
            write_vm_constraint(writer, base)
        }
        VmConstraint2::Lookup(lookup) => {
            writer.u8(1);
            let LookupSpec { table, tuple } = lookup;
            writer.index("LookupSpec.table", *table)?;
            writer.sequence("LookupSpec.tuple", tuple, |writer, expression| {
                write_lean_expr(writer, expression, 0)
            })
        }
        VmConstraint2::MemOp(memory) => {
            writer.u8(2);
            let MemOpSpec {
                guard,
                addr,
                value,
                prev_value,
                prev_serial,
                kind,
            } = memory;
            write_lean_expr(writer, guard, 0)?;
            write_lean_expr(writer, addr, 0)?;
            write_lean_expr(writer, value, 0)?;
            write_lean_expr(writer, prev_value, 0)?;
            write_lean_expr(writer, prev_serial, 0)?;
            write_mem_kind(writer, *kind);
            Ok(())
        }
        VmConstraint2::MapOp(map) => {
            writer.u8(3);
            let MapOpSpec {
                guard,
                root,
                key,
                value,
                new_root,
                op,
            } = map;
            write_lean_expr(writer, guard, 0)?;
            writer.sequence("MapOpSpec.root", root, |writer, expression| {
                write_lean_expr(writer, expression, 0)
            })?;
            write_lean_expr(writer, key, 0)?;
            write_lean_expr(writer, value, 0)?;
            writer.sequence("MapOpSpec.new_root", new_root, |writer, expression| {
                write_lean_expr(writer, expression, 0)
            })?;
            write_map_kind(writer, *op);
            Ok(())
        }
        VmConstraint2::UMemOp(memory) => {
            writer.u8(4);
            let UMemOpSpec {
                guard,
                domain,
                key,
                present,
                value,
                prev_present,
                prev_value,
                prev_serial,
                kind,
            } = memory;
            write_lean_expr(writer, guard, 0)?;
            writer.u32(*domain);
            write_lean_expr(writer, key, 0)?;
            write_lean_expr(writer, present, 0)?;
            write_lean_expr(writer, value, 0)?;
            write_lean_expr(writer, prev_present, 0)?;
            write_lean_expr(writer, prev_value, 0)?;
            write_lean_expr(writer, prev_serial, 0)?;
            write_mem_kind(writer, *kind);
            Ok(())
        }
        VmConstraint2::ProofBind(binding) => {
            writer.u8(5);
            let ProofBindSpec { guard, commit, vk } = binding;
            write_lean_expr(writer, guard, 0)?;
            write_lean_expr(writer, commit, 0)?;
            write_lean_expr(writer, vk, 0)
        }
        VmConstraint2::WindowGate(gate) => {
            writer.u8(6);
            let WindowGateSpec {
                body,
                on_transition,
            } = gate;
            write_window_expr(writer, body, 0)?;
            writer.u8(u8::from(*on_transition));
            Ok(())
        }
    }
}

fn write_hash_input(
    writer: &mut Writer,
    input: &HashInput,
) -> Result<(), CanonicalDescriptorError> {
    match input {
        HashInput::Col(column) => {
            writer.u8(0);
            writer.index("HashInput::Col.column", *column)
        }
        HashInput::Digest(index) => {
            writer.u8(1);
            writer.index("HashInput::Digest.index", *index)
        }
        HashInput::Zero => {
            writer.u8(2);
            Ok(())
        }
    }
}

fn write_hash_site(writer: &mut Writer, site: &VmHashSite) -> Result<(), CanonicalDescriptorError> {
    let VmHashSite {
        digest_col,
        arity,
        inputs,
    } = site;
    writer.index("VmHashSite.digest_col", *digest_col)?;
    writer.index("VmHashSite.arity", *arity)?;
    writer.sequence("VmHashSite.inputs", inputs, write_hash_input)
}

fn write_range(writer: &mut Writer, range: &RangeSpec) -> Result<(), CanonicalDescriptorError> {
    let RangeSpec { wire, bits } = range;
    writer.index("RangeSpec.wire", *wire)?;
    writer.index("RangeSpec.bits", *bits)
}

/// Encode a typed DescriptorIR-v2 relation into schema-v1 canonical bytes.
///
/// This function does not parse or preserve JSON and does not use serde.  It is
/// deliberately fallible so a hypothetical platform with an index wider than
/// the record's fixed `u64` width refuses instead of truncating.
pub fn canonical_effect_vm_descriptor2_bytes(
    descriptor: &EffectVmDescriptor2,
) -> Result<Vec<u8>, CanonicalDescriptorError> {
    let EffectVmDescriptor2 {
        name,
        trace_width,
        public_input_count,
        tables,
        constraints,
        hash_sites,
        ranges,
    } = descriptor;

    let mut writer = Writer::default();
    writer
        .bytes
        .extend_from_slice(&EFFECT_VM_DESCRIPTOR2_CANONICAL_MAGIC);
    writer.u16(EFFECT_VM_DESCRIPTOR2_CANONICAL_VERSION);
    writer.string("EffectVmDescriptor2.name", name)?;
    writer.index("EffectVmDescriptor2.trace_width", *trace_width)?;
    writer.index(
        "EffectVmDescriptor2.public_input_count",
        *public_input_count,
    )?;
    writer.sequence("EffectVmDescriptor2.tables", tables, write_table)?;
    writer.sequence(
        "EffectVmDescriptor2.constraints",
        constraints,
        write_constraint,
    )?;
    writer.sequence(
        "EffectVmDescriptor2.hash_sites",
        hash_sites,
        write_hash_site,
    )?;
    writer.sequence("EffectVmDescriptor2.ranges", ranges, write_range)?;
    check_record_size(writer.bytes.len())?;
    Ok(writer.bytes)
}

/// Domain-separated semantic fingerprint of the canonical typed relation.
pub fn effect_vm_descriptor2_semantic_fingerprint(
    descriptor: &EffectVmDescriptor2,
) -> Result<[u8; 32], CanonicalDescriptorError> {
    let bytes = canonical_effect_vm_descriptor2_bytes(descriptor)?;
    let mut hasher = blake3::Hasher::new_derive_key(EFFECT_VM_DESCRIPTOR2_FINGERPRINT_CONTEXT);
    hasher.update(&bytes);
    Ok(*hasher.finalize().as_bytes())
}

struct Reader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn remaining(&self) -> usize {
        self.bytes.len() - self.offset
    }

    fn take(&mut self, len: usize) -> Result<&'a [u8], CanonicalDescriptorError> {
        let remaining = self.remaining();
        if len > remaining {
            return Err(CanonicalDescriptorError::UnexpectedEof {
                needed: len,
                remaining,
            });
        }
        let start = self.offset;
        self.offset += len;
        Ok(&self.bytes[start..self.offset])
    }

    fn u8(&mut self) -> Result<u8, CanonicalDescriptorError> {
        Ok(self.take(1)?[0])
    }

    fn u16(&mut self) -> Result<u16, CanonicalDescriptorError> {
        let mut bytes = [0; 2];
        let len = bytes.len();
        bytes.copy_from_slice(self.take(len)?);
        Ok(u16::from_le_bytes(bytes))
    }

    fn u32(&mut self) -> Result<u32, CanonicalDescriptorError> {
        let mut bytes = [0; 4];
        let len = bytes.len();
        bytes.copy_from_slice(self.take(len)?);
        Ok(u32::from_le_bytes(bytes))
    }

    fn u64(&mut self) -> Result<u64, CanonicalDescriptorError> {
        let mut bytes = [0; 8];
        let len = bytes.len();
        bytes.copy_from_slice(self.take(len)?);
        Ok(u64::from_le_bytes(bytes))
    }

    fn i64(&mut self) -> Result<i64, CanonicalDescriptorError> {
        let mut bytes = [0; 8];
        let len = bytes.len();
        bytes.copy_from_slice(self.take(len)?);
        Ok(i64::from_le_bytes(bytes))
    }

    fn index(&mut self, field: &'static str) -> Result<usize, CanonicalDescriptorError> {
        let value = self.u64()?;
        usize::try_from(value)
            .map_err(|_| CanonicalDescriptorError::WireIndexOutOfRange { field, value })
    }

    fn length(&mut self, field: &'static str) -> Result<usize, CanonicalDescriptorError> {
        let value = self.u64()?;
        let len = usize::try_from(value)
            .map_err(|_| CanonicalDescriptorError::InvalidLength { field, value })?;
        // Every sequence item in this grammar occupies at least one tag or one
        // fixed-width field.  Refuse an impossible count before reserving.
        if len > self.remaining() {
            return Err(CanonicalDescriptorError::InvalidLength { field, value });
        }
        Ok(len)
    }

    fn string(&mut self, field: &'static str) -> Result<String, CanonicalDescriptorError> {
        let len = self.length(field)?;
        let encoded = self.take(len)?;
        let mut owned = Vec::new();
        owned
            .try_reserve_exact(len)
            .map_err(|_| CanonicalDescriptorError::AllocationFailed { field, len })?;
        owned.extend_from_slice(encoded);
        String::from_utf8(owned).map_err(|_| CanonicalDescriptorError::InvalidUtf8 { field })
    }

    fn sequence<T>(
        &mut self,
        field: &'static str,
        mut read: impl FnMut(&mut Self) -> Result<T, CanonicalDescriptorError>,
    ) -> Result<Vec<T>, CanonicalDescriptorError> {
        let len = self.length(field)?;
        let mut values = Vec::new();
        values
            .try_reserve_exact(len)
            .map_err(|_| CanonicalDescriptorError::AllocationFailed { field, len })?;
        for _ in 0..len {
            values.push(read(self)?);
        }
        Ok(values)
    }

    fn boolean(&mut self) -> Result<bool, CanonicalDescriptorError> {
        match self.u8()? {
            0 => Ok(false),
            1 => Ok(true),
            value => Err(CanonicalDescriptorError::InvalidBool(value)),
        }
    }
}

fn unknown(family: &'static str, tag: u8) -> CanonicalDescriptorError {
    CanonicalDescriptorError::UnknownTag { family, tag }
}

fn check_record_size(len: usize) -> Result<(), CanonicalDescriptorError> {
    if len > MAX_CANONICAL_EFFECT_VM_DESCRIPTOR2_BYTES {
        Err(CanonicalDescriptorError::RecordTooLarge {
            len,
            max: MAX_CANONICAL_EFFECT_VM_DESCRIPTOR2_BYTES,
        })
    } else {
        Ok(())
    }
}

fn read_lean_expr(
    reader: &mut Reader<'_>,
    depth: usize,
) -> Result<LeanExpr, CanonicalDescriptorError> {
    let child_depth = next_depth(depth)?;
    match reader.u8()? {
        0 => Ok(LeanExpr::Var(reader.index("LeanExpr::Var.column")?)),
        1 => Ok(LeanExpr::Const(reader.i64()?)),
        2 => Ok(LeanExpr::Add(
            Box::new(read_lean_expr(reader, child_depth)?),
            Box::new(read_lean_expr(reader, child_depth)?),
        )),
        3 => Ok(LeanExpr::Mul(
            Box::new(read_lean_expr(reader, child_depth)?),
            Box::new(read_lean_expr(reader, child_depth)?),
        )),
        tag => Err(unknown("LeanExpr", tag)),
    }
}

fn read_vm_row(reader: &mut Reader<'_>) -> Result<VmRow, CanonicalDescriptorError> {
    match reader.u8()? {
        0 => Ok(VmRow::First),
        1 => Ok(VmRow::Last),
        tag => Err(unknown("VmRow", tag)),
    }
}

fn read_vm_constraint(reader: &mut Reader<'_>) -> Result<VmConstraint, CanonicalDescriptorError> {
    match reader.u8()? {
        0 => Ok(VmConstraint::Gate(read_lean_expr(reader, 0)?)),
        1 => Ok(VmConstraint::Transition {
            hi: reader.index("VmConstraint::Transition.hi")?,
            lo: reader.index("VmConstraint::Transition.lo")?,
        }),
        2 => Ok(VmConstraint::Boundary {
            row: read_vm_row(reader)?,
            body: read_lean_expr(reader, 0)?,
        }),
        3 => Ok(VmConstraint::PiBinding {
            row: read_vm_row(reader)?,
            col: reader.index("VmConstraint::PiBinding.col")?,
            pi_index: reader.index("VmConstraint::PiBinding.pi_index")?,
        }),
        tag => Err(unknown("VmConstraint", tag)),
    }
}

fn read_table_semantics(reader: &mut Reader<'_>) -> Result<TableSem, CanonicalDescriptorError> {
    match reader.u8()? {
        0 => Ok(TableSem::Main),
        1 => Ok(TableSem::Poseidon2Chip),
        2 => Ok(TableSem::Range {
            bits: reader.index("TableSem::Range.bits")?,
        }),
        3 => Ok(TableSem::Memory),
        4 => Ok(TableSem::MapOps),
        5 => Ok(TableSem::UMemory),
        6 => Ok(TableSem::UMemBoundary),
        7 => Ok(TableSem::UMemBoundaryCohort),
        tag => Err(unknown("TableSem", tag)),
    }
}

fn read_table(reader: &mut Reader<'_>) -> Result<TableDef2, CanonicalDescriptorError> {
    Ok(TableDef2 {
        id: reader.index("TableDef2.id")?,
        name: reader.string("TableDef2.name")?,
        arity: reader.index("TableDef2.arity")?,
        sem: read_table_semantics(reader)?,
    })
}

fn read_mem_kind(reader: &mut Reader<'_>) -> Result<MemKind, CanonicalDescriptorError> {
    match reader.u8()? {
        0 => Ok(MemKind::Read),
        1 => Ok(MemKind::Write),
        tag => Err(unknown("MemKind", tag)),
    }
}

fn read_map_kind(reader: &mut Reader<'_>) -> Result<MapKind, CanonicalDescriptorError> {
    match reader.u8()? {
        0 => Ok(MapKind::Read),
        1 => Ok(MapKind::Write),
        2 => Ok(MapKind::Absent),
        3 => Ok(MapKind::Insert),
        4 => Ok(MapKind::AafiInsert),
        tag => Err(unknown("MapKind", tag)),
    }
}

fn read_window_expr(
    reader: &mut Reader<'_>,
    depth: usize,
) -> Result<WindowExpr, CanonicalDescriptorError> {
    let child_depth = next_depth(depth)?;
    match reader.u8()? {
        0 => Ok(WindowExpr::Loc(reader.index("WindowExpr::Loc.column")?)),
        1 => Ok(WindowExpr::Nxt(reader.index("WindowExpr::Nxt.column")?)),
        2 => Ok(WindowExpr::Const(reader.i64()?)),
        3 => Ok(WindowExpr::Add(
            Box::new(read_window_expr(reader, child_depth)?),
            Box::new(read_window_expr(reader, child_depth)?),
        )),
        4 => Ok(WindowExpr::Mul(
            Box::new(read_window_expr(reader, child_depth)?),
            Box::new(read_window_expr(reader, child_depth)?),
        )),
        tag => Err(unknown("WindowExpr", tag)),
    }
}

fn read_constraint(reader: &mut Reader<'_>) -> Result<VmConstraint2, CanonicalDescriptorError> {
    match reader.u8()? {
        0 => Ok(VmConstraint2::Base(read_vm_constraint(reader)?)),
        1 => Ok(VmConstraint2::Lookup(LookupSpec {
            table: reader.index("LookupSpec.table")?,
            tuple: reader.sequence("LookupSpec.tuple", |reader| read_lean_expr(reader, 0))?,
        })),
        2 => Ok(VmConstraint2::MemOp(MemOpSpec {
            guard: read_lean_expr(reader, 0)?,
            addr: read_lean_expr(reader, 0)?,
            value: read_lean_expr(reader, 0)?,
            prev_value: read_lean_expr(reader, 0)?,
            prev_serial: read_lean_expr(reader, 0)?,
            kind: read_mem_kind(reader)?,
        })),
        3 => Ok(VmConstraint2::MapOp(MapOpSpec {
            guard: read_lean_expr(reader, 0)?,
            root: reader.sequence("MapOpSpec.root", |reader| read_lean_expr(reader, 0))?,
            key: read_lean_expr(reader, 0)?,
            value: read_lean_expr(reader, 0)?,
            new_root: reader.sequence("MapOpSpec.new_root", |reader| read_lean_expr(reader, 0))?,
            op: read_map_kind(reader)?,
        })),
        4 => Ok(VmConstraint2::UMemOp(UMemOpSpec {
            guard: read_lean_expr(reader, 0)?,
            domain: reader.u32()?,
            key: read_lean_expr(reader, 0)?,
            present: read_lean_expr(reader, 0)?,
            value: read_lean_expr(reader, 0)?,
            prev_present: read_lean_expr(reader, 0)?,
            prev_value: read_lean_expr(reader, 0)?,
            prev_serial: read_lean_expr(reader, 0)?,
            kind: read_mem_kind(reader)?,
        })),
        5 => Ok(VmConstraint2::ProofBind(ProofBindSpec {
            guard: read_lean_expr(reader, 0)?,
            commit: read_lean_expr(reader, 0)?,
            vk: read_lean_expr(reader, 0)?,
        })),
        6 => Ok(VmConstraint2::WindowGate(WindowGateSpec {
            body: read_window_expr(reader, 0)?,
            on_transition: reader.boolean()?,
        })),
        tag => Err(unknown("VmConstraint2", tag)),
    }
}

fn read_hash_input(reader: &mut Reader<'_>) -> Result<HashInput, CanonicalDescriptorError> {
    match reader.u8()? {
        0 => Ok(HashInput::Col(reader.index("HashInput::Col.column")?)),
        1 => Ok(HashInput::Digest(reader.index("HashInput::Digest.index")?)),
        2 => Ok(HashInput::Zero),
        tag => Err(unknown("HashInput", tag)),
    }
}

fn read_hash_site(reader: &mut Reader<'_>) -> Result<VmHashSite, CanonicalDescriptorError> {
    Ok(VmHashSite {
        digest_col: reader.index("VmHashSite.digest_col")?,
        arity: reader.index("VmHashSite.arity")?,
        inputs: reader.sequence("VmHashSite.inputs", read_hash_input)?,
    })
}

fn read_range(reader: &mut Reader<'_>) -> Result<RangeSpec, CanonicalDescriptorError> {
    Ok(RangeSpec {
        wire: reader.index("RangeSpec.wire")?,
        bits: reader.index("RangeSpec.bits")?,
    })
}

/// Decode exactly one schema-v1 canonical DescriptorIR-v2 record.
///
/// The decoder is strict: it validates magic/version/tags/booleans/UTF-8,
/// checks every `u64 -> usize` conversion, bounds lengths by remaining input,
/// uses fallible sequence allocation, caps recursive expression depth, and
/// rejects any trailing byte.  Descriptor *well-formedness* remains the
/// interpreter's separate semantic validation step.
pub fn decode_canonical_effect_vm_descriptor2(
    bytes: &[u8],
) -> Result<EffectVmDescriptor2, CanonicalDescriptorError> {
    check_record_size(bytes.len())?;
    let mut reader = Reader::new(bytes);
    if reader.take(EFFECT_VM_DESCRIPTOR2_CANONICAL_MAGIC.len())?
        != EFFECT_VM_DESCRIPTOR2_CANONICAL_MAGIC.as_slice()
    {
        return Err(CanonicalDescriptorError::BadMagic);
    }
    let version = reader.u16()?;
    if version != EFFECT_VM_DESCRIPTOR2_CANONICAL_VERSION {
        return Err(CanonicalDescriptorError::UnsupportedVersion(version));
    }

    let descriptor = EffectVmDescriptor2 {
        name: reader.string("EffectVmDescriptor2.name")?,
        trace_width: reader.index("EffectVmDescriptor2.trace_width")?,
        public_input_count: reader.index("EffectVmDescriptor2.public_input_count")?,
        tables: reader.sequence("EffectVmDescriptor2.tables", read_table)?,
        constraints: reader.sequence("EffectVmDescriptor2.constraints", read_constraint)?,
        hash_sites: reader.sequence("EffectVmDescriptor2.hash_sites", read_hash_site)?,
        ranges: reader.sequence("EffectVmDescriptor2.ranges", read_range)?,
    };
    if reader.remaining() != 0 {
        return Err(CanonicalDescriptorError::TrailingBytes(reader.remaining()));
    }
    Ok(descriptor)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_ir2::parse_vm_descriptor2;

    fn expr(seed: usize) -> LeanExpr {
        LeanExpr::Add(
            Box::new(LeanExpr::Var(seed)),
            Box::new(LeanExpr::Mul(
                Box::new(LeanExpr::Const(-(seed as i64) - 1)),
                Box::new(LeanExpr::Var(seed + 1)),
            )),
        )
    }

    fn roots(seed: usize) -> Vec<LeanExpr> {
        (seed..seed + 8).map(LeanExpr::Var).collect()
    }

    fn map_op(op: MapKind, seed: usize) -> VmConstraint2 {
        VmConstraint2::MapOp(MapOpSpec {
            guard: expr(seed),
            root: roots(seed + 10),
            key: expr(seed + 20),
            value: expr(seed + 30),
            new_root: roots(seed + 40),
            op,
        })
    }

    /// One typed value containing every current enum constructor.  If the
    /// descriptor algebra grows, the production encoder/decoder exhaustive
    /// matches fail compilation; this fixture additionally exercises every tag.
    fn all_variant_descriptor() -> EffectVmDescriptor2 {
        let table_semantics = [
            TableSem::Main,
            TableSem::Poseidon2Chip,
            TableSem::Range { bits: 17 },
            TableSem::Memory,
            TableSem::MapOps,
            TableSem::UMemory,
            TableSem::UMemBoundary,
            TableSem::UMemBoundaryCohort,
        ];
        let tables = table_semantics
            .into_iter()
            .enumerate()
            .map(|(id, sem)| TableDef2 {
                id,
                name: format!("table-{id}-λ"),
                arity: id + 1,
                sem,
            })
            .collect();

        let constraints = vec![
            VmConstraint2::Base(VmConstraint::Gate(expr(0))),
            VmConstraint2::Base(VmConstraint::Transition { hi: 1, lo: 2 }),
            VmConstraint2::Base(VmConstraint::Boundary {
                row: VmRow::First,
                body: expr(3),
            }),
            VmConstraint2::Base(VmConstraint::Boundary {
                row: VmRow::Last,
                body: expr(4),
            }),
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col: 5,
                pi_index: 6,
            }),
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::Last,
                col: 7,
                pi_index: 8,
            }),
            VmConstraint2::Lookup(LookupSpec {
                table: 1,
                tuple: vec![LeanExpr::Var(9), LeanExpr::Const(i64::MIN), expr(10)],
            }),
            VmConstraint2::MemOp(MemOpSpec {
                guard: expr(11),
                addr: expr(12),
                value: expr(13),
                prev_value: expr(14),
                prev_serial: expr(15),
                kind: MemKind::Read,
            }),
            VmConstraint2::MemOp(MemOpSpec {
                guard: expr(16),
                addr: expr(17),
                value: expr(18),
                prev_value: expr(19),
                prev_serial: expr(20),
                kind: MemKind::Write,
            }),
            map_op(MapKind::Read, 21),
            map_op(MapKind::Write, 22),
            map_op(MapKind::Absent, 23),
            map_op(MapKind::Insert, 24),
            map_op(MapKind::AafiInsert, 25),
            VmConstraint2::UMemOp(UMemOpSpec {
                guard: expr(26),
                domain: u32::MAX,
                key: expr(27),
                present: expr(28),
                value: expr(29),
                prev_present: expr(30),
                prev_value: expr(31),
                prev_serial: expr(32),
                kind: MemKind::Read,
            }),
            VmConstraint2::UMemOp(UMemOpSpec {
                guard: expr(33),
                domain: 7,
                key: expr(34),
                present: expr(35),
                value: expr(36),
                prev_present: expr(37),
                prev_value: expr(38),
                prev_serial: expr(39),
                kind: MemKind::Write,
            }),
            VmConstraint2::ProofBind(ProofBindSpec {
                guard: expr(40),
                commit: expr(41),
                vk: expr(42),
            }),
            VmConstraint2::WindowGate(WindowGateSpec {
                body: WindowExpr::Add(
                    Box::new(WindowExpr::Loc(43)),
                    Box::new(WindowExpr::Mul(
                        Box::new(WindowExpr::Nxt(44)),
                        Box::new(WindowExpr::Const(i64::MAX)),
                    )),
                ),
                on_transition: true,
            }),
            VmConstraint2::WindowGate(WindowGateSpec {
                body: WindowExpr::Const(-7),
                on_transition: false,
            }),
        ];

        EffectVmDescriptor2 {
            name: "all-variant-descriptor-λ".to_owned(),
            trace_width: 4_096,
            public_input_count: 73,
            tables,
            constraints,
            hash_sites: vec![VmHashSite {
                digest_col: 77,
                arity: 4,
                inputs: vec![
                    HashInput::Col(1),
                    HashInput::Digest(2),
                    HashInput::Zero,
                    HashInput::Col(3),
                ],
            }],
            ranges: vec![RangeSpec { wire: 88, bits: 31 }],
        }
    }

    fn canonical(descriptor: &EffectVmDescriptor2) -> Vec<u8> {
        canonical_effect_vm_descriptor2_bytes(descriptor).expect("fixture is representable")
    }

    fn fingerprint(descriptor: &EffectVmDescriptor2) -> [u8; 32] {
        effect_vm_descriptor2_semantic_fingerprint(descriptor).expect("fixture is representable")
    }

    fn assert_semantic_change(original: &EffectVmDescriptor2, changed: &EffectVmDescriptor2) {
        assert_ne!(canonical(original), canonical(changed));
        assert_ne!(fingerprint(original), fingerprint(changed));
    }

    #[test]
    fn all_variants_roundtrip_byte_exactly() {
        let original = all_variant_descriptor();
        let bytes = canonical(&original);
        let decoded = decode_canonical_effect_vm_descriptor2(&bytes).expect("strict decode");
        assert_eq!(decoded, original);
        assert_eq!(canonical(&decoded), bytes);
    }

    #[test]
    fn production_exact_fnsp_v3_descriptor_roundtrips() {
        const JSON: &str = include_str!("../descriptors/by-name/faithful-note-spend-exact-v3.json");
        let original = parse_vm_descriptor2(JSON).expect("production descriptor parses");
        let bytes = canonical(&original);
        let decoded = decode_canonical_effect_vm_descriptor2(&bytes).expect("strict decode");
        assert_eq!(decoded, original);
        assert_eq!(canonical(&decoded), bytes);
    }

    #[test]
    fn equivalent_json_spelling_and_key_order_have_one_identity() {
        let compact = r#"{"ir":2,"name":"codec-probe","trace_width":2,"public_input_count":1,"tables":[],"constraints":[{"t":"gate","body":{"t":"var","v":0}}],"hash_sites":[],"ranges":[]}"#;
        let reordered = r#"
        {
          "ranges": [],
          "hash_sites": [],
          "constraints": [ { "t": "gate", "body": { "t": "var", "v": 0 } } ],
          "tables": [],
          "public_input_count": 1,
          "trace_width": 2,
          "name": "codec-probe",
          "ir": 2
        }
        "#;
        let left = parse_vm_descriptor2(compact).expect("compact JSON");
        let right = parse_vm_descriptor2(reordered).expect("reordered JSON");
        assert_eq!(left, right);
        assert_eq!(canonical(&left), canonical(&right));
        assert_eq!(fingerprint(&left), fingerprint(&right));
    }

    #[test]
    fn every_top_level_component_and_nested_constraint_mutation_bites() {
        let original = all_variant_descriptor();

        let mut changed = original.clone();
        changed.name.push('!');
        assert_semantic_change(&original, &changed);

        let mut changed = original.clone();
        changed.trace_width += 1;
        assert_semantic_change(&original, &changed);

        let mut changed = original.clone();
        changed.public_input_count += 1;
        assert_semantic_change(&original, &changed);

        let mut changed = original.clone();
        changed.tables[0].arity += 1;
        assert_semantic_change(&original, &changed);

        let mut changed = original.clone();
        changed.constraints[0] = VmConstraint2::Base(VmConstraint::Gate(LeanExpr::Const(99)));
        assert_semantic_change(&original, &changed);

        let mut changed = original.clone();
        changed.hash_sites[0].digest_col += 1;
        assert_semantic_change(&original, &changed);

        let mut changed = original.clone();
        changed.ranges[0].bits -= 1;
        assert_semantic_change(&original, &changed);

        let mut changed = original.clone();
        let VmConstraint2::MemOp(op) = &mut changed.constraints[7] else {
            panic!("fixture drift")
        };
        op.kind = MemKind::Write;
        assert_semantic_change(&original, &changed);

        let mut changed = original.clone();
        let VmConstraint2::MapOp(op) = &mut changed.constraints[9] else {
            panic!("fixture drift")
        };
        op.op = MapKind::AafiInsert;
        assert_semantic_change(&original, &changed);

        let mut changed = original.clone();
        let VmConstraint2::WindowGate(gate) = &mut changed.constraints[17] else {
            panic!("fixture drift")
        };
        gate.on_transition = false;
        assert_semantic_change(&original, &changed);
    }

    fn one_window_gate() -> EffectVmDescriptor2 {
        EffectVmDescriptor2 {
            name: "hostile".to_owned(),
            trace_width: 2,
            public_input_count: 0,
            tables: vec![],
            constraints: vec![VmConstraint2::WindowGate(WindowGateSpec {
                body: WindowExpr::Const(7),
                on_transition: true,
            })],
            hash_sites: vec![],
            ranges: vec![],
        }
    }

    fn first_constraint_tag_offset(descriptor: &EffectVmDescriptor2) -> usize {
        // magic + version + name(length+bytes) + widths + empty table count + constraint count
        8 + 2 + 8 + descriptor.name.len() + 8 + 8 + 8 + 8
    }

    #[test]
    fn strict_decoder_rejects_hostile_noncanonical_records() {
        let descriptor = one_window_gate();
        let bytes = canonical(&descriptor);

        let mut bad = bytes.clone();
        bad[0] ^= 1;
        assert_eq!(
            decode_canonical_effect_vm_descriptor2(&bad),
            Err(CanonicalDescriptorError::BadMagic)
        );

        let mut bad = bytes.clone();
        bad[8..10].copy_from_slice(&2u16.to_le_bytes());
        assert_eq!(
            decode_canonical_effect_vm_descriptor2(&bad),
            Err(CanonicalDescriptorError::UnsupportedVersion(2))
        );

        let mut bad = bytes.clone();
        bad[10..18].copy_from_slice(&u64::MAX.to_le_bytes());
        assert!(matches!(
            decode_canonical_effect_vm_descriptor2(&bad),
            Err(CanonicalDescriptorError::InvalidLength {
                field: "EffectVmDescriptor2.name",
                ..
            })
        ));

        let constraint_tag = first_constraint_tag_offset(&descriptor);
        let mut bad = bytes.clone();
        bad[constraint_tag] = 0xff;
        assert_eq!(
            decode_canonical_effect_vm_descriptor2(&bad),
            Err(CanonicalDescriptorError::UnknownTag {
                family: "VmConstraint2",
                tag: 0xff,
            })
        );

        // constraint tag + WindowExpr::Const tag + i64 payload = boolean byte.
        let mut bad = bytes.clone();
        bad[constraint_tag + 1 + 1 + 8] = 2;
        assert_eq!(
            decode_canonical_effect_vm_descriptor2(&bad),
            Err(CanonicalDescriptorError::InvalidBool(2))
        );

        let mut truncated = bytes.clone();
        truncated.pop();
        assert!(matches!(
            decode_canonical_effect_vm_descriptor2(&truncated),
            Err(CanonicalDescriptorError::UnexpectedEof { .. })
        ));

        let mut trailing = bytes;
        trailing.push(0);
        assert_eq!(
            decode_canonical_effect_vm_descriptor2(&trailing),
            Err(CanonicalDescriptorError::TrailingBytes(1))
        );
    }

    #[test]
    fn empty_record_layout_is_pinned() {
        let descriptor = EffectVmDescriptor2 {
            name: String::new(),
            trace_width: 0,
            public_input_count: 0,
            tables: vec![],
            constraints: vec![],
            hash_sites: vec![],
            ranges: vec![],
        };
        let mut expected = EFFECT_VM_DESCRIPTOR2_CANONICAL_MAGIC.to_vec();
        expected.extend_from_slice(&EFFECT_VM_DESCRIPTOR2_CANONICAL_VERSION.to_le_bytes());
        // name length, two scalar indices, then four sequence lengths.
        expected.extend_from_slice(&[0; 56]);
        assert_eq!(canonical(&descriptor), expected);
    }

    #[test]
    fn oversized_record_refuses_before_decode_or_allocation() {
        assert_eq!(
            check_record_size(MAX_CANONICAL_EFFECT_VM_DESCRIPTOR2_BYTES + 1),
            Err(CanonicalDescriptorError::RecordTooLarge {
                len: MAX_CANONICAL_EFFECT_VM_DESCRIPTOR2_BYTES + 1,
                max: MAX_CANONICAL_EFFECT_VM_DESCRIPTOR2_BYTES,
            })
        );
    }
}
