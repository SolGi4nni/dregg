//! Descriptor IR v2 — the EPOCH multi-table interpreter (`docs/EPOCH-DESIGN.md`).
//!
//! `lean_descriptor_air.rs` PART 6 interprets the SINGLE-table v1 EffectVM descriptor
//! (`emitVmJson`): per-row hash sites cost a 352-column Poseidon2 aux block each, and range
//! teeth cost one boolean column per bit. This module interprets the VERSIONED v2 wire
//! (`Dregg2.Circuit.DescriptorIR2.emitVmJson2`, `"ir":2`), whose grammar makes hashing a
//! BOUNDARY phenomenon: the descriptor declares TABLES and RELATIONS, and the Rust side
//! assembles a MULTI-TABLE batch STARK (`p3-batch-stark` + the `p3-lookup` LogUp argument)
//! whose instances are
//!
//!   * **main** — one trace row per effect row; interprets the embedded v1 constraint forms
//!     (`gate`/`transition`/`boundary`/`pi_binding`) on the same domains the v1 AIR used, and
//!     realizes every declared `lookup`/`mem_op`/`map_op` as a bus interaction;
//!   * **poseidon2 chip** — one row per permutation `(arity, inputs padded to rate 8, output)`,
//!     each row pinned to the REAL Poseidon2 round constraints (`poseidon2_permute_expr`) so
//!     the table is sound in exactly the sense of Lean's `ChipTableSound`; hash-site lookups
//!     ride the `ir2_p2` bus (the measured 85% lever — one aux block per UNIQUE permutation,
//!     not per row × site);
//!   * **range** — the shared `[0,256)` byte table; a declared `lookup` into the range table
//!     (`rangeLimb bits`) is realized by byte-limb decomposition + LogUp byte queries + a
//!     tight top-limb bit bound (the proven `lean_lookup_air` shape; the realized relation is
//!     exactly `v ∈ [0, 2^bits)` = Lean's `range_row_mem_iff`);
//!   * **memory** — one row per state access, in log order: the offline-memory-checking
//!     instrumentation. The main AIR SENDS each guarded `(addr, value, prev_value,
//!     prev_serial, kind)` op on a permutation-check bus and the memory table RECEIVES it
//!     (exact multiset equality = Lean's `memTableFaithful`); the table's own AIR enforces the
//!     Blum discipline (positional serials, `prev_serial < serial` by range, read ⇒
//!     `value = prev_value`) and runs the read/write multiset argument
//!     (`init + writes = reads + final`, Lean `MemCheck`) on a second permutation bus against
//!     a boundary instance (declared addresses, strictly increasing ⇒ `Nodup`; address
//!     closure by lookup). Soundness of balance ⇒ consistency is the PROVED
//!     `Dregg2.Crypto.MemoryChecking.memcheck_sound`;
//!   * **map-ops** — one row per boundary reconciliation `(root, key, value, op) → new_root`,
//!     each row verifying a REAL sorted-Poseidon2-Merkle opening in-row (leaf
//!     `hash[key, value]`, nodes `hash_fact(l, [r])`, depth 16 — byte-identical to
//!     `heap_root::CanonicalHeapTree`): `read` authenticates the leaf under `root` and pins
//!     `new_root = root`; `write` is the in-place sorted-tree leaf UPDATE (old leaf under
//!     `root`, new leaf over the SAME siblings to `new_root` — `HeapUpdateWitness`'s shape).
//!     Main sends each guarded op; the table receives it (`mapTableFaithful`).
//!
//! **The law: Rust authors NO constraints.** Every enforced relation here is the realization
//! of a DECLARED descriptor element (a v1 form, a lookup into a declared table, a mem op, a
//! map op); the per-table AIRs discharge the per-table faithfulness obligations Lean names
//! (`ChipTableSound`, the faithful range table, `memTableFaithful`+`MemCheck`+`Disciplined`,
//! `mapTableFaithful`+`opensTo`/`writesTo`). Which wires are constrained is entirely the
//! descriptor's (= Lean's) choice.
//!
//! ## Honest boundary notes (named, with their closure lanes)
//!
//!   * `map_op` kind `absent` (non-membership via the sorted gap bracketing) is NOT yet
//!     realized — assembly refuses it with a precise error. Its realization is two adjacent
//!     membership paths + the gap comparisons (`non_membership.rs` machinery); it lands with
//!     the nullifier-insert lane (no shipped v2 descriptor emits `absent` yet).
//!   * `map_op` kind `write` is realized as the in-place leaf UPDATE at an existing key
//!     (exactly `Heap.set` when the key is present — the cap-crown phase-B shape). A
//!     fresh-key sorted INSERT shifts leaf positions and rides the same lane as `absent`.
//!   * The custom table id 5 (Lean `SUBMASK_TID = 0`) is realized as the bitwise-submask
//!     relation at 30 bits (`subsetTable_mem_iff`: both elements in `[0, 2^30)` and
//!     `keep & held = keep`), enforced by per-bit decomposition — the custom-table CONTENTS
//!     manifest is the named small IR follow-up on the Lean side; until it lands the id ↦
//!     relation binding lives here, in one place.
//!   * The memory boundary image (`minit`/`mfin`/declared addresses) is witness-supplied
//!     (the `MemBoundaryWitness` instance); binding the init image to main-trace state
//!     columns is part of the PI-v3 / witness-restructure ride-along, not this module.
//!   * v1 descriptors (no `"ir"` key) keep proving through `lean_descriptor_air::
//!     prove_vm_descriptor` untouched — both registries live until the flag-day.

use std::collections::BTreeMap;

use p3_air::{Air, AirBuilder, BaseAir, PermutationAirBuilder, WindowAccess};
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_lookup::InteractionBuilder;
use p3_lookup::bus::{LookupBus, PermutationCheckBus};
use p3_matrix::dense::RowMajorMatrix;

use p3_batch_stark::{BatchProof, ProverData, StarkInstance, prove_batch, verify_batch};

use crate::field::{BABYBEAR_P, BabyBear};
use crate::heap_root::{CanonicalHeapTree, HEAP_TREE_DEPTH, HeapLeaf};
use crate::lean_descriptor_air::{
    EFFECTVM_STATE_AFTER_BASE, EFFECTVM_STATE_BEFORE_BASE, JsonCursor, LeanExpr, VmConstraint,
    VmHashSite, VmRow, i64_to_babybear, parse_expr, parse_hash_site, parse_range,
    parse_vm_constraint_body,
};
use crate::lean_descriptor_air::{EffectVmDescriptor, RangeSpec};
use crate::plonky3_prover::{
    DreggStarkConfig, POSEIDON2_PERM_AUX_COLS, POSEIDON2_WIDTH, create_config,
    poseidon2_permute_aux_witness, poseidon2_permute_expr, to_p3,
};

// ============================================================================
// Wire constants (the Rust mirror of `DescriptorIR2` §1/§7)
// ============================================================================

/// Stable wire id of the main table.
pub const TID_MAIN: usize = 0;
/// Stable wire id of the Poseidon2 chip table.
pub const TID_P2: usize = 1;
/// Stable wire id of the range (limb) table.
pub const TID_RANGE: usize = 2;
/// Stable wire id of the memory table.
pub const TID_MEMORY: usize = 3;
/// Stable wire id of the map-ops table.
pub const TID_MAP_OPS: usize = 4;
/// Wire id of `custom 0` = the bitwise-submask table (`DescriptorIR2.SUBMASK_TID`).
pub const TID_CUSTOM_SUBMASK: usize = 5;

/// The chip lookup rate in base-field elements (`babyBearD4W16.rate = 8`); a chip tuple is
/// `1 (arity) + CHIP_RATE (padded inputs) + 1 (output) = 10` wide.
pub const CHIP_RATE: usize = 8;
/// The chip tuple arity on the wire.
pub const CHIP_TUPLE_LEN: usize = CHIP_RATE + 2;

/// The effect-mask width of the submask custom table (`EffectVmEmitV2.MASK_BITS`).
pub const SUBMASK_BITS: usize = 30;
/// Bit width of the memory serial-gap / boundary address range checks.
const MEM_GAP_BITS: usize = 30;

/// Bits per range-table byte limb (the shared `[0,256)` table).
pub const LIMB_BITS: usize = 8;
/// The byte-table height (pinned: the table AIR forces `value = row index`).
pub const BYTE_TABLE_HEIGHT: usize = 1 << LIMB_BITS;

/// Minimum height for the auxiliary tables (chip / memory / boundary / map-ops).
const MIN_TABLE_HEIGHT: usize = 8;

// The shared bus names (namespaced so sibling modules' buses never collide).
const BUS_P2: &str = "ir2_p2";
const BUS_BYTE: &str = "ir2_byte";
const BUS_MEM_LOG: &str = "ir2_mem_log";
const BUS_MEM_CHECK: &str = "ir2_mem_check";
const BUS_MEM_ADDRS: &str = "ir2_mem_addrs";
const BUS_MAP_LOG: &str = "ir2_map_log";

/// The `hash_fact` domain-separation marker (`poseidon2::hash_fact` state[5]).
const FACT_MARK: u32 = 0xFACF;

// ============================================================================
// The v2 descriptor mirror (Lean `EffectVmDescriptor2`, decoded from `emitVmJson2`)
// ============================================================================

/// Row semantics of a declared table (Lean `RowSemantics`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TableSem {
    /// One row per effect (the descriptor's own main trace).
    Main,
    /// One row per Poseidon2 permutation (params validated against the deployed pins).
    Poseidon2Chip,
    /// The limb table: rows `[v]` for `v ∈ [0, 2^bits)`.
    Range {
        /// The declared limb width.
        bits: usize,
    },
    /// One row per state access (offline memory checking).
    Memory,
    /// One row per boundary reconciliation (sorted-map opening).
    MapOps,
}

/// A declared table (Lean `TableDef`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TableDef2 {
    /// Stable wire id.
    pub id: usize,
    /// Display name.
    pub name: String,
    /// Column arity.
    pub arity: usize,
    /// Row semantics.
    pub sem: TableSem,
}

/// A lookup: the tuple of expressions is asserted to be a row of the named table
/// (Lean `Lookup`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LookupSpec {
    /// Target table wire id.
    pub table: usize,
    /// The tuple of column expressions.
    pub tuple: Vec<LeanExpr>,
}

/// Memory access kind (Lean `MemoryChecking.Kind`; wire codes 0 = read, 1 = write).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemKind {
    /// A read: returns its claimed previous value.
    Read,
    /// A write: installs `value` over the claimed previous tuple.
    Write,
}

impl MemKind {
    /// The memory-table `kind` column value.
    pub fn code(self) -> u32 {
        match self {
            MemKind::Read => 0,
            MemKind::Write => 1,
        }
    }
}

/// A read/write multiset row (Lean `MemOp`): the offline-memory-checking instrumentation
/// as expressions over the emitting main row. `guard` gates the contribution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemOpSpec {
    /// Selector guard (active iff it evaluates to 1).
    pub guard: LeanExpr,
    /// Address expression.
    pub addr: LeanExpr,
    /// Value returned (read) / installed (write).
    pub value: LeanExpr,
    /// Claimed latest prior value at the address.
    pub prev_value: LeanExpr,
    /// Claimed latest prior serial at the address.
    pub prev_serial: LeanExpr,
    /// Access kind.
    pub kind: MemKind,
}

/// Map reconciliation kind (Lean `MapOpKind`; wire codes 0/1/2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MapKind {
    /// Membership read (root unchanged).
    Read,
    /// Sorted insert-or-update write (realized: in-place update at an existing key).
    Write,
    /// Non-membership read (NOT yet realized; assembly refuses).
    Absent,
}

impl MapKind {
    /// The map-ops table `op` column value.
    pub fn code(self) -> u32 {
        match self {
            MapKind::Read => 0,
            MapKind::Write => 1,
            MapKind::Absent => 2,
        }
    }
}

/// A boundary reconciliation `(root, key, value, op) → new_root` (Lean `MapOp`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MapOpSpec {
    /// Selector guard (active iff it evaluates to 1).
    pub guard: LeanExpr,
    /// The pre-root expression.
    pub root: LeanExpr,
    /// The map key expression.
    pub key: LeanExpr,
    /// The read/written value expression.
    pub value: LeanExpr,
    /// The post-root expression.
    pub new_root: LeanExpr,
    /// Reconciliation kind.
    pub op: MapKind,
}

/// One v2 constraint: a v1 form embedded whole, or one of the three new kinds
/// (Lean `VmConstraint2`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VmConstraint2 {
    /// An embedded v1 constraint form.
    Base(VmConstraint),
    /// A lookup into a declared table.
    Lookup(LookupSpec),
    /// A memory-table access row.
    MemOp(MemOpSpec),
    /// A map-ops-table reconciliation row.
    MapOp(MapOpSpec),
}

/// The Rust mirror of Lean's `EffectVmDescriptor2` (decoded from `emitVmJson2`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EffectVmDescriptor2 {
    /// AIR identity string.
    pub name: String,
    /// The main-trace base width.
    pub trace_width: usize,
    /// Number of public-input slots.
    pub public_input_count: usize,
    /// The declared tables.
    pub tables: Vec<TableDef2>,
    /// The constraint list (v2 grammar).
    pub constraints: Vec<VmConstraint2>,
    /// Legacy v1 hash-site carrier (must be EMPTY for the v2 assembly; graduated
    /// descriptors carry their sites as chip lookups).
    pub hash_sites: Vec<VmHashSite>,
    /// Legacy v1 range carrier (must be EMPTY for the v2 assembly).
    pub ranges: Vec<RangeSpec>,
}

/// Either wire shape, dispatched on the `"ir"` key (`parse_vm_descriptor_any`).
#[derive(Clone, Debug)]
pub enum AnyVmDescriptor {
    /// A v1 descriptor (no `"ir"` key): proves through `lean_descriptor_air`.
    V1(EffectVmDescriptor),
    /// A v2 descriptor (`"ir":2`): proves through this module.
    V2(EffectVmDescriptor2),
}

// ============================================================================
// JSON decode (the v2 grammar; byte-pinned by the Lean `#guard` golden)
// ============================================================================

fn parse_array<T>(
    c: &mut JsonCursor,
    mut item: impl FnMut(&mut JsonCursor) -> Result<T, String>,
) -> Result<Vec<T>, String> {
    c.expect(b'[')?;
    let mut v = Vec::new();
    if c.peek() == Some(b']') {
        c.expect(b']')?;
        return Ok(v);
    }
    loop {
        v.push(item(c)?);
        match c.peek() {
            Some(b',') => c.expect(b',')?,
            Some(b']') => {
                c.expect(b']')?;
                break;
            }
            other => {
                return Err(format!(
                    "expected ',' or ']' in array, found {:?}",
                    other.map(|b| b as char)
                ));
            }
        }
    }
    Ok(v)
}

fn parse_usize(c: &mut JsonCursor, what: &str) -> Result<usize, String> {
    let n = c.parse_int()?;
    if n < 0 {
        return Err(format!("negative {what} {n}"));
    }
    Ok(n as usize)
}

/// Validate the chip `params` object against the DEPLOYED Poseidon2 pins
/// (`babyBearD4W16` ↔ `circuit/src/poseidon2.rs`). A mismatch is a refusal, not a warning:
/// the chip table's row semantics is "the real permutation" and these are its parameters.
fn parse_chip_params(c: &mut JsonCursor) -> Result<(), String> {
    c.expect(b'{')?;
    let expected_num: &[(&str, i64)] = &[
        ("field_modulus", BABYBEAR_P as i64),
        ("d", 4),
        ("width", POSEIDON2_WIDTH as i64),
        ("sbox_degree", 7),
        ("sbox_registers", 1),
        ("half_full_rounds", 4),
        ("partial_rounds", 13),
        ("rate", CHIP_RATE as i64),
    ];
    loop {
        let key = c.parse_string()?;
        c.expect(b':')?;
        match key.as_str() {
            "rc_source" => {
                let s = c.parse_string()?;
                if s != "BABYBEAR_POSEIDON2_RC_16" {
                    return Err(format!("chip params rc_source \"{s}\" != deployed source"));
                }
            }
            "internal_diag_source" => {
                let s = c.parse_string()?;
                if s != "BABYBEAR_POSEIDON2_INTERNAL_DIAG_16" {
                    return Err(format!(
                        "chip params internal_diag_source \"{s}\" != deployed source"
                    ));
                }
            }
            other => {
                let v = c.parse_int()?;
                let Some(&(_, want)) = expected_num.iter().find(|(k, _)| *k == other) else {
                    return Err(format!("unknown chip param \"{other}\""));
                };
                if v != want {
                    return Err(format!("chip param {other} = {v}, deployed pin is {want}"));
                }
            }
        }
        match c.peek() {
            Some(b',') => c.expect(b',')?,
            Some(b'}') => {
                c.expect(b'}')?;
                break;
            }
            other => {
                return Err(format!(
                    "expected ',' or '}}' in chip params, found {:?}",
                    other.map(|b| b as char)
                ));
            }
        }
    }
    Ok(())
}

fn parse_table_def(c: &mut JsonCursor) -> Result<TableDef2, String> {
    c.expect(b'{')?;
    let mut id: Option<usize> = None;
    let mut name: Option<String> = None;
    let mut arity: Option<usize> = None;
    let mut sem_tag: Option<String> = None;
    let mut bits: Option<usize> = None;
    loop {
        let key = c.parse_string()?;
        c.expect(b':')?;
        match key.as_str() {
            "id" => id = Some(parse_usize(c, "table id")?),
            "name" => name = Some(c.parse_string()?),
            "arity" => arity = Some(parse_usize(c, "table arity")?),
            "sem" => sem_tag = Some(c.parse_string()?),
            "bits" => bits = Some(parse_usize(c, "range bits")?),
            "params" => parse_chip_params(c)?,
            other => return Err(format!("unknown table-def key \"{other}\"")),
        }
        match c.peek() {
            Some(b',') => c.expect(b',')?,
            Some(b'}') => {
                c.expect(b'}')?;
                break;
            }
            other => {
                return Err(format!(
                    "expected ',' or '}}' in table def, found {:?}",
                    other.map(|b| b as char)
                ));
            }
        }
    }
    let sem = match sem_tag.as_deref() {
        Some("main") => TableSem::Main,
        Some("poseidon2_chip") => TableSem::Poseidon2Chip,
        Some("range") => TableSem::Range {
            bits: bits.ok_or("range table def missing \"bits\"")?,
        },
        Some("memory") => TableSem::Memory,
        Some("map_ops") => TableSem::MapOps,
        Some(other) => return Err(format!("unknown table sem \"{other}\"")),
        None => return Err("table def missing \"sem\"".to_string()),
    };
    Ok(TableDef2 {
        id: id.ok_or("table def missing \"id\"")?,
        name: name.ok_or("table def missing \"name\"")?,
        arity: arity.ok_or("table def missing \"arity\"")?,
        sem,
    })
}

fn parse_constraint2(c: &mut JsonCursor) -> Result<VmConstraint2, String> {
    c.expect(b'{')?;
    c.expect_key("t")?;
    let tag = c.parse_string()?;
    let out = match tag.as_str() {
        "lookup" => {
            c.expect(b',')?;
            c.expect_key("table")?;
            let table = parse_usize(c, "lookup table id")?;
            c.expect(b',')?;
            c.expect_key("tuple")?;
            let tuple = parse_array(c, parse_expr)?;
            VmConstraint2::Lookup(LookupSpec { table, tuple })
        }
        "mem_op" => {
            c.expect(b',')?;
            c.expect_key("kind")?;
            let kind = match c.parse_string()?.as_str() {
                "read" => MemKind::Read,
                "write" => MemKind::Write,
                other => return Err(format!("unknown mem_op kind \"{other}\"")),
            };
            c.expect(b',')?;
            c.expect_key("guard")?;
            let guard = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("addr")?;
            let addr = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("value")?;
            let value = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("prev_value")?;
            let prev_value = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("prev_serial")?;
            let prev_serial = parse_expr(c)?;
            VmConstraint2::MemOp(MemOpSpec {
                guard,
                addr,
                value,
                prev_value,
                prev_serial,
                kind,
            })
        }
        "map_op" => {
            c.expect(b',')?;
            c.expect_key("op")?;
            let op = match c.parse_string()?.as_str() {
                "read" => MapKind::Read,
                "write" => MapKind::Write,
                "absent" => MapKind::Absent,
                other => return Err(format!("unknown map_op kind \"{other}\"")),
            };
            c.expect(b',')?;
            c.expect_key("guard")?;
            let guard = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("root")?;
            let root = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("key")?;
            let key = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("value")?;
            let value = parse_expr(c)?;
            c.expect(b',')?;
            c.expect_key("new_root")?;
            let new_root = parse_expr(c)?;
            VmConstraint2::MapOp(MapOpSpec {
                guard,
                root,
                key,
                value,
                new_root,
                op,
            })
        }
        v1tag => VmConstraint2::Base(parse_vm_constraint_body(c, v1tag)?),
    };
    c.expect(b'}')?;
    Ok(out)
}

/// **`parse_vm_descriptor2`** — decode a Lean `emitVmJson2` string (`"ir":2`).
pub fn parse_vm_descriptor2(json: &str) -> Result<EffectVmDescriptor2, String> {
    match parse_vm_descriptor_any(json)? {
        AnyVmDescriptor::V2(d) => Ok(d),
        AnyVmDescriptor::V1(_) => {
            Err("descriptor has no \"ir\" key (v1 wire); use parse_vm_descriptor".to_string())
        }
    }
}

/// **`parse_vm_descriptor_any`** — the versioned dispatcher: a missing `"ir"` key is wire
/// version 1 (the untouched `emitVmJson` grammar, re-encoded as `AnyVmDescriptor::V1`);
/// `"ir":2` is the multi-table grammar. Both registries live until the flag-day.
pub fn parse_vm_descriptor_any(json: &str) -> Result<AnyVmDescriptor, String> {
    let mut c = JsonCursor::new(json);
    c.expect(b'{')?;

    let mut name: Option<String> = None;
    let mut ir: Option<usize> = None;
    let mut trace_width: Option<usize> = None;
    let mut public_input_count: Option<usize> = None;
    let mut tables: Vec<TableDef2> = Vec::new();
    let mut constraints: Option<Vec<VmConstraint2>> = None;
    let mut hash_sites: Vec<VmHashSite> = Vec::new();
    let mut ranges: Vec<RangeSpec> = Vec::new();

    loop {
        let key = c.parse_string()?;
        c.expect(b':')?;
        match key.as_str() {
            "name" => name = Some(c.parse_string()?),
            "ir" => ir = Some(parse_usize(&mut c, "ir version")?),
            "trace_width" => trace_width = Some(parse_usize(&mut c, "trace_width")?),
            "public_input_count" => {
                public_input_count = Some(parse_usize(&mut c, "public_input_count")?)
            }
            "tables" => tables = parse_array(&mut c, parse_table_def)?,
            "constraints" => constraints = Some(parse_array(&mut c, parse_constraint2)?),
            "hash_sites" => hash_sites = parse_array(&mut c, parse_hash_site)?,
            "ranges" => ranges = parse_array(&mut c, parse_range)?,
            other => return Err(format!("unknown top-level key \"{other}\"")),
        }
        match c.peek() {
            Some(b',') => c.expect(b',')?,
            Some(b'}') => {
                c.expect(b'}')?;
                break;
            }
            other => {
                return Err(format!(
                    "expected ',' or '}}' in descriptor, found {:?}",
                    other.map(|b| b as char)
                ));
            }
        }
    }

    let name = name.ok_or("descriptor missing \"name\"")?;
    let trace_width = trace_width.ok_or("descriptor missing \"trace_width\"")?;
    let public_input_count = public_input_count.ok_or("descriptor missing \"public_input_count\"")?;
    let constraints = constraints.ok_or("descriptor missing \"constraints\"")?;

    match ir {
        None => {
            // v1 wire: no tables, no v2-only constraint kinds.
            if !tables.is_empty() {
                return Err("v1 descriptor (no \"ir\") declares tables".to_string());
            }
            let mut v1 = Vec::with_capacity(constraints.len());
            for k in constraints {
                match k {
                    VmConstraint2::Base(b) => v1.push(b),
                    other => {
                        return Err(format!(
                            "v1 descriptor (no \"ir\") carries a v2-only constraint: {other:?}"
                        ));
                    }
                }
            }
            Ok(AnyVmDescriptor::V1(EffectVmDescriptor {
                name,
                trace_width,
                public_input_count,
                constraints: v1,
                hash_sites,
                ranges,
            }))
        }
        Some(2) => Ok(AnyVmDescriptor::V2(EffectVmDescriptor2 {
            name,
            trace_width,
            public_input_count,
            tables,
            constraints,
            hash_sites,
            ranges,
        })),
        Some(v) => Err(format!("unsupported descriptor ir version {v}")),
    }
}

// ============================================================================
// Layout: byte-limb decomposition geometry + the main-trace aux blocks
// ============================================================================

/// Limb geometry of a `bits`-wide byte decomposition: `(num_limbs, top_bits)`.
/// The top limb is bit-bound when `top_bits < 8` (the tight bound); full limbs are
/// byte-bus lookups.
const fn limb_geom(bits: usize) -> (usize, usize) {
    let n = bits.div_ceil(LIMB_BITS);
    (n, bits - (n - 1) * LIMB_BITS)
}

/// Aux columns one `bits`-wide decomposition adds (limbs + top bits when partial).
const fn decomp_cols(bits: usize) -> usize {
    let (n, top) = limb_geom(bits);
    n + if top < LIMB_BITS { top } else { 0 }
}

/// One declared range lookup, resolved to its aux block in the extended main trace.
#[derive(Clone, Debug)]
struct RangeBlock {
    /// The range-checked base wire (the lookup tuple's single `Var`).
    wire: usize,
    /// Declared bit width (from the range table def).
    bits: usize,
    /// First limb column (extended-trace index).
    limb0: usize,
}

/// One declared submask lookup, resolved to its bit blocks.
#[derive(Clone, Debug)]
struct SubmaskBlock {
    /// The kept (must-be-subset) mask expression — lookup tuple\[0\].
    keep: LeanExpr,
    /// The held (superset) mask expression — lookup tuple\[1\].
    held: LeanExpr,
    /// First bit column of the keep decomposition.
    keep0: usize,
    /// First bit column of the held decomposition.
    held0: usize,
}

/// The resolved main-instance layout: base wires, then per-range limb blocks, then
/// per-submask bit blocks.
#[derive(Clone, Debug)]
struct MainLayout {
    width: usize,
    ranges: Vec<RangeBlock>,
    submasks: Vec<SubmaskBlock>,
}

impl MainLayout {
    fn build(desc: &EffectVmDescriptor2) -> Result<Self, String> {
        let range_bits = desc.tables.iter().find_map(|t| match t.sem {
            TableSem::Range { bits } => Some(bits),
            _ => None,
        });
        let mut next = desc.trace_width;
        let mut ranges = Vec::new();
        let mut submasks = Vec::new();
        for (ci, k) in desc.constraints.iter().enumerate() {
            let VmConstraint2::Lookup(l) = k else { continue };
            match l.table {
                TID_RANGE => {
                    let bits = range_bits.ok_or_else(|| {
                        format!("constraint {ci}: range lookup but no range table declared")
                    })?;
                    if l.tuple.len() != 1 {
                        return Err(format!(
                            "constraint {ci}: range lookup tuple arity {} != 1",
                            l.tuple.len()
                        ));
                    }
                    let LeanExpr::Var(wire) = l.tuple[0] else {
                        return Err(format!(
                            "constraint {ci}: range lookup tuple must be a bare column \
                             (graduateV1 emits `.var wire`)"
                        ));
                    };
                    ranges.push(RangeBlock {
                        wire,
                        bits,
                        limb0: next,
                    });
                    next += decomp_cols(bits);
                }
                TID_CUSTOM_SUBMASK => {
                    if l.tuple.len() != 2 {
                        return Err(format!(
                            "constraint {ci}: submask lookup tuple arity {} != 2",
                            l.tuple.len()
                        ));
                    }
                    let keep0 = next;
                    let held0 = next + SUBMASK_BITS;
                    next += 2 * SUBMASK_BITS;
                    submasks.push(SubmaskBlock {
                        keep: l.tuple[0].clone(),
                        held: l.tuple[1].clone(),
                        keep0,
                        held0,
                    });
                }
                TID_P2 => {
                    if l.tuple.len() != CHIP_TUPLE_LEN {
                        return Err(format!(
                            "constraint {ci}: chip lookup tuple arity {} != {CHIP_TUPLE_LEN}",
                            l.tuple.len()
                        ));
                    }
                }
                TID_MAIN | TID_MEMORY | TID_MAP_OPS => {
                    return Err(format!(
                        "constraint {ci}: lookups into table {} are not part of the graduated \
                         grammar (state accesses are mem_op / map_op constraints)",
                        l.table
                    ));
                }
                other => {
                    return Err(format!(
                        "constraint {ci}: custom table id {other} has no realized relation \
                         (only the submask table, id {TID_CUSTOM_SUBMASK}, is bound; the \
                         custom-table contents manifest is the named IR follow-up)"
                    ));
                }
            }
        }
        Ok(MainLayout {
            width: next,
            ranges,
            submasks,
        })
    }
}

/// Bounds- and shape-check a v2 descriptor for assembly. Returns the resolved layout.
fn check_descriptor2(desc: &EffectVmDescriptor2) -> Result<MainLayout, String> {
    if !desc.hash_sites.is_empty() || !desc.ranges.is_empty() {
        return Err(
            "v2 assembly requires a GRADUATED descriptor (empty hash_sites/ranges carriers); \
             embedV1-shaped descriptors keep the v1 path during the epoch"
                .to_string(),
        );
    }
    let w = desc.trace_width;
    let chk = |e: &LeanExpr, what: &str, ci: usize| -> Result<(), String> {
        if let Some(m) = e.max_var() {
            if m >= w {
                return Err(format!(
                    "constraint {ci}: {what} references column {m} >= trace_width {w}"
                ));
            }
        }
        Ok(())
    };
    for (ci, k) in desc.constraints.iter().enumerate() {
        match k {
            VmConstraint2::Base(VmConstraint::Gate(body))
            | VmConstraint2::Base(VmConstraint::Boundary { body, .. }) => {
                chk(body, "gate/boundary body", ci)?
            }
            VmConstraint2::Base(VmConstraint::Transition { hi, lo }) => {
                if EFFECTVM_STATE_BEFORE_BASE + hi >= w || EFFECTVM_STATE_AFTER_BASE + lo >= w {
                    return Err(format!("constraint {ci}: transition out of bounds"));
                }
            }
            VmConstraint2::Base(VmConstraint::PiBinding { col, pi_index, .. }) => {
                if *col >= w {
                    return Err(format!("constraint {ci}: pi_binding col out of bounds"));
                }
                if *pi_index >= desc.public_input_count {
                    return Err(format!("constraint {ci}: pi_binding pi_index out of bounds"));
                }
            }
            VmConstraint2::Lookup(l) => {
                for e in &l.tuple {
                    chk(e, "lookup tuple element", ci)?;
                }
            }
            VmConstraint2::MemOp(m) => {
                for e in [&m.guard, &m.addr, &m.value, &m.prev_value, &m.prev_serial] {
                    chk(e, "mem_op field", ci)?;
                }
            }
            VmConstraint2::MapOp(m) => {
                if m.op == MapKind::Absent {
                    return Err(format!(
                        "constraint {ci}: map_op kind `absent` is not realized yet (the \
                         bracketed-gap non-membership leg rides the nullifier-insert lane)"
                    ));
                }
                for e in [&m.guard, &m.root, &m.key, &m.value, &m.new_root] {
                    chk(e, "map_op field", ci)?;
                }
            }
        }
    }
    MainLayout::build(desc)
}

// ============================================================================
// The multi-table AIR (one enum type: prove_batch is monomorphic in the AIR)
// ============================================================================

// -- Memory table layout (one row per access, log order). --
const MEM_ADDR: usize = 0;
const MEM_VALUE: usize = 1;
const MEM_PREV_VALUE: usize = 2;
const MEM_PREV_SERIAL: usize = 3;
const MEM_KIND: usize = 4;
const MEM_SERIAL: usize = 5;
const MEM_IS_REAL: usize = 6;
const MEM_GAP: usize = 7;
const MEM_GAP_LIMB0: usize = 8;
const MEM_WIDTH: usize = MEM_GAP_LIMB0 + decomp_cols(MEM_GAP_BITS); // 8 + 10 = 18

// -- Memory boundary layout (one row per declared address, strictly increasing). --
const MB_ADDR: usize = 0;
const MB_INIT_VAL: usize = 1;
const MB_FIN_VAL: usize = 2;
const MB_FIN_SERIAL: usize = 3;
const MB_IS_REAL: usize = 4;
const MB_ADDR_MULT: usize = 5;
const MB_AGAP: usize = 6;
const MB_AGAP_LIMB0: usize = 7;
const MB_ACHK: usize = MB_AGAP_LIMB0 + decomp_cols(MEM_GAP_BITS); // 17
const MB_ACHK_LIMB0: usize = MB_ACHK + 1; // 18
const MB_WIDTH: usize = MB_ACHK_LIMB0 + decomp_cols(MEM_GAP_BITS); // 28

// -- Map-ops table layout (one row per reconciliation, log order). --
const MAP_ROOT: usize = 0;
const MAP_KEY: usize = 1;
const MAP_VALUE: usize = 2;
const MAP_OP: usize = 3;
const MAP_NEW_ROOT: usize = 4;
const MAP_IS_REAL: usize = 5;
const MAP_OLD_VALUE: usize = 6;
const MAP_SIB0: usize = 7;
const MAP_DIR0: usize = MAP_SIB0 + HEAP_TREE_DEPTH; // 23
const MAP_AUX0: usize = MAP_DIR0 + HEAP_TREE_DEPTH; // 39
/// Permutation blocks per map row: old leaf + new leaf + two depth-16 chains.
const MAP_PERM_BLOCKS: usize = 2 + 2 * HEAP_TREE_DEPTH; // 34
const MAP_WIDTH: usize = MAP_AUX0 + MAP_PERM_BLOCKS * POSEIDON2_PERM_AUX_COLS;

// -- Chip table layout. --
const CHIP_ARITY: usize = 0;
const CHIP_IN0: usize = 1;
const CHIP_OUT: usize = CHIP_IN0 + CHIP_RATE; // 9
const CHIP_MULT: usize = CHIP_OUT + 1; // 10
const CHIP_AUX0: usize = CHIP_MULT + 1; // 11
const CHIP_WIDTH: usize = CHIP_AUX0 + POSEIDON2_PERM_AUX_COLS; // 363

/// The five-table interpreter AIR. One Rust type covering every instance of the batch
/// (the batch prover is monomorphic in the AIR type), entirely descriptor-driven.
#[derive(Clone)]
pub enum Ir2Air {
    /// The main instance: the descriptor's own constraints + bus interactions.
    Main {
        /// The interpreted descriptor.
        desc: EffectVmDescriptor2,
        /// Resolved aux layout.
        layout: MainLayoutPub,
    },
    /// The Poseidon2 chip table (every row a REAL permutation; `ChipTableSound`).
    Chip,
    /// The `[0,256)` byte table (value column pinned to the row index).
    ByteTable,
    /// The memory access table (Blum discipline + the read/write multiset legs).
    Memory,
    /// The memory boundary (init/final image over the declared, strictly increasing
    /// address list).
    MemBoundary,
    /// The map-ops table (in-row sorted-Poseidon2 openings).
    MapOps,
}

/// Public re-export wrapper of the resolved main layout (kept opaque; constructed by
/// `check_descriptor2` via the prove/verify entry points).
#[derive(Clone, Debug)]
pub struct MainLayoutPub(MainLayout);

impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for Ir2Air {
    fn width(&self) -> usize {
        match self {
            Ir2Air::Main { layout, .. } => layout.0.width,
            Ir2Air::Chip => CHIP_WIDTH,
            Ir2Air::ByteTable => 2,
            Ir2Air::Memory => MEM_WIDTH,
            Ir2Air::MemBoundary => MB_WIDTH,
            Ir2Air::MapOps => MAP_WIDTH,
        }
    }

    fn num_public_values(&self) -> usize {
        match self {
            Ir2Air::Main { desc, .. } => desc.public_input_count,
            _ => 0,
        }
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        match self {
            // The Poseidon2 S-box (degree 7) dominates the permutation-bearing tables.
            Ir2Air::Chip | Ir2Air::MapOps => Some(7),
            // Let the symbolic analysis infer the main instance (descriptor gates vary).
            _ => None,
        }
    }
}

/// Emit one byte-limb decomposition: `value_expr = Σ limbᵢ·256ⁱ`, full limbs queried on the
/// byte bus, a partial top limb bit-bound tightly. The realization of "∈ [0, 2^bits)".
fn eval_decomp<AB>(builder: &mut AB, value_expr: AB::Expr, limbs: &[AB::Var], bits: usize)
where
    AB: AirBuilder + InteractionBuilder,
    AB::F: PrimeField32,
{
    let bus = LookupBus::new(BUS_BYTE);
    let (n, top_bits) = limb_geom(bits);
    let partial = top_bits < LIMB_BITS;
    let limb_base = AB::Expr::from_u64(1 << LIMB_BITS);
    let mut recomposed = AB::Expr::ZERO;
    let mut weight = AB::Expr::ONE;
    for i in 0..n {
        let limb: AB::Expr = limbs[i].into();
        recomposed = recomposed + limb.clone() * weight.clone();
        weight = weight.clone() * limb_base.clone();
        if i == n - 1 && partial {
            // Tight top-limb bound: bit-decompose into `top_bits` booleans.
            let mut top_recomp = AB::Expr::ZERO;
            let mut bw = AB::Expr::ONE;
            for b in 0..top_bits {
                let bit: AB::Expr = limbs[n + b].into();
                builder.assert_zero(bit.clone() * (bit.clone() - AB::Expr::ONE));
                top_recomp = top_recomp + bit * bw.clone();
                bw = bw.clone() + bw;
            }
            builder.assert_zero(top_recomp - limb);
        } else {
            bus.lookup_key(builder, [limb], AB::Expr::ONE);
        }
    }
    builder.assert_zero(recomposed - value_expr);
}

/// The in-circuit `hash_many([a, b])` input state (two-element absorb, arity tag at state 4)
/// — byte-identical to `poseidon2::hash_many` and the v1 site absorb.
fn hash2_state<AB: AirBuilder>(a: AB::Expr, b: AB::Expr) -> [AB::Expr; POSEIDON2_WIDTH] {
    let mut st: [AB::Expr; POSEIDON2_WIDTH] = core::array::from_fn(|_| AB::Expr::ZERO);
    st[0] = a;
    st[1] = b;
    st[4] = AB::Expr::from_u64(2);
    st
}

/// The in-circuit `hash_fact(l, [r])` input state (the Merkle NODE hash) — byte-identical
/// to `poseidon2::hash_fact` (marker at state 5, leaf flag at state 6).
fn fact_state<AB: AirBuilder>(l: AB::Expr, r: AB::Expr) -> [AB::Expr; POSEIDON2_WIDTH] {
    let mut st: [AB::Expr; POSEIDON2_WIDTH] = core::array::from_fn(|_| AB::Expr::ZERO);
    st[0] = l;
    st[1] = r;
    st[5] = AB::Expr::from_u64(FACT_MARK as u64);
    st[6] = AB::Expr::ONE;
    st
}

impl<AB> Air<AB> for Ir2Air
where
    AB: AirBuilder + PermutationAirBuilder + InteractionBuilder,
    AB::F: PrimeField32,
{
    fn eval(&self, builder: &mut AB) {
        let (local, next): (Vec<AB::Var>, Vec<AB::Var>) = {
            let main = builder.main();
            (main.current_slice().to_vec(), main.next_slice().to_vec())
        };
        match self {
            // ----------------------------------------------------------------
            Ir2Air::Main { desc, layout } => {
                let pv: Vec<AB::Expr> =
                    builder.public_values().iter().map(|&v| v.into()).collect();

                // -- The embedded v1 forms, on the v1 domains. --
                {
                    let mut fb = builder.when_first_row();
                    for k in &desc.constraints {
                        if let VmConstraint2::Base(c) = k {
                            match c {
                                VmConstraint::PiBinding {
                                    row: VmRow::First,
                                    col,
                                    pi_index,
                                } => fb.assert_zero(local[*col].into() - pv[*pi_index].clone()),
                                VmConstraint::Boundary {
                                    row: VmRow::First,
                                    body,
                                } => fb.assert_zero(body.eval_expr::<AB>(&local)),
                                _ => {}
                            }
                        }
                    }
                }
                {
                    let mut lb = builder.when_last_row();
                    for k in &desc.constraints {
                        if let VmConstraint2::Base(c) = k {
                            match c {
                                VmConstraint::PiBinding {
                                    row: VmRow::Last,
                                    col,
                                    pi_index,
                                } => lb.assert_zero(local[*col].into() - pv[*pi_index].clone()),
                                VmConstraint::Boundary {
                                    row: VmRow::Last,
                                    body,
                                } => lb.assert_zero(body.eval_expr::<AB>(&local)),
                                _ => {}
                            }
                        }
                    }
                }
                {
                    let mut tb = builder.when_transition();
                    for k in &desc.constraints {
                        if let VmConstraint2::Base(c) = k {
                            match c {
                                VmConstraint::Gate(body) => {
                                    tb.assert_zero(body.eval_expr::<AB>(&local))
                                }
                                VmConstraint::Transition { hi, lo } => {
                                    let n: AB::Expr = next[EFFECTVM_STATE_BEFORE_BASE + hi].into();
                                    let l: AB::Expr = local[EFFECTVM_STATE_AFTER_BASE + lo].into();
                                    tb.assert_zero(n - l);
                                }
                                _ => {}
                            }
                        }
                    }
                }

                // -- Chip lookups: each declared tuple queried on the chip bus, every row. --
                let p2 = LookupBus::new(BUS_P2);
                for k in &desc.constraints {
                    if let VmConstraint2::Lookup(l) = k {
                        if l.table == TID_P2 {
                            let tuple: Vec<AB::Expr> =
                                l.tuple.iter().map(|e| e.eval_expr::<AB>(&local)).collect();
                            p2.lookup_key(builder, tuple, AB::Expr::ONE);
                        }
                    }
                }

                // -- Range lookups: the byte-limb realization, every row. --
                for rb in &layout.0.ranges {
                    let cols = decomp_cols(rb.bits);
                    let limbs: Vec<AB::Var> = local[rb.limb0..rb.limb0 + cols].to_vec();
                    eval_decomp(builder, local[rb.wire].into(), &limbs, rb.bits);
                }

                // -- Submask lookups: the bitwise a&b=a relation at SUBMASK_BITS. --
                for sb in &layout.0.submasks {
                    let mut keep_recomp = AB::Expr::ZERO;
                    let mut held_recomp = AB::Expr::ZERO;
                    let mut w = AB::Expr::ONE;
                    for i in 0..SUBMASK_BITS {
                        let kb: AB::Expr = local[sb.keep0 + i].into();
                        let hb: AB::Expr = local[sb.held0 + i].into();
                        builder.assert_zero(kb.clone() * (kb.clone() - AB::Expr::ONE));
                        builder.assert_zero(hb.clone() * (hb.clone() - AB::Expr::ONE));
                        // Non-amplification, bitwise: keep ⇒ held.
                        builder.assert_zero(kb.clone() * (AB::Expr::ONE - hb.clone()));
                        keep_recomp = keep_recomp + kb * w.clone();
                        held_recomp = held_recomp + hb * w.clone();
                        w = w.clone() + w;
                    }
                    builder.assert_zero(keep_recomp - sb.keep.eval_expr::<AB>(&local));
                    builder.assert_zero(held_recomp - sb.held.eval_expr::<AB>(&local));
                }

                // -- Mem ops: send the instrumented row on the memory log bus. --
                let mem_log = PermutationCheckBus::new(BUS_MEM_LOG);
                for k in &desc.constraints {
                    if let VmConstraint2::MemOp(m) = k {
                        let fields = [
                            m.addr.eval_expr::<AB>(&local),
                            m.value.eval_expr::<AB>(&local),
                            m.prev_value.eval_expr::<AB>(&local),
                            m.prev_serial.eval_expr::<AB>(&local),
                            AB::Expr::from_u64(m.kind.code() as u64),
                        ];
                        mem_log.send(builder, fields, m.guard.eval_expr::<AB>(&local));
                    }
                }

                // -- Map ops: send the reconciliation row on the map log bus. --
                let map_log = PermutationCheckBus::new(BUS_MAP_LOG);
                for k in &desc.constraints {
                    if let VmConstraint2::MapOp(m) = k {
                        let fields = [
                            m.root.eval_expr::<AB>(&local),
                            m.key.eval_expr::<AB>(&local),
                            m.value.eval_expr::<AB>(&local),
                            AB::Expr::from_u64(m.op.code() as u64),
                            m.new_root.eval_expr::<AB>(&local),
                        ];
                        map_log.send(builder, fields, m.guard.eval_expr::<AB>(&local));
                    }
                }
            }

            // ----------------------------------------------------------------
            Ir2Air::Chip => {
                let arity: AB::Expr = local[CHIP_ARITY].into();
                let two = AB::Expr::from_u64(2);
                let four = AB::Expr::from_u64(4);
                // arity ∈ {0 (pad), 2, 4} — the deployed site arities.
                builder.assert_zero(
                    arity.clone() * (arity.clone() - two.clone()) * (arity.clone() - four.clone()),
                );
                // Inputs beyond the arity are ZERO (the padTo discipline — a row with junk
                // padding is not a genuine chipRow and must be rejected).
                for i in 0..2 {
                    // in0/in1 vanish unless arity ∈ {2,4}.
                    let inp: AB::Expr = local[CHIP_IN0 + i].into();
                    builder
                        .assert_zero(inp * (arity.clone() - two.clone()) * (arity.clone() - four.clone()));
                }
                for i in 2..4 {
                    // in2/in3 vanish unless arity = 4.
                    let inp: AB::Expr = local[CHIP_IN0 + i].into();
                    builder.assert_zero(inp * (arity.clone() - four.clone()));
                }
                for i in 4..CHIP_RATE {
                    // The deployed absorb is rate-4 with the arity tag at state 4; the high
                    // padding lanes are identically zero.
                    builder.assert_zero(local[CHIP_IN0 + i].into());
                }
                // The REAL permutation: state = (in0..in3, arity tag), output pinned.
                let mut st: [AB::Expr; POSEIDON2_WIDTH] = core::array::from_fn(|_| AB::Expr::ZERO);
                for i in 0..4 {
                    st[i] = local[CHIP_IN0 + i].into();
                }
                st[4] = arity;
                let aux: Vec<AB::Var> =
                    local[CHIP_AUX0..CHIP_AUX0 + POSEIDON2_PERM_AUX_COLS].to_vec();
                let digest = poseidon2_permute_expr::<AB>(builder, st, &aux);
                builder.assert_zero(local[CHIP_OUT].into() - digest);

                // Provide the (arity, ins, out) tuple, consumed `mult` times.
                let bus = LookupBus::new(BUS_P2);
                let mut tuple: Vec<AB::Expr> = Vec::with_capacity(CHIP_TUPLE_LEN);
                tuple.push(local[CHIP_ARITY].into());
                for i in 0..CHIP_RATE {
                    tuple.push(local[CHIP_IN0 + i].into());
                }
                tuple.push(local[CHIP_OUT].into());
                bus.table_entry(builder, tuple, local[CHIP_MULT].into());
            }

            // ----------------------------------------------------------------
            Ir2Air::ByteTable => {
                // value = row index (first row 0, increment 1): the table cannot lie.
                builder.when_first_row().assert_zero(local[0].into());
                builder
                    .when_transition()
                    .assert_zero(next[0].into() - local[0].into() - AB::Expr::ONE);
                let bus = LookupBus::new(BUS_BYTE);
                bus.table_entry(builder, [local[0].into()], local[1].into());
            }

            // ----------------------------------------------------------------
            Ir2Air::Memory => {
                let is_real: AB::Expr = local[MEM_IS_REAL].into();
                let kind: AB::Expr = local[MEM_KIND].into();
                builder.assert_zero(is_real.clone() * (is_real.clone() - AB::Expr::ONE));
                builder.assert_zero(kind.clone() * (kind.clone() - AB::Expr::ONE));
                // Real rows form a prefix.
                builder.when_transition().assert_zero(
                    (AB::Expr::ONE - local[MEM_IS_REAL].into()) * next[MEM_IS_REAL].into(),
                );
                // Positional serials: 1, 2, 3, … (Lean: op i carries serial i+1).
                builder
                    .when_first_row()
                    .assert_zero(local[MEM_SERIAL].into() - AB::Expr::ONE);
                builder.when_transition().assert_zero(
                    next[MEM_SERIAL].into() - local[MEM_SERIAL].into() - AB::Expr::ONE,
                );
                // Read discipline: a read returns exactly its claimed previous value.
                builder.assert_zero(
                    is_real.clone()
                        * (AB::Expr::ONE - kind)
                        * (local[MEM_VALUE].into() - local[MEM_PREV_VALUE].into()),
                );
                // prev_serial < serial (Disciplined): gap = is_real·(serial − 1 − prev_serial)
                // and gap ∈ [0, 2^30) by byte decomposition.
                builder.assert_zero(
                    local[MEM_GAP].into()
                        - is_real.clone()
                            * (local[MEM_SERIAL].into()
                                - AB::Expr::ONE
                                - local[MEM_PREV_SERIAL].into()),
                );
                let limbs: Vec<AB::Var> =
                    local[MEM_GAP_LIMB0..MEM_GAP_LIMB0 + decomp_cols(MEM_GAP_BITS)].to_vec();
                eval_decomp(builder, local[MEM_GAP].into(), &limbs, MEM_GAP_BITS);

                // The table carries EXACTLY the gathered log (memTableFaithful).
                let mem_log = PermutationCheckBus::new(BUS_MEM_LOG);
                mem_log.receive(
                    builder,
                    [
                        local[MEM_ADDR].into(),
                        local[MEM_VALUE].into(),
                        local[MEM_PREV_VALUE].into(),
                        local[MEM_PREV_SERIAL].into(),
                        local[MEM_KIND].into(),
                    ],
                    is_real.clone(),
                );
                // The Blum multiset legs: every op consumes its claimed prior tuple and
                // publishes its own (reads republish their value — Lean writeSetFrom).
                let mem_check = PermutationCheckBus::new(BUS_MEM_CHECK);
                mem_check.send(
                    builder,
                    [
                        local[MEM_ADDR].into(),
                        local[MEM_VALUE].into(),
                        local[MEM_SERIAL].into(),
                    ],
                    is_real.clone(),
                );
                mem_check.receive(
                    builder,
                    [
                        local[MEM_ADDR].into(),
                        local[MEM_PREV_VALUE].into(),
                        local[MEM_PREV_SERIAL].into(),
                    ],
                    is_real.clone(),
                );
                // Address closure: every op address is a declared boundary address.
                let addrs = LookupBus::new(BUS_MEM_ADDRS);
                addrs.lookup_key(builder, [local[MEM_ADDR].into()], is_real);
            }

            // ----------------------------------------------------------------
            Ir2Air::MemBoundary => {
                let is_real: AB::Expr = local[MB_IS_REAL].into();
                builder.assert_zero(is_real.clone() * (is_real.clone() - AB::Expr::ONE));
                builder.when_transition().assert_zero(
                    (AB::Expr::ONE - local[MB_IS_REAL].into()) * next[MB_IS_REAL].into(),
                );
                // Strictly increasing declared addresses (⇒ Nodup): on a real→real step the
                // gap (next.addr − addr − 1) is bound and range-checked.
                builder.when_transition().assert_zero(
                    local[MB_AGAP].into()
                        - next[MB_IS_REAL].into()
                            * (next[MB_ADDR].into() - local[MB_ADDR].into() - AB::Expr::ONE),
                );
                let agap_limbs: Vec<AB::Var> =
                    local[MB_AGAP_LIMB0..MB_AGAP_LIMB0 + decomp_cols(MEM_GAP_BITS)].to_vec();
                eval_decomp(builder, local[MB_AGAP].into(), &agap_limbs, MEM_GAP_BITS);
                // Address magnitude bound (so the increasing chain cannot wrap the field):
                // addr_chk = is_real·addr ∈ [0, 2^30).
                builder.assert_zero(
                    local[MB_ACHK].into() - is_real.clone() * local[MB_ADDR].into(),
                );
                let achk_limbs: Vec<AB::Var> =
                    local[MB_ACHK_LIMB0..MB_ACHK_LIMB0 + decomp_cols(MEM_GAP_BITS)].to_vec();
                eval_decomp(builder, local[MB_ACHK].into(), &achk_limbs, MEM_GAP_BITS);

                // Init entries produced at serial 0; final entries consumed.
                let mem_check = PermutationCheckBus::new(BUS_MEM_CHECK);
                mem_check.send(
                    builder,
                    [
                        local[MB_ADDR].into(),
                        local[MB_INIT_VAL].into(),
                        AB::Expr::ZERO,
                    ],
                    is_real.clone(),
                );
                mem_check.receive(
                    builder,
                    [
                        local[MB_ADDR].into(),
                        local[MB_FIN_VAL].into(),
                        local[MB_FIN_SERIAL].into(),
                    ],
                    is_real,
                );
                // The declared-address table for closure lookups.
                let addrs = LookupBus::new(BUS_MEM_ADDRS);
                addrs.table_entry(builder, [local[MB_ADDR].into()], local[MB_ADDR_MULT].into());
            }

            // ----------------------------------------------------------------
            Ir2Air::MapOps => {
                let is_real: AB::Expr = local[MAP_IS_REAL].into();
                let op: AB::Expr = local[MAP_OP].into();
                builder.assert_zero(is_real.clone() * (is_real.clone() - AB::Expr::ONE));
                builder.assert_zero(op.clone() * (op.clone() - AB::Expr::ONE));
                // A read returns the committed value: old_value = value on read rows.
                builder.assert_zero(
                    is_real.clone()
                        * (AB::Expr::ONE - op)
                        * (local[MAP_OLD_VALUE].into() - local[MAP_VALUE].into()),
                );
                for lvl in 0..HEAP_TREE_DEPTH {
                    let dir: AB::Expr = local[MAP_DIR0 + lvl].into();
                    builder.assert_zero(dir.clone() * (dir - AB::Expr::ONE));
                }

                let aux_block = |i: usize| -> Vec<AB::Var> {
                    let base = MAP_AUX0 + i * POSEIDON2_PERM_AUX_COLS;
                    local[base..base + POSEIDON2_PERM_AUX_COLS].to_vec()
                };

                // Leaf digests: hash[key, old_value] and hash[key, value].
                let old_leaf = poseidon2_permute_expr::<AB>(
                    builder,
                    hash2_state::<AB>(local[MAP_KEY].into(), local[MAP_OLD_VALUE].into()),
                    &aux_block(0),
                );
                let new_leaf = poseidon2_permute_expr::<AB>(
                    builder,
                    hash2_state::<AB>(local[MAP_KEY].into(), local[MAP_VALUE].into()),
                    &aux_block(1),
                );

                // The two chains share siblings and directions: the in-place sorted-tree
                // leaf update (HeapUpdateWitness's shape).
                let mut cur_old = old_leaf;
                let mut cur_new = new_leaf;
                for lvl in 0..HEAP_TREE_DEPTH {
                    let sib: AB::Expr = local[MAP_SIB0 + lvl].into();
                    let dir: AB::Expr = local[MAP_DIR0 + lvl].into();
                    let mix = |cur: AB::Expr| -> (AB::Expr, AB::Expr) {
                        let left = (AB::Expr::ONE - dir.clone()) * cur.clone()
                            + dir.clone() * sib.clone();
                        let right =
                            (AB::Expr::ONE - dir.clone()) * sib.clone() + dir.clone() * cur;
                        (left, right)
                    };
                    let (lo, ro) = mix(cur_old);
                    cur_old = poseidon2_permute_expr::<AB>(
                        builder,
                        fact_state::<AB>(lo, ro),
                        &aux_block(2 + lvl),
                    );
                    let (ln, rn) = mix(cur_new);
                    cur_new = poseidon2_permute_expr::<AB>(
                        builder,
                        fact_state::<AB>(ln, rn),
                        &aux_block(2 + HEAP_TREE_DEPTH + lvl),
                    );
                }
                // The old path authenticates against the pre-root; the new path IS the
                // post-root. (On reads old_value = value makes the chains coincide, so
                // new_root = root is forced transitively.)
                builder.assert_zero(is_real.clone() * (cur_old - local[MAP_ROOT].into()));
                builder.assert_zero(is_real.clone() * (cur_new - local[MAP_NEW_ROOT].into()));

                // The table carries EXACTLY the gathered log (mapTableFaithful).
                let map_log = PermutationCheckBus::new(BUS_MAP_LOG);
                map_log.receive(
                    builder,
                    [
                        local[MAP_ROOT].into(),
                        local[MAP_KEY].into(),
                        local[MAP_VALUE].into(),
                        local[MAP_OP].into(),
                        local[MAP_NEW_ROOT].into(),
                    ],
                    is_real,
                );
            }
        }
    }
}

// ============================================================================
// Witness generation (the restructure: chip rows + lookup tuples from hash sites,
// memory rows from state accesses, map-op rows from boundary reconciliations)
// ============================================================================

/// Concrete evaluation of a `LeanExpr` over one main row.
fn eval_c(e: &LeanExpr, row: &[BabyBear]) -> BabyBear {
    match e {
        LeanExpr::Var(i) => row[*i],
        LeanExpr::Const(c) => i64_to_babybear(*c),
        LeanExpr::Add(a, b) => eval_c(a, row) + eval_c(b, row),
        LeanExpr::Mul(a, b) => eval_c(a, row) * eval_c(b, row),
    }
}

/// Concrete permutation: full aux block + the squeezed digest (`state[0]` of the last round).
fn perm_aux(st: [BabyBear; POSEIDON2_WIDTH]) -> (Vec<BabyBear>, BabyBear) {
    let aux = poseidon2_permute_aux_witness(st);
    let digest = aux[aux.len() - POSEIDON2_WIDTH];
    (aux, digest)
}

fn hash2_state_c(a: BabyBear, b: BabyBear) -> [BabyBear; POSEIDON2_WIDTH] {
    let mut st = [BabyBear::ZERO; POSEIDON2_WIDTH];
    st[0] = a;
    st[1] = b;
    st[4] = BabyBear::new(2);
    st
}

fn fact_state_c(l: BabyBear, r: BabyBear) -> [BabyBear; POSEIDON2_WIDTH] {
    let mut st = [BabyBear::ZERO; POSEIDON2_WIDTH];
    st[0] = l;
    st[1] = r;
    st[5] = BabyBear::new(FACT_MARK);
    st[6] = BabyBear::ONE;
    st
}

/// Fill one `bits`-wide decomposition (limbs + top bits) of `val`, counting the byte-bus
/// queries into `hist`. `val` must already be `< 2^bits`.
fn fill_decomp(val: u32, bits: usize, out: &mut Vec<BabyBear>, hist: &mut [u64; 256]) {
    let (n, top_bits) = limb_geom(bits);
    let partial = top_bits < LIMB_BITS;
    for i in 0..n {
        let byte = ((val >> (i * LIMB_BITS)) & 0xff) as u32;
        out.push(BabyBear::new(byte));
        if !(i == n - 1 && partial) {
            hist[byte as usize] += 1;
        }
    }
    if partial {
        let top = (val >> ((n - 1) * LIMB_BITS)) & 0xff;
        for b in 0..top_bits {
            out.push(BabyBear::new((top >> b) & 1));
        }
    }
}

fn next_pow2(n: usize) -> usize {
    n.next_power_of_two().max(MIN_TABLE_HEIGHT)
}

fn to_matrix(rows: &[Vec<BabyBear>]) -> RowMajorMatrix<P3BabyBear> {
    let width = rows[0].len();
    let values: Vec<P3BabyBear> = rows
        .iter()
        .flat_map(|row| row.iter().map(|&v| to_p3(v)))
        .collect();
    RowMajorMatrix::new(values, width)
}

/// The witness-supplied memory boundary: the declared address list (STRICTLY increasing,
/// each `< 2^30`) and the initial image over it. The final image is computed by replaying
/// the gathered log. Lean's `(minit, mfin, maddrs)` triple.
#[derive(Clone, Debug, Default)]
pub struct MemBoundaryWitness {
    /// Declared addresses, strictly increasing.
    pub addrs: Vec<u32>,
    /// Initial value per declared address (same length as `addrs`).
    pub init_vals: Vec<u32>,
}

/// One fully assembled multi-table witness (the six instance traces, in instance order).
struct Ir2Traces {
    main: Vec<Vec<BabyBear>>,
    chip: Vec<Vec<BabyBear>>,
    byte: Vec<Vec<BabyBear>>,
    memory: Vec<Vec<BabyBear>>,
    boundary: Vec<Vec<BabyBear>>,
    map_ops: Vec<Vec<BabyBear>>,
}

/// Build a fully padded map-ops row (main columns given; aux blocks computed concretely,
/// valid for pad rows too — every permutation block is genuine on any column values).
fn map_row_with_aux(main_cols: &[BabyBear]) -> Vec<BabyBear> {
    let mut row = main_cols.to_vec();
    debug_assert_eq!(row.len(), MAP_AUX0);
    let key = row[MAP_KEY];
    let value = row[MAP_VALUE];
    let old_value = row[MAP_OLD_VALUE];
    let (aux_old_leaf, mut cur_old) = perm_aux(hash2_state_c(key, old_value));
    let (aux_new_leaf, mut cur_new) = perm_aux(hash2_state_c(key, value));
    let mut chain_old_aux: Vec<BabyBear> = Vec::new();
    let mut chain_new_aux: Vec<BabyBear> = Vec::new();
    for lvl in 0..HEAP_TREE_DEPTH {
        let sib = row[MAP_SIB0 + lvl];
        let dir = row[MAP_DIR0 + lvl];
        let mix = |cur: BabyBear| -> (BabyBear, BabyBear) {
            if dir == BabyBear::ZERO {
                (cur, sib)
            } else {
                (sib, cur)
            }
        };
        let (lo, ro) = mix(cur_old);
        let (aux, d) = perm_aux(fact_state_c(lo, ro));
        chain_old_aux.extend(aux);
        cur_old = d;
        let (ln, rn) = mix(cur_new);
        let (aux, d) = perm_aux(fact_state_c(ln, rn));
        chain_new_aux.extend(aux);
        cur_new = d;
    }
    row.extend(aux_old_leaf);
    row.extend(aux_new_leaf);
    row.extend(chain_old_aux);
    row.extend(chain_new_aux);
    debug_assert_eq!(row.len(), MAP_WIDTH);
    row
}

/// Assemble all six instance traces from the base main trace + the boundary witness +
/// the map heaps. `check` controls the prover-side pre-flight replay (the test harness
/// disables it to exercise the in-circuit refusals).
#[allow(clippy::too_many_lines)]
fn build_traces(
    desc: &EffectVmDescriptor2,
    layout: &MainLayout,
    base_trace: &[Vec<BabyBear>],
    mem_boundary: &MemBoundaryWitness,
    map_heaps: &[Vec<HeapLeaf>],
    check: bool,
) -> Result<Ir2Traces, String> {
    let mut byte_hist = [0u64; 256];

    // ---- main: base wires + range limb blocks + submask bit blocks. ----
    let mut main: Vec<Vec<BabyBear>> = Vec::with_capacity(base_trace.len());
    for (ri, base_row) in base_trace.iter().enumerate() {
        let mut row = base_row.clone();
        for rb in &layout.ranges {
            let v = base_row[rb.wire].as_u32();
            if (v as u64) >= (1u64 << rb.bits) {
                return Err(format!(
                    "row {ri}: range wire {} value {v} >= 2^{}",
                    rb.wire, rb.bits
                ));
            }
            fill_decomp(v, rb.bits, &mut row, &mut byte_hist);
        }
        for sb in &layout.submasks {
            let keep = eval_c(&sb.keep, base_row).as_u32();
            let held = eval_c(&sb.held, base_row).as_u32();
            for v in [keep, held] {
                if (v as u64) >= (1u64 << SUBMASK_BITS) {
                    return Err(format!("row {ri}: submask operand {v} >= 2^{SUBMASK_BITS}"));
                }
            }
            if check && (keep & held) != keep {
                return Err(format!(
                    "row {ri}: submask violation: keep {keep:#x} ⊄ held {held:#x}"
                ));
            }
            for i in 0..SUBMASK_BITS {
                row.push(BabyBear::new((keep >> i) & 1));
            }
            for i in 0..SUBMASK_BITS {
                row.push(BabyBear::new((held >> i) & 1));
            }
        }
        debug_assert_eq!(row.len(), layout.width);
        main.push(row);
    }

    // ---- chip: histogram of every row's every chip-lookup tuple. ----
    let mut chip_hist: BTreeMap<Vec<u32>, u64> = BTreeMap::new();
    for base_row in base_trace {
        for k in &desc.constraints {
            if let VmConstraint2::Lookup(l) = k {
                if l.table == TID_P2 {
                    let tuple: Vec<u32> =
                        l.tuple.iter().map(|e| eval_c(e, base_row).as_u32()).collect();
                    *chip_hist.entry(tuple).or_insert(0) += 1;
                }
            }
        }
    }
    let mut chip: Vec<Vec<BabyBear>> = Vec::new();
    for (tuple, mult) in &chip_hist {
        let mut row: Vec<BabyBear> = tuple.iter().map(|&v| BabyBear::new(v)).collect();
        row.push(BabyBear::new((*mult % (BABYBEAR_P as u64)) as u32));
        let mut st = [BabyBear::ZERO; POSEIDON2_WIDTH];
        for i in 0..4 {
            st[i] = row[CHIP_IN0 + i];
        }
        st[4] = row[CHIP_ARITY];
        let (aux, _digest) = perm_aux(st);
        row.extend(aux);
        chip.push(row);
    }
    // Pad: genuine arity-0 permutation rows with multiplicity 0.
    {
        let (aux, digest) = perm_aux([BabyBear::ZERO; POSEIDON2_WIDTH]);
        let mut pad = vec![BabyBear::ZERO; CHIP_AUX0];
        pad[CHIP_OUT] = digest;
        pad.extend(aux);
        let target = next_pow2(chip.len());
        while chip.len() < target {
            chip.push(pad.clone());
        }
    }

    // ---- the memory log (per row, per declared mem op, guard = 1). ----
    let mut mem_log: Vec<[BabyBear; 5]> = Vec::new();
    for (ri, base_row) in base_trace.iter().enumerate() {
        for k in &desc.constraints {
            if let VmConstraint2::MemOp(m) = k {
                let g = eval_c(&m.guard, base_row);
                if g == BabyBear::ZERO {
                    continue;
                }
                if g != BabyBear::ONE {
                    return Err(format!("row {ri}: mem_op guard evaluates to {g:?}, not 0/1"));
                }
                mem_log.push([
                    eval_c(&m.addr, base_row),
                    eval_c(&m.value, base_row),
                    eval_c(&m.prev_value, base_row),
                    eval_c(&m.prev_serial, base_row),
                    BabyBear::new(m.kind.code()),
                ]);
            }
        }
    }

    // ---- memory table: log rows in order, positional serials, gap decomposition. ----
    let mem_height = next_pow2(mem_log.len());
    let mut memory: Vec<Vec<BabyBear>> = Vec::with_capacity(mem_height);
    for i in 0..mem_height {
        let serial = (i + 1) as u32;
        let mut row = vec![BabyBear::ZERO; MEM_ADDR];
        let (tuple, is_real): ([BabyBear; 5], bool) = if i < mem_log.len() {
            (mem_log[i], true)
        } else {
            ([BabyBear::ZERO; 5], false)
        };
        row.extend_from_slice(&tuple);
        row.push(BabyBear::new(serial));
        row.push(if is_real { BabyBear::ONE } else { BabyBear::ZERO });
        let gap = if is_real {
            let prev = tuple[3].as_u32();
            if prev >= serial {
                return Err(format!(
                    "memory op {i}: claimed prev serial {prev} not before own serial {serial}"
                ));
            }
            serial - 1 - prev
        } else {
            0
        };
        if (gap as u64) >= (1u64 << MEM_GAP_BITS) {
            return Err(format!("memory op {i}: serial gap {gap} >= 2^{MEM_GAP_BITS}"));
        }
        row.push(BabyBear::new(gap));
        fill_decomp(gap, MEM_GAP_BITS, &mut row, &mut byte_hist);
        debug_assert_eq!(row.len(), MEM_WIDTH);
        memory.push(row);
    }

    // ---- memory boundary: declared addrs (strictly increasing), replayed final image. ----
    if mem_boundary.addrs.len() != mem_boundary.init_vals.len() {
        return Err("mem boundary addrs/init_vals length mismatch".to_string());
    }
    for w in mem_boundary.addrs.windows(2) {
        if w[1] <= w[0] {
            return Err(format!(
                "mem boundary addresses must be strictly increasing ({} then {})",
                w[0], w[1]
            ));
        }
    }
    for &a in &mem_boundary.addrs {
        if (a as u64) >= (1u64 << MEM_GAP_BITS) {
            return Err(format!("mem boundary address {a} >= 2^{MEM_GAP_BITS}"));
        }
    }
    // Replay: image addr → (value, serial); count per-address op multiplicity.
    let mut image: BTreeMap<u32, (BabyBear, u32)> = mem_boundary
        .addrs
        .iter()
        .zip(&mem_boundary.init_vals)
        .map(|(&a, &v)| (a, (BabyBear::new(v), 0u32)))
        .collect();
    let mut addr_mult: BTreeMap<u32, u64> = BTreeMap::new();
    for (i, op) in mem_log.iter().enumerate() {
        let a = op[0].as_u32();
        let Some(&(cur_v, cur_s)) = image.get(&a) else {
            return Err(format!(
                "memory op {i} touches undeclared address {a} (memClosed)"
            ));
        };
        if check && (op[2] != cur_v || op[3].as_u32() != cur_s) {
            return Err(format!(
                "memory op {i} at addr {a}: claimed prev ({}, {}) != replayed ({}, {cur_s})",
                op[2].as_u32(),
                op[3].as_u32(),
                cur_v.as_u32(),
            ));
        }
        image.insert(a, (op[1], (i + 1) as u32));
        *addr_mult.entry(a).or_insert(0) += 1;
    }
    let mb_height = next_pow2(mem_boundary.addrs.len());
    let mut boundary: Vec<Vec<BabyBear>> = Vec::with_capacity(mb_height);
    for i in 0..mb_height {
        let mut row: Vec<BabyBear> = Vec::with_capacity(MB_WIDTH);
        let (addr, init_v, is_real) = if i < mem_boundary.addrs.len() {
            (
                mem_boundary.addrs[i],
                BabyBear::new(mem_boundary.init_vals[i]),
                true,
            )
        } else {
            (0, BabyBear::ZERO, false)
        };
        let (fin_v, fin_s) = if is_real {
            image[&addr]
        } else {
            (BabyBear::ZERO, 0)
        };
        row.push(BabyBear::new(addr));
        row.push(init_v);
        row.push(fin_v);
        row.push(BabyBear::new(fin_s));
        row.push(if is_real { BabyBear::ONE } else { BabyBear::ZERO });
        row.push(BabyBear::new(
            (*addr_mult.get(&addr).unwrap_or(&0) % (BABYBEAR_P as u64)) as u32
                * (is_real as u32),
        ));
        // agap: bound on real→real transitions; zero elsewhere.
        let agap = if i + 1 < mem_boundary.addrs.len() {
            mem_boundary.addrs[i + 1] - addr - 1
        } else {
            0
        };
        row.push(BabyBear::new(agap));
        fill_decomp(agap, MEM_GAP_BITS, &mut row, &mut byte_hist);
        // addr_chk = is_real·addr.
        let achk = if is_real { addr } else { 0 };
        row.push(BabyBear::new(achk));
        fill_decomp(achk, MEM_GAP_BITS, &mut row, &mut byte_hist);
        debug_assert_eq!(row.len(), MB_WIDTH);
        boundary.push(row);
    }

    // ---- the map-ops log + the opening witnesses. ----
    let mut map_log: Vec<([BabyBear; 5], MapKind)> = Vec::new();
    for (ri, base_row) in base_trace.iter().enumerate() {
        for k in &desc.constraints {
            if let VmConstraint2::MapOp(m) = k {
                let g = eval_c(&m.guard, base_row);
                if g == BabyBear::ZERO {
                    continue;
                }
                if g != BabyBear::ONE {
                    return Err(format!("row {ri}: map_op guard evaluates to {g:?}, not 0/1"));
                }
                map_log.push((
                    [
                        eval_c(&m.root, base_row),
                        eval_c(&m.key, base_row),
                        eval_c(&m.value, base_row),
                        BabyBear::new(m.op.code()),
                        eval_c(&m.new_root, base_row),
                    ],
                    m.op,
                ));
            }
        }
    }
    let mut trees: Vec<CanonicalHeapTree> = map_heaps
        .iter()
        .map(|leaves| CanonicalHeapTree::new(leaves.clone(), HEAP_TREE_DEPTH))
        .collect();
    let map_height = next_pow2(map_log.len());
    let mut map_ops: Vec<Vec<BabyBear>> = Vec::with_capacity(map_height);
    for (i, (tuple, kind)) in map_log.iter().enumerate() {
        let [root, key, value, _opc, new_root] = *tuple;
        let tree = trees
            .iter()
            .find(|t| t.root() == root)
            .cloned()
            .ok_or_else(|| format!("map op {i}: no witness heap with root {}", root.as_u32()))?;
        let (old_value, sibs, dirs) = match kind {
            MapKind::Read => {
                let pos = tree.position_of(key).ok_or_else(|| {
                    format!("map op {i}: read key {} not in heap", key.as_u32())
                })?;
                let leaf = tree.sorted_leaves()[pos];
                if check && leaf.value != value {
                    return Err(format!(
                        "map op {i}: read at key {} opens to {}, row claims {}",
                        key.as_u32(),
                        leaf.value.as_u32(),
                        value.as_u32()
                    ));
                }
                if check && new_root != root {
                    return Err(format!("map op {i}: read must preserve the root"));
                }
                let (sibs, dirs) = tree
                    .prove_membership(pos)
                    .ok_or_else(|| format!("map op {i}: membership path failed"))?;
                (value, sibs, dirs)
            }
            MapKind::Write => {
                let w = tree
                    .update_witness(HeapLeaf { addr: key, value })
                    .ok_or_else(|| {
                        format!(
                            "map op {i}: write key {} not present — a fresh-key sorted INSERT \
                             is the named follow-up lane (only in-place updates are realized)",
                            key.as_u32()
                        )
                    })?;
                if check && w.new_root != new_root {
                    return Err(format!(
                        "map op {i}: claimed new_root {} != genuine sorted write {}",
                        new_root.as_u32(),
                        w.new_root.as_u32()
                    ));
                }
                // Advance the working set: the post-write heap is reachable for later ops.
                let new_leaves: Vec<HeapLeaf> = tree
                    .sorted_leaves()
                    .iter()
                    .map(|l| {
                        if l.addr == key {
                            HeapLeaf { addr: key, value }
                        } else {
                            *l
                        }
                    })
                    .collect();
                trees.push(CanonicalHeapTree::new(new_leaves, HEAP_TREE_DEPTH));
                (w.old_leaf.value, w.siblings, w.directions)
            }
            MapKind::Absent => unreachable!("absent refused by check_descriptor2"),
        };
        let mut cols = vec![BabyBear::ZERO; MAP_AUX0];
        cols[MAP_ROOT] = root;
        cols[MAP_KEY] = key;
        cols[MAP_VALUE] = value;
        cols[MAP_OP] = BabyBear::new(kind.code());
        cols[MAP_NEW_ROOT] = new_root;
        cols[MAP_IS_REAL] = BabyBear::ONE;
        cols[MAP_OLD_VALUE] = old_value;
        for lvl in 0..HEAP_TREE_DEPTH {
            cols[MAP_SIB0 + lvl] = sibs[lvl];
            cols[MAP_DIR0 + lvl] = BabyBear::new(dirs[lvl] as u32);
        }
        map_ops.push(map_row_with_aux(&cols));
    }
    while map_ops.len() < map_height {
        map_ops.push(map_row_with_aux(&vec![BabyBear::ZERO; MAP_AUX0]));
    }

    // ---- the byte table (height pinned at 256). ----
    let byte: Vec<Vec<BabyBear>> = (0..BYTE_TABLE_HEIGHT)
        .map(|b| {
            vec![
                BabyBear::new(b as u32),
                BabyBear::new((byte_hist[b] % (BABYBEAR_P as u64)) as u32),
            ]
        })
        .collect();

    Ok(Ir2Traces {
        main,
        chip,
        byte,
        memory,
        boundary,
        map_ops,
    })
}

/// The six instance AIRs for a checked descriptor, in instance order
/// (main, chip, byte, memory, boundary, map-ops).
fn instance_airs(desc: &EffectVmDescriptor2, layout: MainLayout) -> Vec<Ir2Air> {
    vec![
        Ir2Air::Main {
            desc: desc.clone(),
            layout: MainLayoutPub(layout),
        },
        Ir2Air::Chip,
        Ir2Air::ByteTable,
        Ir2Air::Memory,
        Ir2Air::MemBoundary,
        Ir2Air::MapOps,
    ]
}

fn prove_vm_descriptor2_inner(
    desc: &EffectVmDescriptor2,
    base_trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    mem_boundary: &MemBoundaryWitness,
    map_heaps: &[Vec<HeapLeaf>],
    check: bool,
) -> Result<BatchProof<DreggStarkConfig>, String> {
    let layout = check_descriptor2(desc)?;
    if base_trace.is_empty() {
        return Err("base trace must be non-empty".to_string());
    }
    if !base_trace.len().is_power_of_two() {
        return Err(format!(
            "base trace height {} must be a power of two",
            base_trace.len()
        ));
    }
    if base_trace[0].len() != desc.trace_width {
        return Err(format!(
            "base row width {} must equal descriptor trace_width {}",
            base_trace[0].len(),
            desc.trace_width
        ));
    }
    if public_inputs.len() != desc.public_input_count {
        return Err(format!(
            "public input count {} != descriptor public_input_count {}",
            public_inputs.len(),
            desc.public_input_count
        ));
    }

    let traces = build_traces(desc, &layout, base_trace, mem_boundary, map_heaps, check)?;
    let airs = instance_airs(desc, layout);

    let matrices = [
        to_matrix(&traces.main),
        to_matrix(&traces.chip),
        to_matrix(&traces.byte),
        to_matrix(&traces.memory),
        to_matrix(&traces.boundary),
        to_matrix(&traces.map_ops),
    ];
    let pis: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
    let pvs: Vec<Vec<P3BabyBear>> = vec![pis, vec![], vec![], vec![], vec![], vec![]];

    let config = create_config();
    let instances: Vec<StarkInstance<'_, DreggStarkConfig, Ir2Air>> = airs
        .iter()
        .zip(matrices.iter())
        .zip(pvs.iter())
        .map(|((air, trace), pv)| StarkInstance {
            air,
            trace,
            public_values: pv.clone(),
        })
        .collect();

    let prover_data = ProverData::from_instances(&config, &instances);
    let common = &prover_data.common;
    let proof = prove_batch(&config, &instances, &prover_data);

    verify_batch(&config, &airs, &proof, &pvs, common)
        .map_err(|e| format!("IR v2 batch self-verify failed: {e:?}"))?;
    Ok(proof)
}

/// **`prove_vm_descriptor2`** — assemble + prove the multi-table batch STARK for a
/// graduated v2 descriptor over a base main trace.
///
/// * `base_trace` — the `trace_width`-column main rows (power-of-two height); digest
///   columns must already carry the genuine values (the Lean executor witness fills them).
/// * `mem_boundary` — the declared memory addresses + initial image (empty when the
///   descriptor declares no mem ops).
/// * `map_heaps` — one leaf set per pre-state heap the map ops open (empty when none).
///
/// The proof self-verifies before return. A witness violating any descriptor relation —
/// a tampered memory read, a forged map opening, an out-of-range limb, an amplified
/// submask — has no satisfying assembly (the pre-flight replay refuses it eagerly; with
/// the replay bypassed the batch prover/verifier rejects).
pub fn prove_vm_descriptor2(
    desc: &EffectVmDescriptor2,
    base_trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    mem_boundary: &MemBoundaryWitness,
    map_heaps: &[Vec<HeapLeaf>],
) -> Result<BatchProof<DreggStarkConfig>, String> {
    prove_vm_descriptor2_inner(desc, base_trace, public_inputs, mem_boundary, map_heaps, true)
}

/// **`verify_vm_descriptor2`** — verify an IR v2 batch proof against the descriptor
/// (the AIRs are rebuilt from the descriptor alone; heights come from the proof).
pub fn verify_vm_descriptor2(
    desc: &EffectVmDescriptor2,
    proof: &BatchProof<DreggStarkConfig>,
    public_inputs: &[BabyBear],
) -> Result<(), String> {
    let layout = check_descriptor2(desc)?;
    let airs = instance_airs(desc, layout);
    let config = create_config();
    let pis: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
    let pvs: Vec<Vec<P3BabyBear>> = vec![pis, vec![], vec![], vec![], vec![], vec![]];
    let common = ProverData::from_airs_and_degrees(&config, &airs, &proof.degree_bits).common;
    verify_batch(&config, &airs, proof, &pvs, &common)
        .map_err(|e| format!("IR v2 verification failed: {e:?}"))
}

// ============================================================================
// Tests (run on persvati with the batched validation, not by the build lane)
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::poseidon2::hash_many;

    /// The Lean `#guard`-pinned demo-v2 golden (DescriptorIR2 §10): every v2 constraint
    /// kind + the five tables, byte-for-byte.
    const DEMO_V2: &str = "{\"name\":\"demo-v2\",\"ir\":2,\"trace_width\":2,\"public_input_count\":1,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":2,\"sem\":\"main\"},{\"id\":1,\"name\":\"poseidon2_chip\",\"arity\":10,\"sem\":\"poseidon2_chip\",\"params\":{\"field_modulus\":2013265921,\"d\":4,\"width\":16,\"sbox_degree\":7,\"sbox_registers\":1,\"half_full_rounds\":4,\"partial_rounds\":13,\"rate\":8,\"rc_source\":\"BABYBEAR_POSEIDON2_RC_16\",\"internal_diag_source\":\"BABYBEAR_POSEIDON2_INTERNAL_DIAG_16\"}},{\"id\":2,\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":30},{\"id\":3,\"name\":\"memory\",\"arity\":5,\"sem\":\"memory\"},{\"id\":4,\"name\":\"map_ops\",\"arity\":5,\"sem\":\"map_ops\"}],\"constraints\":[{\"t\":\"transition\",\"hi\":0,\"lo\":0},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":0}]},{\"t\":\"mem_op\",\"kind\":\"read\",\"guard\":{\"t\":\"const\",\"v\":1},\"addr\":{\"t\":\"var\",\"v\":0},\"value\":{\"t\":\"var\",\"v\":1},\"prev_value\":{\"t\":\"var\",\"v\":1},\"prev_serial\":{\"t\":\"const\",\"v\":0}},{\"t\":\"map_op\",\"op\":\"write\",\"guard\":{\"t\":\"const\",\"v\":1},\"root\":{\"t\":\"var\",\"v\":0},\"key\":{\"t\":\"var\",\"v\":1},\"value\":{\"t\":\"const\",\"v\":0},\"new_root\":{\"t\":\"var\",\"v\":1}}],\"hash_sites\":[],\"ranges\":[]}";

    /// The byte-pinned Lean golden parses, with every v2 element decoded.
    #[test]
    fn parses_lean_golden() {
        let d = parse_vm_descriptor2(DEMO_V2).expect("golden must parse");
        assert_eq!(d.name, "demo-v2");
        assert_eq!(d.trace_width, 2);
        assert_eq!(d.public_input_count, 1);
        assert_eq!(d.tables.len(), 5);
        assert_eq!(d.tables[2].sem, TableSem::Range { bits: 30 });
        assert_eq!(d.constraints.len(), 4);
        assert!(matches!(d.constraints[0], VmConstraint2::Base(_)));
        assert!(matches!(
            d.constraints[1],
            VmConstraint2::Lookup(LookupSpec { table: TID_RANGE, .. })
        ));
        assert!(matches!(
            d.constraints[2],
            VmConstraint2::MemOp(MemOpSpec { kind: MemKind::Read, .. })
        ));
        assert!(matches!(
            d.constraints[3],
            VmConstraint2::MapOp(MapOpSpec { op: MapKind::Write, .. })
        ));
    }

    /// A v1 wire string (no "ir") dispatches to the V1 arm unchanged.
    #[test]
    fn dispatches_v1() {
        let v1 = "{\"name\":\"t\",\"trace_width\":2,\"public_input_count\":0,\"constraints\":[{\"t\":\"transition\",\"hi\":0,\"lo\":0}],\"hash_sites\":[],\"ranges\":[]}";
        match parse_vm_descriptor_any(v1).expect("v1 must parse") {
            AnyVmDescriptor::V1(d) => assert_eq!(d.name, "t"),
            AnyVmDescriptor::V2(_) => panic!("v1 wire must dispatch V1"),
        }
    }

    /// Tampered chip params (wrong partial_rounds) are REFUSED at parse.
    #[test]
    fn refuses_tampered_chip_params() {
        let bad = DEMO_V2.replace("\"partial_rounds\":13", "\"partial_rounds\":12");
        assert!(parse_vm_descriptor2(&bad).is_err());
    }

    // ---- the end-to-end gauntlet descriptors ----

    /// Base layout for the test descriptor: cols 0 a, 1 b, 2 digest of hash[a,b],
    /// 3 a 30-bit balance wire, 4 mem addr, 5 mem value, 6 mem prev_value,
    /// 7 mem prev_serial, 8 mem guard, 9 map root, 10 map key, 11 map value,
    /// 12 map new_root, 13 map guard, 14 keep mask, 15 held mask.
    fn test_desc() -> EffectVmDescriptor2 {
        let chip_tuple = |a: usize, b: usize, d: usize| -> Vec<LeanExpr> {
            let mut t = vec![LeanExpr::Const(2), LeanExpr::Var(a), LeanExpr::Var(b)];
            for _ in 0..(CHIP_RATE - 2) {
                t.push(LeanExpr::Const(0));
            }
            t.push(LeanExpr::Var(d));
            t
        };
        EffectVmDescriptor2 {
            name: "ir2-test".to_string(),
            trace_width: 16,
            public_input_count: 0,
            tables: vec![TableDef2 {
                id: TID_RANGE,
                name: "range".to_string(),
                arity: 1,
                sem: TableSem::Range { bits: 30 },
            }],
            constraints: vec![
                VmConstraint2::Lookup(LookupSpec {
                    table: TID_P2,
                    tuple: chip_tuple(0, 1, 2),
                }),
                VmConstraint2::Lookup(LookupSpec {
                    table: TID_RANGE,
                    tuple: vec![LeanExpr::Var(3)],
                }),
                VmConstraint2::MemOp(MemOpSpec {
                    guard: LeanExpr::Var(8),
                    addr: LeanExpr::Var(4),
                    value: LeanExpr::Var(5),
                    prev_value: LeanExpr::Var(6),
                    prev_serial: LeanExpr::Var(7),
                    kind: MemKind::Read,
                }),
                VmConstraint2::MapOp(MapOpSpec {
                    guard: LeanExpr::Var(13),
                    root: LeanExpr::Var(9),
                    key: LeanExpr::Var(10),
                    value: LeanExpr::Var(11),
                    new_root: LeanExpr::Var(12),
                    op: MapKind::Read,
                }),
                VmConstraint2::Lookup(LookupSpec {
                    table: TID_CUSTOM_SUBMASK,
                    tuple: vec![LeanExpr::Var(14), LeanExpr::Var(15)],
                }),
            ],
            hash_sites: vec![],
            ranges: vec![],
        }
    }

    fn test_heap() -> Vec<HeapLeaf> {
        vec![
            HeapLeaf {
                addr: BabyBear::new(100),
                value: BabyBear::new(77),
            },
            HeapLeaf {
                addr: BabyBear::new(200),
                value: BabyBear::new(88),
            },
        ]
    }

    fn test_base_row() -> Vec<BabyBear> {
        let a = BabyBear::new(11);
        let b = BabyBear::new(22);
        let digest = hash_many(&[a, b]);
        let tree = CanonicalHeapTree::new(test_heap(), HEAP_TREE_DEPTH);
        let root = tree.root();
        vec![
            a,
            b,
            digest,
            BabyBear::new((1 << 30) - 1), // max in-range balance
            BabyBear::new(5),             // mem addr
            BabyBear::new(9),             // mem value (read returns init)
            BabyBear::new(9),             // mem prev_value
            BabyBear::ZERO,               // mem prev_serial (init)
            BabyBear::ZERO,               // mem guard (row 0 active only — set per row)
            root,                         // map root
            BabyBear::new(100),           // map key
            BabyBear::new(77),            // map value
            root,                         // map new_root (read preserves)
            BabyBear::ZERO,               // map guard (set per row)
            BabyBear::new(0b0101),        // keep ⊑ held
            BabyBear::new(0b0111),        // held
        ]
    }

    fn test_trace() -> Vec<Vec<BabyBear>> {
        // 4 rows; the mem/map ops fire on row 0 only.
        let mut rows = vec![test_base_row(); 4];
        rows[0][8] = BabyBear::ONE;
        rows[0][13] = BabyBear::ONE;
        // Rows 1..: prev_serial would still be 0 if the op fired again — guards are 0,
        // so the columns are inert there.
        rows
    }

    fn test_boundary() -> MemBoundaryWitness {
        MemBoundaryWitness {
            addrs: vec![5],
            init_vals: vec![9],
        }
    }

    /// THE acceptance gate: an honest multi-table witness (chip lookup + range lookup +
    /// memory read + map read + submask) proves and verifies through the real batch
    /// prover with LogUp.
    #[test]
    fn ir2_honest_witness_proves_and_verifies() {
        let desc = test_desc();
        let proof = prove_vm_descriptor2(
            &desc,
            &test_trace(),
            &[],
            &test_boundary(),
            &[test_heap()],
        )
        .expect("honest IR v2 witness must prove");
        verify_vm_descriptor2(&desc, &proof, &[]).expect("honest IR v2 proof must verify");
    }

    /// A tampered memory READ (claims value 7 where the init image holds 9) must REFUSE:
    /// the pre-flight replay rejects it, and with the replay bypassed the in-circuit
    /// multiset argument has no balancing assembly (debug prover panics / proof fails
    /// verification).
    #[test]
    fn ir2_tampered_read_refuses() {
        let desc = test_desc();
        let mut rows = test_trace();
        rows[0][5] = BabyBear::new(7); // value
        rows[0][6] = BabyBear::new(7); // prev_value (read discipline forces equality)
        // Pre-flight replay refuses.
        assert!(
            prove_vm_descriptor2(&desc, &rows, &[], &test_boundary(), &[test_heap()]).is_err()
        );
        // In-circuit tooth: bypass the replay; the mem_check bus cannot balance.
        let r = std::panic::catch_unwind(|| {
            prove_vm_descriptor2_inner(
                &desc,
                &rows,
                &[],
                &test_boundary(),
                &[test_heap()],
                false,
            )
        });
        match r {
            Err(_) => {} // debug prover panicked on the unbalanced bus — refused
            Ok(res) => assert!(
                res.is_err(),
                "tampered memory read produced an accepted proof — Blum tooth OPEN"
            ),
        }
    }

    /// A forged map READ (claims value 78 at key 100 where the committed heap holds 77)
    /// must refuse the same way.
    #[test]
    fn ir2_forged_map_opening_refuses() {
        let desc = test_desc();
        let mut rows = test_trace();
        rows[0][11] = BabyBear::new(78);
        assert!(
            prove_vm_descriptor2(&desc, &rows, &[], &test_boundary(), &[test_heap()]).is_err()
        );
        let r = std::panic::catch_unwind(|| {
            prove_vm_descriptor2_inner(
                &desc,
                &rows,
                &[],
                &test_boundary(),
                &[test_heap()],
                false,
            )
        });
        match r {
            Err(_) => {}
            Ok(res) => assert!(
                res.is_err(),
                "forged map opening produced an accepted proof — opening tooth OPEN"
            ),
        }
    }

    /// An amplified submask (keep ⋢ held) must refuse.
    #[test]
    fn ir2_amplified_submask_refuses() {
        let desc = test_desc();
        let mut rows = test_trace();
        for row in &mut rows {
            row[14] = BabyBear::new(0b1000); // keep has a bit held lacks
        }
        assert!(
            prove_vm_descriptor2(&desc, &rows, &[], &test_boundary(), &[test_heap()]).is_err()
        );
        let r = std::panic::catch_unwind(|| {
            prove_vm_descriptor2_inner(
                &desc,
                &rows,
                &[],
                &test_boundary(),
                &[test_heap()],
                false,
            )
        });
        match r {
            Err(_) => {}
            Ok(res) => assert!(
                res.is_err(),
                "amplified submask produced an accepted proof — non-amp tooth OPEN"
            ),
        }
    }

    /// A forged hash digest (column 2 ≠ hash[a,b]) must refuse: the chip table only
    /// carries genuine permutation rows, so the lookup cannot be served.
    #[test]
    fn ir2_forged_digest_refuses() {
        let desc = test_desc();
        let mut rows = test_trace();
        for row in &mut rows {
            row[2] = row[2] + BabyBear::ONE;
        }
        // The chip table gathers the (forged) tuple and binds its own output column to
        // the REAL permutation — prover cannot satisfy both.
        let r = std::panic::catch_unwind(|| {
            prove_vm_descriptor2(&desc, &rows, &[], &test_boundary(), &[test_heap()])
        });
        match r {
            Err(_) => {}
            Ok(res) => assert!(
                res.is_err(),
                "forged digest produced an accepted proof — chip tooth OPEN"
            ),
        }
    }

    /// An out-of-range balance wire (2^30) must refuse (the tight top-limb bound).
    #[test]
    fn ir2_out_of_range_refuses() {
        let desc = test_desc();
        let mut rows = test_trace();
        for row in &mut rows {
            row[3] = BabyBear::new(1 << 30);
        }
        assert!(
            prove_vm_descriptor2(&desc, &rows, &[], &test_boundary(), &[test_heap()]).is_err()
        );
    }

    /// A map WRITE (in-place update at an existing key) proves: the new root is the
    /// genuine sorted write, chained so a later read against the NEW root sees it.
    #[test]
    fn ir2_map_write_update_proves() {
        let tree = CanonicalHeapTree::new(test_heap(), HEAP_TREE_DEPTH);
        let root = tree.root();
        let w = tree
            .update_witness(HeapLeaf {
                addr: BabyBear::new(100),
                value: BabyBear::new(99),
            })
            .expect("key 100 present");
        let desc = EffectVmDescriptor2 {
            name: "ir2-map-write".to_string(),
            trace_width: 6,
            public_input_count: 0,
            tables: vec![],
            constraints: vec![VmConstraint2::MapOp(MapOpSpec {
                guard: LeanExpr::Var(5),
                root: LeanExpr::Var(0),
                key: LeanExpr::Var(1),
                value: LeanExpr::Var(2),
                new_root: LeanExpr::Var(3),
                op: MapKind::Write,
            })],
            hash_sites: vec![],
            ranges: vec![],
        };
        let mut rows = vec![
            vec![
                root,
                BabyBear::new(100),
                BabyBear::new(99),
                w.new_root,
                BabyBear::ZERO,
                BabyBear::ZERO,
            ];
            4
        ];
        rows[0][5] = BabyBear::ONE;
        let proof = prove_vm_descriptor2(
            &desc,
            &rows,
            &[],
            &MemBoundaryWitness::default(),
            &[test_heap()],
        )
        .expect("map write update must prove");
        verify_vm_descriptor2(&desc, &proof, &[]).expect("map write proof must verify");
    }
}
