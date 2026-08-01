//! # `table_air` — the decoder for a Lean-authored TABLE AIR.
//!
//! ## What was missing
//!
//! IR-v2 emits the MAIN instance: an [`crate::descriptor_ir2::EffectVmDescriptor2`] carries one
//! effect's own row algebra and `Ir2Air::Main` interprets it. The other instances the deployed
//! prover assembles — the Poseidon2 chip, the byte table, the memory pair, the map-ops pair, the
//! universal-memory pair — are a SECOND kind of AIR: a shared auxiliary table with its own width,
//! its own column space, and its own bus interactions. IR-v2 had no vocabulary for that object, so
//! all of them were hand-authored Rust algebra, in direct violation of architectural law #1
//! (*"circuits are emitted from Lean; Rust only INTERPRETS"*).
//!
//! This module is the interpreter for the vocabulary. The Lean author is
//! `Dregg2/Circuit/TableAirIR.lean`; the per-table emitters are `Dregg2/Circuit/Emit/*TableEmit.lean`
//! and their emissions are `circuit/descriptors/table-airs/*.json`. **Nothing in this file authors a
//! constraint**: it decodes a wire object whose `gates` are [`WindowExpr`] trees under a [`RowSel`],
//! and whose `interactions` name a bus, a call shape, a multiplicity expression and a tuple.
//! `Ir2Air::LeanTable` walks that and calls `assert_zero` / `lookup_key` / `table_entry` /
//! `receive` / `send` on exactly what it says.
//!
//! ## The two fields a descriptor `Lookup`/`Gate` could not carry
//!
//! **The multiplicity expression.** `Ir2Air::Main` hardcodes multiplicity `1` on every declared
//! lookup, because a main row is unconditionally real. A shared table is PADDED — the map-absent
//! table's chip absorbs ride at multiplicity `is_real`, so a pad row must send ZERO queries or the
//! LogUp balance is wrong — so a table IR without a per-row multiplicity expression cannot express
//! the deployed AIR at all. That is why [`TableInteraction`] exists rather than reusing `Lookup`.
//!
//! **The row selector.** ⚑ This is what blocked every table but map-absent, and it is new in the
//! second pass. The map-absent table is the ONLY purely row-local one; every other shared table is
//! a SORTED or COUNTED table whose content is a relation between ADJACENT rows, asserted under a
//! p3 row filter. [`TableGate`] carries that filter and [`WindowExpr::Nxt`] reads the next row.
//!
//! ⚠ Bus interactions carry NO selector, deliberately: every deployed table pushes its
//! interactions on the unfiltered builder (a filtered p3 builder is not an `InteractionBuilder`),
//! and the padding discipline rides in the multiplicity expression instead.
//!
//! ## Column space
//!
//! `WindowExpr::Loc(c)` / `Nxt(c)` here read column `c` of **this table's** current / next row, not
//! the main trace's. That is the whole "sub-descriptor at a column offset" content, and it is why
//! this is a separate `Ir2Air` arm rather than a splice into the main constraint walk.

use std::sync::{Arc, OnceLock};

use crate::descriptor_ir2::WindowExpr;
use crate::lean_descriptor_air::JsonCursor;

/// The bus call shape (Lean `TableAirIR.BusOp`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BusOp {
    /// `LookupBus::lookup_key` — a subset query against a served table.
    Query,
    /// `LookupBus::table_entry` — this table SERVES the entry (p3 `count_weight = 0`).
    Provide,
    /// `PermutationCheckBus::receive` — a positive multiset contribution.
    Receive,
    /// `PermutationCheckBus::send` — a negative multiset contribution.
    Send,
}

impl BusOp {
    /// The stable wire tag (Lean `BusOp.tag`).
    pub fn tag(self) -> &'static str {
        match self {
            BusOp::Query => "query",
            BusOp::Provide => "provide",
            BusOp::Receive => "receive",
            BusOp::Send => "send",
        }
    }

    fn from_tag(t: &str) -> Result<Self, String> {
        match t {
            "query" => Ok(BusOp::Query),
            "provide" => Ok(BusOp::Provide),
            "receive" => Ok(BusOp::Receive),
            "send" => Ok(BusOp::Send),
            other => Err(format!("unknown bus op \"{other}\"")),
        }
    }
}

/// The p3 row filter a gate is asserted under (Lean `TableAirIR.RowSel`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RowSel {
    /// Unfiltered `builder.assert_zero` — every row, wrap row included.
    All,
    /// `builder.when_first_row()`.
    First,
    /// `builder.when_last_row()`.
    Last,
    /// `builder.when_transition()` — every row but the last; the only scope where `Nxt` is the
    /// genuine successor rather than the wrap row.
    Transition,
}

impl RowSel {
    /// The stable wire tag (Lean `RowSel.tag`).
    pub fn tag(self) -> &'static str {
        match self {
            RowSel::All => "all",
            RowSel::First => "first",
            RowSel::Last => "last",
            RowSel::Transition => "transition",
        }
    }

    fn from_tag(t: &str) -> Result<Self, String> {
        match t {
            "all" => Ok(RowSel::All),
            "first" => Ok(RowSel::First),
            "last" => Ok(RowSel::Last),
            "transition" => Ok(RowSel::Transition),
            other => Err(format!("unknown row selector \"{other}\"")),
        }
    }
}

/// One gate of a table AIR (Lean `TableAirIR.TableGate`): a two-row polynomial and the row filter
/// it is asserted under.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TableGate {
    /// The row filter.
    pub sel: RowSel,
    /// The two-row polynomial body, which must VANISH on every row the filter admits.
    pub body: WindowExpr,
}

/// One bus interaction of a table AIR (Lean `TableAirIR.BusInteraction`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TableInteraction {
    /// The bus name — matches the `BUS_*` string constants in `descriptor_ir2`.
    pub bus: String,
    /// The call shape.
    pub op: BusOp,
    /// Per-row multiplicity. `Const(1)` is the unconditional case.
    pub mult: WindowExpr,
    /// The tuple placed on the bus.
    pub tuple: Vec<WindowExpr>,
}

/// A table AIR, authored in Lean and decoded here (Lean `TableAirIR.TableAir`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeanTableAir {
    /// The emitted name (the artifact's identity).
    pub name: String,
    /// This table's own column count.
    pub width: usize,
    /// Row-filtered gates: each must VANISH on every row its selector admits.
    pub gates: Vec<TableGate>,
    /// The declared bus interactions.
    pub interactions: Vec<TableInteraction>,
}

impl LeanTableAir {
    /// The maximum polynomial degree over all gates and all multiplicity-weighted tuples — what
    /// the batch assembly needs to size the quotient.
    ///
    /// ⚠ A row-filtered gate costs ONE MORE than its body: p3's `FilteredAirBuilder::assert_zero`
    /// multiplies by the selector, and so does this module's interpreter. Counting the body alone
    /// would under-report the deployed degree of every `.first`/`.last`/`.transition` gate.
    pub fn max_degree(&self) -> usize {
        let gate_deg = self
            .gates
            .iter()
            .map(|g| g.body.degree() + usize::from(!matches!(g.sel, RowSel::All)))
            .max()
            .unwrap_or(0);
        let bus_deg = self
            .interactions
            .iter()
            .map(|i| {
                let m = i.mult.degree();
                m + i.tuple.iter().map(WindowExpr::degree).max().unwrap_or(0)
            })
            .max()
            .unwrap_or(0);
        gate_deg.max(bus_deg)
    }

    /// How many interactions this table declares on a given bus. A re-emission that drops a bus
    /// leg moves this, which is what the shape pins in the cutover tests check.
    pub fn bus_count_on(&self, bus: &str) -> usize {
        self.interactions.iter().filter(|i| i.bus == bus).count()
    }

    /// How many interactions on a bus have a given call shape. `Query` vs `Provide` is the SIDE of
    /// a `LookupBus`; a count that reads only the bus cannot tell a server from a client.
    pub fn bus_count_op(&self, bus: &str, op: BusOp) -> usize {
        self.interactions
            .iter()
            .filter(|i| i.bus == bus && i.op == op)
            .count()
    }

    /// How many gates sit under a given selector.
    pub fn gate_count_sel(&self, sel: RowSel) -> usize {
        self.gates.iter().filter(|g| g.sel == sel).count()
    }

    /// Every column index the table reads must be inside its declared width, and a gate that reads
    /// the NEXT row must be `.transition`- or `.first`-scoped.
    ///
    /// The width half refuses an out-of-bounds index at decode time instead of panicking inside the
    /// `Air` evaluator. The scope half refuses the one shape whose meaning silently changes: on the
    /// LAST row p3's `next` is the WRAP row (back to row 0), so an `.all`- or `.last`-scoped `Nxt`
    /// is a constraint between the final row and the first — never what a sorted table means, and
    /// invisible in the algebra.
    fn check(&self) -> Result<(), String> {
        let mut worst: Option<usize> = None;
        let mut note = |e: &WindowExpr| {
            if let Some(v) = e.max_var() {
                worst = Some(worst.map_or(v, |w: usize| w.max(v)));
            }
        };
        for g in &self.gates {
            note(&g.body);
        }
        for i in &self.interactions {
            note(&i.mult);
            for t in &i.tuple {
                note(t);
            }
        }
        if let Some(v) = worst
            && v >= self.width
        {
            return Err(format!(
                "table air \"{}\" reads column {} but declares width {}",
                self.name, v, self.width
            ));
        }
        for (gi, g) in self.gates.iter().enumerate() {
            if matches!(g.sel, RowSel::All | RowSel::Last) && reads_next(&g.body) {
                return Err(format!(
                    "table air \"{}\": gate {} is \"{}\"-scoped but reads the next row; \
                     on the last row that is the WRAP row",
                    self.name,
                    gi,
                    g.sel.tag()
                ));
            }
        }
        Ok(())
    }
}

/// Does this expression read the NEXT row anywhere?
fn reads_next(e: &WindowExpr) -> bool {
    match e {
        WindowExpr::Nxt(_) => true,
        WindowExpr::Loc(_) | WindowExpr::Const(_) => false,
        WindowExpr::Add(a, b) | WindowExpr::Mul(a, b) => reads_next(a) || reads_next(b),
    }
}

/// Parse one gate object `{"sel":…,"body":…}`.
fn parse_gate(c: &mut JsonCursor) -> Result<TableGate, String> {
    c.expect(b'{')?;
    c.expect_key("sel")?;
    let sel = RowSel::from_tag(&c.parse_string()?)?;
    c.expect(b',')?;
    c.expect_key("body")?;
    let body = crate::descriptor_ir2::parse_window_expr(c)?;
    c.expect(b'}')?;
    Ok(TableGate { sel, body })
}

/// Parse one interaction object.
fn parse_interaction(c: &mut JsonCursor) -> Result<TableInteraction, String> {
    c.expect(b'{')?;
    c.expect_key("bus")?;
    let bus = c.parse_string()?;
    c.expect(b',')?;
    c.expect_key("op")?;
    let op = BusOp::from_tag(&c.parse_string()?)?;
    c.expect(b',')?;
    c.expect_key("mult")?;
    let mult = crate::descriptor_ir2::parse_window_expr(c)?;
    c.expect(b',')?;
    c.expect_key("tuple")?;
    let tuple = parse_expr_array(c)?;
    c.expect(b'}')?;
    Ok(TableInteraction {
        bus,
        op,
        mult,
        tuple,
    })
}

/// Parse a JSON array of `<window_expr>` objects.
fn parse_expr_array(c: &mut JsonCursor) -> Result<Vec<WindowExpr>, String> {
    c.expect(b'[')?;
    let mut out = Vec::new();
    if c.peek() == Some(b']') {
        c.expect(b']')?;
        return Ok(out);
    }
    loop {
        out.push(crate::descriptor_ir2::parse_window_expr(c)?);
        match c.peek() {
            Some(b',') => {
                c.expect(b',')?;
            }
            _ => break,
        }
    }
    c.expect(b']')?;
    Ok(out)
}

/// Parse a JSON array of `<gate>` objects.
fn parse_gate_array(c: &mut JsonCursor) -> Result<Vec<TableGate>, String> {
    c.expect(b'[')?;
    let mut out = Vec::new();
    if c.peek() == Some(b']') {
        c.expect(b']')?;
        return Ok(out);
    }
    loop {
        out.push(parse_gate(c)?);
        match c.peek() {
            Some(b',') => {
                c.expect(b',')?;
            }
            _ => break,
        }
    }
    c.expect(b']')?;
    Ok(out)
}

/// **Decode a Lean-emitted table AIR.** Mirrors `TableAirIR.emitTableAirJson` key for key; the
/// `"kind"` and `"ir"` fields are checked so a v2 descriptor JSON cannot be mistaken for one.
pub fn parse_table_air(src: &str) -> Result<LeanTableAir, String> {
    let mut c = JsonCursor::new(src);
    c.expect(b'{')?;
    c.expect_key("name")?;
    let name = c.parse_string()?;
    c.expect(b',')?;
    c.expect_key("kind")?;
    let kind = c.parse_string()?;
    if kind != "table_air" {
        return Err(format!("expected kind \"table_air\", found \"{kind}\""));
    }
    c.expect(b',')?;
    c.expect_key("ir")?;
    let ir = c.parse_int()?;
    if ir != 2 {
        return Err(format!("unsupported table-air IR version {ir}"));
    }
    c.expect(b',')?;
    c.expect_key("width")?;
    let width = c.parse_int()?;
    if width <= 0 {
        return Err(format!("table air \"{name}\" declares width {width}"));
    }
    c.expect(b',')?;
    c.expect_key("gates")?;
    let gates = parse_gate_array(&mut c)?;
    c.expect(b',')?;
    c.expect_key("interactions")?;
    c.expect(b'[')?;
    let mut interactions = Vec::new();
    if c.peek() == Some(b']') {
        c.expect(b']')?;
    } else {
        loop {
            interactions.push(parse_interaction(&mut c)?);
            match c.peek() {
                Some(b',') => {
                    c.expect(b',')?;
                }
                _ => break,
            }
        }
        c.expect(b']')?;
    }
    c.expect(b'}')?;

    let t = LeanTableAir {
        name,
        width: width as usize,
        gates,
        interactions,
    };
    t.check()?;
    Ok(t)
}

// ================================================================================================
// The checked-in Lean emissions.
// ================================================================================================

/// The map-absent table AIR, emitted by `Dregg2.Circuit.Emit.MapAbsentTableEmit.mapAbsentTable`.
///
/// ⚑ This is the live in-circuit double-spend gate: a note spend reaches it through
/// `noteSpendVmDescriptor2R24`'s `nullifierFreshOp`. Its algebra used to be ~150 lines of
/// hand-written Rust in `descriptor_ir2.rs::Ir2Air::MapAbsent`; those lines are deleted and this
/// string is what replaced them.
pub const MAP_ABSENT_TABLE_AIR_JSON: &str =
    include_str!("../descriptors/table-airs/dregg-ir2-map-absent-v1.json");

/// The byte (nibble) table AIR, emitted by `Dregg2.Circuit.Emit.ByteTableEmit.byteTable`.
///
/// ⚑ This is what "this felt is 30 bits wide" MEANS at the deployed prover: `eval_decomp` splits a
/// value into 4-bit limbs and queries each full limb here. Its algebra used to be the
/// `Ir2Air::ByteTable` arm; those lines are deleted.
pub const BYTE_TABLE_AIR_JSON: &str =
    include_str!("../descriptors/table-airs/dregg-ir2-byte-v1.json");

/// The memory-boundary table AIR, emitted by
/// `Dregg2.Circuit.Emit.MemBoundaryTableEmit.memBoundaryTable`.
///
/// The DECLARED ADDRESS LIST of the IR-v2 memory argument: it publishes each declared address's
/// initial image at serial 0, consumes its final image, and SERVES the `ir2_mem_addrs` table that
/// `Ir2Air::Memory` queries for address closure. Its algebra used to be the `Ir2Air::MemBoundary`
/// arm; those lines are deleted.
pub const MEM_BOUNDARY_TABLE_AIR_JSON: &str =
    include_str!("../descriptors/table-airs/dregg-ir2-mem-boundary-v1.json");

/// The memory op-log table AIR, emitted by `Dregg2.Circuit.Emit.MemoryTableEmit.memoryTable`.
///
/// The flat OP LOG of the IR-v2 memory argument: one row per memory operation, carrying the
/// positional serial chain, the read discipline, the serial-gap range check, both `ir2_mem_check`
/// Blum legs and the `ir2_mem_addrs` closure QUERY (the boundary is the server). Its algebra used
/// to be the `Ir2Air::Memory` arm; those lines are deleted.
///
/// ⚑ The Lean file REFUTES one of the three claims that arm asserted in comments: the gap gate
/// DEFINES `prev_serial = serial − 1 − gap` in the field rather than bounding it, so a claimed
/// prior serial of `p − 5` at serial 1 satisfies every gate. The refusal lives in the
/// `ir2_mem_check` multiset, not here.
pub const MEMORY_TABLE_AIR_JSON: &str =
    include_str!("../descriptors/table-airs/dregg-ir2-memory-v1.json");

/// The COHORT universal-boundary table AIR, emitted by
/// `Dregg2.Circuit.Emit.UMemBoundaryCohortTableEmit.cohortTable`.
///
/// The width-9 SINGLE-ROW specialization of the universal-memory boundary: the same
/// `ir2_umem_check` Blum legs and the same served `ir2_umem_addrs` closure table as the general
/// boundary, with the inter-row lexicographic comparator and the canonical key decomposition — 29
/// of the general boundary's 38 columns — dropped. Its algebra used to be the
/// `Ir2Air::UMemBoundaryCohort` arm; those lines are deleted.
///
/// ⚑ The Lean file proves the single-row tooth (`every_row_after_the_first_is_a_pad`, under
/// `Coherent`) — the ENTIRE soundness licence for dropping a `Nodup`-establishing comparator — and
/// then draws the line the deleted comment did not: the tooth bounds the MULTISET's declared list,
/// not the served closure table, whose multiplicity column no gate reads on any row.
pub const UMEM_BOUNDARY_COHORT_TABLE_AIR_JSON: &str =
    include_str!("../descriptors/table-airs/dregg-ir2-umem-boundary-cohort-v1.json");

/// The GENERAL universal-boundary table AIR, emitted by
/// `Dregg2.Circuit.Emit.UMemBoundaryTableEmit.umemBoundaryTable`.
///
/// The width-38 multi-address form of the universal-memory boundary: the same Blum legs and served
/// closure table as the cohort, plus the DOMAIN-MAJOR lexicographic strict-increase comparator over
/// full-felt keys that establishes `Nodup` for more than one declared address. Its algebra used to
/// be the `Ir2Air::UMemBoundary` arm; those lines are deleted.
///
/// ⚑ The Lean file proves the `same_dom` forcing in BOTH directions and then exhibits
/// `the_gates_alone_admit_a_duplicate_declared_address` — a three-row trace with domains 1 → 0 → 1
/// that satisfies every GATE while rows 0 and 2 declare the same `(domain, key)`. The domain-major
/// half of the order is carried by the `ir2_byte` nibble lookup on the gap column, which is a BUS
/// leg; the gates alone do not give `Nodup`.
pub const UMEM_BOUNDARY_TABLE_AIR_JSON: &str =
    include_str!("../descriptors/table-airs/dregg-ir2-umem-boundary-v1.json");

/// The decoded map-absent table AIR. Panics on a malformed artifact — the artifact is
/// `include_str!`d, so a failure here is a build-time defect, not a runtime input.
pub fn map_absent_table_air() -> LeanTableAir {
    (*map_absent_table_air_shared()).clone()
}

/// The decoded map-absent table AIR, parsed ONCE per process.
///
/// `instance_airs` runs on BOTH the prove and the verify path, so a naive
/// `parse_table_air(include_str!(..))` at each call would re-parse 90 KB of JSON per proof and per
/// verification — a cost the deleted hand-written arm did not have, and one the cutover has no
/// reason to introduce. The artifact is a compile-time constant, so the parse is too.
pub fn map_absent_table_air_shared() -> Arc<LeanTableAir> {
    static CACHED: OnceLock<Arc<LeanTableAir>> = OnceLock::new();
    Arc::clone(CACHED.get_or_init(|| {
        Arc::new(
            parse_table_air(MAP_ABSENT_TABLE_AIR_JSON)
                .expect("the checked-in map-absent table AIR must decode"),
        )
    }))
}

/// The decoded byte table AIR.
pub fn byte_table_air() -> LeanTableAir {
    (*byte_table_air_shared()).clone()
}

/// The decoded byte table AIR, parsed ONCE per process (see [`map_absent_table_air_shared`]).
pub fn byte_table_air_shared() -> Arc<LeanTableAir> {
    static CACHED: OnceLock<Arc<LeanTableAir>> = OnceLock::new();
    Arc::clone(CACHED.get_or_init(|| {
        Arc::new(
            parse_table_air(BYTE_TABLE_AIR_JSON)
                .expect("the checked-in byte table AIR must decode"),
        )
    }))
}

/// The decoded memory-boundary table AIR.
pub fn mem_boundary_table_air() -> LeanTableAir {
    (*mem_boundary_table_air_shared()).clone()
}

/// The decoded memory-boundary table AIR, parsed ONCE per process.
pub fn mem_boundary_table_air_shared() -> Arc<LeanTableAir> {
    static CACHED: OnceLock<Arc<LeanTableAir>> = OnceLock::new();
    Arc::clone(CACHED.get_or_init(|| {
        Arc::new(
            parse_table_air(MEM_BOUNDARY_TABLE_AIR_JSON)
                .expect("the checked-in memory-boundary table AIR must decode"),
        )
    }))
}

/// The decoded memory op-log table AIR.
pub fn memory_table_air() -> LeanTableAir {
    (*memory_table_air_shared()).clone()
}

/// The decoded memory op-log table AIR, parsed ONCE per process.
pub fn memory_table_air_shared() -> Arc<LeanTableAir> {
    static CACHED: OnceLock<Arc<LeanTableAir>> = OnceLock::new();
    Arc::clone(CACHED.get_or_init(|| {
        Arc::new(
            parse_table_air(MEMORY_TABLE_AIR_JSON)
                .expect("the checked-in memory table AIR must decode"),
        )
    }))
}

/// The decoded cohort universal-boundary table AIR.
pub fn umem_boundary_cohort_table_air() -> LeanTableAir {
    (*umem_boundary_cohort_table_air_shared()).clone()
}

/// The decoded cohort universal-boundary table AIR, parsed ONCE per process.
pub fn umem_boundary_cohort_table_air_shared() -> Arc<LeanTableAir> {
    static CACHED: OnceLock<Arc<LeanTableAir>> = OnceLock::new();
    Arc::clone(CACHED.get_or_init(|| {
        Arc::new(
            parse_table_air(UMEM_BOUNDARY_COHORT_TABLE_AIR_JSON)
                .expect("the checked-in cohort universal-boundary table AIR must decode"),
        )
    }))
}

/// The decoded general universal-boundary table AIR.
pub fn umem_boundary_table_air() -> LeanTableAir {
    (*umem_boundary_table_air_shared()).clone()
}

/// The decoded general universal-boundary table AIR, parsed ONCE per process.
pub fn umem_boundary_table_air_shared() -> Arc<LeanTableAir> {
    static CACHED: OnceLock<Arc<LeanTableAir>> = OnceLock::new();
    Arc::clone(CACHED.get_or_init(|| {
        Arc::new(
            parse_table_air(UMEM_BOUNDARY_TABLE_AIR_JSON)
                .expect("the checked-in general universal-boundary table AIR must decode"),
        )
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The checked-in artifact decodes, and its shape is the Lean author's — the counts are
    /// derived here from the deployed layout constants rather than transcribed from the Lean
    /// `#guard`, so the two sides are independent.
    #[test]
    fn the_map_absent_emission_decodes_at_the_deployed_shape() {
        let t = map_absent_table_air();
        assert_eq!(t.name, "dregg-ir2-map-absent-v1");

        // Width, from the layout: 8 root + 1 key + 8 new_root + 1 real + 3 leaf fields
        // + 8 leaf + 8·16 sibs + 16 dirs + 8·15 chain + 3·13 canon + 2·13 cmp.
        let depth = crate::heap_root::HEAP_TREE_DEPTH;
        let lanes = crate::descriptor_ir2::CHIP_OUT_LANES;
        let width = 8
            + 1
            + 8
            + 1
            + 3
            + lanes
            + lanes * depth
            + depth
            + lanes * (depth - 1)
            + 3 * 13
            + 2 * 13;
        assert_eq!(t.width, width, "the emitted width is the deployed MA_WIDTH");
        assert_eq!(t.width, 358);

        // Gates: 1 guard + `depth` dir bits + `lanes` root-preservation + 3·9 canon + 2·9 cmp.
        assert_eq!(t.gates.len(), 1 + depth + lanes + 3 * 9 + 2 * 9);
        assert_eq!(t.gates.len(), 70);

        // Interactions: 3·7 canon + 2·7 cmp byte queries, 1 leaf absorb + `depth` node8 folds
        // on the chip bus, 1 map-log receive.
        assert_eq!(t.bus_count_on("ir2_byte"), 3 * 7 + 2 * 7);
        assert_eq!(t.bus_count_on("ir2_p2"), 1 + depth);
        assert_eq!(t.bus_count_on("ir2_map_log"), 1);
        assert_eq!(t.interactions.len(), 53);
    }

    /// ⚑ The map-absent table is purely ROW-LOCAL: every gate is unfiltered and no gate reads the
    /// next row. That is the property that let it be ported against the first-pass IR (which had
    /// no selector at all), so it is the property a re-emission must not quietly lose — a
    /// `.transition` re-scope accepts strictly MORE rows and leaves the algebra untouched.
    #[test]
    fn the_map_absent_table_is_row_local() {
        let t = map_absent_table_air();
        assert_eq!(t.gate_count_sel(RowSel::All), 70);
        assert_eq!(t.gate_count_sel(RowSel::First), 0);
        assert_eq!(t.gate_count_sel(RowSel::Last), 0);
        assert_eq!(t.gate_count_sel(RowSel::Transition), 0);
        assert!(t.gates.iter().all(|g| !reads_next(&g.body)));
    }

    /// The chip absorbs and the log receive ride at multiplicity `is_real` (column 17), not at a
    /// constant — a pad row must send ZERO queries. This is the field `Lookup` could not carry,
    /// so a decoder that silently dropped it would break the LogUp balance rather than a gate.
    #[test]
    fn the_padded_legs_carry_a_column_multiplicity_not_a_constant() {
        let t = map_absent_table_air();
        for i in t.interactions.iter().filter(|i| i.bus != "ir2_byte") {
            // `matches!` DESTRUCTURES — constructing a `WindowExpr` here to compare against would
            // be Rust-authored IR, which is the very thing this module exists to delete (and
            // `law1_no_new_rust_authored_constraints` counts it, `#[cfg(test)]` or not).
            assert!(
                matches!(i.mult, WindowExpr::Loc(17)),
                "the {} leg must ride at `is_real`, got {:?}",
                i.bus,
                i.mult
            );
        }
        // …and the byte queries are the UNCOUNTED variant the deployed arm used.
        for i in t.interactions.iter().filter(|i| i.bus == "ir2_byte") {
            assert!(matches!(i.mult, WindowExpr::Const(1)), "got {:?}", i.mult);
        }
    }

    /// The map-log leg is a RECEIVE. A table that SENT its log would double-count instead of
    /// serving the main AIR's send, so the direction is not cosmetic.
    #[test]
    fn the_map_log_leg_is_a_receive() {
        let t = map_absent_table_air();
        let logs: Vec<_> = t
            .interactions
            .iter()
            .filter(|i| i.bus == "ir2_map_log")
            .collect();
        assert_eq!(logs.len(), 1);
        assert_eq!(logs[0].op, BusOp::Receive);
        assert_eq!(logs[0].tuple.len(), 19, "the 19-felt map-log tuple");
        // op code 2 = `.absent`, canonical value 0, at the tuple's centre.
        assert!(matches!(logs[0].tuple[9], WindowExpr::Const(0)));
        assert!(matches!(logs[0].tuple[10], WindowExpr::Const(2)));
    }

    /// The byte emission decodes at the deployed shape: width 2, one `.first` gate, one
    /// `.transition` gate, and ONE leg — the `.provide` side of `ir2_byte`.
    #[test]
    fn the_byte_emission_decodes_at_the_deployed_shape() {
        let t = byte_table_air();
        assert_eq!(t.name, "dregg-ir2-byte-v1");
        assert_eq!(t.width, 2);
        assert_eq!(t.gates.len(), 2);
        assert_eq!(t.gate_count_sel(RowSel::First), 1);
        assert_eq!(t.gate_count_sel(RowSel::Transition), 1);
        assert_eq!(t.gate_count_sel(RowSel::All), 0);
        assert_eq!(t.interactions.len(), 1);
    }

    /// ⚑ THE SIDE OF THE BUS. The byte table SERVES `ir2_byte`; it does not query it. In p3 the
    /// two differ by the sign of the count AND by `count_weight` (0 vs 1), so a `.query` here
    /// would make the bus unsatisfiable in one direction and vacuous in the other — an error no
    /// gate-level check could see, because there is no gate involved.
    #[test]
    fn the_byte_table_provides_it_does_not_query() {
        let t = byte_table_air();
        assert_eq!(t.bus_count_op("ir2_byte", BusOp::Provide), 1);
        assert_eq!(t.bus_count_op("ir2_byte", BusOp::Query), 0);
        let leg = &t.interactions[0];
        assert_eq!(leg.tuple.len(), 1, "the served key is the value column");
        assert!(matches!(leg.tuple[0], WindowExpr::Loc(0)));
        // The multiplicity is the second column — how many times this entry is consumed.
        assert!(matches!(leg.mult, WindowExpr::Loc(1)));
    }

    /// The increment gate reads the NEXT row, under `.transition` and nothing else. On the last
    /// row p3's `next` wraps to row 0, so an `.all` scope here would make the honest table UNSAT.
    #[test]
    fn the_byte_increment_is_transition_scoped_and_reads_next() {
        let t = byte_table_air();
        let trans: Vec<_> = t
            .gates
            .iter()
            .filter(|g| g.sel == RowSel::Transition)
            .collect();
        assert_eq!(trans.len(), 1);
        assert!(reads_next(&trans[0].body));
        let first: Vec<_> = t.gates.iter().filter(|g| g.sel == RowSel::First).collect();
        assert_eq!(first.len(), 1);
        assert!(!reads_next(&first[0].body), "the anchor is row-local");
    }

    /// A wire object that reads past its declared width is REFUSED at decode time.
    #[test]
    fn a_column_past_the_width_is_refused() {
        let bad = r#"{"name":"x","kind":"table_air","ir":2,"width":2,"gates":[{"sel":"all","body":{"t":"loc","c":7}}],"interactions":[]}"#;
        let err = parse_table_air(bad).expect_err("must refuse");
        assert!(err.contains("reads column 7"), "got: {err}");
    }

    /// ⚑ A next-row read OUTSIDE `.transition`/`.first` is REFUSED. On the last row p3's `next` is
    /// the WRAP row, so an `.all`-scoped `Nxt` silently constrains the final row against the
    /// first — a relation no sorted table means and one the algebra alone cannot show.
    #[test]
    fn an_unscoped_next_row_read_is_refused() {
        let bad = r#"{"name":"x","kind":"table_air","ir":2,"width":2,"gates":[{"sel":"all","body":{"t":"nxt","c":0}}],"interactions":[]}"#;
        let err = parse_table_air(bad).expect_err("must refuse");
        assert!(err.contains("reads the next row"), "got: {err}");
        // …and the same body under `.transition` is fine.
        let ok = r#"{"name":"x","kind":"table_air","ir":2,"width":2,"gates":[{"sel":"transition","body":{"t":"nxt","c":0}}],"interactions":[]}"#;
        assert!(parse_table_air(ok).is_ok());
    }

    /// An unknown row selector is REFUSED rather than defaulted. A wire tag that silently became
    /// `.all` would turn a padded table's transition gate into a wrap-row constraint.
    #[test]
    fn an_unknown_selector_is_refused() {
        let bad = r#"{"name":"x","kind":"table_air","ir":2,"width":2,"gates":[{"sel":"sometimes","body":{"t":"loc","c":0}}],"interactions":[]}"#;
        let err = parse_table_air(bad).expect_err("must refuse");
        assert!(err.contains("unknown row selector"), "got: {err}");
    }

    /// A v2 DESCRIPTOR json cannot be mistaken for a table AIR.
    #[test]
    fn a_descriptor_is_not_a_table_air() {
        let d = r#"{"name":"demo-v2","ir":2,"trace_width":2,"public_input_count":1}"#;
        assert!(parse_table_air(d).is_err());
    }

    /// The memory-boundary emission decodes at the deployed shape. The counts are derived here
    /// from the layout constants (two 30-bit decompositions of `decomp_cols(30)` columns each)
    /// rather than transcribed from the Lean `#guard`, so the two sides are independent.
    #[test]
    fn the_mem_boundary_emission_decodes_at_the_deployed_shape() {
        let t = mem_boundary_table_air();
        assert_eq!(t.name, "dregg-ir2-mem-boundary-v1");

        // Width: 6 named columns + agap + its limbs + achk + its limbs.
        let dc = crate::descriptor_ir2::decomp_cols_pub(30);
        assert_eq!(dc, 10);
        assert_eq!(t.width, 6 + 1 + dc + 1 + dc);
        assert_eq!(t.width, 28);

        // Gates: 1 boolean + 2 transition + two decompositions of (2 top bits + top recomp +
        // whole recomp) + the magnitude definition.
        assert_eq!(t.gates.len(), 1 + 2 + 4 + 1 + 4);
        assert_eq!(t.gates.len(), 12);
        assert_eq!(t.gate_count_sel(RowSel::Transition), 2);
        assert_eq!(t.gate_count_sel(RowSel::All), 10);

        // Interactions: 7 full limbs per decomposition, plus the two Blum legs and the served
        // address table.
        assert_eq!(t.bus_count_on("ir2_byte"), 2 * 7);
        assert_eq!(t.bus_count_on("ir2_mem_check"), 2);
        assert_eq!(t.bus_count_on("ir2_mem_addrs"), 1);
        assert_eq!(t.interactions.len(), 17);
    }

    /// ⚑ THE SIDES OF TWO BUSES AT ONCE. This table SERVES `ir2_mem_addrs` (the closure table
    /// `Ir2Air::Memory` queries) and QUERIES `ir2_byte`. Swapping either would leave every gate
    /// green: a `.query` on `ir2_mem_addrs` makes the closure argument unsatisfiable in one
    /// direction and vacuous in the other, and there is no gate that could notice.
    #[test]
    fn the_mem_boundary_serves_the_address_table_and_queries_the_byte_table() {
        let t = mem_boundary_table_air();
        assert_eq!(t.bus_count_op("ir2_mem_addrs", BusOp::Provide), 1);
        assert_eq!(t.bus_count_op("ir2_mem_addrs", BusOp::Query), 0);
        assert_eq!(t.bus_count_op("ir2_byte", BusOp::Query), 14);
        assert_eq!(t.bus_count_op("ir2_byte", BusOp::Provide), 0);
        // The Blum pair: the init image is PUBLISHED at serial 0, the final image CONSUMED.
        assert_eq!(t.bus_count_op("ir2_mem_check", BusOp::Send), 1);
        assert_eq!(t.bus_count_op("ir2_mem_check", BusOp::Receive), 1);
        let send = t
            .interactions
            .iter()
            .find(|i| i.bus == "ir2_mem_check" && i.op == BusOp::Send)
            .expect("one send");
        assert_eq!(send.tuple.len(), 3);
        assert!(
            matches!(send.tuple[2], WindowExpr::Const(0)),
            "the init image is published at serial ZERO — the anchor the whole Blum chain \
             bottoms out in"
        );
    }

    /// The memory op-log emission decodes at the deployed shape. The counts are derived here from
    /// the layout constants (one 30-bit decomposition of `decomp_cols(30)` columns) rather than
    /// transcribed from the Lean `#guard`, so the two sides are independent.
    #[test]
    fn the_memory_emission_decodes_at_the_deployed_shape() {
        let t = memory_table_air();
        assert_eq!(t.name, "dregg-ir2-memory-v1");

        // Width: 8 named columns + the gap's limb block.
        let dc = crate::descriptor_ir2::decomp_cols_pub(30);
        assert_eq!(dc, 10);
        assert_eq!(t.width, 8 + dc);
        assert_eq!(t.width, 18);

        // Gates: 2 booleans + the real prefix + the serial anchor + the serial increment + the
        // read discipline + the gap definition + one decomposition (2 top bits + top recomp +
        // whole recomp).
        assert_eq!(t.gates.len(), 2 + 1 + 1 + 1 + 1 + 1 + 4);
        assert_eq!(t.gates.len(), 11);
        assert_eq!(t.gate_count_sel(RowSel::All), 8);
        assert_eq!(t.gate_count_sel(RowSel::Transition), 2);
        assert_eq!(t.gate_count_sel(RowSel::First), 1);
        assert_eq!(t.gate_count_sel(RowSel::Last), 0);

        // Interactions: 7 full limbs, the op log, the two Blum legs, the closure query.
        assert_eq!(t.bus_count_on("ir2_byte"), 7);
        assert_eq!(t.bus_count_on("ir2_mem_log"), 1);
        assert_eq!(t.bus_count_on("ir2_mem_check"), 2);
        assert_eq!(t.bus_count_on("ir2_mem_addrs"), 1);
        assert_eq!(t.interactions.len(), 11);
    }

    /// ⚑ THE TWO SIDES OF `ir2_mem_addrs`, pinned from the CLIENT end. The op log QUERIES the
    /// declared-address table; the boundary SERVES it. Both halves are asserted here against the
    /// two decoded emissions at once, because a swap on either side leaves every gate green.
    #[test]
    fn the_op_log_queries_the_address_table_the_boundary_serves() {
        let mem = memory_table_air();
        let bnd = mem_boundary_table_air();
        assert_eq!(mem.bus_count_op("ir2_mem_addrs", BusOp::Query), 1);
        assert_eq!(mem.bus_count_op("ir2_mem_addrs", BusOp::Provide), 0);
        assert_eq!(bnd.bus_count_op("ir2_mem_addrs", BusOp::Provide), 1);
        assert_eq!(bnd.bus_count_op("ir2_mem_addrs", BusOp::Query), 0);

        // The op PUBLISHES its own image at its own serial and CONSUMES the prior one it claims.
        assert_eq!(mem.bus_count_op("ir2_mem_check", BusOp::Send), 1);
        assert_eq!(mem.bus_count_op("ir2_mem_check", BusOp::Receive), 1);
        let send = mem
            .interactions
            .iter()
            .find(|i| i.bus == "ir2_mem_check" && i.op == BusOp::Send)
            .expect("one publish");
        // (addr, value, serial) — the SERIAL column, not the claimed prior one.
        assert_eq!(send.tuple.len(), 3);
        assert!(matches!(send.tuple[2], WindowExpr::Loc(5)));
        let recv = mem
            .interactions
            .iter()
            .find(|i| i.bus == "ir2_mem_check" && i.op == BusOp::Receive)
            .expect("one consume");
        assert!(
            matches!(recv.tuple[2], WindowExpr::Loc(3)),
            "the CLAIMED prior serial"
        );
    }

    /// The cohort universal-boundary emission decodes at the deployed shape. ⚑ The counts are
    /// derived here from the DEPLOYED width constant rather than transcribed from the Lean
    /// `#guard`, and the width relation to the general boundary — the whole point of the
    /// specialization — is asserted rather than described.
    #[test]
    fn the_cohort_umem_boundary_emission_decodes_at_the_deployed_shape() {
        let t = umem_boundary_cohort_table_air();
        assert_eq!(t.name, "dregg-ir2-umem-boundary-cohort-v1");
        // 7 named columns + the guard + the served multiplicity.
        assert_eq!(t.width, 9);

        // Gates: 3 booleans + the single-row tooth + two canonical-`none` legs.
        assert_eq!(t.gates.len(), 3 + 1 + 2);
        assert_eq!(t.gate_count_sel(RowSel::All), 5);
        assert_eq!(t.gate_count_sel(RowSel::Transition), 1);
        assert_eq!(t.gate_count_sel(RowSel::First), 0);
        assert_eq!(t.gate_count_sel(RowSel::Last), 0);

        // Interactions: the domain nibble, the two Blum legs, the served closure entry.
        assert_eq!(t.bus_count_on("ir2_byte"), 1);
        assert_eq!(t.bus_count_on("ir2_umem_check"), 2);
        assert_eq!(t.bus_count_on("ir2_umem_addrs"), 1);
        assert_eq!(t.interactions.len(), 4);
    }

    /// ⚑ THE SINGLE-ROW TOOTH IS THE ONE TRANSITION GATE, and it reads ONLY the next row's guard.
    /// A `.all` re-scope would bind the WRAP row (on the last row p3's `next` is row 0) and make an
    /// honest cohort with a real row 0 UNSAT; the decoder refuses that shape outright, and this
    /// pins that the deployed gate sits where it must.
    #[test]
    fn the_cohort_single_row_tooth_is_transition_scoped_and_reads_only_next() {
        let t = umem_boundary_cohort_table_air();
        let trans: Vec<_> = t
            .gates
            .iter()
            .filter(|g| g.sel == RowSel::Transition)
            .collect();
        assert_eq!(trans.len(), 1);
        assert!(matches!(trans[0].body, WindowExpr::Nxt(7)), "next.is_real");
        // …and it SERVES the closure table at a column multiplicity, never a constant.
        assert_eq!(t.bus_count_op("ir2_umem_addrs", BusOp::Provide), 1);
        assert_eq!(t.bus_count_op("ir2_umem_addrs", BusOp::Query), 0);
        let serve = t
            .interactions
            .iter()
            .find(|i| i.bus == "ir2_umem_addrs")
            .expect("one served entry");
        assert_eq!(serve.tuple.len(), 2, "(domain, key)");
        assert!(matches!(serve.mult, WindowExpr::Loc(8)));
        // The Blum legs ride at `is_real`, which is what makes a pad declare NOTHING to the
        // multiset — the reason the single-row tooth bounds the declared list at all.
        for i in t.interactions.iter().filter(|i| i.bus == "ir2_umem_check") {
            assert!(matches!(i.mult, WindowExpr::Loc(7)));
        }
    }

    /// The general universal-boundary emission decodes at the deployed shape, and — ⚑ the check
    /// that says what the specialization BUYS — the cohort really is a quarter of it.
    #[test]
    fn the_general_umem_boundary_emission_decodes_at_the_deployed_shape() {
        let t = umem_boundary_table_air();
        assert_eq!(t.name, "dregg-ir2-umem-boundary-v1");

        // Width: 9 shared columns + a 13-column canonical key split + dgap/same_dom/inv
        // + a 13-column comparator block.
        let canon = 1 + crate::descriptor_ir2::decomp_cols_pub(27) + 2;
        let cmp = 3 + crate::descriptor_ir2::decomp_cols_pub(27);
        assert_eq!((canon, cmp), (13, 13));
        assert_eq!(t.width, 9 + canon + 3 + cmp);
        assert_eq!(t.width, 38);

        // Gates: 4 booleans + the real prefix + 2 canonical-`none` + 9 canonical split
        // + dgap def + inverse witness + `dgap·same_dom` + 6 comparator row-local + 3 branches.
        assert_eq!(t.gates.len(), 4 + 1 + 2 + 9 + 3 + 6 + 3);
        assert_eq!(t.gates.len(), 28);
        assert_eq!(t.gate_count_sel(RowSel::All), 22);
        assert_eq!(t.gate_count_sel(RowSel::Transition), 6);
        assert_eq!(t.gate_count_sel(RowSel::First), 0);
        assert_eq!(t.gate_count_sel(RowSel::Last), 0);

        // Interactions: domain nibble + 7 canonical + dgap nibble + 7 comparator + 2 Blum + serve.
        assert_eq!(t.bus_count_on("ir2_byte"), 1 + 7 + 1 + 7);
        assert_eq!(t.bus_count_on("ir2_umem_check"), 2);
        assert_eq!(t.bus_count_on("ir2_umem_addrs"), 1);
        assert_eq!(t.interactions.len(), 19);

        // ⚑ WHAT THE COHORT BUYS, measured against the two emissions rather than described: the
        // specialization is a quarter of the width and carries a fifth of the gates.
        let c = umem_boundary_cohort_table_air();
        assert!(
            c.width * 4 <= t.width,
            "cohort {} vs general {}",
            c.width,
            t.width
        );
        assert!(c.gates.len() * 4 <= t.gates.len());
        // …and the cohort's 9-column prefix is the general one's: the two Blum tuples agree
        // column-for-column, which is what lets `build_traces` write ONE prefix for both.
        for op in [BusOp::Send, BusOp::Receive] {
            let g = t
                .interactions
                .iter()
                .find(|i| i.bus == "ir2_umem_check" && i.op == op)
                .expect("a general Blum leg");
            let cc = c
                .interactions
                .iter()
                .find(|i| i.bus == "ir2_umem_check" && i.op == op)
                .expect("a cohort Blum leg");
            assert_eq!(
                g.tuple, cc.tuple,
                "the two boundaries' {op:?} tuples must agree"
            );
            assert_eq!(g.mult, cc.mult);
        }
    }

    /// ⚑ THE COMPARATOR'S THREE BRANCH EQUATIONS ARE `.transition`-SCOPED AND READ THE NEXT ROW —
    /// the property that distinguishes this table from `map-absent`, which asserts the SAME three
    /// under `.all` against two columns of one row. A drift either way leaves the algebra
    /// byte-identical (`TableGate.transition_weakens`), so it is pinned on the emitted object.
    #[test]
    fn the_general_boundary_comparator_compares_against_the_successor() {
        let t = umem_boundary_table_air();
        let trans: Vec<_> = t
            .gates
            .iter()
            .filter(|g| g.sel == RowSel::Transition)
            .collect();
        assert_eq!(
            trans.len(),
            6,
            "prefix, dgap def, inverse witness, 3 branches"
        );
        // The last three transition gates are the comparator branches, and two of the three read
        // the next row (the middle one is `gate·(1−s)·(bHi − aHi)`, which reads it too).
        assert!(
            trans[3..].iter().all(|g| reads_next(&g.body)),
            "every comparator branch must compare against the SUCCESSOR"
        );
        // …and the map-absent comparator does NOT, because it compares within one row.
        let ma = map_absent_table_air();
        assert!(ma.gates.iter().all(|g| !reads_next(&g.body)));
    }

    /// A row-filtered gate costs one more degree than its body, because p3's filtered builder
    /// multiplies by the selector — and so does the interpreter. The byte table's bodies are
    /// linear, so its gate degree is 2, and its bus leg (`mult` × tuple, both linear) is 2 too.
    #[test]
    fn a_filtered_gate_costs_the_selector() {
        let t = byte_table_air();
        assert_eq!(t.max_degree(), 2);
        // The map-absent table is unfiltered, so no gate pays the selector.
        let ma = map_absent_table_air();
        assert!(ma.gates.iter().all(|g| g.sel == RowSel::All));
    }
}
