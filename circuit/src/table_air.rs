//! # `table_air` — the decoder for a Lean-authored TABLE AIR.
//!
//! ## What was missing
//!
//! IR-v2 emits the MAIN instance: an [`crate::descriptor_ir2::EffectVmDescriptor2`] carries one
//! effect's own row algebra and `Ir2Air::Main` interprets it. The other eight instances the
//! deployed prover assembles — the Poseidon2 chip, the byte table, the memory pair, the map-ops
//! pair, the universal-memory pair — are a SECOND kind of AIR: a shared auxiliary table with its
//! own width, its own column space, and its own bus interactions. IR-v2 had no vocabulary for that
//! object, so all eight were hand-authored Rust algebra, in direct violation of architectural law
//! #1 (*"circuits are emitted from Lean; Rust only INTERPRETS"*).
//!
//! This module is the interpreter for the vocabulary. The Lean author is
//! `Dregg2/Circuit/TableAirIR.lean`; `Dregg2/Circuit/Emit/MapAbsentTableEmit.lean` is the first
//! table to use it, and `circuit/descriptors/table-airs/dregg-ir2-map-absent-v1.json` is its
//! emission. **Nothing in this file authors a constraint**: it decodes a wire object whose
//! `gates` are [`LeanExpr`] trees and whose `interactions` name a bus, a call shape, a
//! multiplicity expression and a tuple. `Ir2Air::LeanTable` walks that and calls `assert_zero` /
//! `lookup_key` / `receive` on exactly what it says.
//!
//! ## Why the multiplicity expression is the load-bearing new field
//!
//! `Ir2Air::Main` hardcodes multiplicity `1` on every declared lookup, because a main row is
//! unconditionally real. A shared table is PADDED — the map-absent table's chip absorbs ride at
//! multiplicity `is_real`, so a pad row must send ZERO queries or the LogUp balance is wrong — so
//! a table IR without a per-row multiplicity expression cannot express the deployed AIR at all.
//! That is the concrete reason [`TableInteraction`] exists rather than reusing the descriptor's
//! `Lookup`.
//!
//! ## Column space
//!
//! `LeanExpr::Var(c)` here reads column `c` of **this table's** row, not the main trace's. That is
//! the whole "sub-descriptor at a column offset" content, and it is why this is a separate
//! `Ir2Air` arm rather than a splice into the main constraint walk.

use std::sync::{Arc, OnceLock};

use crate::lean_descriptor_air::{JsonCursor, LeanExpr, parse_expr};

/// The bus call shape (Lean `TableAirIR.BusOp`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BusOp {
    /// `LookupBus::lookup_key` — a subset query against a served table.
    Query,
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
            BusOp::Receive => "receive",
            BusOp::Send => "send",
        }
    }

    fn from_tag(t: &str) -> Result<Self, String> {
        match t {
            "query" => Ok(BusOp::Query),
            "receive" => Ok(BusOp::Receive),
            "send" => Ok(BusOp::Send),
            other => Err(format!("unknown bus op \"{other}\"")),
        }
    }
}

/// One bus interaction of a table AIR (Lean `TableAirIR.BusInteraction`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TableInteraction {
    /// The bus name — matches the `BUS_*` string constants in `descriptor_ir2`.
    pub bus: String,
    /// The call shape.
    pub op: BusOp,
    /// Per-row multiplicity. `Const(1)` is the unconditional case.
    pub mult: LeanExpr,
    /// The tuple placed on the bus.
    pub tuple: Vec<LeanExpr>,
}

/// A table AIR, authored in Lean and decoded here (Lean `TableAirIR.TableAir`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeanTableAir {
    /// The emitted name (the artifact's identity).
    pub name: String,
    /// This table's own column count.
    pub width: usize,
    /// Row-local gates: each must VANISH on every row.
    pub gates: Vec<LeanExpr>,
    /// The declared bus interactions.
    pub interactions: Vec<TableInteraction>,
}

impl LeanTableAir {
    /// The maximum polynomial degree over all gates and all multiplicity-weighted tuples — what
    /// the batch assembly needs to size the quotient.
    pub fn max_degree(&self) -> usize {
        let gate_deg = self.gates.iter().map(LeanExpr::degree).max().unwrap_or(0);
        let bus_deg = self
            .interactions
            .iter()
            .map(|i| {
                let m = i.mult.degree();
                m + i.tuple.iter().map(LeanExpr::degree).max().unwrap_or(0)
            })
            .max()
            .unwrap_or(0);
        gate_deg.max(bus_deg)
    }

    /// How many interactions this table declares on a given bus. A re-emission that drops a bus
    /// leg moves this, which is what the shape pins in the cutover test check.
    pub fn bus_count_on(&self, bus: &str) -> usize {
        self.interactions.iter().filter(|i| i.bus == bus).count()
    }

    /// Every column index the table reads must be inside its declared width. A wire object that
    /// reads past its row would index out of bounds inside the `Air` evaluator; this refuses it
    /// at decode time instead.
    fn check_width(&self) -> Result<(), String> {
        let mut worst: Option<usize> = None;
        let mut note = |e: &LeanExpr| {
            if let Some(v) = e.max_var() {
                worst = Some(worst.map_or(v, |w: usize| w.max(v)));
            }
        };
        for g in &self.gates {
            note(g);
        }
        for i in &self.interactions {
            note(&i.mult);
            for t in &i.tuple {
                note(t);
            }
        }
        match worst {
            Some(v) if v >= self.width => Err(format!(
                "table air \"{}\" reads column {} but declares width {}",
                self.name, v, self.width
            )),
            _ => Ok(()),
        }
    }
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
    let mult = parse_expr(c)?;
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

/// Parse a JSON array of `<expr>` objects.
fn parse_expr_array(c: &mut JsonCursor) -> Result<Vec<LeanExpr>, String> {
    c.expect(b'[')?;
    let mut out = Vec::new();
    if c.peek() == Some(b']') {
        c.expect(b']')?;
        return Ok(out);
    }
    loop {
        out.push(parse_expr(c)?);
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
    let gates = parse_expr_array(&mut c)?;
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
    t.check_width()?;
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

/// The decoded map-absent table AIR. Panics on a malformed artifact — the artifact is
/// `include_str!`d, so a failure here is a build-time defect, not a runtime input.
pub fn map_absent_table_air() -> LeanTableAir {
    (*map_absent_table_air_shared()).clone()
}

/// The decoded map-absent table AIR, parsed ONCE per process.
///
/// `instance_airs` runs on BOTH the prove and the verify path, so a naive
/// `parse_table_air(include_str!(..))` at each call would re-parse 79 KB of JSON per proof and per
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

    /// The chip absorbs and the log receive ride at multiplicity `is_real` (column 17), not at a
    /// constant — a pad row must send ZERO queries. This is the field `Lookup` could not carry,
    /// so a decoder that silently dropped it would break the LogUp balance rather than a gate.
    #[test]
    fn the_padded_legs_carry_a_column_multiplicity_not_a_constant() {
        let t = map_absent_table_air();
        for i in t.interactions.iter().filter(|i| i.bus != "ir2_byte") {
            // `matches!` DESTRUCTURES — constructing a `LeanExpr` here to compare against would
            // be Rust-authored IR, which is the very thing this module exists to delete (and
            // `law1_no_new_rust_authored_constraints` counts it, `#[cfg(test)]` or not).
            assert!(
                matches!(i.mult, LeanExpr::Var(17)),
                "the {} leg must ride at `is_real`, got {:?}",
                i.bus,
                i.mult
            );
        }
        // …and the byte queries are the UNCOUNTED variant the deployed arm used.
        for i in t.interactions.iter().filter(|i| i.bus == "ir2_byte") {
            assert!(matches!(i.mult, LeanExpr::Const(1)), "got {:?}", i.mult);
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
        assert!(matches!(logs[0].tuple[9], LeanExpr::Const(0)));
        assert!(matches!(logs[0].tuple[10], LeanExpr::Const(2)));
    }

    /// A wire object that reads past its declared width is REFUSED at decode time.
    #[test]
    fn a_column_past_the_width_is_refused() {
        let bad = r#"{"name":"x","kind":"table_air","ir":2,"width":2,"gates":[{"t":"var","v":7}],"interactions":[]}"#;
        let err = parse_table_air(bad).expect_err("must refuse");
        assert!(err.contains("reads column 7"), "got: {err}");
    }

    /// A v2 DESCRIPTOR json cannot be mistaken for a table AIR.
    #[test]
    fn a_descriptor_is_not_a_table_air() {
        let d = r#"{"name":"demo-v2","ir":2,"trace_width":2,"public_input_count":1}"#;
        assert!(parse_table_air(d).is_err());
    }
}
