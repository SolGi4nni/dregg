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
//! constraint**: it decodes a wire object whose `gates` are [`TableExpr`] trees under a [`RowSel`],
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
//! p3 row filter. [`TableGate`] carries that filter and [`TableExpr::Nxt`] reads the next row.
//!
//! ⚠ Bus interactions carry NO selector, deliberately: every deployed table pushes its
//! interactions on the unfiltered builder (a filtered p3 builder is not an `InteractionBuilder`),
//! and the padding discipline rides in the multiplicity expression instead.
//!
//! ## Column space
//!
//! `TableExpr::Loc(c)` / `Nxt(c)` here read column `c` of **this table's** current / next row, not
//! the main trace's. That is the whole "sub-descriptor at a column offset" content, and it is why
//! this is a separate `Ir2Air` arm rather than a splice into the main constraint walk.

//! ## ⚑ Column space, and why this module has its OWN expression type
//!
//! A table AIR's expression is [`TableExpr`], not the main descriptor's `TableExpr`. The decision
//! and its evidence live in the Lean author (`Dregg2/Circuit/TableAirIR.lean` §1b); the Rust side
//! mirrors it for the same reason, stated in the terms that bite here: `Ir2Air::Main` has NO
//! definition list, so a `Shr` leaf reaching it has nothing to resolve against, and it has no
//! preprocessed trace, so a future `Prep` leaf would index out of an empty slice. Widening
//! `TableExpr` would put permanently-unserviceable variants into the type `Ir2Air::Main`
//! interprets and buy a fail-closed refusal on the main decode path for each. Here they are simply
//! a different type that the main path never sees.
//!
//! The five shared constructors carry IDENTICAL wire tags to `TableExpr`'s, which is why the eight
//! artifacts emitted before the sharing node existed re-emit with every gate and interaction byte
//! unchanged.

use std::sync::{Arc, OnceLock};

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

/// A table AIR's expression (Lean `TableAirIR.TExpr`): the main IR's five leaves plus the SHARING
/// leaf. `Loc(c)` / `Nxt(c)` read column `c` of **this table's** current / next row, not the main
/// trace's — that is the whole "sub-descriptor at a column offset" content, and it is why this is a
/// separate `Ir2Air` arm rather than a splice into the main constraint walk.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TableExpr {
    /// Current-row column `c`.
    Loc(usize),
    /// Next-row column `c`.
    Nxt(usize),
    /// A signed integer constant.
    Const(i64),
    /// ⚑ **The SHARING leaf**: the already-computed value of [`LeanTableAir::defs`]`[i]`.
    ///
    /// The interpreter evaluates the definition list ONCE per row into a vector and every `Shr`
    /// reads it — which is what makes the emitted DAG cost the prover what the deployed
    /// hand-written arm costs it, rather than what a re-expanded tree would. A definition may
    /// reference only STRICTLY EARLIER definitions ([`LeanTableAir::check`] refuses otherwise), so
    /// one left-to-right pass resolves the whole list.
    Shr(usize),
    /// ⚑ **The PREPROCESSED leaf**: column `c` of this row of the table's preprocessed matrix.
    ///
    /// A DIFFERENT COLUMN SPACE from `Loc`/`Nxt`. The preprocessed matrix is not committed by the
    /// prover — the verifier rebuilds it from the descriptor and commits it itself — so a value
    /// read here is verifier-known by construction, which is the whole content of an exact-public
    /// manifest. Bounded by [`LeanTableAir::prep_width`], never by `width`; a decoder that checked
    /// it against `width` would be checking a bound in the wrong space.
    ///
    /// ⚠ There is no next-row form. Every preprocessed-reading arm declares
    /// `preprocessed_next_row_columns() == []` and reads `current_slice()` alone.
    Prep(usize),
    /// Field addition.
    Add(Box<TableExpr>, Box<TableExpr>),
    /// Field multiplication.
    Mul(Box<TableExpr>, Box<TableExpr>),
}

impl TableExpr {
    /// The maximum column index referenced (over both row tags), if any. ⚠ `Shr` reads NO column of
    /// its own — its columns are its definition's, and [`LeanTableAir::check`] resolves that through
    /// the definition list rather than here.
    pub(crate) fn max_var(&self) -> Option<usize> {
        match self {
            TableExpr::Loc(i) | TableExpr::Nxt(i) => Some(*i),
            TableExpr::Const(_) | TableExpr::Shr(_) | TableExpr::Prep(_) => None,
            TableExpr::Add(a, b) | TableExpr::Mul(a, b) => match (a.max_var(), b.max_var()) {
                (Some(x), Some(y)) => Some(x.max(y)),
                (Some(x), None) | (None, Some(x)) => Some(x),
                (None, None) => None,
            },
        }
    }

    /// The maximum `Shr` index referenced, if any. What the acyclicity and range checks read —
    /// and what a differential reads to say "this gate block shares nothing", which is the
    /// hypothesis a sub-table analysis of it needs.
    pub fn max_share(&self) -> Option<usize> {
        match self {
            TableExpr::Shr(i) => Some(*i),
            TableExpr::Loc(_) | TableExpr::Nxt(_) | TableExpr::Const(_) | TableExpr::Prep(_) => {
                None
            }
            TableExpr::Add(a, b) | TableExpr::Mul(a, b) => match (a.max_share(), b.max_share()) {
                (Some(x), Some(y)) => Some(x.max(y)),
                (Some(x), None) | (None, Some(x)) => Some(x),
                (None, None) => None,
            },
        }
    }

    /// The maximum PREPROCESSED column index referenced, if any — the Lean `TExpr.maxPrep`.
    ///
    /// ⚠ A `Shr` contributes NOTHING here: its `Prep` reads are its DEFINITION's, and
    /// [`LeanTableAir::check`] scans every definition in its own right, so the whole list is
    /// covered without chasing through the share.
    pub fn max_prep(&self) -> Option<usize> {
        match self {
            TableExpr::Prep(c) => Some(*c),
            TableExpr::Loc(_) | TableExpr::Nxt(_) | TableExpr::Const(_) | TableExpr::Shr(_) => None,
            TableExpr::Add(a, b) | TableExpr::Mul(a, b) => match (a.max_prep(), b.max_prep()) {
                (Some(x), Some(y)) => Some(x.max(y)),
                (Some(x), None) | (None, Some(x)) => Some(x),
                (None, None) => None,
            },
        }
    }

    /// The total degree as a polynomial over the columns, given the degrees of the definitions
    /// already resolved. `Const` = 0, `Loc`/`Nxt` = 1, `Shr(i)` = `def_degrees[i]`, `Add` = max,
    /// `Mul` = sum.
    ///
    /// ⚠ A `Shr` is NOT degree 1. Sharing changes REPRESENTATION, not degree, and a version that
    /// treated a share as a leaf would report the chip's degree-7 S-box as degree 1 and silently
    /// under-size the quotient. `def_degrees` is built in the same left-to-right pass the values
    /// are.
    pub(crate) fn degree_with(&self, def_degrees: &[usize]) -> usize {
        match self {
            TableExpr::Const(_) => 0,
            // A preprocessed cell is a committed column of the preprocessed commitment: degree 1,
            // exactly as a main-trace column is.
            TableExpr::Loc(_) | TableExpr::Nxt(_) | TableExpr::Prep(_) => 1,
            TableExpr::Shr(i) => def_degrees.get(*i).copied().unwrap_or(usize::MAX),
            TableExpr::Add(a, b) => a.degree_with(def_degrees).max(b.degree_with(def_degrees)),
            TableExpr::Mul(a, b) => a
                .degree_with(def_degrees)
                .saturating_add(b.degree_with(def_degrees)),
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
    pub body: TableExpr,
}

/// One bus interaction of a table AIR (Lean `TableAirIR.BusInteraction`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TableInteraction {
    /// The bus name — matches the `BUS_*` string constants in `descriptor_ir2`.
    pub bus: String,
    /// The call shape.
    pub op: BusOp,
    /// Per-row multiplicity. `Const(1)` is the unconditional case.
    pub mult: TableExpr,
    /// The tuple placed on the bus.
    pub tuple: Vec<TableExpr>,
}

/// A table AIR, authored in Lean and decoded here (Lean `TableAirIR.TableAir`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeanTableAir {
    /// The emitted name (the artifact's identity).
    pub name: String,
    /// This table's own COMMITTED column count.
    pub width: usize,
    /// ⚑ **THE DECLARED PREPROCESSED WIDTH** — the column count [`TableExpr::Prep`] indexes, and
    /// `0` for a table that reads none.
    ///
    /// A SEPARATE bound because it is a separate column space: `width` bounds the trace the prover
    /// commits, this bounds the matrix the VERIFIER rebuilds and commits. The exact-public family
    /// reads `width = 1` against `prep_width = arity + 2`, so a `Prep` index checked against
    /// `width` would pass nothing and a `Loc` index checked against this would pass almost
    /// anything. `BaseAir::preprocessed_width` for an `Ir2Air::LeanTable` is exactly this number,
    /// which is what makes the sweep oracle's fail-closed shape contract key on the AIR's own
    /// declaration rather than on a list of arms.
    pub prep_width: usize,
    /// ⚑ **THE SHARED DEFINITION LIST** — the sub-expressions the interpreter computes ONCE per
    /// row, which every [`TableExpr::Shr`] then reads.
    ///
    /// The deployed hand-written arms hold their shared sub-values as `AB::Expr` VALUES:
    /// `poseidon2_permute_expr_lanes` computes each round's 16 S-box outputs once and the linear
    /// layer references them 35× each. A tree emission of the same polynomial duplicates them —
    /// 141,439 nodes against 7,355 on the chip, 70,524 field operations against 2,943. `defs` is
    /// the vocabulary for the sharing the deployed gadget already had.
    ///
    /// Entry `i` may reference only entries `< i`; [`LeanTableAir::check`] refuses otherwise, which
    /// is what makes the interpreter's single left-to-right pass a resolution rather than a guess.
    pub defs: Vec<TableExpr>,
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
        let dd = self.def_degrees();
        let gate_deg = self
            .gates
            .iter()
            .map(|g| g.body.degree_with(&dd) + usize::from(!matches!(g.sel, RowSel::All)))
            .max()
            .unwrap_or(0);
        let bus_deg = self
            .interactions
            .iter()
            .map(|i| {
                let m = i.mult.degree_with(&dd);
                m + i
                    .tuple
                    .iter()
                    .map(|e| e.degree_with(&dd))
                    .max()
                    .unwrap_or(0)
            })
            .max()
            .unwrap_or(0);
        gate_deg.max(bus_deg)
    }

    /// The degree of each shared definition, resolved in the one left-to-right pass the values are.
    ///
    /// ⚠ This is what keeps `ir2_degree_budget` honest under sharing: the chip's S-box is four
    /// definitions whose degrees run 2, 3, 4, 7, and a gate that reads the last of them is degree
    /// 7 exactly as the tree spelling was. Sharing changes representation, not degree.
    pub fn def_degrees(&self) -> Vec<usize> {
        let mut out: Vec<usize> = Vec::with_capacity(self.defs.len());
        for d in &self.defs {
            let deg = d.degree_with(&out);
            out.push(deg);
        }
        out
    }

    /// The number of shared definitions — a count a re-emission cannot silently drop.
    pub fn def_count(&self) -> usize {
        self.defs.len()
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
    /// ⚑ …and the definition list must be ACYCLIC BY ORDER and every `Shr` in range.
    ///
    /// `defs[i]` may reference only `defs[j]` with `j < i`. That is not a style rule: the
    /// interpreter resolves the list in ONE left-to-right pass, so a forward or self reference
    /// would read a slot that does not exist yet. This function refuses it; nothing downstream
    /// substitutes a zero. An out-of-range `Shr` in a gate, a multiplicity or a tuple is refused
    /// for the same reason.
    fn check(&self) -> Result<(), String> {
        // Shares FIRST: `reads_next` and the column bound both resolve through the definition
        // list, and neither is meaningful until the list is known to be well-formed.
        for (di, d) in self.defs.iter().enumerate() {
            if let Some(m) = d.max_share()
                && m >= di
            {
                return Err(format!(
                    "table air \"{}\": definition {} references definition {}, which is not \
                     strictly earlier; the definition list must be topologically ordered",
                    self.name, di, m
                ));
            }
        }
        let nd = self.defs.len();
        let mut share_out_of_range = |e: &TableExpr, what: &str| -> Result<(), String> {
            match e.max_share() {
                Some(m) if m >= nd => Err(format!(
                    "table air \"{}\": {} references definition {} but only {} are declared",
                    self.name, what, m, nd
                )),
                _ => Ok(()),
            }
        };
        for (gi, g) in self.gates.iter().enumerate() {
            share_out_of_range(&g.body, &format!("gate {gi}"))?;
        }
        for (ii, i) in self.interactions.iter().enumerate() {
            share_out_of_range(&i.mult, &format!("interaction {ii} multiplicity"))?;
            for (ti, t) in i.tuple.iter().enumerate() {
                share_out_of_range(t, &format!("interaction {ii} tuple element {ti}"))?;
            }
        }

        // ⚑ THE PREPROCESSED BOUND, in its OWN space. The Lean `TableAir.prepsInRange`. Every
        // `Prep` — definitions included, since a share resolves to one — must name a declared
        // preprocessed column, or the evaluator would index past `current_slice()` and panic
        // inside p3 rather than refusing here.
        let pw = self.prep_width;
        let mut prep_out_of_range = |e: &TableExpr, what: &str| -> Result<(), String> {
            match e.max_prep() {
                Some(m) if m >= pw => Err(format!(
                    "table air \"{}\": {} reads preprocessed column {} but declares \
                     prep_width {}",
                    self.name, what, m, pw
                )),
                _ => Ok(()),
            }
        };
        for (di, d) in self.defs.iter().enumerate() {
            prep_out_of_range(d, &format!("definition {di}"))?;
        }
        for (gi, g) in self.gates.iter().enumerate() {
            prep_out_of_range(&g.body, &format!("gate {gi}"))?;
        }
        for (ii, i) in self.interactions.iter().enumerate() {
            prep_out_of_range(&i.mult, &format!("interaction {ii} multiplicity"))?;
            for (ti, t) in i.tuple.iter().enumerate() {
                prep_out_of_range(t, &format!("interaction {ii} tuple element {ti}"))?;
            }
        }

        let mut worst: Option<usize> = None;
        {
            // A `Shr` reads its DEFINITION's columns, so the column bound is resolved through the
            // list — which is also why the definitions are scanned here at all.
            let mut note = |e: &TableExpr| {
                if let Some(v) = e.max_var() {
                    worst = Some(worst.map_or(v, |w: usize| w.max(v)));
                }
            };
            for d in &self.defs {
                note(d);
            }
            for g in &self.gates {
                note(&g.body);
            }
            for i in &self.interactions {
                note(&i.mult);
                for t in &i.tuple {
                    note(t);
                }
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

        // ⚑ The next-row scope refusal, resolved THROUGH the definitions. A gate that reads `nxt`
        // only via a `Shr` is still a gate that reads the next row, and a version of this check
        // that stopped at the `Shr` leaf would wave exactly that shape through under `.all` — a
        // silent constraint between the final row and the first.
        let dn = self.defs_read_next();
        for (gi, g) in self.gates.iter().enumerate() {
            if matches!(g.sel, RowSel::All | RowSel::Last) && reads_next_with(&g.body, &dn) {
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

    /// Per-definition next-row verdicts, one left-to-right pass.
    fn defs_read_next(&self) -> Vec<bool> {
        let mut out: Vec<bool> = Vec::with_capacity(self.defs.len());
        for d in &self.defs {
            let r = reads_next_with(d, &out);
            out.push(r);
        }
        out
    }

    /// Does this gate read the next row, resolving `Shr` through this table's definitions?
    pub fn gate_reads_next(&self, g: &TableGate) -> bool {
        reads_next_with(&g.body, &self.defs_read_next())
    }
}

/// Does this expression read the NEXT row, given per-definition verdicts already computed?
///
/// ⚠ An out-of-range `Shr` reads `true` — FAIL-CLOSED, so an unresolvable share is refused by the
/// `.all`-scoped-`nxt` check rather than waved through. (`check` refuses it first; this is the
/// belt.)
fn reads_next_with(e: &TableExpr, def_verdicts: &[bool]) -> bool {
    match e {
        TableExpr::Nxt(_) => true,
        // ⚠ `Prep` is a CURRENT-row read and there is no next-row preprocessed leaf, so it is not
        // the wrap-row hazard this predicate exists to refuse.
        TableExpr::Loc(_) | TableExpr::Const(_) | TableExpr::Prep(_) => false,
        TableExpr::Shr(i) => def_verdicts.get(*i).copied().unwrap_or(true),
        TableExpr::Add(a, b) | TableExpr::Mul(a, b) => {
            reads_next_with(a, def_verdicts) || reads_next_with(b, def_verdicts)
        }
    }
}

/// **Parse one `TableExpr`.** Mirrors Lean `TableAirIR.TExpr.toJson` tag for tag. The five shared
/// tags are `parse_window_expr`'s verbatim; `shr` is the sixth and it carries an INDEX (`i`), not a
/// column (`c`) — a decoder that read `c` here would resolve every share against column 0.
fn parse_table_expr(c: &mut JsonCursor) -> Result<TableExpr, String> {
    c.expect(b'{')?;
    c.expect_key("t")?;
    let tag = c.parse_string()?;
    let out = match tag.as_str() {
        "loc" => {
            c.expect(b',')?;
            c.expect_key("c")?;
            let i = c.parse_int()?;
            if i < 0 {
                return Err(format!("table expr `loc` index {i} is negative"));
            }
            TableExpr::Loc(i as usize)
        }
        "nxt" => {
            c.expect(b',')?;
            c.expect_key("c")?;
            let i = c.parse_int()?;
            if i < 0 {
                return Err(format!("table expr `nxt` index {i} is negative"));
            }
            TableExpr::Nxt(i as usize)
        }
        "const" => {
            c.expect(b',')?;
            c.expect_key("v")?;
            TableExpr::Const(c.parse_int()?)
        }
        "shr" => {
            c.expect(b',')?;
            c.expect_key("i")?;
            let i = c.parse_int()?;
            if i < 0 {
                return Err(format!("table expr `shr` index {i} is negative"));
            }
            TableExpr::Shr(i as usize)
        }
        // ⚠ `prep` carries a COLUMN (`c`), like `loc`/`nxt`; `shr` carries an INDEX (`i`). The keys
        // differ, so a decoder that read the wrong one resolves NOTHING rather than resolving
        // something wrong.
        "prep" => {
            c.expect(b',')?;
            c.expect_key("c")?;
            let i = c.parse_int()?;
            if i < 0 {
                return Err(format!("table expr `prep` column {i} is negative"));
            }
            TableExpr::Prep(i as usize)
        }
        "add" | "mul" => {
            c.expect(b',')?;
            c.expect_key("l")?;
            let l = parse_table_expr(c)?;
            c.expect(b',')?;
            c.expect_key("r")?;
            let r = parse_table_expr(c)?;
            if tag == "add" {
                TableExpr::Add(Box::new(l), Box::new(r))
            } else {
                TableExpr::Mul(Box::new(l), Box::new(r))
            }
        }
        other => return Err(format!("unknown table expr tag \"{other}\"")),
    };
    c.expect(b'}')?;
    Ok(out)
}

/// Parse one gate object `{"sel":…,"body":…}`.
fn parse_gate(c: &mut JsonCursor) -> Result<TableGate, String> {
    c.expect(b'{')?;
    c.expect_key("sel")?;
    let sel = RowSel::from_tag(&c.parse_string()?)?;
    c.expect(b',')?;
    c.expect_key("body")?;
    let body = parse_table_expr(c)?;
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
    let mult = parse_table_expr(c)?;
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
fn parse_expr_array(c: &mut JsonCursor) -> Result<Vec<TableExpr>, String> {
    c.expect(b'[')?;
    let mut out = Vec::new();
    if c.peek() == Some(b']') {
        c.expect(b']')?;
        return Ok(out);
    }
    loop {
        out.push(parse_table_expr(c)?);
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
    c.expect_key("prep_width")?;
    let prep_width = c.parse_int()?;
    if prep_width < 0 {
        return Err(format!(
            "table air \"{name}\" declares prep_width {prep_width}"
        ));
    }
    c.expect(b',')?;
    c.expect_key("defs")?;
    let defs = parse_expr_array(&mut c)?;
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
        prep_width: prep_width as usize,
        defs,
        gates,
        interactions,
    };
    t.check()?;
    Ok(t)
}

/// **Decode a Lean-emitted table AIR FAMILY** — a JSON ARRAY of the object [`parse_table_air`]
/// decodes, mirroring `TableAirIR.emitTableAirFamilyJson`.
///
/// ⚑ It exists because one of the eleven ported arms is not a table but a SCHEMA:
/// `Ir2Air::ExactPublicTable` was a family indexed by the declared tuple ARITY, and a single
/// descriptor may declare tables at several arities at once. The elements are ordinary table AIRs —
/// this adds no grammar, only a top-level array — and each is `check`ed exactly as a singleton is.
pub fn parse_table_air_family(src: &str) -> Result<Vec<LeanTableAir>, String> {
    // The elements are whole table-air objects, and `parse_table_air` owns the object grammar
    // (including its `check`). Split on the top-level array structure by tracking brace depth
    // inside the array, then hand each element to the singleton decoder verbatim, so the two
    // paths cannot drift.
    let bytes = src.as_bytes();
    let mut i = 0usize;
    while i < bytes.len() && bytes[i].is_ascii_whitespace() {
        i += 1;
    }
    if i >= bytes.len() || bytes[i] != b'[' {
        return Err("table air family must be a JSON array".to_string());
    }
    i += 1;
    let mut out: Vec<LeanTableAir> = Vec::new();
    loop {
        while i < bytes.len() && bytes[i].is_ascii_whitespace() {
            i += 1;
        }
        if i >= bytes.len() {
            return Err("table air family: unterminated array".to_string());
        }
        if bytes[i] == b']' {
            break;
        }
        if bytes[i] != b'{' {
            return Err(format!(
                "table air family: element {} does not begin with an object",
                out.len()
            ));
        }
        let start = i;
        let mut depth = 0usize;
        let mut in_string = false;
        while i < bytes.len() {
            let b = bytes[i];
            if in_string {
                // The emitted names and bus strings carry no escapes (`TableAirIR` renders them
                // verbatim), so a backslash cannot appear inside one; a quote always closes.
                if b == b'"' {
                    in_string = false;
                }
            } else if b == b'"' {
                in_string = true;
            } else if b == b'{' {
                depth += 1;
            } else if b == b'}' {
                depth -= 1;
                if depth == 0 {
                    i += 1;
                    break;
                }
            }
            i += 1;
        }
        if depth != 0 {
            return Err(format!(
                "table air family: element {} is unterminated",
                out.len()
            ));
        }
        out.push(parse_table_air(&src[start..i])?);
        while i < bytes.len() && bytes[i].is_ascii_whitespace() {
            i += 1;
        }
        if i < bytes.len() && bytes[i] == b',' {
            i += 1;
        }
    }
    if out.is_empty() {
        return Err("table air family declares no members".to_string());
    }
    Ok(out)
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

/// The UNIVERSAL memory op-log table AIR, emitted by
/// `Dregg2.Circuit.Emit.UMemoryTableEmit.umemoryTable`.
///
/// The op log of the ONE Blum multiset over `Domain × κ`, whose cells are `Option`s: the flat
/// memory's positional serial chain and 30-bit gap range check, a read discipline over BOTH
/// components of the `(present, value)` pair, canonical-`none` on both images, and the NULLIFIER
/// insert-only tooth. Its algebra used to be the `Ir2Air::UMemory` arm; those lines are deleted.
///
/// ⚑ The Lean file REFUTES two of the sentences that arm asserted in comments:
///
/// * *"`prev_serial < serial` (Disciplined), exactly the flat memory's gap shape"* — the second
///   clause is true and it is the refutation: there is NO magnitude gate on `UM_PREV_SERIAL`, so the
///   gap gate DEFINES the claimed serial in the field. `wrapped_prev_serial_satisfies_every_gate`
///   exhibits a nullifier-domain freshness read at serial 1 claiming a prior serial of `p − 5`.
/// * *"a nullifier-domain write installing `none` is UNSAT"* — true only of REAL rows. The tooth
///   `is_null·kind·(1 − present)` carries no `is_real` factor; the gating arrives two gates away
///   through the inverse-witness gate that forces `is_null = is_real`, so
///   `a_pad_row_spells_the_forbidden_nullifier_write` satisfies every gate.
///
/// Both are contained by the `ir2_umem_log` / `ir2_umem_check` legs, which ride at `is_real` — bus
/// legs, one object out.
pub const UMEMORY_TABLE_AIR_JSON: &str =
    include_str!("../descriptors/table-airs/dregg-ir2-umemory-v1.json");

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

/// The map RECONCILIATION table AIR, emitted by
/// `Dregg2.Circuit.Emit.MapOpsTableEmit.mapOpsTable`.
///
/// One row per map op: the 8-felt pre-root and post-root, the key/value/op code, the read/write
/// Merkle path, and — since gap-#5 — the whole APPEND-AT-FREE-INDEX (`op = 4`) two-path insert with
/// its pointer-bracket range block. Its algebra used to be ~320 lines of hand-written Rust in
/// `descriptor_ir2.rs::Ir2Air::MapOps`; those lines are deleted and this string is what replaced
/// them.
///
/// ⚑ The Lean file proves the AAFI selector pin in BOTH directions (`s_is_the_op4_indicator`) —
/// which is the entire licence for a COMMITTED degree-1 `is_aafi` standing in for the degree-3
/// polynomial that would blow the map-ops budget of 4 — and then REFUTES the sentence the deleted
/// arm's comment implies:
///
/// * `an_aafi_row_with_no_opening_satisfies_every_gate` — NOT ONE of this table's 84 chip legs is a
///   gate. A row with `root = new_root = 0`, an honest pointer bracket and an ALL-ZERO opening (no
///   leaf digest, no sibling, no chain node) satisfies every one of the 91 emitted gates at
///   `is_real = 1`. The Merkle content is 70% of the interactions and 0% of the algebra.
/// * `a_pad_row_can_spell_an_aafi_insert` — the AAFI ROW-LOCAL gates carry `s` alone, no `is_real`
///   factor, where every chip leg rides `aafi_gate = is_real·s`. So a PAD row must still carry a
///   real bracket and still SENDS the range block's 35 byte queries; what makes it inert is the
///   `ir2_map_log` receive riding at `is_real` — a bus leg, one object out.
pub const MAP_OPS_TABLE_AIR_JSON: &str =
    include_str!("../descriptors/table-airs/dregg-ir2-map-ops-v1.json");

/// The Poseidon2 CHIP table AIR, emitted by `Dregg2.Circuit.Emit.ChipTableEmit.chipTable`.
///
/// ⚑ The shared hash table EVERY IR-v2 proof rides: one instance per batch serves every hash fact —
/// the main trace's hash-site lookups, the map-ops leaf absorbs, the Merkle-chain facts. Its
/// arity/selector algebra, its seeding, its output binding and the 352 constraints of
/// `poseidon2_permute_expr_lanes` used to be ~280 lines of hand-written Rust in
/// `descriptor_ir2.rs::Ir2Air::Chip`; those lines are DELETED and this string is what replaced them.
///
/// ⚑ **This is the artifact the sharing node exists for.** 1,078 shared definitions — the round
/// constant adds, the four multiplications of each `exp_const_u64::<7>`, and the `t*`/`state`/`sums`
/// values of each `external_linear_layer_expr` — carrying the SAME sharing the deleted Rust arm had
/// as locals. Tree spelling: 141,439 nodes, 70,524 field operations per row, 3.1 MB. Shared:
/// 7,355 nodes, **2,943 operations**, 159 KB.
///
/// ⚑ The Lean file REFUTES FOUR of the deleted arm's comment-only claims — see
/// `Dregg2/Circuit/Emit/ChipTableEmit.lean` §7, and the `⚠ THE COMMENT WAS WRONG` notes on the
/// deleted arm's own text below.
pub const CHIP_TABLE_AIR_JSON: &str =
    include_str!("../descriptors/table-airs/dregg-ir2-chip-v1.json");

/// The `ChipState16` variant, emitted by `Dregg2.Circuit.Emit.ChipTableEmit.chipState16Table`.
///
/// The same width, the same 1,078 definitions and the same permutation as the legacy chip, plus ONE
/// gate (`mult_state16 · (arity − 16)`, which pins any row with a nonzero state-bus multiplicity to
/// arity 16) and a different bus interface: it serves the raw `[16, input_state16, output_state16]`
/// transition instead of the absorb/narrow/fact triple.
///
/// ⚑ The Lean file proves the extra gate is NOT decoration (`state16_refuses_arity4_at_nonzero_mult`)
/// and that it forces NOTHING at zero multiplicity, and it REFUTES the `(1 − is_fact)` factor on the
/// state16 bus multiplicity: `state16_bus_guard_is_dead` shows `mult_state16 ≢ 0 ∧ is_fact ≡ 1` is
/// unsatisfiable, so the factor never differs from 1 anywhere it could matter.
pub const CHIP_STATE16_TABLE_AIR_JSON: &str =
    include_str!("../descriptors/table-airs/dregg-ir2-chip-state16-v1.json");

/// ⚑ The EXACT-PUBLIC manifest table AIR FAMILY, emitted by
/// `Dregg2.Circuit.Emit.ExactPublicTableEmit.exactPublicFamily`.
///
/// ⚑ **The ELEVENTH and LAST hand-written arm.** `Ir2Air::ExactPublicTable` realized one declared
/// `TableSem::ExactPublicRows` manifest as ONE multiplicity-bearing batch instance: a single
/// committed capacity column pinned to a preprocessed one, plus a `table_entry` leg serving the
/// manifest tuple. Those lines are DELETED — the enum VARIANT too — and this array is what replaced
/// them. `Ir2Air` is now `Main | LeanTable`.
///
/// It is a FAMILY rather than a table because the arm was a schema: element `i` is arity `i + 1`,
/// up to `MAX_EXACT_PUBLIC_ARITY`, and one descriptor may declare tables at several arities at once.
///
/// ⚑ **And the bus name moved out of the string and into the tuple**, which is what made a
/// per-arity family expressible at all. The deployed shape spent one bus `ir2_exact_public_{id}`
/// per declared table — a number no artifact can know. The bus is now `ir2_exact_public_a{arity}`
/// and the TABLE ID is preprocessed column 0, the first field of every served tuple and of every
/// query. The separation is exactly as strong: LogUp balance is a multiset equality over TUPLES,
/// the id is a tuple field, and it lives in the matrix the verifier REBUILDS rather than accepts.
///
/// ⚑ The Lean file proves the pin in BOTH directions (`capacity_is_the_declared_multiplicity`,
/// `the_pin_refuses_a_free_capacity`, `..._a_short_capacity` — the gate is an EQUALITY, not a
/// `≤`) and REFUTES three of the deleted arm's comment-only claims:
///
/// * `the_gates_bind_no_manifest_value` / `the_gates_bind_no_table_id` — NOT ONE manifest value,
///   and not the id the whole per-instance separation rests on, is bound by any gate. The tuple is
///   100% of this table's soundness content and 0% of its algebra; what binds it is the verifier
///   rebuilding the matrix, one object out.
/// * `a_pad_shaped_row_is_admitted_at_any_capacity_the_matrix_declares` — *"pads carry
///   multiplicity ZERO so they contribute nothing"* is a property of
///   `ExactPublicManifest::preprocessed`'s `resize`, not of the gate.
/// * `gates_admit_every_height` — every gate is `.all`-scoped, so this AIR does not bound its own
///   committed height and `MIN_EXACT_PUBLIC_HEIGHT` is a p3 fact it neither knows nor enforces.
pub const EXACT_PUBLIC_TABLE_AIR_FAMILY_JSON: &str =
    include_str!("../descriptors/table-airs/dregg-ir2-exact-public-v1.json");

/// The decoded exact-public family, parsed ONCE per process.
///
/// ⚠ The length is NOT pinned here — `descriptor_ir2` pins it against its own
/// `MAX_EXACT_PUBLIC_ARITY` when it selects a member, so a drift between the emitted family and the
/// deployed ceiling REFUSES at selection rather than silently serving the wrong schema.
pub fn exact_public_table_air_family() -> &'static [LeanTableAir] {
    static CACHED: OnceLock<Vec<LeanTableAir>> = OnceLock::new();
    CACHED.get_or_init(|| {
        parse_table_air_family(EXACT_PUBLIC_TABLE_AIR_FAMILY_JSON)
            .expect("the checked-in exact-public table AIR family must decode")
    })
}

/// The arity-`arity` member of the exact-public family, shared.
///
/// # Errors
/// Returns the reason the arity is outside the emitted family — which is the fail-closed half: a
/// descriptor declaring a wider manifest than the Lean emission covers is REFUSED rather than
/// served by a nearby member.
pub fn exact_public_table_air_for(arity: usize) -> Result<Arc<LeanTableAir>, String> {
    static CACHED: OnceLock<Vec<Arc<LeanTableAir>>> = OnceLock::new();
    let all = CACHED.get_or_init(|| {
        exact_public_table_air_family()
            .iter()
            .map(|t| Arc::new(t.clone()))
            .collect()
    });
    if arity == 0 || arity > all.len() {
        return Err(format!(
            "exact-public arity {arity} is outside the emitted family 1..={}",
            all.len()
        ));
    }
    Ok(Arc::clone(&all[arity - 1]))
}

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

/// The decoded universal memory op-log table AIR.
pub fn umemory_table_air() -> LeanTableAir {
    (*umemory_table_air_shared()).clone()
}

/// The decoded universal memory op-log table AIR, parsed ONCE per process.
pub fn umemory_table_air_shared() -> Arc<LeanTableAir> {
    static CACHED: OnceLock<Arc<LeanTableAir>> = OnceLock::new();
    Arc::clone(CACHED.get_or_init(|| {
        Arc::new(
            parse_table_air(UMEMORY_TABLE_AIR_JSON)
                .expect("the checked-in universal memory table AIR must decode"),
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

/// The decoded Poseidon2 chip table AIR.
pub fn chip_table_air() -> LeanTableAir {
    (*chip_table_air_shared()).clone()
}

/// The decoded Poseidon2 chip table AIR, parsed ONCE per process. ⚑ Every batch carries a chip
/// instance, so this `OnceLock` is on the hottest path of the whole system.
pub fn chip_table_air_shared() -> Arc<LeanTableAir> {
    static CACHED: OnceLock<Arc<LeanTableAir>> = OnceLock::new();
    Arc::clone(CACHED.get_or_init(|| {
        Arc::new(
            parse_table_air(CHIP_TABLE_AIR_JSON)
                .expect("the checked-in chip table AIR must decode"),
        )
    }))
}

/// The decoded `ChipState16` table AIR.
pub fn chip_state16_table_air() -> LeanTableAir {
    (*chip_state16_table_air_shared()).clone()
}

/// The decoded `ChipState16` table AIR, parsed ONCE per process.
pub fn chip_state16_table_air_shared() -> Arc<LeanTableAir> {
    static CACHED: OnceLock<Arc<LeanTableAir>> = OnceLock::new();
    Arc::clone(CACHED.get_or_init(|| {
        Arc::new(
            parse_table_air(CHIP_STATE16_TABLE_AIR_JSON)
                .expect("the checked-in chip-state16 table AIR must decode"),
        )
    }))
}

/// The decoded map reconciliation table AIR.
pub fn map_ops_table_air() -> LeanTableAir {
    (*map_ops_table_air_shared()).clone()
}

/// The decoded map reconciliation table AIR, parsed ONCE per process. ⚑ The largest of the eight
/// artifacts at 331 KB — 84 chip lookups, each a 25-felt tuple with a direction-mixed L8/R8 block —
/// so the `OnceLock` matters more here than anywhere else: `instance_airs` runs on both the prove
/// and the verify path.
pub fn map_ops_table_air_shared() -> Arc<LeanTableAir> {
    static CACHED: OnceLock<Arc<LeanTableAir>> = OnceLock::new();
    Arc::clone(CACHED.get_or_init(|| {
        Arc::new(
            parse_table_air(MAP_OPS_TABLE_AIR_JSON)
                .expect("the checked-in map-ops table AIR must decode"),
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
        assert!(t.gates.iter().all(|g| !t.gate_reads_next(g)));
    }

    /// The chip absorbs and the log receive ride at multiplicity `is_real` (column 17), not at a
    /// constant — a pad row must send ZERO queries. This is the field `Lookup` could not carry,
    /// so a decoder that silently dropped it would break the LogUp balance rather than a gate.
    #[test]
    fn the_padded_legs_carry_a_column_multiplicity_not_a_constant() {
        let t = map_absent_table_air();
        for i in t.interactions.iter().filter(|i| i.bus != "ir2_byte") {
            // `matches!` DESTRUCTURES — constructing a `TableExpr` here to compare against would
            // be Rust-authored IR, which is the very thing this module exists to delete (and
            // `law1_no_new_rust_authored_constraints` counts it, `#[cfg(test)]` or not).
            assert!(
                matches!(i.mult, TableExpr::Loc(17)),
                "the {} leg must ride at `is_real`, got {:?}",
                i.bus,
                i.mult
            );
        }
        // …and the byte queries are the UNCOUNTED variant the deployed arm used.
        for i in t.interactions.iter().filter(|i| i.bus == "ir2_byte") {
            assert!(matches!(i.mult, TableExpr::Const(1)), "got {:?}", i.mult);
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
        assert!(matches!(logs[0].tuple[9], TableExpr::Const(0)));
        assert!(matches!(logs[0].tuple[10], TableExpr::Const(2)));
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
        assert!(matches!(leg.tuple[0], TableExpr::Loc(0)));
        // The multiplicity is the second column — how many times this entry is consumed.
        assert!(matches!(leg.mult, TableExpr::Loc(1)));
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
        assert!(t.gate_reads_next(trans[0]));
        let first: Vec<_> = t.gates.iter().filter(|g| g.sel == RowSel::First).collect();
        assert_eq!(first.len(), 1);
        assert!(!t.gate_reads_next(first[0]), "the anchor is row-local");
    }

    /// A wire object that reads past its declared width is REFUSED at decode time.
    #[test]
    fn a_column_past_the_width_is_refused() {
        let bad = r#"{"name":"x","kind":"table_air","ir":2,"width":2,"prep_width":0,"defs":[],"gates":[{"sel":"all","body":{"t":"loc","c":7}}],"interactions":[]}"#;
        let err = parse_table_air(bad).expect_err("must refuse");
        assert!(err.contains("reads column 7"), "got: {err}");
    }

    /// ⚑ A next-row read OUTSIDE `.transition`/`.first` is REFUSED. On the last row p3's `next` is
    /// the WRAP row, so an `.all`-scoped `Nxt` silently constrains the final row against the
    /// first — a relation no sorted table means and one the algebra alone cannot show.
    #[test]
    fn an_unscoped_next_row_read_is_refused() {
        let bad = r#"{"name":"x","kind":"table_air","ir":2,"width":2,"prep_width":0,"defs":[],"gates":[{"sel":"all","body":{"t":"nxt","c":0}}],"interactions":[]}"#;
        let err = parse_table_air(bad).expect_err("must refuse");
        assert!(err.contains("reads the next row"), "got: {err}");
        // …and the same body under `.transition` is fine.
        let ok = r#"{"name":"x","kind":"table_air","ir":2,"width":2,"prep_width":0,"defs":[],"gates":[{"sel":"transition","body":{"t":"nxt","c":0}}],"interactions":[]}"#;
        assert!(parse_table_air(ok).is_ok());
    }

    /// An unknown row selector is REFUSED rather than defaulted. A wire tag that silently became
    /// `.all` would turn a padded table's transition gate into a wrap-row constraint.
    #[test]
    fn an_unknown_selector_is_refused() {
        let bad = r#"{"name":"x","kind":"table_air","ir":2,"width":2,"prep_width":0,"defs":[],"gates":[{"sel":"sometimes","body":{"t":"loc","c":0}}],"interactions":[]}"#;
        let err = parse_table_air(bad).expect_err("must refuse");
        assert!(err.contains("unknown row selector"), "got: {err}");
    }

    /// ⚑ A `shr` that references a LATER definition is REFUSED. The interpreter resolves the
    /// definition list in ONE left-to-right pass, so a forward or self reference would read a slot
    /// that does not exist yet — and `Vec::get` would hand it a `None`, i.e. a silent zero. This is
    /// the refusal that makes the one-pass resolution sound rather than lucky.
    #[test]
    fn a_forward_definition_reference_is_refused() {
        let bad = r#"{"name":"x","kind":"table_air","ir":2,"width":2,"prep_width":0,"defs":[{"t":"shr","i":1},{"t":"loc","c":0}],"gates":[{"sel":"all","body":{"t":"shr","i":0}}],"interactions":[]}"#;
        let err = parse_table_air(bad).expect_err("must refuse a forward reference");
        assert!(err.contains("not strictly earlier"), "got: {err}");
        // …and a SELF reference, which is the cycle of length one.
        let selfref = r#"{"name":"x","kind":"table_air","ir":2,"width":2,"prep_width":0,"defs":[{"t":"shr","i":0}],"gates":[{"sel":"all","body":{"t":"shr","i":0}}],"interactions":[]}"#;
        assert!(
            parse_table_air(selfref)
                .expect_err("must refuse a self reference")
                .contains("not strictly earlier")
        );
        // …and the same list in TOPOLOGICAL order decodes.
        let ok = r#"{"name":"x","kind":"table_air","ir":2,"width":2,"prep_width":0,"defs":[{"t":"loc","c":0},{"t":"mul","l":{"t":"shr","i":0},"r":{"t":"shr","i":0}}],"gates":[{"sel":"all","body":{"t":"shr","i":1}}],"interactions":[]}"#;
        let t = parse_table_air(ok).expect("a topologically ordered list decodes");
        assert_eq!(t.def_count(), 2);
        // …and the shared square really is degree 2, not degree 1: a `Shr` is NOT a leaf.
        assert_eq!(t.def_degrees(), vec![1, 2]);
        assert_eq!(t.max_degree(), 2);
    }

    /// ⚑ A `shr` naming a definition that does not exist is REFUSED — in a gate, in a multiplicity
    /// and in a tuple. Substituting a zero would make the gate a DIFFERENT polynomial silently.
    #[test]
    fn an_out_of_range_share_is_refused() {
        for bad in [
            r#"{"name":"x","kind":"table_air","ir":2,"width":2,"prep_width":0,"defs":[],"gates":[{"sel":"all","body":{"t":"shr","i":0}}],"interactions":[]}"#,
            r#"{"name":"x","kind":"table_air","ir":2,"width":2,"prep_width":0,"defs":[{"t":"loc","c":0}],"gates":[],"interactions":[{"bus":"b","op":"query","mult":{"t":"shr","i":3},"tuple":[{"t":"loc","c":0}]}]}"#,
            r#"{"name":"x","kind":"table_air","ir":2,"width":2,"prep_width":0,"defs":[{"t":"loc","c":0}],"gates":[],"interactions":[{"bus":"b","op":"query","mult":{"t":"const","v":1},"tuple":[{"t":"shr","i":9}]}]}"#,
        ] {
            let err = parse_table_air(bad).expect_err("must refuse an out-of-range share");
            assert!(err.contains("only"), "got: {err}");
        }
    }

    /// ⚑ A next-row read hidden BEHIND a definition is still a next-row read. A `reads_next` that
    /// stopped at the `Shr` leaf would wave exactly this through under `.all` — the silent
    /// final-row-against-first constraint the scope refusal exists to prevent, now reachable by an
    /// emitter that hoists the read into a shared value.
    #[test]
    fn a_next_row_read_through_a_definition_is_refused() {
        let bad = r#"{"name":"x","kind":"table_air","ir":2,"width":2,"prep_width":0,"defs":[{"t":"nxt","c":0}],"gates":[{"sel":"all","body":{"t":"shr","i":0}}],"interactions":[]}"#;
        let err = parse_table_air(bad).expect_err("must refuse a shared next-row read under .all");
        assert!(err.contains("reads the next row"), "got: {err}");
        // …and TWO definitions deep, so the chase is not one level.
        let deep = r#"{"name":"x","kind":"table_air","ir":2,"width":2,"prep_width":0,"defs":[{"t":"nxt","c":0},{"t":"add","l":{"t":"shr","i":0},"r":{"t":"const","v":1}}],"gates":[{"sel":"all","body":{"t":"shr","i":1}}],"interactions":[]}"#;
        assert!(
            parse_table_air(deep)
                .expect_err("must chase through two definitions")
                .contains("reads the next row")
        );
        // …and the same shape under `.transition` decodes, so the refusal is about SCOPE.
        let ok = r#"{"name":"x","kind":"table_air","ir":2,"width":2,"prep_width":0,"defs":[{"t":"nxt","c":0}],"gates":[{"sel":"transition","body":{"t":"shr","i":0}}],"interactions":[]}"#;
        assert!(parse_table_air(ok).is_ok());
    }

    /// ⚑ A column read only THROUGH a definition is still bounded by the declared width. An
    /// emitter that hoisted an out-of-range read into a shared value would otherwise reach the
    /// evaluator and panic on the slice index.
    #[test]
    fn a_column_past_the_width_inside_a_definition_is_refused() {
        let bad = r#"{"name":"x","kind":"table_air","ir":2,"width":2,"prep_width":0,"defs":[{"t":"loc","c":7}],"gates":[{"sel":"all","body":{"t":"shr","i":0}}],"interactions":[]}"#;
        let err = parse_table_air(bad).expect_err("must refuse");
        assert!(err.contains("reads column 7"), "got: {err}");
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
            matches!(send.tuple[2], TableExpr::Const(0)),
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
        assert!(matches!(send.tuple[2], TableExpr::Loc(5)));
        let recv = mem
            .interactions
            .iter()
            .find(|i| i.bus == "ir2_mem_check" && i.op == BusOp::Receive)
            .expect("one consume");
        assert!(
            matches!(recv.tuple[2], TableExpr::Loc(3)),
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
        assert!(matches!(trans[0].body, TableExpr::Nxt(7)), "next.is_real");
        // …and it SERVES the closure table at a column multiplicity, never a constant.
        assert_eq!(t.bus_count_op("ir2_umem_addrs", BusOp::Provide), 1);
        assert_eq!(t.bus_count_op("ir2_umem_addrs", BusOp::Query), 0);
        let serve = t
            .interactions
            .iter()
            .find(|i| i.bus == "ir2_umem_addrs")
            .expect("one served entry");
        assert_eq!(serve.tuple.len(), 2, "(domain, key)");
        assert!(matches!(serve.mult, TableExpr::Loc(8)));
        // The Blum legs ride at `is_real`, which is what makes a pad declare NOTHING to the
        // multiset — the reason the single-row tooth bounds the declared list at all.
        for i in t.interactions.iter().filter(|i| i.bus == "ir2_umem_check") {
            assert!(matches!(i.mult, TableExpr::Loc(7)));
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
            trans[3..].iter().all(|g| t.gate_reads_next(g)),
            "every comparator branch must compare against the SUCCESSOR"
        );
        // …and the map-absent comparator does NOT, because it compares within one row.
        let ma = map_absent_table_air();
        assert!(ma.gates.iter().all(|g| !ma.gate_reads_next(g)));
    }

    /// The universal memory op-log emission decodes at the deployed shape. The counts are derived
    /// here from the layout constants (one 30-bit decomposition of `decomp_cols(30)` columns) rather
    /// than transcribed from the Lean `#guard`, so the two sides are independent.
    #[test]
    fn the_umemory_emission_decodes_at_the_deployed_shape() {
        let t = umemory_table_air();
        assert_eq!(t.name, "dregg-ir2-umemory-v1");

        // Width: the 8-felt `ir2_umem_log` tuple + serial + is_real + gap + its limb block
        // + the nullifier indicator and its inverse witness.
        let dc = crate::descriptor_ir2::decomp_cols_pub(30);
        assert_eq!(dc, 10);
        assert_eq!(t.width, 8 + 1 + 1 + 1 + dc + 2);
        assert_eq!(t.width, 23);

        // Gates: 5 booleans + the real prefix + the serial anchor + the serial increment
        // + 2 read-discipline (the `Option` is a PAIR) + 2 canonical-`none` + the gap definition
        // + one decomposition (2 top bits + top recomp + whole recomp) + 2 nullifier-forcing
        // + the insert-only tooth.
        assert_eq!(t.gates.len(), 5 + 1 + 1 + 1 + 2 + 2 + 1 + 4 + 2 + 1);
        assert_eq!(t.gates.len(), 20);
        assert_eq!(t.gate_count_sel(RowSel::All), 17);
        assert_eq!(t.gate_count_sel(RowSel::Transition), 2);
        assert_eq!(t.gate_count_sel(RowSel::First), 1);
        assert_eq!(t.gate_count_sel(RowSel::Last), 0);

        // Interactions: 7 full gap limbs + the DOMAIN nibble, the op log, the two Blum legs, the
        // closure query.
        assert_eq!(t.bus_count_on("ir2_byte"), 7 + 1);
        assert_eq!(t.bus_count_on("ir2_umem_log"), 1);
        assert_eq!(t.bus_count_on("ir2_umem_check"), 2);
        assert_eq!(t.bus_count_on("ir2_umem_addrs"), 1);
        assert_eq!(t.interactions.len(), 12);
    }

    /// ⚑ **THE TWO SIDES OF `ir2_umem_addrs`, PINNED FROM BOTH ENDS AT ONCE.** The universal op log
    /// QUERIES the declared-address table; BOTH boundary forms SERVE it. A swap on either side
    /// leaves every gate green — there is no gate involved — so it is asserted here against the
    /// three decoded emissions together.
    #[test]
    fn the_umem_op_log_queries_the_address_table_both_boundaries_serve() {
        let um = umemory_table_air();
        assert_eq!(um.bus_count_op("ir2_umem_addrs", BusOp::Query), 1);
        assert_eq!(um.bus_count_op("ir2_umem_addrs", BusOp::Provide), 0);
        for bnd in [umem_boundary_cohort_table_air(), umem_boundary_table_air()] {
            assert_eq!(bnd.bus_count_op("ir2_umem_addrs", BusOp::Provide), 1);
            assert_eq!(bnd.bus_count_op("ir2_umem_addrs", BusOp::Query), 0);
        }

        // The Blum pair: this op PUBLISHES its own `Option` image at its OWN serial and CONSUMES
        // the prior image at the CLAIMED one.
        let send = um
            .interactions
            .iter()
            .find(|i| i.bus == "ir2_umem_check" && i.op == BusOp::Send)
            .expect("one publish");
        assert_eq!(send.tuple.len(), 5, "(domain, key, present, value, serial)");
        assert!(matches!(send.tuple[4], TableExpr::Loc(8)), "UM_SERIAL");
        let recv = um
            .interactions
            .iter()
            .find(|i| i.bus == "ir2_umem_check" && i.op == BusOp::Receive)
            .expect("one consume");
        assert!(
            matches!(recv.tuple[4], TableExpr::Loc(6)),
            "the CLAIMED prior serial"
        );
        // Every multiset/log/closure leg rides at `is_real` (column 9), which is what makes a pad
        // row declare NOTHING — and is exactly the containment the pad-row refutation rests on.
        for i in um.interactions.iter().filter(|i| i.bus != "ir2_byte") {
            assert!(matches!(i.mult, TableExpr::Loc(9)), "{} leg", i.bus);
        }
        // …while both byte queries (gap limbs and the domain nibble) are the UNCOUNTED variant, so
        // a pad row's DOMAIN is range-bound even though nothing else about a pad is.
        for i in um.interactions.iter().filter(|i| i.bus == "ir2_byte") {
            assert!(matches!(i.mult, TableExpr::Const(1)));
        }
    }

    /// The map reconciliation emission decodes at the deployed shape. ⚑ Every count is DERIVED
    /// here from the deployed layout constants (`HEAP_TREE_DEPTH`, `CHIP_OUT_LANES`,
    /// `decomp_cols_pub(27)`) and the width is compared against the REAL `MAP_WIDTH` the trace
    /// producer writes — two independent sources, not a transcription of the Lean `#guard`.
    ///
    /// ⚠ This is also where the stale Rust comment gets caught: `descriptor_ir2.rs` annotates
    /// `MAP_WIDTH` `// 897`, and the constant is **898**. Nothing read the comment, so nothing was
    /// wrong; the assertion below is what makes the two sources have to agree.
    #[test]
    fn the_map_ops_emission_decodes_at_the_deployed_shape() {
        let t = map_ops_table_air();
        assert_eq!(t.name, "dregg-ir2-map-ops-v1");

        let depth = crate::heap_root::HEAP_TREE_DEPTH;
        let lanes = crate::descriptor_ir2::CHIP_OUT_LANES;
        let dc = crate::descriptor_ir2::decomp_cols_pub(27);
        assert_eq!((depth, lanes, dc), (16, 8, 10));
        // The width against the DEPLOYED constant the witness producer sizes its row from.
        assert_eq!(t.width, crate::descriptor_ir2::MAP_WIDTH);
        assert_eq!(t.width, 898);

        // Gates: the row guard + the op membership + DEPTH PATH1 direction booleans + the three
        // AAFI selector pins + the read discipline + DEPTH PATH2 direction booleans + three
        // canonical splits (9 each) + two comparators (9 each) + the LANES empty-slot pins.
        assert_eq!(
            t.gates.len(),
            1 + 1 + depth + 3 + 1 + depth + 3 * 9 + 2 * 9 + lanes
        );
        assert_eq!(t.gates.len(), 91);
        // ⚑ Purely row-local: a reconciliation row is a complete statement about ONE map op, and
        // the log ORDER lives in the `ir2_map_log` multiset rather than in an adjacency gate.
        assert_eq!(t.gate_count_sel(RowSel::All), 91);
        assert_eq!(t.gate_count_sel(RowSel::Transition), 0);
        assert_eq!(t.gate_count_sel(RowSel::First), 0);
        assert_eq!(t.gate_count_sel(RowSel::Last), 0);

        // Interactions: three arity-3 leaf absorbs + the two interleaved PATH1 chains + three
        // canonical-split query blocks (7 each) + two comparator query blocks (7 each) + the
        // updated-low absorb + three AAFI folds of DEPTH levels each + the gathered log.
        assert_eq!(
            t.interactions.len(),
            3 + 2 * depth + 3 * 7 + 2 * 7 + 1 + 3 * depth + 1
        );
        assert_eq!(t.interactions.len(), 120);
        assert_eq!(t.bus_count_on("ir2_p2"), 4 + 5 * depth);
        assert_eq!(t.bus_count_on("ir2_p2"), 84);
        assert_eq!(t.bus_count_on("ir2_byte"), 35);
        assert_eq!(t.bus_count_on("ir2_map_log"), 1);

        // ⚑ SIDES. This table SERVES nothing: every chip and byte leg is a QUERY, and the log is a
        // RECEIVE. A swap leaves every gate green and makes the bus unsatisfiable in one direction
        // and vacuous in the other.
        assert_eq!(t.bus_count_op("ir2_p2", BusOp::Query), 84);
        assert_eq!(t.bus_count_op("ir2_p2", BusOp::Provide), 0);
        assert_eq!(t.bus_count_op("ir2_byte", BusOp::Query), 35);
        assert_eq!(t.bus_count_op("ir2_byte", BusOp::Provide), 0);
        assert_eq!(t.bus_count_op("ir2_map_log", BusOp::Receive), 1);
        assert_eq!(t.bus_count_op("ir2_map_log", BusOp::Send), 0);
    }

    /// ⚑ THE TWO TABLES THAT RECEIVE ON `ir2_map_log`, pinned together. `MapOps` receives the
    /// read / write / insert / aafi-insert sub-log and `MapAbsent` the `absent` one; the main
    /// instance SENDs both. The 19-felt tuple shape must agree across all three or the multiset
    /// cannot balance, and no gate on either table would notice.
    #[test]
    fn the_map_log_is_received_by_two_tables_at_one_tuple_shape() {
        let ops = map_ops_table_air();
        let absent = map_absent_table_air();
        for t in [&ops, &absent] {
            assert_eq!(t.bus_count_op("ir2_map_log", BusOp::Receive), 1);
            assert_eq!(t.bus_count_op("ir2_map_log", BusOp::Send), 0);
            let recv = t
                .interactions
                .iter()
                .find(|i| i.bus == "ir2_map_log")
                .expect("one receive");
            // [root8, key, value, op, new_root8] — the Phase H-HEAP-8 19-felt log entry.
            assert_eq!(
                recv.tuple.len(),
                2 * crate::descriptor_ir2::CHIP_OUT_LANES + 3
            );
            assert_eq!(recv.tuple.len(), 19);
        }
        // ⚠ The op code: `MapAbsent` pins it to the CONSTANT 2, `MapOps` reads a COLUMN — which is
        // exactly why `op = 2` has to be UNSAT on the map-ops side (Lean `the_absent_op_is_unsat`)
        // rather than merely unused. Two tables receiving the same tuple at the same op code would
        // let one launder the other's entry.
        let a_recv = absent
            .interactions
            .iter()
            .find(|i| i.bus == "ir2_map_log")
            .unwrap();
        assert!(matches!(a_recv.tuple[10], TableExpr::Const(2)));
        let o_recv = ops
            .interactions
            .iter()
            .find(|i| i.bus == "ir2_map_log")
            .unwrap();
        assert!(matches!(o_recv.tuple[10], TableExpr::Loc(10)));
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

    /// ⚑ **THE PREPROCESSED BOUND IS IN ITS OWN SPACE, and it REFUSES.** A `prep` index past the
    /// declared `prep_width` is rejected at DECODE, not left to panic inside p3's evaluator on a
    /// slice that is one column short.
    ///
    /// ⚠ Both directions of the confusion are exercised: widening `width` does not launder an
    /// out-of-range `prep`, and the two spaces are checked separately.
    #[test]
    fn an_out_of_range_prep_column_is_refused_at_decode() {
        let ok = "{\"name\":\"t\",\"kind\":\"table_air\",\"ir\":2,\"width\":1,\
                  \"prep_width\":2,\"defs\":[],\"gates\":[{\"sel\":\"all\",\"body\":\
                  {\"t\":\"prep\",\"c\":1}}],\"interactions\":[]}";
        let t = parse_table_air(ok).expect("an in-range prep column decodes");
        assert_eq!(t.prep_width, 2);
        assert_eq!(t.gates[0].body, TableExpr::Prep(1));

        // …and one column past the declaration is REFUSED, even though `width` is irrelevant to it.
        let bad = ok.replace("\"c\":1}}]", "\"c\":2}}]");
        let err = parse_table_air(&bad).expect_err("prep column 2 of a prep_width-2 table");
        assert!(err.contains("preprocessed column 2"), "{err}");

        // A `prep` inside a DEFINITION is bounded too — the case a check that only walked gates and
        // interactions would miss, because a `Shr` hides it from every syntactic scan downstream.
        let in_def = ok
            .replace("\"defs\":[]", "\"defs\":[{\"t\":\"prep\",\"c\":7}]")
            .replace("{\"t\":\"prep\",\"c\":1}}]", "{\"t\":\"shr\",\"i\":0}}]");
        let err = parse_table_air(&in_def).expect_err("a definition may not read past prep_width");
        assert!(err.contains("definition 0"), "{err}");
    }

    /// ⚑ **THE EXACT-PUBLIC FAMILY DECODES, and every member is `check`ed exactly as a singleton
    /// is.** The family is the eleventh port's artifact and the only one that is a JSON ARRAY.
    #[test]
    fn the_exact_public_family_decodes_at_every_arity() {
        let family = exact_public_table_air_family();
        assert_eq!(family.len(), 64);
        for (i, t) in family.iter().enumerate() {
            let arity = i + 1;
            assert_eq!(t.name, format!("dregg-ir2-exact-public-a{arity}-v1"));
            assert_eq!(t.width, 1);
            assert_eq!(t.prep_width, arity + 2);
            assert_eq!(t.gates.len(), 1);
            assert_eq!(t.interactions.len(), 1);
            // The pin is degree 1 and the served leg degree 2, at EVERY arity — which is why
            // `ir2_degree_budget` is unchanged by this port.
            assert_eq!(t.max_degree(), 2, "arity {arity}");
        }
    }

    /// …and the family decoder is fail-closed on the shapes a hand-edited artifact would take.
    #[test]
    fn a_malformed_family_is_refused() {
        assert!(parse_table_air_family("{}").is_err(), "not an array");
        assert!(parse_table_air_family("[]").is_err(), "no members");
        assert!(parse_table_air_family("[1]").is_err(), "not an object");
        // A truncated member is refused rather than silently dropped.
        let one = &EXACT_PUBLIC_TABLE_AIR_FAMILY_JSON[..EXACT_PUBLIC_TABLE_AIR_FAMILY_JSON.len() / 2];
        assert!(parse_table_air_family(one).is_err(), "truncated");
    }
}
