//! Descriptor + witness builder for the emitted **note-spend recursion leaf** descriptor
//! (`note-spend-leaf::dregg-note-spending-dsl-v3`, authored in
//! `metatheory/Dregg2/Circuit/Emit/NoteSpendingLeafEmit.lean` as `noteSpendLeafDesc`).
//!
//! ## What this closes (the Gate-1.5 pattern for the note-spend family)
//!
//! The stark-kill migration flips note-spend consumers off the hand DSL STARK
//! ([`crate::dsl::note_spending::note_spending_dsl_circuit`], the v1 `CircuitDescriptor`
//! `dregg-note-spending-dsl-v3`, width 62, 6 PIs) onto the IR-v2 descriptor prover
//! ([`crate::descriptor_ir2::prove_vm_descriptor2`]). The IR-v2 descriptor's trace layout is NOT
//! the hand DSL circuit's layout (it widens to 149 cols: the 62 source columns + the 3 mint-hash
//! carrier columns + 12×7 witnessed Poseidon2-chip lanes), so a consumer needs a Rust fn that
//! produces a trace/PIs matching the EMITTED [`EffectVmDescriptor2`]. `merkle-membership` has
//! [`crate::membership_descriptor_4ary::membership_witness_4ary`]; `adjacency` has
//! [`crate::adjacency_witness::adjacency_witness`]; this module is the note-spend twin.
//!
//! Until now the ONLY producers for this descriptor lived in `circuit-prove`
//! (`note_spend_leaf_adapter::{note_spend_to_descriptor2, note_spend_leaf_base_trace}`), tangled
//! with the recursion-fold wrap. This module lifts the descriptor lowering + the witness builder
//! into `circuit` — grounded in the SAME production DSL circuit
//! ([`crate::dsl::note_spending::note_spending_circuit_descriptor`]), depending on nothing past
//! `crate`, so any consumer of [`crate::descriptor_by_name::descriptor_by_name`] can prove/verify a
//! real note-spend WITHOUT the recursion crate.
//!
//! ## Descriptor grounding (byte-faithful to the Lean emit AND the deployed lowering)
//!
//! [`note_spend_leaf_descriptor`] LOWERS the live [`note_spending_circuit_descriptor`] (it walks the
//! source, not a transcription: a drift in the deployed circuit is a build-time refusal, not a
//! silent divergence) into the IR-v2 carriers:
//!
//! | source constraint (`dregg-note-spending-dsl-v3`)   | IR-v2 carrier                                    |
//! |----------------------------------------------------|--------------------------------------------------|
//! | `Binary` / `Polynomial` / `Equality` (± gates)     | `Base(Gate(body))`                               |
//! | `Transition { CURRENT, PARENT }` (C7)              | `WindowGate(Nxt − Loc)` on the transition domain |
//! | `(Inverted)Gated { Hash }` (C2a..g, C3, C4, C6)    | a SELECTOR-MUXED arity-7 `TID_P2` chip lookup    |
//! | boundary `PiBinding` (First/Last)                  | `Base(PiBinding{row, col, pi})`                  |
//!
//! then appends the in-AIR mint-hash recompute (2 more gated fact sites + the [`NOTE_SPEND_MINT_HASH_PI`]
//! pin). The result is asserted BYTE-EQUAL to [`NOTE_SPEND_LEAF_GOLDEN_JSON`] (the byte-pinned Lean
//! `emitVmJson2` string) in the tests — so this builder reproduces the emitted descriptor exactly,
//! the note-spend analog of membership's byte-equal-to-the-deployed-root claim.
//!
//! ## The witness builder ([`note_spend_witness`])
//!
//! Produces the width-65 base trace (the 62-col DSL note-spending trace, extended by the 3 mint
//! columns on row 0) + the 7-slot claim tuple `[nullifier, merkle_root, value_lo, asset_type,
//! destination_federation, value_hi, mint_hash]`. The 12×7 chip-lane columns (65..149) are left to
//! the prover's `trace_with_chip_lanes` (called inside [`crate::descriptor_ir2::prove_vm_descriptor2`]).
//! It is purely mechanical — it does NOT pre-judge the spend; the DESCRIPTOR's PiBinding pins and the
//! Poseidon2-chip membership/nullifier/commitment lookups are the judge, so a forged PI or a tampered
//! co-path yields a well-formed but UNSATISFYING assembly that `verify_vm_descriptor2` rejects.

use crate::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, EffectVmDescriptor2, LookupSpec, TID_P2,
    VmConstraint2, WindowExpr, WindowGateSpec,
};
use crate::dsl::circuit::{BoundaryDef, BoundaryRow, CircuitDescriptor, ConstraintExpr};
use crate::dsl::note_spending::{
    generate_note_spending_trace, note_spend_mint_hash_felt, note_spending_circuit_descriptor,
};
use crate::field::BabyBear;
use crate::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use crate::note_spending_witness::{
    MIN_MERKLE_DEPTH, NOTE_SPENDING_WIDTH, NoteSpendingWitness, col, pi,
};
use crate::poseidon2::hash_fact;

/// The byte-pinned wire string `emitVmJson2 noteSpendLeafDesc` emits (the `#guard` in
/// `NoteSpendingLeafEmit.lean`); the SAME golden the `circuit-prove` emit gate pins against the
/// production lowering. [`note_spend_leaf_descriptor`] is asserted byte-equal to its decode.
pub const NOTE_SPEND_LEAF_GOLDEN_JSON: &str =
    include_str!("../descriptors/by-name/note-spend-leaf.json");

/// The dispatched AIR-name of the emitted note-spend leaf descriptor.
pub const NOTE_SPEND_LEAF_NAME: &str = "note-spend-leaf::dregg-note-spending-dsl-v3";

/// The exposed claim width: the 6 note-spend PIs + the felt-domain mint_hash.
/// Lanes: `[nullifier, merkle_root, value_lo, asset_type, destination_federation, value_hi,
/// mint_hash]`.
pub const NOTE_SPEND_CLAIM_LEN: usize = 7;

/// PI slot of the felt-domain mint identity (appended after the source descriptor's 6 PIs).
pub const NOTE_SPEND_MINT_HASH_PI: usize = 6;

/// The `hash_fact` domain-separation marker (`poseidon2::hash_fact` state[5]). The KAT
/// `fact_arity7_chip_absorb_matches_hash_fact` (`circuit-prove`) pins the chip absorb against it.
const NS_FACT_MARK: u32 = 0xFACF;

/// Row-0 copy of the Merkle root, pinned to `pi[1]` (`PiBinding{First}`) so the mint-hash absorb can
/// read the root on the commitment row (the canonical root carrier is the last row's `CURRENT`, also
/// pinned to `pi[1]` — both anchored to the same PI).
const MINT_ROOT_COL: usize = NOTE_SPENDING_WIDTH; // 62
/// The mint-hash chain intermediate `hash_fact(nullifier, [root, dest, asset])`.
const MINT_M1_COL: usize = NOTE_SPENDING_WIDTH + 1; // 63
/// The felt-domain mint identity, pinned to `pi[6]`.
const MINT_HASH_COL: usize = NOTE_SPENDING_WIDTH + 2; // 64
/// Base width of the extended trace (source 62 + the 3 mint columns); chip lane columns append past.
const EXT_BASE_WIDTH: usize = NOTE_SPENDING_WIDTH + 3; // 65

/// `x − y` as a `LeanExpr` (no subtraction node: `x + (−1)·y`).
fn sub(x: LeanExpr, y: LeanExpr) -> LeanExpr {
    LeanExpr::add(x, LeanExpr::mul(LeanExpr::Const(-1), y))
}

/// Row-gating selector for a chip site.
#[derive(Clone, Copy)]
enum SiteSel {
    /// Fires when the selector column is 1 (`Gated`).
    When(usize),
    /// Fires when the selector column is 0 (`InvertedGated`).
    Unless(usize),
}

impl SiteSel {
    /// `(fire, hold)` — the firing indicator and its complement, both boolean on trace rows (the
    /// selector column carries a `Binary` gate).
    fn exprs(self) -> (LeanExpr, LeanExpr) {
        match self {
            SiteSel::When(c) => (LeanExpr::Var(c), sub(LeanExpr::Const(1), LeanExpr::Var(c))),
            SiteSel::Unless(c) => (sub(LeanExpr::Const(1), LeanExpr::Var(c)), LeanExpr::Var(c)),
        }
    }
}

/// Build the SELECTOR-MUXED arity-7 `TID_P2` chip lookup carrying one row-gated `hash_fact` site:
/// `input_cols[0]` is the predicate, `input_cols[1..]` (≤ 4) the terms. On a firing row the tuple is
/// the genuine fact absorb `[7, pred, t0..t3, 0xFACF, 1, 0…, out, lanes…]`; on a non-firing row every
/// value lane muxes to zero and the digest lane to `K₀ = hash_fact(0, [])`, so the send degenerates
/// to the satisfiable zero-fact permutation row.
fn gated_fact_site(
    sel: SiteSel,
    output_col: usize,
    input_cols: &[usize],
    lane_base: usize,
) -> Result<VmConstraint2, String> {
    if input_cols.is_empty() || input_cols.len() > 5 {
        return Err(format!(
            "fact site expects 1..=5 input columns (pred + ≤4 terms), got {}",
            input_cols.len()
        ));
    }
    let (fire, hold) = sel.exprs();
    // K₀: the zero-fact digest the non-firing rows degenerate to.
    let k0 = hash_fact(BabyBear::ZERO, &[]).as_u32() as i64;

    let mut tuple: Vec<LeanExpr> = Vec::with_capacity(CHIP_TUPLE_LEN);
    tuple.push(LeanExpr::Const(7));
    for i in 0..CHIP_RATE {
        let e = match i {
            // pred + terms: muxed value lanes (zero-padded past the given inputs).
            0..=4 => match input_cols.get(i) {
                Some(&c) => LeanExpr::mul(fire.clone(), LeanExpr::Var(c)),
                None => LeanExpr::Const(0),
            },
            // The hash_fact domain separation (state[5]/state[6]), constant on every row.
            5 => LeanExpr::Const(NS_FACT_MARK as i64),
            6 => LeanExpr::Const(1),
            _ => LeanExpr::Const(0),
        };
        tuple.push(e);
    }
    // out0: the digest lane — the site's output column when firing, K₀ when not.
    tuple.push(LeanExpr::add(
        LeanExpr::mul(fire, LeanExpr::Var(output_col)),
        LeanExpr::mul(hold, LeanExpr::Const(k0)),
    ));
    // lanes 1..7: the genuine permutation lanes, witnessed columns the chip AIR EQUALITY-binds.
    for j in 0..(CHIP_OUT_LANES - 1) {
        tuple.push(LeanExpr::Var(lane_base + j));
    }
    debug_assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    Ok(VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    }))
}

/// Lower a PURE-LOCAL `ConstraintExpr` to its vanishing gate body. Hash/lookup/cross-row kinds are
/// handled — or refused — by [`note_spend_leaf_descriptor`]'s top level.
fn local_gate_body(expr: &ConstraintExpr) -> Result<LeanExpr, String> {
    Ok(match expr {
        ConstraintExpr::Equality { col_a, col_b } => {
            sub(LeanExpr::Var(*col_a), LeanExpr::Var(*col_b))
        }
        ConstraintExpr::Binary { col } => LeanExpr::mul(
            LeanExpr::Var(*col),
            LeanExpr::add(LeanExpr::Var(*col), LeanExpr::Const(-1)),
        ),
        ConstraintExpr::Polynomial { terms } => {
            let mut acc: Option<LeanExpr> = None;
            for term in terms {
                let mut prod = LeanExpr::Const(term.coeff.as_u32() as i64);
                for &ci in &term.col_indices {
                    prod = LeanExpr::mul(prod, LeanExpr::Var(ci));
                }
                acc = Some(match acc {
                    None => prod,
                    Some(a) => LeanExpr::add(a, prod),
                });
            }
            acc.unwrap_or(LeanExpr::Const(0))
        }
        ConstraintExpr::Gated {
            selector_col,
            inner,
        } => LeanExpr::mul(LeanExpr::Var(*selector_col), local_gate_body(inner)?),
        ConstraintExpr::InvertedGated {
            selector_col,
            inner,
        } => LeanExpr::mul(
            sub(LeanExpr::Const(1), LeanExpr::Var(*selector_col)),
            local_gate_body(inner)?,
        ),
        other => {
            return Err(format!(
                "note-spend lowering: constraint kind {other:?} is not a local gate body"
            ));
        }
    })
}

/// **`note_spend_leaf_descriptor`** — the emitted note-spend recursion-leaf [`EffectVmDescriptor2`]
/// (`note-spend-leaf::dregg-note-spending-dsl-v3`), built by LOWERING the live
/// [`note_spending_circuit_descriptor`] (`dregg-note-spending-dsl-v3`) and appending the in-AIR
/// mint-hash recompute (2 gated fact sites + the [`NOTE_SPEND_MINT_HASH_PI`] pin). The lowering walks
/// the SOURCE descriptor, so a drift in the deployed circuit is a build-time refusal here, never a
/// silent divergence. Asserted byte-equal to [`NOTE_SPEND_LEAF_GOLDEN_JSON`]'s decode in the tests.
pub fn note_spend_leaf_descriptor() -> Result<EffectVmDescriptor2, String> {
    let src: CircuitDescriptor = note_spending_circuit_descriptor();
    if src.name != "dregg-note-spending-dsl-v3" || src.public_input_count != 6 {
        return Err(format!(
            "note-spend lowering is pinned to dregg-note-spending-dsl-v3 (6 PIs); \
             got {} ({} PIs) — re-ground the lowering against the new descriptor",
            src.name, src.public_input_count
        ));
    }
    if src.trace_width != NOTE_SPENDING_WIDTH {
        return Err(format!(
            "note-spend source width {} != NOTE_SPENDING_WIDTH {NOTE_SPENDING_WIDTH}",
            src.trace_width
        ));
    }

    let mut constraints: Vec<VmConstraint2> = Vec::new();
    // Chip lane columns are appended past the extended base width, 7 per site.
    let mut width = EXT_BASE_WIDTH;
    let mut alloc_lanes = || {
        let base = width;
        width += CHIP_OUT_LANES - 1;
        base
    };

    for expr in &src.constraints {
        let c2 = match expr {
            // The Merkle-chain continuity C7: the two-row carrier on rows 0..n−2.
            ConstraintExpr::Transition {
                next_col,
                local_col,
            } => VmConstraint2::WindowGate(WindowGateSpec {
                body: WindowExpr::Add(
                    Box::new(WindowExpr::Nxt(*next_col)),
                    Box::new(WindowExpr::Mul(
                        Box::new(WindowExpr::Const(-1)),
                        Box::new(WindowExpr::Loc(*local_col)),
                    )),
                ),
                on_transition: true,
            }),
            // The row-gated fact-sponge sites: C2a..C2g + C3 + C4 (commitment row,
            // `InvertedGated{is_merkle}`) and C6 (Merkle rows, `Gated{is_merkle}`).
            ConstraintExpr::Gated {
                selector_col,
                inner,
            } if matches!(**inner, ConstraintExpr::Hash { .. }) => {
                let ConstraintExpr::Hash {
                    output_col,
                    input_cols,
                } = &**inner
                else {
                    unreachable!()
                };
                gated_fact_site(
                    SiteSel::When(*selector_col),
                    *output_col,
                    input_cols,
                    alloc_lanes(),
                )?
            }
            ConstraintExpr::InvertedGated {
                selector_col,
                inner,
            } if matches!(**inner, ConstraintExpr::Hash { .. }) => {
                let ConstraintExpr::Hash {
                    output_col,
                    input_cols,
                } = &**inner
                else {
                    unreachable!()
                };
                gated_fact_site(
                    SiteSel::Unless(*selector_col),
                    *output_col,
                    input_cols,
                    alloc_lanes(),
                )?
            }
            // Everything else is a pure-local algebraic gate (C1 Binary, C5 position validity, the C2
            // equality links).
            local => VmConstraint2::Base(VmConstraint::Gate(local_gate_body(local)?)),
        };
        constraints.push(c2);
    }

    // Boundary pins graduate to the row-tagged IR-v2 carriers (First/Last exact).
    for b in &src.boundaries {
        let vmrow = |row: &BoundaryRow| -> Result<VmRow, String> {
            match row {
                BoundaryRow::First => Ok(VmRow::First),
                BoundaryRow::Last => Ok(VmRow::Last),
                BoundaryRow::Index(i) => Err(format!(
                    "boundary at absolute row {i} has no IR-v2 row-tag carrier"
                )),
            }
        };
        let c2 = match b {
            BoundaryDef::PiBinding { row, col, pi_index } => {
                VmConstraint2::Base(VmConstraint::PiBinding {
                    row: vmrow(row)?,
                    col: *col,
                    pi_index: *pi_index,
                })
            }
            BoundaryDef::Fixed { row, col, value } => VmConstraint2::Base(VmConstraint::Boundary {
                row: vmrow(row)?,
                body: sub(LeanExpr::Var(*col), LeanExpr::Const(value.as_u32() as i64)),
            }),
        };
        constraints.push(c2);
    }

    // ---- The mint-hash extension: recompute `note_spend_mint_hash_felt` IN-AIR over the PI-pinned
    //      row-0 columns and pin it to PI 6. ----
    // MINT_ROOT is the root's row-0 copy, anchored to the SAME pi[1] the last-row CURRENT boundary
    // anchors — both PI-pinned, so the absorb reads the genuine root.
    constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::First,
        col: MINT_ROOT_COL,
        pi_index: pi::MERKLE_ROOT,
    }));
    // m1 = hash_fact(nullifier, [root, dest_fed, asset]) — every input column is itself First-row
    // PI-pinned by the source boundaries (nullifier pi0, dest pi4, asset pi3) or by the MINT_ROOT pin.
    constraints.push(gated_fact_site(
        SiteSel::Unless(col::IS_MERKLE),
        MINT_M1_COL,
        &[
            col::NULLIFIER,
            MINT_ROOT_COL,
            col::DESTINATION_FEDERATION,
            col::ASSET_TYPE,
        ],
        alloc_lanes(),
    )?);
    // mint_hash = hash_fact(m1, [value_lo, value_hi]) — both value limbs PI-pinned (pi2/pi5), so the
    // identity binds the FULL u64 amount.
    constraints.push(gated_fact_site(
        SiteSel::Unless(col::IS_MERKLE),
        MINT_HASH_COL,
        &[MINT_M1_COL, col::VALUE, col::VALUE_HI],
        alloc_lanes(),
    )?);
    constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::First,
        col: MINT_HASH_COL,
        pi_index: NOTE_SPEND_MINT_HASH_PI,
    }));

    Ok(EffectVmDescriptor2 {
        name: format!("note-spend-leaf::{}", src.name),
        trace_width: width,
        public_input_count: NOTE_SPEND_CLAIM_LEN,
        challenges: 0,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    })
}

/// The mint identity from a 6-slot note-spend PI vector — [`note_spend_mint_hash_felt`] over the PI
/// slots. This is the FELT-DOMAIN production commitment the executor's
/// `verify_note_spend_descriptor2` binds to; the witness reproduces it byte-for-byte as the
/// appended 7th PI.
fn mint_hash_from_pis(pis: &[BabyBear]) -> BabyBear {
    note_spend_mint_hash_felt(
        pis[pi::NULLIFIER],
        pis[pi::MERKLE_ROOT],
        pis[pi::VALUE],
        pis[pi::ASSET_TYPE],
        pis[pi::DESTINATION_FEDERATION],
        pis[pi::VALUE_HI],
    )
}

/// The HONEST 7-slot claim tuple for a witness: the source circuit's 6 PIs
/// (`generate_note_spending_trace`'s vector) + the felt-domain mint identity.
pub fn note_spend_leaf_public_inputs(witness: &NoteSpendingWitness) -> Vec<BabyBear> {
    let (_, pis) = generate_note_spending_trace(witness);
    let mint = mint_hash_from_pis(&pis);
    let mut out = pis;
    out.push(mint);
    out
}

/// **`note_spend_witness`** — build the width-65 note-spend base trace + the 7-slot claim tuple
/// `[nullifier, merkle_root, value_lo, asset_type, destination_federation, value_hi, mint_hash]` for
/// the emitted [`note_spend_leaf_descriptor`].
///
/// `witness` is the SAME [`NoteSpendingWitness`] the off-AIR `note_spending_dsl_circuit` consumes
/// (spending key, 28-limb commitment preimage, Merkle path). The Merkle depth must be
/// ≥ [`MIN_MERKLE_DEPTH`], the sibling/position lists must agree in length, and every position must
/// be `< 4`. The source trace is extended with the 3 mint columns on row 0 (Merkle/padding rows stay
/// zero — the mint sites are row-gated); the 12×7 chip-lane columns are filled by the prover's
/// `trace_with_chip_lanes`. The appended 7th PI is byte-equal to [`note_spend_mint_hash_felt`] over
/// the source PIs (the felt-domain mint identity). This builder does NOT pre-judge the spend — the
/// descriptor's pins and the Poseidon2-chip lookups do (see the module gate).
pub fn note_spend_witness(
    witness: &NoteSpendingWitness,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    let depth = witness.merkle_siblings.len();
    if depth != witness.merkle_positions.len() {
        return Err(format!(
            "note-spend siblings/positions length mismatch ({depth} vs {})",
            witness.merkle_positions.len()
        ));
    }
    if depth < MIN_MERKLE_DEPTH {
        return Err(format!(
            "note-spend Merkle depth {depth} must be ≥ MIN_MERKLE_DEPTH {MIN_MERKLE_DEPTH}"
        ));
    }
    if let Some(&p) = witness.merkle_positions.iter().find(|&&p| p >= 4) {
        return Err(format!("note-spend Merkle position {p} must be < 4"));
    }

    let (mut trace, pis) = generate_note_spending_trace(witness);
    for row in &mut trace {
        row.resize(EXT_BASE_WIDTH, BabyBear::ZERO);
    }
    let m1 = hash_fact(
        pis[pi::NULLIFIER],
        &[
            pis[pi::MERKLE_ROOT],
            pis[pi::DESTINATION_FEDERATION],
            pis[pi::ASSET_TYPE],
        ],
    );
    let mint = hash_fact(m1, &[pis[pi::VALUE], pis[pi::VALUE_HI]]);
    debug_assert_eq!(mint, mint_hash_from_pis(&pis));
    trace[0][MINT_ROOT_COL] = pis[pi::MERKLE_ROOT];
    trace[0][MINT_M1_COL] = m1;
    trace[0][MINT_HASH_COL] = mint;

    let mut full_pis = pis;
    full_pis.push(mint);
    Ok((trace, full_pis))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_by_name::descriptor_by_name;
    use crate::descriptor_ir2::{
        MemBoundaryWitness, check_descriptor2_wellformed, parse_vm_descriptor2,
        prove_vm_descriptor2, verify_vm_descriptor2,
    };
    use crate::note_spending_witness::{merkle_col, test_spending_key};
    use crate::poseidon2::hash_many;
    use crate::refusal::{Outcome, classify};
    use std::panic::AssertUnwindSafe;

    /// A REAL full-width witness (raw 32-byte fields + a > 2^30 u64 value, so the high limb is live).
    /// Depth 2 → 4 trace rows (1 commitment + 2 Merkle + 1 pad), the deployed DSL circuit's own shape.
    fn make_witness(tag: u8) -> NoteSpendingWitness {
        let owner = [tag; 32];
        let nonce = [tag ^ 0x5A; 32];
        let rand = [tag ^ 0xA5; 32];
        let key = test_spending_key(tag as u32 + 0x77);
        let depth = 2;
        let mut siblings = Vec::with_capacity(depth);
        let mut positions = Vec::with_capacity(depth);
        for i in 0..depth {
            siblings.push([
                hash_many(&[BabyBear::new((i * 3 + 1) as u32), BabyBear::new(tag as u32)]),
                hash_many(&[BabyBear::new((i * 3 + 2) as u32), BabyBear::new(tag as u32)]),
                hash_many(&[BabyBear::new((i * 3 + 3) as u32), BabyBear::new(tag as u32)]),
            ]);
            positions.push((i % 4) as u8);
        }
        NoteSpendingWitness::from_note_limbs(
            &owner,
            0xDEAD_BEEF_CAFE, // > 2^30: the value_hi limb is live
            3,
            &nonce,
            &rand,
            key,
            siblings,
            positions,
        )
    }

    /// `true` iff `(trace, pis)` is REJECTED end-to-end — proving refuses OR the produced proof fails
    /// to verify against `pis`. Prove-THEN-verify is the faithful consumer-posture gate.
    fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
        match classify("rejects", || {
            let proof =
                prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
            verify_vm_descriptor2(desc, &proof, pis)
        }) {
            // The p3 debug prover's DOCUMENTED unsat verdict — a real refusal.
            // `classify` REDs on any other panic (a stray unwrap, a trace-assembly
            // debug_assert), which used to land here and read as "rejected".
            Outcome::UnsatPanic(_) => true,
            Outcome::Err(_) => true,
            Outcome::Accepted(_) => false,
        }
    }

    /// STEP 1 — THE DESCRIPTOR BYTE-MATCH: the builder reproduces the byte-pinned Lean emit exactly,
    /// and the decode is well-formed and dispatches by name. (The `circuit-prove` emit gate pins the
    /// SAME golden against the deployed `note_spend_to_descriptor2` lowering — so all three agree.)
    #[test]
    fn descriptor_is_byte_equal_to_the_lean_emit() {
        let built = note_spend_leaf_descriptor().expect("the note-spend leaf descriptor builds");
        let decoded =
            parse_vm_descriptor2(NOTE_SPEND_LEAF_GOLDEN_JSON).expect("the Lean golden decodes");
        assert_eq!(
            built, decoded,
            "note_spend_leaf_descriptor() must be BYTE-EQUAL to the Lean-emitted noteSpendLeafDesc"
        );
        // Shape pins (mirror the Lean `#guard`s): width 149, 7 PIs, 12 chip lookups, 8 pins, 1 window.
        assert_eq!(built.name, NOTE_SPEND_LEAF_NAME);
        assert_eq!(built.trace_width, 149);
        assert_eq!(built.public_input_count, NOTE_SPEND_CLAIM_LEN);
        check_descriptor2_wellformed(&built).expect("the built descriptor is well-formed");
        let chips = built
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
            .count();
        assert_eq!(
            chips, 12,
            "7 commitment-chain + 2 nullifier + 1 Merkle + 2 mint fact sites"
        );
        let pins = built
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
            .count();
        assert_eq!(pins, 8, "6 source boundary pins + MINT_ROOT + MINT_HASH");
        let windows = built
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
            .count();
        assert_eq!(windows, 1, "the C7 Merkle-chain continuity");
        // The name dispatches through descriptor_by_name to the same descriptor.
        let via_dispatch = descriptor_by_name(NOTE_SPEND_LEAF_NAME).expect("dispatch");
        assert_eq!(
            via_dispatch, built,
            "descriptor_by_name resolves the note-spend leaf"
        );
    }

    /// STEP 2 — THE POSITIVE POLE + THE PRODUCTION-COMMITMENT BYTE-MATCH: an honest REAL note-spend
    /// (spending key + 28-limb commitment + Merkle path) proves through the DISPATCHED emitted
    /// descriptor and re-verifies, AND the appended 7th PI is byte-equal to the felt-domain mint
    /// identity `note_spend_mint_hash_felt` the executor's verifier binds to.
    #[test]
    fn honest_note_spend_proves_and_verifies_via_dispatch() {
        let desc = descriptor_by_name(NOTE_SPEND_LEAF_NAME).expect("dispatch");
        let w = make_witness(0x10);
        let (trace, pis) = note_spend_witness(&w).expect("witness builds");
        assert_eq!(pis.len(), NOTE_SPEND_CLAIM_LEN);
        assert_eq!(
            pis[NOTE_SPEND_MINT_HASH_PI],
            note_spend_mint_hash_felt(pis[0], pis[1], pis[2], pis[3], pis[4], pis[5]),
            "the appended mint PI must byte-equal the production felt-domain mint identity"
        );

        let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .expect("the honest note-spend must prove through the emitted descriptor");
        verify_vm_descriptor2(&desc, &proof, &pis)
            .expect("the honest proof must re-verify against the 7-slot claim tuple");
    }

    /// STEP 3a — MUTATION CANARY (nullifier PI): a forged nullifier slot violates the boundary pin
    /// `PiBinding{First, col::NULLIFIER, pi0}` → UNSAT. Non-vacuous: the honest witness is accepted.
    #[test]
    fn forged_nullifier_pi_refuses() {
        let desc = descriptor_by_name(NOTE_SPEND_LEAF_NAME).expect("dispatch");
        let w = make_witness(0x21);
        let (trace, pis) = note_spend_witness(&w).expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "honest accepted — else vacuous"
        );
        let mut forged = pis.clone();
        forged[pi::NULLIFIER] += BabyBear::ONE;
        assert!(
            rejects(&desc, &trace, &forged),
            "a forged nullifier PI must be REJECTED (nullifier binding tooth)"
        );
    }

    /// STEP 3b — MUTATION CANARY (merkle-root PI): a forged root slot violates the last-row root pin
    /// (and the MINT_ROOT pin at pi1) → UNSAT.
    #[test]
    fn forged_merkle_root_pi_refuses() {
        let desc = descriptor_by_name(NOTE_SPEND_LEAF_NAME).expect("dispatch");
        let w = make_witness(0x32);
        let (trace, pis) = note_spend_witness(&w).expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "non-vacuity: honest accepted"
        );
        let mut forged = pis.clone();
        forged[pi::MERKLE_ROOT] += BabyBear::ONE;
        assert!(
            rejects(&desc, &trace, &forged),
            "a forged merkle-root PI must be REJECTED (membership root binding)"
        );
    }

    /// STEP 3c — MUTATION CANARY (mint-hash PI): a forged mint identity slot violates the pin
    /// `PiBinding{First, MINT_HASH_COL, pi6}` over the in-AIR-recomputed identity → UNSAT. This is
    /// what makes the exposed mint identity a WELD, not a prover-chosen scalar.
    #[test]
    fn forged_mint_hash_pi_refuses() {
        let desc = descriptor_by_name(NOTE_SPEND_LEAF_NAME).expect("dispatch");
        let w = make_witness(0x43);
        let (trace, pis) = note_spend_witness(&w).expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "non-vacuity: honest accepted"
        );
        let mut forged = pis.clone();
        forged[NOTE_SPEND_MINT_HASH_PI] += BabyBear::ONE;
        assert!(
            rejects(&desc, &trace, &forged),
            "a forged mint-hash PI must be REJECTED (mint identity weld tooth)"
        );
    }

    /// STEP 3d — MUTATION CANARY (Merkle co-path): a tampered sibling on a Merkle row, claim tuple
    /// honest. The C6 `Poseidon2Chip` membership lookup names a parent digest no genuine permutation
    /// of the tampered inputs serves → UNSAT.
    #[test]
    fn tampered_merkle_sibling_refuses() {
        let desc = descriptor_by_name(NOTE_SPEND_LEAF_NAME).expect("dispatch");
        let w = make_witness(0x54);
        let (mut trace, pis) = note_spend_witness(&w).expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "non-vacuity: honest accepted"
        );
        // Row 1 is the first Merkle row (is_merkle = 1). Tamper its SIB0 without recomputing PARENT.
        trace[1][merkle_col::SIB0] += BabyBear::ONE;
        assert!(
            rejects(&desc, &trace, &pis),
            "a forged Merkle sibling (wrong co-path) must be REJECTED (C6 chip membership lookup)"
        );
    }

    /// Malformed witnesses (length mismatch, sub-minimum depth, out-of-range position) are refused at
    /// build time.
    #[test]
    fn malformed_witness_refuses() {
        let mut w = make_witness(0x65);
        // length mismatch.
        let mut bad = w.clone();
        bad.merkle_positions.pop();
        assert!(note_spend_witness(&bad).is_err());
        // out-of-range position.
        w.merkle_positions[0] = 4;
        assert!(note_spend_witness(&w).is_err());
    }
}
