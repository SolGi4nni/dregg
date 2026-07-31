//! Re-prove the REAL shielded-spend STARK as a RECURSION-FOLDABLE IR-v2 leaf —
//! the MARQUEE side-structure weld (EFFECTVM-SIDESTRUCTURE-ABI §4.1: the shielded
//! pool moves from BESIDE the effect-VM to a bound fold-leaf).
//!
//! ## Which STARK this re-proves (grounding)
//!
//! The membership+nullifier half of a shielded transfer is the DSL circuit
//! `dregg-shielded-spend-v1`
//! ([`crate::shielded::spend_circuit::shielded_spend_descriptor`], width 20, 3 PIs
//! `[nullifier, merkle_root, value_binding]`). It proves, in zero knowledge over the
//! hiding uni-STARK path: (C3/C5/C6) the input note commitment is a MEMBER of the
//! 4-ary Merkle tree at `merkle_root`, with the leaf CONSTRAINED to
//! `hash_fact(value,[asset,owner,randomness])` (the C6 value-theft tooth — you may
//! only spend a note whose full preimage you know); (C4) the nullifier is
//! `hash_fact(leaf, key[0..4])`, so a re-spend re-derives the same tag and the
//! nullifier-set gate rejects it; and (C7) a hiding `value_binding =
//! hash_fact(value,[randomness,0,0])` linking the STARK leaf value to the off-AIR
//! Pedersen leg. This is EXACTLY the PROVED half the Lean obligation
//! `Dregg2.Shielded.ClaimRefinement.shielded_spend_claim_refines` discharges
//! (membership ⇒ AUTHORIZED, fresh-nullifier ⇒ NO-DOUBLE-SPEND); per-asset value
//! CONSERVATION stays the ATTESTED off-AIR Pedersen/Ristretto residual, never
//! claimed in-AIR here.
//!
//! ## The claim tuple — `[nullifier, merkle_root, value_binding]`, byte-for-byte the PIs
//!
//! Unlike the bridge/note-spend leaf (which appends an in-AIR-recomputed `mint_hash`),
//! the shielded-spend circuit's OWN 3 public inputs ARE the committed claim
//! (`spend_circuit.rs:135-147`, `PUBLIC_INPUT_COUNT = 3`).
//! [`prove_shielded_spend_leaf_with_claim`] re-exposes all
//! `SHIELDED_SPEND_CLAIM_LEN = 3` lanes as its `expose_claim`, read from the leaf's
//! own FRI-bound descriptor PIs (via
//! [`crate::ivc_turn_chain::prove_descriptor_leaf_with_pi_slice_expose`]). Every lane
//! is a `PiBinding` on the descriptor:
//!   * lane 0 (`nullifier`)     — `PiBinding{First}` on `col::NULLIFIER`, itself the
//!     C4 chip-bound `hash_fact(leaf, key)`; the double-spend guard's connect target.
//!   * lane 1 (`merkle_root`)   — `PiBinding{Last}` on `col::PARENT`, the top of the
//!     C3/C5 membership chain; the turn's commitments-root connect target.
//!   * lane 2 (`value_binding`) — `PiBinding{First}` on `col::VALUE_BINDING`, the C7a
//!     ungated `hash_fact(value,[randomness,0,0])`; the ATTESTED link to the off-AIR
//!     Pedersen leg (NOT connected to an in-AIR root — see the binding node).
//!
//! ## The constraint lowering (`dregg-shielded-spend-v1` → `EffectVmDescriptor2`)
//!
//! | source constraint                                  | carrier                                                    |
//! |----------------------------------------------------|------------------------------------------------------------|
//! | `Binary` / `Polynomial` / `Gated{Equality}` (± gates) | `Base(Gate(body))` (the same local-gate lowering)       |
//! | `Transition { CURRENT, PARENT }` (C5)              | `WindowGate(Nxt − Loc)` on the transition domain           |
//! | UNGATED `Hash` (C3 Merkle, C6a leaf-commit, C7a value-binding) | an ALWAYS-firing arity-7 `TID_P2` chip lookup   |
//! | `Gated{ Hash }` (C4 nullifier, `is_leaf`)          | a SELECTOR-MUXED arity-7 `TID_P2` chip lookup              |
//! | boundary `PiBinding` (First/Last)                  | `Base(PiBinding{row, col, pi})` — row-tag exact            |
//!
//! **The fact-sponge carrier.** A DSL `ConstraintExpr::Hash` is `hash_fact(pred, terms)`:
//! ONE Poseidon2 permutation seeded `st[0]=pred, st[1..5]=terms, st[5]=FACT_MARK(0xFACF),
//! st[6]=1`. The chip's arity-7 row seeds `st[0..7]` verbatim, so the faithful carrier is
//! an arity-7 chip lookup with inputs `[pred, t0..t3, Const(0xFACF), Const(1)]` — the same
//! KAT-pinned equivalence the note-spend adapter rests on
//! (`fact_arity7_chip_absorb_matches_hash_fact`).
//!
//! **Gated vs ungated.** The shielded circuit differs from note-spend in that its
//! Merkle/leaf-commit/value-binding hashes are UNGATED (they fire on EVERY row; the
//! forward-chained padding is authored so the hash holds throughout,
//! `spend_circuit.rs:11-21,483-573`). So those sites use [`SiteSel::Always`] — no mux,
//! the tuple IS the genuine absorb on every row. The nullifier hash (C4) is
//! `Gated{is_leaf}`, so it uses [`SiteSel::When`] and muxes to the satisfiable
//! zero-fact permutation on non-leaf rows.
//!
//! ## THE PROVED / ATTESTED split (honest grade)
//!
//! This leaf realizes the **PROVED-for-membership+nullifier** half: the folded claim is
//! welded (through the FRI-bound descriptor PIs + the chip-recomputed hash chains) to a
//! genuine key-knowledge + membership + fresh-nullifier execution. Per-asset
//! **conservation is ATTESTED** — the hidden `Σvᵢ_in = Σvᵢ_out` rides the off-AIR
//! Pedersen excess + Bulletproof range proof (`shielded/mod.rs:29-41`); lane 2
//! (`value_binding`) binds only a Poseidon2 COMMITMENT to the leaf value, the DECO
//! posture. Lifting conservation to PROVED is the value-commitments-in-AIR weld
//! (ABI §4.1(c)), a named-open crypto seam — NOT claimed here.

use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, EffectVmDescriptor2, LookupSpec, MemBoundaryWitness,
    TID_P2, UMemBoundaryWitness, VmConstraint2, WindowExpr, WindowGateSpec,
    prove_vm_descriptor2_for_config,
};
use dregg_circuit::dsl::circuit::{BoundaryDef, BoundaryRow, CircuitDescriptor, ConstraintExpr};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use dregg_circuit::poseidon2::hash_fact;

use p3_recursion::{ProveNextLayerParams, RecursionOutput};

use crate::ivc_turn_chain::{
    prove_descriptor_leaf_rotated_with_config, prove_descriptor_leaf_with_pi_slice_expose,
};
use crate::joint_turn_aggregation::JointAggError;
use crate::plonky3_recursion_impl::recursive::DreggRecursionConfig;
use crate::shielded::spend_circuit::{
    self, ShieldedSpendWitness, generate_shielded_spend_trace, shielded_spend_descriptor,
};

/// Extension degree of the recursion config's PCS (the BabyBear-quartic stack).
const D: usize = 4;

/// The `hash_fact` domain-separation marker (`poseidon2::hash_fact` state[5]).
/// Kept file-local (the descriptor_ir2 twin is private); the KAT test
/// `fact_arity7_chip_absorb_matches_hash_fact` (note-spend adapter) pins the two.
const NS_FACT_MARK: u32 = 0xFACF;

/// The exposed claim width: the shielded-spend circuit's own 3 PIs
/// `[nullifier, merkle_root, value_binding]` (`spend_circuit.rs:135-147`).
pub const SHIELDED_SPEND_CLAIM_LEN: usize = spend_circuit::PUBLIC_INPUT_COUNT;

/// Base width of the extended trace = the source width (no appended columns; the
/// shielded circuit's PIs already ARE the claim). Chip lane columns are allocated
/// past this.
const BASE_WIDTH: usize = spend_circuit::WIDTH;

/// `x − y` as a `LeanExpr` (no subtraction node: `x + (−1)·y`).
fn sub(x: LeanExpr, y: LeanExpr) -> LeanExpr {
    LeanExpr::add(x, LeanExpr::mul(LeanExpr::Const(-1), y))
}

/// Row-gating selector for a chip fact site.
#[derive(Clone, Copy)]
enum SiteSel {
    /// Fires on EVERY row (an ungated `Hash`; no mux — the tuple is the genuine
    /// absorb everywhere, satisfiable because the trace carries the preimage
    /// constant per row).
    Always,
    /// Fires when the selector column is 1 (`Gated`).
    When(usize),
    /// Fires when the selector column is 0 (`InvertedGated`).
    Unless(usize),
}

impl SiteSel {
    /// `(fire, hold)` — the firing indicator and its complement, both boolean on
    /// trace rows.
    fn exprs(self) -> (LeanExpr, LeanExpr) {
        match self {
            SiteSel::Always => (LeanExpr::Const(1), LeanExpr::Const(0)),
            SiteSel::When(c) => (LeanExpr::Var(c), sub(LeanExpr::Const(1), LeanExpr::Var(c))),
            SiteSel::Unless(c) => (sub(LeanExpr::Const(1), LeanExpr::Var(c)), LeanExpr::Var(c)),
        }
    }
}

/// Build the arity-7 `TID_P2` chip lookup carrying one `hash_fact` site:
/// `input_cols[0]` is the predicate, `input_cols[1..]` (≤ 4) the terms. For an
/// [`SiteSel::Always`] site the tuple is unconditionally the genuine fact absorb
/// `[CHIP_RATE, pred, t0..t3, 0xFACF, 1, 0…, out, lanes…]`; for a gated site the
/// value lanes ride `s·col` and the digest lane `s·out + (1−s)·K₀`, degenerating to
/// the satisfiable zero-fact permutation row on non-firing rows (mirrors the
/// note-spend adapter's `gated_fact_site`).
fn fact_site(
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
            // The hash_fact domain separation (state[5]/state[6]), constant on
            // every row — the zero-fact degenerate row keeps them too.
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
    // lanes 1..8: the genuine permutation lanes the chip AIR equality-binds.
    for j in 0..(CHIP_OUT_LANES - 1) {
        tuple.push(LeanExpr::Var(lane_base + j));
    }
    debug_assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    Ok(VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    }))
}

/// Lower a PURE-LOCAL `ConstraintExpr` to its vanishing gate body (the same lowering
/// discipline as the note-spend adapter's `local_gate_body`, duplicated file-locally
/// per the new-files-only lane discipline). Hash/transition kinds are handled — or
/// refused — by [`shielded_spend_to_descriptor2`]'s top level.
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
                "shielded-spend lowering: constraint kind {other:?} is not a local gate body"
            ));
        }
    })
}

/// Adapt the REAL deployed shielded-spend descriptor
/// ([`shielded_spend_descriptor`], `dregg-shielded-spend-v1`) into the IR-v2
/// [`EffectVmDescriptor2`]. The lowering WALKS the SOURCE descriptor (not a
/// transcription), so a drift in the deployed circuit is a build-time refusal here,
/// never a silent divergence. No columns are appended — the source's 3 PIs already
/// ARE the exposed claim.
pub fn shielded_spend_to_descriptor2() -> Result<EffectVmDescriptor2, String> {
    let src: CircuitDescriptor = shielded_spend_descriptor();
    if src.name != "dregg-shielded-spend-v1" || src.public_input_count != SHIELDED_SPEND_CLAIM_LEN {
        return Err(format!(
            "shielded-spend lowering is pinned to dregg-shielded-spend-v1 ({SHIELDED_SPEND_CLAIM_LEN} PIs); \
             got {} ({} PIs) — re-ground the lowering against the new descriptor",
            src.name, src.public_input_count
        ));
    }
    if src.trace_width != BASE_WIDTH {
        return Err(format!(
            "shielded-spend source width {} != spend_circuit::WIDTH {BASE_WIDTH}",
            src.trace_width
        ));
    }

    let mut constraints: Vec<VmConstraint2> = Vec::new();
    // Chip lane columns are appended past the base width, CHIP_OUT_LANES-1 per site.
    let mut width = BASE_WIDTH;
    let mut alloc_lanes = || {
        let base = width;
        width += CHIP_OUT_LANES - 1;
        base
    };

    for expr in &src.constraints {
        let c2 = match expr {
            // The Merkle-chain continuity C5: the two-row carrier on rows 0..n−2.
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
            // A ROW-GATED fact-sponge site (C4 nullifier, `Gated{is_leaf}`).
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
                fact_site(
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
                fact_site(
                    SiteSel::Unless(*selector_col),
                    *output_col,
                    input_cols,
                    alloc_lanes(),
                )?
            }
            // An UNGATED fact-sponge site (C3 Merkle, C6a leaf-commit, C7a
            // value-binding) — fires on every row.
            ConstraintExpr::Hash {
                output_col,
                input_cols,
            } => fact_site(SiteSel::Always, *output_col, input_cols, alloc_lanes())?,
            // Everything else is a pure-local algebraic gate (C1 Binary, C2 position
            // validity, C6b Gated{Equality}, the C7b pad Polynomials).
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

    Ok(EffectVmDescriptor2 {
        name: format!("shielded-spend-leaf::{}", src.name),
        trace_width: width,
        public_input_count: SHIELDED_SPEND_CLAIM_LEN,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    })
}

/// The HONEST 3-slot claim tuple for a witness: the source circuit's PIs
/// `[nullifier, merkle_root, value_binding]` from [`generate_shielded_spend_trace`].
pub fn shielded_spend_leaf_public_inputs(witness: &ShieldedSpendWitness) -> Vec<BabyBear> {
    let (_, pis) = generate_shielded_spend_trace(witness);
    pis
}

/// Build the base trace for the IR-v2 leaf: the shielded-spend trace itself (width
/// [`BASE_WIDTH`]; no appended columns). Chip lane columns are filled by the general
/// prover's descriptor-driven weld (`trace_with_chip_lanes`).
fn shielded_spend_leaf_base_trace(
    witness: &ShieldedSpendWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let (mut trace, pis) = generate_shielded_spend_trace(witness);
    for row in &mut trace {
        row.resize(BASE_WIDTH, BabyBear::ZERO);
    }
    (trace, pis)
}

/// The shared inner IR-v2 prove (descriptor lowering + batch mint under the recursion
/// config type).
fn prove_shielded_spend_inner(
    witness: &ShieldedSpendWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<
    (
        EffectVmDescriptor2,
        dregg_circuit::descriptor_ir2::Ir2BatchProof<DreggRecursionConfig>,
    ),
    String,
> {
    if public_inputs.len() != SHIELDED_SPEND_CLAIM_LEN {
        return Err(format!(
            "shielded-spend leaf expects {SHIELDED_SPEND_CLAIM_LEN} PI slots, got {}",
            public_inputs.len()
        ));
    }
    let desc2 = shielded_spend_to_descriptor2()?;
    let (base_trace, _honest_pis) = shielded_spend_leaf_base_trace(witness);

    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc2,
        &base_trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .map_err(|e| format!("shielded-spend leaf inner IR-v2 prove failed: {e}"))?;
    Ok((desc2, inner))
}

/// Prove a REAL shielded-spend as a RECURSION-FOLDABLE IR-v2 leaf.
///
/// `witness` is the SAME [`ShieldedSpendWitness`] the off-AIR hiding prover consumes
/// (value/asset/owner/randomness, spending key, Merkle path). `public_inputs` is the
/// 3-slot claim tuple — for an HONEST proof, [`shielded_spend_leaf_public_inputs`].
/// Passing a DIFFERENT tuple is exactly a forged backing: the `PiBinding` pins + the
/// chip-recomputed hash chains make the mismatch UNSAT, so no foldable leaf is minted
/// (the leaf-level tooth).
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_shielded_spend_leaf(
    witness: &ShieldedSpendWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let (desc2, inner) = prove_shielded_spend_inner(witness, public_inputs, config)?;
    prove_descriptor_leaf_rotated_with_config(&desc2, &inner, public_inputs, config)
        .map_err(|e| format!("shielded-spend leaf recursion wrap failed: {e}"))
}

/// Prove a REAL shielded-spend leaf (as [`prove_shielded_spend_leaf`]) AND RE-EXPOSE
/// its 3-slot claim tuple `[nullifier, merkle_root, value_binding]` as an
/// IN-CIRCUIT `expose_claim` (lanes `[0 .. SHIELDED_SPEND_CLAIM_LEN)`), read from the
/// leaf's own FRI-bound descriptor PIs — the shielded analog of
/// [`crate::note_spend_leaf_adapter::prove_note_spend_leaf_with_claim`].
///
/// Lane 0 is the nullifier (the double-spend guard's connect target); lane 1 the
/// merkle_root (the turn's commitments-root connect target); lane 2 the value_binding
/// (the ATTESTED off-AIR Pedersen link).
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_shielded_spend_leaf_with_claim(
    witness: &ShieldedSpendWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let (desc2, inner) = prove_shielded_spend_inner(witness, public_inputs, config)?;
    prove_descriptor_leaf_with_pi_slice_expose(
        &desc2,
        &inner,
        public_inputs,
        config,
        0,
        SHIELDED_SPEND_CLAIM_LEN,
    )
    .map_err(|e| format!("shielded-spend claim leaf expose-wrap failed: {e}"))
}

/// **THE SHIELDED-SPEND BINDING MECHANISM NODE (no segment).** Aggregate a leg leaf
/// that RE-EXPOSES its CLAIMED 3-slot tuple WITH the shielded-spend sub-proof leaf
/// ([`prove_shielded_spend_leaf_with_claim`]), CONNECTING the two tuples lane-by-lane
/// in-circuit and re-exposing the bound tuple. A leg claiming a
/// `[nullifier, merkle_root, value_binding]` no verifying shielded-spend backs is a
/// `connect` conflict ⇒ UNSAT ⇒ no root — the term-for-term shielded twin of
/// [`crate::note_spend_leaf_adapter::prove_note_spend_binding_node`].
///
/// This realizes the ABI §3.3 BIND for the shielded pool: the exposed
/// membership+nullifier claim is bound to a leg by EQUALITY (a DSU merge, UNSAT on
/// conflict), not assignment — the circuit half of the Lean
/// `shielded_spend_claim_refines` `hbound` teeth.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_shielded_spend_binding_node(
    leg_claim_leaf: &RecursionOutput<DreggRecursionConfig>,
    shielded_spend_leaf: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::ivc_turn_chain::expose_claim_instance_index;
    use crate::plonky3_recursion_impl::recursive::create_recursion_backend;
    use p3_circuit::CircuitBuilder;
    use p3_recursion::{BatchOnly, Target, build_and_prove_aggregation_layer_with_expose};

    type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

    let leg_idx = expose_claim_instance_index(&leg_claim_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason:
                "shielded-spend leg leaf carries no re-exposed tuple (expose_claim) table — it \
                     must expose the claimed 3-slot tuple"
                    .to_string(),
        }
    })?;
    let cs_idx = expose_claim_instance_index(&shielded_spend_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason:
                "shielded-spend sub-proof leaf carries no exposed tuple (expose_claim) table — \
                     it must be minted via prove_shielded_spend_leaf_with_claim"
                    .to_string(),
        }
    })?;

    let left = leg_claim_leaf.into_recursion_input::<BatchOnly>();
    let right = shielded_spend_leaf.into_recursion_input::<BatchOnly>();

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>],
                       _left_vk_cap: &[Target],
                       _right_vk_cap: &[Target]| {
        let lg = left_apt
            .get(leg_idx)
            .expect("shielded-spend leg's re-exposed tuple instance present");
        let cs = right_apt
            .get(cs_idx)
            .expect("shielded-spend sub-proof's exposed tuple instance present");
        debug_assert!(lg.len() >= SHIELDED_SPEND_CLAIM_LEN && cs.len() >= SHIELDED_SPEND_CLAIM_LEN);
        // THE BINDING TOOTH, IN-CIRCUIT: the leg's CLAIMED tuple must equal the
        // shielded-spend leaf's GENUINE bound tuple, lane by lane.
        for k in 0..SHIELDED_SPEND_CLAIM_LEN {
            cb.connect(lg[k], cs[k]);
        }
        let bound: Vec<Target> = (0..SHIELDED_SPEND_CLAIM_LEN).map(|k| lg[k]).collect();
        cb.expose_as_public_output(&bound);
    };

    build_and_prove_aggregation_layer_with_expose::<DreggRecursionConfig, BatchOnly, BatchOnly, _, D>(
        &left,
        &right,
        config,
        &backend,
        &params,
        None,
        Some(&expose),
    )
    .map_err(|e| JointAggError::AggregationProofInvalid {
        reason: format!("shielded-spend binding aggregation node failed: {e:?}"),
    })
}

/// **THE SEGMENT-PRESERVING SHIELDED ROOT-BINDING NODE (deployed-path shape).** The
/// turn-bind that makes a shielded spend NATIVE: the leg is a DUAL-EXPOSE leaf
/// (`expose_claim` = segment lanes `[0 .. SEG_WIDTH)` ++ the two ROOT-bound claimed
/// lanes — the deployed descriptor's nullifier PI and commitments-root PI); the
/// sub-proof leaf is [`prove_shielded_spend_leaf_with_claim`]. The node `connect`s
/// the leg's nullifier lane to the shielded leaf's lane 0 and the leg's root lane to
/// the shielded leaf's lane 1, then re-exposes the segment so the result folds into
/// `aggregate_tree` like any per-turn segment leaf.
///
/// A forged shielded claim (a non-member note, a re-used nullifier, or a merkle_root
/// that does not match the turn's committed commitments-root) is a `connect` conflict
/// ⇒ UNSAT ⇒ no root mints — fail-closed, the ABI §5 no-forgery/nullifier invariants.
///
/// **HONEST GRADE:** only lanes 0 (nullifier) and 1 (merkle_root) — the PROVED
/// membership+nullifier half — bind to in-AIR turn roots here. Lane 2 (value_binding)
/// is the ATTESTED off-AIR Pedersen link and is deliberately NOT connected to an
/// in-AIR conservation root (there is none; conservation rides the off-AIR Schnorr
/// excess). This is the exact split the Lean `shielded_spend_claim_refines` proves
/// (membership ⇒ AUTHORIZED, fresh ⇒ NO-DOUBLE-SPEND) with conservation named ATTESTED.
///
/// ⚑ The DEPLOYED leg side (the shielded descriptor rung that PI-emits the nullifier
/// at the `NOTESPEND_NULLIFIER`-analog slot + the commitments-root, and dual-exposes
/// them) is the named `Effect::ShieldedTransfer` big-bang VK-regen piece
/// (ABI §4.1(b)); this node is its ready consumer.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_shielded_spend_root_binding_node_segmented(
    dual_expose_leg_leaf: &RecursionOutput<DreggRecursionConfig>,
    shielded_spend_leaf: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::ivc_turn_chain::{SEG_WIDTH, expose_claim_instance_index};
    use crate::plonky3_recursion_impl::recursive::create_recursion_backend;
    use p3_circuit::CircuitBuilder;
    use p3_recursion::{BatchOnly, Target, build_and_prove_aggregation_layer_with_expose};

    type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

    // The two root-bound lanes: nullifier (claim lane 0) and merkle_root (claim lane 1).
    const ROOT_BOUND_LANES: usize = 2;

    let leg_idx = expose_claim_instance_index(&dual_expose_leg_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "dual-expose shielded leg leaf carries no expose_claim table — it must \
                     re-expose (segment ++ the nullifier & merkle_root lanes)"
                .to_string(),
        }
    })?;
    let cs_idx = expose_claim_instance_index(&shielded_spend_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason:
                "shielded-spend sub-proof leaf carries no exposed tuple (expose_claim) table — \
                     it must be minted via prove_shielded_spend_leaf_with_claim"
                    .to_string(),
        }
    })?;

    let left = dual_expose_leg_leaf.into_recursion_input::<BatchOnly>();
    let right = shielded_spend_leaf.into_recursion_input::<BatchOnly>();

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>],
                       _left_vk_cap: &[Target],
                       _right_vk_cap: &[Target]| {
        let lg = left_apt
            .get(leg_idx)
            .expect("dual-expose shielded leg's claim instance present");
        let cs = right_apt
            .get(cs_idx)
            .expect("shielded-spend sub-proof's exposed tuple instance present");
        debug_assert!(
            lg.len() >= SEG_WIDTH + ROOT_BOUND_LANES && cs.len() >= SHIELDED_SPEND_CLAIM_LEN,
            "dual-expose claim must carry segment ++ the nullifier & root lanes; shielded leaf \
             carries the 3-lane tuple"
        );
        // THE BINDING TOOTH, IN-CIRCUIT: the leg's published nullifier and
        // commitments-root must equal the shielded leaf's GENUINE bound nullifier
        // (lane 0) and merkle_root (lane 1). value_binding (lane 2) is ATTESTED and
        // NOT connected here.
        for k in 0..ROOT_BOUND_LANES {
            cb.connect(lg[SEG_WIDTH + k], cs[k]);
        }
        let seg: Vec<Target> = (0..SEG_WIDTH).map(|k| lg[k]).collect();
        cb.expose_as_public_output(&seg);
    };

    build_and_prove_aggregation_layer_with_expose::<DreggRecursionConfig, BatchOnly, BatchOnly, _, D>(
        &left,
        &right,
        config,
        &backend,
        &params,
        None,
        Some(&expose),
    )
    .map_err(|e| JointAggError::AggregationProofInvalid {
        reason: format!("segmented shielded root-binding aggregation node failed: {e:?}"),
    })
}

/// Read the exposed 3-lane claim tuple off a leaf minted by
/// [`prove_shielded_spend_leaf_with_claim`].
pub fn read_exposed_shielded_spend_claim(
    output: &RecursionOutput<DreggRecursionConfig>,
) -> Option<[BabyBear; SHIELDED_SPEND_CLAIM_LEN]> {
    use p3_field::PrimeField32;
    let claims: Vec<BabyBear> = output
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")?
        .public_values
        .iter()
        .map(|&v| BabyBear::new(v.as_canonical_u32()))
        .collect();
    if claims.len() < SHIELDED_SPEND_CLAIM_LEN {
        return None;
    }
    Some(core::array::from_fn(|i| claims[i]))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ivc_turn_chain::ir2_leaf_wrap_config;
    use crate::shielded::spend_circuit::pi;
    use dregg_circuit::refusal::must_refuse_or_unsat_panic;

    /// A REAL shielded-spend witness (depth-4 Merkle path, a live > 2^0 value). The
    /// forward-chained padding makes the ungated Merkle/leaf/value-binding hashes hold
    /// on every trace row.
    fn make_witness(tag: u8) -> ShieldedSpendWitness {
        let depth = 4;
        let mut siblings = Vec::with_capacity(depth);
        let mut positions = Vec::with_capacity(depth);
        for i in 0..depth {
            positions.push(((i + tag as usize) % 4) as u8);
            siblings.push([
                BabyBear::new((i as u32) * 7 + tag as u32 + 1),
                BabyBear::new((i as u32) * 7 + tag as u32 + 2),
                BabyBear::new((i as u32) * 7 + tag as u32 + 3),
            ]);
        }
        ShieldedSpendWitness {
            value: BabyBear::new(1_000 + tag as u32),
            asset_type: BabyBear::new(42),
            owner: BabyBear::new(0xABCDE + tag as u32),
            randomness: BabyBear::new(0x13579 + tag as u32),
            key: [
                BabyBear::new(7 + tag as u32),
                BabyBear::new(8),
                BabyBear::new(9),
                BabyBear::new(10),
            ],
            siblings,
            positions,
        }
    }

    /// The lowering consumes the REAL deployed descriptor and produces the expected
    /// shape: 4 chip sites (1 Merkle + 1 nullifier + 1 leaf-commit + 1 value-binding),
    /// the C5 WindowGate, and 3 PiBindings, with the right trace width.
    #[test]
    fn shielded_spend_descriptor_lowers() {
        let desc2 =
            shielded_spend_to_descriptor2().expect("the real shielded-spend descriptor lowers");
        assert_eq!(desc2.public_input_count, SHIELDED_SPEND_CLAIM_LEN);
        let sites = desc2
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
            .count();
        assert_eq!(
            sites, 4,
            "1 merkle + 1 nullifier + 1 leaf-commit + 1 value-binding"
        );
        let windows = desc2
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
            .count();
        assert_eq!(windows, 1, "the C5 Merkle-chain continuity");
        let pins = desc2
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
            .count();
        assert_eq!(pins, 3, "nullifier + merkle_root + value_binding");
        // Lane accounting: 4 sites × (CHIP_OUT_LANES-1) lanes past the base width.
        assert_eq!(desc2.trace_width, BASE_WIDTH + 4 * (CHIP_OUT_LANES - 1));
    }

    /// THE POSITIVE POLE: an honest REAL shielded-spend (membership + nullifier +
    /// value-binding) proves as a foldable recursion leaf, and the exposed claim tuple
    /// equals the bound PIs `[nullifier, merkle_root, value_binding]`.
    #[test]
    fn honest_shielded_spend_proves_as_foldable_leaf_and_exposes_claim() {
        let w = make_witness(0x10);
        let pis = shielded_spend_leaf_public_inputs(&w);
        assert_eq!(pis.len(), SHIELDED_SPEND_CLAIM_LEN);
        assert_eq!(
            pis[pi::NULLIFIER],
            w.nullifier(),
            "lane 0 is the C4 nullifier"
        );
        assert_eq!(
            pis[pi::MERKLE_ROOT],
            w.merkle_root(),
            "lane 1 is the membership root"
        );
        assert_eq!(
            pis[pi::VALUE_BINDING],
            w.value_binding(),
            "lane 2 is the C7a value-binding"
        );
        let config = ir2_leaf_wrap_config();

        let output = prove_shielded_spend_leaf_with_claim(&w, &pis, &config)
            .expect("the honest shielded-spend must prove as a foldable claim leaf");
        let exposed =
            read_exposed_shielded_spend_claim(&output).expect("the leaf exposes the 3-lane claim");
        assert_eq!(
            exposed.as_slice(),
            pis.as_slice(),
            "the exposed claim is the bound tuple"
        );
    }

    /// THE NEGATIVE POLE (nullifier): a FORGED claim (tampered nullifier lane, honest
    /// witness) has no satisfying assembly — the `PiBinding{First}` + the chip-bound
    /// C4 nullifier chain refuse it AT THE LEAF; no foldable leaf is minted.
    #[test]
    fn forged_nullifier_does_not_fold() {
        let w = make_witness(0x22);
        let mut pis = shielded_spend_leaf_public_inputs(&w);
        pis[pi::NULLIFIER] += BabyBear::ONE;
        let config = ir2_leaf_wrap_config();

        must_refuse_or_unsat_panic("a FORGED nullifier", || {
            prove_shielded_spend_leaf(&w, &pis, &config)
        });
    }

    /// THE NEGATIVE POLE (merkle_root): a FORGED merkle_root lane (a note claimed
    /// under a tree it is not a member of) is refused AT THE LEAF — the last-row
    /// `PiBinding{Last}` on the C3/C5 membership chain top makes it UNSAT.
    #[test]
    fn forged_merkle_root_does_not_fold() {
        let w = make_witness(0x33);
        let mut pis = shielded_spend_leaf_public_inputs(&w);
        pis[pi::MERKLE_ROOT] += BabyBear::ONE;
        let config = ir2_leaf_wrap_config();

        must_refuse_or_unsat_panic("a FORGED merkle_root", || {
            prove_shielded_spend_leaf(&w, &pis, &config)
        });
    }

    /// THE NEGATIVE POLE (value-binding): a FORGED value_binding lane (the ATTESTED
    /// Pedersen link decoupled from the leaf value) is refused AT THE LEAF — the
    /// row-0 `PiBinding{First}` + the ungated C7a hash make it UNSAT. Even the ATTESTED
    /// lane cannot float free of the spend this leaf proves.
    #[test]
    fn forged_value_binding_does_not_fold() {
        let w = make_witness(0x44);
        let mut pis = shielded_spend_leaf_public_inputs(&w);
        pis[pi::VALUE_BINDING] += BabyBear::ONE;
        let config = ir2_leaf_wrap_config();

        must_refuse_or_unsat_panic("a FORGED value_binding", || {
            prove_shielded_spend_leaf(&w, &pis, &config)
        });
    }

    /// THE BINDING TOOTH (both polarities), a REAL in-circuit `connect`. A leg leaf and
    /// the shielded sub-proof leaf are BOTH minted with `expose_claim`; the binding
    /// node connects their tuples lane-by-lane.
    ///
    /// TRUE: two leaves of the SAME honest spend share the tuple — the connect
    /// succeeds and the node folds (the claim binds).
    ///
    /// FALSE: a leg leaf of a DIFFERENT spend (different nullifier & root) cannot
    /// connect to the sub-proof's genuine tuple — a `connect` conflict ⇒ the
    /// aggregation is UNSAT ⇒ no bound root.
    #[test]
    fn shielded_claim_binds_and_forged_leg_does_not() {
        let config = ir2_leaf_wrap_config();

        // The genuine spend + its two claim leaves (the leg and the sub-proof).
        let w = make_witness(0x51);
        let pis = shielded_spend_leaf_public_inputs(&w);
        let sub = prove_shielded_spend_leaf_with_claim(&w, &pis, &config)
            .expect("shielded sub-proof leaf");
        let leg = prove_shielded_spend_leaf_with_claim(&w, &pis, &config)
            .expect("honest leg leaf (same spend)");

        // TRUE: the honest leg's claim binds to the sub-proof's genuine tuple.
        let bound = prove_shielded_spend_binding_node(&leg, &sub, &config)
            .expect("an honest shielded claim must bind (connect succeeds)");
        let bound_claim = read_exposed_shielded_spend_claim(&bound)
            .expect("the bound node re-exposes the 3-lane tuple");
        assert_eq!(
            bound_claim.as_slice(),
            pis.as_slice(),
            "the bound tuple is the genuine spend's claim"
        );

        // FALSE: a leg from a DIFFERENT spend cannot bind to this sub-proof.
        let w2 = make_witness(0x62);
        let pis2 = shielded_spend_leaf_public_inputs(&w2);
        assert_ne!(pis2[pi::NULLIFIER], pis[pi::NULLIFIER], "distinct spends");
        let forged_leg = prove_shielded_spend_leaf_with_claim(&w2, &pis2, &config)
            .expect("the forged leg is itself an honest leaf of a DIFFERENT spend");
        must_refuse_or_unsat_panic(
            "a leg claiming a tuple no verifying shielded-spend backs BOUND",
            || prove_shielded_spend_binding_node(&forged_leg, &sub, &config),
        );
    }
}
