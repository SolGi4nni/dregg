//! Re-prove the REAL foreign note-spend STARK as a RECURSION-FOLDABLE IR-v2 leaf —
//! the bridge carrier's G2 BACKING half (WELD-STATE §3 bridge row).
//!
//! ## Which STARK this re-proves (grounding)
//!
//! The STARK a bridge mint's backing rests on executor-side is the DSL note-spending
//! circuit `dregg-note-spending-dsl-v3`
//! ([`dregg_circuit::dsl::note_spending::note_spending_circuit_descriptor`], width 62,
//! 6 PIs `[nullifier, merkle_root, value_lo30, asset_type, destination_federation,
//! value_hi34]`): `turn::executor::apply::apply_bridge_mint` verifies it via
//! `verify_note_spend_dsl_full` (apply.rs:1676) inside `verify_portable_note`. It
//! carries the SPEND SEMANTICS — spending-key knowledge (the two-step 8-limb
//! nullifier chain C3/C4), the FULL-WIDTH 28-limb commitment binding (C2a..C2g),
//! and Merkle membership (the `hash_fact(current, [sib0..2, position])` chain C6/C7)
//! — everything `bridge_action_air` does NOT have. (`SCHEMA_NOTE_SPEND` in
//! `effect_action_air.rs` is a different surface: the in-federation binding schema
//! for `Effect::NoteSpend` rows, not the bridge's foreign backing proof.)
//!
//! ## Why this module exists — folding `bridge_action_air` is UNSOUND as a backing
//!
//! [`crate::bridge_leaf_adapter`] folds `BridgeActionAir`, which is a BINDING-ONLY
//! AIR: its 26-limb tuple is a prover-chosen constant trace with NO Merkle membership
//! and NO spending-key relation, and the deployed `mint_hash` is read by ZERO
//! constraints. A leaf that re-proves only the binding AIR gives a light client a
//! tuple the prover invented — the vacuous connect the fail-open law forbids. The
//! SOUND backing leaf is THIS one: re-prove the real note-spend STARK, so the folded
//! claim is welded (through the FRI-bound descriptor PIs) to a genuine
//! key-knowledge + membership + full-width-commitment execution.
//!
//! ## The constraint lowering (`dregg-note-spending-dsl-v3` → `EffectVmDescriptor2`)
//!
//! The source descriptor's kinds and their IR-v2 carriers:
//!
//! | source constraint                                | carrier                                                        |
//! |--------------------------------------------------|----------------------------------------------------------------|
//! | `Binary` / `Polynomial` / `Equality` (± gates)   | `Base(Gate(body))` (the same local-gate lowering custom uses)  |
//! | `Transition { CURRENT, PARENT }` (C7)            | `WindowGate(Nxt − Loc)` on the transition domain               |
//! | `(Inverted)Gated { Hash }` (C2a..g, C3, C4, C6)  | a SELECTOR-MUXED arity-7 `TID_P2` chip lookup (see below)      |
//! | boundary `PiBinding` (First/Last)                | `Base(PiBinding{row, col, pi})` — row-tag exact                |
//!
//! **The fact-sponge carrier (the piece `cellprogram_to_descriptor2` refuses).** A DSL
//! `ConstraintExpr::Hash` is `hash_fact(pred, terms)`: ONE Poseidon2 permutation
//! seeded `st[0]=pred, st[1..5]=terms, st[5]=FACT_MARK(0xFACF), st[6]=1`. The chip's
//! arity-7 row seeds `st[0..7] = in0..in6` verbatim (`chip_absorb_all_lanes`, the
//! `seed456` branch), so the faithful carrier is an arity-7 chip lookup with inputs
//! `[pred, t0..t3, Const(0xFACF), Const(1)]` — byte-identical (KAT-pinned by
//! `fact_arity7_chip_absorb_matches_hash_fact`).
//!
//! **The row-gating mux.** Chip lookups fire on EVERY main row, but the note-spend
//! hash sites are row-gated (commitment-row sites via `1 − is_merkle`, the Merkle
//! site via `is_merkle`). The carrier muxes the tuple by the (Binary-pinned) selector
//! `s`: value inputs ride as `s·col`, the domain constants stay constant, and the
//! digest lane rides as `s·out + (1−s)·K₀` where `K₀ = hash_fact(0, [])`. On a firing
//! row the tuple IS the genuine site; on a non-firing row it degenerates to the
//! constant zero-fact permutation row (satisfiable by construction, binding nothing).
//! All muxed tuple entries are degree ≤ 2 (below the degree-4 `MerkleHash` exprs the
//! custom adapter already ships).
//!
//! ## The claim tuple — `(…PIs…, mint_hash)`, with mint_hash RECOMPUTED IN-CIRCUIT
//!
//! [`prove_note_spend_leaf_with_claim`] exposes all `NOTE_SPEND_CLAIM_LEN = 7` lanes
//! `[nullifier, merkle_root, value_lo, asset_type, destination_federation, value_hi,
//! mint_hash]` as its `expose_claim` (via
//! [`crate::ivc_turn_chain::prove_descriptor_leaf_with_pi_slice_expose`]). Lane 6 is
//! the FELT-DOMAIN mint identity [`note_spend_mint_hash_felt`] =
//! `hash_fact(hash_fact(nullifier, [root, dest_fed, asset]), [value_lo, value_hi])`,
//! recomputed IN-AIR by two more gated fact sites over the SAME PI-pinned row-0
//! columns and pinned to PI 6 — so a prover cannot expose a mint identity that
//! disagrees with the spend this leaf actually proves. Lane 0 (the nullifier) is the
//! double-mint guard's connect target: the deployed descriptor ALREADY commits the
//! faithful `nullifier_root` (pre-limb 26) and `NOTESPEND_NULLIFIER` (PI 198).
//!
//! ## THE FORMERLY-VK-GATED SEAM — CLOSED (the felt-domain mint_hash thread)
//!
//! The two pieces named here as riding the big-bang VK regen have LANDED:
//!
//! 1. **The `mintV3` mint_hash PI-emit** — via the STEP-1 EXECUTOR RE-ALIGN (the
//!    `687601953` membership-compress precedent, stronger than the descriptor-side
//!    `lifecycle_payload_felt` shape originally sketched): `effect_vm_bridge.rs` (and
//!    the SDK/differential projector twins) now derive `mint_hash` AS the FELT-domain
//!    [`note_spend_mint_hash_felt`] (`dsl::note_spending::bridge_mint_hash_felt`, over
//!    the six compressed felts `apply_bridge_mint` enforces the note-spend STARK
//!    against), and the deployed `mintVmDescriptor2R24` (Lean `mintV3BridgeHash`)
//!    pins the mint row's `param0` at PI 46 (`withMintHashPin`, producer-filled —
//!    the STEP-3/4 regen).
//! 2. **The deployed-path fold arm** — `prove_chain_core_rotated`'s Bridge arm mints
//!    the dual-expose leg at PI 46 and folds THIS module's backing leaf under
//!    [`prove_note_spend_mint_binding_node_segmented`] (one connected lane binds the
//!    whole spend tuple through the in-AIR `hash_fact` chain).
//!
//! `apply_bridge_mint`'s off-AIR `verify_note_spend_dsl_full` remains the executor
//! enforcer; this leaf is its light-client-witnessable twin, now CONNECTED on the
//! deployed path.

use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, EffectVmDescriptor2, LookupSpec, MemBoundaryWitness,
    TID_P2, UMemBoundaryWitness, VmConstraint2, WindowExpr, WindowGateSpec,
    prove_vm_descriptor2_for_config,
};
use dregg_circuit::dsl::circuit::{BoundaryDef, BoundaryRow, CircuitDescriptor, ConstraintExpr};
use dregg_circuit::dsl::note_spending::{
    generate_note_spending_trace, note_spending_circuit_descriptor,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use dregg_circuit::note_spending_air::{NOTE_SPENDING_WIDTH, NoteSpendingWitness, col, pi};
use dregg_circuit::poseidon2::hash_fact;

use p3_recursion::{ProveNextLayerParams, RecursionOutput};

use crate::ivc_turn_chain::{
    prove_descriptor_leaf_rotated_with_config, prove_descriptor_leaf_with_pi_slice_expose,
};
use crate::joint_turn_aggregation::JointAggError;
use crate::plonky3_recursion_impl::recursive::DreggRecursionConfig;

/// Extension degree of the recursion config's PCS (the BabyBear-quartic stack).
const D: usize = 4;

/// The `hash_fact` domain-separation marker (`poseidon2::hash_fact` state[5]).
/// Kept file-local (the descriptor_ir2 twin is private); the KAT test
/// `fact_arity7_chip_absorb_matches_hash_fact` pins the two against divergence.
const NS_FACT_MARK: u32 = 0xFACF;

/// The exposed claim width: the 6 note-spend PIs + the felt-domain mint_hash.
/// Lanes: `[nullifier, merkle_root, value_lo, asset_type, destination_federation,
/// value_hi, mint_hash]`.
pub const NOTE_SPEND_CLAIM_LEN: usize = 7;

/// PI slot of the felt-domain mint identity (appended after the source
/// descriptor's 6 PIs).
pub const NOTE_SPEND_MINT_HASH_PI: usize = 6;

// The three extension columns appended past the source trace width (62), BEFORE the
// per-site chip lane columns.
/// Row-0 copy of the Merkle root, pinned to `pi[1]` (`PiBinding{First}`). The root's
/// canonical carrier is the LAST row's `CURRENT` (also pinned to `pi[1]`), so both
/// are anchored to the same PI — this column just makes the root readable on the
/// commitment row for the mint-hash absorb.
const MINT_ROOT_COL: usize = NOTE_SPENDING_WIDTH;
/// The mint-hash chain intermediate `hash_fact(nullifier, [root, dest, asset, value])`.
const MINT_M1_COL: usize = NOTE_SPENDING_WIDTH + 1;
/// The felt-domain mint identity, pinned to `pi[6]`.
const MINT_HASH_COL: usize = NOTE_SPENDING_WIDTH + 2;
/// Base width of the extended trace (source 62 + the 3 mint columns); chip lane
/// columns are allocated past this.
const EXT_BASE_WIDTH: usize = NOTE_SPENDING_WIDTH + 3;

/// `x − y` as a `LeanExpr` (no subtraction node: `x + (−1)·y`).
fn sub(x: LeanExpr, y: LeanExpr) -> LeanExpr {
    LeanExpr::add(x, LeanExpr::mul(LeanExpr::Const(-1), y))
}

/// **THE FELT-DOMAIN MINT IDENTITY** — the in-circuit-recomputable bridge-mint
/// `mint_hash`. The canonical definition now lives beside the verifier it binds
/// to ([`dregg_circuit::dsl::note_spending::note_spend_mint_hash_felt`] — the
/// STEP-1 executor re-align moved it there so the executor/SDK projectors and
/// this leaf share ONE function); re-exported here so the leaf's claim-lane
/// vocabulary is unchanged.
///
/// `hash_fact(hash_fact(nullifier, [merkle_root, destination_federation,
/// asset_type]), [value_lo, value_hi])` over the SAME compressed felts the
/// executor's `verify_note_spend_dsl_full` call binds. The leaf recomputes this
/// IN-AIR from its PI-pinned row-0 columns and exposes it at claim lane
/// [`NOTE_SPEND_MINT_HASH_PI`]; the deployed `mintV3` row publishes the SAME
/// felt (the executor-derived `VmEffect::BridgeMint.mint_hash`) at its
/// mint-hash PI slot.
pub use dregg_circuit::dsl::note_spending::note_spend_mint_hash_felt;

/// Row-gating selector for a chip site.
#[derive(Clone, Copy)]
enum SiteSel {
    /// Fires when the selector column is 1 (`Gated`).
    When(usize),
    /// Fires when the selector column is 0 (`InvertedGated`).
    Unless(usize),
}

impl SiteSel {
    /// `(fire, hold)` — the firing indicator and its complement, both boolean on
    /// trace rows (the selector column carries a `Binary` gate).
    fn exprs(self) -> (LeanExpr, LeanExpr) {
        match self {
            SiteSel::When(c) => (LeanExpr::Var(c), sub(LeanExpr::Const(1), LeanExpr::Var(c))),
            SiteSel::Unless(c) => (sub(LeanExpr::Const(1), LeanExpr::Var(c)), LeanExpr::Var(c)),
        }
    }
}

/// Build the SELECTOR-MUXED arity-7 `TID_P2` chip lookup carrying one row-gated
/// `hash_fact` site: `input_cols[0]` is the predicate, `input_cols[1..]` (≤ 4) the
/// terms. On a firing row the tuple is the genuine fact absorb
/// `[7, pred, t0..t3, 0xFACF, 1, 0…, out, lanes…]`; on a non-firing row every value
/// lane muxes to zero and the digest lane to the constant `K₀ = hash_fact(0, [])`, so
/// the send degenerates to the satisfiable zero-fact permutation row.
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
    // lanes 1..7: the genuine permutation lanes, witnessed columns the chip AIR
    // EQUALITY-binds (`fill_chip_lanes` writes them from the muxed inputs).
    for j in 0..(CHIP_OUT_LANES - 1) {
        tuple.push(LeanExpr::Var(lane_base + j));
    }
    debug_assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    Ok(VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    }))
}

/// Lower a PURE-LOCAL `ConstraintExpr` to its vanishing gate body — the same
/// lowering discipline as `custom_leaf_adapter`'s private `gate_body` (duplicated
/// file-locally per the new-files-only lane discipline). Hash/lookup/cross-row kinds
/// are handled — or refused — by [`note_spend_to_descriptor2`]'s top level.
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

/// Adapt the REAL deployed note-spend descriptor
/// ([`note_spending_circuit_descriptor`], `dregg-note-spending-dsl-v3`) into the
/// IR-v2 [`EffectVmDescriptor2`], appending the in-AIR mint-hash recompute (2 more
/// gated fact sites + the [`NOTE_SPEND_MINT_HASH_PI`] pin). The lowering walks the
/// SOURCE descriptor (not a transcription), so a drift in the deployed circuit is a
/// build-time refusal here, never a silent divergence.
pub fn note_spend_to_descriptor2() -> Result<EffectVmDescriptor2, String> {
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
            // Everything else in this descriptor is a pure-local algebraic gate
            // (C1 Binary, C5 position validity, the C2 equality links).
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

    // ---- The mint-hash extension: recompute `note_spend_mint_hash_felt` IN-AIR over
    //      the PI-pinned row-0 columns and pin it to PI 6. ----
    //
    // MINT_ROOT is the root's row-0 copy, anchored to the SAME pi[1] the last-row
    // CURRENT boundary anchors — both PI-pinned, so the absorb reads the genuine root.
    constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::First,
        col: MINT_ROOT_COL,
        pi_index: pi::MERKLE_ROOT,
    }));
    // m1 = hash_fact(nullifier, [root, dest_fed, asset]) — every input column is
    // itself First-row PI-pinned by the source boundaries (nullifier pi0, dest pi4,
    // asset pi3) or by the MINT_ROOT pin above (pi1).
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
    // mint_hash = hash_fact(m1, [value_lo, value_hi]) — both value limbs PI-pinned
    // (pi2/pi5), so the identity binds the FULL u64 amount.
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
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    })
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

/// The mint identity from a 6-slot note-spend PI vector — [`note_spend_mint_hash_felt`]
/// over the PI slots.
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

/// Extend the source trace with the three mint columns (row 0; Merkle/padding rows
/// stay zero — the mint sites are row-gated). Chip lane columns are filled by the
/// general prover's descriptor-driven weld (`trace_with_chip_lanes`).
fn note_spend_leaf_base_trace(
    witness: &NoteSpendingWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
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
    (trace, full_pis)
}

/// Prove a REAL note-spend as a RECURSION-FOLDABLE IR-v2 leaf.
///
/// `witness` is the SAME `NoteSpendingWitness` the off-AIR `prove_note_spend_dsl`
/// consumes (spending key, 28-limb preimage, Merkle path). `public_inputs` is the
/// 7-slot claim tuple — for an HONEST proof, [`note_spend_leaf_public_inputs`].
/// Passing a DIFFERENT tuple is exactly a forged backing: the `PiBinding{First}`
/// pins + the chip-recomputed hash chain make the mismatch UNSAT, so no foldable
/// leaf is minted (the leaf-level tooth).
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_note_spend_leaf(
    witness: &NoteSpendingWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let (desc2, inner) = prove_note_spend_inner(witness, public_inputs, config)?;
    prove_descriptor_leaf_rotated_with_config(&desc2, &inner, public_inputs, config)
        .map_err(|e| format!("note-spend leaf recursion wrap failed: {e}"))
}

/// Prove a REAL note-spend leaf (as [`prove_note_spend_leaf`]) AND RE-EXPOSE its
/// 7-slot claim tuple `[nullifier, merkle_root, value_lo, asset_type,
/// destination_federation, value_hi, mint_hash]` as an IN-CIRCUIT `expose_claim`
/// (lanes `[0 .. NOTE_SPEND_CLAIM_LEN)`), read from the leaf's own FRI-bound
/// descriptor PIs — the note-spend analog of
/// [`crate::bridge_leaf_adapter::prove_bridge_leaf_tuple_claim`].
///
/// The exposed lane 6 is the in-AIR-recomputed [`note_spend_mint_hash_felt`]; lane 0
/// is the nullifier (the double-mint guard's connect target — `NOTESPEND_NULLIFIER`
/// PI 198 + the faithful `nullifier_root` pre-limb already exist committed).
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_note_spend_leaf_with_claim(
    witness: &NoteSpendingWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let (desc2, inner) = prove_note_spend_inner(witness, public_inputs, config)?;
    prove_descriptor_leaf_with_pi_slice_expose(
        &desc2,
        &inner,
        public_inputs,
        config,
        0,
        NOTE_SPEND_CLAIM_LEN,
    )
    .map_err(|e| format!("note-spend claim leaf expose-wrap failed: {e}"))
}

/// The shared inner IR-v2 prove (descriptor lowering + trace extension + batch mint
/// under the recursion config type).
fn prove_note_spend_inner(
    witness: &NoteSpendingWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<
    (
        EffectVmDescriptor2,
        dregg_circuit::descriptor_ir2::Ir2BatchProof<DreggRecursionConfig>,
    ),
    String,
> {
    if public_inputs.len() != NOTE_SPEND_CLAIM_LEN {
        return Err(format!(
            "note-spend leaf expects {NOTE_SPEND_CLAIM_LEN} PI slots, got {}",
            public_inputs.len()
        ));
    }
    let desc2 = note_spend_to_descriptor2()?;
    let (base_trace, _honest_pis) = note_spend_leaf_base_trace(witness);

    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc2,
        &base_trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .map_err(|e| format!("note-spend leaf inner IR-v2 prove failed: {e}"))?;
    Ok((desc2, inner))
}

/// **THE NOTE-SPEND BINDING MECHANISM NODE (no segment).** Aggregate a leg leaf that
/// RE-EXPOSES its CLAIMED 7-slot tuple WITH the note-spend sub-proof leaf
/// ([`prove_note_spend_leaf_with_claim`]), CONNECTING the two tuples lane-by-lane
/// in-circuit and re-exposing the bound tuple. A leg claiming a
/// `(…, mint_hash)`/nullifier no verifying note-spend backs is a `connect` conflict
/// ⇒ UNSAT ⇒ no root — the term-for-term note-spend twin of
/// [`crate::joint_turn_recursive::prove_bridge_binding_node`].
///
/// ⚑ The DEPLOYED leg side (the `mintV3` mint_hash PI-emit + dual-expose) is the
/// named VK-gated big-bang piece (module docs); this node is its ready consumer.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_note_spend_binding_node(
    leg_claim_leaf: &RecursionOutput<DreggRecursionConfig>,
    note_spend_leaf: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::ivc_turn_chain::expose_claim_instance_index;
    use crate::plonky3_recursion_impl::recursive::create_recursion_backend;
    use p3_circuit::CircuitBuilder;
    use p3_recursion::{BatchOnly, Target, build_and_prove_aggregation_layer_with_expose};

    type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

    let leg_idx = expose_claim_instance_index(&leg_claim_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "note-spend leg leaf carries no re-exposed tuple (expose_claim) table — it \
                     must expose the claimed 7-slot tuple"
                .to_string(),
        }
    })?;
    let cs_idx = expose_claim_instance_index(&note_spend_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "note-spend sub-proof leaf carries no exposed tuple (expose_claim) table — \
                     it must be minted via prove_note_spend_leaf_with_claim"
                .to_string(),
        }
    })?;

    let left = leg_claim_leaf.into_recursion_input::<BatchOnly>();
    let right = note_spend_leaf.into_recursion_input::<BatchOnly>();

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>]| {
        let lg = left_apt
            .get(leg_idx)
            .expect("note-spend leg's re-exposed tuple instance present");
        let cs = right_apt
            .get(cs_idx)
            .expect("note-spend sub-proof's exposed tuple instance present");
        debug_assert!(lg.len() >= NOTE_SPEND_CLAIM_LEN && cs.len() >= NOTE_SPEND_CLAIM_LEN);
        // THE BINDING TOOTH, IN-CIRCUIT: the leg's CLAIMED tuple must equal the
        // note-spend leaf's GENUINE bound tuple, lane by lane.
        for k in 0..NOTE_SPEND_CLAIM_LEN {
            cb.connect(lg[k], cs[k]);
        }
        let bound: Vec<Target> = (0..NOTE_SPEND_CLAIM_LEN).map(|k| lg[k]).collect();
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
        reason: format!("note-spend binding aggregation node failed: {e:?}"),
    })
}

/// **THE SEGMENT-PRESERVING NOTE-SPEND BINDING NODE (deployed-path shape, VK-gated
/// consumer).** The note-spend twin of
/// [`crate::joint_turn_recursive::prove_bridge_binding_node_segmented`]: the leg is a
/// DUAL-EXPOSE leaf (`expose_claim` = segment lanes `[0 .. SEG_WIDTH)` ++ the claimed
/// tuple lanes `[SEG_WIDTH ..)`), the sub-proof leaf is
/// [`prove_note_spend_leaf_with_claim`]; the node `connect`s the tuple lanes and
/// re-exposes the segment so the result folds into `aggregate_tree` like any per-turn
/// segment leaf. The dual-expose leg requires the `mintV3` PI-emit (the named
/// VK-gated seam) — this node is ready for it.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_note_spend_binding_node_segmented(
    dual_expose_leg_leaf: &RecursionOutput<DreggRecursionConfig>,
    note_spend_leaf: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::ivc_turn_chain::{SEG_WIDTH, expose_claim_instance_index};
    use crate::plonky3_recursion_impl::recursive::create_recursion_backend;
    use p3_circuit::CircuitBuilder;
    use p3_recursion::{BatchOnly, Target, build_and_prove_aggregation_layer_with_expose};

    type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

    let leg_idx = expose_claim_instance_index(&dual_expose_leg_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "dual-expose note-spend leg leaf carries no expose_claim table — it must \
                     re-expose (segment ++ the 7-slot tuple)"
                .to_string(),
        }
    })?;
    let cs_idx = expose_claim_instance_index(&note_spend_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "note-spend sub-proof leaf carries no exposed tuple (expose_claim) table — \
                     it must be minted via prove_note_spend_leaf_with_claim"
                .to_string(),
        }
    })?;

    let left = dual_expose_leg_leaf.into_recursion_input::<BatchOnly>();
    let right = note_spend_leaf.into_recursion_input::<BatchOnly>();

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>]| {
        let lg = left_apt
            .get(leg_idx)
            .expect("dual-expose note-spend leg's claim instance present");
        let cs = right_apt
            .get(cs_idx)
            .expect("note-spend sub-proof's exposed tuple instance present");
        debug_assert!(
            lg.len() >= SEG_WIDTH + NOTE_SPEND_CLAIM_LEN && cs.len() >= NOTE_SPEND_CLAIM_LEN,
            "dual-expose claim must carry segment ++ tuple; note-spend leaf carries the tuple"
        );
        for k in 0..NOTE_SPEND_CLAIM_LEN {
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
        reason: format!("segmented note-spend binding aggregation node failed: {e:?}"),
    })
}

/// **THE DEPLOYED MINT-HASH BINDING NODE (the 7th carrier's live shape).** The leg is a
/// DUAL-EXPOSE leaf over the deployed `mintVmDescriptor2R24` (`mintV3BridgeHash`): its
/// `expose_claim` = segment lanes `[0 .. SEG_WIDTH)` ++ ONE claimed lane — the published
/// mint-hash PI 46 (the STEP-1 felt-domain `note_spend_mint_hash_felt` the producer filled and
/// the pin welded to the mint row's `param0`). The sub-proof leaf is
/// [`prove_note_spend_leaf_with_claim`] (7 exposed lanes, lane [`NOTE_SPEND_MINT_HASH_PI`] the
/// in-AIR-recomputed identity over the REAL verified spend). The node `connect`s the leg's ONE
/// claimed lane to the leaf's lane 6 and re-exposes the segment.
///
/// ONE lane suffices to bind the WHOLE tuple: lane 6 is the `hash_fact` chain over the leaf's
/// OWN PI-pinned `(nullifier, root, value_lo, asset, dest_fed, value_hi)` (the in-AIR recompute
/// — `forged_mint_hash_does_not_fold`), so under Poseidon2-CR a leg identity that connects IS
/// the identity of exactly that verified spend — which nullifier, from which source root, to
/// which federation, which asset, the full u64 amount. A leg claiming a mint identity no
/// verifying note-spend backs is a `connect` conflict ⇒ UNSAT ⇒ no root.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_note_spend_mint_binding_node_segmented(
    dual_expose_leg_leaf: &RecursionOutput<DreggRecursionConfig>,
    note_spend_leaf: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::ivc_turn_chain::{SEG_WIDTH, expose_claim_instance_index};
    use crate::plonky3_recursion_impl::recursive::create_recursion_backend;
    use p3_circuit::CircuitBuilder;
    use p3_recursion::{BatchOnly, Target, build_and_prove_aggregation_layer_with_expose};

    type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

    let leg_idx = expose_claim_instance_index(&dual_expose_leg_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "dual-expose bridge-mint leg leaf carries no expose_claim table — it must \
                     re-expose (segment ++ the published mint-hash PI)"
                .to_string(),
        }
    })?;
    let cs_idx = expose_claim_instance_index(&note_spend_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "note-spend sub-proof leaf carries no exposed tuple (expose_claim) table — \
                     it must be minted via prove_note_spend_leaf_with_claim"
                .to_string(),
        }
    })?;

    let left = dual_expose_leg_leaf.into_recursion_input::<BatchOnly>();
    let right = note_spend_leaf.into_recursion_input::<BatchOnly>();

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>]| {
        let lg = left_apt
            .get(leg_idx)
            .expect("dual-expose bridge-mint leg's claim instance present");
        let cs = right_apt
            .get(cs_idx)
            .expect("note-spend sub-proof's exposed tuple instance present");
        debug_assert!(
            lg.len() >= SEG_WIDTH + 1 && cs.len() >= NOTE_SPEND_CLAIM_LEN,
            "dual-expose claim must carry segment ++ the mint-hash lane; note-spend leaf \
             carries the 7-lane tuple"
        );
        // THE BINDING TOOTH, IN-CIRCUIT: the leg's published mint identity must equal the
        // note-spend leaf's in-AIR-recomputed identity over its genuine verified spend.
        cb.connect(lg[SEG_WIDTH], cs[NOTE_SPEND_MINT_HASH_PI]);
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
        reason: format!("segmented bridge mint-hash binding aggregation node failed: {e:?}"),
    })
}

/// Read the exposed 7-lane claim tuple off a leaf minted by
/// [`prove_note_spend_leaf_with_claim`].
pub fn read_exposed_note_spend_claim(
    output: &RecursionOutput<DreggRecursionConfig>,
) -> Option<[BabyBear; NOTE_SPEND_CLAIM_LEN]> {
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
    if claims.len() < NOTE_SPEND_CLAIM_LEN {
        return None;
    }
    Some(core::array::from_fn(|i| claims[i]))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ivc_turn_chain::ir2_leaf_wrap_config;
    use dregg_circuit::descriptor_ir2::chip_absorb_all_lanes;
    use dregg_circuit::note_spending_air::test_spending_key;
    use dregg_circuit::poseidon2::hash_many;

    /// THE FEASIBILITY KAT: the chip's arity-7 absorb with inputs
    /// `[pred, t0..t3, 0xFACF, 1]` is BYTE-IDENTICAL to `poseidon2::hash_fact` —
    /// the seeding equivalence the whole fact-site carrier rests on. Also pins the
    /// zero-fact constant `K₀` the non-firing rows degenerate to.
    #[test]
    fn fact_arity7_chip_absorb_matches_hash_fact() {
        let pred = BabyBear::new(123_456);
        let terms = [
            BabyBear::new(7),
            BabyBear::new(88),
            BabyBear::new(999),
            BabyBear::new(1_000_000),
        ];
        let ins = [
            pred,
            terms[0],
            terms[1],
            terms[2],
            terms[3],
            BabyBear::new(NS_FACT_MARK),
            BabyBear::ONE,
        ];
        assert_eq!(
            chip_absorb_all_lanes(7, &ins)[0],
            hash_fact(pred, &terms),
            "arity-7 chip absorb must reproduce hash_fact exactly"
        );
        // Zero-padded terms (the C2g 3-term site shape).
        let ins3 = [
            pred,
            terms[0],
            terms[1],
            terms[2],
            BabyBear::ZERO,
            BabyBear::new(NS_FACT_MARK),
            BabyBear::ONE,
        ];
        assert_eq!(
            chip_absorb_all_lanes(7, &ins3)[0],
            hash_fact(pred, &[terms[0], terms[1], terms[2]]),
            "zero-padded fact absorb must match hash_fact's zero pad"
        );
        // The non-firing degenerate row: all value lanes zero.
        let ins0 = [
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::new(NS_FACT_MARK),
            BabyBear::ONE,
        ];
        assert_eq!(
            chip_absorb_all_lanes(7, &ins0)[0],
            hash_fact(BabyBear::ZERO, &[]),
            "the K₀ zero-fact constant must match the muxed-off digest lane"
        );
    }

    /// The lowering consumes the REAL deployed descriptor and produces the expected
    /// shape: 12 chip sites (7 commitment-chain + 2 nullifier + 1 Merkle + 2 mint),
    /// the C7 WindowGate, and 8 PiBindings (6 source + MINT_ROOT + MINT_HASH).
    #[test]
    fn note_spend_descriptor_lowers() {
        let desc2 = note_spend_to_descriptor2().expect("the real note-spend descriptor lowers");
        assert_eq!(desc2.public_input_count, NOTE_SPEND_CLAIM_LEN);
        let sites = desc2
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
            .count();
        assert_eq!(sites, 12, "7 chain + 2 nullifier + 1 merkle + 2 mint sites");
        let windows = desc2
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
            .count();
        assert_eq!(windows, 1, "the C7 Merkle-chain continuity");
        let pins = desc2
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
            .count();
        assert_eq!(pins, 8, "6 source boundary pins + MINT_ROOT + MINT_HASH");
        // Lane accounting: 12 sites × 7 lanes past the 65-wide extended base.
        assert_eq!(
            desc2.trace_width,
            EXT_BASE_WIDTH + 12 * (CHIP_OUT_LANES - 1)
        );
    }

    /// A REAL full-width witness (raw 32-byte fields + a > 2^30 u64 value, so the
    /// high limb is live). Depth 2 → 4 trace rows (1 commitment + 2 Merkle + 1 pad),
    /// the one-padding-row discipline the deployed DSL circuit's own tests use.
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

    /// THE POSITIVE POLE: an honest REAL note-spend (spending key + 28-limb
    /// commitment + Merkle path) proves as a foldable recursion leaf, and the
    /// exposed claim tuple equals the bound PIs — with lane 6 the in-AIR-recomputed
    /// felt-domain mint identity.
    #[test]
    fn honest_note_spend_proves_as_foldable_leaf_and_exposes_claim() {
        let w = make_witness(0x10);
        let pis = note_spend_leaf_public_inputs(&w);
        assert_eq!(pis.len(), NOTE_SPEND_CLAIM_LEN);
        assert_eq!(
            pis[NOTE_SPEND_MINT_HASH_PI],
            note_spend_mint_hash_felt(pis[0], pis[1], pis[2], pis[3], pis[4], pis[5]),
            "the host mint identity matches the named composition"
        );
        let config = ir2_leaf_wrap_config();

        let output = prove_note_spend_leaf_with_claim(&w, &pis, &config)
            .expect("the honest note-spend must prove as a foldable claim leaf");
        let exposed =
            read_exposed_note_spend_claim(&output).expect("the leaf exposes the 7-lane claim");
        assert_eq!(
            exposed.as_slice(),
            pis.as_slice(),
            "the exposed claim is the bound tuple"
        );
    }

    /// THE NEGATIVE POLE (tuple): a FORGED claim (tampered nullifier lane) has no
    /// satisfying assembly — the `PiBinding{First}` + the chip-bound nullifier chain
    /// refuse it AT THE LEAF; no foldable leaf is minted.
    #[test]
    fn forged_nullifier_does_not_fold() {
        let w = make_witness(0x22);
        let mut pis = note_spend_leaf_public_inputs(&w);
        pis[pi::NULLIFIER] += BabyBear::ONE;
        let config = ir2_leaf_wrap_config();

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_note_spend_leaf(&w, &pis, &config)
        }));
        match result {
            Err(_) => {}     // debug constraint builder panicked on the unsatisfied pin
            Ok(Err(_)) => {} // or the inner self-verify rejected
            Ok(Ok(_)) => panic!("a FORGED nullifier minted a foldable leaf — soundness OPEN"),
        }
    }

    /// THE MINT-BINDING TOOTH: a forged mint_hash lane (every other PI honest) is
    /// refused AT THE LEAF — the in-AIR recompute (the two gated fact sites over the
    /// PI-pinned row-0 columns) plus the PI-6 pin make it UNSAT. This is what makes
    /// the exposed mint identity a WELD, not a prover-chosen scalar.
    #[test]
    fn forged_mint_hash_does_not_fold() {
        let w = make_witness(0x33);
        let mut pis = note_spend_leaf_public_inputs(&w);
        pis[NOTE_SPEND_MINT_HASH_PI] += BabyBear::ONE;
        let config = ir2_leaf_wrap_config();

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_note_spend_leaf(&w, &pis, &config)
        }));
        match result {
            Err(_) => {}
            Ok(Err(_)) => {}
            Ok(Ok(_)) => panic!("a FORGED mint_hash minted a foldable leaf — soundness OPEN"),
        }
    }
}
