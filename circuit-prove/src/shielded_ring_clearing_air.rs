//! Shielded ring-clearing **layout constants + witness types** (2-leg) — NOT an AIR (name is historical).
//!
//! ⚠ Renamed-in-place by docstring (2026-07-16 sweep): this file holds `RING_LEGS`, `RING_CLAIM_LEN` and
//! friends. It authors NO constraints in any of the three dialects (`builder.assert_*`, `Constraint{eval}`
//! closures, `ConstraintExpr` data). The 2-leg shielded ring-clearing algebra of DrEX rung-3
//! (`Market/ShieldedClearing.lean::shielded_ring_clears`, fused by
//! `Market/LedgerRealizationExt.lean::shielded_ring_fused_clears`), at the smallest
//! tractable size (`demoShieldedRing` / `fusedRing` scale, 2 legs, 1 pair).
//!
//! ## What this converts (PROVED-SPEC → BUILT at 2-leg)
//!
//! `docs/deos/{ZK-AUCTION-SUITE.md §3.11/§6, SHIELDED-AUCTIONS-DESIGN.md §3 #5/§6}`
//! name the ring-clearing apex AIR as THE single next build between the proved
//! private-matching theorem and a running private auction. The Lean side is a
//! machine-checked theorem: `shielded_ring_fused_clears` — a `CycleValid` ring whose
//! every leg is `LegFused` (the matcher's committed `node.offerAsset`/`offerAmount`
//! ARE a spent member note's `asset`/`value`) settles CONSERVING + FAIR + FUSED over
//! hidden commitments. This module is the silicon: a foldable AIR that verifies that
//! ring over the shielded-spend leaves.
//!
//! ## The three clauses, and where each is enforced (honest map)
//!
//!   * **(a) each leg is a valid shielded spend** — membership (the note is a member
//!     of the tree at `merkle_root`, its full preimage known) + a FRESH nullifier.
//!     This is ALREADY BUILT: it is exactly what
//!     [`crate::shielded_spend_leaf_adapter::prove_shielded_spend_leaf_with_claim`]
//!     proves, exposing `[nullifier, merkle_root, value_binding]`. The apex FOLDS two
//!     such leaves and BINDS the ring-clearing leaf's per-leg claim to them by an
//!     in-circuit `connect` (a forged/mismatched leg is a `connect` conflict ⇒ UNSAT).
//!
//!   * **(b) the RING structure + FUSION** — enforced IN-AIR in the ring-clearing
//!     descriptor over the two legs' plaintext witness:
//!       - FUSION (`LegFused`): `offer_asset[i] == asset[i]` and
//!         `offer_amount[i] == value[i]` — the matcher clears the NOTE, not a
//!         `MatchNode` beside it. The bound to the REAL note rides the value-binding:
//!         the AIR RE-COMPUTES `value_binding[i] = hash_fact(value[i],[asset[i],
//!         randomness[i],0])` (the SAME Poseidon2 fact-sponge the shielded-spend
//!         circuit's C7a publishes — binding (value, asset) jointly under HashCR, the
//!         PQ value-commitment) and the apex `connect`s it to the leaf's exposed
//!         value_binding,
//!         so `value[i]` is provably the spent note's value under Poseidon2 CR.
//!       - RING (`CycleValid` 2-cycle edges): `offer_asset[0] == want_asset[1]` and
//!         `offer_asset[1] == want_asset[0]` (the leg-0-wants-what-leg-1-offers-and-
//!         vice-versa chain), with the TIGHT-cycle amount match `offer_amount[k] ==
//!         want_min[(k+1)%2]` (the `demoShieldedRing`/`fusedRing` swap is tight;
//!         the general `offer_amount ≥ want_min` partial-fill inequality needs an
//!         in-AIR range gadget and is the named N-leg next rung).
//!       - NO IN-RING DOUBLE-SPEND: `nullifier[0] != nullifier[1]` (an inverse-witness
//!         `≠` gate), the circuit twin of the Lean `#guard legA.claim.nullifier !=
//!         legB.claim.nullifier`.
//!
//!   * **(c) CONSERVATION over the Pedersen value commitments** — enforced IN-AIR as
//!     the homomorphic excess `Σ C_in − Σ C_out = 0` over the REAL two-generator
//!     Pedersen `commit v r = (v, r)` (`Dregg2/Shielded/RealCrypto.lean::pedTwoGen`,
//!     whose binding IS DLog): with that commitment the excess is zero iff
//!     `Σ value_in = Σ value_out` AND `Σ blinding_in = Σ blinding_out`, the exact
//!     hypothesis→conclusion of `ring_conserves_pedersen_list`
//!     (`shielded_ring_value_conserves_hidden`). The AIR enforces both coordinate
//!     sums, so a value-minting ring (Σ value_out too large) has a NON-zero excess and
//!     is UNSAT — the circuit twin of `RealCrypto.pedCommit_mint_refused`.
//!
//!     **(c.range) THE VALUE RANGE GADGET (the field-soundness weld).** The bare
//!     coordinate sum is a BabyBear FIELD equation, and a field equation alone does NOT
//!     testify to INTEGER conservation: a value-minting ring can satisfy `Σ value_in ≡
//!     Σ value_out (mod p)` by WRAPAROUND (an output committed to `p − k`, a "wrapped
//!     negative"), keeping the field sum fixed while minting real value — a genuine
//!     soundness hole in the pre-range AIR. So every conservation value is now
//!     BIT-DECOMPOSED IN-AIR into `VALUE_BITS` boolean columns that recompose to it,
//!     forcing `value ∈ [0, 2^VALUE_BITS)`. With `RING_LEGS · 2^VALUE_BITS ≤ p`
//!     (compile-time asserted), both per-side sums are `< p` (canonical), so the field
//!     conservation gate IS the integer conservation `Σ value_in = Σ value_out` — the
//!     `hval` hypothesis `RealCrypto.ring_conserves_pedersen_list` consumes
//!     (`RealCrypto.twoLeg_noWrap_conservation` /
//!     `RealCrypto.inAir_conservation_refines_pedersen`). This is the in-AIR realization
//!     of the shielded pool's per-output Bulletproof range proof
//!     (`shielded/pool.rs::output_range_proofs`) — moved from ATTESTED off-AIR to a
//!     CIRCUIT constraint (a wraparound mint is now UNSAT in-AIR, not merely attested
//!     out-of-range). No amount is revealed: the values (and their bit witnesses) live
//!     only in the witness (hidden under the hiding PCS); the apex exposes the note
//!     claim prefix plus the constrained endpoint surface, never the amounts themselves.
//!
//! ## HONEST GRADE — 2-leg BUILT; what is in-AIR vs the leaf's exposed claim
//!
//!   * The Pedersen conservation (c) is enforced IN-AIR at the aggregate level (Σ value
//!     + Σ blinding), matching `ring_conserves_pedersen_list` (the 2-generator
//!     `pedTwoGen`, NOT the multi-generator asset commitment); the per-ASSET routing
//!     is carried by the ring edges (b), exactly the two-weld split of the Lean.
//!     PROVED-IN-CIRCUIT: the VALUE-conservation soundness — that the field gate is the
//!     integer conservation, no wraparound mint — is now a CIRCUIT constraint via the
//!     range gadget (c.range), retiring the ATTESTED off-AIR range-proof residual for
//!     the BabyBear-scale (`< 2^VALUE_BITS`) range. NAMED RESIDUAL (still off-AIR /
//!     ATTESTED): (i) the full 64-bit amount range — one BabyBear field caps a 2-leg
//!     conserving sum near `2^30`, so amounts above `2^VALUE_BITS` still lean on the
//!     off-AIR Bulletproof; (ii) full in-AIR Ristretto EC arithmetic — the conservation
//!     runs over the two-COORDINATE `pedTwoGen (v, r)` abstraction, NOT the real group
//!     point `v·G + r·H` over Ristretto; realizing the actual curve-point excess in-AIR
//!     is the EC-in-circuit build named next; (iii) the blinding coordinate's faithful
//!     (group-scalar) reduction, which rides the off-AIR Schnorr excess (a blinding
//!     wraparound mints no value, so it is out of THIS weld's scope).
//!   * The fusion value `value[i]` is bound to the real spent note THROUGH the leaf's
//!     value_binding (Poseidon2 CR), re-computed in-AIR here and `connect`ed to the
//!     leaf's exposed lane 2 — it is NOT a fresh in-AIR opening of a curve point. This
//!     is the same DECO posture the shielded-spend leaf already documents (lane 2 =
//!     the ATTESTED off-AIR Pedersen link); here that link is made a load-bearing
//!     in-AIR fusion gate rather than an off-AIR attestation.
//!   * SCOPE: this is the 2-leg (single-pair), TIGHT-cycle realization. The N-leg
//!     generalization (a variable-length cycle, the `offer_amount ≥ want_min`
//!     partial-fill inequality via an in-AIR range gadget) and the launchpad/DEX
//!     integration (§3.3/§3.12/§3.13) are the next rungs, named not built.
//!   * **ENDPOINT BOUNDARY (load-bearing):** this leaf additionally proves two ordinary
//!     balance-action rows (creator/receiver/asset/amount, funded pre/post balances,
//!     authorization and lifecycle), advances the receipt root by those two actions, and
//!     publishes genuine eight-lane pre/post commitments over two 178-limb kernel blocks.
//!     Every published endpoint lane is a PI pin to a constrained wide Poseidon carrier;
//!     the forged-endpoint KATs below demonstrate that these are not metadata carriers.

use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, EffectVmDescriptor2, LookupSpec, MemBoundaryWitness,
    TID_P2, UMemBoundaryWitness, VmConstraint2, prove_vm_descriptor2_for_config,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

use p3_recursion::{ProveNextLayerParams, RecursionOutput};

use crate::ivc_turn_chain::prove_descriptor_leaf_with_pi_slice_expose;
use crate::joint_turn_aggregation::JointAggError;
use crate::plonky3_recursion_impl::recursive::DreggRecursionConfig;
use crate::shielded::spend_circuit::ShieldedSpendWitness;
use crate::shielded_spend_leaf_adapter::SHIELDED_SPEND_CLAIM_LEN;

/// Extension degree of the recursion config's PCS (the BabyBear-quartic stack).
const D: usize = 4;

/// The `hash_fact` domain-separation marker (`poseidon2::hash_fact` state[5]). Kept
/// file-local (the `descriptor_ir2` twin is private); the note-spend adapter's KAT
/// `fact_arity7_chip_absorb_matches_hash_fact` pins the chip absorb to `hash_fact`.
const NS_FACT_MARK: u32 = 0xFACF;

/// The two-leg ring exposes, per leg, a 3-slot claim `[nullifier, merkle_root,
/// value_binding]` (the SAME tuple the shielded-spend leaf exposes), so the apex can
/// bind each leg to its spend leaf lane-by-lane.
pub const RING_LEG_CLAIM_LEN: usize = SHIELDED_SPEND_CLAIM_LEN; // 3

/// The number of legs in this (smallest tractable) ring.
pub const RING_LEGS: usize = 2;

/// The full cleared-ring claim width: both legs' 3-slot claims, in leg order.
pub const RING_CLAIM_LEN: usize = RING_LEGS * RING_LEG_CLAIM_LEN; // 6

/// Faithful endpoint width.  The first six lanes remain the shielded-spend claims,
/// followed by the two creators, the (fixed) two-action count, the receipt-index
/// roots before/after the batch, and the eight-felt pre/post kernel commitments.
pub const RING_ENDPOINT_PUBLIC_LEN: usize = RING_CLAIM_LEN + 2 + 8 + 8 + 1 + 1 + 1; // 27

/// Public-input offsets of the endpoint surface.
pub mod endpoint_pi {
    use super::RING_CLAIM_LEN;

    pub const CREATOR_0: usize = RING_CLAIM_LEN;
    pub const CREATOR_1: usize = CREATOR_0 + 1;
    pub const TURN_COUNT: usize = CREATOR_1 + 1;
    pub const PRE_RECEIPT_ROOT: usize = TURN_COUNT + 1;
    pub const POST_RECEIPT_ROOT: usize = PRE_RECEIPT_ROOT + 1;
    pub const PRE_COMMIT_8: usize = POST_RECEIPT_ROOT + 1;
    pub const POST_COMMIT_8: usize = PRE_COMMIT_8 + 8;
}

/// Per-leg base column layout (leg-major; leg `i` occupies `[i*LEG_WIDTH ..
/// (i+1)*LEG_WIDTH)`). All are witness columns carried constant on every trace row.
mod lc {
    pub const VALUE: usize = 0;
    pub const RANDOMNESS: usize = 1;
    pub const VB_PAD0: usize = 2;
    pub const VB_PAD1: usize = 3;
    pub const VALUE_BINDING: usize = 4;
    pub const ASSET: usize = 5;
    pub const OFFER_ASSET: usize = 6;
    pub const OFFER_AMOUNT: usize = 7;
    pub const WANT_ASSET: usize = 8;
    pub const WANT_MIN: usize = 9;
    pub const NULLIFIER: usize = 10;
    pub const MERKLE_ROOT: usize = 11;
    pub const OUT_VAL: usize = 12;
    pub const OUT_BLIND: usize = 13;
    pub const LEG_WIDTH: usize = 14;
}

/// Column index of field `f` of leg `i`.
const fn leg_col(i: usize, f: usize) -> usize {
    i * lc::LEG_WIDTH + f
}

/// The shared inverse-witness column for the `nullifier[0] != nullifier[1]` gate.
const NF_DIFF_INV: usize = RING_LEGS * lc::LEG_WIDTH;

/// The pre-range base width (base ring columns + the nullifier-difference inverse).
const BASE_WIDTH: usize = NF_DIFF_INV + 1;

/// **The in-AIR range-gadget bit-width.** Each conservation-relevant value is
/// bit-decomposed into `VALUE_BITS` boolean columns recomposing to the value, so a
/// witnessed value provably lies in `[0, 2^VALUE_BITS)`. This is the FIELD-SOUNDNESS
/// tooth of the conservation gate: without it, `Σ value_in − Σ value_out == 0` is only a
/// BabyBear FIELD equation, satisfiable by a value-minting ring via wraparound (an output
/// committed to `p − k`, a "wrapped negative"). With every value range-bounded and
/// `RING_LEGS · 2^VALUE_BITS ≤ p`, both per-side sums are `< p` (canonical), so the field
/// equation IS the INTEGER conservation `Σ value_in = Σ value_out`. `29` is the largest
/// width the single BabyBear field admits for a 2-leg conserving sum
/// (`2·2^29 = 2^30 < p ≈ 2^30.9`); the full 64-bit amount range stays the off-AIR
/// Bulletproof (named residual — one BabyBear field caps a 2-leg sum near `2^30`).
const VALUE_BITS: usize = 29;

/// No-wraparound guarantee, checked at compile time: `RING_LEGS · 2^VALUE_BITS ≤ p`, so
/// neither the input nor the output value-sum can wrap BabyBear and the field conservation
/// gate is exactly integer conservation.
const _: () = assert!(
    (RING_LEGS as u64) * (1u64 << VALUE_BITS) <= dregg_circuit::field::BABYBEAR_P as u64,
    "VALUE_BITS too large: a 2-leg value-sum could wrap BabyBear, re-opening wraparound mint"
);

/// The value columns the range gadget bounds: both legs' spent-note `value` and both legs'
/// created-note `out_val`. Range-checking BOTH sides makes the field⇒integer conservation
/// reduction self-contained within this AIR (the output half is the in-AIR analog of the
/// shielded pool's per-output Bulletproof range proof; the input half closes the dual
/// hole of an input note carrying a wrapped value).
const RANGE_TARGET_COLS: [usize; 4] = [
    leg_col(0, lc::VALUE),
    leg_col(1, lc::VALUE),
    leg_col(0, lc::OUT_VAL),
    leg_col(1, lc::OUT_VAL),
];

/// First column of the range bit-decomposition block (right after the base region; the
/// chip lanes are appended AFTER the range block).
const RANGE_BIT_BASE: usize = BASE_WIDTH;

/// Total width of the range bit block: one `VALUE_BITS`-wide decomposition per target.
const RANGE_WIDTH: usize = RANGE_TARGET_COLS.len() * VALUE_BITS;

/// The pre-chip-lane trace width (base ring columns + the range bit block). The chip lanes
/// (`alloc_lanes`) grow the width from here.
const PRE_LANE_WIDTH: usize = BASE_WIDTH + RANGE_WIDTH;

/// The two existing value-binding sites each allocate seven auxiliary output lanes.
const VALUE_BINDING_LANE_WIDTH: usize = RING_LEGS * (CHIP_OUT_LANES - 1);

/// First endpoint column, after the note algebra and its two value-binding lane groups.
const ENDPOINT_BASE: usize = PRE_LANE_WIDTH + VALUE_BINDING_LANE_WIDTH;

/// Per-action endpoint row.  The balance rows are deliberately explicit: the endpoint
/// commitment is computed from these columns, so creator/asset/amount/auth/lifecycle and
/// both sides of each debit/credit cannot be swapped out behind a carried public root.
mod ac {
    pub const CREATOR: usize = 0;
    pub const RECEIVER: usize = 1;
    pub const ASSET: usize = 2;
    pub const AMOUNT: usize = 3;
    pub const SRC_PRE: usize = 4;
    pub const SRC_POST: usize = 5;
    pub const DST_PRE: usize = 6;
    pub const DST_POST: usize = 7;
    pub const AUTHORIZED: usize = 8;
    pub const SRC_LIVE: usize = 9;
    pub const DST_LIVE: usize = 10;
    pub const ACTION_HASH: usize = 11;
    pub const WIDTH: usize = 12;
}

const fn action_col(i: usize, f: usize) -> usize {
    ENDPOINT_BASE + i * ac::WIDTH + f
}

const ENDPOINT_SHARED_BASE: usize = ENDPOINT_BASE + RING_LEGS * ac::WIDTH;
const CREATOR_DIFF_INV: usize = ENDPOINT_SHARED_BASE;
const ASSET_DIFF_INV: usize = CREATOR_DIFF_INV + 1;
const AMOUNT_0_INV: usize = ASSET_DIFF_INV + 1;
const AMOUNT_1_INV: usize = AMOUNT_0_INV + 1;
const TURN_COUNT_COL: usize = AMOUNT_1_INV + 1;
const PRE_RECEIPT_ROOT_COL: usize = TURN_COUNT_COL + 1;
const MID_RECEIPT_ROOT_COL: usize = PRE_RECEIPT_ROOT_COL + 1;
const POST_RECEIPT_ROOT_COL: usize = MID_RECEIPT_ROOT_COL + 1;

/// The endpoint commitment uses the deployed wide carrier geometry: a pre-iroot block followed by
/// the receipt-index root, with an eight-felt carrier at every Poseidon step.  This is the same
/// `wireCommitR8` shape as the live wide cohort.
///
/// ⚑ PINNED 2026-07-31 (the 178 -> 184 ninth-lane flag day). That sentence was a CLAIM carried by a
/// hand-written `178` with nothing checking it, so a geometry flag day would have moved the live
/// cohort and left this endpoint silently disagreeing while every build stayed green — "breaking it
/// silently", which is the only cost `CLAUDE.md` recognises. The value is now PROJECTED from the
/// Lean-emitted table and the pin below refuses to COMPILE if the two ever part.
const ENDPOINT_NUM_PRE_LIMBS: usize = dregg_circuit::effect_vm::layout_generated::NUM_PRE_LIMBS;

const _: () = {
    assert!(
        ENDPOINT_NUM_PRE_LIMBS == dregg_circuit::effect_vm::layout_generated::NUM_PRE_LIMBS,
        "the ring-clearing endpoint claims the deployed wide geometry; it must BE it"
    );
    assert!(
        ENDPOINT_NUM_PRE_LIMBS >= 4 && (ENDPOINT_NUM_PRE_LIMBS - 4) % 3 == 0,
        "wireCommitR8 folds the body in arity-3 groups after the arity-4 head (Legal.bodyAligned)"
    );
};
const PRE_KERNEL_LIMBS_BASE: usize = POST_RECEIPT_ROOT_COL + 1;
const PRE_KERNEL_IROOT_COL: usize = PRE_KERNEL_LIMBS_BASE + ENDPOINT_NUM_PRE_LIMBS;
const POST_KERNEL_LIMBS_BASE: usize = PRE_KERNEL_IROOT_COL + 1;
const POST_KERNEL_IROOT_COL: usize = POST_KERNEL_LIMBS_BASE + ENDPOINT_NUM_PRE_LIMBS;

const fn wide_carriers_for_limbs(n: usize) -> usize {
    let body = n - 4;
    1 + body / 3 + body % 3 + 1
}

const ENDPOINT_WIDE_CARRIERS: usize = wide_carriers_for_limbs(ENDPOINT_NUM_PRE_LIMBS); // 60
const ENDPOINT_WIDE_BLOCK_SPAN: usize = ENDPOINT_WIDE_CARRIERS * CHIP_OUT_LANES;
const RECEIPT_SITE_COUNT: usize = 4; // two action hashes + two receipt-chain hashes
const RECEIPT_LANE_BASE: usize = POST_KERNEL_IROOT_COL + 1;
const ENDPOINT_HOST_WIDTH: usize = RECEIPT_LANE_BASE + RECEIPT_SITE_COUNT * (CHIP_OUT_LANES - 1);
const PRE_WIDE_CARRIER_BASE: usize = ENDPOINT_HOST_WIDTH;
const POST_WIDE_CARRIER_BASE: usize = PRE_WIDE_CARRIER_BASE + ENDPOINT_WIDE_BLOCK_SPAN;
const ENDPOINT_TRACE_WIDTH: usize = POST_WIDE_CARRIER_BASE + ENDPOINT_WIDE_BLOCK_SPAN;
const FINAL_TRACE_WIDTH: usize = ENDPOINT_TRACE_WIDTH;
const ENDPOINT_COMMIT_CARRIER: usize = ENDPOINT_WIDE_CARRIERS - 1;

const _: () = {
    // ⚑ DERIVED, not pinned to the 178-limb literals (the nine-lane epoch moved them).
    // This file's doc CLAIMED "the same wireCommitR8 shape as the live wide cohort" with nothing
    // checking it; these now assert that relation instead of restating two numbers.
    assert!(ENDPOINT_WIDE_CARRIERS == dregg_circuit::effect_vm::trace_rotated::WIDE_NUM_CARRIERS);
    assert!(ENDPOINT_COMMIT_CARRIER + 1 == ENDPOINT_WIDE_CARRIERS);
    assert!(POST_WIDE_CARRIER_BASE + ENDPOINT_WIDE_BLOCK_SPAN == ENDPOINT_TRACE_WIDTH);
};

/// Column of bit `j` of range target `t`.
const fn range_bit_col(t: usize, j: usize) -> usize {
    RANGE_BIT_BASE + t * VALUE_BITS + j
}

/// The main-trace height (a power of two ≥ `MIN_TABLE_HEIGHT`; every row carries the
/// same constant ring data — the gates fire on the transition rows, the PiBindings on
/// the first row).
const TRACE_HEIGHT: usize = 8;

/// `x − y` as a `LeanExpr` (`x + (−1)·y`).
fn sub(x: LeanExpr, y: LeanExpr) -> LeanExpr {
    LeanExpr::add(x, LeanExpr::mul(LeanExpr::Const(-1), y))
}

/// A pure-row vanishing gate.
fn gate(body: LeanExpr) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// `col_a − col_b == 0`.
fn eq_gate(col_a: usize, col_b: usize) -> VmConstraint2 {
    gate(sub(LeanExpr::Var(col_a), LeanExpr::Var(col_b)))
}

/// Build the arity-7 `TID_P2` chip lookup carrying one UNGATED `hash_fact` site (the
/// value-binding recompute): the tuple is unconditionally the genuine fact absorb
/// `[7, pred, t0..t3, 0xFACF, 1, out, lane1..7]`. File-local twin of the shielded-spend
/// adapter's `fact_site` at `SiteSel::Always` (new-files-only lane discipline).
fn fact_site_always(output_col: usize, input_cols: &[usize], lane_base: usize) -> VmConstraint2 {
    assert!(
        !input_cols.is_empty() && input_cols.len() <= 5,
        "fact site expects 1..=5 input columns (pred + ≤4 terms)"
    );
    let mut tuple: Vec<LeanExpr> = Vec::with_capacity(CHIP_TUPLE_LEN);
    tuple.push(LeanExpr::Const(7));
    for i in 0..CHIP_RATE {
        let e = match i {
            0..=4 => match input_cols.get(i) {
                Some(&c) => LeanExpr::Var(c),
                None => LeanExpr::Const(0),
            },
            5 => LeanExpr::Const(NS_FACT_MARK as i64),
            6 => LeanExpr::Const(1),
            _ => LeanExpr::Const(0),
        };
        tuple.push(e);
    }
    // out0 = the digest lane = the site's output column (fire == 1, hold == 0).
    tuple.push(LeanExpr::Var(output_col));
    // lanes 1..8: the genuine permutation lanes the chip AIR equality-binds.
    for j in 0..(CHIP_OUT_LANES - 1) {
        tuple.push(LeanExpr::Var(lane_base + j));
    }
    debug_assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    })
}

/// One chip-faithful eight-lane Poseidon absorb.  `inputs` is the exact arity-tagged
/// input (four limbs for the head, or the previous eight-felt carrier plus three new
/// limbs for every body/final step); `output_base..output_base+8` is the next carrier.
fn wide_site_always(
    arity: usize,
    inputs: impl IntoIterator<Item = LeanExpr>,
    output_base: usize,
) -> VmConstraint2 {
    assert!(arity <= CHIP_RATE);
    let input_vec: Vec<LeanExpr> = inputs.into_iter().collect();
    assert_eq!(input_vec.len(), arity);
    let mut tuple = Vec::with_capacity(CHIP_TUPLE_LEN);
    tuple.push(LeanExpr::Const(arity as i64));
    for i in 0..CHIP_RATE {
        tuple.push(input_vec.get(i).cloned().unwrap_or(LeanExpr::Const(0)));
    }
    for j in 0..CHIP_OUT_LANES {
        tuple.push(LeanExpr::Var(output_base + j));
    }
    debug_assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    })
}

/// Append the exact `wireCommitR8` lookup chain for one 178-limb endpoint block.
fn append_endpoint_wide_commit_constraints(
    constraints: &mut Vec<VmConstraint2>,
    limb_base: usize,
    receipt_root_col: usize,
    carrier_base: usize,
) {
    constraints.push(wide_site_always(
        4,
        (0..4).map(|j| LeanExpr::Var(limb_base + j)),
        carrier_base,
    ));
    let mut carrier = 1usize;
    let mut limb = 4usize;
    while limb < ENDPOINT_NUM_PRE_LIMBS {
        let remaining = ENDPOINT_NUM_PRE_LIMBS - limb;
        let take = if remaining >= 3 { 3 } else { 1 };
        let arity = CHIP_OUT_LANES + take;
        let inputs = (0..CHIP_OUT_LANES)
            .map(|j| LeanExpr::Var(carrier_base + (carrier - 1) * CHIP_OUT_LANES + j))
            .chain((0..take).map(|j| LeanExpr::Var(limb_base + limb + j)));
        constraints.push(wide_site_always(
            arity,
            inputs,
            carrier_base + carrier * CHIP_OUT_LANES,
        ));
        carrier += 1;
        limb += take;
    }
    let final_inputs = (0..CHIP_OUT_LANES)
        .map(|j| LeanExpr::Var(carrier_base + (carrier - 1) * CHIP_OUT_LANES + j))
        .chain([
            LeanExpr::Var(receipt_root_col),
            LeanExpr::Const(0),
            LeanExpr::Const(0),
        ]);
    constraints.push(wide_site_always(
        11,
        final_inputs,
        carrier_base + carrier * CHIP_OUT_LANES,
    ));
    debug_assert_eq!(carrier, ENDPOINT_COMMIT_CARRIER);
}

/// Build the endpoint-carrying 2-leg ring-clearing descriptor AIR. Its 27 PIs are
/// the six spend-claim lanes, two creators, action count, pre/post receipt roots, and
/// eight-felt pre/post commitments. The note prefix remains the apex `connect`
/// surface; every added endpoint is constrained by the action and wide-commit gates.
pub fn shielded_ring_clear_descriptor() -> EffectVmDescriptor2 {
    let mut constraints: Vec<VmConstraint2> = Vec::new();
    let mut width = PRE_LANE_WIDTH;
    let mut alloc_lanes = || {
        let base = width;
        width += CHIP_OUT_LANES - 1;
        base
    };

    // --- (b.i) FUSION: the matcher's offer IS the note (per leg). ---
    for i in 0..RING_LEGS {
        // offer_asset[i] == asset[i]
        constraints.push(eq_gate(leg_col(i, lc::OFFER_ASSET), leg_col(i, lc::ASSET)));
        // offer_amount[i] == value[i]
        constraints.push(eq_gate(leg_col(i, lc::OFFER_AMOUNT), leg_col(i, lc::VALUE)));
    }

    // --- (b.ii) RING (CycleValid 2-cycle edges) + TIGHT-cycle amount match. ---
    // offer_asset[0] == want_asset[1], offer_asset[1] == want_asset[0].
    constraints.push(eq_gate(
        leg_col(0, lc::OFFER_ASSET),
        leg_col(1, lc::WANT_ASSET),
    ));
    constraints.push(eq_gate(
        leg_col(1, lc::OFFER_ASSET),
        leg_col(0, lc::WANT_ASSET),
    ));
    // offer_amount[0] == want_min[1], offer_amount[1] == want_min[0] (tight swap).
    constraints.push(eq_gate(
        leg_col(0, lc::OFFER_AMOUNT),
        leg_col(1, lc::WANT_MIN),
    ));
    constraints.push(eq_gate(
        leg_col(1, lc::OFFER_AMOUNT),
        leg_col(0, lc::WANT_MIN),
    ));

    // --- (b.iii) NO IN-RING DOUBLE-SPEND: nullifier[0] != nullifier[1]. ---
    // (nf₀ − nf₁)·inv − 1 == 0 : satisfiable iff nf₀ ≠ nf₁ (an inverse exists).
    constraints.push(gate(sub(
        LeanExpr::mul(
            sub(
                LeanExpr::Var(leg_col(0, lc::NULLIFIER)),
                LeanExpr::Var(leg_col(1, lc::NULLIFIER)),
            ),
            LeanExpr::Var(NF_DIFF_INV),
        ),
        LeanExpr::Const(1),
    )));

    // --- (c) PEDERSEN CONSERVATION: Σ C_in − Σ C_out = 0 over pedTwoGen (v, r). ---
    // value coordinate: (value₀ + value₁) − (out_val₀ + out_val₁) == 0
    constraints.push(gate(sub(
        LeanExpr::add(
            LeanExpr::Var(leg_col(0, lc::VALUE)),
            LeanExpr::Var(leg_col(1, lc::VALUE)),
        ),
        LeanExpr::add(
            LeanExpr::Var(leg_col(0, lc::OUT_VAL)),
            LeanExpr::Var(leg_col(1, lc::OUT_VAL)),
        ),
    )));
    // blinding coordinate: (rand₀ + rand₁) − (out_blind₀ + out_blind₁) == 0.
    // (The blinding coordinate is NOT range-checked in-AIR: a blinding wraparound mints no
    // VALUE — it is the group-scalar coordinate, whose faithful reduction rides the real
    // Schnorr excess off-AIR. Only the VALUE coordinate carries the mint hazard the range
    // gadget below closes.)
    constraints.push(gate(sub(
        LeanExpr::add(
            LeanExpr::Var(leg_col(0, lc::RANDOMNESS)),
            LeanExpr::Var(leg_col(1, lc::RANDOMNESS)),
        ),
        LeanExpr::add(
            LeanExpr::Var(leg_col(0, lc::OUT_BLIND)),
            LeanExpr::Var(leg_col(1, lc::OUT_BLIND)),
        ),
    )));

    // --- (c.range) THE VALUE RANGE GADGET: every conservation value ∈ [0, 2^VALUE_BITS). ---
    // This is what makes the field conservation gate above IMPLY integer conservation: with
    // both per-side sums range-bounded below the wrap point (`RING_LEGS·2^VALUE_BITS ≤ p`,
    // checked at compile time), `Σ value_in ≡ Σ value_out (mod p)` forces `Σ value_in =
    // Σ value_out` over ℤ. A value-minting ring that balances the FIELD equation by
    // wraparound (an output committed to `p − k`) has no `VALUE_BITS`-bit preimage and is
    // UNSAT at the recompose gate. This is the in-AIR realization of the shielded pool's
    // per-output Bulletproof range proof (`shielded/pool.rs`) — moved from ATTESTED off-AIR
    // to a CIRCUIT constraint (over the BabyBear no-wrap range; the full 64-bit range stays
    // the off-AIR Bulletproof, named).
    for (t, &col) in RANGE_TARGET_COLS.iter().enumerate() {
        // Each bit column is boolean: b·(b − 1) == 0.
        for j in 0..VALUE_BITS {
            let b = LeanExpr::Var(range_bit_col(t, j));
            constraints.push(gate(LeanExpr::mul(b.clone(), sub(b, LeanExpr::Const(1)))));
        }
        // Recompose: col − Σⱼ 2ʲ·bitⱼ == 0 (so a witnessed `col` has an exact bit preimage).
        let mut acc = LeanExpr::Var(col);
        for j in 0..VALUE_BITS {
            acc = sub(
                acc,
                LeanExpr::mul(
                    LeanExpr::Const(1i64 << j),
                    LeanExpr::Var(range_bit_col(t, j)),
                ),
            );
        }
        constraints.push(gate(acc));
    }

    // --- the value-binding pad cells are constant-zero (so the fact absorbs
    // [asset, randomness, 0]; vb_pad1 is now vestigial). ---
    for i in 0..RING_LEGS {
        constraints.push(gate(LeanExpr::Var(leg_col(i, lc::VB_PAD0))));
        constraints.push(gate(LeanExpr::Var(leg_col(i, lc::VB_PAD1))));
    }

    // --- the value-binding RECOMPUTE (per leg): value_binding[i] ==
    // hash_fact(value[i], [asset[i], randomness[i], 0]). The fusion anchor, now binding
    // the ASSET too (the PQ HashCR value-commitment binds (value, asset) jointly). ---
    for i in 0..RING_LEGS {
        let site = fact_site_always(
            leg_col(i, lc::VALUE_BINDING),
            &[
                leg_col(i, lc::VALUE),
                leg_col(i, lc::ASSET),
                leg_col(i, lc::RANDOMNESS),
                leg_col(i, lc::VB_PAD0),
            ],
            alloc_lanes(),
        );
        constraints.push(site);
    }

    debug_assert_eq!(width, ENDPOINT_BASE);

    // --- THE ENDPOINT APEX: two genuine balance rows, not public carriers. ---
    // The receiver is the next creator in the two-cycle, and the action tuple is the
    // exact matcher offer already fused to the spent note above.
    for i in 0..RING_LEGS {
        constraints.push(eq_gate(
            action_col(i, ac::RECEIVER),
            action_col(1 - i, ac::CREATOR),
        ));
        constraints.push(eq_gate(
            action_col(i, ac::ASSET),
            leg_col(i, lc::OFFER_ASSET),
        ));
        constraints.push(eq_gate(
            action_col(i, ac::AMOUNT),
            leg_col(i, lc::OFFER_AMOUNT),
        ));

        // The endpoint normal form represents the funded two-action batch with the
        // offered balance entirely debited and the receiver's corresponding balance
        // entirely credited.  These equations are integer-sound because `amount` is
        // range-constrained above; no field-wrap balance can inhabit this normal form.
        constraints.push(eq_gate(
            action_col(i, ac::SRC_PRE),
            action_col(i, ac::AMOUNT),
        ));
        constraints.push(gate(LeanExpr::Var(action_col(i, ac::SRC_POST))));
        constraints.push(gate(LeanExpr::Var(action_col(i, ac::DST_PRE))));
        constraints.push(eq_gate(
            action_col(i, ac::DST_POST),
            action_col(i, ac::AMOUNT),
        ));

        // Both ordinary balance actions must pass authorization and lifecycle on both
        // endpoints.  A zero/forged guard is not metadata: it violates a gate.
        for f in [ac::AUTHORIZED, ac::SRC_LIVE, ac::DST_LIVE] {
            constraints.push(gate(sub(
                LeanExpr::Var(action_col(i, f)),
                LeanExpr::Const(1),
            )));
        }
    }

    // Cycle participants and assets are distinct.  Besides matching `CycleValid`'s
    // creator tooth, asset distinctness prevents the two balance rows from aliasing the
    // same `(cell, asset)` slot while using the endpoint normal form above.
    constraints.push(gate(sub(
        LeanExpr::mul(
            sub(
                LeanExpr::Var(action_col(0, ac::CREATOR)),
                LeanExpr::Var(action_col(1, ac::CREATOR)),
            ),
            LeanExpr::Var(CREATOR_DIFF_INV),
        ),
        LeanExpr::Const(1),
    )));
    constraints.push(gate(sub(
        LeanExpr::mul(
            sub(
                LeanExpr::Var(action_col(0, ac::ASSET)),
                LeanExpr::Var(action_col(1, ac::ASSET)),
            ),
            LeanExpr::Var(ASSET_DIFF_INV),
        ),
        LeanExpr::Const(1),
    )));
    // A DrEX clearing requires strictly-positive wants.  The tight two-cycle equates
    // each want minimum with the counterparty's offered amount, so a nonzero inverse
    // for each action amount plus the 29-bit range decomposition below is exactly
    // `0 < wantMin` over the canonical integer range.
    for (i, inv_col) in [(0usize, AMOUNT_0_INV), (1usize, AMOUNT_1_INV)] {
        constraints.push(gate(sub(
            LeanExpr::mul(
                LeanExpr::Var(action_col(i, ac::AMOUNT)),
                LeanExpr::Var(inv_col),
            ),
            LeanExpr::Const(1),
        )));
    }
    constraints.push(gate(sub(
        LeanExpr::Var(TURN_COUNT_COL),
        LeanExpr::Const(RING_LEGS as i64),
    )));

    // The truthful two-action receipt chain.  Each action hash binds
    // `(creator,receiver,asset,amount)`, then the two hashes advance the prior receipt
    // root in execution order.  The post state commitment below absorbs the resulting
    // root, so omitting/reordering either action moves both the published receipt root
    // and the published post commitment.
    constraints.push(fact_site_always(
        action_col(0, ac::ACTION_HASH),
        &[
            action_col(0, ac::CREATOR),
            action_col(0, ac::CREATOR),
            action_col(0, ac::RECEIVER),
            action_col(0, ac::AMOUNT),
        ],
        RECEIPT_LANE_BASE,
    ));
    constraints.push(fact_site_always(
        action_col(1, ac::ACTION_HASH),
        &[
            action_col(1, ac::CREATOR),
            action_col(1, ac::CREATOR),
            action_col(1, ac::RECEIVER),
            action_col(1, ac::AMOUNT),
        ],
        RECEIPT_LANE_BASE + (CHIP_OUT_LANES - 1),
    ));
    // The pre-root is the already-committed receipt-index root of the decoded pre
    // kernel.  It may represent any prior log; the two constrained updates below are
    // what force the exact two-action suffix.
    constraints.push(fact_site_always(
        MID_RECEIPT_ROOT_COL,
        &[PRE_RECEIPT_ROOT_COL, action_col(0, ac::ACTION_HASH)],
        RECEIPT_LANE_BASE + 2 * (CHIP_OUT_LANES - 1),
    ));
    constraints.push(fact_site_always(
        POST_RECEIPT_ROOT_COL,
        &[MID_RECEIPT_ROOT_COL, action_col(1, ac::ACTION_HASH)],
        RECEIPT_LANE_BASE + 3 * (CHIP_OUT_LANES - 1),
    ));

    // Canonical ring-kernel block.  Every nonzero limb is tied to an in-circuit
    // semantic column; every unassigned limb is forced zero.  The BEFORE/AFTER blocks
    // differ exactly at the four debited/credited balance slots.  Creator, action,
    // auth/lifecycle, note-claim and count material is included on both sides.
    let common_limb_cols = [
        (0usize, action_col(0, ac::CREATOR)),
        (1, action_col(1, ac::CREATOR)),
        (2, action_col(0, ac::ASSET)),
        (3, action_col(1, ac::ASSET)),
        (8, action_col(0, ac::AUTHORIZED)),
        (9, action_col(1, ac::AUTHORIZED)),
        (10, action_col(0, ac::SRC_LIVE)),
        (11, action_col(1, ac::SRC_LIVE)),
        (12, action_col(0, ac::DST_LIVE)),
        (13, action_col(1, ac::DST_LIVE)),
        (14, TURN_COUNT_COL),
        (15, leg_col(0, lc::NULLIFIER)),
        (16, leg_col(1, lc::NULLIFIER)),
        (17, leg_col(0, lc::MERKLE_ROOT)),
        (18, leg_col(1, lc::MERKLE_ROOT)),
        (19, leg_col(0, lc::VALUE_BINDING)),
        (20, leg_col(1, lc::VALUE_BINDING)),
    ];
    let pre_balance_cols = [
        (4usize, action_col(0, ac::SRC_PRE)),
        (5, action_col(0, ac::DST_PRE)),
        (6, action_col(1, ac::SRC_PRE)),
        (7, action_col(1, ac::DST_PRE)),
    ];
    let post_balance_cols = [
        (4usize, action_col(0, ac::SRC_POST)),
        (5, action_col(0, ac::DST_POST)),
        (6, action_col(1, ac::SRC_POST)),
        (7, action_col(1, ac::DST_POST)),
    ];
    for j in 0..ENDPOINT_NUM_PRE_LIMBS {
        if let Some((_, c)) = common_limb_cols.iter().find(|(k, _)| *k == j) {
            constraints.push(eq_gate(PRE_KERNEL_LIMBS_BASE + j, *c));
            constraints.push(eq_gate(POST_KERNEL_LIMBS_BASE + j, *c));
        } else {
            if let Some((_, c)) = pre_balance_cols.iter().find(|(k, _)| *k == j) {
                constraints.push(eq_gate(PRE_KERNEL_LIMBS_BASE + j, *c));
            } else {
                constraints.push(gate(LeanExpr::Var(PRE_KERNEL_LIMBS_BASE + j)));
            }
            if let Some((_, c)) = post_balance_cols.iter().find(|(k, _)| *k == j) {
                constraints.push(eq_gate(POST_KERNEL_LIMBS_BASE + j, *c));
            } else {
                constraints.push(gate(LeanExpr::Var(POST_KERNEL_LIMBS_BASE + j)));
            }
        }
    }
    constraints.push(eq_gate(PRE_KERNEL_IROOT_COL, PRE_RECEIPT_ROOT_COL));
    constraints.push(eq_gate(POST_KERNEL_IROOT_COL, POST_RECEIPT_ROOT_COL));

    // The load-bearing eight-lane pre/post commitments.  These are genuine wide
    // Poseidon chains over the in-circuit blocks and receipt roots, not exposed bytes.
    append_endpoint_wide_commit_constraints(
        &mut constraints,
        PRE_KERNEL_LIMBS_BASE,
        PRE_KERNEL_IROOT_COL,
        PRE_WIDE_CARRIER_BASE,
    );
    append_endpoint_wide_commit_constraints(
        &mut constraints,
        POST_KERNEL_LIMBS_BASE,
        POST_KERNEL_IROOT_COL,
        POST_WIDE_CARRIER_BASE,
    );

    // --- the exposed endpoint claim, pinned to the public inputs. ---
    for i in 0..RING_LEGS {
        for (slot, col) in [lc::NULLIFIER, lc::MERKLE_ROOT, lc::VALUE_BINDING]
            .into_iter()
            .enumerate()
        {
            constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col: leg_col(i, col),
                pi_index: i * RING_LEG_CLAIM_LEN + slot,
            }));
        }
    }
    constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::First,
        col: action_col(0, ac::CREATOR),
        pi_index: endpoint_pi::CREATOR_0,
    }));
    constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::First,
        col: action_col(1, ac::CREATOR),
        pi_index: endpoint_pi::CREATOR_1,
    }));
    for j in 0..8 {
        constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::First,
            col: PRE_WIDE_CARRIER_BASE + ENDPOINT_COMMIT_CARRIER * 8 + j,
            pi_index: endpoint_pi::PRE_COMMIT_8 + j,
        }));
        constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::Last,
            col: POST_WIDE_CARRIER_BASE + ENDPOINT_COMMIT_CARRIER * 8 + j,
            pi_index: endpoint_pi::POST_COMMIT_8 + j,
        }));
    }
    for (col, pi_index) in [
        (TURN_COUNT_COL, endpoint_pi::TURN_COUNT),
        (PRE_RECEIPT_ROOT_COL, endpoint_pi::PRE_RECEIPT_ROOT),
        (POST_RECEIPT_ROOT_COL, endpoint_pi::POST_RECEIPT_ROOT),
    ] {
        constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::First,
            col,
            pi_index,
        }));
    }

    EffectVmDescriptor2 {
        name: "shielded-ring-clear-2-endpoint-wide".into(),
        trace_width: FINAL_TRACE_WIDTH,
        public_input_count: RING_ENDPOINT_PUBLIC_LEN,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// A 2-leg shielded ring witness: the two shielded spends (each an honest
/// [`ShieldedSpendWitness`]) plus the ring-level matcher fields and the created
/// (output) notes. `honest_demo` builds a genuine tight fused swap; teeth perturb
/// individual fields.
#[derive(Clone, Debug)]
pub struct ShieldedRing2 {
    /// Per-leg shielded spend (asset_type/value/randomness ARE the fused note fields).
    pub leg: [ShieldedSpendWitness; RING_LEGS],
    /// Per-leg matcher offer asset (fused: should equal `leg[i].asset_type`).
    pub offer_asset: [BabyBear; RING_LEGS],
    /// Per-leg matcher offer amount (fused: should equal `leg[i].value`).
    pub offer_amount: [BabyBear; RING_LEGS],
    /// Per-leg matcher wanted asset (ring: `want_asset[i] == offer_asset[1−i]`).
    pub want_asset: [BabyBear; RING_LEGS],
    /// Per-leg matcher wanted minimum (tight: `want_min[i] == offer_amount[1−i]`).
    pub want_min: [BabyBear; RING_LEGS],
    /// Per-leg created (output) note value — Σ out_val must equal Σ leg.value.
    pub out_val: [BabyBear; RING_LEGS],
    /// Per-leg created (output) note blinding — Σ out_blind must equal Σ leg.randomness.
    pub out_blind: [BabyBear; RING_LEGS],
}

/// A real depth-4 shielded-spend witness for one leg (forward-chained padding makes
/// the ungated membership/leaf/value-binding hashes hold on every trace row).
fn demo_leg_witness(tag: u8, asset: u32, value: u32) -> ShieldedSpendWitness {
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
        value: BabyBear::new(value),
        asset_type: BabyBear::new(asset),
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

impl ShieldedRing2 {
    /// The genuine `demoShieldedRing`/`fusedRing` tight swap: leg 0 offers (asset 0,
    /// value 3) and wants (asset 1, 4); leg 1 offers (asset 1, value 4) and wants
    /// (asset 0, 3). Fused (offer == note), a valid `CycleValid` 2-cycle, and
    /// value-neutral (Σ value_in = 3+4 = Σ value_out; Σ blinding balanced by swapping
    /// the two randomnesses onto the outputs).
    pub fn honest_demo() -> Self {
        let leg0 = demo_leg_witness(0x10, 0, 3);
        let leg1 = demo_leg_witness(0x20, 1, 4);
        let out_blind = [leg1.randomness, leg0.randomness]; // Σ preserved
        ShieldedRing2 {
            offer_asset: [leg0.asset_type, leg1.asset_type],
            offer_amount: [leg0.value, leg1.value],
            // ring edges: want_asset[i] = offer_asset[1-i]
            want_asset: [leg1.asset_type, leg0.asset_type],
            // tight: want_min[i] = offer_amount[1-i]
            want_min: [leg1.value, leg0.value],
            // leg i receives the counterparty's offered value (value-neutral swap)
            out_val: [leg1.value, leg0.value],
            out_blind,
            leg: [leg0, leg1],
        }
    }

    /// The per-leg 3-slot claim `[nullifier, merkle_root, value_binding]` (the exact
    /// PI tuple the shielded-spend leaf exposes for leg `i`).
    pub fn leg_claim(&self, i: usize) -> [BabyBear; RING_LEG_CLAIM_LEN] {
        [
            self.leg[i].nullifier(),
            self.leg[i].merkle_root(),
            self.leg[i].value_binding(),
        ]
    }

    /// The full endpoint public-input tuple.  The six note lanes remain the prefix,
    /// followed by creators, the two-action count, receipt roots, and the faithful
    /// pre/post commitments.
    pub fn public_inputs(&self) -> Vec<BabyBear> {
        let row = self.base_row();
        let mut pis = Vec::with_capacity(RING_ENDPOINT_PUBLIC_LEN);
        for i in 0..RING_LEGS {
            pis.extend_from_slice(&self.leg_claim(i));
        }
        pis.push(row[action_col(0, ac::CREATOR)]);
        pis.push(row[action_col(1, ac::CREATOR)]);
        pis.push(row[TURN_COUNT_COL]);
        pis.push(row[PRE_RECEIPT_ROOT_COL]);
        pis.push(row[POST_RECEIPT_ROOT_COL]);
        let pre_commit = PRE_WIDE_CARRIER_BASE + ENDPOINT_COMMIT_CARRIER * CHIP_OUT_LANES;
        pis.extend_from_slice(&row[pre_commit..pre_commit + CHIP_OUT_LANES]);
        let post_commit = POST_WIDE_CARRIER_BASE + ENDPOINT_COMMIT_CARRIER * CHIP_OUT_LANES;
        pis.extend_from_slice(&row[post_commit..post_commit + CHIP_OUT_LANES]);
        debug_assert_eq!(pis.len(), RING_ENDPOINT_PUBLIC_LEN);
        pis
    }

    /// One complete endpoint row.  All wide-carrier lane zeroes are computed here;
    /// the generic descriptor prover independently recomputes lanes 1..7 from the
    /// lookup tuples, making this fill a witness rather than a trusted calculation.
    fn base_row(&self) -> Vec<BabyBear> {
        use dregg_circuit::descriptor_ir2::chip_absorb_all_lanes;
        use dregg_circuit::poseidon2::hash_fact;

        let nf_diff = self.leg[0].nullifier() - self.leg[1].nullifier();
        // If the two nullifiers collide (a double-spend), no inverse exists; a zero
        // witness makes the `(nf₀−nf₁)·inv − 1` gate evaluate to −1 ≠ 0 (UNSAT), which
        // is exactly the double-spend refusal.
        let nf_diff_inv = nf_diff.inverse().unwrap_or(BabyBear::ZERO);

        let mut row = vec![BabyBear::ZERO; FINAL_TRACE_WIDTH];
        for i in 0..RING_LEGS {
            let w = &self.leg[i];
            row[leg_col(i, lc::VALUE)] = w.value;
            row[leg_col(i, lc::RANDOMNESS)] = w.randomness;
            row[leg_col(i, lc::VB_PAD0)] = BabyBear::ZERO;
            row[leg_col(i, lc::VB_PAD1)] = BabyBear::ZERO;
            row[leg_col(i, lc::VALUE_BINDING)] = w.value_binding();
            row[leg_col(i, lc::ASSET)] = w.asset_type;
            row[leg_col(i, lc::OFFER_ASSET)] = self.offer_asset[i];
            row[leg_col(i, lc::OFFER_AMOUNT)] = self.offer_amount[i];
            row[leg_col(i, lc::WANT_ASSET)] = self.want_asset[i];
            row[leg_col(i, lc::WANT_MIN)] = self.want_min[i];
            row[leg_col(i, lc::NULLIFIER)] = w.nullifier();
            row[leg_col(i, lc::MERKLE_ROOT)] = w.merkle_root();
            row[leg_col(i, lc::OUT_VAL)] = self.out_val[i];
            row[leg_col(i, lc::OUT_BLIND)] = self.out_blind[i];
        }
        row[NF_DIFF_INV] = nf_diff_inv;

        // The range-gadget witness: bit-decompose each conservation value into its
        // `VALUE_BITS` boolean columns. For an IN-RANGE value the recompose gate holds; for
        // an out-of-range / wrapped value the low-`VALUE_BITS` bits do NOT recompose to the
        // canonical field value, so the recompose gate is violated ⇒ UNSAT (the tooth).
        for (t, &col) in RANGE_TARGET_COLS.iter().enumerate() {
            let v = row[col].as_u32();
            for j in 0..VALUE_BITS {
                row[range_bit_col(t, j)] = BabyBear::new((v >> j) & 1);
            }
        }

        // The two ordinary balance-action rows.  Owner is the hidden note creator;
        // each creator sends its offered asset to the counterparty creator.
        for i in 0..RING_LEGS {
            row[action_col(i, ac::CREATOR)] = self.leg[i].owner;
            row[action_col(i, ac::RECEIVER)] = self.leg[1 - i].owner;
            row[action_col(i, ac::ASSET)] = self.offer_asset[i];
            row[action_col(i, ac::AMOUNT)] = self.offer_amount[i];
            row[action_col(i, ac::SRC_PRE)] = self.offer_amount[i];
            row[action_col(i, ac::SRC_POST)] = BabyBear::ZERO;
            row[action_col(i, ac::DST_PRE)] = BabyBear::ZERO;
            row[action_col(i, ac::DST_POST)] = self.offer_amount[i];
            row[action_col(i, ac::AUTHORIZED)] = BabyBear::ONE;
            row[action_col(i, ac::SRC_LIVE)] = BabyBear::ONE;
            row[action_col(i, ac::DST_LIVE)] = BabyBear::ONE;
            row[action_col(i, ac::ACTION_HASH)] = hash_fact(
                row[action_col(i, ac::CREATOR)],
                &[
                    row[action_col(i, ac::CREATOR)],
                    row[action_col(i, ac::RECEIVER)],
                    row[action_col(i, ac::AMOUNT)],
                ],
            );
        }
        let creator_diff = row[action_col(0, ac::CREATOR)] - row[action_col(1, ac::CREATOR)];
        row[CREATOR_DIFF_INV] = creator_diff.inverse().unwrap_or(BabyBear::ZERO);
        let asset_diff = row[action_col(0, ac::ASSET)] - row[action_col(1, ac::ASSET)];
        row[ASSET_DIFF_INV] = asset_diff.inverse().unwrap_or(BabyBear::ZERO);
        row[AMOUNT_0_INV] = row[action_col(0, ac::AMOUNT)]
            .inverse()
            .unwrap_or(BabyBear::ZERO);
        row[AMOUNT_1_INV] = row[action_col(1, ac::AMOUNT)]
            .inverse()
            .unwrap_or(BabyBear::ZERO);
        row[TURN_COUNT_COL] = BabyBear::new(RING_LEGS as u32);
        row[PRE_RECEIPT_ROOT_COL] = hash_fact(BabyBear::ZERO, &[]);
        row[MID_RECEIPT_ROOT_COL] = hash_fact(
            row[PRE_RECEIPT_ROOT_COL],
            &[row[action_col(0, ac::ACTION_HASH)]],
        );
        row[POST_RECEIPT_ROOT_COL] = hash_fact(
            row[MID_RECEIPT_ROOT_COL],
            &[row[action_col(1, ac::ACTION_HASH)]],
        );

        let common_limb_cols = [
            (0usize, action_col(0, ac::CREATOR)),
            (1, action_col(1, ac::CREATOR)),
            (2, action_col(0, ac::ASSET)),
            (3, action_col(1, ac::ASSET)),
            (8, action_col(0, ac::AUTHORIZED)),
            (9, action_col(1, ac::AUTHORIZED)),
            (10, action_col(0, ac::SRC_LIVE)),
            (11, action_col(1, ac::SRC_LIVE)),
            (12, action_col(0, ac::DST_LIVE)),
            (13, action_col(1, ac::DST_LIVE)),
            (14, TURN_COUNT_COL),
            (15, leg_col(0, lc::NULLIFIER)),
            (16, leg_col(1, lc::NULLIFIER)),
            (17, leg_col(0, lc::MERKLE_ROOT)),
            (18, leg_col(1, lc::MERKLE_ROOT)),
            (19, leg_col(0, lc::VALUE_BINDING)),
            (20, leg_col(1, lc::VALUE_BINDING)),
        ];
        for (j, c) in common_limb_cols {
            row[PRE_KERNEL_LIMBS_BASE + j] = row[c];
            row[POST_KERNEL_LIMBS_BASE + j] = row[c];
        }
        for (j, c) in [
            (4usize, action_col(0, ac::SRC_PRE)),
            (5, action_col(0, ac::DST_PRE)),
            (6, action_col(1, ac::SRC_PRE)),
            (7, action_col(1, ac::DST_PRE)),
        ] {
            row[PRE_KERNEL_LIMBS_BASE + j] = row[c];
        }
        for (j, c) in [
            (4usize, action_col(0, ac::SRC_POST)),
            (5, action_col(0, ac::DST_POST)),
            (6, action_col(1, ac::SRC_POST)),
            (7, action_col(1, ac::DST_POST)),
        ] {
            row[POST_KERNEL_LIMBS_BASE + j] = row[c];
        }
        row[PRE_KERNEL_IROOT_COL] = row[PRE_RECEIPT_ROOT_COL];
        row[POST_KERNEL_IROOT_COL] = row[POST_RECEIPT_ROOT_COL];

        fn fill_wide(
            row: &mut [BabyBear],
            limb_base: usize,
            iroot_col: usize,
            carrier_base: usize,
        ) {
            let mut digest = chip_absorb_all_lanes(4, &row[limb_base..limb_base + 4]);
            row[carrier_base..carrier_base + 8].copy_from_slice(&digest);
            let mut carrier = 1usize;
            let mut limb = 4usize;
            while limb < ENDPOINT_NUM_PRE_LIMBS {
                let remaining = ENDPOINT_NUM_PRE_LIMBS - limb;
                let take = if remaining >= 3 { 3 } else { 1 };
                let mut inputs = [BabyBear::ZERO; 11];
                inputs[..8].copy_from_slice(&digest);
                inputs[8..8 + take]
                    .copy_from_slice(&row[limb_base + limb..limb_base + limb + take]);
                digest = chip_absorb_all_lanes(8 + take, &inputs);
                let out = carrier_base + carrier * 8;
                row[out..out + 8].copy_from_slice(&digest);
                carrier += 1;
                limb += take;
            }
            let mut inputs = [BabyBear::ZERO; 11];
            inputs[..8].copy_from_slice(&digest);
            inputs[8] = row[iroot_col];
            digest = chip_absorb_all_lanes(11, &inputs);
            let out = carrier_base + carrier * 8;
            row[out..out + 8].copy_from_slice(&digest);
            debug_assert_eq!(carrier, ENDPOINT_COMMIT_CARRIER);
        }
        fill_wide(
            &mut row,
            PRE_KERNEL_LIMBS_BASE,
            PRE_KERNEL_IROOT_COL,
            PRE_WIDE_CARRIER_BASE,
        );
        fill_wide(
            &mut row,
            POST_KERNEL_LIMBS_BASE,
            POST_KERNEL_IROOT_COL,
            POST_WIDE_CARRIER_BASE,
        );

        row
    }

    /// The main trace: every row carries the same endpoint witness.  First/last PI
    /// pins select the pre/post wide commitments and the AIR gates all semantic data.
    fn base_trace(&self) -> Vec<Vec<BabyBear>> {
        let row = self.base_row();

        vec![row; TRACE_HEIGHT]
    }
}

/// The shared inner IR-v2 prove for the ring-clearing descriptor over a witness.
fn prove_ring_clear_inner(
    ring: &ShieldedRing2,
    config: &DreggRecursionConfig,
) -> Result<
    (
        EffectVmDescriptor2,
        dregg_circuit::descriptor_ir2::Ir2BatchProof<DreggRecursionConfig>,
    ),
    String,
> {
    let desc = shielded_ring_clear_descriptor();
    let pis = ring.public_inputs();
    let base_trace = ring.base_trace();
    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc,
        &base_trace,
        &pis,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .map_err(|e| format!("ring-clear inner IR-v2 prove failed: {e}"))?;
    Ok((desc, inner))
}

/// **The 2-leg ring-clearing LEAF.** Prove the ring-clearing descriptor AIR over the
/// ring witness and RE-EXPOSE its 6-lane cleared-ring claim
/// `[nf₀,root₀,vb₀,nf₁,root₁,vb₁]` as an in-circuit `expose_claim`, so the apex can
/// bind each leg's 3-slot claim to its shielded-spend leaf. A ring that violates
/// fusion / the cycle edges / the tight-amount match / distinct nullifiers /
/// conservation has no satisfying assembly — no foldable leaf is minted.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_shielded_ring_clear_leaf(
    ring: &ShieldedRing2,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let (desc, inner) = prove_ring_clear_inner(ring, config)?;
    let pis = ring.public_inputs();
    prove_descriptor_leaf_with_pi_slice_expose(
        &desc,
        &inner,
        &pis,
        config,
        0,
        RING_ENDPOINT_PUBLIC_LEN,
    )
    .map_err(|e| format!("ring-clear claim leaf expose-wrap failed: {e}"))
}

/// Read the exposed cleared-ring claim off a leaf/apex minted with the 6-lane expose.
pub fn read_exposed_ring_claim(
    output: &RecursionOutput<DreggRecursionConfig>,
) -> Option<[BabyBear; RING_CLAIM_LEN]> {
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
    if claims.len() < RING_CLAIM_LEN {
        return None;
    }
    Some(core::array::from_fn(|i| claims[i]))
}

/// A single binding aggregation node: fold `left` (carrying a ≥6-lane exposed ring
/// claim) with a shielded-spend `sub` leaf, `connect`ing `left`'s leg-`leg_idx` 3-slot
/// window (`[leg_idx*3 .. leg_idx*3+3)`) to the sub-proof's genuine
/// `[nullifier, merkle_root, value_binding]`, and RE-EXPOSING the full 6-lane ring
/// claim so the next node can bind the other leg. A leg whose claimed tuple no
/// verifying shielded-spend backs is a `connect` conflict ⇒ UNSAT ⇒ no root.
fn bind_leg_node(
    left: &RecursionOutput<DreggRecursionConfig>,
    sub: &RecursionOutput<DreggRecursionConfig>,
    leg_idx: usize,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::ivc_turn_chain::expose_claim_instance_index;
    use crate::plonky3_recursion_impl::recursive::create_recursion_backend;
    use p3_circuit::CircuitBuilder;
    use p3_recursion::{BatchOnly, Target, build_and_prove_aggregation_layer_with_expose};

    type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

    let left_idx = expose_claim_instance_index(&left.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "ring-clear left leaf carries no expose_claim table — it must re-expose the \
                     6-lane cleared-ring claim"
                .to_string(),
        }
    })?;
    let sub_idx = expose_claim_instance_index(&sub.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "shielded-spend sub-proof leaf carries no expose_claim table — it must be \
                     minted via prove_shielded_spend_leaf_with_claim"
                .to_string(),
        }
    })?;

    let left_in = left.into_recursion_input::<BatchOnly>();
    let right_in = sub.into_recursion_input::<BatchOnly>();
    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();
    let base = leg_idx * RING_LEG_CLAIM_LEN;

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>],
                       _left_vk_cap: &[Target],
                       _right_vk_cap: &[Target]| {
        let lg = left_apt
            .get(left_idx)
            .expect("ring-clear left leaf's re-exposed claim instance present");
        let cs = right_apt
            .get(sub_idx)
            .expect("shielded-spend sub-proof's exposed tuple instance present");
        debug_assert!(lg.len() >= RING_ENDPOINT_PUBLIC_LEN && cs.len() >= RING_LEG_CLAIM_LEN);
        // THE BINDING TOOTH, IN-CIRCUIT: leg `leg_idx`'s claimed 3-slot tuple must
        // equal the shielded-spend leaf's GENUINE bound tuple, lane by lane.
        for k in 0..RING_LEG_CLAIM_LEN {
            cb.connect(lg[base + k], cs[k]);
        }
        // Re-expose the complete endpoint claim (carried forward for the second
        // spend bind and for the light-client apex output).
        let bound: Vec<Target> = (0..RING_ENDPOINT_PUBLIC_LEN).map(|k| lg[k]).collect();
        cb.expose_as_public_output(&bound);
    };

    build_and_prove_aggregation_layer_with_expose::<DreggRecursionConfig, BatchOnly, BatchOnly, _, D>(
        &left_in,
        &right_in,
        config,
        &backend,
        &params,
        None,
        Some(&expose),
    )
    .map_err(|e| JointAggError::AggregationProofInvalid {
        reason: format!("ring-clear leg-{leg_idx} binding node failed: {e:?}"),
    })
}

/// **THE 2-LEG SHIELDED RING-CLEARING NOTE APEX.** Fold the ring-clearing leaf
/// ([`prove_shielded_ring_clear_leaf`]) with the two shielded-spend leaves
/// ([`crate::shielded_spend_leaf_adapter::prove_shielded_spend_leaf_with_claim`]),
/// binding each leg's exposed 3-slot claim to its spend leaf in-circuit. The apex
/// verifies the conserving fused 2-cycle over the hidden commitments (the ring/fusion/
/// conservation constraints ride the ring-clearing leaf; the membership + fresh
/// nullifier ride each spend leaf; the `connect`s weld them), and RE-EXPOSES the
/// complete 27-lane endpoint claim. The first six lanes are bound to the two verified
/// spend leaves; the remaining lanes retain the ring leaf's constrained action,
/// receipt and wide-kernel endpoints.
///
/// A leg claiming a `[nullifier, merkle_root, value_binding]` that no verifying
/// shielded spend backs (a non-member note, a re-used nullifier, a value-binding
/// decoupled from the note value) is a `connect` conflict ⇒ UNSAT ⇒ no apex root.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_shielded_ring_clearing_apex(
    ring_leaf: &RecursionOutput<DreggRecursionConfig>,
    spend_leaf_0: &RecursionOutput<DreggRecursionConfig>,
    spend_leaf_1: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    // node1: bind leg 0 to spend leaf 0 (re-expose the 6-lane claim).
    let node1 = bind_leg_node(ring_leaf, spend_leaf_0, 0, config)?;
    // node2: bind leg 1 to spend leaf 1 (re-expose the cleared ring's committed claim).
    bind_leg_node(&node1, spend_leaf_1, 1, config)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ivc_turn_chain::ir2_leaf_wrap_config;
    use crate::shielded_spend_leaf_adapter::{
        prove_shielded_spend_leaf, prove_shielded_spend_leaf_with_claim,
        shielded_spend_leaf_public_inputs,
    };
    use dregg_circuit::refusal::must_refuse_or_unsat_panic;

    /// The descriptor lowers to the expected shape: note binding, two receipt-chain
    /// hashes, two 60-step wide commitment chains, and all 27 endpoint PI pins.
    #[test]
    fn ring_clear_descriptor_lowers() {
        let desc = shielded_ring_clear_descriptor();
        assert_eq!(desc.public_input_count, RING_ENDPOINT_PUBLIC_LEN);
        let sites = desc
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
            .count();
        assert_eq!(
            sites,
            2 + RECEIPT_SITE_COUNT + 2 * ENDPOINT_WIDE_CARRIERS,
            "two note hashes + four receipt hashes + two 60-step wide commits"
        );
        let pins = desc
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
            .count();
        assert_eq!(
            pins, RING_ENDPOINT_PUBLIC_LEN,
            "the complete endpoint surface"
        );
        assert_eq!(desc.trace_width, FINAL_TRACE_WIDTH);
        // The range gadget adds, per target, VALUE_BITS boolean gates + 1 recompose gate.
        let gates = desc
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::Gate(_))))
            .count();
        assert!(
            gates >= RANGE_TARGET_COLS.len() * (VALUE_BITS + 1),
            "each range target contributes VALUE_BITS boolean gates + 1 recompose gate"
        );
    }

    /// The honest demo ring IS a fused, tight, value-neutral 2-cycle (the plaintext
    /// invariants the AIR enforces, checked outside the circuit as a sanity floor).
    #[test]
    fn honest_demo_ring_is_fused_tight_conserving() {
        let r = ShieldedRing2::honest_demo();
        for i in 0..RING_LEGS {
            assert_eq!(r.offer_asset[i], r.leg[i].asset_type, "fused asset");
            assert_eq!(r.offer_amount[i], r.leg[i].value, "fused amount");
            assert_eq!(r.offer_asset[i], r.want_asset[1 - i], "ring edge");
            assert_eq!(r.offer_amount[i], r.want_min[1 - i], "tight amount");
        }
        assert_ne!(
            r.leg[0].nullifier(),
            r.leg[1].nullifier(),
            "distinct spends"
        );
        assert_eq!(
            r.leg[0].value + r.leg[1].value,
            r.out_val[0] + r.out_val[1],
            "Σ value conserved"
        );
        assert_eq!(
            r.leg[0].randomness + r.leg[1].randomness,
            r.out_blind[0] + r.out_blind[1],
            "Σ blinding conserved"
        );
    }

    /// THE POSITIVE POLE — a genuine shielded 2-ring FOLDS + verifies. The ring-clearing
    /// leaf proves (fusion + cycle + conservation), the two shielded-spend leaves prove
    /// (membership + fresh nullifier), and the apex binds them, re-exposing the cleared
    /// ring's committed claim.
    #[test]
    fn honest_shielded_2ring_folds_and_verifies() {
        let config = ir2_leaf_wrap_config();
        let r = ShieldedRing2::honest_demo();

        let ring_leaf = prove_shielded_ring_clear_leaf(&r, &config)
            .expect("the honest fused conserving 2-ring must prove as a foldable leaf");

        let pis0 = shielded_spend_leaf_public_inputs(&r.leg[0]);
        let pis1 = shielded_spend_leaf_public_inputs(&r.leg[1]);
        let spend0 = prove_shielded_spend_leaf_with_claim(&r.leg[0], &pis0, &config)
            .expect("honest shielded-spend leaf 0");
        let spend1 = prove_shielded_spend_leaf_with_claim(&r.leg[1], &pis1, &config)
            .expect("honest shielded-spend leaf 1");

        let apex = prove_shielded_ring_clearing_apex(&ring_leaf, &spend0, &spend1, &config)
            .expect("the honest ring must fold into a bound apex root");
        let cleared = read_exposed_ring_claim(&apex).expect("apex re-exposes the 6-lane claim");
        assert_eq!(
            cleared.as_slice(),
            &r.public_inputs()[..RING_CLAIM_LEN],
            "the cleared ring's committed claim is the two legs' genuine tuples"
        );
    }

    /// THE ENDPOINT TOOTH: the honest witness computes the post eight-lane commitment
    /// in-circuit.  Flipping one published lane while leaving the witness untouched is
    /// UNSAT at the PI binding; endpoint lanes are constraints, not metadata carriers.
    ///
    /// WHICH REFUSAL MECHANISM, AND WHY IT IS NOT `must_refuse`: a `PiBinding` is an AIR
    /// constraint of the Main instance (`lean_descriptor_air.rs`'s `when_last_row` block), so
    /// a forged PI is caught by p3's debug-gated `check_constraints`, which PANICS inside
    /// `prove_batch` — BEFORE `prove_vm_descriptor2_inner`'s `check && debug_assertions`
    /// self-verify could return `Err`. `prove_vm_descriptor2_for_config` passes `check: true`,
    /// but that pre-flight replay covers only the mem/map/umem/exact-public/submask witnesses,
    /// NOT the algebraic gates or the PI pins.  So for a gate/PI forgery on this entry point the
    /// documented unsat panic IS the mechanism, and the `Err` arm `must_refuse` demands is
    /// unreachable.  The reason assertion below keeps this a discriminating tooth: acceptance,
    /// any non-unsat panic, and a shape/arity `Err` all still RED.
    #[test]
    fn forged_post_endpoint_lane_is_unsat() {
        let config = ir2_leaf_wrap_config();
        let r = ShieldedRing2::honest_demo();
        let desc = shielded_ring_clear_descriptor();
        let trace = r.base_trace();
        let mut pis = r.public_inputs();
        pis[endpoint_pi::POST_COMMIT_8 + 7] += BabyBear::ONE;
        dregg_circuit::refusal::assert_committed_shape(
            "a forged ring post-commitment lane",
            &desc,
            &trace,
            &pis,
        );

        let refusal = must_refuse_or_unsat_panic("a forged ring post-commitment lane", || {
            prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
                &desc,
                &trace,
                &pis,
                &MemBoundaryWitness::default(),
                &[],
                &UMemBoundaryWitness::default(),
                &config,
            )
        });
        dregg_circuit::refusal::assert_violated_constraint_not_bus(
            "a forged ring post-commitment lane must be refused by a VIOLATED CONSTRAINT (the \
             last-row PI pin), not by a bus imbalance or any other path",
            &refusal.reason(),
        );
    }

    /// The receipt chain is part of the post commitment.  Forging the published
    /// post-receipt root fails its direct pin even before the wide-commit pin is read.
    /// Same refusal mechanism as [`forged_post_endpoint_lane_is_unsat`] — see its note.
    #[test]
    fn forged_receipt_log_endpoint_is_unsat() {
        let config = ir2_leaf_wrap_config();
        let r = ShieldedRing2::honest_demo();
        let desc = shielded_ring_clear_descriptor();
        let trace = r.base_trace();
        let mut pis = r.public_inputs();
        pis[endpoint_pi::POST_RECEIPT_ROOT] += BabyBear::ONE;
        dregg_circuit::refusal::assert_committed_shape(
            "a forged two-action receipt root",
            &desc,
            &trace,
            &pis,
        );

        let refusal = must_refuse_or_unsat_panic("a forged two-action receipt root", || {
            prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
                &desc,
                &trace,
                &pis,
                &MemBoundaryWitness::default(),
                &[],
                &UMemBoundaryWitness::default(),
                &config,
            )
        });
        dregg_circuit::refusal::assert_violated_constraint_not_bus(
            "a forged two-action receipt root must be refused by a VIOLATED CONSTRAINT (its \
             first-row PI pin), not by a bus imbalance or any other path",
            &refusal.reason(),
        );
    }

    /// THE NEGATIVE POLE (conservation): a NON-conserving ring (a value-minting output)
    /// has a non-zero Pedersen excess — the `Σ value_in == Σ value_out` gate refuses it,
    /// no ring-clearing leaf is minted. Genuine circuit non-satisfiability.
    #[test]
    fn nonconserving_ring_is_unsat() {
        let config = ir2_leaf_wrap_config();
        let mut r = ShieldedRing2::honest_demo();
        // Mint value: an output worth one more than the inputs cover.
        r.out_val[0] = r.out_val[0] + BabyBear::ONE;

        must_refuse_or_unsat_panic("a value-minting ring", || {
            prove_shielded_ring_clear_leaf(&r, &config)
        });
    }

    /// THE NEGATIVE POLE (WRAPAROUND MINT — the range gadget's reason to exist): a ring that
    /// balances the FIELD conservation gate `Σ value_in ≡ Σ value_out (mod p)` by WRAPAROUND —
    /// one output committed to a large value, its counterpart to a "wrapped negative"
    /// (`p − k`), keeping the field sum fixed — MINTS real value. The pre-range AIR accepted
    /// this (the field equation holds); the range gadget makes it UNSAT: neither `out_val₀ +
    /// 2^VALUE_BITS` nor `out_val₁ − 2^VALUE_BITS = p − …` has a `VALUE_BITS`-bit preimage, so
    /// the recompose gate is violated. This is the field-soundness weld: no wraparound mint.
    #[test]
    fn wraparound_mint_ring_is_unsat() {
        let config = ir2_leaf_wrap_config();
        let mut r = ShieldedRing2::honest_demo();
        // Shift value between the two outputs by 2^VALUE_BITS: the FIELD sum
        // (out_val₀ + out_val₁) is UNCHANGED (the conservation gate still holds), but
        // out_val₀ jumps out of [0, 2^VALUE_BITS) and out_val₁ wraps to p − (…), a minted
        // "negative". Only the range gadget can refuse it.
        let wrap = BabyBear::new(1u32 << VALUE_BITS);
        r.out_val[0] = r.out_val[0] + wrap;
        r.out_val[1] = r.out_val[1] - wrap;
        // Sanity: the field conservation gate is STILL satisfied (Σ unchanged) —
        // so the ONLY thing that can reject this is the in-AIR range gadget.
        assert_eq!(
            r.leg[0].value + r.leg[1].value,
            r.out_val[0] + r.out_val[1],
            "the wraparound mint keeps the FIELD conservation equation satisfied"
        );

        must_refuse_or_unsat_panic(
            "a wraparound-minting ring (field-conserving, range-violating) minted a  foldable leaf",
            || prove_shielded_ring_clear_leaf(&r, &config),
        );
    }

    /// THE NEGATIVE POLE (out-of-range output): an output value ≥ 2^VALUE_BITS (even without
    /// touching the conservation equation) has no `VALUE_BITS`-bit preimage and is UNSAT at the
    /// recompose gate — the input side is left conserving so ONLY the range gate bites. (Here
    /// the conservation gate ALSO breaks, but the point is the recompose gate independently
    /// refuses any out-of-range committed value.)
    #[test]
    fn out_of_range_output_is_unsat() {
        let config = ir2_leaf_wrap_config();
        let mut r = ShieldedRing2::honest_demo();
        r.out_val[0] = BabyBear::new(1u32 << VALUE_BITS); // exactly 2^VALUE_BITS: out of range

        must_refuse_or_unsat_panic("an out-of-range output value", || {
            prove_shielded_ring_clear_leaf(&r, &config)
        });
    }

    /// THE NEGATIVE POLE (double-spend): a ring whose two legs re-use ONE note (the same
    /// nullifier) fails the `nullifier[0] != nullifier[1]` gate (no inverse witness) —
    /// UNSAT, no ring-clearing leaf. The circuit twin of `shielded_leg_no_double_spend`.
    #[test]
    fn double_spend_ring_is_unsat() {
        let config = ir2_leaf_wrap_config();
        let mut r = ShieldedRing2::honest_demo();
        // Both legs spend leg 0's note ⇒ identical nullifiers.
        r.leg[1] = r.leg[0].clone();

        must_refuse_or_unsat_panic("a double-spend ring", || {
            prove_shielded_ring_clear_leaf(&r, &config)
        });
    }

    /// THE NEGATIVE POLE (mis-fusion): a leg whose matcher offer amount does NOT equal
    /// its note value fails the `offer_amount == value` fusion gate — UNSAT. The circuit
    /// twin of the Lean `legA_not_fused`.
    #[test]
    fn misfused_leg_is_unsat() {
        let config = ir2_leaf_wrap_config();
        let mut r = ShieldedRing2::honest_demo();
        // Decouple leg 0's cleared offer from its note value (the matcher clears a
        // MatchNode beside the note, not the note) — but keep the cycle self-consistent
        // so ONLY the fusion gate bites.
        r.offer_amount[0] = r.offer_amount[0] + BabyBear::ONE;
        r.want_min[1] = r.want_min[1] + BabyBear::ONE; // keep the tight edge intact

        must_refuse_or_unsat_panic("a mis-fused leg", || {
            prove_shielded_ring_clear_leaf(&r, &config)
        });
    }

    /// THE BINDING TOOTH (apex): a ring-clearing leaf whose leg claims a tuple that a
    /// DIFFERENT spend leaf does not back cannot bind — the apex `connect` conflicts ⇒
    /// UNSAT ⇒ no apex root. (The ring leaf is honest; the spend leaf fed for leg 1 is
    /// of a different note.)
    #[test]
    fn mismatched_fold_does_not_bind() {
        let config = ir2_leaf_wrap_config();
        let r = ShieldedRing2::honest_demo();
        let ring_leaf = prove_shielded_ring_clear_leaf(&r, &config).expect("honest ring leaf");

        let pis0 = shielded_spend_leaf_public_inputs(&r.leg[0]);
        let spend0 = prove_shielded_spend_leaf_with_claim(&r.leg[0], &pis0, &config)
            .expect("honest spend leaf 0");

        // A spend leaf of a DIFFERENT note (not leg 1's) — its tuple cannot connect to
        // leg 1's claimed tuple.
        let other = demo_leg_witness(0x77, 1, 4);
        assert_ne!(other.nullifier(), r.leg[1].nullifier(), "distinct spends");
        let pis_other = shielded_spend_leaf_public_inputs(&other);
        let spend_other = prove_shielded_spend_leaf_with_claim(&other, &pis_other, &config)
            .expect("the mismatched leaf is itself an honest spend of a DIFFERENT note");

        must_refuse_or_unsat_panic("a leg bound to a non-backing spend", || {
            prove_shielded_ring_clearing_apex(&ring_leaf, &spend0, &spend_other, &config)
        });
    }

    /// Sanity: the membership tooth still bites AT THE LEAF (a forged spend never even
    /// becomes a foldable leaf to bind) — reusing the shielded-spend leaf's own tooth so
    /// the ring apex inherits clause (a)'s soundness.
    #[test]
    fn forged_spend_leg_never_mints_a_leaf() {
        let config = ir2_leaf_wrap_config();
        let w = demo_leg_witness(0x31, 0, 3);
        let mut pis = shielded_spend_leaf_public_inputs(&w);
        pis[1] = pis[1] + BabyBear::ONE; // forge the merkle_root

        must_refuse_or_unsat_panic("a forged-membership spend minted a leaf", || {
            prove_shielded_spend_leaf(&w, &pis, &config)
        });
    }
}
