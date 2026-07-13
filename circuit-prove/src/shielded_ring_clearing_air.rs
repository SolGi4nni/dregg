//! The 2-leg shielded RING-CLEARING AIR — the circuit realization of DrEX rung-3
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
//!         the AIR RE-COMPUTES `value_binding[i] = hash_fact(value[i],[randomness[i],
//!         0,0])` (the SAME Poseidon2 fact-sponge the shielded-spend circuit's C7a
//!         publishes) and the apex `connect`s it to the leaf's exposed value_binding,
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
//!     is UNSAT — the circuit twin of `RealCrypto.pedCommit_mint_refused`. No amount is
//!     revealed: the values live only in the witness (hidden under the hiding PCS); the
//!     apex exposes only the cleared ring's committed claim `[nf₀,root₀,vb₀,nf₁,root₁,
//!     vb₁]`.
//!
//! ## HONEST GRADE — 2-leg BUILT; what is in-AIR vs the leaf's exposed claim
//!
//!   * The Pedersen conservation (c) is enforced IN-AIR at the aggregate level (Σ value
//!     + Σ blinding), matching `ring_conserves_pedersen_list` (the 2-generator
//!     `pedTwoGen`, NOT the multi-generator asset commitment); the per-ASSET routing
//!     is carried by the ring edges (b), exactly the two-weld split of the Lean.
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

/// The pre-chip-lane base width.
const BASE_WIDTH: usize = NF_DIFF_INV + 1;

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

/// Build the 2-leg ring-clearing descriptor AIR (`shielded-ring-clear-2`). Its 6 PIs
/// are `[nf₀, root₀, vb₀, nf₁, root₁, vb₁]` (nullifier + merkle_root pass through to
/// the apex `connect`; value_binding is RE-COMPUTED in-AIR by the fact chip so the
/// fused `value[i]` is bound to the note the spend leaf published).
pub fn shielded_ring_clear_descriptor() -> EffectVmDescriptor2 {
    let mut constraints: Vec<VmConstraint2> = Vec::new();
    let mut width = BASE_WIDTH;
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
    // blinding coordinate: (rand₀ + rand₁) − (out_blind₀ + out_blind₁) == 0
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

    // --- the value-binding pad cells are constant-zero (so the fact absorbs
    // [randomness, 0, 0]). ---
    for i in 0..RING_LEGS {
        constraints.push(gate(LeanExpr::Var(leg_col(i, lc::VB_PAD0))));
        constraints.push(gate(LeanExpr::Var(leg_col(i, lc::VB_PAD1))));
    }

    // --- the value-binding RECOMPUTE (per leg): value_binding[i] ==
    // hash_fact(value[i], [randomness[i], 0, 0]). The fusion anchor. ---
    for i in 0..RING_LEGS {
        let site = fact_site_always(
            leg_col(i, lc::VALUE_BINDING),
            &[
                leg_col(i, lc::VALUE),
                leg_col(i, lc::RANDOMNESS),
                leg_col(i, lc::VB_PAD0),
                leg_col(i, lc::VB_PAD1),
            ],
            alloc_lanes(),
        );
        constraints.push(site);
    }

    // --- the exposed 6-lane claim, pinned to the PIs (First row). ---
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

    EffectVmDescriptor2 {
        name: "shielded-ring-clear-2".into(),
        trace_width: width,
        public_input_count: RING_CLAIM_LEN,
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

    /// The full 6-lane public-input tuple `[nf₀,root₀,vb₀,nf₁,root₁,vb₁]`.
    pub fn public_inputs(&self) -> Vec<BabyBear> {
        let mut pis = Vec::with_capacity(RING_CLAIM_LEN);
        for i in 0..RING_LEGS {
            pis.extend_from_slice(&self.leg_claim(i));
        }
        pis
    }

    /// The base main trace (`TRACE_HEIGHT × BASE_WIDTH`): every row carries the same
    /// constant ring data; the chip lane columns are appended + filled by the
    /// descriptor-driven prover weld.
    fn base_trace(&self) -> Vec<Vec<BabyBear>> {
        let nf_diff = self.leg[0].nullifier() - self.leg[1].nullifier();
        // If the two nullifiers collide (a double-spend), no inverse exists; a zero
        // witness makes the `(nf₀−nf₁)·inv − 1` gate evaluate to −1 ≠ 0 (UNSAT), which
        // is exactly the double-spend refusal.
        let nf_diff_inv = nf_diff.inverse().unwrap_or(BabyBear::ZERO);

        let mut row = vec![BabyBear::ZERO; BASE_WIDTH];
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
    prove_descriptor_leaf_with_pi_slice_expose(&desc, &inner, &pis, config, 0, RING_CLAIM_LEN)
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
                       right_apt: &[Vec<Target>]| {
        let lg = left_apt
            .get(left_idx)
            .expect("ring-clear left leaf's re-exposed claim instance present");
        let cs = right_apt
            .get(sub_idx)
            .expect("shielded-spend sub-proof's exposed tuple instance present");
        debug_assert!(lg.len() >= RING_CLAIM_LEN && cs.len() >= RING_LEG_CLAIM_LEN);
        // THE BINDING TOOTH, IN-CIRCUIT: leg `leg_idx`'s claimed 3-slot tuple must
        // equal the shielded-spend leaf's GENUINE bound tuple, lane by lane.
        for k in 0..RING_LEG_CLAIM_LEN {
            cb.connect(lg[base + k], cs[k]);
        }
        // Re-expose the full 6-lane cleared-ring claim (carried forward for the
        // second bind + the apex output).
        let bound: Vec<Target> = (0..RING_CLAIM_LEN).map(|k| lg[k]).collect();
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

/// **THE 2-LEG SHIELDED RING-CLEARING APEX.** Fold the ring-clearing leaf
/// ([`prove_shielded_ring_clear_leaf`]) with the two shielded-spend leaves
/// ([`crate::shielded_spend_leaf_adapter::prove_shielded_spend_leaf_with_claim`]),
/// binding each leg's exposed 3-slot claim to its spend leaf in-circuit. The apex
/// verifies the conserving fused 2-cycle over the hidden commitments (the ring/fusion/
/// conservation constraints ride the ring-clearing leaf; the membership + fresh
/// nullifier ride each spend leaf; the `connect`s weld them), and RE-EXPOSES the
/// cleared ring's committed claim `[nf₀,root₀,vb₀,nf₁,root₁,vb₁]`.
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

    /// The descriptor lowers to the expected shape: 2 fact sites (the two value-binding
    /// recomputes), 6 PiBindings (2 legs × 3), and the fusion/ring/conservation gates.
    #[test]
    fn ring_clear_descriptor_lowers() {
        let desc = shielded_ring_clear_descriptor();
        assert_eq!(desc.public_input_count, RING_CLAIM_LEN);
        let sites = desc
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
            .count();
        assert_eq!(sites, 2, "one value-binding recompute per leg");
        let pins = desc
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
            .count();
        assert_eq!(pins, RING_CLAIM_LEN, "nf/root/vb per leg");
        assert_eq!(desc.trace_width, BASE_WIDTH + 2 * (CHIP_OUT_LANES - 1));
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
            r.public_inputs().as_slice(),
            "the cleared ring's committed claim is the two legs' genuine tuples"
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

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_shielded_ring_clear_leaf(&r, &config)
        }));
        match result {
            Err(_) => {}
            Ok(Err(_)) => {}
            Ok(Ok(_)) => panic!("a value-minting ring minted a foldable leaf — conservation OPEN"),
        }
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

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_shielded_ring_clear_leaf(&r, &config)
        }));
        match result {
            Err(_) => {}
            Ok(Err(_)) => {}
            Ok(Ok(_)) => panic!("a double-spend ring minted a foldable leaf — nullifier OPEN"),
        }
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

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_shielded_ring_clear_leaf(&r, &config)
        }));
        match result {
            Err(_) => {}
            Ok(Err(_)) => {}
            Ok(Ok(_)) => panic!("a mis-fused leg minted a foldable leaf — fusion OPEN"),
        }
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

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_shielded_ring_clearing_apex(&ring_leaf, &spend0, &spend_other, &config)
        }));
        match result {
            Err(_) => {}
            Ok(Err(_)) => {}
            Ok(Ok(_)) => panic!("a leg bound to a non-backing spend — apex binding OPEN"),
        }
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

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_shielded_spend_leaf(&w, &pis, &config)
        }));
        match result {
            Err(_) => {}
            Ok(Err(_)) => {}
            Ok(Ok(_)) => panic!("a forged-membership spend minted a leaf — clause (a) OPEN"),
        }
    }
}
