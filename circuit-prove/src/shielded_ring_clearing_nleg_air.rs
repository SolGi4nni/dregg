//! The **N-leg** shielded RING-CLEARING AIR — the variable-length-cycle generalization
//! of the 2-leg tight-cycle apex ([`crate::shielded_ring_clearing_air`]), plus the
//! **partial-fill inequality** (`offer_amount ≥ want_min`) enforced IN-AIR by the same
//! bit-decomposition range bedrock the 2-leg file uses for the no-wrap conservation gate.
//!
//! This is **component 1** of `docs/deos/SHIELDED-DREX-ASSURANCE-ROADMAP.md` (the N-leg
//! variable cycle + partial-fill `offer ≥ want_min` in-AIR), and the enabler for the
//! reveal-nothing ZK theorem (component 3): it FIXES the transcript shape `[nf, root, vb]ⁿ`
//! that the ZK theorem must quantify over. NO NEW CRYPTO — it reuses the proven range
//! bedrock (`Dregg2.Bignum.legs_noWrap_conservation` / `le_iff`, the bit-decomposition +
//! borrow-sub compare) and the same Poseidon2 value-binding fusion the 2-leg apex uses.
//!
//! ## What this converts (PROVED-SPEC → BUILT at N-leg)
//!
//! `Market/ShieldedClearing.lean::shielded_ring_clears` and
//! `Market/LedgerRealizationExt.lean::shielded_ring_fused_clears` are **already N-general**
//! — they quantify over a `List (ShieldedLeg ...)` of arbitrary length, with `CycleValid`
//! the variable-length chain and `clearing_respects_limits` giving `wantMin ≤ receivedAmount`
//! (the partial-fill inequality, NOT a tightness). This module is the silicon at that
//! generality: a foldable AIR that verifies an N-cycle conserving fused ring over N
//! shielded-spend leaves, admitting partial fills.
//!
//! ## The clauses, and where each is enforced (honest map — same split as the 2-leg)
//!
//!   * **(a) each leg is a valid shielded spend** — membership + FRESH nullifier — is the
//!     BUILT [`crate::shielded_spend_leaf_adapter::prove_shielded_spend_leaf_with_claim`]
//!     leaf, exposing `[nullifier, merkle_root, value_binding]`. The apex FOLDS the N leaves
//!     and BINDS each ring leg's per-leg claim to its leaf by an in-circuit `connect` (a
//!     forged/mismatched leg is a `connect` conflict ⇒ UNSAT ⇒ no apex root).
//!
//!   * **(b) the RING structure + FUSION**, in-AIR over the N legs' plaintext witness:
//!       - FUSION (`LegFused`): `offer_asset[i] == asset[i]`, `offer_amount[i] == value[i]`,
//!         with `value[i]` (and `asset[i]`) bound to the spent note through the
//!         RE-COMPUTED `value_binding[i] = hash_fact(value[i], [asset[i], randomness[i],
//!         0])` (the SAME Poseidon2 fact-sponge the shielded-spend circuit's C7a
//!         publishes — the PQ HashCR value-commitment binding (value, asset) jointly),
//!         `connect`ed to the leaf's exposed value_binding under Poseidon2 CR.
//!       - RING (`CycleValid` N-cycle edges): `want_asset[i] == offer_asset[(i+1) mod N]`
//!         (leg `i` wants what the next leg offers, the variable-length chain closed mod N).
//!       - **PARTIAL FILL** (`clearing_respects_limits`): `want_min[i] ≤ offer_amount[(i+1)
//!         mod N]` (leg `i` receives the next leg's offer, ≥ its declared minimum). This is
//!         the general clearing — the 2-leg file enforced the TIGHT `offer_amount ==
//!         want_min`; here it is the INEQUALITY, realized in-AIR by the borrow-sub range
//!         compare (see (d)): a witnessed `VALUE_BITS`-bit difference `offer − want_min`
//!         exists IFF `offer ≥ want_min` (the circuit twin of `Dregg2.Bignum.le_iff`, the
//!         `∃ borrow-sub witness ↔ X ≤ Y` keystone).
//!       - NO IN-RING DOUBLE-SPEND: `nullifier[i] != nullifier[j]` for every pair `i < j`
//!         (an inverse-witness `≠` gate per pair), the circuit twin of the Lean
//!         `∀ leg∈sr` distinct-nullifier discipline across ALL N legs.
//!
//!   * **(c) CONSERVATION over the Pedersen value commitments** — `Σ C_in − Σ C_out = 0`
//!     over the two-generator `pedTwoGen (v, r)`: `Σ value[i] == Σ out_val[i]` (value
//!     coordinate) AND `Σ randomness[i] == Σ out_blind[i]` (blinding coordinate), the exact
//!     hypothesis→conclusion of `RealCrypto.ring_conserves_pedersen_list` at N legs (its
//!     `legs_noWrap_conservation` is ALREADY k-leg). A value-minting ring has a non-zero
//!     excess ⇒ UNSAT.
//!
//!   * **(d) THE VALUE RANGE GADGET (field-soundness weld) + the partial-fill compare.**
//!     Every conservation value (`value[i]`, `out_val[i]`) AND every `want_min[i]` is
//!     BIT-DECOMPOSED into `VALUE_BITS` boolean columns recomposing to it, forcing `∈ [0,
//!     2^VALUE_BITS)`. With `N · 2^VALUE_BITS ≤ p` (asserted at descriptor-build time), both
//!     per-side conservation sums are `< p` (canonical), so the FIELD gate `Σ value ≡ Σ
//!     out_val (mod p)` IS the INTEGER conservation `Σ value = Σ out_val`
//!     (`legs_noWrap_conservation`) — a wraparound mint has no `VALUE_BITS`-bit preimage and
//!     is UNSAT. The SAME bedrock realizes the partial-fill `≥`: for each edge a
//!     `VALUE_BITS`-bit difference column recomposes to `offer_amount[(i+1) mod N] −
//!     want_min[i]`; that difference has a range preimage IFF the subtraction did not
//!     underflow, i.e. IFF `offer ≥ want_min` — an under-want ring (`offer < want_min`)
//!     wraps to `p − k`, has no preimage, and is UNSAT. This is `Dregg2.Bignum.le_iff` /
//!     `sub_underflow_unsat` at a single BabyBear limb, both operands range-bounded.
//!
//! ## HONEST GRADE — N-leg + partial-fill BUILT; what is NAMED next
//!
//!   * **BUILT here:** the N-leg variable-length conserving fused ring with partial fills,
//!     genuine both-polarity teeth (3-leg + 4-leg fold+verify; non-conserving / wraparound /
//!     double-spend / mis-fused / **under-want** / mismatched-fold all UNSAT). The transcript
//!     is `[nf, root, vb]ⁿ` — all plaintext (values, offer/want, out_val/out_blind, range
//!     bits, fill-diff bits) is WITNESS-ONLY under the hiding PCS; the apex exposes only the
//!     N per-leg committed claims. **This is the transcript the ZK theorem quantifies over.**
//!   * **NAMED next (NOT built here):**
//!       - **The reveal-nothing ZK theorem (component 3).** That the transcript `[nf,root,vb]ⁿ`
//!         + the proof is a simulable function of only the public data (roots, fresh-nullifier
//!         set, batch size N), independent of the private trades. RESEARCH; this module only
//!         FINALIZES the transcript it must quantify over.
//!       - **Full Ristretto EC excess in-AIR (component 2).** Conservation runs over the
//!         two-COORDINATE `pedTwoGen (v, r)` abstraction, not the real group point `v·G + r·H`;
//!         the actual curve-point excess in-AIR is the EC-in-circuit build. RESEARCH.
//!         (The value-mint hazard is CLOSED in-circuit by (d); this is a faithfulness upgrade.)
//!       - **64-bit range + deployed-VK fold (components 2/6).** One BabyBear field caps an
//!         N-leg conserving sum near `2^30/N`; amounts above `2^VALUE_BITS` still lean on the
//!         off-AIR Bulletproof, and the deployed-epoch VK fold is a separate rung.

use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, EffectVmDescriptor2, LookupSpec, MemBoundaryWitness,
    TID_P2, UMemBoundaryWitness, VmConstraint2, prove_vm_descriptor2_for_config,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

use p3_recursion::{ProveNextLayerParams, RecursionOutput};

use crate::ivc_turn_chain::prove_descriptor_leaf_with_pi_slice_expose;
use crate::joint_turn_aggregation::JointAggError;
use crate::plonky3_recursion_impl::recursive::DreggRecursionConfig;
use crate::shielded::spend_circuit::ShieldedSpendWitness;
use crate::shielded_spend_leaf_adapter::SHIELDED_SPEND_CLAIM_LEN;

/// Extension degree of the recursion config's PCS (the BabyBear-quartic stack).
const D: usize = 4;

/// The `hash_fact` domain-separation marker (`poseidon2::hash_fact` state[5]). File-local,
/// matching the 2-leg module + the note-spend adapter's `hash_fact` KAT.
const NS_FACT_MARK: u32 = 0xFACF;

/// Per-leg 3-slot claim `[nullifier, merkle_root, value_binding]` — the SAME tuple the
/// shielded-spend leaf exposes, so each ring leg binds to its spend leaf lane-by-lane.
pub const RING_LEG_CLAIM_LEN: usize = SHIELDED_SPEND_CLAIM_LEN; // 3

/// **The in-AIR range-gadget bit-width.** Each conservation value + each `want_min` is
/// bit-decomposed into `VALUE_BITS` boolean columns, so a witnessed value provably lies in
/// `[0, 2^VALUE_BITS)`. This is BOTH (i) the field-soundness tooth of the conservation gate
/// (`Σ value ≡ Σ out_val (mod p)` becomes INTEGER conservation once every value is range-
/// bounded and `N · 2^VALUE_BITS ≤ p`) AND (ii) the operand range the partial-fill borrow-sub
/// compare needs (`Dregg2.Bignum.le_iff` requires `Ranged` on both operands).
///
/// `27` keeps `N · 2^27 ≤ p ≈ 2^30.9` for any ring up to `N = 15`
/// (`15 · 2^27 = 2013265920 = p − 1 ≤ p`) — a comfortable margin over the demo sizes. The
/// exact per-descriptor no-wrap bound is asserted at build time against the actual `N`
/// ([`ring_no_wrap_ok`]). The full 64-bit amount range stays the off-AIR Bulletproof (named).
const VALUE_BITS: usize = 27;

/// Per-leg base column layout (leg-major). Identical field set to the 2-leg module.
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

/// The three range-checked fields per leg, in target order: `value`, `out_val`, `want_min`.
/// `value`/`out_val` carry the conservation no-wrap; `want_min` is the compare's second
/// operand (both operands `Ranged`, the `le_iff` hypotheses).
const RANGE_FIELDS: [usize; 3] = [lc::VALUE, lc::OUT_VAL, lc::WANT_MIN];

/// The column layout for an `n`-leg ring. All offsets are functions of `n` (no compile-time
/// `RING_LEGS`), so the descriptor scales to variable-length cycles.
#[derive(Clone, Copy, Debug)]
struct Layout {
    n: usize,
}

impl Layout {
    fn new(n: usize) -> Self {
        assert!(n >= 2, "a ring needs at least 2 legs");
        Layout { n }
    }

    /// The full cleared-ring claim width: all legs' 3-slot claims, in leg order.
    fn claim_len(&self) -> usize {
        self.n * RING_LEG_CLAIM_LEN
    }

    /// Column index of field `f` of leg `i` (leg-major base region).
    fn leg_col(&self, i: usize, f: usize) -> usize {
        i * lc::LEG_WIDTH + f
    }

    /// The base region width (leg columns only).
    fn base_region(&self) -> usize {
        self.n * lc::LEG_WIDTH
    }

    /// Number of unordered nullifier pairs (the `≠` inverse-witness columns).
    fn num_pairs(&self) -> usize {
        self.n * (self.n - 1) / 2
    }

    /// Linear index of the unordered pair `(i, j)` with `i < j` (row-major over the strict
    /// upper triangle).
    fn pair_index(&self, i: usize, j: usize) -> usize {
        debug_assert!(i < j && j < self.n);
        i * (self.n - 1) - i * (i.wrapping_sub(1)) / 2 + (j - i - 1)
    }

    /// The inverse-witness column for the `nullifier[i] != nullifier[j]` gate.
    fn nf_inv_col(&self, i: usize, j: usize) -> usize {
        self.base_region() + self.pair_index(i, j)
    }

    /// First column of the range bit-decomposition block.
    fn range_bit_base(&self) -> usize {
        self.base_region() + self.num_pairs()
    }

    /// Number of range targets (`value`, `out_val`, `want_min` per leg).
    fn num_range_targets(&self) -> usize {
        self.n * RANGE_FIELDS.len()
    }

    /// The base column of range target `t = leg * RANGE_FIELDS.len() + field_ix`.
    fn range_target_col(&self, t: usize) -> usize {
        let i = t / RANGE_FIELDS.len();
        let f = RANGE_FIELDS[t % RANGE_FIELDS.len()];
        self.leg_col(i, f)
    }

    /// Column of bit `b` of range target `t`.
    fn range_bit_col(&self, t: usize, b: usize) -> usize {
        self.range_bit_base() + t * VALUE_BITS + b
    }

    /// First column of the partial-fill difference block (one `VALUE_BITS`-wide diff per edge).
    fn fill_bit_base(&self) -> usize {
        self.range_bit_base() + self.num_range_targets() * VALUE_BITS
    }

    /// Column of bit `b` of the partial-fill difference for edge `i` (leg `i` receiving from
    /// leg `(i+1) mod n`): recomposes to `offer_amount[(i+1) mod n] − want_min[i]`.
    fn fill_bit_col(&self, i: usize, b: usize) -> usize {
        self.fill_bit_base() + i * VALUE_BITS + b
    }

    /// The pre-chip-lane trace width (base + nullifier inverses + range bits + fill-diff bits).
    /// The chip lanes (the per-leg value-binding recompute) grow the width from here.
    fn pre_lane_width(&self) -> usize {
        self.fill_bit_base() + self.n * VALUE_BITS
    }
}

/// The no-wrap admissibility check for an `n`-leg ring: `n · 2^VALUE_BITS ≤ p`, so neither
/// conservation sum can wrap BabyBear and the field conservation gate is exactly integer
/// conservation (`legs_noWrap_conservation`'s `#legs · 2ⁿ ≤ p` hypothesis, at the deployed
/// `VALUE_BITS`). Asserted at descriptor-build time against the actual leg count.
pub fn ring_no_wrap_ok(n: usize) -> bool {
    (n as u64) * (1u64 << VALUE_BITS) <= BABYBEAR_P as u64
}

/// `x − y` as a `LeanExpr`.
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

/// `Σ cols` as a `LeanExpr` (empty ⇒ `0`).
fn sum_cols(cols: impl IntoIterator<Item = usize>) -> LeanExpr {
    let mut it = cols.into_iter();
    match it.next() {
        None => LeanExpr::Const(0),
        Some(c0) => it.fold(LeanExpr::Var(c0), |acc, c| {
            LeanExpr::add(acc, LeanExpr::Var(c))
        }),
    }
}

/// `col − Σⱼ 2ʲ·bitⱼ` as a `LeanExpr` — the recompose body: `== 0` forces `col` to have an
/// exact `VALUE_BITS`-bit preimage (`col ∈ [0, 2^VALUE_BITS)`).
fn recompose_body(col: LeanExpr, bit_col: impl Fn(usize) -> usize) -> LeanExpr {
    let mut acc = col;
    for j in 0..VALUE_BITS {
        acc = sub(
            acc,
            LeanExpr::mul(LeanExpr::Const(1i64 << j), LeanExpr::Var(bit_col(j))),
        );
    }
    acc
}

/// A boolean gate `b·(b − 1) == 0` on column `c`.
fn bool_gate(c: usize) -> VmConstraint2 {
    let b = LeanExpr::Var(c);
    gate(LeanExpr::mul(b.clone(), sub(b, LeanExpr::Const(1))))
}

/// Build the arity-7 `TID_P2` chip lookup carrying one UNGATED `hash_fact` site (the
/// value-binding recompute) — file-local twin of the 2-leg module's `fact_site_always`.
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
    tuple.push(LeanExpr::Var(output_col));
    for j in 0..(CHIP_OUT_LANES - 1) {
        tuple.push(LeanExpr::Var(lane_base + j));
    }
    debug_assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    })
}

/// Build the **N-leg** ring-clearing descriptor AIR (`shielded-ring-clear-N`). Its `n·3` PIs
/// are `[nf, root, vb]ⁿ` (nullifier + merkle_root pass through to the apex `connect`;
/// value_binding is RE-COMPUTED in-AIR by the fact chip so the fused `value[i]` is bound to
/// the spent note). Panics if `n · 2^VALUE_BITS` would wrap BabyBear ([`ring_no_wrap_ok`]).
pub fn shielded_ring_clear_descriptor(n: usize) -> EffectVmDescriptor2 {
    let lo = Layout::new(n);
    assert!(
        ring_no_wrap_ok(n),
        "N-leg ring: N·2^VALUE_BITS ({n}·2^{VALUE_BITS}) exceeds BabyBear p — a value-sum \
         could wrap, re-opening the wraparound mint. Lower N or VALUE_BITS."
    );

    let mut constraints: Vec<VmConstraint2> = Vec::new();
    let mut width = lo.pre_lane_width();
    let mut alloc_lanes = || {
        let base = width;
        width += CHIP_OUT_LANES - 1;
        base
    };

    // --- (b.i) FUSION: the matcher's offer IS the note (per leg). ---
    for i in 0..n {
        constraints.push(eq_gate(
            lo.leg_col(i, lc::OFFER_ASSET),
            lo.leg_col(i, lc::ASSET),
        ));
        constraints.push(eq_gate(
            lo.leg_col(i, lc::OFFER_AMOUNT),
            lo.leg_col(i, lc::VALUE),
        ));
    }

    // --- (b.ii) RING (CycleValid N-cycle asset edges): want_asset[i] == offer_asset[(i+1)%n]. ---
    for i in 0..n {
        let nxt = (i + 1) % n;
        constraints.push(eq_gate(
            lo.leg_col(i, lc::WANT_ASSET),
            lo.leg_col(nxt, lc::OFFER_ASSET),
        ));
    }

    // --- (b.iii) NO IN-RING DOUBLE-SPEND: nullifier[i] != nullifier[j] for every pair i<j. ---
    // (nf_i − nf_j)·inv − 1 == 0 : satisfiable iff nf_i ≠ nf_j (an inverse exists).
    for i in 0..n {
        for j in (i + 1)..n {
            constraints.push(gate(sub(
                LeanExpr::mul(
                    sub(
                        LeanExpr::Var(lo.leg_col(i, lc::NULLIFIER)),
                        LeanExpr::Var(lo.leg_col(j, lc::NULLIFIER)),
                    ),
                    LeanExpr::Var(lo.nf_inv_col(i, j)),
                ),
                LeanExpr::Const(1),
            )));
        }
    }

    // --- (c) PEDERSEN CONSERVATION over pedTwoGen (v, r): Σ C_in − Σ C_out = 0. ---
    // value coordinate: Σ value[i] − Σ out_val[i] == 0.
    constraints.push(gate(sub(
        sum_cols((0..n).map(|i| lo.leg_col(i, lc::VALUE))),
        sum_cols((0..n).map(|i| lo.leg_col(i, lc::OUT_VAL))),
    )));
    // blinding coordinate: Σ randomness[i] − Σ out_blind[i] == 0 (NOT range-checked — the
    // group-scalar coordinate rides the off-AIR Schnorr excess; a blinding wrap mints no VALUE).
    constraints.push(gate(sub(
        sum_cols((0..n).map(|i| lo.leg_col(i, lc::RANDOMNESS))),
        sum_cols((0..n).map(|i| lo.leg_col(i, lc::OUT_BLIND))),
    )));

    // --- (d.range) THE VALUE RANGE GADGET: every value / out_val / want_min ∈ [0, 2^VALUE_BITS). ---
    // Range-bounding value/out_val makes the field conservation gate IMPLY integer conservation
    // (legs_noWrap_conservation); range-bounding want_min is the compare's second operand.
    for t in 0..lo.num_range_targets() {
        for b in 0..VALUE_BITS {
            constraints.push(bool_gate(lo.range_bit_col(t, b)));
        }
        constraints.push(gate(recompose_body(
            LeanExpr::Var(lo.range_target_col(t)),
            |b| lo.range_bit_col(t, b),
        )));
    }

    // --- (d.fill) THE PARTIAL-FILL COMPARE: want_min[i] ≤ offer_amount[(i+1)%n]. ---
    // For each edge i, a VALUE_BITS-bit difference recomposes to `offer_amount[(i+1)%n] −
    // want_min[i]`. Such a preimage EXISTS iff the subtraction did not underflow, i.e. iff
    // `offer ≥ want_min` (Dregg2.Bignum.le_iff / sub_underflow_unsat at one BabyBear limb). An
    // under-want ring (offer < want_min) has the difference wrap to `p − k`, no VALUE_BITS-bit
    // preimage ⇒ UNSAT.
    for i in 0..n {
        let nxt = (i + 1) % n;
        // difference = offer_amount[nxt] − want_min[i].
        let diff = sub(
            LeanExpr::Var(lo.leg_col(nxt, lc::OFFER_AMOUNT)),
            LeanExpr::Var(lo.leg_col(i, lc::WANT_MIN)),
        );
        for b in 0..VALUE_BITS {
            constraints.push(bool_gate(lo.fill_bit_col(i, b)));
        }
        constraints.push(gate(recompose_body(diff, |b| lo.fill_bit_col(i, b))));
    }

    // --- the value-binding pad cells are constant-zero (fact absorbs [asset, randomness, 0];
    // vb_pad1 is now vestigial). ---
    for i in 0..n {
        constraints.push(gate(LeanExpr::Var(lo.leg_col(i, lc::VB_PAD0))));
        constraints.push(gate(LeanExpr::Var(lo.leg_col(i, lc::VB_PAD1))));
    }

    // --- the value-binding RECOMPUTE (per leg): value_binding[i] == hash_fact(value[i],
    // [asset[i], randomness[i], 0]). The fusion anchor, now binding the ASSET too (the PQ
    // HashCR value-commitment binds (value, asset) jointly). ---
    for i in 0..n {
        let site = fact_site_always(
            lo.leg_col(i, lc::VALUE_BINDING),
            &[
                lo.leg_col(i, lc::VALUE),
                lo.leg_col(i, lc::ASSET),
                lo.leg_col(i, lc::RANDOMNESS),
                lo.leg_col(i, lc::VB_PAD0),
            ],
            alloc_lanes(),
        );
        constraints.push(site);
    }

    // --- the exposed n·3-lane claim, pinned to the PIs (First row). ---
    for i in 0..n {
        for (slot, col) in [lc::NULLIFIER, lc::MERKLE_ROOT, lc::VALUE_BINDING]
            .into_iter()
            .enumerate()
        {
            constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col: lo.leg_col(i, col),
                pi_index: i * RING_LEG_CLAIM_LEN + slot,
            }));
        }
    }

    EffectVmDescriptor2 {
        name: format!("shielded-ring-clear-{n}"),
        trace_width: width,
        public_input_count: lo.claim_len(),
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// The main-trace height (power of two; every row carries the same constant ring data).
const TRACE_HEIGHT: usize = 8;

/// An **N-leg** shielded ring witness: the N shielded spends (each an honest
/// [`ShieldedSpendWitness`]) plus the ring-level matcher fields and the created output notes.
/// `honest_tight` / `honest_partial_fill` build genuine conserving fused N-cycles.
#[derive(Clone, Debug)]
pub struct ShieldedRingN {
    /// Per-leg shielded spend (asset_type/value/randomness ARE the fused note fields).
    pub leg: Vec<ShieldedSpendWitness>,
    /// Per-leg matcher offer asset (fused: `== leg[i].asset_type`).
    pub offer_asset: Vec<BabyBear>,
    /// Per-leg matcher offer amount (fused: `== leg[i].value`).
    pub offer_amount: Vec<BabyBear>,
    /// Per-leg matcher wanted asset (ring: `want_asset[i] == offer_asset[(i+1)%n]`).
    pub want_asset: Vec<BabyBear>,
    /// Per-leg matcher wanted minimum (partial fill: `want_min[i] ≤ offer_amount[(i+1)%n]`).
    pub want_min: Vec<BabyBear>,
    /// Per-leg created (output) note value — Σ out_val must equal Σ leg.value.
    pub out_val: Vec<BabyBear>,
    /// Per-leg created (output) note blinding — Σ out_blind must equal Σ leg.randomness.
    pub out_blind: Vec<BabyBear>,
}

/// A real depth-4 shielded-spend witness for one leg (forward-chained padding makes the
/// ungated membership/leaf/value-binding hashes hold on every trace row). Twin of the 2-leg
/// module's `demo_leg_witness`.
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

impl ShieldedRingN {
    /// Number of legs.
    pub fn n(&self) -> usize {
        self.leg.len()
    }

    /// The genuine N-cycle: leg `i` offers `(asset i, value vals[i])` and wants `asset
    /// (i+1)%n`. `want_min[i]` is set from `wants[i]` (`≤ vals[(i+1)%n]`, the received
    /// amount). Fused, a valid `CycleValid` N-cycle, value-neutral (out_val / out_blind are
    /// the cyclic permutation of the offered values / randomnesses, so both sums are
    /// preserved), and each leg receives ≥ its declared minimum.
    fn build(vals: &[u32], wants: &[u32]) -> Self {
        let n = vals.len();
        assert!(n >= 2 && wants.len() == n);
        let leg: Vec<ShieldedSpendWitness> = (0..n)
            .map(|i| demo_leg_witness(0x10 + i as u8, i as u32, vals[i]))
            .collect();
        let offer_asset: Vec<BabyBear> = (0..n).map(|i| leg[i].asset_type).collect();
        let offer_amount: Vec<BabyBear> = (0..n).map(|i| leg[i].value).collect();
        // ring edge: want_asset[i] = offer_asset[(i+1)%n]
        let want_asset: Vec<BabyBear> = (0..n).map(|i| leg[(i + 1) % n].asset_type).collect();
        // partial fill: want_min[i] ≤ received = offer_amount[(i+1)%n]
        let want_min: Vec<BabyBear> = (0..n).map(|i| BabyBear::new(wants[i])).collect();
        // value-neutral swap: leg i receives the next leg's offered value + randomness.
        let out_val: Vec<BabyBear> = (0..n).map(|i| leg[(i + 1) % n].value).collect();
        let out_blind: Vec<BabyBear> = (0..n).map(|i| leg[(i + 1) % n].randomness).collect();
        ShieldedRingN {
            leg,
            offer_asset,
            offer_amount,
            want_asset,
            want_min,
            out_val,
            out_blind,
        }
    }

    /// A TIGHT N-cycle: each leg's want_min equals exactly the received amount.
    pub fn honest_tight(vals: &[u32]) -> Self {
        let n = vals.len();
        let wants: Vec<u32> = (0..n).map(|i| vals[(i + 1) % n]).collect();
        Self::build(vals, &wants)
    }

    /// A PARTIAL-FILL N-cycle: each leg's want_min is STRICTLY below the received amount
    /// (`want_min[i] = vals[(i+1)%n] − 1`), so every leg is filled beyond its minimum — the
    /// general (non-tight) clearing. Requires each received value ≥ 1.
    pub fn honest_partial_fill(vals: &[u32]) -> Self {
        let n = vals.len();
        let wants: Vec<u32> = (0..n)
            .map(|i| {
                vals[(i + 1) % n]
                    .checked_sub(1)
                    .expect("received value ≥ 1")
            })
            .collect();
        Self::build(vals, &wants)
    }

    /// The per-leg 3-slot claim `[nullifier, merkle_root, value_binding]`.
    pub fn leg_claim(&self, i: usize) -> [BabyBear; RING_LEG_CLAIM_LEN] {
        [
            self.leg[i].nullifier(),
            self.leg[i].merkle_root(),
            self.leg[i].value_binding(),
        ]
    }

    /// The full `n·3`-lane public-input tuple `[nf, root, vb]ⁿ`.
    pub fn public_inputs(&self) -> Vec<BabyBear> {
        let mut pis = Vec::with_capacity(self.n() * RING_LEG_CLAIM_LEN);
        for i in 0..self.n() {
            pis.extend_from_slice(&self.leg_claim(i));
        }
        pis
    }

    /// The base main trace (`TRACE_HEIGHT × pre_lane_width`): every row carries the same
    /// constant ring data; the chip lane columns are appended + filled by the descriptor-
    /// driven prover weld.
    fn base_trace(&self) -> Vec<Vec<BabyBear>> {
        let n = self.n();
        let lo = Layout::new(n);
        let mut row = vec![BabyBear::ZERO; lo.pre_lane_width()];
        for i in 0..n {
            let w = &self.leg[i];
            row[lo.leg_col(i, lc::VALUE)] = w.value;
            row[lo.leg_col(i, lc::RANDOMNESS)] = w.randomness;
            row[lo.leg_col(i, lc::VB_PAD0)] = BabyBear::ZERO;
            row[lo.leg_col(i, lc::VB_PAD1)] = BabyBear::ZERO;
            row[lo.leg_col(i, lc::VALUE_BINDING)] = w.value_binding();
            row[lo.leg_col(i, lc::ASSET)] = w.asset_type;
            row[lo.leg_col(i, lc::OFFER_ASSET)] = self.offer_asset[i];
            row[lo.leg_col(i, lc::OFFER_AMOUNT)] = self.offer_amount[i];
            row[lo.leg_col(i, lc::WANT_ASSET)] = self.want_asset[i];
            row[lo.leg_col(i, lc::WANT_MIN)] = self.want_min[i];
            row[lo.leg_col(i, lc::NULLIFIER)] = w.nullifier();
            row[lo.leg_col(i, lc::MERKLE_ROOT)] = w.merkle_root();
            row[lo.leg_col(i, lc::OUT_VAL)] = self.out_val[i];
            row[lo.leg_col(i, lc::OUT_BLIND)] = self.out_blind[i];
        }

        // Nullifier pairwise-difference inverses (double-spend gate witness). If any pair
        // collides, no inverse exists; a zero witness makes `(nf_i−nf_j)·inv − 1` = −1 ≠ 0
        // (UNSAT) — the double-spend refusal.
        for i in 0..n {
            for j in (i + 1)..n {
                let d = self.leg[i].nullifier() - self.leg[j].nullifier();
                row[lo.nf_inv_col(i, j)] = d.inverse().unwrap_or(BabyBear::ZERO);
            }
        }

        // Range-gadget witness: bit-decompose each range target. An out-of-range / wrapped
        // value fails the recompose gate ⇒ UNSAT (the range tooth).
        for t in 0..lo.num_range_targets() {
            let v = row[lo.range_target_col(t)].as_u32();
            for b in 0..VALUE_BITS {
                row[lo.range_bit_col(t, b)] = BabyBear::new((v >> b) & 1);
            }
        }

        // Partial-fill difference witness: bit-decompose `offer_amount[(i+1)%n] − want_min[i]`.
        // For an honest ring (offer ≥ want_min) the difference is a small nonneg with a
        // VALUE_BITS-bit preimage; an under-want ring wraps to `p − k` whose low VALUE_BITS bits
        // do NOT recompose ⇒ UNSAT (the partial-fill tooth).
        for i in 0..n {
            let nxt = (i + 1) % n;
            let diff = self.offer_amount[nxt] - self.want_min[i];
            let v = diff.as_u32();
            for b in 0..VALUE_BITS {
                row[lo.fill_bit_col(i, b)] = BabyBear::new((v >> b) & 1);
            }
        }

        vec![row; TRACE_HEIGHT]
    }
}

/// The shared inner IR-v2 prove for the N-leg ring-clearing descriptor over a witness.
fn prove_ring_clear_inner(
    ring: &ShieldedRingN,
    config: &DreggRecursionConfig,
) -> Result<
    (
        EffectVmDescriptor2,
        dregg_circuit::descriptor_ir2::Ir2BatchProof<DreggRecursionConfig>,
    ),
    String,
> {
    let desc = shielded_ring_clear_descriptor(ring.n());
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
    .map_err(|e| format!("N-leg ring-clear inner IR-v2 prove failed: {e}"))?;
    Ok((desc, inner))
}

/// **The N-leg ring-clearing LEAF.** Prove the ring-clearing descriptor AIR over the ring
/// witness and RE-EXPOSE its `n·3`-lane cleared-ring claim `[nf, root, vb]ⁿ` as an in-circuit
/// `expose_claim`, so the apex can bind each leg's 3-slot claim to its shielded-spend leaf. A
/// ring that violates fusion / the cycle edges / the partial-fill inequality / distinct
/// nullifiers / conservation has no satisfying assembly — no foldable leaf is minted.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_shielded_ring_clear_leaf(
    ring: &ShieldedRingN,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let (desc, inner) = prove_ring_clear_inner(ring, config)?;
    let pis = ring.public_inputs();
    let claim_len = ring.n() * RING_LEG_CLAIM_LEN;
    prove_descriptor_leaf_with_pi_slice_expose(&desc, &inner, &pis, config, 0, claim_len)
        .map_err(|e| format!("N-leg ring-clear claim leaf expose-wrap failed: {e}"))
}

/// Read the exposed cleared-ring claim (`n·3` lanes) off a leaf/apex minted with the expose.
pub fn read_exposed_ring_claim(
    output: &RecursionOutput<DreggRecursionConfig>,
    n: usize,
) -> Option<Vec<BabyBear>> {
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
    let claim_len = n * RING_LEG_CLAIM_LEN;
    if claims.len() < claim_len {
        return None;
    }
    Some(claims[..claim_len].to_vec())
}

/// A single binding aggregation node: fold `left` (carrying the `n·3`-lane exposed ring claim)
/// with a shielded-spend `sub` leaf, `connect`ing `left`'s leg-`leg_idx` 3-slot window to the
/// sub-proof's genuine `[nullifier, merkle_root, value_binding]`, and RE-EXPOSING the full
/// `n·3`-lane ring claim so the next node can bind the next leg. A leg whose claimed tuple no
/// verifying shielded-spend backs is a `connect` conflict ⇒ UNSAT ⇒ no root.
fn bind_leg_node(
    left: &RecursionOutput<DreggRecursionConfig>,
    sub: &RecursionOutput<DreggRecursionConfig>,
    leg_idx: usize,
    n: usize,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::ivc_turn_chain::expose_claim_instance_index;
    use crate::plonky3_recursion_impl::recursive::create_recursion_backend;
    use p3_circuit::CircuitBuilder;
    use p3_recursion::{BatchOnly, Target, build_and_prove_aggregation_layer_with_expose};

    type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

    let left_idx = expose_claim_instance_index(&left.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "N-leg ring-clear left leaf carries no expose_claim table — it must re-expose \
                     the n·3-lane cleared-ring claim"
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
    let claim_len = n * RING_LEG_CLAIM_LEN;

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>],
                       _left_vk_cap: &[Target],
                       _right_vk_cap: &[Target]| {
        let lg = left_apt
            .get(left_idx)
            .expect("N-leg ring-clear left leaf's re-exposed claim instance present");
        let cs = right_apt
            .get(sub_idx)
            .expect("shielded-spend sub-proof's exposed tuple instance present");
        debug_assert!(lg.len() >= claim_len && cs.len() >= RING_LEG_CLAIM_LEN);
        // THE BINDING TOOTH, IN-CIRCUIT: leg `leg_idx`'s claimed 3-slot tuple must equal the
        // shielded-spend leaf's GENUINE bound tuple, lane by lane.
        for k in 0..RING_LEG_CLAIM_LEN {
            cb.connect(lg[base + k], cs[k]);
        }
        // Re-expose the full n·3-lane cleared-ring claim (carried forward).
        let bound: Vec<Target> = (0..claim_len).map(|k| lg[k]).collect();
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
        reason: format!("N-leg ring-clear leg-{leg_idx} binding node failed: {e:?}"),
    })
}

/// **THE N-LEG SHIELDED RING-CLEARING APEX.** Fold the ring-clearing leaf
/// ([`prove_shielded_ring_clear_leaf`]) with the N shielded-spend leaves
/// ([`crate::shielded_spend_leaf_adapter::prove_shielded_spend_leaf_with_claim`]), binding
/// each leg's exposed 3-slot claim to its spend leaf in-circuit. The apex verifies the
/// conserving fused N-cycle (admitting partial fills) over the hidden commitments and
/// RE-EXPOSES the cleared ring's committed claim `[nf, root, vb]ⁿ`.
///
/// A leg claiming a tuple that no verifying shielded spend backs is a `connect` conflict ⇒
/// UNSAT ⇒ no apex root. `spend_leaves.len()` must equal the ring's leg count.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_shielded_ring_clearing_apex(
    ring_leaf: &RecursionOutput<DreggRecursionConfig>,
    spend_leaves: &[RecursionOutput<DreggRecursionConfig>],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    let n = spend_leaves.len();
    assert!(n >= 2, "an N-leg ring needs ≥ 2 spend leaves");
    let mut node = bind_leg_node(ring_leaf, &spend_leaves[0], 0, n, config)?;
    for (i, leaf) in spend_leaves.iter().enumerate().skip(1) {
        node = bind_leg_node(&node, leaf, i, n, config)?;
    }
    Ok(node)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ivc_turn_chain::ir2_leaf_wrap_config;
    use crate::shielded_spend_leaf_adapter::{
        prove_shielded_spend_leaf_with_claim, shielded_spend_leaf_public_inputs,
    };

    /// Assemble the full N-leg apex from a ring witness (helper for the fold+verify teeth).
    fn prove_apex(
        r: &ShieldedRingN,
        config: &DreggRecursionConfig,
    ) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
        let ring_leaf = prove_shielded_ring_clear_leaf(r, config)?;
        let mut spends = Vec::with_capacity(r.n());
        for i in 0..r.n() {
            let pis = shielded_spend_leaf_public_inputs(&r.leg[i]);
            let s = prove_shielded_spend_leaf_with_claim(&r.leg[i], &pis, config)
                .map_err(|e| format!("spend leaf {i}: {e}"))?;
            spends.push(s);
        }
        prove_shielded_ring_clearing_apex(&ring_leaf, &spends, config)
            .map_err(|e| format!("apex: {e:?}"))
    }

    /// `catch_unwind` a leaf-prove, returning `true` iff it was UNSAT (Err or panic).
    fn is_unsat_leaf(r: &ShieldedRingN, config: &DreggRecursionConfig) -> bool {
        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_shielded_ring_clear_leaf(r, config)
        }));
        !matches!(res, Ok(Ok(_)))
    }

    /// The descriptor lowers to the expected shape for N legs: N fact sites, N·3 PiBindings,
    /// and the fusion / ring / conservation / range / partial-fill gates.
    #[test]
    fn nleg_descriptor_lowers() {
        for n in [2usize, 3, 4, 5] {
            let lo = Layout::new(n);
            let desc = shielded_ring_clear_descriptor(n);
            assert_eq!(desc.public_input_count, n * RING_LEG_CLAIM_LEN);
            let sites = desc
                .constraints
                .iter()
                .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
                .count();
            assert_eq!(sites, n, "one value-binding recompute per leg");
            let pins = desc
                .constraints
                .iter()
                .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
                .count();
            assert_eq!(pins, n * RING_LEG_CLAIM_LEN, "nf/root/vb per leg");
            assert_eq!(
                desc.trace_width,
                lo.pre_lane_width() + n * (CHIP_OUT_LANES - 1)
            );
            // range targets (3n) × (VALUE_BITS bool + 1 recompose) + fill edges (n) × same.
            let gates = desc
                .constraints
                .iter()
                .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::Gate(_))))
                .count();
            assert!(
                gates >= (lo.num_range_targets() + n) * (VALUE_BITS + 1),
                "each range target + each fill edge contributes VALUE_BITS bool gates + 1 recompose"
            );
        }
    }

    /// The layout's pair-index bijects the strict upper triangle onto `[0, n(n-1)/2)`.
    #[test]
    fn pair_index_is_a_bijection() {
        for n in 2..8 {
            let lo = Layout::new(n);
            let mut seen = vec![false; lo.num_pairs()];
            for i in 0..n {
                for j in (i + 1)..n {
                    let idx = lo.pair_index(i, j);
                    assert!(idx < lo.num_pairs(), "pair index in range");
                    assert!(!seen[idx], "pair index unique");
                    seen[idx] = true;
                }
            }
            assert!(seen.iter().all(|&b| b), "every pair index hit");
        }
    }

    /// The honest tight / partial-fill rings ARE fused, cyclic, conserving (checked outside
    /// the circuit as a sanity floor), and partial-fill genuinely fills beyond the minimum.
    #[test]
    fn honest_rings_are_fused_cyclic_conserving() {
        for n in [3usize, 4, 5] {
            let vals: Vec<u32> = (0..n).map(|i| 3 + i as u32).collect();
            for (r, tight) in [
                (ShieldedRingN::honest_tight(&vals), true),
                (ShieldedRingN::honest_partial_fill(&vals), false),
            ] {
                let sum_in: u64 = (0..n).map(|i| r.leg[i].value.as_u32() as u64).sum();
                let sum_out: u64 = (0..n).map(|i| r.out_val[i].as_u32() as u64).sum();
                assert_eq!(sum_in, sum_out, "Σ value conserved (n={n})");
                for i in 0..n {
                    assert_eq!(r.offer_asset[i], r.leg[i].asset_type, "fused asset");
                    assert_eq!(r.offer_amount[i], r.leg[i].value, "fused amount");
                    assert_eq!(r.want_asset[i], r.offer_asset[(i + 1) % n], "ring edge");
                    let recv = r.offer_amount[(i + 1) % n].as_u32();
                    let wmin = r.want_min[i].as_u32();
                    assert!(wmin <= recv, "partial-fill inequality holds");
                    if !tight {
                        assert!(wmin < recv, "partial fill strictly below received");
                    }
                }
            }
        }
    }

    /// THE POSITIVE POLE (3-leg): a genuine tight conserving 3-ring FOLDS + verifies, and the
    /// apex re-exposes the cleared ring's `[nf,root,vb]³` committed claim.
    #[test]
    fn honest_3ring_folds_and_verifies() {
        let config = ir2_leaf_wrap_config();
        let r = ShieldedRingN::honest_tight(&[3, 4, 5]);
        let apex = prove_apex(&r, &config).expect("honest 3-ring must fold into a bound apex root");
        let cleared =
            read_exposed_ring_claim(&apex, r.n()).expect("apex re-exposes the 9-lane claim");
        assert_eq!(
            cleared,
            r.public_inputs(),
            "cleared claim is the three legs' genuine tuples"
        );
    }

    /// THE POSITIVE POLE (4-leg): a genuine tight conserving 4-ring FOLDS + verifies.
    #[test]
    fn honest_4ring_folds_and_verifies() {
        let config = ir2_leaf_wrap_config();
        let r = ShieldedRingN::honest_tight(&[3, 4, 5, 6]);
        let apex = prove_apex(&r, &config).expect("honest 4-ring must fold into a bound apex root");
        let cleared =
            read_exposed_ring_claim(&apex, r.n()).expect("apex re-exposes the 12-lane claim");
        assert_eq!(
            cleared,
            r.public_inputs(),
            "cleared claim is the four legs' genuine tuples"
        );
    }

    /// THE POSITIVE POLE (PARTIAL FILL): a genuine conserving 4-ring in which EVERY leg is
    /// filled strictly beyond its declared want_min FOLDS + verifies — the general (non-tight)
    /// clearing, the partial-fill `offer ≥ want_min` inequality satisfied with slack.
    #[test]
    fn honest_partial_fill_4ring_folds_and_verifies() {
        let config = ir2_leaf_wrap_config();
        let r = ShieldedRingN::honest_partial_fill(&[3, 4, 5, 6]);
        let apex = prove_apex(&r, &config)
            .expect("honest partial-fill 4-ring must fold into a bound apex root");
        let cleared = read_exposed_ring_claim(&apex, r.n()).expect("apex re-exposes the claim");
        assert_eq!(
            cleared,
            r.public_inputs(),
            "cleared claim is the legs' genuine tuples"
        );
    }

    /// THE NEGATIVE POLE (conservation): a value-minting N-ring (an output worth one more than
    /// the inputs cover) has a non-zero Pedersen excess — UNSAT, no foldable leaf.
    #[test]
    fn nonconserving_nring_is_unsat() {
        let config = ir2_leaf_wrap_config();
        let mut r = ShieldedRingN::honest_tight(&[3, 4, 5]);
        r.out_val[0] = r.out_val[0] + BabyBear::ONE;
        assert!(
            is_unsat_leaf(&r, &config),
            "a value-minting 3-ring minted a leaf — conservation OPEN"
        );
    }

    /// THE NEGATIVE POLE (WRAPAROUND MINT): shift value between two outputs by 2^VALUE_BITS —
    /// the FIELD conservation sum is unchanged, but one output leaves [0,2^VALUE_BITS) and its
    /// counterpart wraps to `p − k`. Only the range gadget refuses it ⇒ UNSAT.
    #[test]
    fn wraparound_mint_nring_is_unsat() {
        let config = ir2_leaf_wrap_config();
        let mut r = ShieldedRingN::honest_tight(&[3, 4, 5]);
        let wrap = BabyBear::new(1u32 << VALUE_BITS);
        r.out_val[0] = r.out_val[0] + wrap;
        r.out_val[1] = r.out_val[1] - wrap;
        // The field conservation gate is STILL satisfied (Σ unchanged) — only the range gadget bites.
        let sum_in: BabyBear = (0..r.n())
            .map(|i| r.leg[i].value)
            .fold(BabyBear::ZERO, |a, b| a + b);
        let sum_out: BabyBear = (0..r.n())
            .map(|i| r.out_val[i])
            .fold(BabyBear::ZERO, |a, b| a + b);
        assert_eq!(
            sum_in, sum_out,
            "wraparound keeps the FIELD conservation equation satisfied"
        );
        assert!(
            is_unsat_leaf(&r, &config),
            "a wraparound-minting N-ring minted a leaf — range OPEN"
        );
    }

    /// THE NEGATIVE POLE (double-spend): two legs re-use ONE note (the same nullifier) — the
    /// pairwise `nullifier[i] != nullifier[j]` gate has no inverse witness ⇒ UNSAT.
    #[test]
    fn double_spend_nring_is_unsat() {
        let config = ir2_leaf_wrap_config();
        let mut r = ShieldedRingN::honest_tight(&[3, 4, 5]);
        // Leg 2 re-spends leg 0's note ⇒ colliding nullifiers on a non-adjacent pair (0,2).
        r.leg[2] = r.leg[0].clone();
        assert!(
            is_unsat_leaf(&r, &config),
            "a double-spend N-ring minted a leaf — nullifier OPEN"
        );
    }

    /// THE NEGATIVE POLE (mis-fusion): a leg whose matcher offer amount does NOT equal its note
    /// value fails the `offer_amount == value` fusion gate ⇒ UNSAT. The cycle is kept
    /// self-consistent so ONLY the fusion gate bites.
    #[test]
    fn misfused_leg_nring_is_unsat() {
        let config = ir2_leaf_wrap_config();
        let mut r = ShieldedRingN::honest_tight(&[3, 4, 5]);
        // Decouple leg 0's cleared offer from its note value; keep the received edge (leg 2
        // wants leg 0's offer) consistent so only fusion breaks.
        r.offer_amount[0] = r.offer_amount[0] + BabyBear::ONE;
        r.want_min[2] = r.want_min[2] + BabyBear::ONE;
        assert!(
            is_unsat_leaf(&r, &config),
            "a mis-fused leg minted a leaf — fusion OPEN"
        );
    }

    /// THE NEGATIVE POLE (UNDER-WANT — the partial-fill tooth's reason to exist): a leg whose
    /// declared want_min EXCEEDS the amount it receives (`want_min[i] > offer_amount[(i+1)%n]`)
    /// makes the partial-fill difference `offer − want_min` wrap negative — no VALUE_BITS-bit
    /// preimage ⇒ UNSAT. The circuit twin of `Dregg2.Bignum.sub_underflow_unsat`.
    #[test]
    fn under_want_nring_is_unsat() {
        let config = ir2_leaf_wrap_config();
        let mut r = ShieldedRingN::honest_tight(&[3, 4, 5]);
        // Leg 0 receives offer_amount[1] = 4; demand 5 (> 4). The ring stays conserving and
        // fused — ONLY the partial-fill inequality is violated.
        r.want_min[0] = r.offer_amount[1] + BabyBear::ONE;
        // Sanity: still conserving + fused (only the ≥ compare should reject it).
        let sum_in: BabyBear = (0..r.n())
            .map(|i| r.leg[i].value)
            .fold(BabyBear::ZERO, |a, b| a + b);
        let sum_out: BabyBear = (0..r.n())
            .map(|i| r.out_val[i])
            .fold(BabyBear::ZERO, |a, b| a + b);
        assert_eq!(sum_in, sum_out, "under-want keeps conservation satisfied");
        assert!(
            is_unsat_leaf(&r, &config),
            "an under-want N-ring minted a leaf — partial-fill OPEN"
        );
    }

    /// THE BINDING TOOTH (apex): a ring-clearing leaf whose leg claims a tuple a DIFFERENT
    /// spend leaf does not back cannot bind — the apex `connect` conflicts ⇒ UNSAT ⇒ no root.
    #[test]
    fn mismatched_fold_does_not_bind() {
        let config = ir2_leaf_wrap_config();
        let r = ShieldedRingN::honest_tight(&[3, 4, 5]);
        let ring_leaf = prove_shielded_ring_clear_leaf(&r, &config).expect("honest 3-ring leaf");

        let mut spends = Vec::with_capacity(r.n());
        for i in 0..r.n() {
            let pis = shielded_spend_leaf_public_inputs(&r.leg[i]);
            spends.push(
                prove_shielded_spend_leaf_with_claim(&r.leg[i], &pis, &config)
                    .expect("honest spend leaf"),
            );
        }
        // Replace leg 2's spend leaf with a spend of a DIFFERENT note — its tuple cannot connect.
        let other = demo_leg_witness(0x77, 2, 5);
        assert_ne!(other.nullifier(), r.leg[2].nullifier(), "distinct spends");
        let pis_other = shielded_spend_leaf_public_inputs(&other);
        spends[2] = prove_shielded_spend_leaf_with_claim(&other, &pis_other, &config)
            .expect("the mismatched leaf is itself an honest spend of a DIFFERENT note");

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_shielded_ring_clearing_apex(&ring_leaf, &spends, &config)
        }));
        assert!(
            !matches!(result, Ok(Ok(_))),
            "a leg bound to a non-backing spend — apex binding OPEN"
        );
    }
}
