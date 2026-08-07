//! The `FieldDelta` RESULT-RANGE AIR — the in-AIR bit-decomposition gadget that
//! closes the flagship game-economy underflow-wrap MINT.
//!
//! ## The hole (audit: CRITICAL)
//!
//! `StateConstraint::FieldDelta { index, delta }` enforces `new == old + delta`
//! over a WRAPPING add (`cell::program::eval::field_add`, u64 lane; the in-circuit
//! projection is a BabyBear FIELD sum). The wrap is LOAD-BEARING for the affordable
//! decrement — a purchase encodes `delta` as the additive inverse of the price
//! (`120 + (2^64 − 50) == 70`), so the equation itself CANNOT be de-wrapped. But a
//! wrapping equation with NO range on the result is a mint: an UNAFFORDABLE
//! decrement (`old < |delta|`) is satisfiable by committing the WRAP value directly
//! (executor lane `2^64 − k`; the in-circuit BabyBear lane `p − k ≈ 2^31`), which
//! equals `old + delta mod p` and so passes `new == old + delta` while MINTING
//! ~2^31 gold / hp / quantity into the slot — bypassing the honest executor's
//! `.max(0)` clamp. Real exploit surface: The Descent / `dungeon-on-dregg` /
//! `dreggnet-offerings`.
//!
//! ## The fix (this module — the CIRCUIT lane)
//!
//! Range-check the RESULT slot: bit-decompose `new` into `RESULT_BITS` boolean
//! columns that recompose to it, forcing `new ∈ [0, 2^RESULT_BITS)`. With
//! `2^RESULT_BITS ≤ p` (compile-time asserted) the recompose sum is canonical, so a
//! WRAP value (`p − k`, which is `≥ 2^30`) has NO `RESULT_BITS`-bit preimage and is
//! UNSAT at the recompose gate — the mint is UNCONSTRUCTABLE. The affordable case
//! (`old ≥ |delta|`, result small) keeps its bit preimage and stays SAT: the
//! additive-inverse wrap encoding is preserved for the affordable decrement, refused
//! for the unaffordable one.
//!
//! This is the exact idiom the shielded-ring conservation weld used
//! (`shielded_ring_clearing_air.rs::(c.range)`) — a value-minting wraparound has no
//! bit preimage and dies at the recompose gate — applied to the `FieldDelta` result.
//! ⚠ That file is DELETED (2026-08-07, the Rust-authored shielded-spend tower, house
//! law #1), so the citation is to a retired precedent, not to live code. The idiom
//! itself is unaffected and lives on here and in the Lean-emitted wide-carrier limb
//! blocks (`Emit/ShieldedSpendCompleteEmit.lean` R1/R2/R3).
//!
//! ## Where it sits (honest map)
//!
//!   * The DEPLOYED teeth are the executor kernel re-check
//!     (`cell::program::eval` `FieldDelta` / `FieldDeltaInRange` arms, now range-
//!     forcing) and the off-AIR verifier re-eval
//!     (`circuit::effect_vm::verify::verify_slot_caveat_manifest`, now range-forcing).
//!     Those close the mint on the live path today.
//!   * THIS module is the in-AIR REALIZATION of that same result range — a genuine
//!     STARK constraint whose non-satisfiability a pure light client witnesses,
//!     rather than trusting an off-AIR re-eval over caller-supplied slot views. It is
//!     VK-affecting (a fresh descriptor / VK), matching the `satisfaction_weld`
//!     posture: built BESIDE the deployed off-AIR check, flipped onto the live
//!     descriptor path under a gated VK epoch.
//!
//! ## Named residual
//!
//!   * `RESULT_BITS = 30` caps a `FieldDelta` slot at `< 2^30 ≈ 1.07e9` (ample for
//!     gold / hp / quantity; every deployed game delta is in the tens–hundreds). A
//!     slot that must hold a larger legitimate value needs a wider (2-limb)
//!     decomposition, like the `balance` limb split — named, not built here.
//!   * The full executor-lane u64 range (`< 2^64`) is not expressible in one BabyBear
//!     field; the executor arm bounds the low u64 lane at `2^30` and rejects any
//!     non-zero high bytes (`eval::field_result_in_range`), which is a STRICTLY
//!     tighter bound than this in-AIR gadget carries — the two agree on refusing
//!     every wrap value.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, UMemBoundaryWitness, parse_vm_descriptor2,
    prove_vm_descriptor2_for_config,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};

use crate::plonky3_recursion_impl::recursive::DreggRecursionConfig;

/// **The in-AIR result range-gadget bit-width.** A witnessed `new` is bit-decomposed
/// into `RESULT_BITS` boolean columns recomposing to it, so it provably lies in
/// `[0, 2^RESULT_BITS)`. Matches `dregg_cell::program::eval::FIELD_DELTA_RESULT_BITS`
/// and `dregg_circuit::effect_vm::pi::FIELD_DELTA_RESULT_BITS`.
pub const RESULT_BITS: usize = 30;

/// No-wrap guarantee, checked at compile time: `2^RESULT_BITS ≤ p`, so the recompose
/// sum `Σⱼ 2ʲ·bitⱼ` is canonical (never itself wraps BabyBear) and a witnessed `new`
/// has an exact preimage iff `new ∈ [0, 2^RESULT_BITS)`.
const _: () = assert!(
    (1u64 << RESULT_BITS) <= BABYBEAR_P as u64,
    "RESULT_BITS too large: the recompose sum could wrap BabyBear"
);

// Column layout: the transition triple, then the result's bit block.
const OLD_COL: usize = 0;
const DELTA_COL: usize = 1;
const NEW_COL: usize = 2;
const BIT_BASE: usize = 3;
const WIDTH: usize = BIT_BASE + RESULT_BITS;

/// The trace height (a power of two; every row carries the same constant transition
/// data — the row-local gates fire on every row, the PiBindings on the first row).
const TRACE_HEIGHT: usize = 8;

/// Public inputs: the exact-delta transition triple `[old, delta, new]`.
#[cfg_attr(not(test), allow(dead_code))]
const PI_COUNT: usize = 3;

/// Column of bit `j` of the result decomposition.
const fn bit_col(j: usize) -> usize {
    BIT_BASE + j
}

/// Exact IR2 bytes emitted and pinned by
/// `Dregg2.Circuit.Emit.FieldDeltaRangeEmit`.
pub const FIELD_DELTA_RANGE_DESCRIPTOR_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/field-delta-result-range.json");

/// **The FieldDelta-result-range descriptor.** Lean enforces, per row:
///   * the exact-delta transition `new − (old + delta) == 0` (the deployed
///     `FieldDelta` gate — the WRAPPING modular equation, kept faithful), and
///   * the RESULT range gadget: each bit column boolean, and `new` recomposes to
///     its `RESULT_BITS`-bit decomposition (so `new ∈ [0, 2^RESULT_BITS)`).
/// The triple `[old, delta, new]` is pinned to the public inputs on the first row.
pub fn field_delta_range_descriptor() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(FIELD_DELTA_RANGE_DESCRIPTOR_JSON)
        .expect("Lean-emitted FieldDelta range descriptor must parse")
}

/// One `FieldDelta` transition case: the pre-state slot `old`, the (possibly
/// additive-inverse) `delta`, and the committed result `new = old + delta`.
#[derive(Clone, Copy, Debug)]
pub struct FieldDeltaCase {
    pub old: BabyBear,
    pub delta: BabyBear,
    pub new: BabyBear,
}

/// The additive inverse of `n` in BabyBear (`p − n mod p`) — the in-circuit twin of
/// the executor's `field_neg_u64`: a DECREMENT of `n` is encoded as `+ neg(n)`.
pub fn neg(n: u32) -> BabyBear {
    BabyBear::ZERO - BabyBear::new(n)
}

impl FieldDeltaCase {
    /// An INCREMENT / affordable-DECREMENT transition: `new = old + delta` with the
    /// result committed as the genuine (canonical) field sum.
    pub fn step(old: u32, delta: BabyBear) -> Self {
        let old_f = BabyBear::new(old);
        FieldDeltaCase {
            old: old_f,
            delta,
            new: old_f + delta,
        }
    }

    /// The public inputs `[old, delta, new]`.
    pub fn public_inputs(&self) -> Vec<BabyBear> {
        vec![self.old, self.delta, self.new]
    }

    /// The base trace: every row carries the constant transition triple plus the
    /// `RESULT_BITS`-bit decomposition of `new` (its low `RESULT_BITS` bits). For an
    /// IN-RANGE result the recompose gate holds; for a wrapped / out-of-range result
    /// the low bits do NOT recompose to the canonical field value, so the recompose
    /// gate is violated ⇒ UNSAT.
    pub fn base_trace(&self) -> Vec<Vec<BabyBear>> {
        let mut row = vec![BabyBear::ZERO; WIDTH];
        row[OLD_COL] = self.old;
        row[DELTA_COL] = self.delta;
        row[NEW_COL] = self.new;
        let v = self.new.as_u32();
        for j in 0..RESULT_BITS {
            row[bit_col(j)] = BabyBear::new((v >> j) & 1);
        }
        vec![row; TRACE_HEIGHT]
    }
}

/// Prove the `FieldDelta`-result-range descriptor over one transition case. Returns
/// `Ok` iff the case satisfies BOTH the exact-delta gate AND the result range gadget;
/// a wrapped (mint) result has no bit preimage and fails to prove (the range tooth).
pub fn prove_field_delta_range(
    case: &FieldDeltaCase,
    config: &DreggRecursionConfig,
) -> Result<(), String> {
    let desc = field_delta_range_descriptor();
    let pis = case.public_inputs();
    let base_trace = case.base_trace();
    prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc,
        &base_trace,
        &pis,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .map(|_| ())
    .map_err(|e| format!("field-delta-range prove failed: {e}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ivc_turn_chain::ir2_leaf_wrap_config;

    /// The descriptor lowers to the expected shape: 1 transition gate + (RESULT_BITS
    /// boolean gates + 1 recompose gate) + 3 PiBindings.
    #[test]
    fn descriptor_lowers() {
        let desc = field_delta_range_descriptor();
        assert_eq!(desc.public_input_count, PI_COUNT);
        assert_eq!(desc.trace_width, WIDTH);
        // 1 transition + RESULT_BITS boolean + 1 recompose + 3 PiBinding.
        assert_eq!(desc.constraints.len(), 1 + RESULT_BITS + 1 + 3);
    }

    /// The wrap value is genuinely `≥ 2^RESULT_BITS` (has no bit preimage): a witness
    /// sanity check that the mint case actually exercises the range gate.
    #[test]
    fn unaffordable_result_is_out_of_range() {
        // old = 30, delta = neg(50): new = 30 + (p − 50) = p − 20 (canonical).
        let case = FieldDeltaCase::step(30, neg(50));
        assert_eq!(
            case.new.as_u32(),
            BABYBEAR_P - 20,
            "the wrap value is p − 20"
        );
        assert!(
            case.new.as_u32() >= (1u32 << RESULT_BITS),
            "the wrap value is out of [0, 2^RESULT_BITS) — no bit preimage"
        );
        // the affordable case IS in range.
        let ok = FieldDeltaCase::step(120, neg(50));
        assert_eq!(ok.new.as_u32(), 70);
        assert!(ok.new.as_u32() < (1u32 << RESULT_BITS));
    }

    /// THE POSITIVE POLE — an affordable decrement (`old = 120`, `delta = −50`,
    /// `new = 70`) proves: the exact-delta gate holds (`120 + (p − 50) ≡ 70`) AND the
    /// result has a RESULT_BITS-bit preimage. The additive-inverse wrap encoding is
    /// preserved for the affordable case.
    #[test]
    fn affordable_decrement_is_sat() {
        let config = ir2_leaf_wrap_config();
        let case = FieldDeltaCase::step(120, neg(50));
        prove_field_delta_range(&case, &config)
            .expect("the affordable decrement (result 70, in range) must prove");
    }

    /// THE POSITIVE POLE (boundary) — spending the LAST coin (`old = 50`, `delta =
    /// −50`, `new = 0`) proves: `0` is in range. The tooth is exact, not a keep-one-
    /// coin hack.
    #[test]
    fn last_coin_decrement_is_sat() {
        let config = ir2_leaf_wrap_config();
        let case = FieldDeltaCase::step(50, neg(50));
        assert_eq!(case.new.as_u32(), 0);
        prove_field_delta_range(&case, &config)
            .expect("spending the last coin (result 0, in range) must prove");
    }

    /// THE POSITIVE POLE (increment) — a genuine gain (`old = 40`, `delta = +500`,
    /// `new = 540`, e.g. `seize the takings`) proves.
    #[test]
    fn increment_is_sat() {
        let config = ir2_leaf_wrap_config();
        let case = FieldDeltaCase::step(40, BabyBear::new(500));
        assert_eq!(case.new.as_u32(), 540);
        prove_field_delta_range(&case, &config).expect("an honest increment must prove");
    }

    /// THE NEGATIVE POLE (THE MINT — the range gadget's reason to exist): an
    /// UNAFFORDABLE decrement (`old = 30`, `delta = −50`) whose committed result is the
    /// WRAP value `new = old + delta = p − 20 ≈ 2^31`. The exact-delta gate STILL holds
    /// (`30 + (p − 50) ≡ p − 20`) — the pre-range AIR admitted this, MINTING ~2^31 into
    /// the slot. The range gadget makes it UNSAT: `p − 20` has no RESULT_BITS-bit
    /// preimage, so the recompose gate is violated. Genuine circuit non-satisfiability.
    #[test]
    fn underflow_wrap_mint_is_unsat() {
        let config = ir2_leaf_wrap_config();
        let case = FieldDeltaCase::step(30, neg(50));
        // Sanity: the exact-delta equation is STILL satisfied (new == old + delta) —
        // so the ONLY thing that can reject this is the in-AIR range gadget.
        assert_eq!(
            case.new,
            case.old + case.delta,
            "the mint keeps new == old + delta"
        );

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_field_delta_range(&case, &config)
        }));
        match result {
            Err(_) => {}
            Ok(Err(_)) => {}
            Ok(Ok(())) => panic!(
                "an underflow-wrap mint (new == old + delta == p − 20, out of range) proved — \
                 the FieldDelta result range gadget is OPEN"
            ),
        }
    }

    /// THE NEGATIVE POLE (a bare out-of-range result, decoupled from the delta): a
    /// committed `new = 2^RESULT_BITS` has no RESULT_BITS-bit preimage and is UNSAT at
    /// the recompose gate, independent of the transition. (Here the exact-delta gate
    /// also fails; the point is that the recompose gate independently refuses any
    /// out-of-range committed result.)
    #[test]
    fn out_of_range_result_is_unsat() {
        let config = ir2_leaf_wrap_config();
        // An out-of-range result with a matching delta so the transition gate holds
        // (new == 0 + delta) but the range gate bites.
        let big = BabyBear::new(1u32 << RESULT_BITS); // exactly 2^RESULT_BITS: out of range
        let case = FieldDeltaCase {
            old: BabyBear::ZERO,
            delta: big,
            new: big,
        };
        assert!(case.new.as_u32() >= (1u32 << RESULT_BITS));

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_field_delta_range(&case, &config)
        }));
        match result {
            Err(_) => {}
            Ok(Err(_)) => {}
            Ok(Ok(())) => {
                panic!("an out-of-range committed result proved — the range gadget is OPEN")
            }
        }
    }
}
