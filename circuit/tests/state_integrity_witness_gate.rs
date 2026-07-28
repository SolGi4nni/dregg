//! The witness-generation gate on a `CellState` — and the two arms of it that cannot fire.
//!
//! `verify_state_integrity` is the EffectVM's only check that a `CellState`'s carried
//! `state_commitment` still matches the fields it claims to commit. Measured 2026-07-27 it had
//! **zero call sites in the whole tree, tests included**: defined in `effect_vm::verify`,
//! re-exported from `effect_vm` (`mod.rs:266`), and invoked by nothing. Its sibling in the same
//! file, `verify_balance_limb_pis`, got a dedicated gate test (`balance_limb_pi_gate.rs`); the
//! commit that wired that one up put this one in `baseline/production-callers.tsv` instead.
//!
//! ## Why the commitment half is load-bearing, and not free
//!
//! `CellState`'s fields are `pub` and `state_commitment` is a CARRIED felt, not a derived one.
//! The two then go to different places inside one call:
//!
//! * `CellState::to_trace_cols` copies the carried felt VERBATIM into row 0's
//!   `state_before[state::STATE_COMMIT]`;
//! * `PI[OLD_COMMIT_BASE..]` is recomputed FRESH from the fields
//!   (`generate_effect_vm_trace_ext` → `compute_commitment_8`).
//!
//! So a state whose fields were mutated without `refresh_commitment()` yields a trace whose
//! committed-state column disagrees with the public input the descriptor recomputes. That is not
//! hypothetical: `braid-hook::fold::mint_entity_custom_leg` carries a hand-written
//! `st.refresh_commitment()` with a comment saying exactly this ("or the trace's committed-state
//! column is stale vs the hash the descriptor recomputes"), and so does every other
//! direct-mutation site in the tree — `grain-turn::finalize`, `sdk::full_turn_proof` (twice),
//! `turn::executor::proof_verify`, `dregg-multiway-tug::fold`. Six hand-written repairs of one
//! invariant, and nothing checking it.
//!
//! The gate now runs in `generate_effect_vm_trace_ext`, which is the single funnel BOTH entry
//! points pass through: the plain `generate_effect_vm_trace` wrapper, and the deployed rotated
//! leg (`trace_rotated.rs:595`).
//!
//! ## ⚠ The range half: two arms of three cannot fire
//!
//! `verify_state_integrity` also calls `verify_balance_limb_ranges`, whose first two arms this
//! file proves UNREACHABLE from any `CellState`, because the encoders saturate before the check
//! sees them:
//!
//! * `balance_lo >= 2^30` — `split_u64` computes `val & 0x3FFF_FFFF`, so `lo < 2^30` always;
//! * `balance_hi >= 2^31` — `BabyBear::new(v)` is `v % BABYBEAR_P`, so `hi.0 < p < 2^31` always.
//!
//! Those two were the "EXECUTOR-SIDE RANGE VALIDATION (o1vm audit mitigations)" `assert!`s
//! hand-inlined in `generate_effect_vm_trace_ext`; they were checking conditions no `u64` balance
//! can produce, and the call to `verify_state_integrity` replaced them. The THIRD arm — limb
//! reconstruction — is genuinely reachable, and `refuses_a_balance_that_does_not_survive_its_limbs`
//! drives it. The verifier-side range precondition on the leg that ships is a different function
//! reading PI offsets (`verify_balance_limb_pis`), and it is separately gated.

use dregg_circuit::effect_vm::{
    CellState, Effect, STATE_BEFORE_BASE, generate_effect_vm_trace, state,
};
use dregg_circuit::field::BabyBear;
use std::panic::{AssertUnwindSafe, catch_unwind};

/// A state built the way a production producer builds one: construct, populate the field octet,
/// then `refresh_commitment()`. This is `braid-hook::mint_entity_custom_leg`'s exact shape.
fn honest_state() -> CellState {
    let mut st = CellState::new(1_000, 5);
    for (i, f) in st.fields.iter_mut().enumerate() {
        *f = BabyBear::new(100 + i as u32);
    }
    st.refresh_commitment();
    st
}

fn one_transfer() -> Vec<Effect> {
    vec![Effect::Transfer {
        amount: 300,
        direction: 1,
    }]
}

/// Run the PRODUCTION entry point and report whether it refused. Nothing here calls
/// `verify_state_integrity` directly — a test that reaches a check by hand is not evidence the
/// check runs.
fn generate_via_production_entry(
    st: &CellState,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let out = catch_unwind(AssertUnwindSafe(|| {
        generate_effect_vm_trace(st, &one_transfer())
    }));
    std::panic::set_hook(prev);
    out.map_err(|e| {
        e.downcast_ref::<String>()
            .cloned()
            .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
            .unwrap_or_else(|| "<non-string panic>".to_string())
    })
}

/// POLE 1 — ADMIT. An honest state generates a trace, and the property the gate protects HOLDS:
/// row 0's carried `state_commit` column is the commitment its own fields hash to, which is the
/// same value the fresh `compute_commitment` recomputation produces for `PI[OLD_COMMIT]`.
#[test]
fn admits_an_honest_state_and_the_carried_commit_matches_the_recomputed_one() {
    let st = honest_state();
    let (trace, _pis) = generate_via_production_entry(&st).expect("an honest state must generate");
    assert!(
        !trace.is_empty(),
        "the production entry produced no trace at all"
    );

    let carried = trace[0][STATE_BEFORE_BASE + state::STATE_COMMIT];
    let recomputed = CellState::compute_commitment(
        st.balance,
        st.nonce,
        &st.fields,
        st.capability_root,
        st.record_digest,
    );
    assert_eq!(
        carried, recomputed,
        "row 0's committed-state column must be the commitment the fields hash to — this is the \
         equality PI[OLD_COMMIT] is independently recomputed from"
    );
}

/// POLE 2 — REFUSE, on the real footgun. The SAME state, fields mutated without
/// `refresh_commitment()`: the exact slip `braid-hook` repairs by hand. The production entry must
/// refuse rather than emit a trace whose committed-state column and public input disagree.
#[test]
fn refuses_a_state_whose_carried_commitment_went_stale() {
    let mut st = honest_state();
    st.fields[3] = BabyBear::new(424_242); // …and NO refresh_commitment().

    let err = generate_via_production_entry(&st)
        .expect_err("a stale carried commitment must be refused at witness generation");
    assert!(
        err.contains("state_commitment mismatch"),
        "refusal must name the stale commitment, got: {err}"
    );

    // And the divergence it prevents is real: the carried felt is NOT what the fields hash to.
    let recomputed = CellState::compute_commitment(
        st.balance,
        st.nonce,
        &st.fields,
        st.capability_root,
        st.record_digest,
    );
    assert_ne!(
        st.state_commitment, recomputed,
        "the refused input must actually be inconsistent — otherwise this test proves nothing"
    );
}

/// POLE 3 — REFUSE, the one range arm that can fire. A balance at or above `p · 2^30` does not
/// survive its own limb encoding: `BabyBear::new(val >> 30)` reduces mod p, so joining the limbs
/// back does not reproduce the balance. The trace would then commit to a DIFFERENT balance than
/// the one the caller handed in.
#[test]
fn refuses_a_balance_that_does_not_survive_its_limbs() {
    let mut st = CellState::new(u64::MAX, 5);
    st.refresh_commitment(); // honest in every other respect: only the balance is out of domain.

    let err = generate_via_production_entry(&st)
        .expect_err("a balance that does not round-trip through its limbs must be refused");
    assert!(
        err.contains("balance limb reconstruction mismatch"),
        "refusal must name the limb reconstruction, got: {err}"
    );
}

/// The two arms that CANNOT fire, asserted rather than assumed. A guard whose arms are
/// unreachable reads in review exactly like one that is checking something.
#[test]
fn the_two_saturating_range_arms_are_structurally_unreachable() {
    use dregg_circuit::field::BABYBEAR_P;

    // `split_u64` masks the low limb to 30 bits, so the `lo >= 2^30` arm has no input.
    for probe in [
        u64::MAX,
        (1u64 << 30) - 1,
        1u64 << 30,
        0xDEAD_BEEF_CAFE_BABE,
    ] {
        let lo = (probe & 0x3FFF_FFFF) as u32;
        assert!(lo < (1 << 30), "split_u64's low limb escaped 30 bits: {lo}");
    }

    // `BabyBear::new` reduces mod p, so the `hi >= 2^31` arm has no input either.
    assert!(
        BABYBEAR_P < (1u32 << 31),
        "the field modulus no longer bounds the hi arm"
    );
    for probe in [u32::MAX, 1u32 << 31, BABYBEAR_P, BABYBEAR_P - 1] {
        assert!(
            BabyBear::new(probe).0 < (1 << 31),
            "BabyBear::new stopped reducing below 2^31"
        );
    }
}
