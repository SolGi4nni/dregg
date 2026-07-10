//! # R3 on a REAL driven grain session — the adapter end-to-end.
//!
//! Drives a tiny grain session through the genuine R2 weld ([`ToolGatewayMinter`] — each
//! `mint_turn` is a committed `ToolGateway::invoke` executor turn), FINALIZES it into a
//! `Vec<FinalizedTurn>` via [`grain_turn::finalize_session`] (the rotated wide-anchored
//! EffectVM legs, minted from the REAL captured turn data), and hands them to
//! [`grain_verify::r3_verify`] — the Lean-proven R3 decision. This is R3 running on a real
//! driven session, not a hand-minted fixture.
//!
//! SLOW: every leg is a full IR-v2 batch prove and the fold is the recursive step
//! (~minutes), so `#[ignore]`'d — run with
//! `cargo test -p grain-turn --features prover --test r3_grain_adapter -- --ignored --nocapture`.
//!
//! Scope note (see `finalize::finalize_session`'s RESIDUAL GAP doc): a grain turn writes
//! ≥3 distinct field slots in one executor turn that ticks the cell nonce ONCE, while the
//! rotated EffectVM leg ticks it once PER field-write — so the head this fold binds is the
//! EffectVM-model head, NOT the executor's on-ledger grain-cell head. A single-turn session
//! folds internally-consistently and is anchored at that model head here.

#![cfg(feature = "prover")]

use dregg_agent::agent::GrainTurnMinter;
use grain_turn::{ToolGatewayMinter, finalize_session};
use grain_verify::{R3Error, r3_verify};

/// The wide (8-felt, ~124-bit) head-lane commit of the last leg in the chain — the
/// fold's committed head, exactly the anchor the honest case pins (mirrors the R3
/// whole-history test's `final_root.as_u32()`).
fn chain_head(legs: &[dregg_circuit_prove::ivc_turn_chain::FinalizedTurn]) -> u32 {
    legs.last()
        .expect("non-empty chain")
        .participant
        .rotated
        .wide_new_root8()
        .expect("deployed grain leg is wide-anchored")[0]
        .as_u32()
}

#[test]
#[ignore = "SLOW: per-field-write IR-v2 batch proves + a recursive fold (~minutes); run with --ignored"]
fn r3_verifies_a_real_driven_grain_session() {
    // The DECISION is the Lean-proven verifier; without the extracted core linked there is
    // NO Rust fallback (by design). Report and stop rather than assert a decision we don't
    // have — mirrors grain-verify's own R3 test.
    if !dregg_lean_ffi::grain_r3_verify_core_available() {
        eprintln!(
            "R3: the Lean-proven core `dregg_grain_r3_verify` is not linked — rebuild \
             dregg-lean-ffi to splice Dregg2.Grain.R3Verify, then re-run. (No Rust fallback.)"
        );
        return;
    }

    // ── DRIVE a tiny grain session (ONE admitted action → ONE committed executor turn). ──
    // A single grain turn's legs form a chain that closes internally at the EffectVM head
    // (the multi-turn cross-continuity is the named residual gap, so we drive one turn).
    let mut minter = ToolGatewayMinter::open("grain-r3-adapter", 8).expect("open grain minter");
    let cell_root = [9u8; 32];
    let t_mint = std::time::Instant::now();
    minter
        .mint_turn("search", 1, 1, cell_root)
        .expect("the grain turn commits (admitted, in-rate)");
    let mint_elapsed = t_mint.elapsed();
    assert_eq!(
        minter.records().len(),
        1,
        "one committed grain turn captured"
    );

    // ── FINALIZE: mint the rotated wide-anchored EffectVM legs from the REAL turn data. ──
    let t_fin = std::time::Instant::now();
    let legs = finalize_session(minter.records()).expect("real grain turn finalizes to legs");
    let finalize_elapsed = t_fin.elapsed();
    assert!(
        legs.len() >= 3,
        "a grain turn writes ≥3 distinct field slots (calls_made/consumed/heap_root/action) \
         → a cohort-run chain of ≥3 rotated legs; got {}",
        legs.len()
    );
    let head = chain_head(&legs);

    // (i) HONEST — the real driven session, anchored at its genuine folded head → "1".
    let t_fold = std::time::Instant::now();
    let v = r3_verify(&legs, head).expect("a real driven grain session R3-verifies");
    let fold_elapsed = t_fold.elapsed();
    assert_eq!(v.num_turns, legs.len());
    assert_eq!(v.anchored_head, head);
    assert_eq!(
        v.aggregate_head, head,
        "the aggregate's committed head IS the genuine fold head (head-binding holds)"
    );

    // (ii) WRONG-HEAD — the SAME chain anchored at head+1 → the Lean anti-ghost tooth rejects.
    match r3_verify(&legs, head.wrapping_add(1)) {
        Err(R3Error::Rejected {
            aggregate_verified,
            anchored_head,
            ..
        }) => {
            assert!(
                aggregate_verified,
                "the aggregate itself DID verify — only the anchor is foreign"
            );
            assert_eq!(anchored_head, head.wrapping_add(1));
        }
        other => panic!("a foreign anchor must be Lean-REJECTED; got {other:?}"),
    }

    // (iii) TAMPER — forge the last leg's claimed post-state PI → the fold does not verify.
    let forged = forge_last_post_state(minter.records());
    match r3_verify(&forged, head) {
        Err(R3Error::Rejected {
            aggregate_verified, ..
        }) => assert!(
            !aggregate_verified,
            "a forged post-state's aggregate must NOT verify — verified-status is false"
        ),
        other => panic!("a tampered history must be R3-REJECTED; got {other:?}"),
    }

    eprintln!(
        "R3 on a REAL grain session: mint={mint_elapsed:?}, finalize({} legs)={finalize_elapsed:?}, \
         honest fold={fold_elapsed:?} — the ACCEPT decision rendered by the Lean-proven r3VerifyCore.",
        legs.len()
    );
}

/// Re-finalize the session, then forge the LAST leg's claimed post-state PI (the 8-felt
/// wide AFTER-commit): the execution witness stays honest, only the CLAIM is forged, so the
/// leaf re-verify is UNSAT and the fold does not verify. Mirrors the whole-history test's
/// `forge_last_post_state`.
fn forge_last_post_state(
    records: &[grain_turn::GrainTurnRecord],
) -> Vec<dregg_circuit_prove::ivc_turn_chain::FinalizedTurn> {
    use dregg_circuit::field::BabyBear;
    use dregg_circuit_prove::ivc_turn_chain::FinalizedTurn;
    use dregg_circuit_prove::joint_turn_aggregation::{
        DescriptorParticipant, RotatedParticipantLeg,
    };

    let mut legs = finalize_session(records).expect("finalize for the tamper case");
    let last = legs.len() - 1;
    let DescriptorParticipant { rotated } = legs.remove(last).participant;
    let RotatedParticipantLeg {
        proof,
        descriptor,
        mut public_inputs,
        carrier_witness,
    } = rotated;
    let pi_wide_new = public_inputs.len() - 8;
    public_inputs[pi_wide_new] = public_inputs[pi_wide_new] + BabyBear::ONE;
    legs.push(FinalizedTurn::new(DescriptorParticipant::rotated(
        RotatedParticipantLeg {
            proof,
            descriptor,
            public_inputs,
            carrier_witness,
        },
    )));
    legs
}
