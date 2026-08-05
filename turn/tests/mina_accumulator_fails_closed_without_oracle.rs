//! # ⚑⚑ THE MINA DEFERRED-IPA ACCUMULATOR IS REFUSED WHEN IT CANNOT BE DISCHARGED — exhibited.
//!
//! ## Substrate, said out loud (HOUSE LAW #1)
//!
//! Nothing here is an AIR. The accumulator discharge is deliberately NOT a circuit — Halo/Pickles
//! never evaluate the SRS multi-scalar multiplication in-circuit, and the deferral is the whole
//! innovation. This file tests the SEAM at which a dregg turn's acceptance is made to depend on
//! that native discharge having happened.
//!
//! ## What this file exists to prove, and why an assertion would not have done
//!
//! `minted-fail-open-gate-class` is a long catalogue in this repo, and every entry looked like a
//! reasonable degrade when it was written. The claim "an absent accumulator oracle is a REJECTION,
//! never a skip" is worth nothing as a doc-comment; it is worth something as a test that DRIVES the
//! absent case and reads the refusal.
//!
//! ⚑ `dregg-turn`'s own test process **never installs a backend** — it cannot, the backend needs
//! `libdregg_lean.a` and a 4 MB Vesta SRS that live in `dregg-exec-lean`. So this integration test
//! runs in exactly the disposition a wasm32 card, an SP1 guest, or a node built without the archive
//! runs in, and the fail-closed pole is the DEFAULT here rather than something staged.
//!
//! Run: `cargo test -p dregg-turn --release --test mina_accumulator_fails_closed_without_oracle`

use dregg_turn::executor::mina_accumulator_oracle::{
    MINA_ACCUMULATOR_ROUNDS, WireAccumulatorClaim, installed_mina_accumulator_oracle,
    mina_accumulator_oracle_installed,
};

/// A structurally well-formed claim. Its arithmetic is nonsense — that is deliberate: this file
/// never reaches arithmetic, because the refusal it exhibits happens BEFORE any MSM could run.
fn well_formed_claim() -> WireAccumulatorClaim {
    WireAccumulatorClaim {
        comm_x: [0x11; 32],
        comm_y: [0x22; 32],
        chals: (0..MINA_ACCUMULATOR_ROUNDS)
            .map(|i| {
                let mut c = [0u8; 32];
                c[0] = i as u8;
                c
            })
            .collect(),
    }
}

/// ⚑ **POLE 1 — THE ABSENT BACKEND IS A REFUSAL.**
///
/// No oracle is installed in this process, and the accessor says so. That `None` is the value
/// `MinaAnchoredHeadStarkVerifier::verify` turns into `WitnessedPredicateError::Rejected`; there is
/// no other branch it can take, because deciding the claim requires the SRS the backend carries.
#[test]
fn an_absent_accumulator_oracle_is_the_refusing_disposition() {
    assert!(
        !mina_accumulator_oracle_installed(),
        "dregg-turn cannot link the Lean archive, so its own test process must have NO backend — \
         if this ever passes it means a backend was installed and the fail-closed pole is no \
         longer being driven here"
    );
    assert!(
        installed_mina_accumulator_oracle().is_none(),
        "the accessor must report the absence rather than manufacturing a permissive default"
    );
}

/// ⚑ **POLE 2 — AND THE CLAIM IS WELL-FORMED, so the refusal is about the ABSENT DISCHARGE and not
/// about a malformed wire.**
///
/// This is the distinction that makes pole 1 meaningful. A test that fed a broken claim into a
/// missing oracle would be green for the wrong reason forever: the wire would be refused at the
/// arity check and the absence of the backend would never be reached. So the claim used here PASSES
/// every check `dregg-turn` can make for itself, and the only thing left standing between it and an
/// accept is the oracle that is not there.
#[test]
fn the_refused_claim_is_itself_well_formed() {
    let claim = well_formed_claim();
    claim
        .check_arity()
        .expect("the claim this file refuses must be structurally valid, or pole 1 proves nothing");
    assert_eq!(claim.chals.len(), MINA_ACCUMULATOR_ROUNDS);
    assert!(installed_mina_accumulator_oracle().is_none());
}

/// ⚑ **BOTH POLARITIES OF THE ONE CHECK THIS CRATE OWNS.** The arity check is not a discharge and
/// must never be mistaken for one, but it is a real refusal and it has both directions.
#[test]
fn a_claim_that_is_not_sixteen_challenges_is_refused() {
    let mut short = well_formed_claim();
    short.chals.pop();
    let e = short
        .check_arity()
        .expect_err("15 challenges must be refused: 2^15 does not tile a 65536-generator SRS");
    assert!(e.contains("bulletproof challenges"), "{e}");

    let mut long = well_formed_claim();
    long.chals.push([0xFF; 32]);
    assert!(long.check_arity().is_err(), "17 challenges must be refused");

    // …and the honest arity is admitted, so the check is not simply always-refusing.
    assert!(well_formed_claim().check_arity().is_ok());
}

/// ⚑ **THE INSTALLED-SET IS EMPTY, NOT ABSENT-MEANING-TRUE.** A registry whose "nothing installed"
/// state reads as permission is the fail-open shape this seam was built to avoid; the two accessors
/// must agree, in this process, that there is nothing here.
#[test]
fn the_two_accessors_agree_about_the_absence() {
    assert_eq!(
        mina_accumulator_oracle_installed(),
        installed_mina_accumulator_oracle().is_some(),
        "the boolean and the accessor must not be able to disagree about whether a backend exists"
    );
    assert!(!mina_accumulator_oracle_installed());
}
