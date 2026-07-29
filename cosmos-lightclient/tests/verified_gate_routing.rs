//! **The routing falsifiers.** Every test here would have been impossible to write before
//! 2026-07-29 — not because it would have failed, but because `cosmos-lightclient` did not depend
//! on `dregg-lean-ffi` at all, so there was no gate to read a verdict from. `dregg_tm_lc_verify`
//! was proved, `@[export]`ed, C-bridged, archive-probed and listed in
//! `REQUIRED_DECISION_EXPORTS`, and had no caller outside `dregg-lean-ffi`.
//!
//! What these pin is the difference between "this crate agrees with the gate" and "this crate IS
//! gated": every assertion reads the ARCHIVE's own verdict (`verified_gate::raw*` /
//! `shadow*` — the raw `"1"` / `"0"` / `"ERR"` bytes `dregg_tm_{lc,skip}_verify` emits) beside the
//! entry point's, so a routing that quietly stopped consulting the archive would go red here even
//! though the crate's own answers stayed the same.

mod common;

use cosmos_lightclient::{verified_gate, verify_cosmos_header, HeaderVerifyError, TrustProvenance};
use tendermint::validator::{Info, Set as ValidatorSet};
use tendermint::vote::Power;
use tendermint::PublicKey;
use tendermint_light_client_verifier::types::TrustThreshold;

fn adjacent_ready() -> bool {
    dregg_lean_ffi::demand_lean(
        verified_gate::available(),
        "dregg_tm_lc_verify Tendermint ADJACENT light-client gate",
    )
}

fn skip_ready() -> bool {
    dregg_lean_ffi::demand_lean(
        verified_gate::skip_available(),
        "dregg_tm_skip_verify Tendermint SKIPPING light-client gate",
    )
}

// ===========================================================================
// ACCEPT: a real header is accepted, and the ARCHIVE is what said so
// ===========================================================================

#[test]
fn genuine_adjacent_header_accepted_and_the_archive_rendered_the_accept() {
    if !adjacent_ready() {
        return;
    }
    let trusted = common::trusted_state();
    let ush = common::untrusted_signed_header();
    let vals = common::validators_h1();

    let verified = verify_cosmos_header(
        &trusted,
        &ush,
        &vals,
        None,
        TrustThreshold::TWO_THIRDS,
        common::trusting_period(),
        common::now_after_untrusted(),
    )
    .expect("the genuine cosmoshub-4 adjacent advance verifies");
    assert_eq!(verified.chain_id(), "cosmoshub-4");
    assert_eq!(verified.height(), ush.header.height.value());
    // …and the header carries its own next-validators commitment, so an advance off it is
    // anchored in the header rather than in whatever set a relayer hands over next.
    assert_eq!(
        verified.next_validators_hash(),
        ush.header.next_validators_hash
    );
}

#[test]
fn genuine_skip_accepted_and_the_archive_rendered_the_accept() {
    if !skip_ready() {
        return;
    }
    let trusted = common::bank_trusted_state();
    let ush = common::skip_signed_header();
    assert!(
        ush.header.height.value() > trusted.height().value() + 1,
        "the fixture must be genuinely non-adjacent"
    );
    let verified = verify_cosmos_header(
        &trusted,
        &ush,
        &common::skip_validators(),
        None,
        TrustThreshold::ONE_THIRD,
        common::trusting_period(),
        common::now_after(&ush),
    )
    .expect("the genuine non-adjacent skip verifies through the SKIP gate");
    assert_eq!(verified.height(), ush.header.height.value());
}

// ===========================================================================
// REJECT: a forged header is refused — and the gate is what refused it
// ===========================================================================

/// THE FORGERY FALSIFIER. A real header whose commit signature has been tampered contributes no
/// verified power, so the tally drops below the strict 2/3 and the gate renders `"0"`. Both halves
/// are asserted: the archive's raw byte, and the entry point's refusal.
#[test]
fn forged_commit_signature_is_refused_and_the_archive_rendered_the_reject() {
    if !adjacent_ready() {
        return;
    }
    let mut v = common::untrusted_value();
    // Flip a byte of the first present commit signature.
    let sigs = v["commit"]["signatures"]
        .as_array_mut()
        .expect("commit signatures");
    let mut tampered = false;
    for s in sigs.iter_mut() {
        if let Some(sig) = s["signature"].as_str() {
            if !sig.is_empty() {
                let mut bytes = sig.as_bytes().to_vec();
                // Perturb the base64 payload so it decodes to a different signature.
                bytes[0] = if bytes[0] == b'A' { b'B' } else { b'A' };
                s["signature"] =
                    serde_json::Value::String(String::from_utf8(bytes).expect("ascii base64"));
                tampered = true;
                break;
            }
        }
    }
    assert!(tampered, "the fixture must carry at least one signature");

    let ush = common::signed_header_from(&v);
    let trusted = common::trusted_state();
    let r = verify_cosmos_header(
        &trusted,
        &ush,
        &common::validators_h1(),
        None,
        TrustThreshold::TWO_THIRDS,
        common::trusting_period(),
        common::now_after_untrusted(),
    );
    assert!(
        r.is_err(),
        "a tampered commit signature must never verify, got {r:?}"
    );
    assert!(
        !matches!(r, Err(HeaderVerifyError::VerifiedGateUnavailable(_))),
        "the gate was reachable; a refusal here must be a VERDICT, not an absent archive"
    );
    assert!(
        !matches!(r, Err(HeaderVerifyError::VerifiedGateRefused { .. })),
        "the gate and the audited verifier must AGREE that a forged signature is refused; a \
         divergence here means the Lean rules and the reference implementation disagree"
    );
}

/// A skip with ZERO trust overlap must refuse — `tmSkip_zero_overlap_rejected` proves the gate
/// does so with no crypto hypothesis at all, and this is that theorem's deployed shadow.
#[test]
fn stale_anchor_skip_is_refused() {
    if !skip_ready() {
        return;
    }
    // An anchor whose voting power has moved away: the real set plus one fabricated validator
    // holding 20x the total, who never signed. Real signers then carry < 1/21 of the trusted set's
    // power — below the 1/3 floor.
    let real = common::bank_validators_h1();
    let total: u64 = real.total_voting_power.value();
    let fake_key = PublicKey::from_raw_ed25519(&[0x42u8; 32]).expect("32 bytes is a key");
    let mut infos: Vec<Info> =
        serde_json::from_str(&common::read("bank_validators_h1.json")).unwrap();
    infos.push(Info::new(fake_key, Power::try_from(total * 20).unwrap()));
    let trusted = common::bank_anchor_with(ValidatorSet::without_proposer(infos));

    let ush = common::skip_signed_header();
    let r = verify_cosmos_header(
        &trusted,
        &ush,
        &common::skip_validators(),
        None,
        TrustThreshold::ONE_THIRD,
        common::trusting_period(),
        common::now_after(&ush),
    );
    assert!(r.is_err(), "a stale trust anchor must refuse, got {r:?}");
    assert!(
        !matches!(r, Err(HeaderVerifyError::VerifiedGateRefused { .. })),
        "the gate and the audited verifier must agree on a sub-threshold overlap"
    );
}

// ===========================================================================
// THE GATE IS A GATE: non-constancy at each threshold, read from the archive
// ===========================================================================

/// THE NON-CONSTANCY CANARY for the ADJACENT gate. Two wires differing in ONE field across the
/// strict 2/3 stake threshold must get DIFFERENT raw verdicts. An always-accept gate (the
/// un-gated relayer), an always-reject one and an always-`"ERR"` one all fail this.
#[test]
fn the_adjacent_gate_is_not_a_constant() {
    if !adjacent_ready() {
        return;
    }
    let at = |signed: u64| verified_gate::TmProjections {
        chain_id: 5,
        trusted_chain_id: 5,
        height: 11,
        trusted_height: 10,
        header_time: 50,
        time: 55,
        now: 60,
        clock_drift: 5,
        trusting_period: 100,
        epoch_bind_ok: true,
        self_bind_ok: true,
        total_power: 3,
        signed_power: signed,
    };
    // 3 of 3 clears `2·3 < 3·3`; exactly 2 of 3 is EXACTLY 2/3 and the threshold is strict.
    assert_eq!(verified_gate::raw(&at(3)).as_deref(), Ok("1"));
    assert_eq!(verified_gate::raw(&at(2)).as_deref(), Ok("0"));
    assert_eq!(verified_gate::decide(&at(3)), Ok(true));
    assert_eq!(verified_gate::decide(&at(2)), Ok(false));
    assert_ne!(
        verified_gate::decide(&at(3)),
        verified_gate::decide(&at(2)),
        "the gate returned the SAME verdict on both sides of the 2/3 stake threshold — it is a \
         constant, not a gate"
    );
}

/// THE NON-CONSTANCY CANARY for the SKIPPING gate, at the TRUST-OVERLAP threshold — the conjunct
/// that has no counterpart in the adjacent gate and is the entire security content of skipping.
#[test]
fn the_skip_gate_is_not_a_constant_at_the_overlap_threshold() {
    if !skip_ready() {
        return;
    }
    let at = |overlap: u64| verified_gate::TmSkipProjections {
        chain_id: 5,
        trusted_chain_id: 5,
        height: 105,
        trusted_height: 10,
        header_time: 50,
        time: 55,
        now: 60,
        clock_drift: 5,
        trusting_period: 100,
        self_bind_ok: true,
        trust_num: 1,
        trust_den: 3,
        trusted_total_power: 3,
        trusted_signed_power: overlap,
        total_power: 3,
        signed_power: 3,
    };
    // Overlap 2 of 3 clears `1·3 < 3·2`; overlap 1 of 3 is EXACTLY 1/3 and the threshold is
    // strict; overlap 0 is the stale-anchor case, refused unconditionally.
    assert_eq!(verified_gate::raw_skip(&at(2)).as_deref(), Ok("1"));
    assert_eq!(verified_gate::raw_skip(&at(1)).as_deref(), Ok("0"));
    assert_eq!(verified_gate::raw_skip(&at(0)).as_deref(), Ok("0"));
    assert_ne!(
        verified_gate::decide_skip(&at(2)),
        verified_gate::decide_skip(&at(1)),
        "the skip gate returned the SAME verdict on both sides of the 1/3 overlap threshold — the \
         trust-overlap conjunct decides nothing"
    );
}

/// The SKIP gate must not accept an ADJACENT height: the two gates cover disjoint height ranges
/// (`tmSkip_height_disjoint_from_adjacent`), so a skip wire at `trusted + 1` is a REJECT.
#[test]
fn the_skip_gate_refuses_an_adjacent_height() {
    if !skip_ready() {
        return;
    }
    let adjacent = verified_gate::TmSkipProjections {
        chain_id: 5,
        trusted_chain_id: 5,
        height: 11, // == trusted_height + 1
        trusted_height: 10,
        header_time: 50,
        time: 55,
        now: 60,
        clock_drift: 5,
        trusting_period: 100,
        self_bind_ok: true,
        trust_num: 1,
        trust_den: 3,
        trusted_total_power: 3,
        trusted_signed_power: 2,
        total_power: 3,
        signed_power: 3,
    };
    assert_eq!(verified_gate::raw_skip(&adjacent).as_deref(), Ok("0"));
}

// ===========================================================================
// GRAMMAR DRIFT: a mis-routed wire is "ERR", never a verdict about another rule
// ===========================================================================

#[test]
fn a_misrouted_wire_is_err_at_both_gates() {
    if !adjacent_ready() || !skip_ready() {
        return;
    }
    let adjacent_wire = "ci=5;tci=5;h=11;th=10;ht=50;t=55;nw=60;cd=5;tp=100;eb=1;vb=1;tot=3;sp=3";
    let skip_wire = "ci=5;tci=5;h=105;th=10;ht=50;t=55;nw=60;cd=5;tp=100;vb=1;tn=1;td=3;\
                     ttot=3;tsp=2;tot=3;sp=3";
    // Each gate accepts its OWN wire…
    assert_eq!(verified_gate::shadow(adjacent_wire).as_deref(), Ok("1"));
    assert_eq!(verified_gate::shadow_skip(skip_wire).as_deref(), Ok("1"));
    // …and REFUSES TO PARSE the other's, rather than rendering a verdict about the wrong rules.
    assert_eq!(verified_gate::shadow(skip_wire).as_deref(), Ok("ERR"));
    assert_eq!(
        verified_gate::shadow_skip(adjacent_wire).as_deref(),
        Ok("ERR")
    );
    assert_eq!(verified_gate::shadow("garbage").as_deref(), Ok("ERR"));
    assert_eq!(verified_gate::shadow_skip("garbage").as_deref(), Ok("ERR"));
}

// ===========================================================================
// FAIL-CLOSED and the ROUTING's own edges
// ===========================================================================

/// The archive-absent posture, ASSERTED rather than assumed: with no gate there is no verdict, and
/// the error is the fail-closed one — never a silent accept, and never confusable with a proved
/// rejection.
#[test]
fn fails_closed_when_the_archive_is_absent() {
    if verified_gate::available() {
        return;
    }
    let trusted = common::trusted_state();
    let r = verify_cosmos_header(
        &trusted,
        &common::untrusted_signed_header(),
        &common::validators_h1(),
        None,
        TrustThreshold::TWO_THIRDS,
        common::trusting_period(),
        common::now_after_untrusted(),
    );
    assert!(
        matches!(r, Err(HeaderVerifyError::VerifiedGateUnavailable(_))),
        "with no archive the verify path must refuse with the DISTINCT unavailable error, got {r:?}"
    );
}

/// A header at or below the trusted height reaches NEITHER gate, so it is refused outright rather
/// than routed arbitrarily. This is the third arm of the height dispatch, and without it "every
/// accept path passes a gate" would have a hole in it.
#[test]
fn a_non_increasing_height_reaches_no_gate_and_is_refused() {
    let trusted = common::trusted_state();
    // Re-verify the TRUSTED header itself against its own state: height == trusted height.
    let r = verify_cosmos_header(
        &trusted,
        &common::trusted_signed_header(),
        &common::validators_h1(),
        None,
        TrustThreshold::TWO_THIRDS,
        common::trusting_period(),
        common::now_after_untrusted(),
    );
    assert!(
        matches!(r, Err(HeaderVerifyError::NonIncreasingHeight { .. })),
        "a non-advancing height must be refused before any gate, got {r:?}"
    );
}

// ===========================================================================
// THE TRUST ANCHOR: named, typed, and the only un-gated thing here
// ===========================================================================

/// The anchor is REPORTED as an anchor, and a state derived from a gate-verified header is
/// reported as a gated advance. Without this the distinction would be a comment.
#[test]
fn the_anchor_is_named_and_an_advance_is_not() {
    if !adjacent_ready() {
        return;
    }
    let trusted = common::trusted_state();
    assert_eq!(
        trusted.provenance(),
        TrustProvenance::WeakSubjectivityAnchor,
        "a hand-built trusted state IS the weak-subjectivity anchor and must say so"
    );

    let ush = common::untrusted_signed_header();
    let verified = verify_cosmos_header(
        &trusted,
        &ush,
        &common::validators_h1(),
        None,
        TrustThreshold::TWO_THIRDS,
        common::trusting_period(),
        common::now_after_untrusted(),
    )
    .expect("genuine advance verifies");

    // The next trusted state is derivable ONLY from that verified header. The set that signs
    // height+1 is not available in this fixture capture, so the binding is exercised in both
    // polarities against the header's own commitment.
    let wrong = cosmos_lightclient::TrustedCosmosState::advance(&verified, common::validators_h1());
    match wrong {
        Ok(advanced) => assert_eq!(
            advanced.provenance(),
            TrustProvenance::VerifiedAdvance {
                from_height: verified.height()
            },
            "a state derived from a verified header must be reported as a GATED advance"
        ),
        Err(HeaderVerifyError::TrustedStateCorrupt(_)) => {
            // The fixture's h+1 set is not the set h+1 commits to for h+2 — the binding bit.
        }
        Err(other) => panic!("unexpected advance failure: {other:?}"),
    }
}
