//! # Wound #22 falsification — the R3 anti-ghost tooth binds ~124 bits and a CALLER-HELD VK.
//!
//! `docs/WOUND-felt-width-boundaries-2026-07-19.md` #22 catalogued the R3 accept decision as
//! having TWO independently fatal conjuncts:
//!
//!   1. the aggregate↔anchor binding ran through ONE felt (`proof.final_root[0].as_u32()`,
//!      ~31 bits), so a lying host could grind ~2^31 offline for a fabricated final anchor
//!      whose LANE 0 matched the renter's honest head and re-point it at that anchor; and
//!   2. the other conjunct was SELF-ANCHORED — `verify_whole_chain_proof_bytes(&bytes,
//!      &proof.root_vk_fingerprint())` verified the proof against the fingerprint the proof
//!      ITSELF supplied, establishing nothing about which VK it should carry.
//!
//! This test FALSIFIES both, against the DEPLOYED decision object — the extracted Lean
//! `Dregg2.Grain.R3Verify.r3VerifyCore` running as native code through
//! `dregg_lean_ffi::shadow_grain_r3_verify`. It drives the SAME wire
//! `grain_verify::r3::r3_verify` marshals (via the shared `r3_wire_for_test`, not a
//! re-implementation), so what is under test is the real seam encoding, not a mirror.
//!
//! **Why this test exists next to `r3_whole_history.rs`.** That one is the end-to-end
//! article and is `#[ignore]`d behind five real minutes-long recursive folds. This one pays
//! nothing: the forged FACTS are the point, and the fold that would produce them is not.
//! It is therefore RUNNABLE in CI, and it fails loudly if the linked archive still carries
//! the pre-repair narrow core (the positive pole below only accepts under the widened one).

use grain_verify::r3::{R3_WIRE_LEN, r3_wire_for_test};

use dregg_circuit_prove::ivc_turn_chain::{RecursionVk, SEG_ANCHOR_WIDTH};

/// An honest 8-felt (~124-bit) anchor.
fn honest_head() -> [u32; SEG_ANCHOR_WIDTH] {
    [7, 101, 102, 103, 104, 105, 106, 107]
}

/// An honest-setup trust anchor.
fn honest_vk() -> RecursionVk {
    let mut b = [0u8; 32];
    for (i, x) in b.iter_mut().enumerate() {
        *x = (i as u8).wrapping_mul(7).wrapping_add(3);
    }
    RecursionVk(b)
}

/// The DEPLOYED Lean decision's THREE answers.
///
/// ⚑ WHY THIS IS NOT A `bool`, AND WHAT WAS WRONG WITH IT WHEN IT WAS. Until 2026-08-07
/// this helper was `out == "1"`, so every `!lean_decides(…)` below was satisfied by ANY
/// non-`"1"` reply — including the `"0"` the Lean side rendered for a wire it could not
/// PARSE. Forty-four negative assertions therefore could not tell "the ~2^31 lane-0 grind
/// was refused by `r3_wide_head_mismatch_rejected`" from "`r3_wire` and `parseWireE`
/// disagree and nothing was decided". The falsifications did not falsify; they only
/// established that the reply was not `"1"`, which a broken wire gives for free.
///
/// The Lean side now renders `"2 <fault>"` for an unreadable wire — a code no verdict can
/// produce (`Dregg2.Grain.R3Verify.renderR3_ne_malformed`, over all wires and all verdicts)
/// — so each pole below asserts the answer it actually means.
#[derive(Debug, PartialEq, Eq)]
enum LeanR3 {
    Accept,
    /// The Lean-proven core RAN and REFUSED. This is what a falsifier must observe.
    Reject,
    /// The Lean side could not READ the wire, so nothing was decided. In this file that is
    /// ALWAYS a test bug or a stale archive — never a falsification result.
    Malformed(String),
}

/// Ask the DEPLOYED Lean decision.
fn lean_answer(wire: &str) -> LeanR3 {
    match dregg_lean_ffi::shadow_grain_r3_verify(wire) {
        Ok(out) => match out.split_whitespace().next() {
            Some("1") => LeanR3::Accept,
            Some("0") => LeanR3::Reject,
            _ => LeanR3::Malformed(out),
        },
        Err(e) => panic!("the Lean-proven R3 core is present but did not answer: {e}"),
    }
}

/// The positive pole, unchanged in meaning.
fn lean_accepts(wire: &str) -> bool {
    lean_answer(wire) == LeanR3::Accept
}

/// ⚑ THE NEGATIVE POLE, AND IT IS NO LONGER FREE. Asserts the Lean core RAN and returned
/// the whole-history REFUSAL — a malformed wire now FAILS this, loudly, instead of passing
/// it silently.
fn assert_lean_refuses(wire: &str, what: &str) {
    match lean_answer(wire) {
        LeanR3::Reject => {}
        LeanR3::Accept => panic!("{what}: the Lean-proven core ACCEPTED — the tooth is gone"),
        LeanR3::Malformed(out) => panic!(
            "{what}: VACUOUS — the Lean side answered {out:?}, i.e. it could not READ the wire \
             this test sent, so it never rendered a verdict and this falsification falsified \
             NOTHING. Either the marshalling in `r3_wire_for_test` and \
             `Dregg2.Grain.R3Verify.parseWireE` have drifted apart, or the linked \
             libdregg_lean.a is stale. Before 2026-08-07 this state PASSED."
        ),
    }
}

/// **This FAILS rather than skips when the verified core is absent — deliberately, and unlike
/// the end-to-end `r3_whole_history.rs`, which report-and-stops.**
///
/// A falsification that cannot run has falsified NOTHING. Report-and-stop is right for a
/// demo (it says "the article is not linked here"), but in a falsification test it turns an
/// absent or stale archive into a GREEN — the exact "green that means nothing" shape this
/// whole repair exists to remove. Measured, not hypothetical: on a remote build host whose
/// `dregg-lean-ffi` splice omitted `dregg_grain_r3_verify`, an earlier report-and-stop
/// version of this file reported `4 passed` while executing none of the assertions below.
/// So: absent core ⇒ RED, meaning "blocked", never "verified".
fn require_core() {
    assert!(
        dregg_lean_ffi::grain_r3_verify_core_available(),
        "REFUSING TO PASS VACUOUSLY: the Lean-proven core `dregg_grain_r3_verify` is not in \
         the linked archive, so none of the wound-#22 falsifications below can run. Rebuild \
         dregg-lean-ffi so its splice picks up Dregg2.Grain.R3Verify (build the Lean module \
         first so its `:c` facet is emitted), then re-run. A skipped falsification is not a \
         passed one."
    );
}

/// **THE POSITIVE POLE — and the archive-freshness canary.** Honest facts ACCEPT. This also
/// proves the linked archive carries the WIDENED core: the pre-repair export read a
/// three-int wire and fails closed on this `R3_WIRE_LEN`-int one, so a stale archive turns
/// this assertion RED rather than letting the negative poles pass vacuously.
#[test]
fn honest_facts_accept_and_the_widened_core_is_linked() {
    require_core();
    let head = honest_head();
    let vk = honest_vk();
    let wire = r3_wire_for_test(true, &vk, &vk, &head, &head);
    assert_eq!(
        wire.split(' ').count(),
        R3_WIRE_LEN,
        "the seam must marshal exactly r3WireLen ints"
    );
    assert!(
        lean_accepts(&wire),
        "honest facts must ACCEPT — if this answers anything else, the linked archive still \
         carries a PRE-REPAIR r3VerifyCore (it fails closed on the widened wire); rebuild \
         dregg-lean-ffi to splice the current Dregg2.Grain.R3Verify. Answer was: {:?}",
        lean_answer(&wire)
    );
}

/// **FALSIFIER (1) — THE WIDTH.** A forged aggregate head that is byte-identical in LANE 0
/// and differs ONLY at a higher lane is REFUSED. This is precisely the ~2^31 grind product
/// the wound described, and precisely the perturbation the pre-fix seam could not see: every
/// bit it compared is equal.
#[test]
fn a_forged_head_differing_only_outside_lane_0_is_refused() {
    require_core();
    let anchored = honest_head();
    let vk = honest_vk();

    // Perturb each lane 1..8 in turn — every one must be caught.
    for lane in 1..SEG_ANCHOR_WIDTH {
        let mut forged = anchored;
        forged[lane] = forged[lane].wrapping_add(1);
        assert_eq!(
            forged[0], anchored[0],
            "the forgery must be INDISTINGUISHABLE to the pre-fix lane-0 seam"
        );
        assert_ne!(
            forged, anchored,
            "…while being a genuinely different anchor"
        );
        let wire = r3_wire_for_test(true, &vk, &vk, &forged, &anchored);
        assert_lean_refuses(
            &wire,
            &format!(
                "a fabricated aggregate head differing only at lane {lane} must be REFUSED \
                 (wound #22, the ~2^31 offline grind)"
            ),
        );
    }

    // And the honest head still accepts, so the tooth discriminates rather than just
    // rejecting everything (the restore half of the falsification).
    let wire = r3_wire_for_test(true, &vk, &vk, &anchored, &anchored);
    assert!(
        lean_accepts(&wire),
        "the genuine head must still ACCEPT — the width tooth must discriminate, not \
         blanket-reject"
    );
}

/// **FALSIFIER (2) — THE SELF-ANCHORING.** A presented fingerprint that is not the caller's
/// out-of-band anchor is REFUSED, byte by byte. Under the pre-fix seam the "expected" VK
/// *was* the presented one, so this input was indistinguishable from the honest one: the
/// conjunct was vacuous (`Dregg2.Grain.R3Verify.selfAnchoredVk_vacuous`).
#[test]
fn a_presented_vk_that_is_not_the_callers_anchor_is_refused() {
    require_core();
    let head = honest_head();
    let expected = honest_vk();

    // Every single byte of the fingerprint is load-bearing.
    for i in 0..32 {
        let mut b = expected.0;
        b[i] ^= 0x01;
        let presented = RecursionVk(b);
        assert_ne!(presented, expected);
        let wire = r3_wire_for_test(true, &presented, &expected, &head, &head);
        assert_lean_refuses(
            &wire,
            &format!(
                "a presented root fingerprint differing at byte {i} from the caller's anchor \
                 must be REFUSED (wound #22, the self-anchored VK)"
            ),
        );

        // THE ANTI-LAUNDER, on the wire: the SAME foreign fingerprint, self-anchored
        // (presented == expected, as the pre-fix seam had it), ACCEPTS. So widening the
        // felt alone — leaving this shape in place — would have been a green that means
        // nothing. Machine-checked over all inputs as
        // `Dregg2.Grain.R3Verify.neither_half_alone_suffices`.
        let laundered = r3_wire_for_test(true, &presented, &presented, &head, &head);
        assert!(
            lean_accepts(&laundered),
            "the self-anchored shape accepts a foreign fingerprint — that is the wound, and \
             it is why the repair could not stop at the felt width"
        );
    }

    // Restore: the caller's own anchor accepts.
    let wire = r3_wire_for_test(true, &expected, &expected, &head, &head);
    assert!(
        lean_accepts(&wire),
        "the caller's own anchor must ACCEPT — the VK tooth must discriminate"
    );
}

/// **FAIL-CLOSED — AND THE TWO KINDS OF REFUSAL ARE NOW DIFFERENT ANSWERS.**
///
/// ⚑ THIS TEST IS WHERE THE COLLISION LIVED. It asserted the SAME thing (`!lean_decides`) of
/// a non-verifying aggregate — a real R3 REFUSAL, resting on the proven
/// `r3_unverified_rejected` that `r3_verify`'s fold-failure path depends on — and of four
/// wires the Lean side could not parse. All five produced `"0"`, so the file could not tell
/// its own load-bearing negative from a grammar disagreement, and a drifted `r3_wire` would
/// have kept it green.
///
/// Now the verdict wires assert `Reject` and the unreadable wires assert `Malformed`, so a
/// drift in either direction is RED.
#[test]
fn a_non_verifying_aggregate_is_refused_by_the_verdict_not_by_the_parser() {
    require_core();
    let head = honest_head();
    let vk = honest_vk();

    assert_lean_refuses(
        &r3_wire_for_test(false, &vk, &vk, &head, &head),
        "a non-verifying aggregate must REJECT whatever the VKs and heads say",
    );
}

/// **THE OTHER POLE — an unreadable wire says SO, in its own code.** Each of these must come
/// back `"2 <fault>"`, never `"0"`: a stale caller's pre-repair three-int wire still fails
/// closed (it cannot re-open the ~31-bit binding), and it is now also legible AS a stale
/// caller rather than as a lying host.
#[test]
fn an_unreadable_wire_is_malformed_not_a_whole_history_refusal() {
    require_core();
    let head = honest_head();
    let vk = honest_vk();

    let mut trailing_junk = r3_wire_for_test(true, &vk, &vk, &head, &head);
    trailing_junk.push_str(" x");
    let mut trailing_int = r3_wire_for_test(true, &vk, &vk, &head, &head);
    trailing_int.push_str(" 9");

    for (wire, why) in [
        (
            "1 42 42".to_string(),
            "the PRE-REPAIR three-int wire — a stale caller, not a lying host",
        ),
        ("garbage".to_string(), "wholly unreadable input"),
        (String::new(), "the empty wire"),
        (
            trailing_junk,
            "a well-formed wire plus a non-integer token (the strict `mapM` catches it before \
             the length gate, so a bad token can never be dropped and shift the lanes)",
        ),
        (trailing_int, "a well-formed wire plus one extra integer"),
    ] {
        match lean_answer(&wire) {
            LeanR3::Malformed(out) => {
                assert!(
                    out.starts_with('2'),
                    "{why}: expected the malformed code, got {out:?}"
                );
            }
            LeanR3::Reject => panic!(
                "{why}: the Lean side answered \"0\" — the WHOLE-HISTORY REFUSAL — for a wire it \
                 cannot read. That is the exact collision this repair removed; either the Lean \
                 archive is pre-2026-08-07 or `parseWireE` has been widened to accept this."
            ),
            LeanR3::Accept => panic!("{why}: an unreadable wire must never ACCEPT"),
        }
    }
}
