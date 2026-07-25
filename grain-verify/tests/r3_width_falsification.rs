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

/// Ask the DEPLOYED Lean decision.
fn lean_decides(wire: &str) -> bool {
    match dregg_lean_ffi::shadow_grain_r3_verify(wire) {
        Ok(out) => out == "1",
        Err(e) => panic!("the Lean-proven R3 core is present but did not answer: {e}"),
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
        lean_decides(&wire),
        "honest facts must ACCEPT — if this REJECTS, the linked archive still carries the \
         PRE-REPAIR narrow r3VerifyCore (it fails closed on the widened wire); rebuild \
         dregg-lean-ffi to splice the current Dregg2.Grain.R3Verify"
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
        assert!(
            !lean_decides(&wire),
            "a fabricated aggregate head differing only at lane {lane} must be REFUSED \
             (wound #22, the ~2^31 offline grind)"
        );
    }

    // And the honest head still accepts, so the tooth discriminates rather than just
    // rejecting everything (the restore half of the falsification).
    let wire = r3_wire_for_test(true, &vk, &vk, &anchored, &anchored);
    assert!(
        lean_decides(&wire),
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
        assert!(
            !lean_decides(&wire),
            "a presented root fingerprint differing at byte {i} from the caller's anchor \
             must be REFUSED (wound #22, the self-anchored VK)"
        );

        // THE ANTI-LAUNDER, on the wire: the SAME foreign fingerprint, self-anchored
        // (presented == expected, as the pre-fix seam had it), ACCEPTS. So widening the
        // felt alone — leaving this shape in place — would have been a green that means
        // nothing. Machine-checked over all inputs as
        // `Dregg2.Grain.R3Verify.neither_half_alone_suffices`.
        let laundered = r3_wire_for_test(true, &presented, &presented, &head, &head);
        assert!(
            lean_decides(&laundered),
            "the self-anchored shape accepts a foreign fingerprint — that is the wound, and \
             it is why the repair could not stop at the felt width"
        );
    }

    // Restore: the caller's own anchor accepts.
    let wire = r3_wire_for_test(true, &expected, &expected, &head, &head);
    assert!(
        lean_decides(&wire),
        "the caller's own anchor must ACCEPT — the VK tooth must discriminate"
    );
}

/// **FAIL-CLOSED.** A non-accepting verified-status rejects regardless (the proven
/// `r3_unverified_rejected`, which `r3_verify`'s fold-failure path rests on); the PRE-REPAIR
/// three-int wire is refused, so a stale caller cannot re-open the ~31-bit binding by
/// accident; and malformed input is refused.
#[test]
fn fail_closed_on_bad_status_stale_wire_and_garbage() {
    require_core();
    let head = honest_head();
    let vk = honest_vk();

    assert!(
        !lean_decides(&r3_wire_for_test(false, &vk, &vk, &head, &head)),
        "a non-verifying aggregate must REJECT whatever the VKs and heads say"
    );
    assert!(
        !lean_decides("1 42 42"),
        "the PRE-REPAIR three-int wire must fail CLOSED — a stale caller must never be able \
         to re-open the ~31-bit binding"
    );
    assert!(!lean_decides("garbage"));
    assert!(!lean_decides(""), "an empty wire must fail closed");
    // A well-formed wire with one extra non-integer token: the Lean parse is strict
    // (`mapM`, not `filterMap`), so a malformed token can never be silently dropped and
    // shift the lanes into a passing alignment.
    let mut w = r3_wire_for_test(true, &vk, &vk, &head, &head);
    w.push_str(" x");
    assert!(!lean_decides(&w));
}
