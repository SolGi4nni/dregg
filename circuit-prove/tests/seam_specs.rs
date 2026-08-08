//! ⚑ **THE SEAM DRIFT GATE** — pins the emitted `circuit/descriptors/seams/*.json` to the fold
//! sites that read them, and the port census to the seams that cover it.
//!
//! Three parties must agree, and each pair is checked here:
//!
//! 1. **The emitted seam ↔ the deployed claim layouts.** The pin lists must be exactly the index
//!    arithmetic the fold functions USED to author (`ENDO_PI_XI`, `CONJ_PI_XI`,
//!    `CHAIN_OUT_LANE0`, `CLAIM_VPRIME`, `V_PRIME_LIMBS`, `STATE_WIDTH`) — that arithmetic now
//!    lives HERE, as the gate, and nowhere in a fold.
//! 2. **The emitted seam ↔ the served descriptors.** Each end's fingerprint lanes must equal the
//!    lanes RECOMPUTED from the descriptor the fold actually loads (`SeamEnd::require_matches` —
//!    the same refusal the fold performs at configuration time; here it runs in the fast suite).
//! 3. **The port census ↔ the seams.** Every port `ports.json` declares must be covered by one of
//!    the emitted seams — the artifact-side twin of the Lean census
//!    (`MinaSeams.every_declared_port_is_covered_by_a_named_seam`).
//!
//! Fast tests only — nothing here proves. The proving paths are exercised by the heavy
//! `mina_wrap_finalize_fold.rs` / `mina_kimchi_verifier_gadget.rs` suites, which now go through
//! `apply_seam` on every run.

use dregg_circuit::descriptor_ir2::{EffectVmDescriptor2, parse_vm_descriptor2};
use dregg_circuit_prove::mina_kimchi_verifier_gadget::GADGET_CONNECTS;
use dregg_circuit_prove::mina_phase2_chain_leaf::chain_link_descriptor;
use dregg_circuit_prove::mina_wrap_finalize_fold::{
    CONJ_PI_COUNT, CONJ_PI_XI, ENDO_PI_COUNT, ENDO_PI_XI, SK, V_PRIME_LIMBS,
    conjunction_descriptor, endo_lift_descriptor,
};
use dregg_circuit_prove::seam::{
    SeamSpec, fresh_sponge_seam, head_tip_seam, v_prime_seam, xi_seam,
};
use dregg_recursion_verify::chain_root::{CHAIN_CLAIM_LEN, STATE_WIDTH};
use dregg_recursion_verify::kimchi_root::FINALIZE_CLAIM_LEN;

/// The served Mina head verify descriptor — the head↔link seam's LEFT end.
fn head_verify_descriptor() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(include_str!(
        "../../circuit/descriptors/by-name/dregg-mina-lightclient-verify-v1.json"
    ))
    .expect("served head verify descriptor parses")
}

/// The served Mina link segment descriptor — the seam's RIGHT end.
fn link_segment_descriptor() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(include_str!(
        "../../circuit/descriptors/by-name/dregg-mina-lightclient-link-v1.json"
    ))
    .expect("served link segment descriptor parses")
}

#[test]
fn the_four_seams_parse_and_validate() {
    for seam in [
        xi_seam(),
        v_prime_seam(),
        fresh_sponge_seam(),
        head_tip_seam(),
    ] {
        let s = seam.expect("emitted seam parses and validates");
        assert_eq!(s.left.lanes.len(), 9);
        assert_eq!(s.right.lanes.len(), 9);
    }
}

/// ⚑ Gate 1 for the head↔link seam: the pin list is exactly the executor's REFUSAL 13/14a/14b
/// slot arithmetic — nine anchor pins `(i, i)`, nine tip pins `(9+i, 9+i)`, and the anchor-height
/// pin `(29, 18)`. The Lean twin is `MinaSeams.head_tip_seam_pins_are_the_nineteen`.
///
/// ⚠ REFUSAL 14c (`link PI[19] = head PI[18] − head PI[29]`) is AFFINE and deliberately absent: a
/// `SeamSpec` welds slots, and a seam that silently "covered" the derived segment length would
/// claim a relation no pin enforces.
#[test]
fn the_head_tip_seam_is_the_executors_nineteen_refusals() {
    let s = head_tip_seam().unwrap();
    assert_eq!(s.left.claim_len, 39);
    assert_eq!(s.right.claim_len, 37);
    let mut expected: Vec<(usize, usize)> = (0..9).map(|i| (i, i)).collect();
    expected.extend((0..9).map(|i| (9 + i, 9 + i)));
    expected.push((29, 18));
    assert_eq!(
        s.pins, expected,
        "nineteen pins: anchor block, tip block, anchor height"
    );
    assert!(s.zero_left.is_empty() && s.zero_right.is_empty());
    assert_eq!(s.connect_count(), 19);
}

/// Gate 1 for ξ: the pin list is exactly the 32 welds `fold_endo_into_finalize` documents —
/// endo slot `ENDO_PI_XI + i` to conjunction slot `CONJ_PI_XI + i`.
#[test]
fn the_xi_seam_is_the_folds_thirty_two_welds() {
    let s = xi_seam().unwrap();
    assert_eq!(s.left.claim_len, ENDO_PI_COUNT);
    assert_eq!(s.right.claim_len, CONJ_PI_COUNT);
    let expected: Vec<(usize, usize)> = (0..SK).map(|i| (ENDO_PI_XI + i, CONJ_PI_XI + i)).collect();
    assert_eq!(
        s.pins, expected,
        "the ξ seam must weld exactly the two ξ blocks, limb for limb"
    );
    assert!(s.zero_left.is_empty() && s.zero_right.is_empty());
    assert_eq!(s.connect_count(), SK);
}

/// Gate 1 for `v′`: 16 welds from the chain root's outgoing lane 0 to the finalize `v′` block,
/// plus 16 zero-pins on the high limbs — `connect_chain_root_v_prime`'s content, now emitted.
#[test]
fn the_v_prime_seam_is_the_gadgets_sixteen_plus_sixteen() {
    let s = v_prime_seam().unwrap();
    assert_eq!(s.left.claim_len, CHAIN_CLAIM_LEN);
    assert_eq!(s.right.claim_len, FINALIZE_CLAIM_LEN);
    let expected_pins: Vec<(usize, usize)> =
        (0..V_PRIME_LIMBS).map(|i| (STATE_WIDTH + i, i)).collect();
    assert_eq!(s.pins, expected_pins);
    let expected_zeros: Vec<usize> = (V_PRIME_LIMBS..SK).collect();
    assert_eq!(
        s.zero_right, expected_zeros,
        "the truncation half of the low-128-bits reading"
    );
    assert!(s.zero_left.is_empty());
}

/// Gate 1 for the fresh sponge: the whole 96-lane incoming state, zero-pinned, nothing else.
#[test]
fn the_fresh_sponge_seam_zeroes_the_whole_incoming_state() {
    let s = fresh_sponge_seam().unwrap();
    assert_eq!(s.left.claim_len, CHAIN_CLAIM_LEN);
    let expected: Vec<usize> = (0..STATE_WIDTH).collect();
    assert_eq!(s.zero_left, expected);
    assert!(s.pins.is_empty() && s.zero_right.is_empty());
}

/// The gadget's documented constraint count is exactly the two seams it applies.
#[test]
fn the_gadget_connect_count_is_the_two_seams() {
    let fresh = fresh_sponge_seam().unwrap();
    let vprime = v_prime_seam().unwrap();
    assert_eq!(
        fresh.connect_count() + vprime.connect_count(),
        GADGET_CONNECTS
    );
}

/// Gate 2: every seam end names the descriptor its fold loads, by name AND recomputed
/// fingerprint lanes. A re-emitted descriptor with a stale seam artifact fails HERE by name.
#[test]
fn every_seam_end_matches_its_served_descriptor() {
    let endo = endo_lift_descriptor().unwrap();
    let conj = conjunction_descriptor().unwrap();
    let chain = chain_link_descriptor().unwrap();

    let xi = xi_seam().unwrap();
    xi.left
        .require_matches(&endo)
        .expect("ξ seam left end is the endo-lift");
    xi.right
        .require_matches(&conj)
        .expect("ξ seam right end is the conjunction");

    for s in [v_prime_seam().unwrap(), fresh_sponge_seam().unwrap()] {
        s.left
            .require_matches(&chain)
            .expect("chain seam left end is the fq chainlink");
        s.right
            .require_matches(&endo)
            .expect("chain seam right end grounds in the endo-lift");
    }

    // ⚑ The head↔link seam's two ends, against the SERVED light-client descriptors. This is the
    // gate that catches the `ABSORB_VK_LANES` class for this seam: a re-emitted verify or link
    // descriptor whose seam artifact did not follow fails HERE by recomputed fingerprint, not in
    // a docblock six weeks later.
    let head = head_verify_descriptor();
    let link = link_segment_descriptor();
    let ht = head_tip_seam().unwrap();
    ht.left
        .require_matches(&head)
        .expect("head-tip seam left end is the served head verify");
    ht.right
        .require_matches(&link)
        .expect("head-tip seam right end is the served link segment");
}

/// Gate 3: the artifact-side port census. Every port `ports.json` declares is covered, slot for
/// slot, by a registered seam's welds or zero-pins on the end naming that descriptor.
#[test]
fn every_declared_port_is_covered_by_an_emitted_seam() {
    #[derive(serde::Deserialize)]
    struct Port {
        name: String,
        lo: usize,
        width: usize,
    }
    #[derive(serde::Deserialize)]
    struct PortSet {
        descriptor: String,
        pi_count: usize,
        ports: Vec<Port>,
        covered_by: Vec<String>,
    }
    let ports: Vec<PortSet> =
        serde_json::from_str(include_str!("../../circuit/descriptors/seams/ports.json"))
            .expect("ports.json parses");
    assert!(
        !ports.is_empty(),
        "the census has at least the conjunction row"
    );

    let seams: Vec<SeamSpec> = [
        xi_seam(),
        v_prime_seam(),
        fresh_sponge_seam(),
        head_tip_seam(),
    ]
    .into_iter()
    .map(|s| s.unwrap())
    .collect();

    let covers = |s: &SeamSpec, desc: &str, p: &Port| -> bool {
        let left = s.left.descriptor == desc
            && (p.lo..p.lo + p.width)
                .all(|k| s.pins.iter().any(|&(l, _)| l == k) || s.zero_left.contains(&k));
        let right = s.right.descriptor == desc
            && (p.lo..p.lo + p.width)
                .all(|k| s.pins.iter().any(|&(_, r)| r == k) || s.zero_right.contains(&k));
        left || right
    };

    for ps in &ports {
        for p in &ps.ports {
            assert!(
                p.lo + p.width <= ps.pi_count,
                "port {} out of range",
                p.name
            );
            let seam = seams.iter().find(|s| covers(s, &ps.descriptor, p));
            let seam = seam.unwrap_or_else(|| {
                panic!(
                    "port `{}` of `{}` is covered by NO emitted seam — a free-but-published \
                     block must either have a named seam or fail this gate",
                    p.name, ps.descriptor
                )
            });
            assert!(
                ps.covered_by.contains(&seam.name),
                "port `{}` is covered by `{}` but ports.json credits {:?}",
                p.name,
                seam.name,
                ps.covered_by
            );
        }
    }

    // The conjunction's ξ port is present and covered by the ξ seam specifically — the
    // retroactive instance this whole mechanism was built for.
    let conj = ports
        .iter()
        .find(|ps| ps.descriptor == "dregg-mina-wrap-conjunction::v1")
        .expect("the conjunction declares its port set");
    assert!(
        conj.ports
            .iter()
            .any(|p| p.name == "xi" && p.lo == 0 && p.width == 32)
    );

    // ⚑ The head's SEAM-covered ports are present: the anchor block and the tip block — the tip
    // being the `LINK_OK`-guarded `proof_bind`'s commit surface, which with `bound := none`
    // appears in no emitted polynomial and is therefore exactly the shape this census exists to
    // keep covered. The head's two digest-shaped commitment ports (REFUSAL 4/15) and the link's
    // two UNCOVERED body ports are censused in Lean (`MinaSeams`), not here — see
    // `EmitSeamSpecs.lean` for why this file carries only what a `SeamSpec` can cover.
    let head = ports
        .iter()
        .find(|ps| ps.descriptor == "dregg-mina-lightclient-verify::v1")
        .expect("the head verify declares its seam-covered port set");
    assert_eq!(head.pi_count, 39);
    assert!(
        head.ports
            .iter()
            .any(|p| p.name == "anchor-state" && p.lo == 0 && p.width == 9)
    );
    assert!(
        head.ports
            .iter()
            .any(|p| p.name == "tip-state" && p.lo == 9 && p.width == 9)
    );
}
