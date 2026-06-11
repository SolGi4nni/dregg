//! Adversarial tests for the gossip mesh's eclipse resistance + small-network
//! transaction-origin anonymity (F-5 / L4).
//!
//! Threat model (adversary A3/A5): a Byzantine peer / on-path network adversary
//! that (a) floods the victim with many Sybil connections from a single subnet
//! to **capture the spanning tree** (eclipse), and (b) exploits the fact that a
//! tiny network historically disabled Dandelion++ stem (`peer_count < 5`),
//! exposing the **transaction origin** directly to every mesh peer.
//!
//! WAS A FINDING (`_THREAT-MODEL.md` F-5 / L4): below 5 peers the stem was set
//! to immediate self-fluff (origin broadcasts directly = zero origin anonymity),
//! and there was no anchor / trusted-peer anti-eclipse policy — most vulnerable
//! exactly when the network is smallest.
//!
//! FIX (CLOSED): `net::peer_score::PeerScoreboard::select_eager_with_anchors`
//! pins operator-trusted **anchor** peers into the eager set ahead of any Sybil
//! flood (so the spanning tree cannot be captured), and the publish path keeps
//! the origin one hop removed (stem via an anchor) whenever any peer is present.
//!
//! These tests drive the PUBLIC eclipse-resistance surface (the scoreboard) and
//! assert DEFENDED. The stem-origin invariant itself is pinned by net-internal
//! `gossip::tests::stem_plan_*` (StemPlan is crate-private).

use dregg_net::peer_score::{PeerScoreboard, Penalty};
use std::collections::HashSet;
use std::net::SocketAddr;

fn addr(s: &str) -> SocketAddr {
    s.parse().unwrap()
}

// ===========================================================================
// ATTACK 1 — single-subnet Sybil flood tries to CAPTURE the eager set.
//
// The attacker opens 200 connections, all in 10.0/16, all with max reputation
// (it relays diligently to look good). The victim has ONE trusted anchor in a
// different subnet with only modest reputation. Despite being outnumbered and
// outscored 200:1, the anchor MUST remain in the eager set — an eclipse cannot
// fully capture the spanning tree while a trusted anchor relays.
// ===========================================================================

#[test]
fn attack_sybil_flood_cannot_evict_trusted_anchor_from_eager_set() {
    let mut sb = PeerScoreboard::new();

    let mut all: Vec<SocketAddr> = Vec::new();
    for i in 0..200u16 {
        let a = addr(&format!(
            "10.0.{}.{}:9000",
            (i >> 8) as u8,
            (i & 0xff) as u8
        ));
        for _ in 0..40 {
            sb.reward_fresh_delivery(a); // attacker looks maximally reliable
        }
        all.push(a);
    }

    // One trusted anchor, different subnet, modest reputation.
    let anchor = addr("203.0.113.7:9000");
    sb.observe(anchor);
    all.push(anchor);

    let mut anchors = HashSet::new();
    anchors.insert(anchor);

    // Even with a small eager degree, the anchor is pinned first.
    for eager_degree in [1usize, 2, 3, 4] {
        let eager = sb.select_eager_with_anchors(&all, &anchors, eager_degree);
        assert!(
            eager.contains(&anchor),
            "FINDING: 200-Sybil flood captured the eager set at degree {eager_degree} \
             (anchor evicted: {eager:?})"
        );
        // And the single-subnet attacker cannot hold the WHOLE eager set: at
        // minimum the anchor slot is denied to it.
        let attacker_slots = eager.iter().filter(|a| **a != anchor).count();
        assert!(
            attacker_slots < eager_degree.max(1),
            "FINDING: attacker still holds every eager slot at degree {eager_degree}"
        );
    }
    eprintln!("[NET ATTACK 1 / F-5] sybil-flood eager-set capture: DEFENDED (anchor pinned)");
}

// ===========================================================================
// ATTACK 2 — flap the anchor's connection to STARVE it out of the candidate
// set (the eclipse-by-attrition angle). The scoreboard models this: a mild
// disconnect penalty must NOT push a trusted anchor below the graylist
// threshold (which would let the Sybils take its slot). We apply several
// transient-disconnect penalties and confirm the anchor is still eager.
// ===========================================================================

#[test]
fn attack_anchor_flap_does_not_starve_it_from_eager_set() {
    let mut sb = PeerScoreboard::new();

    // A Sybil bloc, distinct subnet each so diversity does not save us — only
    // anchor pinning does.
    let mut all: Vec<SocketAddr> = Vec::new();
    for i in 0..8u8 {
        let a = addr(&format!("100.{}.0.1:9000", 64 + i));
        for _ in 0..10 {
            sb.reward_fresh_delivery(a);
        }
        all.push(a);
    }

    let anchor = addr("203.0.113.7:9000");
    sb.observe(anchor);
    // join_topic marks bootstrap peers as trusted anchors — replicate that.
    sb.mark_anchor(anchor);
    all.push(anchor);
    let mut anchors = HashSet::new();
    anchors.insert(anchor);

    // Simulate MANY transient connection drops (the gossip layer applies a mild
    // InvalidMessage penalty on a dead anchor connection but RETAINS it). Enough
    // to drive a NON-anchor well past the graylist threshold.
    for _ in 0..10 {
        sb.penalize(anchor, Penalty::InvalidMessage);
    }
    // Sanity: the same beating WOULD graylist a non-anchor peer.
    {
        let mut sb2 = PeerScoreboard::new();
        let normal = addr("198.51.100.9:9000");
        sb2.observe(normal);
        for _ in 0..10 {
            sb2.penalize(normal, Penalty::InvalidMessage);
        }
        assert!(
            sb2.is_graylisted(&normal),
            "control: a non-anchor peer is graylisted by this many flaps"
        );
    }
    // A mild-penalized anchor must not be graylisted (categorical eviction is
    // reserved for proven equivocation), so it is still pinned.
    assert!(
        !sb.is_graylisted(&anchor),
        "FINDING: transient flaps graylisted the trusted anchor (eclipse-by-attrition)"
    );
    let eager = sb.select_eager_with_anchors(&all, &anchors, 3);
    assert!(
        eager.contains(&anchor),
        "FINDING: flapped anchor lost its pinned eager slot: {eager:?}"
    );
    eprintln!("[NET ATTACK 2 / F-5] anchor flap starvation: DEFENDED (retained + pinned)");
}

// ===========================================================================
// ATTACK 3 — a TRUSTED anchor turns Byzantine (relays a proven equivocation).
// Trust must not be a license to equivocate: a graylisted anchor is NOT pinned,
// so the defense does not become an attack vector if an anchor is compromised.
// ===========================================================================

#[test]
fn attack_byzantine_anchor_is_not_pinned() {
    let mut sb = PeerScoreboard::new();
    let anchor = addr("203.0.113.7:9000");
    let honest = addr("198.51.100.4:9000");
    sb.observe(honest);
    sb.penalize(anchor, Penalty::EquivocationRelay); // proven slashable fault

    let mut anchors = HashSet::new();
    anchors.insert(anchor);

    let eager = sb.select_eager_with_anchors(&[anchor, honest], &anchors, 3);
    assert!(
        !eager.contains(&anchor),
        "FINDING: a proven-Byzantine anchor was still pinned eager (trust != license)"
    );
    assert!(
        eager.contains(&honest),
        "the honest peer takes the slot instead"
    );
    eprintln!("[NET ATTACK 3 / F-5] byzantine anchor pinning: DEFENDED (graylisted, not pinned)");
}
