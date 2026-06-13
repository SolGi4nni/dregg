//! The honest static/dynamic boundary — what this toolkit CAN and CANNOT
//! certify from a constructed-but-not-submitted artifact alone.
//!
//! The `Dregg2.AssuranceCase` states five guarantees (A Authority, B
//! Conservation, C Integrity, D Freshness, E Unfoolability) over the kernel
//! and the running executor. Of those, only the parts decidable from the
//! ARTIFACT'S SHAPE are checkable here. The rest need live state, the
//! executor, or the proof — and claiming otherwise would launder vacuity.
//! This module is the machine-and-human-readable statement of that line.

/// What is **statically checkable** from the artifact alone (this crate).
pub const STATIC_CHECKABLE: &[(&str, &str)] = &[
    (
        "B (conservation) — move sum",
        "Per asset, the forest's Transfer / balance_change / note value MOVES \
         net to exactly zero. Decidable: it is arithmetic over the artifact's \
         own numbers.",
    ),
    (
        "A (non-amplification) — IN-FOREST edges",
        "A grant that exceeds a cap delegated to the granting cell EARLIER IN \
         THE SAME FOREST is a provable amplification. Decidable for the \
         in-artifact delegation chain.",
    ),
    (
        "well-formedness",
        "Authorization::Unchecked outside genesis, OneOf-carrying-Unchecked, \
         empty actions, no-op exercises. Pure structural shape.",
    ),
    (
        "ring balance (B specialization)",
        "A settlement ring's legs close a cycle and net every participant to \
         zero per asset. Decidable over the leg list.",
    ),
];

/// What is **dynamic** — needs the live executor / state / proof, and is
/// therefore OUT OF SCOPE for this crate (route to `dregg-intent::
/// verified_settle` or submit-and-verify the receipt instead).
pub const DYNAMIC_ONLY: &[(&str, &str)] = &[
    (
        "A (non-amplification) — the HOLDING half",
        "Whether the signer actually HELD the capability it grants (the live \
         c-list lookup). A grant over a target not delegated in-forest is \
         NOT flagged here — holding is a live-state question.",
    ),
    (
        "B (conservation) — sufficiency / underflow",
        "Whether `from` actually HAS the value it moves. A conserving forest \
         can still be rejected for insufficient balance — a live-balance check.",
    ),
    (
        "WHO — credential / signature validity",
        "ed25519 signature verification, STARK auth-proof checks, bearer-cap \
         and caveat-chain (HMAC) discharge against the live ShadowHostCtx \
         (block_height, frozen set, stored_head, budget, intro_lifetime). \
         These are §8 crypto carriers, not artifact shape.",
    ),
    (
        "C (integrity) — the whole-state commitment",
        "Whether the receipt binds the WHOLE post-state (Poseidon2 state \
         commitment). Produced by the executor; verified against the proof. \
         No artifact-only check exists.",
    ),
    (
        "D (freshness) — nullifier / replay / revocation",
        "Whether a spent note's nullifier was fresh, whether a stored cap \
         outlived its grantor's revocation epoch. Needs the live nullifier \
         set and the grantor's current delegation_epoch.",
    ),
    (
        "E (unfoolability) — the aggregate proof",
        "The recursive history fold a light client verifies. This is the \
         proof, not the turn — entirely downstream of submission.",
    ),
    (
        "BridgeMint cross-federation value",
        "A bridged note's value conservation is a portable-proof property \
         across federations, not a within-forest sum — not netted by \
         check_conservation.",
    ),
];

/// Render the boundary as a human-readable report (used by the CLI's
/// `--boundary` flag and embeddable in SDK explanations).
pub fn report() -> String {
    let mut s = String::new();
    s.push_str("=== STATIC (checked by dregg-userspace-verify, from the artifact alone) ===\n");
    for (name, desc) in STATIC_CHECKABLE {
        s.push_str(&format!("  [✓] {name}\n      {desc}\n"));
    }
    s.push_str("\n=== DYNAMIC (NOT checkable here — needs executor / live state / proof) ===\n");
    for (name, desc) in DYNAMIC_ONLY {
        s.push_str(&format!("  [·] {name}\n      {desc}\n"));
    }
    s.push_str(
        "\nThis toolkit is the cheap pre-flight (necessary, not sufficient). A Pass means \
         the artifact is well-shaped and self-conserving; it does NOT mean the executor \
         will accept it. For the dynamic half, route through \
         dregg-intent::verified_settle or submit and verify the receipt.\n",
    );
    s
}
