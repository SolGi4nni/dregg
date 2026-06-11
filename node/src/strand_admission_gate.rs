//! Verified FEDERATION-ADMISSION GATE — gate finality participation on the Lean-exported F-4 rule.
//!
//! # What this is
//!
//! `blocklace_sync::poll_finalized_blocks` hands the constitution's `participants` set to
//! `dregg_blocklace::ordering::tau` (and the verified finality gate). Red-team finding F-4: a strand
//! is just a keypair, so an adversary can spin up unlimited free strands; if such a Sybil keypair
//! reaches the participant set it can anchor finality. The fix (the verified
//! `Dregg2.Distributed.StrandAdmission`): an `admitted` strand must be a genesis SEED, OR vouched to
//! threshold by rooted members, OR bonded ≥ `min_bond`. The Lean `finalLeaderAtAdmitted` gates the
//! finalized order on `admitted`, so a non-admitted Sybil anchors NOTHING.
//!
//! This module makes the node CALL that verified rule at the live finalization point. It builds a
//! [`dregg_federation::AdmissionRegistry`] from the node's real consensus state — the constitution
//! participants are the bootstrap **seeds** (the trust root, admitted by construction, exactly the
//! Lean `seeds`/`isSeed` semantics, identical to `Constitution::new`'s initial set) — and filters the
//! participant set through `AdmissionRegistry::admitted`. With the node's `dregg-federation`
//! dependency built `--features lean-admission`, `admitted` routes through the VERIFIED Lean
//! `dregg_strand_admit` export (`dregg_lean_ffi::verified_admits`), so the participant set the node
//! finalizes over is decided BY THE VERIFIED RULE — not a Rust mirror. The Lean theorem
//! `strand_admit_eq_admitted` proves the export's verdict IS `StrandAdmission.admitted`, so this gates
//! the live path on the verified rule by construction.
//!
//! # Why seeds = constitution participants is faithful (and not a degradation)
//!
//! The genesis committee IS the bootstrap trust root — the same set `MembershipSafety`/the
//! constitution recognizes by construction. A strand the constitution already lists as a participant
//! is `is_seed`-admitted (transparent: the gate never drops a legitimate constitutional member). The
//! gate BITES only on a keypair that appears in the lace / proposed set but is NOT a constitutional
//! member and has NO vouch/bond standing — precisely the free Sybil F-4 names. As the federation
//! grows a vouch/bond registry (gossip-fed), the same `AdmissionRegistry` carries those attestations
//! (the verified rule's vouch/stake paths) into this gate; today the seed root is the load-bearing
//! anti-Sybil tooth the node enforces live.
//!
//! # Flag + fail-safety
//!
//! Gated by [`strand_admission_gate_enabled`] (`DREGG_STRAND_ADMISSION_GATE`, **default ON**). When
//! the Lean archive lacks the export (stale/marshal-only build), `AdmissionRegistry::admitted` itself
//! FALLS BACK to its pure-Rust differential sibling, so the gate is never broken — only un-verified —
//! and a loud warning is logged once. The gate is fail-CLOSED on a strand basis: an un-admitted
//! strand is filtered OUT of the participant set (it contributes nothing to finality).

use std::sync::Once;

use dregg_federation::admission::AdmissionRegistry;
use dregg_types::PublicKey;

/// One-shot guard so the verified/fallback diagnostic is logged at most once per process.
static GATE_BACKEND_ANNOUNCED: Once = Once::new();

/// Whether the live strand-admission gate is enabled. **Default ON** (devnet-readiness: the verified
/// F-4 rule gates participation). `DREGG_STRAND_ADMISSION_GATE=0`/`false`/`off` opts OUT (keeps the
/// raw constitution participant set) for an operator who needs to bypass it.
pub fn strand_admission_gate_enabled() -> bool {
    match std::env::var("DREGG_STRAND_ADMISSION_GATE").ok().as_deref() {
        Some("0") | Some("false") | Some("FALSE") | Some("off") | Some("OFF") => false,
        _ => true,
    }
}

/// Whether the verified Lean strand-admission export is linked (so the gate decides via the VERIFIED
/// rule rather than the Rust fallback). Surfaced for the once-warning + diagnostics.
pub fn lean_backed() -> bool {
    dregg_lean_ffi::strand_admit_available()
}

/// Build a [`dregg_federation::AdmissionRegistry`] whose SEEDS are the given constitution
/// participants (the bootstrap trust root) and filter `candidates` to the admitted subset — the F-4
/// gate IN FRONT of `tau`. When [`strand_admission_gate_enabled`] is false this is the identity (the
/// raw candidate list). `participants` are the constitution's recognized members; `candidates` is the
/// set headed to `tau` (normally equal to `participants`, but kept separate so a caller may gate a
/// wider proposed set against the constitutional seed root).
///
/// With the node's `dregg-federation` built `--features lean-admission`, `AdmissionRegistry::admitted`
/// routes each verdict through the VERIFIED Lean `dregg_strand_admit` export — so the returned subset
/// is the one the VERIFIED `StrandAdmission.admitted` rule admits. The pure-Rust sibling is the
/// fallback when the archive is absent.
pub fn admitted_participants(participants: &[[u8; 32]], candidates: &[[u8; 32]]) -> Vec<[u8; 32]> {
    if !strand_admission_gate_enabled() {
        return candidates.to_vec();
    }
    // Announce ONCE which backend decides the live F-4 gate: the VERIFIED Lean `dregg_strand_admit`
    // rule (the strong bar — the node actually invokes the exported, proved `admitted`), or the
    // pure-Rust differential sibling (when the Lean archive is stale/marshal-only). An operator on a
    // fallback build is told LOUDLY that the gate is running un-verified so they can rebuild the
    // closure-complete archive (`scripts/seed-dregg2-closure.sh`).
    GATE_BACKEND_ANNOUNCED.call_once(|| {
        if lean_backed() {
            tracing::info!(
                "strand-admission gate (F-4) is LEAN-BACKED: participation is decided by the \
                 VERIFIED `dregg_strand_admit` export (StrandAdmission.admitted)"
            );
        } else {
            tracing::warn!(
                "strand-admission gate (F-4) is running on the pure-Rust fallback: the Lean \
                 `dregg_strand_admit` export is not linked (stale/marshal-only archive). Rebuild \
                 the closure-complete archive to gate participation on the VERIFIED rule."
            );
        }
    });
    // Seeds = the constitution participants (the trust root, admitted by construction). The vouch
    // threshold / min-bond are set high-but-finite; with no vouch/bond registry fed yet, the seed
    // path is the live anti-Sybil tooth (a non-seed with no standing is rejected).
    let seeds: Vec<PublicKey> = participants.iter().map(|p| PublicKey(*p)).collect();
    // Vouch threshold 1 (any single rooted vouch admits, once a vouch registry exists) + a nominal
    // bond floor; both are inert today (no vouches/bonds fed), so admission reduces to the seed root.
    let registry = AdmissionRegistry::new(seeds, 1, 1);
    candidates
        .iter()
        .copied()
        .filter(|c| registry.admitted(&PublicKey(*c)))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_types::generate_keypair;
    use std::sync::Mutex;

    /// Serializes the env-sensitive tests in this module. `disabled_gate_is_identity` mutates the
    /// process-global `DREGG_STRAND_ADMISSION_GATE` env var; without this lock the default parallel
    /// test runner can let that mutation leak into `gate_admits_members_rejects_sybil` (which reads
    /// the same var through `strand_admission_gate_enabled`), flakily turning the gate into the
    /// identity and admitting the Sybil. Both tests acquire this guard so the env state each observes
    /// is its own.
    static ENV_GUARD: Mutex<()> = Mutex::new(());

    /// The gate admits the constitutional members (seeds) and REJECTS a fresh non-member Sybil — the
    /// live F-4 closure, decided through `AdmissionRegistry::admitted` (the verified Lean rule when the
    /// archive is linked, the Rust sibling otherwise; both agree on this seed-only case).
    #[test]
    fn gate_admits_members_rejects_sybil() {
        let _guard = ENV_GUARD.lock().unwrap_or_else(|p| p.into_inner());
        let (_, a) = generate_keypair();
        let (_, b) = generate_keypair();
        let (_, sybil) = generate_keypair();
        let participants = vec![*a.as_bytes(), *b.as_bytes()];
        // candidates = the two members + a fresh Sybil keypair not in the constitution.
        let candidates = vec![*a.as_bytes(), *b.as_bytes(), *sybil.as_bytes()];
        let admitted = admitted_participants(&participants, &candidates);
        assert!(
            admitted.contains(a.as_bytes()),
            "constitutional member a admitted"
        );
        assert!(
            admitted.contains(b.as_bytes()),
            "constitutional member b admitted"
        );
        assert!(
            !admitted.contains(sybil.as_bytes()),
            "F-4: a fresh non-member Sybil strand is filtered out of the participant set"
        );
    }

    /// With the gate disabled (`DREGG_STRAND_ADMISSION_GATE=0`) the candidate list passes through
    /// unchanged (operator bypass). Uses a process-local env guard.
    #[test]
    fn disabled_gate_is_identity() {
        let _guard = ENV_GUARD.lock().unwrap_or_else(|p| p.into_inner());
        // Save/restore so we don't disturb other tests in the same process.
        let prev = std::env::var("DREGG_STRAND_ADMISSION_GATE").ok();
        // SAFETY (edition 2024): single-threaded test; we restore the prior value
        // below so no other test in this process observes a torn env.
        unsafe {
            std::env::set_var("DREGG_STRAND_ADMISSION_GATE", "0");
        }
        let (_, a) = generate_keypair();
        let (_, sybil) = generate_keypair();
        let participants = vec![*a.as_bytes()];
        let candidates = vec![*a.as_bytes(), *sybil.as_bytes()];
        let admitted = admitted_participants(&participants, &candidates);
        assert_eq!(
            admitted, candidates,
            "disabled gate is the identity on the candidate list"
        );
        unsafe {
            match prev {
                Some(v) => std::env::set_var("DREGG_STRAND_ADMISSION_GATE", v),
                None => std::env::remove_var("DREGG_STRAND_ADMISSION_GATE"),
            }
        }
    }
}
