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
//! dependency (Lean unconditional on native), `admitted` routes through the VERIFIED Lean
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
//! FALLS BACK to twin#7's DECLARED NARROWING — genesis SEEDS only, a local deterministic check that
//! needs no Lean (`federation/src/admission.rs::admitted_no_gate`, registered in
//! `scripts/ci-invariants/gate-dataflow.tsv` as `narrow:is_seed`). The gate is never broken, only
//! un-verified, and a loud warning is logged once. The gate is fail-CLOSED on a strand basis: an
//! un-admitted strand is filtered OUT of the participant set (it contributes nothing to finality).
//!
//! # ⚑ FAIL-CLOSED — the FIFTH member of the fail-OPEN class, at the OPERATOR-ESCAPE flavour
//!
//! The gate-ABSENT path here was never the hole: it is twin#7's declared narrowing above. The hole
//! was the gate-DISABLED path. `admitted_participants` opened with
//!
//! ```ignore
//! // IGNORED: the DELETED opening line of `admitted_participants`, quoted as the defect
//! // exhibit this section is about. `candidates` is that removed function's parameter;
//! // the line no longer exists and must not be resurrected by an over-eager repair.
//! if !strand_admission_gate_enabled() { return candidates.to_vec(); }
//! ```
//!
//! — an UNREGISTERED, UNLOGGED, UNMETERED environment variable that returns the raw candidate list
//! with NO admission rule having decided it. It was invisible to invariant 6 (no row), silent in
//! every CI log (not one line of output on the bypass path), and — the part that matters most —
//! `DREGG_REQUIRE_LEAN=1` HAD NO EFFECT ON IT AT ALL: an operator could demand the verified artifact
//! and still be opted out of the F-4 rule by a second variable. That is the same defect
//! `bcab8925b9` closed for the PQ gate.
//!
//! POLICY: the operator escape survives, but as a DECLARED, REVOCABLE bypass. When the F-4 rule did
//! not decide the set and no bypass is declared, this site REFUSES the raw list and runs the rule
//! anyway ([`strand_admission_disposition`] ⇒ [`gated_admitted`]).
//!
//! ONE DECLARED BYPASS ([`strand_admission_bypass_allowed`]): the operator explicitly disabled this
//! gate (`DREGG_STRAND_ADMISSION_GATE=0`). `DREGG_REQUIRE_LEAN=1` REVOKES it.
//!
//! Deliberately NOT a bypass, and this is what makes the row stronger than its siblings': the Lean
//! export being ABSENT. Every other member of this class treats an archive-less build as a bypass
//! because there is nothing to route to. Here there IS — `AdmissionRegistry::admitted` still answers,
//! seeds-only, through twin#7's registered narrowing — so a missing archive buys no escape at all.
//!
//! ## ⚑ AT ITS CURRENT RESOLUTION: this refusal is REAL but DORMANT on the live caller
//!
//! Say it plainly rather than let the fix read bigger than it is. `blocklace_sync.rs:1450` is the
//! ONLY live caller and it passes `admitted_participants(&raw_participants, &raw_participants)` —
//! `candidates == participants`, so every candidate is a seed and the F-4 filter provably cannot drop
//! anything (already recorded as the "identity gate" finding in
//! `docs/deos/CRATE-EXCELLENCE-PLAN.md` §P1(e)). On THAT call the bypass and the gate return the
//! same set, so `DREGG_STRAND_ADMISSION_GATE=0` does **not** admit a Sybil today — the F-4 reopening
//! is a property of this FUNCTION, not of the live path, and it arms the moment any caller widens
//! `candidates` beyond the constitutional set (the growth path this module's header describes).
//!
//! What the refusal changes TODAY is therefore narrow and worth stating exactly: `DREGG_REQUIRE_LEAN=1`
//! now HAS AN EFFECT on this path where it previously had none, the bypass is announced instead of
//! silent, it carries a metric, and the site is a REGISTERED decision site so the warn-and-admit
//! cannot regrow unseen. [`unvouched_candidate_count`] is logged on every refusal precisely so the
//! dormancy is VISIBLE in the field: `unvouched = 0` says the bypass could not have widened anything.
//!
//! The vacuity short-circuit is deliberately the NARROW one (`candidates.is_empty()`), not
//! `unvouched == 0`. Short-circuiting on `unvouched == 0` would have been the more "correct-looking"
//! filter and it would have made this guard STRUCTURALLY DEAD against its only production caller — a
//! floor that cannot be reached is not a floor. Both error directions here are cheap: refusing where
//! the bypass was harmless costs one extra registry pass returning the identical set, while
//! short-circuiting where the bypass WOULD widen is the bug itself.

use std::sync::Once;

use dregg_federation::admission::AdmissionRegistry;
use dregg_types::PublicKey;

/// One-shot guard so the verified/fallback diagnostic is logged at most once per process.
static GATE_BACKEND_ANNOUNCED: Once = Once::new();

/// One-shot guard so the DECLARED operator bypass announces itself at most once per process. Before
/// this existed the bypass path emitted NOTHING — an operator (or a CI job) could run with the F-4
/// rule switched off and see no evidence of it anywhere in the log.
static GATE_BYPASS_ANNOUNCED: Once = Once::new();

/// Whether the live strand-admission gate is enabled. **Default ON** (devnet-readiness: the verified
/// F-4 rule gates participation). `DREGG_STRAND_ADMISSION_GATE=0`/`false`/`off` opts OUT (keeps the
/// raw constitution participant set) — a DECLARED bypass that `DREGG_REQUIRE_LEAN=1` revokes.
pub fn strand_admission_gate_enabled() -> bool {
    !matches!(
        std::env::var("DREGG_STRAND_ADMISSION_GATE").ok().as_deref(),
        Some("0") | Some("false") | Some("FALSE") | Some("off") | Some("OFF")
    )
}

/// Whether the verified Lean strand-admission export is linked (so the gate decides via the VERIFIED
/// rule rather than the Rust fallback). Surfaced for the once-warning + diagnostics.
pub fn lean_backed() -> bool {
    dregg_lean_ffi::strand_admit_available()
}

/// `DREGG_REQUIRE_LEAN=1` — "I demand the verified artifact". The tree-wide signal (the
/// `dregg-lean-ffi` build gate; `turn`'s `require_verified_conservation_gate`; twin#8b's and
/// twin#3b's `require_verified_lean_gate`) that a build must not take ANY declared bypass around a
/// verified gate. It promotes [`strand_admission_bypass_allowed`]'s single bypass to the hard
/// refusal.
fn require_verified_lean_gate() -> bool {
    std::env::var_os("DREGG_REQUIRE_LEAN")
        .is_some_and(|v| matches!(v.to_string_lossy().trim(), "1" | "true" | "on" | "yes"))
}

/// FAIL-CLOSED CLASS (twin#7b, the strand-admission sibling of `belt_gate_bypass_allowed` /
/// `coord_gate_bypass_allowed` / `mldsa_verify_bypass_allowed`): whether the F-4 admission rule —
/// `StrandAdmission.admitted`, reached through `AdmissionRegistry::admitted` — may be BYPASSED
/// entirely, handing `tau` the raw candidate list.
///
/// ONE DECLARED bypass, and nothing else:
///   * `gate_disabled_by_operator` — `DREGG_STRAND_ADMISSION_GATE=0`, the operator's explicit
///     opt-out. They kept the raw constitution participant set deliberately.
///
/// `require_lean` (`DREGG_REQUIRE_LEAN=1`) revokes it.
///
/// A missing Lean export is DELIBERATELY NOT a bypass here (unlike every sibling): the rule still
/// answers through twin#7's declared seeds-only narrowing, so there is always an admission decision
/// available to route to.
///
/// ⚑ ONE BOOLEAN EXPRESSION, DELIBERATELY — DO NOT REINTRODUCE AN EARLY RETURN. A leading
/// `if require_lean { return false; }` puts a bare `return false` inside a declared discriminator,
/// and `scripts/ci-invariants/gate-dataflow.py` reads that as the REFUSAL token while inlining this
/// helper into the caller's gate-absent region — which leaves the caller's real refusal arm unread.
/// Two sites shipped blind on exactly that shape (`1736835f69`); see the same note on
/// `belt_gate_bypass_allowed` and `coord_gate_bypass_allowed`.
fn strand_admission_bypass_allowed(gate_disabled_by_operator: bool, require_lean: bool) -> bool {
    !require_lean && gate_disabled_by_operator
}

/// Why a participant set REFUSED the un-gated candidate list. Distinct from every "the F-4 rule
/// dropped this strand" outcome on purpose: mirroring twin#1's `ConservationGateUnavailable` and
/// twin#8b's `FinalityGateUnavailable`, no strand is judged here and none was rejected — no
/// admission rule ran at all, so the site declines to hand `tau` a set nothing decided.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StrandAdmissionRefusal {
    /// The F-4 admission rule did not decide this candidate set (the operator disabled the gate) and
    /// no declared bypass holds. The raw candidate list does not reach `tau`; the rule runs anyway.
    StrandAdmissionGateUnavailable,
}

impl std::fmt::Display for StrandAdmissionRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::StrandAdmissionGateUnavailable => write!(
                f,
                "StrandAdmissionGateUnavailable: no F-4 admission rule \
                 (dregg_strand_admit = StrandAdmission.admitted, or twin#7's seeds-only narrowing) \
                 decided this candidate set and the operator opt-out is REVOKED — the raw candidate \
                 list REFUSES to reach tau (this is a MISSING GATE, not a verdict about any strand)"
            ),
        }
    }
}

/// How many candidates have NO constitutional standing — the ONLY strands the operator bypass can
/// widen the participant set with, since with no vouch/bond registry fed `AdmissionRegistry::admitted`
/// reduces to the seed root.
///
/// This is a DIAGNOSTIC, never a decider. It is logged on every refusal so the field can see whether
/// the bypass was actually widening anything; see this module's header on why it is deliberately NOT
/// the vacuity short-circuit.
fn unvouched_candidate_count(participants: &[[u8; 32]], candidates: &[[u8; 32]]) -> usize {
    candidates
        .iter()
        .filter(|c| !participants.contains(c))
        .count()
}

/// THE FAIL-CLOSED DISPOSITION for the F-4 strand-admission gate. Called by
/// [`admitted_participants`] on every participant projection.
///
/// `Ok(())` ⇒ the caller may hand back whatever it has (the rule's own verdict, or — under the
/// declared bypass — the raw candidate list). `Err(StrandAdmissionGateUnavailable)` ⇒ REFUSE the raw
/// list: the caller runs the F-4 rule regardless of the operator's opt-out.
///
/// ## The vacuity short-circuit
///
/// A refusal that fires where it means nothing is not a gate. With no candidates there is no
/// admission decision in existence for any rule to have made, so an empty set short-circuits BEFORE
/// the verdict is consulted. (The header states at length why the WIDER filter — "no candidate lacks
/// constitutional standing" — is deliberately rejected: it would make this guard unreachable from its
/// only production caller.)
fn strand_admission_disposition(
    admission_verdict: Option<&[[u8; 32]]>,
    candidate_count: usize,
    gate_disabled_by_operator: bool,
    require_lean: bool,
) -> Result<(), StrandAdmissionRefusal> {
    // VACUOUS SET — no candidate at all, so there is no admission decision in existence. Short-
    // circuited BEFORE the verdict is consulted, so the refusal below can never fire where it would
    // mean nothing.
    if candidate_count == 0 {
        return Ok(());
    }
    let Some(_admitted) = admission_verdict else {
        if strand_admission_bypass_allowed(gate_disabled_by_operator, require_lean) {
            return Ok(());
        }
        return Err(StrandAdmissionRefusal::StrandAdmissionGateUnavailable);
    };
    Ok(())
}

/// Build a [`dregg_federation::AdmissionRegistry`] whose SEEDS are the given constitution
/// participants (the bootstrap trust root) and filter `candidates` to the admitted subset — the F-4
/// gate IN FRONT of `tau`. `participants` are the constitution's recognized members; `candidates` is
/// the set headed to `tau` (normally equal to `participants`, but kept separate so a caller may gate a
/// wider proposed set against the constitutional seed root).
///
/// With the node's `dregg-federation` (Lean unconditional on native), `AdmissionRegistry::admitted`
/// routes each verdict through the VERIFIED Lean `dregg_strand_admit` export — so the returned subset
/// is the one the VERIFIED `StrandAdmission.admitted` rule admits. When the archive lacks the export
/// it degrades to twin#7's DECLARED seeds-only narrowing, which is still an admission decision.
///
/// When [`strand_admission_gate_enabled`] is false the raw candidate list passes through — but only
/// as a DECLARED bypass that [`strand_admission_disposition`] governs and `DREGG_REQUIRE_LEAN=1`
/// revokes, not as an unconditional early return. See the module header for the full policy and for
/// the honest statement of how much this buys on today's only caller.
pub fn admitted_participants(participants: &[[u8; 32]], candidates: &[[u8; 32]]) -> Vec<[u8; 32]> {
    let gate_disabled_by_operator = !strand_admission_gate_enabled();
    let require_lean = require_verified_lean_gate();

    // `None` EXACTLY when no admission rule ran at all — the operator's opt-out. That is the state in
    // which the raw candidate list, un-vouched Sybils included, would reach `tau`. Note this is NOT
    // the archive-less state: `gated_admitted` still answers there, seeds-only, through twin#7's
    // declared narrowing.
    let admission_verdict: Option<Vec<[u8; 32]>> = if gate_disabled_by_operator {
        None
    } else {
        Some(gated_admitted(participants, candidates))
    };

    if let Err(refusal) = strand_admission_disposition(
        admission_verdict.as_deref(),
        candidates.len(),
        gate_disabled_by_operator,
        require_lean,
    ) {
        crate::metrics::inc_strand_admission_gate_unavailable_refusals();
        tracing::warn!(
            refusal = %refusal,
            candidates = candidates.len(),
            unvouched = unvouched_candidate_count(participants, candidates),
            lean_backed = lean_backed(),
            "F-4 strand-admission gate DISABLED by DREGG_STRAND_ADMISSION_GATE=0 while \
             DREGG_REQUIRE_LEAN=1 REVOKES that bypass — FAILING CLOSED: the raw candidate list does \
             NOT reach tau, the admission rule runs anyway. This is NOT a verdict about any strand \
             (none was rejected; no rule had decided the set). `unvouched=0` means the bypass could \
             not have widened this particular set. Unset DREGG_REQUIRE_LEAN to keep the opt-out."
        );
        return gated_admitted(participants, candidates);
    }

    admission_verdict.unwrap_or_else(|| {
        // The DECLARED, PERMITTED bypass. Announced once so it is never silent again.
        GATE_BYPASS_ANNOUNCED.call_once(|| {
            tracing::warn!(
                "F-4 strand-admission gate is BYPASSED (DREGG_STRAND_ADMISSION_GATE=0): the raw \
                 constitution candidate list reaches tau with NO admission rule having decided it. \
                 This is the ONE declared bypass in gate-dataflow.tsv's twin#7b row; set \
                 DREGG_REQUIRE_LEAN=1 to revoke it."
            );
        });
        candidates.to_vec()
    })
}

/// Run the F-4 admission rule over `candidates` with `participants` as the seed root — the gate
/// itself, with no bypass logic in it. Both the normal path and the REFUSAL path call this, which is
/// what makes the refusal cheap: refusing the operator's opt-out costs one registry pass, and on the
/// live `(raw, raw)` call site it returns the identical set.
fn gated_admitted(participants: &[[u8; 32]], candidates: &[[u8; 32]]) -> Vec<[u8; 32]> {
    // Announce ONCE which backend decides the live F-4 gate: the VERIFIED Lean `dregg_strand_admit`
    // rule (the strong bar — the node actually invokes the exported, proved `admitted`), or twin#7's
    // declared seeds-only narrowing (when the Lean archive is stale/marshal-only). An operator on a
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
                "strand-admission gate (F-4) is running on twin#7's declared seeds-only narrowing: \
                 the Lean `dregg_strand_admit` export is not linked (stale/marshal-only archive). \
                 Rebuild the closure-complete archive to gate participation on the VERIFIED rule."
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

    /// Save/restore a process-global env var around a closure, so an env-sensitive test never leaks
    /// its mutation into a sibling running in the same process.
    fn with_env<T>(vars: &[(&str, Option<&str>)], f: impl FnOnce() -> T) -> T {
        let saved: Vec<(String, Option<String>)> = vars
            .iter()
            .map(|(k, _)| ((*k).to_string(), std::env::var(k).ok()))
            .collect();
        // SAFETY (edition 2024): every caller holds `ENV_GUARD`, so this process observes one
        // mutator at a time, and the prior values are restored before the guard is dropped.
        unsafe {
            for (k, v) in vars {
                match v {
                    Some(v) => std::env::set_var(k, v),
                    None => std::env::remove_var(k),
                }
            }
        }
        let out = f();
        unsafe {
            for (k, v) in &saved {
                match v {
                    Some(v) => std::env::set_var(k, v),
                    None => std::env::remove_var(k),
                }
            }
        }
        out
    }

    /// With the gate disabled (`DREGG_STRAND_ADMISSION_GATE=0`) and the bypass NOT revoked, the
    /// candidate list passes through unchanged — the DECLARED operator bypass still works. A
    /// fail-closed change that bricks the documented escape is not a fix.
    #[test]
    fn disabled_gate_is_identity() {
        let _guard = ENV_GUARD.lock().unwrap_or_else(|p| p.into_inner());
        let (_, a) = generate_keypair();
        let (_, sybil) = generate_keypair();
        let participants = vec![*a.as_bytes()];
        let candidates = vec![*a.as_bytes(), *sybil.as_bytes()];
        let admitted = with_env(
            &[
                ("DREGG_STRAND_ADMISSION_GATE", Some("0")),
                ("DREGG_REQUIRE_LEAN", None),
            ],
            || admitted_participants(&participants, &candidates),
        );
        assert_eq!(
            admitted, candidates,
            "the DECLARED operator bypass is the identity on the candidate list"
        );
    }

    /// ⚑ POLE A (the DISPOSITION, exhaustively): the F-4 admission rule did not decide the set and
    /// the site REFUSES the raw candidate list. This is the FIFTH member of the conservation twin's
    /// fail-OPEN class, at its OPERATOR-ESCAPE flavour — `admitted_participants` used to open with a
    /// bare `if !strand_admission_gate_enabled() { return candidates.to_vec(); }`: unregistered,
    /// unlogged, unmetered, and completely unaffected by `DREGG_REQUIRE_LEAN=1`.
    ///
    /// The test asserts THE NEGATIVE the way conservation's, twin#8b's and twin#3b's Pole A do: an
    /// `Ok(())` in the no-bypass quadrant PANICS with a FAIL-OPEN message, because `Ok(())` there
    /// means the site went on to hand `tau` a participant set no admission rule decided.
    ///
    /// It also pins the VACUITY short-circuit and the bypass predicate's own quadrants, because
    /// invariant 6 checks that the region REACHES a refusal past a declared discriminator and does
    /// NOT evaluate the discriminator: a mutation of `strand_admission_bypass_allowed` to a bare
    /// `true` stays GREEN there and must redden HERE. Invariants 2 and 6 are COMPLEMENTS at this
    /// site, not alternatives.
    #[test]
    fn strand_admission_fails_closed_when_no_rule_decided_the_set() {
        // ── THE HOLE, CLOSED. Candidates exist, no rule decided them, the operator opt-out is
        //    REVOKED by DREGG_REQUIRE_LEAN=1 ⇒ REFUSE.
        match strand_admission_disposition(None, 3, true, true) {
            Err(StrandAdmissionRefusal::StrandAdmissionGateUnavailable) => { /* fail-closed */ }
            Ok(()) => panic!(
                "FAIL-OPEN: there are candidates, NO F-4 admission rule decided them, and the \
                 operator's opt-out is REVOKED by DREGG_REQUIRE_LEAN=1 — yet the disposition permits \
                 the site to hand `tau` the raw candidate list, un-vouched Sybils included. That is \
                 the F-4 reopening this gate exists to prevent, reachable by environment variable."
            ),
        }

        // ── VACUITY SHORT-CIRCUIT: no candidates at all, so no admission decision exists.
        assert!(
            strand_admission_disposition(None, 0, true, true).is_ok(),
            "an EMPTY candidate set must NOT be refused — there is no admission decision in \
             existence for a missing rule to have made"
        );

        // ── THE RULE ANSWERED: there is no missing gate to dispose of, whatever it admitted —
        //    including the maximally-restrictive answer (it dropped everything).
        let seed = [7u8; 32];
        for verdict in [&[seed][..], &[][..]] {
            assert!(
                strand_admission_disposition(Some(verdict), 3, false, false).is_ok(),
                "an ANSWERING rule must never be refused — {} admitted strands is the F-4 rule's \
                 own verdict, not a missing gate",
                verdict.len()
            );
        }

        // ── THE ONE DECLARED BYPASS: the operator explicitly disabled the gate.
        assert!(
            strand_admission_disposition(None, 3, true, false).is_ok(),
            "DREGG_STRAND_ADMISSION_GATE=0 is the operator's declared opt-out (the same shape \
             twin#8b, twin#3b and twin#13 use), not a silent fall-open"
        );
        // ── `DREGG_REQUIRE_LEAN=1` REVOKES it. Before this row existed that variable had NO EFFECT
        //    ON THIS PATH AT ALL — the exact defect `bcab8925b9` closed for the PQ gate.
        assert!(
            strand_admission_disposition(None, 3, true, true).is_err(),
            "DREGG_REQUIRE_LEAN=1 must revoke the operator opt-out"
        );

        // The bypass predicate itself, so a future widening is a visible diff and not a quiet
        // boolean flip. Invariant 6 CANNOT see this (it does not evaluate the discriminator) —
        // these four lines are the complement that catches a `strand_admission_bypass_allowed ->
        // true` mutant.
        assert!(!strand_admission_bypass_allowed(false, false));
        assert!(strand_admission_bypass_allowed(true, false));
        assert!(!strand_admission_bypass_allowed(true, true));
        assert!(!strand_admission_bypass_allowed(false, true));

        // The diagnostic that makes the dormancy visible: on the live `(raw, raw)` call site every
        // candidate is a seed, so the bypass could not widen anything. THAT is the current
        // resolution of this gate, and it is asserted rather than merely written in a comment.
        let a = [1u8; 32];
        let b = [2u8; 32];
        let sybil = [9u8; 32];
        assert_eq!(unvouched_candidate_count(&[a, b], &[a, b]), 0);
        assert_eq!(unvouched_candidate_count(&[a, b], &[a, b, sybil]), 1);
        assert_eq!(unvouched_candidate_count(&[], &[]), 0);
    }

    /// ⚑ POLE A AT THE SITE, and its NON-OVER-FIRE companion beside it: the SAME participants, the
    /// SAME candidates — the ONLY thing that changes is whether the operator's opt-out is revoked.
    ///
    /// * BYPASS DECLARED AND PERMITTED ⇒ the raw list passes (the escape still works).
    /// * BYPASS REVOKED ⇒ the F-4 rule runs anyway and the Sybil is DROPPED; a Sybil observed in
    ///   the returned set PANICS with a FAIL-OPEN message.
    /// * GATE ENABLED ⇒ the Sybil is dropped whatever `DREGG_REQUIRE_LEAN` says (the refusal did not
    ///   become the only way to get filtering).
    #[test]
    fn admitted_participants_refuses_the_raw_list_when_the_bypass_is_revoked() {
        let _guard = ENV_GUARD.lock().unwrap_or_else(|p| p.into_inner());
        let (_, a) = generate_keypair();
        let (_, sybil) = generate_keypair();
        let participants = vec![*a.as_bytes()];
        // ≥1 UN-VOUCHED CANDIDATE, or the pole is vacuous: the refusal must be observable, which on
        // the live `(raw, raw)` call site it is NOT (see the module header).
        let candidates = vec![*a.as_bytes(), *sybil.as_bytes()];
        assert_eq!(
            unvouched_candidate_count(&participants, &candidates),
            1,
            "this pole needs a candidate the F-4 rule can actually drop, or it asserts nothing"
        );

        // ── THE DECLARED BYPASS STILL WORKS.
        let bypassed = with_env(
            &[
                ("DREGG_STRAND_ADMISSION_GATE", Some("0")),
                ("DREGG_REQUIRE_LEAN", None),
            ],
            || admitted_participants(&participants, &candidates),
        );
        assert_eq!(
            bypassed, candidates,
            "the declared operator bypass must still hand back the raw list — a fail-closed change \
             that bricks the documented escape is not a fix"
        );

        // ── POLE A: hold EVERYTHING fixed and revoke the bypass.
        let refused = with_env(
            &[
                ("DREGG_STRAND_ADMISSION_GATE", Some("0")),
                ("DREGG_REQUIRE_LEAN", Some("1")),
            ],
            || admitted_participants(&participants, &candidates),
        );
        if refused.contains(sybil.as_bytes()) {
            panic!(
                "FAIL-OPEN: DREGG_REQUIRE_LEAN=1 REVOKES the DREGG_STRAND_ADMISSION_GATE=0 opt-out, \
                 and `admitted_participants` STILL handed back the un-vouched Sybil — so \
                 `poll_finalized_blocks` would run `tau` over a participant set NO admission rule \
                 decided, and a free Sybil keypair could anchor finality. That is F-4, reopened by \
                 environment variable, on a node whose operator explicitly demanded the verified \
                 artifact."
            );
        }
        assert_eq!(
            refused,
            vec![*a.as_bytes()],
            "the revoked bypass must yield the F-4 rule's own answer (the seed root), not the raw \
             candidate list"
        );

        // ── AND IT DOES NOT OVER-FIRE: with the gate ENABLED the Sybil is dropped either way, so
        //    the refusal is not the only thing standing between `tau` and a Sybil.
        for require_lean in [None, Some("1")] {
            let gated = with_env(
                &[
                    ("DREGG_STRAND_ADMISSION_GATE", None),
                    ("DREGG_REQUIRE_LEAN", require_lean),
                ],
                || admitted_participants(&participants, &candidates),
            );
            assert_eq!(
                gated,
                vec![*a.as_bytes()],
                "with the gate ENABLED the F-4 rule drops the Sybil regardless of \
                 DREGG_REQUIRE_LEAN={require_lean:?}"
            );
        }
    }
}
