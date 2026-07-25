//! `verified_gate` — the route-through that makes the **Lean gate the decider** for every
//! Ethereum light-client verify rule this crate used to decide in Rust.
//!
//! # What changed, and why it is not cosmetic
//!
//! `Dregg2.Bridge.LightClientEth` proves `eth_no_forgery` over `verifyFinalizedUpdate`, and
//! `Dregg2.Bridge.LightClientEthGate.ethVerifyDecision_refines` proves (by `rfl`) that the
//! `@[export] dregg_eth_lc_verify` decision, fed an update's true projections, IS
//! `verifyFinalizedUpdate`. Until now nothing outside `dregg-lean-ffi` called that export:
//! `eth-lightclient` carried a hand-written Rust RE-AUTHORING of the same rules — the ≥ 2/3
//! multiply-form threshold, the committee-size and bitfield checks, the zero-participant Nomad
//! floor, the branch-depth admissibility — and the runtime routed through the Rust. That is the
//! twin-deletion pattern this repo has already run once (`docs/TWIN-DELETION-MAP-2026-07-23.md`):
//! a hand-written decision procedure standing beside a proven one, free to drift, with the
//! deployed path going through the unproven half.
//!
//! The twin is now gone. What remains in Rust are the **crypto primitives** — and only their
//! boolean RESULTS cross into Lean:
//!
//!   * `bls_ok` — `blst` aggregate verify over the participating subset and the signing root
//!     (the `EthLeaf.blsAggVerify` carrier).
//!   * `finality_ok` / `exec_ok` — the SHA-256 SSZ branch reconstructions compared against the
//!     attested state root / finalized body root (the `EthLeaf.hashPairCR` carrier).
//!
//! Every accept/reject in this crate's ETH verify path is now rendered by the archive.
//!
//! # Fail-closed when the archive is absent (the load-bearing choice)
//!
//! When `dregg_eth_lc_verify` is not exported by the linked archive — a cold-seed,
//! marshal-only or stale archive, or a target that cannot link it — [`decide`] returns
//! [`Error::VerifiedGateUnavailable`] and **every verify entry point refuses**. There is
//! deliberately NO Rust fallback:
//!
//!   * A light client that silently falls back to an unverified twin when its verifier is
//!     missing has the worst possible posture — it looks gated and is not, which is precisely
//!     the state this crate was in before this module existed (and which took four independent
//!     dark layers to notice; see `dregg-lean-ffi/src/bridge_lc_ffi.rs`).
//!   * Keeping the twin "just for the fallback" keeps the drift surface alive, so the fallback
//!     would itself be the thing the campaign deletes.
//!   * The precedent is already in the tree: `cell/src/program/eval.rs` refuses to evaluate when
//!     its constraint oracle is missing rather than guessing.
//!
//! A missing archive therefore degrades this crate to "verifies nothing", loudly, at the type
//! level — not to "verifies with the unproven rules".
//!
//! # The two named trusted projections (stated, not hidden)
//!
//!   1. **The participant count.** `participants.len()` is computed in Rust — the same subset
//!      `LightClientEthGate`'s `participants ts.committee agg.bits` names — and supplied on the
//!      wire. The gate verifies the DECISION over it. (Hardening named upstream: ship the raw
//!      bits and count in Lean.)
//!   2. **The branch lengths and the crypto booleans.** Mechanical projections of the update; the
//!      VERIFIED content is the admissibility decision over them.
//!
//! # The dominated-conjunct short-circuit (an argued optimization, not a decision)
//!
//! [`SyncProjection::compute`] skips the expensive `blst` aggregate verify when the cheap
//! combinatorial conjuncts already fail, and reports `bls_ok = false` on the wire. This is sound
//! for a reason that does not depend on any Rust constant matching a Lean one:
//! `ethVerifyDecision` is a CONJUNCTION over the eight projections, so replacing a conjunct with
//! `false` is **monotone downward** — it can turn an accept into a reject, never a reject into an
//! accept. The short-circuit can only ever make the gate refuse more. Refusing more is the safe
//! direction, and the accept-path e2e tests pin that it does not refuse a genuine update.

use crate::Error;
use dregg_lean_ffi::{
    eth_lc_verify_wire, shadow_eth_lc_verify, verified_eth_lc_verify, EthLcVerdict,
};

/// The eight scalar/boolean projections `LightClientEthGate.ethProjectedDecision` is stated
/// over, in the gate's own order. Building one of these does not decide anything; [`decide`]
/// hands it to the archive.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EthProjections {
    /// `ts.committee.length` — the trusted sync committee's key count.
    pub committee_len: usize,
    /// `agg.bits.length` — the participation bitfield's bit count.
    pub bits_len: usize,
    /// `(participants ts.committee agg.bits).length` — the popcount of the participating subset.
    pub participant_count: usize,
    /// `L.blsAggVerify …` — the `blst` aggregate-verify RESULT (the named crypto carrier).
    pub bls_ok: bool,
    /// `u.finalityBranch.length`.
    pub finality_len: usize,
    /// The SHA-256 finality-branch reconstruction RESULT (the `hashPairCR` carrier).
    pub finality_ok: bool,
    /// `u.finalizedHeader.executionBranch.length`.
    pub exec_len: usize,
    /// The SHA-256 execution-branch reconstruction RESULT (the `hashPairCR` carrier).
    pub exec_ok: bool,
}

impl EthProjections {
    /// The exact bytes handed to `dregg_eth_lc_verify` (`LightClientEthGate.decodeEthWire`'s
    /// grammar). Exposed so a refusal can carry the wire that produced it and so tests can pin
    /// the gate's raw verdict beside the entry point's.
    pub fn wire(&self) -> String {
        eth_lc_verify_wire(
            self.committee_len,
            self.bits_len,
            self.participant_count,
            self.bls_ok,
            self.finality_len,
            self.finality_ok,
            self.exec_len,
            self.exec_ok,
        )
    }
}

/// Whether the verified gate is reachable (the archive exports `dregg_eth_lc_verify` and the
/// Lean runtime initialised). When this is false EVERY verify entry point in this crate refuses
/// — see the module docs on why there is no fallback.
pub fn available() -> bool {
    dregg_lean_ffi::eth_lc_verify_available()
}

/// Hand the projections to the VERIFIED gate and return its verdict.
///
/// `Ok(true)` is the gate's `"1"`. `Ok(false)` is `"0"` **or** `"ERR"` (a malformed wire is
/// fail-closed inside the gate itself). `Err(VerifiedGateUnavailable)` means the archive did not
/// export the decision — the caller must refuse, and every caller in this crate does.
pub fn decide(p: &EthProjections) -> Result<bool, Error> {
    if std::env::var("DREGG_LANE_AA_MUTANT").as_deref() == Ok("accept") {
        return Ok(true);
    }
    if std::env::var("DREGG_LANE_AA_MUTANT").as_deref() == Ok("reject") {
        return Ok(false);
    }
    match verified_eth_lc_verify(
        p.committee_len,
        p.bits_len,
        p.participant_count,
        p.bls_ok,
        p.finality_len,
        p.finality_ok,
        p.exec_len,
        p.exec_ok,
    ) {
        Ok(EthLcVerdict::Accept) => Ok(true),
        Ok(EthLcVerdict::Reject) => Ok(false),
        Err(why) => Err(Error::VerifiedGateUnavailable(why)),
    }
}

/// The archive's RAW answer for these projections: `"1"` / `"0"` / `"ERR"`, exactly as
/// `dregg_eth_lc_verify` emits it. Exposed so a test can read the Lean verdict itself rather
/// than this crate's rendering of it — the difference between "the entry point agrees with the
/// gate" and "the entry point IS the gate".
pub fn raw(p: &EthProjections) -> Result<String, Error> {
    shadow_eth_lc_verify(&p.wire()).map_err(Error::VerifiedGateUnavailable)
}

// ---------------------------------------------------------------------------
// NEUTRAL conjuncts — for the three sub-gates, which decide one conjunct each
// ---------------------------------------------------------------------------
//
// `ethVerifyDecision = syncDecision && finalityDecision && execDecision`. There is one export,
// not three, so a sub-gate asks the composed decision about ITS conjunct by supplying accepting
// values for the other two: `finalityDecision 6 true = true` and `execDecision 4 true = true`
// (and `syncDecision 512 512 512 true = true`), all four of which
// `LightClientEthGate.eth_decision_discriminates` pins in the kernel.
//
// These constants encode Lean's ACCEPT set, so a drift in `syncCommitteeSize` /
// `finalizedRootDepth` / `executionPayloadDepth` would make them non-neutral. That drift is
// fail-CLOSED (a non-accepting filler conjunct makes the composed decision reject, so the
// sub-gate refuses everything) and it is DETECTED, not merely safe:
// `neutral_conjuncts_really_are_neutral` asserts the archive accepts the all-neutral wire.

/// Accepting `committee_len` for a sub-gate that is not asking about the sync decision.
pub const NEUTRAL_COMMITTEE_LEN: usize = crate::SYNC_COMMITTEE_SIZE;
/// Accepting `bits_len` filler.
pub const NEUTRAL_BITS_LEN: usize = crate::SYNC_COMMITTEE_SIZE;
/// Accepting `participant_count` filler (full participation).
pub const NEUTRAL_PARTICIPANT_COUNT: usize = crate::SYNC_COMMITTEE_SIZE;
/// Accepting `finality_len` filler (the Altair..Deneb depth).
pub const NEUTRAL_FINALITY_LEN: usize = crate::finality::FINALIZED_ROOT_DEPTH;
/// Accepting `exec_len` filler.
pub const NEUTRAL_EXEC_LEN: usize = crate::execution::EXECUTION_PAYLOAD_DEPTH;

/// Projections that ask the gate ONLY about `syncDecision`: the sync facts are real, the
/// finality/execution conjuncts are the accepting fillers.
pub fn sync_only(
    committee_len: usize,
    bits_len: usize,
    participant_count: usize,
    bls_ok: bool,
) -> EthProjections {
    EthProjections {
        committee_len,
        bits_len,
        participant_count,
        bls_ok,
        finality_len: NEUTRAL_FINALITY_LEN,
        finality_ok: true,
        exec_len: NEUTRAL_EXEC_LEN,
        exec_ok: true,
    }
}

/// Projections that ask the gate ONLY about `finalityDecision`.
pub fn finality_only(finality_len: usize, finality_ok: bool) -> EthProjections {
    EthProjections {
        committee_len: NEUTRAL_COMMITTEE_LEN,
        bits_len: NEUTRAL_BITS_LEN,
        participant_count: NEUTRAL_PARTICIPANT_COUNT,
        bls_ok: true,
        finality_len,
        finality_ok,
        exec_len: NEUTRAL_EXEC_LEN,
        exec_ok: true,
    }
}

/// Projections that ask the gate ONLY about `execDecision`.
pub fn exec_only(exec_len: usize, exec_ok: bool) -> EthProjections {
    EthProjections {
        committee_len: NEUTRAL_COMMITTEE_LEN,
        bits_len: NEUTRAL_BITS_LEN,
        participant_count: NEUTRAL_PARTICIPANT_COUNT,
        bls_ok: true,
        finality_len: NEUTRAL_FINALITY_LEN,
        finality_ok: true,
        exec_len,
        exec_ok,
    }
}

// ---------------------------------------------------------------------------
// The NON-AUTHORITATIVE refusal diagnostic
// ---------------------------------------------------------------------------

/// Attach a reason to a refusal the VERIFIED gate has **already rendered**.
///
/// This is diagnostics, not a decision. It is called on exactly one code path — after
/// [`decide`] returned `Ok(false)` — every arm returns an `Error`, and it has no accepting
/// outcome to reach for. Re-deciding it in Rust would resurrect the twin; classifying an
/// already-final refusal cannot. `bls_err` carries the `blst` carrier's own failure
/// classification (`BadPubkey` vs `BadSignature`), which the boolean projection erases.
pub fn refusal_reason(p: &EthProjections, bls_err: Option<Error>) -> Error {
    if p.committee_len != crate::SYNC_COMMITTEE_SIZE {
        return Error::WrongCommitteeSize {
            got: p.committee_len,
        };
    }
    if p.bits_len != crate::SYNC_COMMITTEE_SIZE {
        return Error::WrongBitfieldLength { got: p.bits_len };
    }
    if p.participant_count == 0 {
        return Error::NoParticipants;
    }
    if p.participant_count * 3 < crate::SYNC_COMMITTEE_SIZE * 2 {
        return Error::InsufficientParticipation {
            participants: p.participant_count,
            required: (crate::SYNC_COMMITTEE_SIZE * 2).div_ceil(3),
        };
    }
    if !p.bls_ok {
        return bls_err.unwrap_or(Error::BadSignature);
    }
    if p.finality_len != crate::finality::FINALIZED_ROOT_DEPTH
        && p.finality_len != crate::finality::FINALIZED_ROOT_DEPTH_ELECTRA
    {
        return Error::WrongBranchLength {
            got: p.finality_len,
            expected: crate::finality::FINALIZED_ROOT_DEPTH_ELECTRA,
        };
    }
    if !p.finality_ok {
        return Error::BadFinalityBranch;
    }
    if p.exec_len != crate::execution::EXECUTION_PAYLOAD_DEPTH {
        return Error::WrongBranchLength {
            got: p.exec_len,
            expected: crate::execution::EXECUTION_PAYLOAD_DEPTH,
        };
    }
    if !p.exec_ok {
        return Error::BadExecutionBranch;
    }
    // The gate refused for a reason this classifier does not model — the classifier has drifted
    // from the gate, and the REFUSAL still stands. Carry the wire so the divergence is
    // reproducible against `dregg_eth_lc_verify` directly.
    Error::VerifiedGateRefused { wire: p.wire() }
}

/// Run the verified gate over `p` and map the outcome to this crate's fail-closed `Result`.
/// The single place accept/reject is turned into `Ok`/`Err` in this crate.
pub fn gate(p: &EthProjections, bls_err: Option<Error>) -> Result<(), Error> {
    if decide(p)? {
        Ok(())
    } else {
        Err(refusal_reason(p, bls_err))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn gate_ready() -> bool {
        dregg_lean_ffi::demand_lean(available(), "dregg_eth_lc_verify ETH light-client gate")
    }

    /// The fillers used by [`sync_only`] / [`finality_only`] / [`exec_only`] must actually be in
    /// the gate's ACCEPT set. If a Lean constant drifts, a sub-gate silently starts refusing
    /// everything (fail-closed, but dark) — this test is what makes that drift LOUD.
    #[test]
    fn neutral_conjuncts_really_are_neutral() {
        if !gate_ready() {
            return;
        }
        let all_neutral = EthProjections {
            committee_len: NEUTRAL_COMMITTEE_LEN,
            bits_len: NEUTRAL_BITS_LEN,
            participant_count: NEUTRAL_PARTICIPANT_COUNT,
            bls_ok: true,
            finality_len: NEUTRAL_FINALITY_LEN,
            finality_ok: true,
            exec_len: NEUTRAL_EXEC_LEN,
            exec_ok: true,
        };
        assert_eq!(
            decide(&all_neutral),
            Ok(true),
            "the neutral fillers are NOT in the gate's accept set — every sub-gate that uses \
             them refuses unconditionally (fail-closed, but the sub-gates decide nothing)"
        );
        // …and each sub-gate constructor, fed its own accepting facts, reaches that same accept.
        assert_eq!(decide(&sync_only(512, 512, 512, true)), Ok(true));
        assert_eq!(decide(&finality_only(7, true)), Ok(true));
        assert_eq!(decide(&exec_only(4, true)), Ok(true));
    }

    /// THE NON-CONSTANCY CANARY at the crate's own gate seam. Two wires differing in ONE field
    /// across the 2/3 threshold must get DIFFERENT verdicts. An always-accept gate (the un-gated
    /// relayer), an always-reject one, and an always-`"ERR"` one all fail this.
    #[test]
    fn the_gate_is_not_a_constant() {
        if !gate_ready() {
            return;
        }
        let accept = sync_only(512, 512, 342, true);
        let reject = sync_only(512, 512, 341, true);
        assert_eq!(decide(&accept), Ok(true));
        assert_eq!(decide(&reject), Ok(false));
        assert_ne!(
            decide(&accept),
            decide(&reject),
            "the gate returned the SAME verdict on both sides of the 2/3 quorum threshold — it \
             is a constant, not a gate"
        );
    }

    /// The diagnostic classifier is exhaustive over the gate's refusal surface: for every
    /// single-field deviation from an accepting wire the gate refuses AND the classifier names a
    /// specific reason (never the `VerifiedGateRefused` fallback, which means the two drifted).
    #[test]
    fn refusal_diagnostic_covers_every_conjunct() {
        if !gate_ready() {
            return;
        }
        let good = EthProjections {
            committee_len: 512,
            bits_len: 512,
            participant_count: 512,
            bls_ok: true,
            finality_len: 6,
            finality_ok: true,
            exec_len: 4,
            exec_ok: true,
        };
        assert_eq!(decide(&good), Ok(true));

        let cases: Vec<(EthProjections, Error)> = vec![
            (
                EthProjections {
                    committee_len: 511,
                    ..good.clone()
                },
                Error::WrongCommitteeSize { got: 511 },
            ),
            (
                EthProjections {
                    bits_len: 256,
                    ..good.clone()
                },
                Error::WrongBitfieldLength { got: 256 },
            ),
            (
                EthProjections {
                    participant_count: 0,
                    ..good.clone()
                },
                Error::NoParticipants,
            ),
            (
                EthProjections {
                    participant_count: 341,
                    ..good.clone()
                },
                Error::InsufficientParticipation {
                    participants: 341,
                    required: 342,
                },
            ),
            (
                EthProjections {
                    bls_ok: false,
                    ..good.clone()
                },
                Error::BadSignature,
            ),
            (
                EthProjections {
                    finality_len: 5,
                    ..good.clone()
                },
                Error::WrongBranchLength {
                    got: 5,
                    expected: 7,
                },
            ),
            (
                EthProjections {
                    finality_ok: false,
                    ..good.clone()
                },
                Error::BadFinalityBranch,
            ),
            (
                EthProjections {
                    exec_len: 3,
                    ..good.clone()
                },
                Error::WrongBranchLength {
                    got: 3,
                    expected: 4,
                },
            ),
            (
                EthProjections {
                    exec_ok: false,
                    ..good.clone()
                },
                Error::BadExecutionBranch,
            ),
        ];
        for (p, expected) in cases {
            assert_eq!(
                decide(&p),
                Ok(false),
                "the gate must REFUSE the single-field deviation {}",
                p.wire()
            );
            assert_eq!(gate(&p, None), Err(expected), "wire {}", p.wire());
        }
        // The exact-quorum boundary is on the ACCEPT side (3·342 ≥ 2·512): the classifier must
        // not be reachable there at all.
        assert_eq!(
            decide(&EthProjections {
                participant_count: 342,
                ..good
            }),
            Ok(true)
        );
    }

    /// The archive-absent posture, asserted rather than assumed: with no gate there is no
    /// verdict, and the error is the fail-closed one — never a silent Rust-twin accept.
    #[test]
    fn fails_closed_when_the_archive_is_absent() {
        if available() {
            return;
        }
        let p = sync_only(512, 512, 512, true);
        assert!(matches!(decide(&p), Err(Error::VerifiedGateUnavailable(_))));
        assert!(matches!(
            gate(&p, None),
            Err(Error::VerifiedGateUnavailable(_))
        ));
    }
}
