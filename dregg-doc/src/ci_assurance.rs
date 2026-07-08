//! PLURALISTIC CI ASSURANCE — a documented lattice of dispute-resolution
//! strategies for a work-binding CI check ([`crate::ci_verdict`]).
//!
//! ## The problem this solves (the scholar-review hole)
//!
//! [`crate::check::CheckRequirement::CiRun`] binds a [`crate::CiVerdict`] to the
//! PR's real code inside a signed turn — but "signed by a trusted key" is only
//! the WEAKEST honest-host guarantee: a lying host IS the trusted executor and
//! can sign a well-formed-but-fabricated `output_digest`. Catching that is a
//! spectrum, not a single mechanism: you can re-execute and compare, wait out a
//! fraud-proof challenge window, verify a proof-of-execution, or bond the claim.
//! Each has a DIFFERENT cost / latency / trust tradeoff.
//!
//! Rather than hard-wire one point on that spectrum (or force a repo author to
//! squint at the tradeoff-space), [`CiAssurance`] makes the *assurance level* a
//! first-class, pluggable choice. A repo dials the assurance it wants; the
//! tradeoff of each rung is documented AT THE TYPE (a uniform block: trust
//! assumption / cost / latency / determinism dependence / catches a lying
//! host?), so the enum is self-documenting — you read the variant and know what
//! you are buying.
//!
//! ## The lattice (weakest/cheapest → strongest/costliest)
//!
//! 1. [`CiAssurance::TrustedSigned`] — one trusted-key-signed work-bound verdict
//!    (today's L1). Detection is out-of-band.
//! 2. [`CiAssurance::ReExecuted`] — the verdict PLUS `quorum` independent
//!    re-execution attestations that must all agree; a divergent attestation is
//!    a [`Conviction`]. The real "catches a lying host via agreement" rung.
//! 3. [`CiAssurance::OptimisticChallenge`] — accepted provisionally, satisfied
//!    only once a fraud-proof challenge window has elapsed with no conviction.
//! 4. [`CiAssurance::Proven`] — the verdict carries a proof-of-execution; verify
//!    the proof, no re-execution or dispute needed.
//! 5. [`CiAssurance::Staked`] — a WRAPPER: any inner policy plus a bond that is
//!    forfeit when the inner policy convicts a lie.
//!
//! ## What is fully wired vs. interface-real (named seams)
//!
//! - **Fully wired**: `TrustedSigned` (signature + active-key set), `ReExecuted`
//!   (quorum of distinct-active-key, turn-bound, same-work attestations; a
//!   divergent one convicts), the `OptimisticChallenge` height/conviction gate,
//!   the `Staked` composition (delegates to `inner`, binds `bond_ref`, surfaces
//!   the [`Conviction`]), and the [`GovernedKeySet`] rotation/revocation gate.
//! - **Interface-real, execution deferred (named seams)**:
//!   - `Proven`'s prover — [`verify_ci_proof`] is an honest STUB behind the
//!     [`CiProofVerifier`] trait; a real zk/STARK-of-execution drops in there
//!     (the heavy R3 seam). The POLICY and plumbing are real: a valid
//!     proof-hook-return satisfies, an invalid one refuses.
//!   - `OptimisticChallenge`'s live dispute transport — the gossip/challenge
//!     network that WRITES a [`ChallengeContext::conviction`] is out-of-crate;
//!     the height/conviction gate here actually gates on what it is told.
//!   - `Staked`'s slash-transfer — the escrow-market / stake-cell that MOVES the
//!     forfeit bond is out-of-crate; the [`Conviction`]-carrying outcome and the
//!     `bond_ref` binding are real and typed.

use crate::ci_verdict::{CiVerdict, planned_ci_run_hash};
use dregg_turn::{Finality, TurnReceipt, verify_receipt_signature_with_keys};

// ─────────────────────────────────────────────────────────────────────────────
// The governed trusted-executor key set (Finding-3): NOT a bare `Vec`.
// ─────────────────────────────────────────────────────────────────────────────

/// One entry in a [`GovernedKeySet`]: a trusted-executor Ed25519 verifying key,
/// the epoch it was admitted at, and whether it has been revoked.
///
/// A revoked key's verdicts stop satisfying — [`GovernedKeySet::active_keys`]
/// excludes it, so a receipt signed only by a revoked key fails the
/// signature-verify gate ([`crate::check::CheckRefusal::SignatureUnverified`]).
/// This is KEY ROTATION: revoke the old key, admit the new one, and in-flight
/// verdicts signed by the retired key no longer pass.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrustedKey {
    /// The Ed25519 verifying-key bytes.
    pub key: [u8; 32],
    /// The governance epoch this key was admitted at (monotone; a rotation bumps
    /// the epoch of the incoming key).
    pub added_epoch: u64,
    /// Whether this key has been revoked (a revoked key never satisfies).
    pub revoked: bool,
}

/// WHO may add/remove a trusted-executor key — the governance seam
/// (Finding-3). The membership of the trusted set is not ambient: changing it is
/// itself a governed action (a `governed-namespace` threshold swap). This field
/// NAMES that seam as a typed policy so the deployment binds it; the actual
/// threshold-signature admission/eviction transport is out-of-crate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KeyGovernance {
    /// A fixed set, mutable only by an out-of-band operator (the simplest repo
    /// policy — the trusted set is repo config).
    Operator,
    /// The set is governed by a threshold over a named governance namespace: a
    /// key add/remove requires `threshold`-of-N approvals from the namespace's
    /// members. The transport (the threshold-signature swap) is the named seam;
    /// this records the intended policy at the type.
    GovernedNamespace {
        /// The governance namespace id (who the members are).
        namespace: [u8; 32],
        /// How many approvals a key add/remove requires.
        threshold: u16,
    },
}

/// THE TRUSTED-EXECUTOR KEY SET as a first-class GOVERNED SET (Finding-3), not a
/// bare `Vec<[u8;32]>`: it carries per-key revocation/epoch and a
/// [`KeyGovernance`] policy naming who may rotate it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GovernedKeySet {
    /// The trusted keys (some possibly revoked).
    pub entries: Vec<TrustedKey>,
    /// The governance policy: who may add/remove a key (the named rotation seam).
    pub governance: KeyGovernance,
}

impl GovernedKeySet {
    /// A set of operator-governed keys, all admitted at epoch 0, none revoked —
    /// the ergonomic constructor matching the old bare-`Vec` shape.
    pub fn operator(keys: impl IntoIterator<Item = [u8; 32]>) -> Self {
        GovernedKeySet {
            entries: keys
                .into_iter()
                .map(|key| TrustedKey {
                    key,
                    added_epoch: 0,
                    revoked: false,
                })
                .collect(),
            governance: KeyGovernance::Operator,
        }
    }

    /// The threshold-governed constructor: the set is mutated only by
    /// `threshold`-of-N approvals over `namespace` (the named governance seam).
    pub fn governed(
        keys: impl IntoIterator<Item = [u8; 32]>,
        namespace: [u8; 32],
        threshold: u16,
    ) -> Self {
        let mut s = GovernedKeySet::operator(keys);
        s.governance = KeyGovernance::GovernedNamespace {
            namespace,
            threshold,
        };
        s
    }

    /// The currently-ACTIVE keys (non-revoked). A signature that verifies only
    /// against a revoked key is refused — this is the revocation gate.
    pub fn active_keys(&self) -> Vec<[u8; 32]> {
        self.entries
            .iter()
            .filter(|e| !e.revoked)
            .map(|e| e.key)
            .collect()
    }

    /// Revoke `key` (idempotent). A ROTATION step: after revoking, the retired
    /// key's verdicts stop satisfying. Returns `true` if a matching active key
    /// was found and revoked.
    pub fn revoke(&mut self, key: &[u8; 32]) -> bool {
        let mut hit = false;
        for e in &mut self.entries {
            if &e.key == key && !e.revoked {
                e.revoked = true;
                hit = true;
            }
        }
        hit
    }

    /// Admit a fresh key at `epoch` (the incoming half of a rotation).
    pub fn admit(&mut self, key: [u8; 32], epoch: u64) {
        self.entries.push(TrustedKey {
            key,
            added_epoch: epoch,
            revoked: false,
        });
    }

    /// KEY ROTATION in one step: revoke `old`, admit `new` at `epoch`.
    pub fn rotate(&mut self, old: &[u8; 32], new: [u8; 32], epoch: u64) {
        self.revoke(old);
        self.admit(new, epoch);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Proof-of-execution (the `Proven` rung): interface-real, prover-deferred.
// ─────────────────────────────────────────────────────────────────────────────

/// A PROOF-OF-EXECUTION carried alongside a [`CiVerdict`] for the
/// [`CiAssurance::Proven`] rung: a proof that running the command produced the
/// committed `output_digest`. The real payload is a zk/STARK proof; here the
/// bytes are opaque and checked by [`verify_ci_proof`] (the deferred prover seam).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CiExecutionProof {
    /// The verifying key this proof is against (must equal the check's
    /// `Proven { verifying_key }`).
    pub proving_vk: [u8; 32],
    /// The output digest the proof asserts the execution produced (must equal
    /// the verdict's `output_digest`).
    pub asserted_output: [u8; 32],
    /// The opaque proof bytes (a real STARK proof; the STUB verifier requires
    /// them non-empty).
    pub proof_bytes: Vec<u8>,
}

/// THE PROVER SEAM (R3): verify a [`CiExecutionProof`] against a verifying key
/// and the verdict it claims. A real zk/STARK-of-execution verifier implements
/// this; drop it in and the `Proven` policy needs no other change.
pub trait CiProofVerifier {
    /// `true` iff `proof` is a valid proof, under `verifying_key`, that the
    /// execution produced `verdict.output_digest`.
    fn verify(
        &self,
        verifying_key: &[u8; 32],
        verdict: &CiVerdict,
        proof: &CiExecutionProof,
    ) -> bool;
}

/// The HONEST STUB verifier: the plumbing is real (a matching, well-formed proof
/// verifies; a mismatched or empty one refuses) but it does NOT check a real
/// cryptographic proof — a real [`CiProofVerifier`] replaces it. It accepts iff
/// the proof is against the expected vk, asserts the verdict's exact output, and
/// carries non-empty proof bytes.
#[derive(Clone, Debug, Default)]
pub struct StubProofVerifier;

impl CiProofVerifier for StubProofVerifier {
    fn verify(
        &self,
        verifying_key: &[u8; 32],
        verdict: &CiVerdict,
        proof: &CiExecutionProof,
    ) -> bool {
        proof.proving_vk == *verifying_key
            && proof.asserted_output == verdict.output_digest
            && !proof.proof_bytes.is_empty()
    }
}

/// Verify a CI execution proof through the default ([`StubProofVerifier`]) hook.
/// This is the function the `Proven` policy calls; swapping the trait impl in a
/// deployment swaps the prover with no policy change (the deferred R3 seam).
pub fn verify_ci_proof(
    verifying_key: &[u8; 32],
    verdict: &CiVerdict,
    proof: &CiExecutionProof,
) -> bool {
    StubProofVerifier.verify(verifying_key, verdict, proof)
}

// ─────────────────────────────────────────────────────────────────────────────
// Convictions + the optimistic-challenge context.
// ─────────────────────────────────────────────────────────────────────────────

/// A bond identifier for [`CiAssurance::Staked`] — the reference to the stake
/// that is forfeit when the inner policy convicts a lie. The escrow that holds
/// and MOVES the bond is out-of-crate (the named slash-transfer seam); this is
/// the typed handle that binds a conviction to a specific bond.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BondRef(pub [u8; 32]);

/// WHAT proved a lie — the evidence carried by a [`Conviction`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConvictionEvidence {
    /// A re-execution attestation over the SAME work reported a DIFFERENT
    /// `output_digest` than the verdict — agreement failed, so a host lied.
    ReExecDivergence {
        /// The verdict's claimed output digest.
        claimed: [u8; 32],
        /// The divergent attestation's output digest.
        divergent: [u8; 32],
        /// The trusted key that signed the divergent attestation.
        signer: [u8; 32],
    },
    /// A challenge was upheld during the optimistic window (a fraud proof landed).
    ChallengeUpheld {
        /// A digest identifying the upheld challenge (opaque here — the dispute
        /// transport's evidence handle).
        challenge_id: [u8; 32],
    },
}

/// A CONVICTION: the policy proved a lie. Carries the evidence and, when the
/// policy was [`CiAssurance::Staked`], the `bond_ref` that is now forfeit. A
/// conviction is a REFUSAL (the check is not satisfied) that additionally names
/// what to slash — the transfer itself is the deferred seam.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Conviction {
    /// The bond forfeit by this conviction, if the policy was `Staked`.
    pub bond_ref: Option<BondRef>,
    /// The evidence that proved the lie.
    pub evidence: ConvictionEvidence,
}

/// The optimistic-challenge context for [`CiAssurance::OptimisticChallenge`]:
/// where in the challenge window the verdict is, and whether a conviction has
/// been recorded. The live gossip/dispute transport that WRITES `conviction` is
/// the named seam; the height/conviction gate here gates on what it is told.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChallengeContext {
    /// The height the verdict was posted (accepted provisionally) at.
    pub posted_height: u64,
    /// The current height (the verifier's clock).
    pub now_height: u64,
    /// A recorded conviction, if a challenge was upheld during the window.
    pub conviction: Option<ConvictionEvidence>,
}

// ─────────────────────────────────────────────────────────────────────────────
// The assurance lattice.
// ─────────────────────────────────────────────────────────────────────────────

/// THE PLURALISTIC CI-ASSURANCE LATTICE. Each variant is a distinct
/// dispute-resolution strategy carrying its own params, documented with a
/// uniform tradeoff block so the enum is self-documenting. Ordered
/// weakest/cheapest → strongest/costliest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CiAssurance {
    /// **L1 — a single trusted-key-signed, work-bound verdict** (today's `CiRun`).
    /// The verdict is bound to the PR's code inside a signed turn; that is all.
    ///
    /// # Trust assumption
    /// The trusted host signs truthfully — it ran the command and reported the
    /// real output. A lying host (which IS the signer) is NOT caught here.
    /// # Cost
    /// One execution, one signature. Cheapest.
    /// # Latency
    /// Immediate — satisfied the moment the signed verdict is presented.
    /// # Determinism dependence
    /// None — no output is ever compared, so a non-deterministic build is fine.
    /// # Catches a lying host?
    /// NO. Detection is out-of-band (audit / slashing after the fact).
    TrustedSigned {
        /// The governed trusted-executor key set (the primary must be signed by
        /// an active key).
        keys: GovernedKeySet,
    },

    /// **L2 — re-executed to quorum**: the verdict PLUS `quorum` INDEPENDENT
    /// re-execution attestations (each a signed [`CiVerdict`] from a DISTINCT
    /// active key over the SAME `input_root`+`command_id`) whose `output_digest`
    /// all MATCH; a divergent attestation is a [`Conviction`]. `quorum == 1` is a
    /// single re-exec; `quorum == N` is N-of agreement.
    ///
    /// # Trust assumption
    /// At least `quorum` independent executors are honest AND the build is
    /// reproducible; a single lying host cannot fake agreement it does not
    /// control.
    /// # Cost
    /// `quorum + 1` executions + signatures. Linear in `quorum`.
    /// # Latency
    /// Waits for `quorum` re-executions to finish and report.
    /// # Determinism dependence
    /// HIGH — the outputs must be byte-identical, so the command must be
    /// reproducible (same digest across independent runs).
    /// # Catches a lying host?
    /// YES, via agreement — a fabricated `output_digest` diverges from honest
    /// re-executions and convicts. This is the real detection rung.
    ReExecuted {
        /// The governed trusted-executor key set (primary + every attestation
        /// must be signed by DISTINCT active keys).
        keys: GovernedKeySet,
        /// How many distinct-key matching re-execution attestations are required.
        quorum: u8,
    },

    /// **L2.5 — optimistic with a fraud-proof challenge window**: accepted
    /// provisionally, satisfied only once the current height is past
    /// `posted_height + challenge_window_height` with NO recorded conviction. A
    /// challenge upheld during the window is a [`Conviction`].
    ///
    /// # Trust assumption
    /// At least one honest watcher will challenge a lie within the window; an
    /// unchallenged claim is presumed honest once the window closes.
    /// # Cost
    /// One execution normally; a re-execution only WHEN challenged (cheap in the
    /// common no-fraud case).
    /// # Latency
    /// HIGH — must wait out the whole challenge window before it can land.
    /// # Determinism dependence
    /// Only when challenged (a dispute re-executes and compares); the happy path
    /// compares nothing.
    /// # Catches a lying host?
    /// YES, IF someone challenges in time — the window/conviction gate is real;
    /// the live dispute transport that records the conviction is the named seam.
    OptimisticChallenge {
        /// The governed trusted-executor key set (the provisional primary must be
        /// signed by an active key).
        keys: GovernedKeySet,
        /// How many heights the challenge window lasts.
        challenge_window_height: u64,
    },

    /// **L3 — proven**: the verdict carries a [`CiExecutionProof`] that the
    /// execution produced the committed `output_digest`; satisfied by verifying
    /// the proof ([`verify_ci_proof`]) — NO re-execution or dispute needed.
    ///
    /// # Trust assumption
    /// Only the soundness of the proof system and `verifying_key` — NO trust in
    /// the host at all (it cannot forge a valid proof of a false output).
    /// # Cost
    /// One (expensive) proving run + one (cheap) verification. Proving is heavy.
    /// # Latency
    /// The proving time up front, then immediate verification.
    /// # Determinism dependence
    /// None on re-execution — the proof binds the exact output; the host need
    /// not be re-run.
    /// # Catches a lying host?
    /// YES, unconditionally — a false output has no valid proof. Strongest.
    Proven {
        /// The verifying key the [`CiExecutionProof`] must verify against.
        verifying_key: [u8; 32],
    },

    /// **Wrapper — staked**: any inner policy PLUS a bond that is forfeit when
    /// the inner policy CONVICTS a lie. Composes with every rung: it does not
    /// change WHEN the inner policy is satisfied, it adds economic skin so a
    /// caught lie has a cost.
    ///
    /// # Trust assumption
    /// The inner policy's, PLUS that the bond is large enough to deter a lie
    /// (economic security on top of the inner cryptographic/agreement security).
    /// # Cost
    /// The inner policy's cost PLUS locking the bond capital.
    /// # Latency
    /// The inner policy's latency (staking adds none to satisfaction).
    /// # Determinism dependence
    /// The inner policy's.
    /// # Catches a lying host?
    /// As the inner policy does — and additionally SLASHES it when caught. The
    /// slash-transfer itself is the named seam; the conviction + `bond_ref`
    /// binding is real.
    Staked {
        /// The bond forfeit on an inner conviction.
        bond_ref: BondRef,
        /// The wrapped policy that actually decides satisfaction/conviction.
        inner: Box<CiAssurance>,
    },
}

/// The inputs an assurance policy evaluates: the primary CI-run receipt+verdict
/// (already work-bound by the caller) plus the extra witness data richer rungs
/// need (re-execution attestations, a proof, a challenge context) and the
/// CI-run region cell identity used to re-derive+bind attestation turns.
pub struct AssuranceInput<'a> {
    /// The primary committed CI-run receipt.
    pub receipt: &'a TurnReceipt,
    /// The verdict that receipt's turn committed (bound + shape-checked by the
    /// caller: command_id / input_root / exit_code / turn-hash binding).
    pub verdict: &'a CiVerdict,
    /// Independent re-execution attestations (for [`CiAssurance::ReExecuted`]).
    pub attestations: &'a [(TurnReceipt, CiVerdict)],
    /// The execution proof, if any (for [`CiAssurance::Proven`]).
    pub proof: Option<&'a CiExecutionProof>,
    /// The challenge context, if any (for [`CiAssurance::OptimisticChallenge`]).
    pub challenge: Option<&'a ChallengeContext>,
    /// The CI-run region cell's editor identity seed (to re-derive attestation
    /// turn hashes — see [`crate::ci_verdict::planned_ci_run_hash`]).
    pub editor_seed: u8,
    /// The CI-run region cell's region identity seed.
    pub region_seed: u8,
}

/// The result of evaluating a [`CiAssurance`] policy.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AssuranceOutcome {
    /// The policy is satisfied — the verdict may land.
    Satisfied,
    /// The policy is NOT (yet) satisfied, but no lie is proven — short quorum,
    /// still inside the challenge window, an invalid proof, or missing witness
    /// data. Carries a human-legible reason.
    Unmet(String),
    /// The policy PROVED a lie (divergent re-execution / an upheld challenge).
    /// A refusal that additionally names what to slash (`bond_ref` when staked).
    Convicted(Conviction),
}

impl CiAssurance {
    /// TrustedSigned over an operator-governed key set — the ergonomic
    /// constructor matching the old bare-`Vec` `CiRun` shape (today's L1).
    pub fn trusted_signed(keys: impl IntoIterator<Item = [u8; 32]>) -> Self {
        CiAssurance::TrustedSigned {
            keys: GovernedKeySet::operator(keys),
        }
    }

    /// The active trusted keys the PRIMARY receipt must be signed by, or `None`
    /// for a proof-only policy ([`CiAssurance::Proven`], which trusts no host
    /// key). `Staked` delegates to its inner policy.
    pub fn primary_active_keys(&self) -> Option<Vec<[u8; 32]>> {
        match self {
            CiAssurance::TrustedSigned { keys }
            | CiAssurance::ReExecuted { keys, .. }
            | CiAssurance::OptimisticChallenge { keys, .. } => Some(keys.active_keys()),
            CiAssurance::Proven { .. } => None,
            CiAssurance::Staked { inner, .. } => inner.primary_active_keys(),
        }
    }

    /// EVALUATE this policy against the witness. The caller has ALREADY bound the
    /// primary verdict to the PR's code (command_id / input_root / exit_code /
    /// turn-hash) and verified the primary signature against
    /// [`CiAssurance::primary_active_keys`]; this decides the assurance-specific
    /// dispute-resolution question (agreement / window / proof / stake).
    pub fn evaluate(&self, input: &AssuranceInput<'_>) -> AssuranceOutcome {
        match self {
            // L1: the primary signature (checked by the caller) IS the assurance.
            CiAssurance::TrustedSigned { .. } => AssuranceOutcome::Satisfied,

            // L2: require `quorum` distinct-active-key, turn-bound, same-work
            // matching attestations; a divergent one convicts.
            CiAssurance::ReExecuted { keys, quorum } => {
                let active = keys.active_keys();
                let mut matching_signers: Vec<[u8; 32]> = Vec::new();
                for (att_receipt, att_verdict) in input.attestations {
                    // Only a genuine trusted attestation counts: finalized,
                    // signed by an ACTIVE key, turn-bound to its own verdict,
                    // over the SAME work (command_id + input_root).
                    if att_receipt.finality != Finality::Final {
                        continue;
                    }
                    let Some(signer) = signing_key_of(att_receipt, &active) else {
                        continue;
                    };
                    let bound =
                        planned_ci_run_hash(input.editor_seed, input.region_seed, att_verdict)
                            .map(|h| h == att_receipt.turn_hash)
                            .unwrap_or(false);
                    if !bound {
                        continue;
                    }
                    if att_verdict.command_id != input.verdict.command_id
                        || att_verdict.input_root != input.verdict.input_root
                    {
                        continue;
                    }
                    // Same work, genuine attestation: does it AGREE?
                    if att_verdict.output_digest != input.verdict.output_digest {
                        return AssuranceOutcome::Convicted(Conviction {
                            bond_ref: None,
                            evidence: ConvictionEvidence::ReExecDivergence {
                                claimed: input.verdict.output_digest,
                                divergent: att_verdict.output_digest,
                                signer,
                            },
                        });
                    }
                    if !matching_signers.contains(&signer) {
                        matching_signers.push(signer);
                    }
                }
                if (matching_signers.len() as u64) >= u64::from(*quorum) {
                    AssuranceOutcome::Satisfied
                } else {
                    AssuranceOutcome::Unmet(format!(
                        "re-execution quorum not met: {} distinct-key matching attestations, need {}",
                        matching_signers.len(),
                        quorum
                    ))
                }
            }

            // L2.5: satisfied iff past the window with no recorded conviction.
            CiAssurance::OptimisticChallenge {
                challenge_window_height,
                ..
            } => {
                let Some(ctx) = input.challenge else {
                    return AssuranceOutcome::Unmet(
                        "optimistic challenge: no challenge context presented".to_string(),
                    );
                };
                if let Some(evidence) = &ctx.conviction {
                    return AssuranceOutcome::Convicted(Conviction {
                        bond_ref: None,
                        evidence: evidence.clone(),
                    });
                }
                let ready_at = ctx.posted_height.saturating_add(*challenge_window_height);
                if ctx.now_height >= ready_at {
                    AssuranceOutcome::Satisfied
                } else {
                    AssuranceOutcome::Unmet(format!(
                        "inside challenge window: now {} < ready {} (posted {} + window {})",
                        ctx.now_height, ready_at, ctx.posted_height, challenge_window_height
                    ))
                }
            }

            // L3: verify the proof-of-execution; no re-exec / dispute.
            CiAssurance::Proven { verifying_key } => {
                let Some(proof) = input.proof else {
                    return AssuranceOutcome::Unmet(
                        "proven: no execution proof presented".to_string(),
                    );
                };
                if verify_ci_proof(verifying_key, input.verdict, proof) {
                    AssuranceOutcome::Satisfied
                } else {
                    AssuranceOutcome::Unmet("proven: execution proof invalid".to_string())
                }
            }

            // Wrapper: delegate, then bind the bond on an inner conviction.
            CiAssurance::Staked { bond_ref, inner } => match inner.evaluate(input) {
                AssuranceOutcome::Satisfied => AssuranceOutcome::Satisfied,
                AssuranceOutcome::Unmet(why) => AssuranceOutcome::Unmet(why),
                AssuranceOutcome::Convicted(mut c) => {
                    // The inner policy caught a lie: this bond is now forfeit.
                    c.bond_ref = Some(*bond_ref);
                    AssuranceOutcome::Convicted(c)
                }
            },
        }
    }
}

/// Which of `active` keys signed `receipt` (the first that verifies), or `None`.
/// Per-key verification is how [`CiAssurance::ReExecuted`] counts DISTINCT
/// signers for its quorum.
fn signing_key_of(receipt: &TurnReceipt, active: &[[u8; 32]]) -> Option<[u8; 32]> {
    if receipt.executor_signature.is_none() {
        return None;
    }
    active
        .iter()
        .copied()
        .find(|k| verify_receipt_signature_with_keys(receipt, &[*k]).is_ok())
}

#[cfg(all(test, feature = "substrate"))]
mod tests {
    use super::*;
    use crate::check::{CheckRefusal, CheckWitness, CiRunWitness, RequiredCheck};
    use crate::ci_verdict::run_ci_verdict;

    // The CI-run region cell identity (repo policy; the verifier rebuilds it).
    const CI_EDITOR: u8 = 7;
    const CI_REGION: u8 = 8;
    const COMMAND: [u8; 32] = [0x11; 32];
    const CONFINEMENT: [u8; 32] = [0xC0; 32];
    const OUTPUT: [u8; 32] = [0xD1; 32];
    // A non-empty PR input root — the code the CI ran on (all verdicts bind it).
    const INPUT: [u8; 32] = [0x22; 32];
    const BOND: BondRef = BondRef([0xB0; 32]);

    // Four distinct executor signing seeds → four distinct trusted keys.
    const S1: [u8; 32] = [1; 32];
    const S2: [u8; 32] = [2; 32];
    const S3: [u8; 32] = [3; 32];
    const S4: [u8; 32] = [4; 32];

    /// The Ed25519 verifying key for a signing seed (standard keygen).
    fn vk(seed: [u8; 32]) -> [u8; 32] {
        ed25519_dalek::SigningKey::from_bytes(&seed)
            .verifying_key()
            .to_bytes()
    }

    fn verdict(output: [u8; 32]) -> CiVerdict {
        CiVerdict {
            input_root: INPUT,
            command_id: COMMAND,
            confinement_id: CONFINEMENT,
            exit_code: 0,
            output_digest: output,
        }
    }

    /// A signed, committed CI-run `(receipt, verdict)` for `seed` over `output`.
    fn run(seed: [u8; 32], output: [u8; 32]) -> (TurnReceipt, CiVerdict) {
        let v = verdict(output);
        let r = run_ci_verdict(CI_EDITOR, CI_REGION, seed, &v).expect("CI run commits");
        (r, v)
    }

    /// Verify a witness against a `CiRun` check dialed to `assurance`.
    fn satisfied(assurance: CiAssurance, witness: CiRunWitness) -> Result<(), CheckRefusal> {
        RequiredCheck::ci_run_assured("build", COMMAND, CI_EDITOR, CI_REGION, assurance)
            .satisfied_by(&CheckWitness::CiRun(witness), INPUT)
    }

    // ── POLE (i): TrustedSigned still satisfies (the L1 regression). ──────────
    #[test]
    fn trusted_signed_still_satisfies() {
        let (receipt, v) = run(S1, OUTPUT);
        let a = CiAssurance::TrustedSigned {
            keys: GovernedKeySet::operator([vk(S1)]),
        };
        satisfied(a, CiRunWitness::signed(receipt, v))
            .expect("a signed, work-bound verdict satisfies L1");
    }

    // ── POLE (ii): ReExecuted{quorum:3} — agreement satisfies; short quorum ──
    //    refuses (AssuranceUnmet); a divergent attestation convicts.
    #[test]
    fn re_executed_quorum_agreement_short_quorum_and_divergence() {
        let keys = GovernedKeySet::operator([vk(S1), vk(S2), vk(S3), vk(S4)]);
        let policy = || CiAssurance::ReExecuted {
            keys: keys.clone(),
            quorum: 3,
        };
        let (primary, pv) = run(S1, OUTPUT);

        // 3 DISTINCT-key matching re-executions → satisfied.
        let three = vec![run(S2, OUTPUT), run(S3, OUTPUT), run(S4, OUTPUT)];
        satisfied(
            policy(),
            CiRunWitness::signed(primary.clone(), pv.clone()).with_attestations(three),
        )
        .expect("three matching independent re-executions meet quorum 3");

        // Only 2 matching → short quorum → AssuranceUnmet (not a conviction).
        let two = vec![run(S2, OUTPUT), run(S3, OUTPUT)];
        match satisfied(
            policy(),
            CiRunWitness::signed(primary.clone(), pv.clone()).with_attestations(two),
        ) {
            Err(CheckRefusal::AssuranceUnmet(why)) => assert!(why.contains("quorum"), "{why}"),
            other => panic!("expected AssuranceUnmet, got {other:?}"),
        }

        // A divergent attestation (same work, DIFFERENT output) → conviction.
        let divergent_out = [0xEE; 32];
        let with_divergence = vec![run(S2, OUTPUT), run(S3, OUTPUT), run(S4, divergent_out)];
        match satisfied(
            policy(),
            CiRunWitness::signed(primary, pv).with_attestations(with_divergence),
        ) {
            Err(CheckRefusal::Convicted(c)) => {
                assert_eq!(c.bond_ref, None, "an unstaked policy names no bond");
                match c.evidence {
                    ConvictionEvidence::ReExecDivergence {
                        claimed,
                        divergent,
                        signer,
                    } => {
                        assert_eq!(claimed, OUTPUT);
                        assert_eq!(divergent, divergent_out);
                        assert_eq!(signer, vk(S4));
                    }
                    other => panic!("expected ReExecDivergence, got {other:?}"),
                }
            }
            other => panic!("expected Convicted, got {other:?}"),
        }
    }

    // ── POLE (iii): OptimisticChallenge — inside window refused; past window ──
    //    unconvicted satisfies; a recorded conviction refuses.
    #[test]
    fn optimistic_challenge_window_and_conviction() {
        let policy = || CiAssurance::OptimisticChallenge {
            keys: GovernedKeySet::operator([vk(S1)]),
            challenge_window_height: 10,
        };
        let (receipt, v) = run(S1, OUTPUT);

        // Inside the window (now 105 < posted 100 + 10) → unmet.
        let inside = ChallengeContext {
            posted_height: 100,
            now_height: 105,
            conviction: None,
        };
        match satisfied(
            policy(),
            CiRunWitness::signed(receipt.clone(), v.clone()).with_challenge(inside),
        ) {
            Err(CheckRefusal::AssuranceUnmet(why)) => assert!(why.contains("window"), "{why}"),
            other => panic!("expected AssuranceUnmet inside window, got {other:?}"),
        }

        // Past the window, unconvicted → satisfied.
        let past = ChallengeContext {
            posted_height: 100,
            now_height: 110,
            conviction: None,
        };
        satisfied(
            policy(),
            CiRunWitness::signed(receipt.clone(), v.clone()).with_challenge(past),
        )
        .expect("past the challenge window with no conviction satisfies");

        // A recorded conviction refuses even past the window.
        let convicted = ChallengeContext {
            posted_height: 100,
            now_height: 999,
            conviction: Some(ConvictionEvidence::ChallengeUpheld {
                challenge_id: [0x7C; 32],
            }),
        };
        match satisfied(
            policy(),
            CiRunWitness::signed(receipt, v).with_challenge(convicted),
        ) {
            Err(CheckRefusal::Convicted(c)) => assert!(matches!(
                c.evidence,
                ConvictionEvidence::ChallengeUpheld { .. }
            )),
            other => panic!("expected Convicted, got {other:?}"),
        }
    }

    // ── POLE (iv): Proven — a valid proof satisfies; an invalid one refuses. ──
    #[test]
    fn proven_valid_proof_satisfies_invalid_refuses() {
        let pvk = [0x9A; 32];
        let policy = || CiAssurance::Proven { verifying_key: pvk };
        let (receipt, v) = run(S1, OUTPUT);

        // A valid proof (right vk, asserts the verdict's output, non-empty).
        let good = CiExecutionProof {
            proving_vk: pvk,
            asserted_output: OUTPUT,
            proof_bytes: vec![0x01, 0x02, 0x03],
        };
        satisfied(
            policy(),
            CiRunWitness::signed(receipt.clone(), v.clone()).with_proof(good),
        )
        .expect("a valid execution proof satisfies with no re-execution");

        // An invalid proof (asserts a different output) → refused.
        let bad = CiExecutionProof {
            proving_vk: pvk,
            asserted_output: [0xEE; 32],
            proof_bytes: vec![0x01],
        };
        match satisfied(
            policy(),
            CiRunWitness::signed(receipt.clone(), v.clone()).with_proof(bad),
        ) {
            Err(CheckRefusal::AssuranceUnmet(why)) => assert!(why.contains("proof"), "{why}"),
            other => panic!("expected AssuranceUnmet for an invalid proof, got {other:?}"),
        }

        // No proof at all → refused.
        match satisfied(policy(), CiRunWitness::signed(receipt, v)) {
            Err(CheckRefusal::AssuranceUnmet(_)) => {}
            other => panic!("expected AssuranceUnmet for a missing proof, got {other:?}"),
        }
    }

    // ── POLE (v): Staked{inner:ReExecuted} — inner-satisfied lands; an inner ──
    //    conviction surfaces a Conviction naming the forfeit bond.
    #[test]
    fn staked_delegates_and_binds_the_bond_on_conviction() {
        let keys = GovernedKeySet::operator([vk(S1), vk(S2)]);
        let staked = |inner| CiAssurance::Staked {
            bond_ref: BOND,
            inner: Box::new(inner),
        };
        let inner = || CiAssurance::ReExecuted {
            keys: keys.clone(),
            quorum: 1,
        };
        let (primary, pv) = run(S1, OUTPUT);

        // Inner satisfied (one matching re-execution) → the staked check lands.
        satisfied(
            staked(inner()),
            CiRunWitness::signed(primary.clone(), pv.clone())
                .with_attestations(vec![run(S2, OUTPUT)]),
        )
        .expect("a staked policy lands exactly when its inner policy is satisfied");

        // Inner conviction (a divergent re-execution) → Conviction{bond_ref}.
        match satisfied(
            staked(inner()),
            CiRunWitness::signed(primary, pv).with_attestations(vec![run(S2, [0xEE; 32])]),
        ) {
            Err(CheckRefusal::Convicted(c)) => {
                assert_eq!(
                    c.bond_ref,
                    Some(BOND),
                    "the staked bond is bound to the conviction"
                );
                assert!(matches!(
                    c.evidence,
                    ConvictionEvidence::ReExecDivergence { .. }
                ));
            }
            other => panic!("expected a bonded Convicted, got {other:?}"),
        }
    }

    // ── POLE (vi): a revoked key's verdict no longer satisfies. ───────────────
    #[test]
    fn a_revoked_key_no_longer_satisfies() {
        let (receipt, v) = run(S1, OUTPUT);

        // Active: the verdict signed by S1 satisfies TrustedSigned.
        let mut keys = GovernedKeySet::operator([vk(S1)]);
        satisfied(
            CiAssurance::TrustedSigned { keys: keys.clone() },
            CiRunWitness::signed(receipt.clone(), v.clone()),
        )
        .expect("an active-key verdict satisfies");

        // Revoke S1 → the SAME signed verdict no longer verifies (no active key).
        assert!(keys.revoke(&vk(S1)), "the active key was revoked");
        match satisfied(
            CiAssurance::TrustedSigned { keys },
            CiRunWitness::signed(receipt, v),
        ) {
            Err(CheckRefusal::SignatureUnverified) => {}
            other => panic!("expected SignatureUnverified after revocation, got {other:?}"),
        }
    }
}
