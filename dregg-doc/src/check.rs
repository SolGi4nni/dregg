//! CI AS RECEIPTED TURNS — the forge's required-check gate
//! (docs/deos/DREGG-FORGE.md).
//!
//! A forge merge is gated on a VERIFIED CHECK with **no trusted CI runner**: a
//! [`crate::PullRequest`] cannot land until every [`RequiredCheck`] it carries
//! is satisfied by a real cryptographic witness — the proof IS the pass. A
//! check is never "satisfied" by a bool someone sets; satisfaction is
//! [`RequiredCheck::satisfied_by`], which verifies one of two witness kinds:
//!
//! - **A committed check-turn receipt**
//!   ([`CheckRequirement::CommittedReceipt`]): the check IS a turn (the CI
//!   job), named by its exact `turn_hash` BEFORE it runs
//!   ([`crate::ExecutorDrivenDoc::planned_turn_hash`]). It is satisfied only by
//!   that turn's committed [`TurnReceipt`] — finalized, carrying a genuine
//!   `executor_signature` that verifies (real Ed25519, via
//!   [`dregg_turn::verify_receipt_signature_with_keys`]) against the check's
//!   trusted executor keys. A `TurnReceipt` struct anyone can populate; the
//!   signature over its canonical message they cannot — so a fabricated
//!   "passing" receipt is refused, fail-closed (an UNSIGNED receipt is refused
//!   too, by the explicit `Unsigned` pre-check). The signature is checked IN
//!   ISOLATION (not as a chain genesis), so a check turn that is NOT its
//!   document's first edit — an approval posted after a comment, whose receipt
//!   carries `previous_receipt_hash = Some(..)` — still satisfies the check.
//! - **A [`ProofCondition`] witness** ([`CheckRequirement::Condition`]): the
//!   check is any provable statement in dregg-turn's conditional grammar
//!   (hash preimage, local/remote STARK proof), satisfied by a
//!   [`ConditionProof`] verified through the REAL
//!   [`dregg_turn::resolve_condition`] path — the same primitive that gates
//!   [`dregg_turn::ConditionalTurn`] execution.
//! - **A WORK-BINDING CI verdict** ([`CheckRequirement::CiRun`],
//!   [`crate::ci_verdict`]): the CI-grade check. `CommittedReceipt` binds only
//!   AUTHORSHIP — "a trusted key signed *some* finalized turn" — so a host can
//!   sign a trivial content-free cursor turn and pass without building anything.
//!   `CiRun` binds WORK: it is satisfied only by a committed, executor-signed
//!   receipt that COMMITS a [`crate::CiVerdict`] whose `command_id` matches,
//!   whose `input_root` equals the PR's real post-merge code
//!   ([`crate::PullRequest::input_root`]), and whose `exit_code == 0`. The
//!   verdict is bound INSIDE the signed turn (its turn hash is re-derived from
//!   the verdict and matched to the receipt), so a loose verdict cannot forge
//!   it; a per-`(base fold, verdict)` nullifier
//!   ([`crate::PullRequest::land_checked`]) stops replay. Use `CiRun` for a
//!   real build/test gate; `CommittedReceipt` remains for approval-shaped
//!   "a trusted party signed off on this turn" checks.
//!
//! The gate itself runs in [`crate::PullRequest::land`]: every required check
//! is verified BEFORE any merge turn is driven, so an unsatisfied check never
//! mutates the ledger ([`crate::PullRequestError::CheckNotSatisfied`], document
//! byte-untouched). Checks and caps are INDEPENDENT gates: a satisfied check
//! set does not confer the base region's edit cap — a capless merger is still
//! refused in-band by the executor.
//!
//! ## Named seams (deferred, not holes)
//!
//! - **The CI body as a confined grain**: here the check turn is driven by the
//!   test itself through [`crate::ExecutorDrivenDoc`]; the real forge runs the
//!   check job as a confined grain (grain-jail) whose only egress is
//!   committing the check-turn receipt. That body is the forge's next slice.
//! - **`ProofCondition::TurnExecuted` verifies a different signing message
//!   than the executor produces**: `turn/src/conditional.rs` checks the
//!   Ed25519 signature over `receipt_hash()`, while the executor (Stage 9
//!   R-4, `maybe_sign_receipt`) signs
//!   `TurnReceipt::canonical_executor_signed_message()` — so a genuinely
//!   executor-signed receipt cannot satisfy `TurnExecuted` through
//!   `resolve_condition` today. [`CheckRequirement::CommittedReceipt`]
//!   therefore verifies through `verify_receipt_chain_with_keys` (which checks
//!   the canonical message the executor actually signs); reconciling
//!   `conditional.rs` to the R-4 message is a dregg-turn fix, out of this
//!   crate.
//! - **Condition freshness/nullifiers**: [`RequiredCheck::satisfied_by`] is a
//!   point verification (height 0, no timeout, fresh nullifier set). Timeout
//!   heights and cross-land proof-reuse prevention belong to the forge-grain's
//!   ledger, not the in-process PR object.

use std::collections::HashSet;

use dregg_turn::{
    ConditionProof, ConditionalResult, DEFAULT_MAX_ROOT_AGE, Finality, ProofCondition, TurnReceipt,
    resolve_condition, verify_receipt_signature_with_keys,
};

use crate::ci_verdict::{CiVerdict, planned_ci_run_hash};

/// The name of a required check — the forge's "required status check" key
/// (e.g. `"build"`, `"proof-gauntlet"`).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CheckId(pub String);

impl CheckId {
    /// The check's name.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<&str> for CheckId {
    fn from(s: &str) -> Self {
        CheckId(s.to_string())
    }
}

impl core::fmt::Display for CheckId {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(&self.0)
    }
}

/// WHAT satisfies a check — always a cryptographic witness, never a bool.
#[derive(Clone, Debug)]
pub enum CheckRequirement {
    /// The check is the exact turn `turn_hash` (the CI job, nameable before it
    /// runs — [`crate::ExecutorDrivenDoc::planned_turn_hash`]); satisfied only
    /// by its COMMITTED receipt: finalized, executor-SIGNED, the signature
    /// verifying against one of `trusted_executor_keys` (Ed25519 verifying-key
    /// bytes). Fail-closed: an unsigned receipt, a wrong-turn receipt, a
    /// tampered signature, or an empty/wrong key set all refuse.
    CommittedReceipt {
        /// The check turn's hash ([`dregg_turn::Turn::hash`]).
        turn_hash: [u8; 32],
        /// Ed25519 verifying keys whose signature over the receipt's canonical
        /// executor-signed message is accepted.
        trusted_executor_keys: Vec<[u8; 32]>,
    },
    /// The check is a provable statement: a [`ProofCondition`] satisfied by a
    /// [`ConditionProof`] through the real [`resolve_condition`] verification
    /// (preimage / STARK). For receipt-shaped checks use
    /// [`CheckRequirement::CommittedReceipt`] (see the module docs' named seam
    /// on `TurnExecuted`'s signing-message mismatch).
    Condition(ProofCondition),
    /// **THE WORK-BINDING CI CHECK** ([`crate::ci_verdict`]): satisfied only by
    /// a committed, executor-signed receipt that COMMITS a [`CiVerdict`] whose
    /// `command_id` matches, whose `input_root` equals the PR's real post-merge
    /// code ([`crate::PullRequest::input_root`]), and whose `exit_code == 0`.
    ///
    /// Unlike [`CheckRequirement::CommittedReceipt`] (which binds AUTHORSHIP —
    /// "a trusted key signed *some* finalized turn"), this binds WORK: the
    /// signed turn must have committed exactly the presented verdict, so a
    /// trivial cursor turn cannot pass. The verdict is re-derived-and-bound
    /// through [`crate::ci_verdict::planned_ci_run_hash`] against the CI-run
    /// region cell identity `(editor_seed, region_seed)`; a loose verdict next
    /// to an unrelated receipt refuses ([`CheckRefusal::VerdictNotCommitted`]).
    CiRun {
        /// The required check's command id — the verdict's `command_id` must
        /// equal this, so the check binds to the intended command, not any turn.
        command_id: [u8; 32],
        /// Ed25519 verifying keys whose signature over the receipt's canonical
        /// executor-signed message is accepted (the trusted CI executors).
        trusted_executor_keys: Vec<[u8; 32]>,
        /// The CI-run region cell's editor identity seed — fixed repo policy, so
        /// the verifier rebuilds the identical genesis cell the runner drove on
        /// ([`crate::ci_verdict::run_ci_verdict`]).
        editor_seed: u8,
        /// The CI-run region cell's region identity seed (see `editor_seed`).
        region_seed: u8,
    },
}

/// The witness presented against a [`RequiredCheck`]. Presenting is
/// [`crate::PullRequest::present_witness`]; VERIFYING is
/// [`RequiredCheck::satisfied_by`], at land time.
#[derive(Clone, Debug)]
pub enum CheckWitness {
    /// A committed check-turn receipt (for [`CheckRequirement::CommittedReceipt`]).
    Receipt(TurnReceipt),
    /// A condition proof (for [`CheckRequirement::Condition`]).
    Condition(ConditionProof),
    /// A CI run (for [`CheckRequirement::CiRun`]): the committed, executor-signed
    /// receipt of the CI-run turn PLUS the [`CiVerdict`] that turn committed. The
    /// verdict is not trusted because it is presented — it is trusted only after
    /// [`RequiredCheck::satisfied_by`] proves the signed `receipt`'s turn hash
    /// equals the hash re-derived from this verdict (the in-turn binding).
    CiRun {
        /// The committed, executor-signed CI-run receipt.
        receipt: TurnReceipt,
        /// The verdict that receipt's turn must have committed (verified, not
        /// trusted-on-presentation).
        verdict: CiVerdict,
    },
}

/// Why a required check is NOT satisfied (carried inside
/// [`crate::PullRequestError::CheckNotSatisfied`]).
#[derive(Clone, Debug)]
pub enum CheckRefusal {
    /// No witness has been presented for this check.
    NoWitness,
    /// The presented witness is the wrong kind for the requirement (e.g. a
    /// condition proof against a committed-receipt check).
    WrongWitnessKind,
    /// The receipt witnesses a different turn than the check names.
    WrongTurn {
        /// The check's required turn hash.
        expected: [u8; 32],
        /// The presented receipt's turn hash.
        got: [u8; 32],
    },
    /// The receipt is not finalized (`Finality::Tentative` — a self-reported
    /// pass, not a committed one).
    NotFinal,
    /// The receipt carries no `executor_signature` — fail-closed: an unsigned
    /// receipt is trivially fabricable, so it cannot witness a check.
    Unsigned,
    /// The receipt's `executor_signature` does not verify against any of the
    /// check's trusted executor keys.
    SignatureUnverified,
    /// The condition proof failed [`resolve_condition`] verification (the
    /// verifier's in-band reason).
    ConditionUnsatisfied(String),
    /// **THE WORK-BINDING REFUSAL**: the presented [`CiVerdict`] is NOT the one
    /// the signed receipt's turn committed — the turn hash re-derived from the
    /// verdict ([`crate::ci_verdict::planned_ci_run_hash`]) does not equal
    /// `receipt.turn_hash`. This is what refuses a loose verdict waved next to
    /// an unrelated signed receipt (the verdict is not bound in the turn).
    VerdictNotCommitted,
    /// The verdict's `command_id` is not the command this check requires (a
    /// real signed verdict, but for a different command).
    WrongCommand {
        /// The check's required command id.
        expected: [u8; 32],
        /// The verdict's command id.
        got: [u8; 32],
    },
    /// The verdict's `input_root` is not this PR's post-merge code
    /// ([`crate::PullRequest::input_root`]) — a verdict for a different PR's
    /// code, or a trivial verdict with no/empty input root, is refused.
    InputRootMismatch {
        /// The PR's real post-merge input root.
        expected: [u8; 32],
        /// The verdict's claimed input root.
        got: [u8; 32],
    },
    /// The CI command did not pass: the verdict's `exit_code` is non-zero.
    CheckFailed {
        /// The failing exit code the verdict carries.
        exit_code: i32,
    },
    /// This signed verdict was already consumed on this base lineage — a replay
    /// (detected at [`crate::PullRequest::land_checked`], per the
    /// [`crate::ci_verdict::ci_nullifier`]).
    WitnessReplayed,
}

/// A named check a [`crate::PullRequest`] must pass before it can land.
#[derive(Clone, Debug)]
pub struct RequiredCheck {
    /// The check's name.
    pub id: CheckId,
    /// The cryptographic requirement that satisfies it.
    pub requirement: CheckRequirement,
}

impl RequiredCheck {
    /// A committed-receipt check: the exact check turn (by hash) must have a
    /// committed, executor-signed receipt verifying against `trusted_executor_keys`.
    pub fn committed_receipt(
        id: impl Into<CheckId>,
        turn_hash: [u8; 32],
        trusted_executor_keys: Vec<[u8; 32]>,
    ) -> Self {
        RequiredCheck {
            id: id.into(),
            requirement: CheckRequirement::CommittedReceipt {
                turn_hash,
                trusted_executor_keys,
            },
        }
    }

    /// A condition check: `condition` must be satisfied by a verified
    /// [`ConditionProof`].
    pub fn condition(id: impl Into<CheckId>, condition: ProofCondition) -> Self {
        RequiredCheck {
            id: id.into(),
            requirement: CheckRequirement::Condition(condition),
        }
    }

    /// **THE WORK-BINDING CI CHECK**: `command_id` must have been run on the CI
    /// runner identity `(editor_seed, region_seed)` and its committed,
    /// executor-signed [`CiVerdict`] receipt (verifying against
    /// `trusted_executor_keys`) must bind THIS PR's post-merge code with
    /// `exit_code == 0`. See [`CheckRequirement::CiRun`] and [`crate::ci_verdict`].
    pub fn ci_run(
        id: impl Into<CheckId>,
        command_id: [u8; 32],
        editor_seed: u8,
        region_seed: u8,
        trusted_executor_keys: Vec<[u8; 32]>,
    ) -> Self {
        RequiredCheck {
            id: id.into(),
            requirement: CheckRequirement::CiRun {
                command_id,
                trusted_executor_keys,
                editor_seed,
                region_seed,
            },
        }
    }

    /// VERIFY a presented witness against this check — the satisfaction
    /// primitive the land gate calls. `Ok(())` iff the witness is a genuine
    /// cryptographic pass; every other path refuses with the reason.
    ///
    /// `pr_input_root` is the landing PR's real post-merge code digest
    /// ([`crate::PullRequest::input_root`]); the [`CheckRequirement::CiRun`] arm
    /// binds the verdict to it (the `CommittedReceipt` / `Condition` arms ignore
    /// it). Anti-replay ([`CheckRefusal::WitnessReplayed`]) is enforced at
    /// [`crate::PullRequest::land_checked`], not here (this is a point verifier).
    pub fn satisfied_by(
        &self,
        witness: &CheckWitness,
        pr_input_root: [u8; 32],
    ) -> Result<(), CheckRefusal> {
        match (&self.requirement, witness) {
            (
                CheckRequirement::CommittedReceipt {
                    turn_hash,
                    trusted_executor_keys,
                },
                CheckWitness::Receipt(receipt),
            ) => {
                // The receipt must witness EXACTLY the named check turn…
                if receipt.turn_hash != *turn_hash {
                    return Err(CheckRefusal::WrongTurn {
                        expected: *turn_hash,
                        got: receipt.turn_hash,
                    });
                }
                // …as a COMMITTED (finalized) result…
                if receipt.finality != Finality::Final {
                    return Err(CheckRefusal::NotFinal);
                }
                // …and be executor-SIGNED. Fail-closed here is load-bearing:
                // `verify_receipt_chain_with_keys` SKIPS receipts without a
                // signature (chain-verification semantics), which for a CI
                // gate would admit any fabricated receipt struct.
                if receipt.executor_signature.is_none() {
                    return Err(CheckRefusal::Unsigned);
                }
                // Real Ed25519 verification of the signature over the
                // receipt's canonical executor-signed message — IN ISOLATION.
                // A check turn need not be its document's genesis: an approval
                // posted after a comment carries `previous_receipt_hash =
                // Some(..)`, which the chain verifier rejects as
                // `GenesisHasPrevious`. The point-verifier here only binds the
                // executor's authorship of THIS receipt, not its chain
                // position.
                verify_receipt_signature_with_keys(receipt, trusted_executor_keys)
                    .map_err(|_| CheckRefusal::SignatureUnverified)
            }

            (CheckRequirement::Condition(condition), CheckWitness::Condition(proof)) => {
                // The REAL conditional-turn verification path (preimage /
                // STARK). Point verification: height 0 with no timeout, a
                // fresh nullifier set, no remote trusted roots, no executor
                // keys (receipt-shaped checks go through CommittedReceipt —
                // see the module docs).
                let mut nullifiers = HashSet::new();
                match resolve_condition(
                    condition,
                    proof,
                    /* current_height */ 0,
                    /* timeout_height */ 0,
                    /* trusted_roots  */ &[],
                    DEFAULT_MAX_ROOT_AGE,
                    &mut nullifiers,
                    /* trusted_executor_keys */ &[],
                ) {
                    ConditionalResult::Resolved => Ok(()),
                    ConditionalResult::InvalidProof(reason) => {
                        Err(CheckRefusal::ConditionUnsatisfied(reason))
                    }
                    ConditionalResult::Pending => Err(CheckRefusal::ConditionUnsatisfied(
                        "condition pending".to_string(),
                    )),
                    ConditionalResult::Expired => Err(CheckRefusal::ConditionUnsatisfied(
                        "condition expired".to_string(),
                    )),
                }
            }

            (
                CheckRequirement::CiRun {
                    command_id,
                    trusted_executor_keys,
                    editor_seed,
                    region_seed,
                },
                CheckWitness::CiRun { receipt, verdict },
            ) => {
                // (a) The receipt must be a COMMITTED (finalized), executor-SIGNED
                //     receipt whose signature verifies against a trusted CI
                //     executor key — same fail-closed discipline as
                //     CommittedReceipt (an unsigned/wrong-key receipt refuses).
                if receipt.finality != Finality::Final {
                    return Err(CheckRefusal::NotFinal);
                }
                if receipt.executor_signature.is_none() {
                    return Err(CheckRefusal::Unsigned);
                }
                verify_receipt_signature_with_keys(receipt, trusted_executor_keys)
                    .map_err(|_| CheckRefusal::SignatureUnverified)?;

                // (b) THE CRUX — the verdict must be BOUND INSIDE the signed
                //     turn. Re-derive the CI-run turn hash from the PRESENTED
                //     verdict on the (repo-policy-fixed) CI runner identity, and
                //     require it to equal the signed receipt's turn hash. Since
                //     the executor signs over a message covering `turn_hash`, a
                //     match proves the trusted key attested a turn that
                //     committed EXACTLY this verdict. A loose verdict waved next
                //     to an unrelated signed receipt re-derives a different hash
                //     and refuses here (the verdict is not committed in the
                //     turn) — the projection is injective in the verdict's bytes.
                let expected = planned_ci_run_hash(*editor_seed, *region_seed, verdict)
                    .ok_or(CheckRefusal::VerdictNotCommitted)?;
                if receipt.turn_hash != expected {
                    return Err(CheckRefusal::VerdictNotCommitted);
                }

                // (c) The verdict must be the result of the REQUIRED command
                //     (not some other turn that happens to be a valid CI run).
                if verdict.command_id != *command_id {
                    return Err(CheckRefusal::WrongCommand {
                        expected: *command_id,
                        got: verdict.command_id,
                    });
                }

                // (d) The verdict must bind THIS PR's real post-merge code. A
                //     verdict for a different PR's code — or a trivial verdict
                //     with no/empty input root — is refused: the CI ran on the
                //     wrong (or no) input.
                if verdict.input_root != pr_input_root {
                    return Err(CheckRefusal::InputRootMismatch {
                        expected: pr_input_root,
                        got: verdict.input_root,
                    });
                }

                // (e) The check must have PASSED. A failing run does not satisfy.
                if verdict.exit_code != 0 {
                    return Err(CheckRefusal::CheckFailed {
                        exit_code: verdict.exit_code,
                    });
                }

                Ok(())
            }

            // A witness of the wrong shape never satisfies.
            (CheckRequirement::CommittedReceipt { .. }, CheckWitness::Condition(_))
            | (CheckRequirement::CommittedReceipt { .. }, CheckWitness::CiRun { .. })
            | (CheckRequirement::Condition(_), CheckWitness::Receipt(_))
            | (CheckRequirement::Condition(_), CheckWitness::CiRun { .. })
            | (CheckRequirement::CiRun { .. }, CheckWitness::Receipt(_))
            | (CheckRequirement::CiRun { .. }, CheckWitness::Condition(_)) => {
                Err(CheckRefusal::WrongWitnessKind)
            }
        }
    }
}
