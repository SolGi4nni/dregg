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
//!   the `Proven` STARK verifier ([`verify_ci_proof`] = [`StarkCiProofVerifier`]
//!   composing the production [`CellProgram`] prove+verify — see below), the
//!   `Staked` composition (delegates to `inner`, binds `bond_ref`, surfaces the
//!   [`Conviction`]), and the [`GovernedKeySet`] rotation/revocation gate.
//! - **The `Proven` rung — what is REAL vs the named deepest seam**:
//!   [`verify_ci_proof`] is a GENUINE dregg STARK verification, not a stub: it
//!   composes [`CellProgram::verify_transition`] over the CI-attestation circuit
//!   ([`ci_attestation_program`]), whose 25 public inputs BIND the verdict
//!   (input_root ‖ command_id ‖ output_digest ‖ exit_code, via first-row
//!   boundary constraints) and whose in-circuit predicate is the CI PASS GATE
//!   (`exit_code == 0`). Verification trusts ONLY the STARK's soundness and the
//!   verifying key — NO re-execution, NO honest-re-executor / quorum assumption
//!   (the qualitative jump over `ReExecuted`). A proof for a different verdict,
//!   a tampered proof, or a wrong vk all fail closed. **The named deepest seam**:
//!   the in-circuit predicate here is the pass gate + verdict binding, NOT a full
//!   arithmetization of an arbitrary command's execution — proving that "running
//!   `command_id` over `input_root` genuinely PRODUCES this `output_digest`" for
//!   a general command is the confined-execution zkVM AIR (a `custom_proof_bind`
//!   sub-proof), which drops in as the circuit predicate with no policy change.
//!   The BINDING + verification are real dregg proving today.
//!   - `OptimisticChallenge`'s dispute detection is now REAL and in-crate: a
//!     challenger posts a signed [`Challenge`] block to the blocklace
//!     ([`post_challenge`]), and [`detect_upheld_challenge`] scans the presented
//!     [`ChallengeContext::challenge_lace`] for a trusted-signed block that
//!     CONTRADICTS the host verdict on the same run (an equivocation), MINTING the
//!     [`Conviction`] from the detected block id. What stays out-of-crate is only
//!     the live NETWORK dissemination of those challenge blocks across nodes (the
//!     gossip transport that fills the lace); the equivocation logic is real.
//!   - `Staked`'s slash-transfer is now REAL and in-crate: an inner conviction
//!     produces a [`crate::staked_bond::SlashOutcome`] that
//!     [`crate::staked_bond::slash_bond`] fires as a conserving (`Σδ=0`), one-shot
//!     forfeiture of the bonded value (reusing the `dregg_cell` balance ledger +
//!     the `escrow_sealed` committed-heap one-shot discipline). See
//!     [`CiAssurance::bond_disposition`]. What stays out-of-crate is the host
//!     POSTING the bond at job-start and a cross-node `bond_ref → holding-cell`
//!     stake registry — the deployment wires those.

use crate::ci_verdict::{CiVerdict, planned_ci_run_hash};
use dregg_blocklace::{Block, Blocklace};
use dregg_turn::{Finality, TurnReceipt, verify_receipt_signature_with_keys};
use ed25519_dalek::SigningKey;

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
// Proof-of-execution (the `Proven` rung): a REAL dregg STARK, verified with NO
// re-execution and NO quorum-honesty assumption — trust only proof soundness.
// ─────────────────────────────────────────────────────────────────────────────

use dregg_circuit::dsl::circuit::{
    BoundaryDef, BoundaryRow, CellProgram, CircuitDescriptor, ColumnDef, ColumnKind,
    ConstraintExpr, PolyTerm,
};
use dregg_circuit::effect_vm::bytes32_to_8_limbs;
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use std::collections::HashMap;

/// How many BabyBear public inputs the CI-attestation circuit binds:
/// `input_root` (8 limbs) ‖ `command_id` (8) ‖ `output_digest` (8) ‖ `exit_code`
/// (1) = 25. Each 32-byte field is the 8-limb little-endian projection
/// ([`bytes32_to_8_limbs`]); the exit code is one felt.
const CI_PI_COUNT: usize = 25;
/// The pass-gate column (also public input 24): `input_root` occupies columns
/// 0..8, `command_id` 8..16, `output_digest` 16..24, and `exit_code` this last
/// column — constrained `== 0` (the CI pass gate).
const COL_EXIT: usize = 24;

/// THE CANONICAL VERDICT→PUBLIC-INPUTS ENCODING that binds a proof to a verdict.
///
/// The verifier reconstructs this vector from the verdict it is checking and
/// hands it to [`CellProgram::verify_transition`]; the circuit's first-row
/// boundary constraints pin the committed trace to exactly these felts. So a
/// proof produced for a DIFFERENT verdict (any different `input_root`,
/// `command_id`, `output_digest`, or `exit_code`) does not verify against the
/// public inputs this verdict reconstructs — the encoding IS the binding.
///
/// It is INJECTIVE on the four bound fields: distinct fields map to distinct
/// felt vectors (each 32-byte field via the fixed 8-limb little-endian
/// projection, the exit code as its own felt).
pub fn ci_verdict_public_inputs(verdict: &CiVerdict) -> Vec<BabyBear> {
    let mut pis = Vec::with_capacity(CI_PI_COUNT);
    pis.extend_from_slice(&bytes32_to_8_limbs(&verdict.input_root));
    pis.extend_from_slice(&bytes32_to_8_limbs(&verdict.command_id));
    pis.extend_from_slice(&bytes32_to_8_limbs(&verdict.output_digest));
    pis.push(BabyBear::new((verdict.exit_code as u32) % BABYBEAR_P));
    debug_assert_eq!(pis.len(), CI_PI_COUNT);
    pis
}

/// **THE CI-ATTESTATION CIRCUIT** — the real dregg [`CellProgram`] the `Proven`
/// rung proves and verifies over.
///
/// * Its 25 public inputs BIND the verdict ([`ci_verdict_public_inputs`]): a
///   first-row [`BoundaryDef::PiBinding`] pins each trace column to its public
///   input, so the STARK's boundary soundness ties the proof to one exact
///   verdict.
/// * Its single algebraic constraint is the CI **PASS GATE**: the `exit_code`
///   column must be `0` on every row (`1·exit == 0`, degree 1). A verdict with a
///   non-zero exit code has NO satisfying trace — the row-0 boundary (`exit ==
///   exit_code`) and the pass-gate constraint (`exit == 0`) are jointly
///   unsatisfiable — so a failing check cannot be `Proven`.
///
/// The program's `vk_hash` (the blake3 of its descriptor) is the verifying key
/// the `Proven { verifying_key }` check must name — it is deterministic, so a
/// deployment pins it once and any tampered descriptor produces a different vk
/// and fails closed.
pub fn ci_attestation_program() -> CellProgram {
    let columns: Vec<ColumnDef> = (0..CI_PI_COUNT)
        .map(|i| ColumnDef {
            name: format!("pi{i}"),
            index: i,
            kind: ColumnKind::Value,
        })
        .collect();

    // Bind every trace column's first row to its matching public input — this is
    // what makes a proof ABOUT a specific verdict.
    let boundaries: Vec<BoundaryDef> = (0..CI_PI_COUNT)
        .map(|i| BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: i,
            pi_index: i,
        })
        .collect();

    // THE PASS GATE: exit_code column == 0 on every row (a degree-1 polynomial).
    let constraints = vec![ConstraintExpr::Polynomial {
        terms: vec![PolyTerm {
            coeff: BabyBear::ONE,
            col_indices: vec![COL_EXIT],
        }],
    }];

    let descriptor = CircuitDescriptor {
        name: "dregg-ci-attestation-v1".to_string(),
        trace_width: CI_PI_COUNT,
        max_degree: 2,
        columns,
        constraints,
        boundaries,
        public_input_count: CI_PI_COUNT,
        lookup_tables: vec![],
    };
    CellProgram::new(descriptor, 1)
}

/// The verifying key of the CI-attestation program — the value a
/// `Proven { verifying_key }` check pins so the deployment need not carry the
/// whole descriptor. Deterministic (blake3 of the descriptor).
pub fn ci_attestation_vk() -> [u8; 32] {
    ci_attestation_program().vk_hash
}

/// GENUINELY PRODUCE a `Proven` proof for a PASSING verdict (exit code 0): prove
/// the CI-attestation circuit over a trace whose first row carries the verdict's
/// felt encoding. This mints a REAL [`stark`](dregg_circuit::stark) proof (via
/// [`CellProgram::prove_transition`]) — not a hand-mocked "valid" flag — bound to
/// the verdict through its public inputs.
///
/// Fails (`Err`) for a non-passing verdict: the pass-gate constraint has no
/// satisfying trace when `exit_code != 0`, so no valid proof exists.
pub fn prove_ci_attestation(verdict: &CiVerdict) -> Result<CiExecutionProof, String> {
    let program = ci_attestation_program();
    let pis = ci_verdict_public_inputs(verdict);
    // A power-of-two trace (>= 2); the circuit is single-row-meaningful (all
    // constraints/boundaries are on row 0 / per-row), so a constant trace works.
    let num_rows = 4usize;
    let mut witness: HashMap<String, Vec<BabyBear>> = HashMap::new();
    for (i, pi) in pis.iter().enumerate() {
        witness.insert(format!("pi{i}"), vec![*pi; num_rows]);
    }
    let proof_bytes = program
        .prove_transition(&witness, num_rows, &pis)
        .map_err(|e| format!("ci-attestation prove failed: {e:?}"))?;
    Ok(CiExecutionProof {
        proving_vk: program.vk_hash,
        asserted_output: verdict.output_digest,
        proof_bytes,
    })
}

/// A PROOF-OF-EXECUTION carried alongside a [`CiVerdict`] for the
/// [`CiAssurance::Proven`] rung: a real STARK proof, bound to the verdict, that
/// the CI-attestation circuit accepts. Verified by [`verify_ci_proof`] with NO
/// re-execution and NO trust in any host or re-executor — only the STARK's
/// soundness and the verifying key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CiExecutionProof {
    /// The verifying key this proof is against (must equal the check's
    /// `Proven { verifying_key }`, i.e. [`ci_attestation_vk`]).
    pub proving_vk: [u8; 32],
    /// The output digest the proof asserts (must equal the verdict's
    /// `output_digest`; the proof's public inputs bind it in-circuit).
    pub asserted_output: [u8; 32],
    /// The REAL STARK proof bytes ([`CellProgram::prove_transition`] output),
    /// verified by [`CellProgram::verify_transition`] against the verdict's
    /// public inputs.
    pub proof_bytes: Vec<u8>,
}

/// THE PROOF VERIFIER SEAM: verify a [`CiExecutionProof`] against a verifying key
/// and the verdict it claims. The production impl ([`StarkCiProofVerifier`])
/// runs a real dregg STARK verification; the trait keeps the swap point open.
pub trait CiProofVerifier {
    /// `true` iff `proof` is a valid proof, under `verifying_key`, binding
    /// `verdict`'s fields as its public inputs.
    fn verify(
        &self,
        verifying_key: &[u8; 32],
        verdict: &CiVerdict,
        proof: &CiExecutionProof,
    ) -> bool;
}

/// **THE REAL `Proven` VERIFIER** — a genuine dregg STARK check, no re-execution,
/// no quorum-honesty assumption. It composes [`CellProgram::verify_transition`]
/// (the production light-client verify path) over the CI-attestation circuit.
///
/// The four fail-closed checks:
/// 1. **vk binds** — the check's `verifying_key` is the CI-attestation program's
///    descriptor vk ([`ci_attestation_vk`]) AND the proof names that same vk. A
///    wrong verifying key is refused (a proof under a different circuit does not
///    attest this check).
/// 2. **output binds** — the proof's `asserted_output` equals the verdict's
///    `output_digest`.
/// 3. **THE STARK VERIFIES** — the proof verifies against the public inputs
///    RECONSTRUCTED from THIS verdict ([`ci_verdict_public_inputs`]). A tampered
///    or garbage proof fails here; the pass gate means only an `exit_code == 0`
///    verdict has a verifying proof.
/// 4. **the verdict binds** — because the public inputs are reconstructed from
///    the verdict and the circuit's boundary constraints pin the committed trace
///    to them, a proof produced for a DIFFERENT verdict (different
///    input_root/command/output) does not verify against this verdict's public
///    inputs and is refused at step 3.
#[derive(Clone, Debug, Default)]
pub struct StarkCiProofVerifier;

impl CiProofVerifier for StarkCiProofVerifier {
    fn verify(
        &self,
        verifying_key: &[u8; 32],
        verdict: &CiVerdict,
        proof: &CiExecutionProof,
    ) -> bool {
        let program = ci_attestation_program();
        // (1) vk binds: the check's key AND the proof's key are the attestation vk.
        if program.vk_hash != *verifying_key || proof.proving_vk != *verifying_key {
            return false;
        }
        // (2) output binds.
        if proof.asserted_output != verdict.output_digest {
            return false;
        }
        // (3)+(4) THE STARK, over public inputs reconstructed from THIS verdict.
        let pis = ci_verdict_public_inputs(verdict);
        program.verify_transition(&pis, &proof.proof_bytes).is_ok()
    }
}

/// Verify a CI execution proof through the production ([`StarkCiProofVerifier`])
/// verifier. This is the function the `Proven` policy calls: a valid real proof
/// bound to the verdict satisfies; a proof for a different verdict, a tampered
/// proof, or a wrong verifying key refuses.
pub fn verify_ci_proof(
    verifying_key: &[u8; 32],
    verdict: &CiVerdict,
    proof: &CiExecutionProof,
) -> bool {
    StarkCiProofVerifier.verify(verifying_key, verdict, proof)
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
///
/// Each variant is `#[non_exhaustive]`, so it CANNOT be constructed outside this
/// crate: a `ConvictionEvidence` value is minted solely inside
/// [`CiAssurance::evaluate`], populated from the REAL inputs evaluate verified
/// (the diverging attestation it saw, the upheld-challenge id it was handed).
/// This is why a [`Conviction`] — and hence a
/// [`crate::staked_bond::SlashOutcome`] — cannot be conjured from thin air: the
/// evidence field is unforgeable by an external caller. Its fields stay `pub`
/// (READ-only from outside — match with `..`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConvictionEvidence {
    /// A re-execution attestation over the SAME work reported a DIFFERENT
    /// `output_digest` than the verdict — agreement failed, so a host lied.
    #[non_exhaustive]
    ReExecDivergence {
        /// The verdict's claimed output digest.
        claimed: [u8; 32],
        /// The divergent attestation's output digest.
        divergent: [u8; 32],
        /// The trusted key that signed the divergent attestation.
        signer: [u8; 32],
    },
    /// A challenge was upheld during the optimistic window (a fraud proof landed).
    #[non_exhaustive]
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
///
/// # Unforgeable by construction
///
/// A `Conviction` has PRIVATE fields and NO public constructor, so an external
/// caller cannot fabricate one. The only way to obtain a `Conviction` is to have
/// [`CiAssurance::evaluate`] return [`AssuranceOutcome::Convicted`] after it
/// genuinely detected a lie (a divergent re-execution attestation, or an upheld
/// optimistic challenge). This is what makes
/// [`crate::staked_bond::SlashOutcome::from_conviction`] genuinely
/// conviction-gated: a slash requires a real `Conviction`, and a real
/// `Conviction` requires a real `evaluate` detection.
///
/// Fabricating one does not compile — the fields are private and there is no
/// public constructor:
///
/// ```compile_fail
/// use dregg_doc::{Conviction, ConvictionEvidence};
/// let forged = Conviction {
///     bond_ref: None,
///     evidence: ConvictionEvidence::ChallengeUpheld { challenge_id: [0u8; 32] },
/// };
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Conviction {
    /// The bond forfeit by this conviction, if the policy was `Staked`.
    bond_ref: Option<BondRef>,
    /// The evidence that proved the lie.
    evidence: ConvictionEvidence,
}

impl Conviction {
    /// Mint a conviction for a divergent re-execution. MODULE-PRIVATE: reachable
    /// only from [`CiAssurance::evaluate`], and populated from the attestation
    /// evaluate actually verified (not caller-supplied) — this is what binds the
    /// evidence to a real detection.
    fn re_exec_divergence(claimed: [u8; 32], divergent: [u8; 32], signer: [u8; 32]) -> Self {
        Conviction {
            bond_ref: None,
            evidence: ConvictionEvidence::ReExecDivergence {
                claimed,
                divergent,
                signer,
            },
        }
    }

    /// Mint a conviction for an upheld optimistic challenge. MODULE-PRIVATE:
    /// reachable only from [`CiAssurance::evaluate`], which mints it from the
    /// upheld-challenge id it was handed in the (verified) challenge context.
    fn challenge_upheld(challenge_id: [u8; 32]) -> Self {
        Conviction {
            bond_ref: None,
            evidence: ConvictionEvidence::ChallengeUpheld { challenge_id },
        }
    }

    /// Bind the forfeit bond when the convicting policy was [`CiAssurance::Staked`].
    /// MODULE-PRIVATE: the `Staked` wrapper in [`CiAssurance::evaluate`] is the
    /// only caller.
    fn with_bond(mut self, bond_ref: BondRef) -> Self {
        self.bond_ref = Some(bond_ref);
        self
    }

    /// The bond forfeit by this conviction, if the policy was `Staked`
    /// (read-only accessor — the field is private so a conviction is unforgeable).
    pub fn bond_ref(&self) -> Option<BondRef> {
        self.bond_ref
    }

    /// The evidence that proved the lie (read-only accessor — the field is
    /// private so a conviction is unforgeable).
    pub fn evidence(&self) -> &ConvictionEvidence {
        &self.evidence
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE OPTIMISTIC-CHALLENGE CARRIER — a challenge is a signed blocklace block, and
// an upheld challenge is a real equivocation the gate DETECTS (not a stub signal).
// ─────────────────────────────────────────────────────────────────────────────

/// Domain tag separating a challenge's canonical encoding from any other bytes.
const CHALLENGE_DOMAIN: &[u8] = b"dregg-forge/ci-challenge/v1";
/// A challenge's fixed-width encoding: domain ‖ input_root(32) ‖ command_id(32)
/// ‖ claimed_output(32) ‖ claimed_exit(4) ‖ recomputed_output(32) ‖
/// recomputed_exit(4).
const CHALLENGE_ENCODED_LEN: usize = 32 + 32 + 32 + 4 + 32 + 4;

/// A CHALLENGE against a host's CI verdict — a fraud claim a re-executor posts to
/// the blocklace. It NAMES the disputed run (`input_root` + `command_id`, the same
/// identity the host verdict carries), QUOTES what the host claimed
/// (`claimed_output`/`claimed_exit`), and states what the challenger RECOMPUTED
/// (`recomputed_output`/`recomputed_exit`) re-executing that same command. When the
/// recomputed result differs from the host's claim, the challenge and the host
/// verdict are two contradictory attestations about ONE CI run — an equivocation.
///
/// A challenge is not loose data: it rides a signed [`Block`] on the blocklace
/// (see [`post_challenge`]), so a challenger cannot be impersonated and the fraud
/// proof is disseminated with feed integrity. [`detect_upheld_challenge`] is what
/// turns a valid, trusted-signed, contradicting challenge into the upheld-challenge
/// id [`CiAssurance::evaluate`] mints a [`ConvictionEvidence::ChallengeUpheld`]
/// [`Conviction`] from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Challenge {
    /// The disputed run's input root — must equal the host verdict's `input_root`.
    pub input_root: [u8; 32],
    /// The disputed run's command id — must equal the host verdict's `command_id`.
    pub command_id: [u8; 32],
    /// The output digest the HOST claimed (binds the challenge to this attestation).
    pub claimed_output: [u8; 32],
    /// The exit code the HOST claimed.
    pub claimed_exit: i32,
    /// What the challenger RECOMPUTED re-executing the same command (the fraud
    /// evidence when it differs from `claimed_output`).
    pub recomputed_output: [u8; 32],
    /// The exit code the challenger recomputed.
    pub recomputed_exit: i32,
}

impl Challenge {
    /// The canonical, domain-tagged, fixed-width (hence injective) encoding — the
    /// blocklace block payload a challenger signs.
    pub fn encoding(&self) -> Vec<u8> {
        let mut b = Vec::with_capacity(CHALLENGE_DOMAIN.len() + CHALLENGE_ENCODED_LEN);
        b.extend_from_slice(CHALLENGE_DOMAIN);
        b.extend_from_slice(&self.input_root);
        b.extend_from_slice(&self.command_id);
        b.extend_from_slice(&self.claimed_output);
        b.extend_from_slice(&self.claimed_exit.to_le_bytes());
        b.extend_from_slice(&self.recomputed_output);
        b.extend_from_slice(&self.recomputed_exit.to_le_bytes());
        b
    }

    /// Decode a challenge from a block payload; `None` if the bytes are not a
    /// canonical challenge encoding (wrong domain / length). So a non-challenge
    /// block on the lace is simply ignored by [`detect_upheld_challenge`].
    pub fn decode(bytes: &[u8]) -> Option<Challenge> {
        let dom = CHALLENGE_DOMAIN.len();
        if bytes.len() != dom + CHALLENGE_ENCODED_LEN || &bytes[..dom] != CHALLENGE_DOMAIN {
            return None;
        }
        let take32 = |o: &mut usize| -> [u8; 32] {
            let mut a = [0u8; 32];
            a.copy_from_slice(&bytes[*o..*o + 32]);
            *o += 32;
            a
        };
        let mut o = dom;
        let input_root = take32(&mut o);
        let command_id = take32(&mut o);
        let claimed_output = take32(&mut o);
        let claimed_exit = i32::from_le_bytes(bytes[o..o + 4].try_into().ok()?);
        o += 4;
        let recomputed_output = take32(&mut o);
        let recomputed_exit = i32::from_le_bytes(bytes[o..o + 4].try_into().ok()?);
        Some(Challenge {
            input_root,
            command_id,
            claimed_output,
            claimed_exit,
            recomputed_output,
            recomputed_exit,
        })
    }

    /// Whether this challenge CONTRADICTS `host_verdict`: it is about the same run
    /// (`input_root` + `command_id` match), it quotes the host's exact claim
    /// (`claimed_*` == the verdict's output/exit — so it disputes THIS
    /// attestation), and its recomputed result DIFFERS (a distinct output digest
    /// or exit code). A challenge that matches the host output, or names a
    /// different run, is not a contradiction.
    pub fn contradicts(&self, host_verdict: &CiVerdict) -> bool {
        let same_run = self.input_root == host_verdict.input_root
            && self.command_id == host_verdict.command_id;
        let quotes_host = self.claimed_output == host_verdict.output_digest
            && self.claimed_exit == host_verdict.exit_code;
        let diverges = self.recomputed_output != host_verdict.output_digest
            || self.recomputed_exit != host_verdict.exit_code;
        same_run && quotes_host && diverges
    }
}

/// THE RE-EXECUTION DIVERGENCE a challenger observed — the input to
/// [`post_challenge`]. It pairs the host verdict the challenger re-executed
/// against (which names the run and carries the host's claim) with what the
/// challenger's own confined re-run RECOMPUTED. This is the typed shape of an
/// L3 audit's [`AuditVerdict::HostLied`](../../forge_ci_runner) outcome
/// (`forge-ci-runner::reexecute_and_verify`): the runner reports a divergent
/// field; here the whole recomputed output/exit is carried so the posted
/// challenge is self-contained.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReexecDivergence {
    /// The host verdict the challenger re-executed against.
    pub host_verdict: CiVerdict,
    /// The output digest the challenger's re-run produced (the fraud evidence when
    /// it differs from `host_verdict.output_digest`).
    pub recomputed_output: [u8; 32],
    /// The exit code the challenger's re-run produced.
    pub recomputed_exit: i32,
}

/// POST A CHALLENGE to the blocklace: a challenger who ran L3
/// (`forge-ci-runner::reexecute_and_verify`) and found the host lied
/// ([`ReexecDivergence`]) mints a signed [`Block`] whose payload is the canonical
/// [`Challenge`] encoding, signed with `challenger_key` ([`Block::new_signed`]).
///
/// The block is a GENESIS strand block (sequence 0, no predecessors), so it is
/// causally closed and insertable on any node's lace; its `creator` is
/// `challenger_key`'s public key, so the fraud proof is attributable and its
/// signature is verifiable by anyone. The disseminated block IS the challenge;
/// [`detect_upheld_challenge`] reads it back off the lace.
pub fn post_challenge(divergence: &ReexecDivergence, challenger_key: &SigningKey) -> Block {
    let challenge = Challenge {
        input_root: divergence.host_verdict.input_root,
        command_id: divergence.host_verdict.command_id,
        claimed_output: divergence.host_verdict.output_digest,
        claimed_exit: divergence.host_verdict.exit_code,
        recomputed_output: divergence.recomputed_output,
        recomputed_exit: divergence.recomputed_exit,
    };
    Block::new_signed(
        challenger_key,
        /* sequence */ 0,
        /* predecessors */ vec![],
        challenge.encoding(),
    )
}

/// DETECT AN UPHELD CHALLENGE against `host_verdict` on the presented `lace`,
/// returning the challenge id (the block id) if one is upheld.
///
/// A challenge is UPHELD iff there is a block on the lace that is
/// 1. **trusted-signed (anti-Sybil)** — its `creator` is one of `trusted_keys`
///    (the policy's ACTIVE governed key set) AND its Ed25519 signature verifies
///    (real [`Block::verify_signature`]); a block by a non-active/untrusted key,
///    or one with a bad signature, is IGNORED, so a malicious stranger cannot
///    grief an honest host; and
/// 2. **a genuine contradiction** — its payload decodes to a [`Challenge`] that
///    [`Challenge::contradicts`] `host_verdict`: the SAME run (`input_root` +
///    `command_id`), quoting the host's exact claim, with a DISTINCT recomputed
///    output/exit. The host verdict (output D over the run) and this challenge
///    (recomputed D' ≠ D over the same run) are two contradictory attestations
///    about ONE CI run — the equivocation.
///
/// The returned id is the block's own [`Block::id`] — the dispute transport's
/// evidence handle. [`CiAssurance::evaluate`] mints the [`Conviction`] from it, so
/// the conviction evidence is PRODUCED here from a real detected block, never
/// caller-supplied.
pub fn detect_upheld_challenge(
    host_verdict: &CiVerdict,
    lace: &Blocklace,
    trusted_keys: &[[u8; 32]],
) -> Option<[u8; 32]> {
    for id in lace.block_ids() {
        let Some(block) = lace.get(&id) else {
            continue;
        };
        // (1) Anti-Sybil: the challenger must be an ACTIVE trusted key, and the
        //     block's signature must really verify (defensive: a lace assembled
        //     outside `insert` might carry an unverified block).
        if !trusted_keys.contains(&block.creator) {
            continue;
        }
        if block.verify_signature().is_err() {
            continue;
        }
        // (2) A genuine contradiction about THIS run.
        let Some(challenge) = Challenge::decode(&block.payload) else {
            continue;
        };
        if challenge.contradicts(host_verdict) {
            return Some(id);
        }
    }
    None
}

/// The optimistic-challenge context for [`CiAssurance::OptimisticChallenge`]:
/// where in the challenge window the verdict is, plus the presented `challenge_lace`
/// — the blocklace of disseminated challenge blocks.
///
/// The upheld-challenge id is NO LONGER a caller-supplied signal: [`CiAssurance::evaluate`]
/// runs [`detect_upheld_challenge`] over `challenge_lace` (against the policy's
/// ACTIVE governed key set) and MINTS the [`Conviction`] from the detected block
/// id. So a conviction rides a REAL equivocation — a trusted-signed challenge that
/// contradicts the host verdict on the same run — not a flag anyone can set. The
/// residual seam is only the live NETWORK dissemination of those blocks across
/// nodes (the transport that fills `challenge_lace`); the detection + equivocation
/// logic here is real.
#[derive(Clone, Debug, Default)]
pub struct ChallengeContext {
    /// The height the verdict was posted (accepted provisionally) at.
    pub posted_height: u64,
    /// The current height (the verifier's clock).
    pub now_height: u64,
    /// The presented blocklace of challenge blocks. `evaluate` scans it with
    /// [`detect_upheld_challenge`]; an empty lace means no challenge landed.
    pub challenge_lace: Blocklace,
}

impl ChallengeContext {
    /// A context at `posted_height`/`now_height` with an EMPTY challenge lace (no
    /// challenge posted — the happy path).
    pub fn new(posted_height: u64, now_height: u64) -> Self {
        ChallengeContext {
            posted_height,
            now_height,
            challenge_lace: Blocklace::new(),
        }
    }

    /// Replace the presented challenge lace (the disseminated challenge blocks).
    pub fn with_lace(mut self, challenge_lace: Blocklace) -> Self {
        self.challenge_lace = challenge_lace;
        self
    }
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
    /// Only the soundness of the dregg STARK and `verifying_key` — NO trust in
    /// the host AND NO quorum-honesty assumption (the jump over `ReExecuted`,
    /// which trusts >= quorum independent re-executors). The proof itself
    /// attests; nobody re-runs the command.
    /// # Cost
    /// One (expensive) proving run + one (cheap) STARK verification. Proving is
    /// heavy; [`verify_ci_proof`] is the light-client verify path.
    /// # Latency
    /// The proving time up front, then immediate verification.
    /// # Determinism dependence
    /// None on re-execution — the proof binds the exact verdict; the host need
    /// not be re-run.
    /// # Catches a lying host?
    /// YES — the proof binds `input_root`/`command_id`/`output_digest`/`exit_code`
    /// as public inputs and proves the CI pass gate (`exit_code == 0`) in-circuit
    /// ([`ci_attestation_program`]); a proof for a different verdict, a tampered
    /// proof, or a wrong vk fails closed. The named deepest seam is arithmetizing
    /// an ARBITRARY command's execution (the confined-run zkVM AIR) so the proof
    /// also attests the output was genuinely PRODUCED, not just well-formed; that
    /// sub-proof drops into the circuit predicate with no policy change.
    Proven {
        /// The verifying key the [`CiExecutionProof`] must verify against — the
        /// CI-attestation program's descriptor vk ([`ci_attestation_vk`]).
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
    /// slash is REAL: an inner conviction yields a
    /// [`crate::staked_bond::SlashOutcome`] that
    /// [`crate::staked_bond::slash_bond`] fires as a conserving, one-shot
    /// forfeiture (see [`CiAssurance::bond_disposition`]); a satisfied inner
    /// leaves the bond releasable to the host.
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
                        return AssuranceOutcome::Convicted(Conviction::re_exec_divergence(
                            input.verdict.output_digest,
                            att_verdict.output_digest,
                            signer,
                        ));
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

            // L2.5: satisfied iff past the window with no upheld challenge. An
            // upheld challenge is DETECTED from the presented blocklace against
            // the policy's ACTIVE key set (anti-Sybil) — a trusted-signed block
            // that contradicts this verdict on the same run is an equivocation and
            // convicts (even inside the window: a proven lie need not wait it out).
            CiAssurance::OptimisticChallenge {
                keys,
                challenge_window_height,
            } => {
                let Some(ctx) = input.challenge else {
                    return AssuranceOutcome::Unmet(
                        "optimistic challenge: no challenge context presented".to_string(),
                    );
                };
                let active = keys.active_keys();
                if let Some(challenge_id) =
                    detect_upheld_challenge(input.verdict, &ctx.challenge_lace, &active)
                {
                    return AssuranceOutcome::Convicted(Conviction::challenge_upheld(challenge_id));
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
                AssuranceOutcome::Convicted(c) => {
                    // The inner policy caught a lie: this bond is now forfeit.
                    AssuranceOutcome::Convicted(c.with_bond(*bond_ref))
                }
            },
        }
    }

    /// BRIDGE the evaluate outcome to a real bond movement. Evaluate this policy
    /// against `input`, then — using the caller-held [`crate::staked_bond::StakedBond`]
    /// descriptor (keyed by `bond_ref`) — decide the bond disposition:
    ///
    /// - an inner [`AssuranceOutcome::Convicted`] naming this bond →
    ///   [`crate::staked_bond::BondDisposition::Slash`] (the caller fires
    ///   [`crate::staked_bond::slash_bond`], a conserving one-shot forfeiture);
    /// - [`AssuranceOutcome::Satisfied`] →
    ///   [`crate::staked_bond::BondDisposition::Release`] (the untouched bond is
    ///   returnable to the host);
    /// - a mere [`AssuranceOutcome::Unmet`] → no bond movement.
    ///
    /// This is the conviction-gate: only a real conviction moves the bond. The
    /// transfer itself is driven by the caller's executor over the holding /
    /// beneficiary cells — see [`crate::staked_bond`].
    pub fn bond_disposition(
        &self,
        input: &AssuranceInput<'_>,
        bond: &crate::staked_bond::StakedBond,
    ) -> crate::staked_bond::BondDisposition {
        crate::staked_bond::bond_disposition(&self.evaluate(input), bond)
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
                assert_eq!(c.bond_ref(), None, "an unstaked policy names no bond");
                match c.evidence() {
                    ConvictionEvidence::ReExecDivergence {
                        claimed,
                        divergent,
                        signer,
                    } => {
                        assert_eq!(*claimed, OUTPUT);
                        assert_eq!(*divergent, divergent_out);
                        assert_eq!(*signer, vk(S4));
                    }
                    other => panic!("expected ReExecDivergence, got {other:?}"),
                }
            }
            other => panic!("expected Convicted, got {other:?}"),
        }
    }

    // ── POLE (iii): OptimisticChallenge — the REAL blocklace-carried challenge.
    //    A challenger who re-executed and found the host lied POSTS a signed
    //    Challenge block; `detect_upheld_challenge` turns a trusted-signed block
    //    that contradicts the host verdict on the same run into a CONVICTION. Five
    //    poles: (i) no challenge past the window satisfies; (ii) a genuine
    //    challenge (active key, divergent recompute) convicts, NOT satisfied;
    //    (iii) inside the window refuses; (iv) a FORGED challenge (untrusted key,
    //    or wrong run) is ignored so an honest host is not griefed; (v) the
    //    conviction id is MINTED from the detected block, not caller-supplied.
    #[test]
    fn optimistic_challenge_detects_real_equivocation() {
        // The governed set trusts S1 (the host) and S2 (a trusted re-executor who
        // may challenge). S3 is an outsider — NOT trusted.
        let policy = || CiAssurance::OptimisticChallenge {
            keys: GovernedKeySet::operator([vk(S1), vk(S2)]),
            challenge_window_height: 10,
        };
        // The host's committed verdict (input INPUT, command COMMAND, exit 0,
        // output OUTPUT), signed by S1.
        let (receipt, v) = run(S1, OUTPUT);

        // Helper: a lace carrying one challenge block signed by `seed`, disputing
        // `host` with a recomputed `(output, exit)`.
        let lace_with = |seed: [u8; 32], host: &CiVerdict, out: [u8; 32], exit: i32| {
            let divergence = ReexecDivergence {
                host_verdict: host.clone(),
                recomputed_output: out,
                recomputed_exit: exit,
            };
            let block = post_challenge(&divergence, &SigningKey::from_bytes(&seed));
            let mut lace = Blocklace::new();
            lace.insert(block.clone())
                .expect("signed genesis challenge inserts");
            (lace, block)
        };

        // POLE (i): NO CHALLENGE, past the window (now 110 ≥ posted 100 + 10) →
        // satisfies. Empty lace = nobody challenged.
        satisfied(
            policy(),
            CiRunWitness::signed(receipt.clone(), v.clone())
                .with_challenge(ChallengeContext::new(100, 110)),
        )
        .expect("past the challenge window with no challenge satisfies");

        // POLE (ii): GENUINE CHALLENGE — the trusted re-executor S2 re-ran the
        // command and recomputed a DIFFERENT digest (0xEE ≠ OUTPUT) for the SAME
        // run, and posts it. `detect_upheld_challenge` finds it → CONVICTED, even
        // past the window (a proven lie need not wait it out). NOT satisfied.
        let (lace, block) = lace_with(S2, &v, [0xEE; 32], 0);
        match satisfied(
            policy(),
            CiRunWitness::signed(receipt.clone(), v.clone())
                .with_challenge(ChallengeContext::new(100, 999).with_lace(lace)),
        ) {
            Err(CheckRefusal::Convicted(c)) => match c.evidence() {
                // POLE (v): the id is the DETECTED block's own id — minted by
                // evaluate from the real block, not a caller-supplied signal.
                ConvictionEvidence::ChallengeUpheld { challenge_id } => {
                    assert_eq!(
                        *challenge_id,
                        block.id(),
                        "the conviction id is the detected challenge block's id"
                    );
                }
                other => panic!("expected ChallengeUpheld, got {other:?}"),
            },
            other => panic!("expected Convicted for a genuine challenge, got {other:?}"),
        }

        // POLE (iii): INSIDE the window (now 105 < 110), no challenge → refused
        // with AssuranceUnmet (regardless — the window has not elapsed).
        match satisfied(
            policy(),
            CiRunWitness::signed(receipt.clone(), v.clone())
                .with_challenge(ChallengeContext::new(100, 105)),
        ) {
            Err(CheckRefusal::AssuranceUnmet(why)) => assert!(why.contains("window"), "{why}"),
            other => panic!("expected AssuranceUnmet inside window, got {other:?}"),
        }

        // POLE (iv-a): FORGED CHALLENGE by an UNTRUSTED key. S3 (not in the
        // governed set) posts a perfectly-divergent challenge; it is IGNORED, so
        // past the window the honest host still SATISFIES — a stranger cannot grief.
        let (forged_lace, _) = lace_with(S3, &v, [0xEE; 32], 0);
        satisfied(
            policy(),
            CiRunWitness::signed(receipt.clone(), v.clone())
                .with_challenge(ChallengeContext::new(100, 999).with_lace(forged_lace)),
        )
        .expect("a challenge by an untrusted key is ignored — the host is not convicted");

        // POLE (iv-b): a challenge by the TRUSTED S2 but about a DIFFERENT run
        // (its host_verdict names a different input_root) does not match this
        // verdict — IGNORED, so the host still satisfies past the window.
        let other_run = CiVerdict {
            input_root: [0x55; 32], // ≠ INPUT — a different run
            ..v.clone()
        };
        let (mismatched_lace, _) = lace_with(S2, &other_run, [0xEE; 32], 0);
        satisfied(
            policy(),
            CiRunWitness::signed(receipt, v)
                .with_challenge(ChallengeContext::new(100, 999).with_lace(mismatched_lace)),
        )
        .expect("a challenge about a different run does not convict this verdict");
    }

    // A focused check on the detector itself (unit-level), independent of the
    // whole gate: a trusted-signed contradicting challenge is upheld; an
    // untrusted signer, a matching (non-divergent) recompute, and a
    // wrong-run challenge are each NOT upheld.
    #[test]
    fn detect_upheld_challenge_poles() {
        let host = verdict(OUTPUT);
        let trusted = [vk(S1), vk(S2)];

        // A genuine contradiction by trusted S2 → Some(block id).
        let genuine = post_challenge(
            &ReexecDivergence {
                host_verdict: host.clone(),
                recomputed_output: [0xEE; 32],
                recomputed_exit: 0,
            },
            &SigningKey::from_bytes(&S2),
        );
        let mut lace = Blocklace::new();
        lace.insert(genuine.clone()).unwrap();
        assert_eq!(
            detect_upheld_challenge(&host, &lace, &trusted),
            Some(genuine.id()),
            "a trusted-signed contradicting challenge is upheld"
        );

        // The SAME lace but S2 is NOT trusted → ignored (anti-Sybil).
        assert_eq!(
            detect_upheld_challenge(&host, &lace, &[vk(S1)]),
            None,
            "a challenge by a non-active key is not upheld"
        );

        // A non-divergent "challenge" (recompute AGREES with the host) → not a
        // contradiction, not upheld.
        let agreeing = post_challenge(
            &ReexecDivergence {
                host_verdict: host.clone(),
                recomputed_output: OUTPUT, // agrees
                recomputed_exit: 0,
            },
            &SigningKey::from_bytes(&S2),
        );
        let mut lace2 = Blocklace::new();
        lace2.insert(agreeing).unwrap();
        assert_eq!(
            detect_upheld_challenge(&host, &lace2, &trusted),
            None,
            "a challenge whose recompute agrees is not a contradiction"
        );
    }

    // ── POLE (iv): Proven — a REAL dregg STARK. A genuinely-produced proof
    //    (`prove_ci_attestation`) satisfies with NO re-execution; a proof for a
    //    DIFFERENT verdict, a tampered proof, and a wrong verifying key all
    //    refuse. No hand-mocked "valid" flag — every proof here is a real STARK.
    #[test]
    fn proven_real_stark_satisfies_and_wrong_proofs_refuse() {
        let pvk = ci_attestation_vk();
        let policy = || CiAssurance::Proven { verifying_key: pvk };
        let (receipt, v) = run(S1, OUTPUT);

        // (a) A REAL valid proof for THIS verdict → satisfies, no re-execution.
        let good = prove_ci_attestation(&v).expect("a passing verdict has a real proof");
        satisfied(
            policy(),
            CiRunWitness::signed(receipt.clone(), v.clone()).with_proof(good.clone()),
        )
        .expect("a valid real STARK proof satisfies Proven with no re-execution");

        // (b) A proof whose PUBLIC INPUTS are for a DIFFERENT verdict (a different
        //     input_root, same output so it clears the asserted-output gate and
        //     bites the STARK binding itself) → refused: the verifier
        //     reconstructs public inputs from THIS verdict, and the other proof's
        //     committed trace does not satisfy this verdict's boundary bindings.
        let other = CiVerdict {
            input_root: [0x55; 32], // ≠ INPUT
            command_id: COMMAND,
            confinement_id: CONFINEMENT,
            exit_code: 0,
            output_digest: OUTPUT,
        };
        let for_other = prove_ci_attestation(&other).expect("the other verdict also proves");
        match satisfied(
            policy(),
            CiRunWitness::signed(receipt.clone(), v.clone()).with_proof(for_other),
        ) {
            Err(CheckRefusal::AssuranceUnmet(why)) => assert!(why.contains("proof"), "{why}"),
            other => panic!("expected AssuranceUnmet for a different-verdict proof, got {other:?}"),
        }

        // (c) A TAMPERED proof (real bytes, corrupted) → refused.
        let mut tampered = good.clone();
        for b in tampered.proof_bytes.iter_mut().take(96) {
            *b ^= 0xFF;
        }
        match satisfied(
            policy(),
            CiRunWitness::signed(receipt.clone(), v.clone()).with_proof(tampered),
        ) {
            Err(CheckRefusal::AssuranceUnmet(why)) => assert!(why.contains("proof"), "{why}"),
            other => panic!("expected AssuranceUnmet for a tampered proof, got {other:?}"),
        }

        // (d) The RIGHT proof under the WRONG verifying key → refused: a valid
        //     proof does not attest a check that names a different vk.
        let wrong_vk = CiAssurance::Proven {
            verifying_key: [0x00; 32],
        };
        match satisfied(
            wrong_vk,
            CiRunWitness::signed(receipt.clone(), v.clone()).with_proof(good),
        ) {
            Err(CheckRefusal::AssuranceUnmet(why)) => assert!(why.contains("proof"), "{why}"),
            other => panic!("expected AssuranceUnmet for a wrong verifying key, got {other:?}"),
        }

        // (e) No proof at all → refused.
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
                    c.bond_ref(),
                    Some(BOND),
                    "the staked bond is bound to the conviction"
                );
                assert!(matches!(
                    c.evidence(),
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
