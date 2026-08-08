//! The shielded **OFF-RAMP**: spend a hidden note, credit the CLEARTEXT ledger, nullify the note.
//!
//! **SAY THE SUBSTRATE OUT LOUD: every AIR here is AUTHORED IN LEAN.** The spend side is
//! `metatheory/Dregg2/Circuit/Emit/ShieldedSpendCompleteEmit.lean`
//! (`dregg-shielded-spend-complete-fsi2::v1`, 557 columns, 25 PIs); the value link is
//! `metatheory/Dregg2/Circuit/Emit/ShieldedDeshieldValueLinkEmit.lean`
//! (`dregg-shielded-deshield-value-link::v1`, 161 columns, 24 PIs). Both are read byte-pinned out
//! of the Lean sources. This module authors NO constraint: it assembles witnesses and calls the
//! Lean-emitted relations' provers/verifiers.
//!
//! ## The gap this closes
//!
//! Value could ENTER the pool (`Effect::Shield` — debit a cleartext note, append a bound shielded
//! leaf) and MOVE inside it (`ShieldedTransfer` — one leaf to another, bound by
//! `dregg-shielded-transfer-value-link::v1`). **It could never leave.** There was no `Deshield`, so
//! every note that entered was trapped: the accumulator holds one leaf shape, every leaf is
//! spendable *within* the pool, and the only exit was another in-pool leaf. A one-way money-mover
//! is not a privacy pool.
//!
//! ## The object
//!
//! 1. **Owner / membership / no-double-spend / value carrier — the hidden spend side.** One
//!    [`ShieldedSpendCompleteProof`](super::spend_complete::ShieldedSpendCompleteProof), identical
//!    to the one a transfer spends with. Value, asset, owner, spending key, randomness, blinding
//!    and the whole membership path stay witness-only; the proof publishes only
//!    `(nullifier, committedRoot[8], wide[16])`.
//! 2. **Value — the hidden value link, made public at exactly one point.** One deshield value-link
//!    proof. Its sixteen carrier PIs are the SPEND's own, supplied by this module after that proof
//!    verified; its eight remaining PIs are the canonical 16-bit limbs of the CLEARTEXT CREDIT,
//!    supplied from the effect's declared `(value, asset_type)`. The relation reads one set of limb
//!    columns for both, so the credit is worth exactly the spent note.
//!
//! ## The mirror, stated exactly
//!
//! `Effect::Shield` is: verify the mint opening, check `value == piVALUE`, DEBIT the cleartext
//! note, APPEND the shielded leaf. `Effect::Deshield` is the same four beats reflected: verify the
//! spend under the committed root, bind the credit to the note's carrier IN THE AIR, NULLIFY the
//! shielded note, CREDIT the cleartext ledger.
//!
//! The one asymmetry is where the conservation lives, and it is an improvement rather than a
//! difference of taste. Shield's boundary equality `value == piVALUE` is an executor-side `u64`
//! comparison against a number the shield-opening proof published (sound, because the opening's
//! `.piBinding`s force it, but it is a comparison in Rust). Deshield has no such comparison to
//! make: the credit's limbs ARE public inputs of the relation, pinned to the very columns the
//! carrier absorbs, so the executor never compares two values — it hands the relation the two ends
//! of the boundary and the relation refuses unless they are one opening.
//!
//! ## Deployed arity, and what is REFUSED
//!
//! ONE spent note, ONE cleartext credit, equal value — a WHOLE-note deshield.
//! [`ShieldedDeshield::verify`] REFUSES anything else BY NAME rather than admitting an arity whose
//! conservation this descriptor does not state. A PARTIAL deshield (credit some, keep a shielded
//! change note) is the next descriptor in the Lean family: it needs the limbwise carry chain
//! `v_in_i = credit_i + change_i − 65536·c_i + c_{i−1}`, `c_i` boolean, `c_3 = 0`, plus a
//! `hash_fact` site for the change note. Widening the arity cannot reopen the value link — every
//! member of the family reads its values off the same limb columns its carriers absorb.
//!
//! ## The privacy residual, named
//!
//! A deshield **reveals the value and the asset** of the note it spends, because the cleartext
//! credit is public and a credit nobody can read is not a credit. What stays hidden is WHICH leaf
//! was spent, its owner, its spending key, its randomness and its membership path.

use dregg_circuit::exact_nullifier_aafi::Digest8;
use dregg_circuit::field::BabyBear;

use crate::shielded::deshield_link::{
    ShieldedDeshieldLinkError, ShieldedDeshieldLinkWitness, prove_shielded_deshield_link,
    verify_shielded_deshield_link,
};
use crate::shielded::spend_complete::{
    ShieldedSpendCompleteError, ShieldedSpendCompleteWitness, prove_shielded_spend_complete,
    verify_shielded_spend_complete_parts,
};
use crate::shielded::transfer::{ShieldedError, ShieldedInputProof};

/// The CLEARTEXT side of a deshield: what the ledger is asked to credit, and the proof that binds
/// it to the note being spent.
///
/// **There is no commitment here and no value the prover chose in a hiding form.** `value` and
/// `asset_type` are plain public `u64`s — that is the point of an off-ramp — and `link_proof` is
/// what makes them not merely *asserted*: the Lean relation pins their canonical 16-bit limbs to
/// the same columns the spent note's carrier absorbs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeshieldCredit {
    /// The cleartext value to credit. Public.
    pub value: u64,
    /// The cleartext asset to credit. Public, and bound: a note denominated in `A` cannot fund a
    /// credit in `A'` (Lean `substituted_credit_asset_unsat`).
    pub asset_type: u64,
    /// Canonical postcard bytes of the hiding value-link proof — an
    /// `Ir2BatchProof<DreggZkStarkConfig>` against `dregg-shielded-deshield-value-link::v1`.
    pub link_proof: Vec<u8>,
}

/// A published shielded deshield (circuit side).
///
/// What a verifier sees: one hidden complete-spend proof (revealing only its nullifier and its wide
/// value carrier), and a public `(value, asset_type)` credit with its value-link proof. What stays
/// hidden: which leaf was spent, its owner and spending key, its Merkle path, its randomness. What
/// is NOT here, by construction: any root the prover chose, and any credit the prover chose
/// *freely* — the credit is public, but it is not free.
///
/// (Not `Clone`/`Debug`: holds `Ir2BatchProof`s.)
pub struct ShieldedDeshield {
    /// The spent notes' hidden complete-spend proofs.
    pub inputs: Vec<ShieldedInputProof>,
    /// The cleartext credit and its binding proof.
    pub credit: DeshieldCredit,
}

/// The deployed arity: exactly one spent note per deshield. See the module docs — this is a
/// REFUSAL, not a silent restriction, and widening it is a new descriptor in the Lean family.
pub const DEPLOYED_DESHIELD_INPUTS: usize = 1;

impl ShieldedDeshield {
    /// **The whole deployed gate.** In order:
    ///
    /// 1. every input's hidden complete-spend proof verifies with `committed_root` as its 8-lane
    ///    `piCommitted`, and the nullifiers are pairwise distinct (no in-deshield double-spend);
    /// 2. the arity is the one the value-link descriptor states;
    /// 3. the value-link proof verifies against **the spend proof's own carrier** and **the public
    ///    credit about to be landed** — so the cleartext credit equals exactly the value the spent
    ///    note holds.
    ///
    /// ⚑ `committed_root` MUST come from live executor state
    /// (`TurnExecutor::note_shielded.root8().limbs()`), never from the payload — there is no
    /// payload field it could come from. A proof folded in the attacker's own tree reaches
    /// `R ≠ committed_root` and the Lean-emitted 8-lane `rootPins` `.piBinding` then has no
    /// satisfying assignment: the spend REFUSES. That is seam #15, inherited.
    ///
    /// ⚑ Step 3 runs AFTER step 1, and that ordering is load-bearing. The carrier handed to the
    /// link is a public input of a proof that has already verified, not a claim the link proof
    /// carries about itself.
    pub fn verify(&self, committed_root: Digest8) -> Result<(), DeshieldError> {
        // ── 1. the spend side, under the executor's root
        if self.inputs.is_empty() {
            return Err(DeshieldError::NoInputs);
        }
        for (i, input) in self.inputs.iter().enumerate() {
            // THE SUBSTITUTION: the claim is assembled HERE, around the executor's root. The wire
            // supplied the nullifier, the carrier and the proof bytes — never the root.
            let claim = input.claim_for(committed_root);
            verify_shielded_spend_complete_parts(&claim, &input.proof).map_err(|e| {
                DeshieldError::InputProofRejected {
                    input_index: i,
                    reason: format!("{e}"),
                }
            })?;
        }
        for i in 0..self.inputs.len() {
            for j in (i + 1)..self.inputs.len() {
                if self.inputs[i].nullifier == self.inputs[j].nullifier {
                    return Err(DeshieldError::DuplicateNullifier { a: i, b: j });
                }
            }
        }

        // ── 2. the arity the value-link descriptor states
        if self.inputs.len() != DEPLOYED_DESHIELD_INPUTS {
            return Err(DeshieldError::UnsupportedArity {
                inputs: self.inputs.len(),
            });
        }

        // ── 3. ⚑ THE OFF-RAMP VALUE LINK. Both ends of the boundary are supplied here: the
        // carrier from the already-verified spend, the credit from the public effect fields. The
        // relation forces them to be one limb opening or has no satisfying trace.
        verify_shielded_deshield_link(
            &self.credit.link_proof,
            &self.inputs[0].spend_wide_binding,
            self.credit.value,
            self.credit.asset_type,
        )
        .map_err(|source| DeshieldError::CreditLinkRejected {
            reason: source.to_string(),
        })?;
        Ok(())
    }

    /// The set of nullifiers this deshield spends (what the chain's nullifier set must reject if
    /// any are already present — the cross-turn double-spend gate, and the reason a note cannot be
    /// deshielded twice).
    pub fn nullifiers(&self) -> Vec<BabyBear> {
        self.inputs.iter().map(|i| i.nullifier).collect()
    }

    /// Reconstruct a published deshield from its **serialized wire parts** — the executor's
    /// `Effect::Deshield` payload.
    ///
    /// ⚑ There is no `merkle_root` parameter and there never can be one: the committed root enters
    /// only at [`verify`](Self::verify), from executor state.
    ///
    /// Every public field element must use its canonical BabyBear integer encoding; accepting
    /// `x + p` here would reintroduce exactly the alias the wide carrier exists to remove.
    pub fn from_serialized_parts(
        inputs: Vec<(u32, [u32; 16], Vec<u8>)>,
        value: u64,
        asset_type: u64,
        link_proof: Vec<u8>,
    ) -> Result<Self, DeshieldError> {
        let ins = ShieldedInputProof::many_from_serialized_parts(inputs).map_err(|e| match e {
            ShieldedError::NonCanonicalPublicField {
                input_index,
                lane,
                value,
            } => DeshieldError::NonCanonicalPublicField {
                input_index,
                lane,
                value,
            },
            other => DeshieldError::ProofDecode {
                reason: other.to_string(),
            },
        })?;
        Ok(ShieldedDeshield {
            inputs: ins,
            credit: DeshieldCredit {
                value,
                asset_type,
                link_proof,
            },
        })
    }
}

/// Witness for building a deshield: the spent note's full opening + spending key + its
/// authenticated place in the COMMITTED shielded accumulator (all hidden).
///
/// **There is no credit field, and that absence is the point.** What the cleartext side receives is
/// the spent note's value, read off the same limb columns by the Lean relation and published there.
#[derive(Clone, Debug)]
pub struct ShieldedDeshieldWitness {
    /// The hidden complete-spend witness (note opening, key, blinding, membership path).
    pub spend: ShieldedSpendCompleteWitness,
}

impl ShieldedDeshieldWitness {
    /// The value-link witness this deshield's credit needs.
    pub fn link_witness(&self) -> ShieldedDeshieldLinkWitness {
        ShieldedDeshieldLinkWitness {
            value: self.spend.value,
            asset_type: self.spend.asset_type,
            in_randomness: self.spend.randomness,
            in_binding_blind: self.spend.binding_blind,
        }
    }
}

/// Build a complete deshield at the deployed arity: one spent note in, one cleartext credit out,
/// equal value by construction of the Lean relation.
///
/// ⚑ No `merkle_root` parameter: which tree the input must be a member of is decided by the
/// EXECUTOR at verification. ⚑ No credit parameter: what the cleartext side receives is decided by
/// the note being spent, not by the prover at all — the returned [`DeshieldCredit`] carries the
/// value the relation published.
pub fn prove_shielded_deshield(
    witness: &ShieldedDeshieldWitness,
) -> Result<ShieldedDeshield, DeshieldError> {
    let proof = prove_shielded_spend_complete(&witness.spend)
        .map_err(|e| DeshieldError::ProveFailed { reason: e })?;
    let input = ShieldedInputProof {
        nullifier: proof.claim.nullifier,
        spend_wide_binding: proof.claim.wide_binding,
        proof: proof.proof,
    };
    let link_witness = witness.link_witness();
    let link = prove_shielded_deshield_link(&link_witness)
        .map_err(|e| DeshieldError::LinkProveFailed { reason: e })?;
    // The credit is READ OFF the proof's published limbs, never re-read from the witness: what
    // lands on the wire is what the relation published, so a construction-side mismatch cannot
    // exist.
    let (value, asset_type) = link
        .claim
        .credit()
        .map_err(|e| DeshieldError::LinkProveFailed { reason: e })?;
    Ok(ShieldedDeshield {
        inputs: vec![input],
        credit: DeshieldCredit {
            value,
            asset_type,
            link_proof: link.proof_bytes(),
        },
    })
}

/// Errors from deshield construction / verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeshieldError {
    /// A deshield must spend a note.
    NoInputs,
    /// Proving the hidden complete-spend proof failed.
    ProveFailed { reason: ShieldedSpendCompleteError },
    /// Proving the credit's value link failed.
    LinkProveFailed { reason: ShieldedDeshieldLinkError },
    /// An input's hidden proof did not verify against the EXECUTOR-SUPPLIED committed root.
    InputProofRejected { input_index: usize, reason: String },
    /// Two inputs carry the same nullifier (in-deshield double-spend).
    DuplicateNullifier { a: usize, b: usize },
    /// A serialized input proof failed to deserialize.
    ProofDecode { reason: String },
    /// A wire public field element is not the canonical BabyBear integer encoding.
    NonCanonicalPublicField {
        input_index: usize,
        lane: usize,
        value: u32,
    },
    /// **THE OFF-RAMP REFUSAL.** The public cleartext credit is not bound by a valid value-link
    /// proof to the carrier the complete-spend proof published — i.e. the ledger is being asked to
    /// credit something other than what the spent note holds.
    CreditLinkRejected { reason: String },
    /// The deshield's arity is not the one the deployed value-link descriptor states. Refused
    /// rather than admitted: there is no descriptor whose conservation covers it.
    UnsupportedArity { inputs: usize },
}

impl core::fmt::Display for DeshieldError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::NoInputs => write!(f, "shielded deshield has no inputs"),
            Self::ProveFailed { reason } => {
                write!(f, "shielded deshield input proving failed: {reason}")
            }
            Self::LinkProveFailed { reason } => {
                write!(f, "shielded deshield value-link proving failed: {reason}")
            }
            Self::InputProofRejected {
                input_index,
                reason,
            } => write!(
                f,
                "shielded deshield input {input_index} complete-spend proof rejected under the \
                 executor-committed root: {reason}"
            ),
            Self::DuplicateNullifier { a, b } => write!(
                f,
                "shielded deshield inputs {a} and {b} share a nullifier (double-spend)"
            ),
            Self::ProofDecode { reason } => {
                write!(f, "shielded deshield proof failed to deserialize: {reason}")
            }
            Self::NonCanonicalPublicField {
                input_index,
                lane,
                value,
            } => write!(
                f,
                "shielded deshield input {input_index} public lane {lane} value {value} is not \
                 canonical BabyBear"
            ),
            Self::CreditLinkRejected { reason } => write!(
                f,
                "shielded deshield credit link rejected — the cleartext credit is not the value \
                 the spent note holds: {reason}"
            ),
            Self::UnsupportedArity { inputs } => write!(
                f,
                "shielded deshield arity {inputs}-in is not stated by the deployed value-link \
                 descriptor (which states {DEPLOYED_DESHIELD_INPUTS}-in); refused rather than \
                 admitted"
            ),
        }
    }
}

impl std::error::Error for DeshieldError {}
