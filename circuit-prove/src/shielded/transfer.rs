//! The shielded transfer: **complete FSI2 spend** per input (membership in the executor's COMMITTED
//! shielded accumulator + nullifier derivation + the full-`u64` wide value carrier), welded to the
//! minted note by the **value-link relation**.
//!
//! **SAY THE SUBSTRATE OUT LOUD: every AIR here is AUTHORED IN LEAN.** The spend side is
//! `metatheory/Dregg2/Circuit/Emit/ShieldedSpendCompleteEmit.lean`
//! (`dregg-shielded-spend-complete-fsi2::v1`, 557 columns, 25 PIs); the value link is
//! `metatheory/Dregg2/Circuit/Emit/ShieldedTransferValueLinkEmit.lean`
//! (`dregg-shielded-transfer-value-link::v1`, 164 columns, 17 PIs). Both are read byte-pinned out
//! of the Lean sources. This module authors NO constraint: it assembles witnesses and calls the
//! Lean-emitted relations' provers/verifiers.
//!
//! ## ⚑ FLAG DAY — the Pedersen leg is DELETED (the value-link residual)
//!
//! The retired object carried, per input and per output, a Ristretto `ShieldedValueLeg` — a
//! Pedersen value commitment the PROVER chose — plus a Schnorr conservation proof over
//! `Σ C_in = Σ C_out` and a Bulletproof range proof per output. Seam #15's lane wrote down what
//! that left open, verbatim:
//!
//! > the Pedersen leg's own `v` is bound to the STARK-side `v` only through this TRANSCRIPT, not by
//! > an equality the circuit enforces … it does not make either of them open the value the
//! > Ristretto commitment holds.
//!
//! So a spender who genuinely owned a note worth `1` published legs committing to `1_000_000`,
//! conservation cleared over those legs, the spend STARK proved the real note, and nothing compared
//! them. **That gap cannot be checked shut.** A BabyBear STARK cannot open a Ristretto point
//! without non-native curve arithmetic in-AIR; a Ristretto sigma protocol cannot open a Poseidon2
//! image without the hash in-group. `cell-crypto/src/value_link_zk.rs` reached the same conclusion
//! and named the exit — *"faithfully encode value/asset in a wide in-AIR hash commitment and
//! enforce no-mint in AIR"* — which is what this file now does.
//!
//! **WHAT RE-EMITS / WHAT REFUSES TO LOAD.** `ShieldedTransferPayload` has no `input_legs`, no
//! `output_legs`, no `output_range_proofs` and no `conservation` field; a pre-cutover payload does
//! not decode as a current one. `ShieldedValueLeg` is gone. `wide_transfer_message` and
//! `verify_stark_with_wide_bindings` are gone with the transcript they served, and the wide sidecar
//! is no longer on the transfer path at all: the value-link relation proves everything the sidecar
//! proved about the input carrier, plus the tie to the output. `dregg-shielded-transfer-value-link::v1`
//! is a NEW descriptor and needs its VK epoch rolled with the shielded family.
//!
//! ## The object, now
//!
//! 1. **Owner / membership / no-double-spend / value carrier — the hidden spend side.** One
//!    [`ShieldedSpendCompleteProof`](super::spend_complete::ShieldedSpendCompleteProof) per input.
//!    Value, asset, owner, spending key, randomness, blinding and the whole membership path stay
//!    witness-only; the proof publishes only `(nullifier, committedRoot[8], wide[16])`.
//! 2. **Value — the hidden value link.** One value-link proof per output. Its sixteen carrier PIs
//!    are the SPEND's own, supplied by this module after that proof verified; its seventeenth PI is
//!    the minted note's commitment. The relation reads one set of limb columns for both, so the
//!    minted note is worth exactly the spent note.
//!
//! Range proofs are gone and not missed: `value` rides four canonical 16-bit limb cells whose
//! booleanity is FORCED in the AIR, so `0 ≤ value < 2^64` is a property of the trace. The
//! negative-value inflation hole the Bulletproofs guarded existed only because the Pedersen group
//! has no notion of range.
//!
//! ## The deployed arity, stated
//!
//! ONE input, ONE output, equal value — a whole-note transfer (a change of owner).
//! [`ShieldedTransfer::verify`] REFUSES anything else rather than admitting an arity whose
//! conservation this descriptor does not state. Splitting (`1-in / 2-out` with change) is the next
//! descriptor in the Lean family: it needs the limbwise carry chain
//! `v_in_i = o1_i + o2_i − 65536·c_i + c_{i−1}`, `c_i` boolean, `c_3 = 0`. Widening the arity
//! cannot reopen the value link — every member of the family reads its values off the same limb
//! columns its carriers absorb.

use dregg_circuit::descriptor_ir2::Ir2BatchProof;
use dregg_circuit::exact_nullifier_aafi::Digest8;
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::stark_zk::DreggZkStarkConfig;

use crate::shielded::spend_complete::{
    ShieldedSpendCompleteClaim, ShieldedSpendCompleteError, ShieldedSpendCompleteWitness,
    WIDE_LANES, prove_shielded_spend_complete, verify_shielded_spend_complete_parts,
};
use crate::shielded::transfer_link::{
    ShieldedTransferLinkError, ShieldedTransferLinkWitness, note_commitment_felt_from_bytes,
    prove_shielded_transfer_link, verify_shielded_transfer_link,
};

/// One spent input's **hidden complete-spend proof**.
///
/// The proof is the Lean-emitted `dregg-shielded-spend-complete-fsi2::v1` relation run through the
/// hiding IR-v2 backend, so its openings reveal nothing about the witness (value, asset, owner,
/// spending key, randomness, blinding, the whole membership path) beyond the published claim.
///
/// Two of the claim's three parts ride here. **The third — the committed root — deliberately does
/// not**: it is supplied at verification time from executor state, so a payload has no field in
/// which to publish a root of its own choosing. That absence IS the #15 fix.
pub struct ShieldedInputProof {
    /// The revealed nullifier (the chain's double-spend tag for this input), PI 0. The Lean
    /// `nulPin` forces it to equal the in-trace `hash_fact(cCM,[key0..3])`, so a spend cannot
    /// publish a nullifier for a note it did not open.
    pub nullifier: BabyBear,
    /// **The ring-side full-`u64` wide value/asset carrier**, PI 9..25 — the sixteen
    /// domain-separated `cap_node8` lanes the Lean `carrierPins` pin to the note's canonical limb
    /// opening. This is the carrier the value-link proof is judged against; it is bound by THIS
    /// proof, which is what makes the link a binding rather than a self-referential claim.
    pub spend_wide_binding: [BabyBear; WIDE_LANES],
    /// The hiding complete-spend proof (membership + nullifier + owner derivation + carrier).
    pub proof: Ir2BatchProof<DreggZkStarkConfig>,
}

impl ShieldedInputProof {
    /// Serialize this input's hidden complete-spend proof for transport inside an executor
    /// `Effect` payload — the canonical postcard encoding
    /// [`ShieldedTransfer::from_serialized_parts`] reads back.
    pub fn proof_bytes(&self) -> Vec<u8> {
        postcard::to_allocvec(&self.proof).expect("Ir2BatchProof postcard serialize")
    }

    /// The public claim this input's proof is checked against, pinned to the **executor-supplied**
    /// committed root. The caller cannot substitute a root: it is this argument or nothing.
    fn claim(&self, committed_root: Digest8) -> ShieldedSpendCompleteClaim {
        ShieldedSpendCompleteClaim {
            nullifier: self.nullifier,
            committed_root,
            wide_binding: self.spend_wide_binding,
        }
    }
}

/// One minted output: the note commitment the executor will append, and the value-link proof that
/// binds it to a spent input's carrier.
///
/// There is no value here and no commitment to a value the prover chose — the commitment is a
/// Poseidon2 note commitment `hash_fact(v,[a,owner,rand])`, the SAME shape the complete-spend
/// relation opens, so the note it names is SPENDABLE. That identity is what makes "value conserved"
/// mean something: the value that arrives can leave again, through the same circuit.
pub struct ShieldedOutput {
    /// The minted note's commitment, `dregg_cell::felt_to_bytes32` encoded — four little-endian
    /// bytes and twenty-eight zero. Anything else refuses (a leaf outside that subspace could be
    /// appended and never opened again).
    pub note_commitment: [u8; 32],
    /// The serialized Lean-emitted value-link proof for this output.
    pub link_proof: Vec<u8>,
}

/// A published shielded transfer (circuit side).
///
/// What a verifier sees: one hidden complete-spend proof per input (each revealing only its
/// nullifier and its wide value carrier), and one minted note commitment per output with its
/// value-link proof. What stays hidden: every note's value, asset, owner and spending key, every
/// Merkle path, and both randomnesses. What is NOT here, by construction: any root the prover
/// chose, and any value the prover chose.
///
/// (Not `Clone`/`Debug`: holds `Ir2BatchProof`s.)
pub struct ShieldedTransfer {
    /// One hidden complete-spend proof per spent input.
    pub inputs: Vec<ShieldedInputProof>,
    /// One minted note per output, each with its value-link proof.
    pub outputs: Vec<ShieldedOutput>,
}

/// The deployed arity: one input, one output. See the module docs — this is a REFUSAL, not a
/// silent restriction, and widening it is a new descriptor in the Lean family.
pub const DEPLOYED_INPUTS: usize = 1;
/// The deployed output arity.
pub const DEPLOYED_OUTPUTS: usize = 1;

impl ShieldedTransfer {
    /// **The whole deployed gate.** In order:
    ///
    /// 1. every input's hidden complete-spend proof verifies with `committed_root` as its 8-lane
    ///    `piCommitted`, and the nullifiers are pairwise distinct (no in-transfer double-spend);
    /// 2. the arity is the one the value-link descriptor states;
    /// 3. every output's value-link proof verifies against **the spend proof's own carrier** and
    ///    **the note commitment about to be appended** — so the minted note opens to exactly the
    ///    value the spent note holds.
    ///
    /// ⚑ `committed_root` MUST come from live executor state
    /// (`TurnExecutor::note_shielded.root8().limbs()`), never from the payload — there is no
    /// payload field it could come from. A proof folded in the attacker's own tree reaches
    /// `R ≠ committed_root` and the Lean-emitted 8-lane `rootPins` `.piBinding` then has no
    /// satisfying assignment: the spend REFUSES. That refusal is the whole of seam #15.
    ///
    /// ⚑ Step 3 runs AFTER step 1, and that ordering is load-bearing. The carrier handed to the
    /// link is a public input of a proof that has already verified, not a claim the link proof
    /// carries about itself — the discipline `ShieldedWideJoinPin.join_still_decouples` names.
    pub fn verify(&self, committed_root: Digest8) -> Result<(), ShieldedError> {
        // ── 1. the spend side, under the executor's root
        if self.inputs.is_empty() {
            return Err(ShieldedError::NoInputs);
        }
        for (i, input) in self.inputs.iter().enumerate() {
            // THE SUBSTITUTION: the claim is assembled HERE, around the executor's root. The wire
            // supplied the nullifier, the carrier and the proof bytes — never the root.
            let claim = input.claim(committed_root);
            verify_shielded_spend_complete_parts(&claim, &input.proof).map_err(|e| {
                ShieldedError::InputProofRejected {
                    input_index: i,
                    reason: format!("{e}"),
                }
            })?;
        }
        // No two inputs may carry the same nullifier (in-transfer double-spend).
        for i in 0..self.inputs.len() {
            for j in (i + 1)..self.inputs.len() {
                if self.inputs[i].nullifier == self.inputs[j].nullifier {
                    return Err(ShieldedError::DuplicateNullifier { a: i, b: j });
                }
            }
        }

        // ── 2. the arity the value-link descriptor states
        if self.inputs.len() != DEPLOYED_INPUTS || self.outputs.len() != DEPLOYED_OUTPUTS {
            return Err(ShieldedError::UnsupportedArity {
                inputs: self.inputs.len(),
                outputs: self.outputs.len(),
            });
        }

        // ── 3. THE VALUE LINK
        for (k, output) in self.outputs.iter().enumerate() {
            let cm =
                note_commitment_felt_from_bytes(&output.note_commitment).map_err(|source| {
                    ShieldedError::OutputLinkRejected {
                        output_index: k,
                        reason: source.to_string(),
                    }
                })?;
            verify_shielded_transfer_link(
                &output.link_proof,
                &self.inputs[k].spend_wide_binding,
                cm,
            )
            .map_err(|source| ShieldedError::OutputLinkRejected {
                output_index: k,
                reason: source.to_string(),
            })?;
        }
        Ok(())
    }

    /// The set of nullifiers this transfer spends (what the chain's nullifier set must reject if
    /// any are already present — the cross-transfer double-spend gate).
    pub fn nullifiers(&self) -> Vec<BabyBear> {
        self.inputs.iter().map(|i| i.nullifier).collect()
    }

    /// The minted note commitments, in order — the leaves the executor appends AFTER
    /// [`verify`](Self::verify) accepted them.
    pub fn output_note_commitments(&self) -> Vec<[u8; 32]> {
        self.outputs.iter().map(|o| o.note_commitment).collect()
    }

    /// Reconstruct a published shielded transfer from its **serialized wire parts** — the
    /// executor's `Effect::ShieldedTransfer` payload.
    ///
    /// ⚑ There is no `merkle_root` parameter and there never can be one: the committed root enters
    /// only at [`verify`](Self::verify), from executor state.
    ///
    /// Every public field element must use its canonical BabyBear integer encoding; accepting
    /// `x + p` here would reintroduce exactly the alias the wide carrier exists to remove.
    pub fn from_serialized_parts(
        inputs: Vec<(u32, [u32; WIDE_LANES], Vec<u8>)>,
        outputs: Vec<([u8; 32], Vec<u8>)>,
    ) -> Result<Self, ShieldedError> {
        let mut ins = Vec::with_capacity(inputs.len());
        for (index, (nullifier, spend_wide_binding, bytes)) in inputs.into_iter().enumerate() {
            if nullifier >= BABYBEAR_P {
                return Err(ShieldedError::NonCanonicalPublicField {
                    input_index: index,
                    lane: 0,
                    value: nullifier,
                });
            }
            for (lane, value) in spend_wide_binding.iter().copied().enumerate() {
                if value >= BABYBEAR_P {
                    return Err(ShieldedError::NonCanonicalPublicField {
                        input_index: index,
                        lane: lane + 1,
                        value,
                    });
                }
            }
            let proof: Ir2BatchProof<DreggZkStarkConfig> =
                postcard::from_bytes(&bytes).map_err(|e| ShieldedError::ProofDecode {
                    reason: format!("{e}"),
                })?;
            ins.push(ShieldedInputProof {
                nullifier: BabyBear::new(nullifier),
                spend_wide_binding: spend_wide_binding.map(BabyBear::new),
                proof,
            });
        }
        Ok(ShieldedTransfer {
            inputs: ins,
            outputs: outputs
                .into_iter()
                .map(|(note_commitment, link_proof)| ShieldedOutput {
                    note_commitment,
                    link_proof,
                })
                .collect(),
        })
    }
}

/// Witness for building a shielded transfer: the spent note's full opening + spending key + its
/// authenticated place in the COMMITTED shielded accumulator (all hidden), plus the two things the
/// sender chooses about the minted note — its owner and its randomness.
///
/// **There is no output value field, and that absence is the fix.** The minted note's value is the
/// spent note's, read off the same limb columns by the Lean relation.
#[derive(Clone, Debug)]
pub struct ShieldedTransferWitness {
    /// The hidden complete-spend witness (note opening, key, blinding, membership path).
    pub spend: ShieldedSpendCompleteWitness,
    /// The recipient's owner felt — `hash_fact(key0,[key1,key2,key3])` of their spending key.
    pub out_owner: BabyBear,
    /// Fresh randomness for the minted note (what keeps its published commitment hiding).
    pub out_randomness: BabyBear,
}

impl ShieldedTransferWitness {
    /// The value-link witness this transfer's single output needs.
    pub fn link_witness(&self) -> ShieldedTransferLinkWitness {
        ShieldedTransferLinkWitness {
            value: self.spend.value,
            asset_type: self.spend.asset_type,
            in_randomness: self.spend.randomness,
            in_binding_blind: self.spend.binding_blind,
            out_owner: self.out_owner,
            out_randomness: self.out_randomness,
        }
    }
}

/// Prove one shielded input through the hiding IR-v2 path, yielding a [`ShieldedInputProof`].
///
/// The proof's own fold reaches whatever root the witness's membership path leads to. Nothing is
/// published about it here — verification supplies the committed root, so an honest witness (a real
/// member of the real accumulator) is admitted and a forged one is not.
pub fn prove_shielded_input(
    spend: &ShieldedSpendCompleteWitness,
) -> Result<ShieldedInputProof, ShieldedError> {
    let proof = prove_shielded_spend_complete(spend)
        .map_err(|e| ShieldedError::ProveFailed { reason: e })?;
    Ok(ShieldedInputProof {
        nullifier: proof.claim.nullifier,
        spend_wide_binding: proof.claim.wide_binding,
        proof: proof.proof,
    })
}

/// Build a complete shielded transfer at the deployed arity: one spent note in, one minted note
/// out, equal value by construction of the Lean relation.
///
/// ⚑ No `merkle_root` parameter: which tree the input must be a member of is decided by the
/// EXECUTOR at verification, not by the prover at construction. ⚑ No output value parameter: what
/// the minted note is worth is decided by the note being spent, not by the prover at all.
pub fn prove_shielded_transfer(
    witness: &ShieldedTransferWitness,
) -> Result<ShieldedTransfer, ShieldedError> {
    let input = prove_shielded_input(&witness.spend)?;
    let link_witness = witness.link_witness();
    let link = prove_shielded_transfer_link(&link_witness)
        .map_err(|e| ShieldedError::LinkProveFailed { reason: e })?;
    Ok(ShieldedTransfer {
        inputs: vec![input],
        outputs: vec![ShieldedOutput {
            note_commitment: dregg_cell::felt_to_bytes32(link.claim.out_note_commitment),
            link_proof: link.proof_bytes(),
        }],
    })
}

/// Errors from shielded-transfer construction / verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShieldedError {
    /// A shielded transfer must spend at least one input.
    NoInputs,
    /// Proving one input's hidden complete-spend proof failed.
    ProveFailed { reason: ShieldedSpendCompleteError },
    /// Proving an output's value link failed.
    LinkProveFailed { reason: ShieldedTransferLinkError },
    /// An input's hidden proof did not verify against the EXECUTOR-SUPPLIED committed root. This
    /// is the seam-#15 refusal: a forged-tree membership proof folds to `R ≠ root8()` and the
    /// 8-lane `rootPins` pin has no satisfying assignment.
    InputProofRejected { input_index: usize, reason: String },
    /// Two inputs carry the same nullifier (in-transfer double-spend).
    DuplicateNullifier { a: usize, b: usize },
    /// A serialized input proof failed to deserialize.
    ProofDecode { reason: String },
    /// A wire public field element is not the canonical BabyBear integer encoding (`lane 0` is the
    /// nullifier; lanes `1..=16` are the ring wide carrier). Accepting `x + p` would reintroduce
    /// the modulus alias the wide carrier exists to remove.
    NonCanonicalPublicField {
        input_index: usize,
        lane: usize,
        value: u32,
    },
    /// **THE VALUE-LINK REFUSAL.** An output's minted note commitment is not bound by a valid
    /// value-link proof to the carrier its input's complete-spend proof published — i.e. the note
    /// being minted does not open to the value the note being spent holds.
    OutputLinkRejected { output_index: usize, reason: String },
    /// The transfer's arity is not the one the deployed value-link descriptor states. Refused
    /// rather than admitted: there is no descriptor whose conservation covers it.
    UnsupportedArity { inputs: usize, outputs: usize },
    /// The number of output range proofs does not equal the number of output legs — retained for
    /// the M2-b multi-asset pool (`pool.rs`), which still rides the Pedersen legs.
    RangeProofCountMismatch { outputs: usize, range_proofs: usize },
}

impl core::fmt::Display for ShieldedError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::NoInputs => write!(f, "shielded transfer has no inputs"),
            Self::ProveFailed { reason } => {
                write!(f, "shielded input proving failed: {reason}")
            }
            Self::LinkProveFailed { reason } => {
                write!(f, "shielded output value-link proving failed: {reason}")
            }
            Self::InputProofRejected {
                input_index,
                reason,
            } => write!(
                f,
                "shielded input {input_index} complete-spend proof rejected under the \
                 executor-committed root: {reason}"
            ),
            Self::DuplicateNullifier { a, b } => write!(
                f,
                "shielded inputs {a} and {b} share a nullifier (double-spend)"
            ),
            Self::ProofDecode { reason } => {
                write!(f, "shielded input proof failed to deserialize: {reason}")
            }
            Self::NonCanonicalPublicField {
                input_index,
                lane,
                value,
            } => write!(
                f,
                "shielded input {input_index} public lane {lane} value {value} is not canonical \
                 BabyBear"
            ),
            Self::OutputLinkRejected {
                output_index,
                reason,
            } => write!(
                f,
                "shielded output {output_index} value link rejected — the minted note does not \
                 open to the value the spent note holds: {reason}"
            ),
            Self::UnsupportedArity { inputs, outputs } => write!(
                f,
                "shielded transfer arity {inputs}-in/{outputs}-out is not stated by the deployed \
                 value-link descriptor (which states {DEPLOYED_INPUTS}-in/{DEPLOYED_OUTPUTS}-out); \
                 refused rather than admitted"
            ),
            Self::RangeProofCountMismatch {
                outputs,
                range_proofs,
            } => write!(
                f,
                "shielded pool transfer has {outputs} outputs but {range_proofs} range \
                 proofs (every output must carry an in-range proof)"
            ),
        }
    }
}

impl std::error::Error for ShieldedError {}
