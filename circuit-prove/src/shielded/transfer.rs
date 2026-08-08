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
//! ## The deployed arities, stated
//!
//! ONE input, and either output arity the Lean family states ([`SUPPORTED_OUTPUTS`]):
//!
//! * **1 output** — `dregg-shielded-transfer-value-link::v1` (164 cols, 17 PIs). A whole-note
//!   transfer at equal value: a change of owner.
//! * **2 outputs** — `dregg-shielded-transfer-value-link-2out::v1`
//!   (`ShieldedTransferValueLink2OutEmit.lean`, 309 cols, 18 PIs, 305 constraints). ⚑ **A SPLIT
//!   WITH CHANGE** — what a shielded note could not do before. Conservation is the limbwise carry
//!   chain `v_i = o1_i + o2_i − 65536·c_i + c_{i−1}`, every `c_i` boolean-pinned, `c_{−1}`
//!   structurally absent from the emitted gate, and `c_3` gate-pinned to zero. The Lean
//!   `link2_conservation` proves `v = o1 + o2` over **ℤ**, not modulo `p`.
//!
//! [`ShieldedTransfer::verify`] REFUSES every other arity BY NAME rather than admitting one whose
//! conservation no descriptor states. Widening the arity cannot reopen the value link — every
//! member of the family reads its values off the same limb columns its carriers absorb, and the
//! Lean files IMPORT one absorb term rather than re-typing it.
//!
//! ⚑ **Why the 2-out link is ONE proof and not two.** Conservation across two outputs is a joint
//! statement. Two independent per-output proofs would each separately claim the whole input value,
//! and their conjunction would say `o1 = v` and `o2 = v` — a double-mint. So the link proof is
//! per-TRANSFER, and `ShieldedOutput` (which carried one proof per output) is deleted.

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
use crate::shielded::transfer_link_2out::{
    ShieldedLink2OutMint, ShieldedTransferLink2OutWitness, prove_shielded_transfer_link_2out,
    verify_shielded_transfer_link_2out,
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
    pub(crate) fn claim_for(&self, committed_root: Digest8) -> ShieldedSpendCompleteClaim {
        ShieldedSpendCompleteClaim {
            nullifier: self.nullifier,
            committed_root,
            wide_binding: self.spend_wide_binding,
        }
    }

    /// **The ONE deserializer for a spent shielded input**, shared by every money-mover that spends
    /// one (`ShieldedTransfer`, `ShieldedDeshield`). It is shared rather than copied so the
    /// canonical-BabyBear refusal cannot drift between them: a second copy that forgot the
    /// `>= p` check would reintroduce the modulus alias on exactly one of the two paths, which is
    /// the shape of defect nobody finds by reading either file alone.
    pub(crate) fn many_from_serialized_parts(
        inputs: Vec<(u32, [u32; WIDE_LANES], Vec<u8>)>,
    ) -> Result<Vec<Self>, ShieldedError> {
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
        Ok(ins)
    }
}

/// A published shielded transfer (circuit side).
///
/// What a verifier sees: one hidden complete-spend proof per input (each revealing only its
/// nullifier and its wide value carrier), the minted note commitments, and ONE value-link proof
/// binding them all to the spent carrier. What stays hidden: every note's value, asset, owner and
/// spending key, every Merkle path, and every randomness. What is NOT here, by construction: any
/// root the prover chose, and any value the prover chose.
///
/// ## ⚑ FLAG DAY (change outputs) — `ShieldedOutput` is DELETED and the link proof MOVED
///
/// The retired `ShieldedOutput { note_commitment, link_proof }` carried a link proof PER OUTPUT.
/// That shape cannot express a split. Conservation across two outputs is a JOINT statement: two
/// independent per-output proofs would each separately claim the whole input value, and their
/// conjunction says `o1 = v` and `o2 = v` — a double-mint, not a split.
///
/// So there is ONE `link_proof` per transfer, and which Lean relation it is judged against is
/// decided by `outputs.len()`. A pre-cutover payload does not decode as a current one.
///
/// (Not `Clone`/`Debug`: holds `Ir2BatchProof`s.)
pub struct ShieldedTransfer {
    /// One hidden complete-spend proof per spent input.
    pub inputs: Vec<ShieldedInputProof>,
    /// The minted note commitments, `dregg_cell::felt_to_bytes32` encoded — four little-endian
    /// bytes and twenty-eight zero each. Anything else refuses (a leaf outside that subspace could
    /// be appended and never opened again). There is no value here and no commitment to a value the
    /// prover chose: each is a Poseidon2 `hash_fact(v,[a,owner,rand])`, the SAME shape the
    /// complete-spend relation opens, so every note named is SPENDABLE. That identity is what makes
    /// "value conserved" mean something — the value that arrives can leave again, through the same
    /// circuit.
    pub outputs: Vec<[u8; 32]>,
    /// The serialized Lean-emitted value-link proof for the WHOLE transfer, judged against the
    /// relation `outputs.len()` selects.
    pub link_proof: Vec<u8>,
}

/// The deployed input arity: one. See the module docs — this is a REFUSAL, not a silent
/// restriction, and widening it is a new descriptor in the Lean family.
pub const DEPLOYED_INPUTS: usize = 1;

/// **The output arities the Lean family STATES**, and therefore the only ones admitted:
///
/// * `1` — `dregg-shielded-transfer-value-link::v1` (164 cols, 17 PIs): a whole-note transfer, a
///   change of owner at equal value;
/// * `2` — `dregg-shielded-transfer-value-link-2out::v1` (309 cols, 18 PIs): a SPLIT with change,
///   conserved by the limbwise carry chain.
///
/// Every other arity refuses BY NAME ([`ShieldedError::UnsupportedArity`]) rather than being
/// admitted without a conservation statement.
pub const SUPPORTED_OUTPUTS: [usize; 2] = [1, 2];

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
            let claim = input.claim_for(committed_root);
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

        // ── 2. the arity the Lean value-link family STATES. Anything outside it refuses by name;
        //       there is no descriptor whose conservation would cover it.
        if self.inputs.len() != DEPLOYED_INPUTS || !SUPPORTED_OUTPUTS.contains(&self.outputs.len())
        {
            return Err(ShieldedError::UnsupportedArity {
                inputs: self.inputs.len(),
                outputs: self.outputs.len(),
            });
        }

        // ── 3. THE VALUE LINK — one proof, judged against the relation the arity selects.
        //
        // Every published commitment is decoded to its felt FIRST. A leaf outside
        // `felt_to_bytes32`'s four-significant-byte subspace could be appended and never opened
        // again (value in, never out), so it refuses before any proof is even consulted.
        let mut cms = Vec::with_capacity(self.outputs.len());
        for (k, note_commitment) in self.outputs.iter().enumerate() {
            cms.push(
                note_commitment_felt_from_bytes(note_commitment).map_err(|source| {
                    ShieldedError::OutputLinkRejected {
                        output_index: k,
                        reason: source.to_string(),
                    }
                })?,
            );
        }

        // ⚑ The carrier handed to the link is `self.inputs[0]`'s, read off a proof that verified in
        // step 1 — not a claim the link proof carries about itself.
        let carrier = &self.inputs[0].spend_wide_binding;
        let verdict = match cms.as_slice() {
            // A whole-note transfer: one note in, one note out, equal value.
            [cm] => verify_shielded_transfer_link(&self.link_proof, carrier, *cm),
            // ⚑ A SPLIT WITH CHANGE. One proof over BOTH mints, because conservation across two
            // outputs is a joint statement: the Lean carry chain
            // `v_i = o1_i + o2_i - 65536*c_i + c_{i-1}` with every `c_i` boolean and `c_3` pinned
            // to zero is what makes `o1 + o2 = v` an equation over the integers rather than a
            // residue, and what makes minting `2^64` from a wrapped sum unsatisfiable.
            [cm0, cm1] => {
                verify_shielded_transfer_link_2out(&self.link_proof, carrier, &[*cm0, *cm1])
            }
            // Unreachable: step 2 already refused every other arity. Kept as a REFUSAL rather than
            // an `unreachable!()` so a future widening of `SUPPORTED_OUTPUTS` that forgets to add
            // its relation here rejects instead of panicking a validator.
            _ => {
                return Err(ShieldedError::UnsupportedArity {
                    inputs: self.inputs.len(),
                    outputs: self.outputs.len(),
                });
            }
        };
        verdict.map_err(|source| ShieldedError::OutputLinkRejected {
            output_index: 0,
            reason: source.to_string(),
        })?;
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
        self.outputs.clone()
    }

    /// Reconstruct a published shielded transfer from its **serialized wire parts** — the
    /// executor's `Effect::ShieldedTransfer` payload.
    ///
    /// ⚑ There is no `merkle_root` parameter and there never can be one: the committed root enters
    /// only at [`verify`](Self::verify), from executor state.
    ///
    /// Every public field element must use its canonical BabyBear integer encoding; accepting
    /// `x + p` here would reintroduce exactly the alias the wide carrier exists to remove.
    ///
    /// ⚑ FLAG DAY: `outputs` is now a plain list of note commitments and the link proof is a
    /// SEPARATE per-transfer argument. The old `Vec<([u8; 32], Vec<u8>)>` shape carried one proof
    /// per output and could not express a split.
    pub fn from_serialized_parts(
        inputs: Vec<(u32, [u32; WIDE_LANES], Vec<u8>)>,
        outputs: Vec<[u8; 32]>,
        link_proof: Vec<u8>,
    ) -> Result<Self, ShieldedError> {
        Ok(ShieldedTransfer {
            inputs: ShieldedInputProof::many_from_serialized_parts(inputs)?,
            outputs,
            link_proof,
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
        outputs: vec![dregg_cell::felt_to_bytes32(link.claim.out_note_commitment)],
        link_proof: link.proof_bytes(),
    })
}

/// Witness for building a shielded transfer **WITH CHANGE**: the spent note's full opening (hidden,
/// as ever), plus what the sender chooses about the two minted notes — a payee, an amount for them,
/// and where the remainder goes.
///
/// **There is no second amount field, and that absence is the point.** The change is
/// `spend.value - payee_value`, computed here; the sender never states it, and the Lean carry chain
/// is what makes the arithmetic binding rather than advisory.
#[derive(Clone, Debug)]
pub struct ShieldedTransferSplitWitness {
    /// The hidden complete-spend witness (note opening, key, blinding, membership path).
    pub spend: ShieldedSpendCompleteWitness,
    /// How much of the spent note goes to the payee.
    pub payee_value: u64,
    /// The payee's owner felt — `hash_fact(key0,[key1,key2,key3])` of their spending key.
    pub payee_owner: BabyBear,
    /// Fresh randomness for the payee's note.
    pub payee_randomness: BabyBear,
    /// The change note's owner felt — normally the sender's own.
    pub change_owner: BabyBear,
    /// Fresh randomness for the change note. Distinct from the payee's, or two equal-valued mints
    /// to the same owner would publish the same commitment.
    pub change_randomness: BabyBear,
}

impl ShieldedTransferSplitWitness {
    /// The 2-out value-link witness this transfer needs, or `None` when the payee amount exceeds
    /// the note being spent.
    pub fn link_witness(&self) -> Option<ShieldedTransferLink2OutWitness> {
        ShieldedTransferLink2OutWitness::split(
            self.spend.value,
            self.spend.asset_type,
            self.spend.randomness,
            self.spend.binding_blind,
            ShieldedLink2OutMint {
                value: self.payee_value,
                owner: self.payee_owner,
                randomness: self.payee_randomness,
            },
            self.change_owner,
            self.change_randomness,
        )
    }
}

/// Build a complete shielded transfer **WITH CHANGE**: one spent note in, TWO minted notes out,
/// conserved by the Lean carry chain.
///
/// This is what a shielded note could not do before: spend part of it and keep the rest. Both
/// minted notes are ordinary `hash_fact(v,[a,owner,rand])` leaves, so both are SPENDABLE by the
/// same complete-spend relation — the change can be spent again, and split again.
///
/// ⚑ No `merkle_root` parameter, for the same reason as [`prove_shielded_transfer`]. ⚑ The change
/// amount is DERIVED, never supplied.
pub fn prove_shielded_transfer_split(
    witness: &ShieldedTransferSplitWitness,
) -> Result<ShieldedTransfer, ShieldedError> {
    let link_witness = witness
        .link_witness()
        .ok_or(ShieldedError::SplitExceedsInput {
            value: witness.spend.value,
            payee_value: witness.payee_value,
        })?;
    let input = prove_shielded_input(&witness.spend)?;
    let link = prove_shielded_transfer_link_2out(&link_witness)
        .map_err(|e| ShieldedError::LinkProveFailed { reason: e })?;
    Ok(ShieldedTransfer {
        inputs: vec![input],
        outputs: link
            .claim
            .out_note_commitments
            .iter()
            .map(|cm| dregg_cell::felt_to_bytes32(*cm))
            .collect(),
        link_proof: link.proof_bytes(),
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
    /// A split was asked to pay out more than the note being spent holds. Refused at CONSTRUCTION:
    /// the resulting witness has no satisfying trace anyway (the Lean carry chain would need a
    /// nonzero terminal carry), so failing here names the mistake instead of surfacing it as an
    /// opaque proving error.
    SplitExceedsInput { value: u64, payee_value: u64 },
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
                 value-link descriptor family (which states {DEPLOYED_INPUTS}-in with \
                 {SUPPORTED_OUTPUTS:?} outputs); refused rather than admitted"
            ),
            Self::SplitExceedsInput { value, payee_value } => write!(
                f,
                "shielded split pays {payee_value} out of a note worth {value}: there is no change \
                 amount that conserves, and no satisfying trace of the 2-out value link"
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
