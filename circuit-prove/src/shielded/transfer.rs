//! The shielded transfer STARK side: **complete FSI2 spend** per input (membership in the
//! executor's COMMITTED shielded accumulator + nullifier derivation + the full-`u64` wide value
//! carrier), welded to the published Pedersen value-commitment transcript.
//!
//! **SAY THE SUBSTRATE OUT LOUD: the AIR is AUTHORED IN LEAN.** Every constraint this module's
//! proofs are checked against is emitted by
//! `metatheory/Dregg2/Circuit/Emit/ShieldedSpendCompleteEmit.lean`
//! (`dregg-shielded-spend-complete-fsi2::v1`, 557 columns, 25 PIs) and read byte-pinned out of the
//! Lean source by [`crate::shielded::spend_complete`]. This module authors NO constraint: it
//! assembles witnesses, calls the Lean-emitted relation's prover/verifier, and composes the
//! Pedersen half around it.
//!
//! ## ⚑ FLAG DAY — the wire no longer carries a Merkle root (seam #15)
//!
//! The retired object carried `merkle_root: BabyBear` **on the wire** and verified every input
//! against it. That is the theft `ShieldedMerkleRootPin.root_substitution_forges` states: an
//! attacker builds their OWN tree holding a note that was never committed, honestly proves
//! membership at THAT tree's root `R`, and publishes `R`. Membership holds; nothing compares `R`
//! to anything.
//!
//! There is no root field any more, and there is no constructor that takes one. The committed root
//! is an **argument to verification**, supplied by the executor from
//! `TurnExecutor::note_shielded.root8()` — live ledger state, never the payload
//! ([`ShieldedTransfer::verify_stark_side`]). A forged-tree proof folds to `R ≠ root8()`, so the
//! Lean-emitted 8-lane `rootPins` `.piBinding` has no satisfying assignment and the transfer
//! REFUSES. `ShieldedMerkleRootPin.pin_rejects_root_substitution` is the statement; the executor
//! KAT `executor_theft_forged_tree_refuses_on_the_deployed_path` is the deployed-path exhibit.
//!
//! ## The two halves, and the join that welds them
//!
//! 1. **Owner / membership / no-double-spend / value carrier — the hidden STARK side.** One
//!    [`ShieldedSpendCompleteProof`] per input. Value, asset, owner, spending key, randomness,
//!    blinding and the whole membership path stay witness-only; the proof publishes only
//!    `(nullifier, committedRoot[8], wide[16])`.
//! 2. **Value balance — the hidden Pedersen side.** Per-note `commit(v,r) = v·V + r·R`, a Schnorr
//!    conservation proof for `Σ C_in = Σ C_out`, and a Bulletproof range proof per output.
//!
//! **The join (`verify_same_opening`) is now non-vacuous, and that is the second thing this flag
//! day fixes.** The retired spend circuit published only a one-felt `value_binding`, so there was
//! no ring-side full-`u64` opening to join a sidecar against — the deployed path passed the ring
//! bindings EMPTY and FAILED CLOSED (no shielded transfer succeeded at all). The complete spend
//! PI-pins its own sixteen `cap_node8` carrier lanes (`carrierPins`), column-for-column the
//! `wide_value_binding.rs` sidecar's, so the join compares **two independently proven openings**:
//! the spend's and the sidecar's. That is precisely what `ShieldedWideJoinPin.join_still_decouples`
//! refuses to let a caller fake by sourcing the ring binding from the sidecar's own claim.

use dregg_circuit::descriptor_ir2::Ir2BatchProof;
use dregg_circuit::exact_nullifier_aafi::Digest8;
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::stark_zk::DreggZkStarkConfig;

use crate::shielded::spend_complete::{
    ShieldedSpendCompleteClaim, ShieldedSpendCompleteError, ShieldedSpendCompleteWitness,
    WIDE_LANES, prove_shielded_spend_complete, verify_shielded_spend_complete_parts,
};

/// One value-commitment leg of a shielded transfer: the asset type (still public in the
/// single-asset M2-a toehold) and the opaque 32-byte compressed Pedersen value commitment
/// (`v·V + r·R`, hiding `v`). The Pedersen conservation proof (downstream, over these bytes)
/// certifies `Σ in = Σ out` without revealing any `v`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShieldedValueLeg {
    /// Asset type (public in M2-a; hidden into a scalar in M2-b's ZSA pool).
    pub asset_type: u64,
    /// Compressed Ristretto encoding of the Pedersen value commitment.
    pub commitment_bytes: [u8; 32],
}

/// One spent input's **hidden complete-spend proof**.
///
/// The proof is the Lean-emitted `dregg-shielded-spend-complete-fsi2::v1` relation run through the
/// hiding IR-v2 backend, so its openings reveal nothing about the witness (value, asset, owner,
/// spending key, randomness, blinding, the whole membership path) beyond the published claim.
///
/// Two of the claim's three parts ride here. **The third — the committed root — deliberately does
/// not**: it is supplied at verification time from executor state, so a payload has no field in
/// which to publish a root of its own choosing. That absence IS the #15 fix; see the module docs.
pub struct ShieldedInputProof {
    /// The revealed nullifier (the chain's double-spend tag for this input), PI 0. The Lean
    /// `nulPin` forces it to equal the in-trace `hash_fact(cCM,[key0..3])`, so a spend cannot
    /// publish a nullifier for a note it did not open.
    pub nullifier: BabyBear,
    /// **The ring-side full-`u64` wide value/asset carrier**, PI 9..25 — the sixteen
    /// domain-separated `cap_node8` lanes the Lean `carrierPins` pin to the note's canonical limb
    /// opening. This is the ring binding the sidecar's `verify_same_opening` joins against; it is
    /// bound by THIS proof, independently of the sidecar, which is what makes the join real.
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

/// A published shielded transfer (the M2-a object, circuit side).
///
/// What a verifier sees: one hidden complete-spend proof per input (each revealing only its
/// nullifier and its wide value carrier), and the input/output value-commitment legs the Pedersen
/// side conserves. What stays hidden: every input note's value, asset, owner and spending key, and
/// every Merkle path. What is NOT here, by construction: any root the prover chose.
///
/// (Not `Clone`/`Debug`: holds `Ir2BatchProof`s.)
pub struct ShieldedTransfer {
    /// One hidden complete-spend proof per spent input.
    pub inputs: Vec<ShieldedInputProof>,
    /// Input value-commitment legs (the spent notes' Pedersen commitments).
    pub input_legs: Vec<ShieldedValueLeg>,
    /// Output value-commitment legs (the minted notes' Pedersen commitments).
    pub output_legs: Vec<ShieldedValueLeg>,
    /// One serialized Bulletproof **range proof** per output leg (same order as `output_legs`),
    /// each attesting the committed value is in `[0, 2^64)`.
    ///
    /// This is the toothed inflation gate: the Pedersen conservation proof alone only certifies
    /// `Σ C_in − Σ C_out = r_excess·R` in the GROUP, which is satisfiable with an output committed
    /// to a value OUTSIDE `[0, 2^64)` (a scalar-field-wrapped "negative" amount). Carried in
    /// [`transfer_message`](Self::transfer_message) so the STARK side, the conservation proof and
    /// the range proofs are all Fiat-Shamir-bound together and cannot be spliced across transfers.
    pub output_range_proofs: Vec<Vec<u8>>,
}

impl ShieldedTransfer {
    /// Verify the **STARK side** against the executor's COMMITTED accumulator root: every input's
    /// hidden complete-spend proof verifies with `committed_root` as its 8-lane `piCommitted`, and
    /// the nullifiers are pairwise distinct (no in-transfer double-spend).
    ///
    /// ⚑ `committed_root` MUST come from live executor state
    /// (`TurnExecutor::note_shielded.root8().limbs()`), never from the payload — there is no
    /// payload field it could come from. A proof folded in the attacker's own tree reaches
    /// `R ≠ committed_root`, and the Lean-emitted 8-lane `rootPins` `.piBinding` then has no
    /// satisfying assignment: the spend REFUSES. That refusal is the whole of seam #15.
    ///
    /// This does NOT check value balance — that is the Pedersen conservation proof over
    /// `input_legs`/`output_legs`, welded through [`transfer_message`](Self::transfer_message).
    pub fn verify_stark_side(&self, committed_root: Digest8) -> Result<(), ShieldedError> {
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
        Ok(())
    }

    /// The set of nullifiers this transfer spends (what the chain's nullifier set must reject if
    /// any are already present — the cross-transfer double-spend gate).
    pub fn nullifiers(&self) -> Vec<BabyBear> {
        self.inputs.iter().map(|i| i.nullifier).collect()
    }

    /// The ring-side wide carriers, in input order — the openings the sidecars must join.
    pub fn ring_wide_bindings(&self) -> Vec<[BabyBear; WIDE_LANES]> {
        self.inputs.iter().map(|i| i.spend_wide_binding).collect()
    }

    /// The transcript that binds the STARK side to the Pedersen side: the **executor-supplied
    /// committed root**, every nullifier, every ring wide carrier, and every value-commitment leg,
    /// in order. Both halves' proofs are Fiat-Shamir-bound to this message, so an adversary cannot
    /// splice the membership proofs of one transfer onto the value commitments of another — nor
    /// replay a conservation proof built against a different accumulator state.
    pub fn transfer_message(&self, committed_root: Digest8) -> Vec<u8> {
        let mut m = Vec::new();
        m.extend_from_slice(b"dregg-shielded-transfer-v2-committed-root");
        for lane in committed_root {
            m.extend_from_slice(&lane.as_u32().to_le_bytes());
        }
        m.extend_from_slice(&(self.inputs.len() as u64).to_le_bytes());
        for input in &self.inputs {
            m.extend_from_slice(&input.nullifier.as_u32().to_le_bytes());
            // The ring carrier is proof-bound (PI-pinned by the complete spend), so absorbing it
            // makes the conservation transcript depend on the full-`u64` value opening the spend
            // proved — not merely on a reduced felt.
            for lane in input.spend_wide_binding {
                m.extend_from_slice(&lane.as_u32().to_le_bytes());
            }
        }
        m.extend_from_slice(&(self.input_legs.len() as u64).to_le_bytes());
        for leg in &self.input_legs {
            m.extend_from_slice(&leg.asset_type.to_le_bytes());
            m.extend_from_slice(&leg.commitment_bytes);
        }
        m.extend_from_slice(&(self.output_legs.len() as u64).to_le_bytes());
        for leg in &self.output_legs {
            m.extend_from_slice(&leg.asset_type.to_le_bytes());
            m.extend_from_slice(&leg.commitment_bytes);
        }
        // Bind the range proofs into the same transcript so they cannot be spliced from another
        // transfer onto these output commitments.
        m.extend_from_slice(&(self.output_range_proofs.len() as u64).to_le_bytes());
        for rp in &self.output_range_proofs {
            m.extend_from_slice(&(rp.len() as u64).to_le_bytes());
            m.extend_from_slice(rp);
        }
        m
    }

    /// The structural inflation gate that must hold BEFORE the downstream Pedersen
    /// `verify_full_conservation_bytes` is even consulted: exactly one range proof per output leg.
    /// A transfer that drops (or pads) range proofs so some output escapes the `[0, 2^64)` bound is
    /// rejected here.
    pub fn check_range_proof_shape(&self) -> Result<(), ShieldedError> {
        if self.output_range_proofs.len() != self.output_legs.len() {
            return Err(ShieldedError::RangeProofCountMismatch {
                outputs: self.output_legs.len(),
                range_proofs: self.output_range_proofs.len(),
            });
        }
        Ok(())
    }

    /// The output value commitments, in order, for the downstream range/conservation verifier.
    pub fn output_commitment_bytes(&self) -> Vec<[u8; 32]> {
        self.output_legs
            .iter()
            .map(|l| l.commitment_bytes)
            .collect()
    }

    /// The input value commitments, in order, for the downstream conservation verifier.
    pub fn input_commitment_bytes(&self) -> Vec<[u8; 32]> {
        self.input_legs.iter().map(|l| l.commitment_bytes).collect()
    }

    /// Reconstruct a published shielded transfer from its **serialized wire parts** — the
    /// executor's `Effect::ShieldedTransfer` payload.
    ///
    /// ⚑ There is no `merkle_root` parameter and there never can be one: the committed root enters
    /// only at [`verify_stark_side`](Self::verify_stark_side), from executor state.
    ///
    /// Every public field element must use its canonical BabyBear integer encoding; accepting
    /// `x + p` here would reintroduce exactly the alias the wide carrier exists to remove.
    pub fn from_serialized_parts(
        inputs: Vec<(u32, [u32; WIDE_LANES], Vec<u8>)>,
        input_legs: Vec<ShieldedValueLeg>,
        output_legs: Vec<ShieldedValueLeg>,
        output_range_proofs: Vec<Vec<u8>>,
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
            input_legs,
            output_legs,
            output_range_proofs,
        })
    }
}

/// Witness for building one input's hidden complete-spend proof: the full note opening + spending
/// key + the note's authenticated place in the COMMITTED shielded accumulator (all hidden), plus
/// the published value commitment leg for it.
#[derive(Clone, Debug)]
pub struct ShieldedTransferWitness {
    /// The hidden complete-spend witness (note opening, key, blinding, membership path).
    pub spend: ShieldedSpendCompleteWitness,
    /// This input's published value-commitment leg.
    pub leg: ShieldedValueLeg,
}

/// Prove one shielded input through the hiding IR-v2 path, yielding a [`ShieldedInputProof`].
///
/// The proof's own fold reaches whatever root the witness's membership path leads to. Nothing is
/// published about it here — verification supplies the committed root, so an honest witness (a real
/// member of the real accumulator) is admitted and a forged one is not.
pub fn prove_shielded_input(
    witness: &ShieldedTransferWitness,
) -> Result<ShieldedInputProof, ShieldedError> {
    let proof = prove_shielded_spend_complete(&witness.spend)
        .map_err(|e| ShieldedError::ProveFailed { reason: e })?;
    Ok(ShieldedInputProof {
        nullifier: proof.claim.nullifier,
        spend_wide_binding: proof.claim.wide_binding,
        proof: proof.proof,
    })
}

/// Build a complete shielded transfer's STARK side from per-input witnesses and the output legs.
/// The caller composes the Pedersen conservation proof over `input_legs`/`output_legs` (downstream)
/// to complete value balance.
///
/// ⚑ No `merkle_root` parameter: which tree the inputs must be members of is decided by the
/// EXECUTOR at verification, not by the prover at construction.
pub fn prove_shielded_transfer(
    witnesses: &[ShieldedTransferWitness],
    output_legs: Vec<ShieldedValueLeg>,
    output_range_proofs: Vec<Vec<u8>>,
) -> Result<ShieldedTransfer, ShieldedError> {
    if witnesses.is_empty() {
        return Err(ShieldedError::NoInputs);
    }
    if output_range_proofs.len() != output_legs.len() {
        return Err(ShieldedError::RangeProofCountMismatch {
            outputs: output_legs.len(),
            range_proofs: output_range_proofs.len(),
        });
    }
    let mut inputs = Vec::with_capacity(witnesses.len());
    let mut input_legs = Vec::with_capacity(witnesses.len());
    for w in witnesses {
        inputs.push(prove_shielded_input(w)?);
        input_legs.push(w.leg.clone());
    }
    Ok(ShieldedTransfer {
        inputs,
        input_legs,
        output_legs,
        output_range_proofs,
    })
}

/// Errors from shielded-transfer construction / verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShieldedError {
    /// A shielded transfer must spend at least one input.
    NoInputs,
    /// Proving one input's hidden complete-spend proof failed.
    ProveFailed { reason: ShieldedSpendCompleteError },
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
    /// The number of output range proofs does not equal the number of output legs — some output
    /// would escape the `[0, 2^64)` bound (the negative-value inflation hole).
    RangeProofCountMismatch { outputs: usize, range_proofs: usize },
}

impl core::fmt::Display for ShieldedError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::NoInputs => write!(f, "shielded transfer has no inputs"),
            Self::ProveFailed { reason } => {
                write!(f, "shielded input proving failed: {reason}")
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
            Self::RangeProofCountMismatch {
                outputs,
                range_proofs,
            } => write!(
                f,
                "shielded transfer has {outputs} outputs but {range_proofs} range \
                 proofs (every output must carry an in-range proof)"
            ),
        }
    }
}

impl std::error::Error for ShieldedError {}
