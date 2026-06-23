//! M2-b: the **multi-asset shielded pool** (ZSA-style) — circuit side.
//!
//! M2-a ([`crate::shielded::transfer`]) hides the *value* and the *owner* of a
//! single-asset transfer but leaves the **asset type** in the clear (a public
//! `u64` on each [`crate::shielded::ShieldedValueLeg`], hashed cleartext into the
//! transfer transcript). M2-b lifts the asset type *into* the hidden scalar of
//! the Pedersen commitment, so one pool can carry MANY asset types and an
//! observer learns neither how much moved, who owned it, NOR which asset it was.
//!
//! # What changes from M2-a, and what does NOT
//!
//! Nothing changes on the **STARK side**. Membership-in-the-commitment-tree and
//! nullifier-derivation are *asset-agnostic*: the shielded-spend circuit
//! ([`crate::shielded::spend_circuit`]) never mentions the value or the asset —
//! those live only in the Pedersen leg. So a [`MultiAssetPoolTransfer`] reuses
//! the *exact same* per-input hidden note-spend proofs as M2-a
//! ([`crate::shielded::ShieldedInputProof`], proved through `HidingFriPcs`), and
//! the same one-nullifier-set-across-all-assets double-spend gate
//! ([`Self::nullifiers`] + the existing nullifier-set grow-gate) — there is one
//! nullifier set for the whole pool, not one per asset.
//!
//! What changes is the **Pedersen / asset side** and the **transcript**:
//!
//! 1. **The leg becomes asset-hiding.** A [`HiddenAssetLeg`] carries ONLY the
//!    opaque 32-byte `commit_hidden_asset(value, asset_type, blinding)` =
//!    `value·V + asset_type·H_asset + blinding·R` encoding
//!    ([`dregg_cell_crypto::value_commitment::ValueCommitment::commit_hidden_asset`]).
//!    There is no public `asset_type` field to leak: the asset type is a blinded
//!    scalar on the FIXED `H_asset` generator, indistinguishable across asset
//!    types under DDH.
//!
//! 2. **Per-asset value conservation is carried by the same homomorphic sum.**
//!    The asset-hiding commitment is binding on `(value, asset_type)` jointly. A
//!    single Schnorr excess proof on `R`
//!    ([`dregg_cell_crypto::value_commitment::prove_asset_conservation`]) certifies the
//!    excess is purely `r_excess·R`, i.e. BOTH the `V`-component (Σ value) AND
//!    the `H_asset`-component (Σ asset-tag) of `Σ C_in − Σ C_out` are zero. With
//!    equal leg counts this *is* per-asset value conservation: a cross-asset
//!    swap `{asset A}→{asset B}` of equal value has a nonzero `(A−B)·H_asset`
//!    excess component and is REJECTED — cross-asset value cannot leak or be
//!    forged while the asset stays hidden.
//!
//! 3. **Split / merge (unequal leg counts) folds in the asset-equality argument.**
//!    A `1→2` split of one asset changes the asset-tag SUM (`at` vs `2·at`), so
//!    the bare excess proof rejects it. The
//!    [`dregg_cell_crypto::value_commitment::AssetEqualityProof`] (a Chaum-Pedersen
//!    equal-discrete-log proof on `H_asset` with a SHARED response across legs)
//!    upgrades the asset-tag-SUM check to a per-leg asset-EQUALITY check, so a
//!    legitimate same-asset split/merge is provable while a mixed-asset split is
//!    still rejected. This is the [`PoolBalanceMode`] dial.
//!
//! # The two-sided construction (unchanged seam; census-first weld)
//!
//! Exactly as M2-a, this is its OWN composed proof object over the existing
//! primitives + p3 `HidingFriPcs`. It is NOT woven into `effect_vm` /
//! `descriptor_ir2`; VK perturbation is free. The circuit crate carries the
//! commitments as opaque bytes (no curve dep — `circuit` is upstream of `cell`);
//! the Pedersen + asset-equality verification composes downstream at the
//! `cell` / test layer (see `circuit/tests/shielded_pool_m2b.rs`).
//!
//! # No Rust-authored AIR (standing law)
//!
//! Zero hand-written circuit constraints: the STARK side is the same
//! Lean-emitted/DSL `shielded_spend_circuit()` descriptor run through the audited
//! `DslP3Air`, hiding config swapped in. This module assembles witnesses and
//! composes proofs; it emits no AIR of its own.

use dregg_circuit::field::BabyBear;
use crate::shielded::transfer::{ShieldedError, ShieldedInputProof, prove_shielded_input};
use crate::shielded::{ShieldedTransferWitness, shielded_spend_circuit};
use dregg_circuit::dsl::dsl_p3_air::verify_dsl_zk;
use crate::shielded::spend_circuit::{PUBLIC_INPUT_COUNT, pi};

/// One asset-hiding value-commitment leg of a multi-asset pool transfer.
///
/// Carries ONLY the opaque 32-byte compressed Ristretto encoding of
/// `commit_hidden_asset(value, asset_type, blinding)` — the asset type is a
/// blinded scalar on the fixed `H_asset` generator, NOT a public field. Contrast
/// [`crate::shielded::ShieldedValueLeg`] (M2-a), which exposes `asset_type: u64`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HiddenAssetLeg {
    /// Compressed Ristretto encoding of `value·V + asset_type·H_asset + blinding·R`.
    /// Hides value AND asset type jointly.
    pub commitment_bytes: [u8; 32],
}

impl HiddenAssetLeg {
    /// Wrap a 32-byte `commit_hidden_asset` encoding as a pool leg.
    pub fn new(commitment_bytes: [u8; 32]) -> Self {
        Self { commitment_bytes }
    }
}

/// How the pool transfer's asset side is balanced — the [`AssetEqualityProof`]
/// dial.
///
/// [`dregg_cell_crypto::value_commitment::AssetEqualityProof`]: the per-leg equal-DLog
/// argument is only NEEDED when leg counts are unequal (split/merge).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolBalanceMode {
    /// Equal input/output leg counts: the bare asset-conservation excess proof
    /// alone enforces per-asset value conservation (the asset-tag SUM cancels
    /// term-by-term). No asset-equality proof is required.
    EqualCount,
    /// Unequal leg counts (a same-asset split or merge): the asset-tag SUM no
    /// longer cancels, so an [`AssetEqualityProof`] over ALL legs is REQUIRED to
    /// prove every leg shares one hidden asset type. The downstream verifier
    /// rejects an `Unequal`-mode transfer that lacks an accepting equality proof.
    Unequal,
}

/// A published **multi-asset shielded pool transfer** (the M2-b object, circuit
/// side).
///
/// What a verifier sees: the commitment-tree `merkle_root`, one hidden
/// note-spend proof per input (each revealing only its nullifier), and the
/// asset-hiding input/output legs the Pedersen+asset-equality side conserves.
/// What stays hidden: every input note's owner and spending key, the full note
/// preimage, every Merkle path (all inside `HidingFriPcs`), the amounts, AND the
/// asset types.
///
/// (Not `Clone`/`Debug`: holds `ShieldedInputProof`s whose inner `DslZkProof`
/// implements neither.)
pub struct MultiAssetPoolTransfer {
    /// The commitment-tree root all input notes are proven members of.
    pub merkle_root: BabyBear,
    /// One hidden note-spend proof per spent input (asset-agnostic, reused from
    /// M2-a).
    pub inputs: Vec<ShieldedInputProof>,
    /// Input asset-hiding legs (the spent notes' hidden-asset commitments).
    pub input_legs: Vec<HiddenAssetLeg>,
    /// Output asset-hiding legs (the minted notes' hidden-asset commitments).
    pub output_legs: Vec<HiddenAssetLeg>,
    /// One serialized Bulletproof **range proof** per output leg (same order as
    /// `output_legs`), attesting each committed value is in `[0, 2^64)`.
    ///
    /// Same inflation gate as M2-a's
    /// [`crate::shielded::ShieldedTransfer::output_range_proofs`]: the
    /// asset-conservation Schnorr proof only certifies the excess is `r_excess·R`
    /// in the GROUP, which is satisfiable with an output committed to a wrapped
    /// negative value. The range proof per output closes that hole. The asset-hiding
    /// `commit_hidden_asset = v·V + at·H_asset + r·R` uses the SAME `V`/`R`
    /// generators as the value-only commitment (Bulletproofs' Pedersen base), so a
    /// 64-bit range proof on the value component verifies against the
    /// `v·V + r·R` projection — the downstream verifier supplies the value-only
    /// commitment for the Bulletproof check while conservation runs over the full
    /// asset-hiding commitments. Bound into [`Self::pool_message`].
    pub output_range_proofs: Vec<Vec<u8>>,
    /// Whether the asset side needs the per-leg asset-equality argument.
    pub mode: PoolBalanceMode,
}

impl MultiAssetPoolTransfer {
    /// Verify the **STARK side**: every input's hidden membership+nullifier proof
    /// verifies against the shared `merkle_root`, and the nullifiers are pairwise
    /// distinct (no in-transfer double-spend, across ALL assets — one nullifier
    /// set for the whole pool).
    ///
    /// This does NOT check value/asset balance — that is the downstream
    /// composition `verify_asset_conservation` (+ `verify_asset_equality` when
    /// [`PoolBalanceMode::Unequal`]) over the legs, bound to [`Self::pool_message`].
    pub fn verify_stark_side(&self) -> Result<(), ShieldedError> {
        if self.inputs.is_empty() {
            return Err(ShieldedError::NoInputs);
        }
        let circuit = shielded_spend_circuit();
        for (i, input) in self.inputs.iter().enumerate() {
            let mut pis = vec![BabyBear::ZERO; PUBLIC_INPUT_COUNT];
            pis[pi::NULLIFIER] = input.nullifier;
            pis[pi::MERKLE_ROOT] = self.merkle_root;
            // The shielded-spend circuit now publishes a value-binding PI (C7); the
            // proof was generated with it, so it must be supplied to the verifier.
            pis[pi::VALUE_BINDING] = input.value_binding;
            verify_dsl_zk(&circuit, &input.proof, &pis).map_err(|e| {
                ShieldedError::InputProofRejected {
                    input_index: i,
                    reason: format!("{e}"),
                }
            })?;
        }
        // One nullifier set across all assets: no two inputs may share a tag.
        for i in 0..self.inputs.len() {
            for j in (i + 1)..self.inputs.len() {
                if self.inputs[i].nullifier == self.inputs[j].nullifier {
                    return Err(ShieldedError::DuplicateNullifier { a: i, b: j });
                }
            }
        }
        Ok(())
    }

    /// Whether an [`AssetEqualityProof`] is required for this transfer (i.e. the
    /// mode is [`PoolBalanceMode::Unequal`] OR the leg counts actually differ).
    /// The downstream verifier MUST reject an `Unequal`/uneven transfer that has
    /// no accepting equality proof — that is the split/merge soundness gate.
    pub fn requires_asset_equality(&self) -> bool {
        matches!(self.mode, PoolBalanceMode::Unequal)
            || self.input_legs.len() != self.output_legs.len()
    }

    /// The nullifiers this transfer spends — the chain's pool-wide double-spend
    /// tags. The nullifier-set grow-gate rejects any already present, regardless
    /// of asset (one set across the whole pool).
    pub fn nullifiers(&self) -> Vec<BabyBear> {
        self.inputs.iter().map(|i| i.nullifier).collect()
    }

    /// The transcript binding the STARK side to the Pedersen+asset side.
    ///
    /// Unlike M2-a's [`crate::shielded::ShieldedTransfer::transfer_message`], this
    /// hashes **no cleartext asset type** (that was the M2-a leak): it binds the
    /// `merkle_root`, every nullifier, and every *opaque* hidden-asset leg
    /// (commitment bytes only). The asset-conservation Schnorr proof and the
    /// asset-equality proof both take this as their `message`, so an adversary
    /// cannot splice one transfer's membership proofs onto another's value/asset
    /// commitments.
    pub fn pool_message(&self) -> Vec<u8> {
        let mut m = Vec::new();
        m.extend_from_slice(b"dregg-shielded-pool-v1");
        m.extend_from_slice(&self.merkle_root.as_u32().to_le_bytes());
        m.extend_from_slice(&(self.inputs.len() as u64).to_le_bytes());
        for input in &self.inputs {
            m.extend_from_slice(&input.nullifier.as_u32().to_le_bytes());
            // Bind each input's value-binding (C7) into the transcript, tying the
            // STARK leaf value to the hidden-asset Pedersen leg.
            m.extend_from_slice(&input.value_binding.as_u32().to_le_bytes());
        }
        m.extend_from_slice(&(self.input_legs.len() as u64).to_le_bytes());
        for leg in &self.input_legs {
            m.extend_from_slice(&leg.commitment_bytes);
        }
        m.extend_from_slice(&(self.output_legs.len() as u64).to_le_bytes());
        for leg in &self.output_legs {
            m.extend_from_slice(&leg.commitment_bytes);
        }
        // Bind the per-output range proofs into the same transcript.
        m.extend_from_slice(&(self.output_range_proofs.len() as u64).to_le_bytes());
        for rp in &self.output_range_proofs {
            m.extend_from_slice(&(rp.len() as u64).to_le_bytes());
            m.extend_from_slice(rp);
        }
        m
    }

    /// The structural inflation gate: exactly one range proof per output leg. A
    /// pool transfer missing any output's range proof is rejected here, closing
    /// the "no range proof ⇒ wrapped/negative output value ⇒ hidden inflation"
    /// hole before the downstream cryptographic check.
    pub fn check_range_proof_shape(&self) -> Result<(), ShieldedError> {
        if self.output_range_proofs.len() != self.output_legs.len() {
            return Err(ShieldedError::RangeProofCountMismatch {
                outputs: self.output_legs.len(),
                range_proofs: self.output_range_proofs.len(),
            });
        }
        Ok(())
    }

    /// Output asset-hiding commitment bytes, in order (for the downstream verifier).
    pub fn output_commitment_bytes(&self) -> Vec<[u8; 32]> {
        self.output_legs.iter().map(|l| l.commitment_bytes).collect()
    }

    /// Input asset-hiding commitment bytes, in order (for the downstream verifier).
    pub fn input_commitment_bytes(&self) -> Vec<[u8; 32]> {
        self.input_legs.iter().map(|l| l.commitment_bytes).collect()
    }
}

/// Witness for building one pool input's hidden note-spend proof: the same hidden
/// shielded-spend witness as M2-a (the membership+nullifier side is
/// asset-agnostic), paired with this input's asset-hiding leg.
#[derive(Clone, Debug)]
pub struct PoolInputWitness {
    /// The hidden shielded-spend witness (leaf, key, Merkle path). Asset-agnostic.
    pub spend: crate::shielded::ShieldedSpendWitness,
    /// This input's published asset-hiding leg.
    pub leg: HiddenAssetLeg,
}

/// Build a multi-asset pool transfer's STARK side from per-input witnesses and the
/// output legs. All inputs are pinned to `merkle_root`. `mode` records whether the
/// asset side needs the per-leg equality argument; if the leg counts are unequal it
/// is forced to [`PoolBalanceMode::Unequal`] so [`Self::requires_asset_equality`]
/// cannot be under-claimed.
///
/// The caller composes `prove_asset_conservation` (always) and, when required,
/// `prove_asset_equality` over the legs downstream to complete value+asset balance.
pub fn prove_pool_transfer(
    merkle_root: BabyBear,
    witnesses: &[PoolInputWitness],
    output_legs: Vec<HiddenAssetLeg>,
    output_range_proofs: Vec<Vec<u8>>,
    mode: PoolBalanceMode,
) -> Result<MultiAssetPoolTransfer, ShieldedError> {
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
        // Reuse the M2-a per-input prover: build the M2-a witness shape it expects
        // (its `ShieldedValueLeg.asset_type` is unused by the STARK side — the
        // spend circuit never reads value or asset — and is dropped here).
        let m2a_witness = ShieldedTransferWitness {
            spend: w.spend.clone(),
            leg: crate::shielded::ShieldedValueLeg {
                asset_type: 0,
                commitment_bytes: w.leg.commitment_bytes,
            },
        };
        inputs.push(prove_shielded_input(&m2a_witness)?);
        input_legs.push(w.leg.clone());
    }
    let mode = if input_legs.len() != output_legs.len() {
        PoolBalanceMode::Unequal
    } else {
        mode
    };
    Ok(MultiAssetPoolTransfer {
        merkle_root,
        inputs,
        input_legs,
        output_legs,
        output_range_proofs,
        mode,
    })
}
