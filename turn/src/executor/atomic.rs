//! Multi-party atomic proofs: sovereign-only and mixed sovereign/hosted turns.

use dregg_cell::{CellId, Ledger};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use crate::action::Effect;
use crate::journal::LedgerJournal;
use crate::turn::{Finality, TurnReceipt};

use super::TurnExecutor;

// =============================================================================
// Multi-Party Atomic Proofs
// =============================================================================

/// A single sovereign cell's proof entry in an atomic multi-party turn.
///
/// Each entry binds a cell to its STARK proof and commitment transition.
/// The `balance_delta` field is a PRE-FLIGHT HINT only: the authoritative delta
/// is EXTRACTED from the proof's public inputs by the verifier. This prevents
/// a submitter from lying about their balance change.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AtomicProofEntry {
    /// The sovereign cell ID.
    pub cell_id: CellId,
    /// The serialized STARK proof bytes.
    pub proof: Vec<u8>,
    /// The old state commitment (must match what the federation stores).
    pub old_commitment: [u8; 32],
    /// The new state commitment (will be stored after verification).
    pub new_commitment: [u8; 32],
    /// The BLAKE3 hash of effects this cell is applying.
    pub effects_hash: [u8; 32],
    /// Pre-flight hint of net balance change (positive = receives, negative = sends).
    /// NOT trusted by the executor: the real delta is extracted from PI[32..34] of the proof.
    /// This field exists for client-side pre-validation and routing hints only.
    pub balance_delta: i64,
}

/// Wire encoding of `AtomicProofEntry::proof`.
///
/// The old hand-STARK proof embedded its own public inputs; the p3 descriptor
/// prover's `Ir2BatchProof` does NOT — the PI vector must be supplied to
/// `verify_vm_descriptor2`. So the on-wire `proof` bytes are a `postcard`
/// encoding of this struct: the u32 public-input vector alongside the IR-v2
/// batch proof. The verifier reads `public_inputs` to reconstruct the PI vector
/// (forwarding non-commitment slots, overriding OLD/NEW_COMMIT with
/// verifier-derived Poseidon2 commitments) and then descriptor-verifies `proof`
/// against that reconstruction.
#[derive(serde::Serialize, serde::Deserialize)]
struct AtomicProofWire {
    public_inputs: Vec<u32>,
    proof: dregg_circuit::descriptor_ir2::Ir2BatchProof<
        dregg_circuit::descriptor_ir2::DreggStarkConfig,
    >,
}

/// A mixed atomic turn containing both sovereign (proof-carrying) and hosted
/// (federation-executed) cells in a single atomic operation.
///
/// Conservation is enforced across BOTH domains: sovereign deltas (extracted from
/// proofs) plus hosted deltas (computed from execution) must sum to zero.
///
/// SECURITY (C1 fix): the hosted side is now expressed as a `Vec<Action>` so
/// each hosted-side operation carries its own `Authorization` (Ed25519 sig,
/// proof, bearer cap, etc.). Each action's authorization is verified via the
/// standard `verify_authorization` pipeline before its effects are applied.
/// Previously `hosted_effects: Vec<(CellId, Vec<Effect>)>` had no
/// per-cell auth, which allowed any caller of `execute_mixed_atomic` to
/// mutate any hosted cell's balance.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MixedAtomicTurn {
    /// The agent submitting this turn (pays fee, provides nonce).
    pub agent: CellId,
    /// Nonce for replay protection.
    pub nonce: u64,
    /// Fee in computrons.
    pub fee: u64,
    /// Proof-carrying sovereign cell entries.
    pub sovereign_entries: Vec<AtomicProofEntry>,
    /// Hosted-side actions. Each `Action` carries its own authorization, which
    /// is verified before any of its effects apply.
    pub hosted_actions: Vec<crate::action::Action>,
}

/// Result of a successful mixed atomic turn execution.
#[derive(Clone, Debug)]
pub struct MixedAtomicResult {
    /// New commitments for sovereign cells (in order of sovereign_entries).
    pub sovereign_commitments: Vec<[u8; 32]>,
    /// Proven balance deltas for sovereign cells (extracted from proofs).
    pub sovereign_deltas: Vec<i64>,
    /// Computed balance deltas for hosted cells.
    pub hosted_deltas: Vec<i64>,
    /// Receipts emitted for every cell touched by this atomic turn (sovereign
    /// entries first in declared order, then hosted actions in declared
    /// order). Each receipt chains to that cell's previous head via
    /// `previous_receipt_hash` and has been fed into
    /// `TurnExecutor::record_receipt_hash` for chain extension, closing the
    /// `execute_turn(S,T) = (S', R)` law on the atomic path.
    /// See `AIR-SOUNDNESS-AUDIT.md` issue #69.
    pub receipts: Vec<TurnReceipt>,
}

/// An atomic multi-party sovereign turn: multiple sovereign cells each provide
/// a STARK proof of their individual state transition. The executor verifies ALL
/// proofs atomically and checks cross-cell conservation (the sum of all balance
/// deltas must be zero).
///
/// This enables multi-party transactions (e.g., Alice sends to Bob) where each
/// party proves their own transition independently, and the federation verifies
/// that the overall conservation law holds.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AtomicSovereignTurn {
    /// The agent submitting this atomic turn (pays fee, provides nonce).
    pub agent: CellId,
    /// Nonce for replay protection (from the agent cell).
    pub nonce: u64,
    /// Fee in computrons (deducted from agent's balance).
    pub fee: u64,
    /// The proof entries: one per sovereign cell involved.
    pub proofs: Vec<AtomicProofEntry>,
}

/// Errors specific to atomic sovereign turn verification.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AtomicTurnError {
    /// No proof entries provided.
    EmptyProofs,
    /// A cell is not registered as sovereign.
    NotSovereign(CellId),
    /// The stored commitment does not match the entry's old_commitment.
    CommitmentMismatch {
        cell: CellId,
        expected: [u8; 32],
        got: [u8; 32],
    },
    /// A STARK proof failed verification.
    ProofFailed { cell: CellId, reason: String },
    /// Cross-cell conservation violated: balance deltas do not sum to zero.
    ConservationViolation { net_excess: i64 },
    /// Per-asset cross-cell conservation violated: one asset class's signed
    /// deltas (per-cell proven deltas + declared mint/burn rows) do not sum to
    /// zero. This is the asset-KEYED replacement for the scalar
    /// `ConservationViolation` — a turn that nets to zero ACROSS assets but is
    /// unbalanced WITHIN an asset (the cross-asset forging attack: asset 7 −10,
    /// asset 8 +10) is REJECTED here even though the scalar sum was zero.
    /// `asset` is the asset / issuer-cell class (the cell's `token_id` folded to
    /// a field element); `imbalance` is its signed `Σδ ≠ 0`.
    PerAssetConservationViolation { asset: u32, imbalance: i64 },
    /// Agent cell not found (for fee/nonce).
    AgentNotFound(CellId),
    /// Insufficient balance for fee.
    /// `available` is SIGNED (THE EPOCH §5).
    InsufficientFee { available: i64, required: u64 },
    /// Nonce mismatch.
    NonceMismatch { expected: u64, got: u64 },
    /// Duplicate cell in proof entries.
    DuplicateCell(CellId),
    /// A cell referenced by the atomic turn is frozen for migration (P0-4).
    FrozenCell(CellId),
    /// An action in the hosted side failed authorization (C1 fix).
    HostedAuthorizationFailed { cell: CellId, reason: String },
    /// An action in the hosted side failed preconditions or effect application.
    HostedApplyFailed { cell: CellId, reason: String },
    /// The agent's nonce overflowed u64::MAX (P2-2 guard).
    NonceOverflow(CellId),
}

impl core::fmt::Display for AtomicTurnError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::EmptyProofs => write!(f, "atomic turn has no proof entries"),
            Self::NotSovereign(id) => write!(f, "cell {} is not sovereign", id),
            Self::CommitmentMismatch {
                cell,
                expected,
                got,
            } => write!(
                f,
                "commitment mismatch for cell {}: expected {:02x}{:02x}..., got {:02x}{:02x}...",
                cell, expected[0], expected[1], got[0], got[1]
            ),
            Self::ProofFailed { cell, reason } => {
                write!(f, "proof failed for cell {}: {}", cell, reason)
            }
            Self::ConservationViolation { net_excess } => {
                write!(
                    f,
                    "cross-cell conservation violated: net excess = {}",
                    net_excess
                )
            }
            Self::PerAssetConservationViolation { asset, imbalance } => {
                write!(
                    f,
                    "per-asset cross-cell conservation violated: asset {} nets to {} (≠ 0) — \
                     a hidden mint/burn across cells of one asset, or cross-asset borrowing",
                    asset, imbalance
                )
            }
            Self::AgentNotFound(id) => write!(f, "agent cell not found: {}", id),
            Self::InsufficientFee {
                available,
                required,
            } => {
                write!(
                    f,
                    "insufficient fee: available {}, required {}",
                    available, required
                )
            }
            Self::NonceMismatch { expected, got } => {
                write!(f, "nonce mismatch: expected {}, got {}", expected, got)
            }
            Self::DuplicateCell(id) => write!(f, "duplicate cell in proof entries: {}", id),
            Self::FrozenCell(id) => {
                write!(f, "cell {} is frozen for migration", id)
            }
            Self::HostedAuthorizationFailed { cell, reason } => {
                write!(
                    f,
                    "hosted action on cell {} failed authorization: {}",
                    cell, reason
                )
            }
            Self::HostedApplyFailed { cell, reason } => {
                write!(
                    f,
                    "hosted action on cell {} failed to apply: {}",
                    cell, reason
                )
            }
            Self::NonceOverflow(id) => {
                write!(
                    f,
                    "nonce overflow on agent cell {}: u64::MAX exceeded; \
                     turn rejected to prevent P2-2 replay window",
                    id
                )
            }
        }
    }
}

impl std::error::Error for AtomicTurnError {}

impl TurnExecutor {
    // -----------------------------------------------------------------------
    // Per-asset cross-cell conservation (closes the LIVE conservation hole)
    // -----------------------------------------------------------------------
    //
    // The old check `proven_deltas.iter().sum::<i64>() == 0` was ASSET-BLIND:
    // a 2-entry turn (cell of asset 7: −10; cell of asset 8: +10) nets to 0 and
    // was ACCEPTED, destroying asset 7 and minting asset 8 out of nothing. The
    // scalar sum is replaced by the per-asset, in-AIR-backed collector
    // `dregg_circuit::block_conservation::BlockConservation`: each entry's
    // proven NET_DELTA is grouped by its asset class and EACH asset is required
    // to conserve INDEPENDENTLY (cross-asset borrowing is impossible — the
    // committed `cross_cell_conservation_air`'s per-asset `balance[last]==0`
    // boundary). Declared mint/burn rows enter the conserved sum explicitly, so
    // a DISCLOSED non-conservation balances but a HIDDEN one is caught.
    //
    // ASSET-ID DERIVATION (the named residual, NARROWED — see
    // `resolve_proof_asset_class`). AssetId := the cell's `token_id` (the
    // dregg3 "AssetId := issuer-cell" materialization, a real committed ledger
    // field) folded to a field element by the ONE canonical fold
    // (`fold_token_id_to_asset`). The original residual — "the per-cell proof
    // does not publish its asset class as a public input at all" — is closed:
    // the proof publishes it at `PI[v3::ASSET_CLASS]`, AIR-bound to the row-0
    // `aux_off::ASSET_CLASS` column (`effect_vm/air.rs`), and the live paths
    // group by the PROOF-BOUND class via
    // `check_per_asset_conservation_by_asset`, rejecting a PI/ledger mismatch.
    // WHAT REMAINS (the narrowed residual): a proof carrying the ZERO sentinel
    // (a prover leg that has not yet threaded `EffectVmContext::asset_class`)
    // falls back to the executor's trusted ledger class — sound for the
    // executor, but the pure light-client partition stays trivial for those
    // legs until every prover leg populates the class.

    /// Derive the asset / issuer-cell class for a cell from its committed
    /// `token_id` (dregg3: AssetId := issuer-cell). Folds the 32-byte token_id
    /// to a single field element (the `BabyBear` the cross-cell collector
    /// partitions on). A cell absent from the ledger (or with the zero token_id,
    /// the native computron asset) derives a stable class.
    fn asset_class_for_cell(ledger: &Ledger, cell: &CellId) -> dregg_circuit::field::BabyBear {
        let token_id: [u8; 32] = ledger.get(cell).map(|c| *c.token_id()).unwrap_or([0u8; 32]);
        Self::fold_token_id_to_asset(&token_id)
    }

    /// Fold a 32-byte `token_id` to a single asset-class field element.
    /// Delegates to `dregg_circuit::block_conservation::fold_token_id_to_asset`
    /// — the ONE canonical fold the prover (`PI[v3::ASSET_CLASS]`), the executor
    /// reconciliation, and the light-client/bundle partition all share, so the
    /// proof-bound class and the ledger-derived class agree by construction.
    fn fold_token_id_to_asset(token_id: &[u8; 32]) -> dregg_circuit::field::BabyBear {
        dregg_circuit::block_conservation::fold_token_id_to_asset(token_id)
    }

    /// THE PER-ASSET CONSERVATION GATE. Given each verified entry's
    /// `(cell_id, proven_net_delta)` (the proven signed delta read from its
    /// per-cell proof PI), group by asset class (from the ledger's committed
    /// `token_id`) and require EACH asset to conserve to zero through the
    /// in-AIR-backed `BlockConservation` collector. `declared_supply` carries
    /// any disclosed mint/burn rows (DECLARED non-conservation) which enter the
    /// conserved sum explicitly. Returns the first imbalanced asset on failure.
    ///
    /// This replaces the asset-BLIND scalar sum. The check is the same
    /// arithmetic the committed per-asset `Σδ=0` AIR forces (its
    /// `balance[last]==0` boundary); under the `prover` feature the full
    /// per-asset AIR is additionally proven+verified so the gate is genuinely
    /// in-circuit, not a re-implemented off-AIR scalar.
    ///
    /// Retained for the ledger-keyed in-AIR collector test; the live executor
    /// paths now group by the PROOF-BOUND class via
    /// [`Self::check_per_asset_conservation_by_asset`].
    #[allow(dead_code)]
    fn check_per_asset_conservation(
        ledger: &Ledger,
        entries: &[(CellId, i64)],
        declared_supply: &[dregg_circuit::block_conservation::DeclaredSupplyChange],
    ) -> Result<(), AtomicTurnError> {
        use dregg_circuit::block_conservation::{BlockConservation, PerCellContribution};
        use dregg_circuit::field::BabyBear;

        let mut block = BlockConservation::new();
        for (cell_id, delta) in entries {
            let asset = Self::asset_class_for_cell(ledger, cell_id);
            // Re-express the proven signed i64 delta as the collector's signed
            // (mag, sign) contribution — the exact shape the per-cell proof's
            // (NET_DELTA_MAG, NET_DELTA_SIGN) PI carries (sign 0 = credit/+,
            // 1 = debit/−).
            let sign_credit = *delta >= 0;
            block.add_contribution(PerCellContribution {
                asset,
                net_delta_mag: BabyBear::new_canonical(delta.unsigned_abs() as u32),
                net_delta_sign: if sign_credit {
                    BabyBear::ZERO
                } else {
                    BabyBear::ONE
                },
            });
        }
        for s in declared_supply {
            block.add_supply_change(*s);
        }

        // The per-asset signed-sum gate: EXACTLY the arithmetic the committed
        // per-asset `cross_cell_conservation_air` forces (its `balance[last]==0`
        // boundary, computed by `cross_cell_balance` over each asset's grouped
        // signed deltas). Fail-closed on the first imbalanced asset. The full
        // per-asset STARK (`BlockConservation::prove_and_verify`) is the
        // light-client-side realization of this same boundary — the executor
        // already trusts the per-cell proofs + the ledger token_ids, so it runs
        // the boundary arithmetic directly (re-proving every turn on the hot path
        // would be redundant); the light client runs `verify_with_proofs` over
        // the carried per-asset proofs. The new test exercises the full
        // prove+verify to witness the in-AIR property end-to-end.
        if let Err(dregg_circuit::block_conservation::BlockConservationError::AssetImbalanced {
            asset,
            imbalance,
        }) = block.check()
        {
            return Err(AtomicTurnError::PerAssetConservationViolation {
                asset: asset.0,
                imbalance,
            });
        }

        Ok(())
    }

    /// Resolve the per-cell ASSET CLASS for the per-asset conservation gate on
    /// the EXECUTOR path (which holds the ledger).
    ///
    /// The proof publishes its asset class at `PI[v3::ASSET_CLASS]`, pinned by
    /// the AIR's row-0 boundary constraint to the trace's committed class — this
    /// is the LIGHT-CLIENT-sound partition key (the ledgerless bundle path
    /// groups by it directly in `check_bundle_per_asset_conservation`). The
    /// executor reconciles it against the cell's committed `token_id`:
    ///   * if the proof carries a NON-zero (populated) class, it MUST equal the
    ///     ledger token_id's fold — a mismatch is a mislabeled asset and is
    ///     REJECTED (the verifier-reconstruction posture of
    ///     OWNER_CELL_ID/FEDERATION_ID);
    ///   * if the proof carries the ZERO sentinel (the prover has not yet
    ///     surfaced the class into the PI on this leg — the named remainder),
    ///     the executor falls back to the trusted ledger class for ITS OWN
    ///     grouping. This keeps the executor path sound (ledger-backed) without
    ///     blocking on the prover threading; the BUNDLE/light-client path still
    ///     groups strictly by the PI value, so closing the remainder (prover
    ///     populates `EffectVmContext::asset_class`) is what makes the pure
    ///     light-client partition non-trivial for multi-asset turns.
    ///
    /// Fails closed when the PI vector is too short to carry the active v3
    /// layout (it cannot be a valid v3 proof).
    fn resolve_proof_asset_class(
        public_inputs: &[dregg_circuit::field::BabyBear],
        ledger: &Ledger,
        cell: &CellId,
    ) -> Result<dregg_circuit::field::BabyBear, AtomicTurnError> {
        use dregg_circuit::field::BabyBear;
        let proof_asset = dregg_circuit::extract_asset_class(public_inputs).ok_or_else(|| {
            AtomicTurnError::ProofFailed {
                cell: *cell,
                reason: "failed to extract ASSET_CLASS from proof PI (PI vector shorter than the \
                         active v3 layout)"
                    .to_string(),
            }
        })?;
        let ledger_asset = Self::asset_class_for_cell(ledger, cell);
        if proof_asset == BabyBear::ZERO {
            // Prover has not yet surfaced the class on this leg — executor
            // falls back to its trusted ledger class (sound here; the named
            // light-client remainder).
            return Ok(ledger_asset);
        }
        if proof_asset != ledger_asset {
            return Err(AtomicTurnError::ProofFailed {
                cell: *cell,
                reason: "proof-bound asset class (PI[ASSET_CLASS]) does not match the cell's \
                         committed token_id — refusing a mislabeled asset partition"
                    .to_string(),
            });
        }
        Ok(proof_asset)
    }

    /// THE LIGHT-CLIENT-SOUND PER-ASSET CONSERVATION GATE. Identical arithmetic
    /// to [`check_per_asset_conservation`] but keyed by the PROOF-BOUND asset
    /// class (`PI[v3::ASSET_CLASS]`) supplied per entry rather than a ledger
    /// lookup. Each `(asset, proven_net_delta)` is grouped by `asset` and EACH
    /// asset is required to conserve to zero independently. The light client /
    /// bundle path uses THIS variant because it has no ledger; the executor
    /// uses it too (after reconciling the proof-bound class against its trusted
    /// ledger token_id) so both paths partition identically.
    fn check_per_asset_conservation_by_asset(
        entries: &[(dregg_circuit::field::BabyBear, i64)],
        declared_supply: &[dregg_circuit::block_conservation::DeclaredSupplyChange],
    ) -> Result<(), AtomicTurnError> {
        use dregg_circuit::block_conservation::{BlockConservation, PerCellContribution};
        use dregg_circuit::field::BabyBear;

        let mut block = BlockConservation::new();
        for (asset, delta) in entries {
            let sign_credit = *delta >= 0;
            block.add_contribution(PerCellContribution {
                asset: *asset,
                net_delta_mag: BabyBear::new_canonical(delta.unsigned_abs() as u32),
                net_delta_sign: if sign_credit {
                    BabyBear::ZERO
                } else {
                    BabyBear::ONE
                },
            });
        }
        for s in declared_supply {
            block.add_supply_change(*s);
        }

        if let Err(dregg_circuit::block_conservation::BlockConservationError::AssetImbalanced {
            asset,
            imbalance,
        }) = block.check()
        {
            return Err(AtomicTurnError::PerAssetConservationViolation {
                asset: asset.0,
                imbalance,
            });
        }

        Ok(())
    }

    // -----------------------------------------------------------------------
    // Per-cell atomic receipts (closes AIR-SOUNDNESS-AUDIT.md #69)
    // -----------------------------------------------------------------------
    //
    // Atomic multi-party turns previously returned only commitments / deltas,
    // making the central executor law `execute_turn(S, T) = (S', R)` literally
    // unimplementable for that path: there was no `R`. This block emits one
    // `TurnReceipt` per cell touched (sovereign + hosted) with the per-entry
    // tuple `(cell_id, old, new, vk_hash, balance_delta)` bound into
    // `effects_hash` and the cell's chain head extended via
    // `record_receipt_hash`. Receipts are signed when the executor was
    // configured with a signing key (same path as cleartext turns).

    /// Deterministic identity hash of an `AtomicSovereignTurn` for receipt
    /// `turn_hash` binding. Captures every field that affects the result so
    /// receipts from two distinct atomic turns never collide.
    fn atomic_sovereign_turn_hash(turn: &AtomicSovereignTurn) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(b"dregg-atomic-sovereign-turn-v1");
        h.update(turn.agent.as_bytes());
        h.update(&turn.nonce.to_le_bytes());
        h.update(&turn.fee.to_le_bytes());
        h.update(&(turn.proofs.len() as u64).to_le_bytes());
        for e in &turn.proofs {
            h.update(e.cell_id.as_bytes());
            h.update(&e.old_commitment);
            h.update(&e.new_commitment);
            h.update(&e.effects_hash);
            h.update(&e.balance_delta.to_le_bytes());
            h.update(&(e.proof.len() as u64).to_le_bytes());
            h.update(&e.proof);
        }
        *h.finalize().as_bytes()
    }

    /// Deterministic identity hash of a `MixedAtomicTurn` (sovereign + hosted).
    fn mixed_atomic_turn_hash(turn: &MixedAtomicTurn) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(b"dregg-mixed-atomic-turn-v1");
        h.update(turn.agent.as_bytes());
        h.update(&turn.nonce.to_le_bytes());
        h.update(&turn.fee.to_le_bytes());
        h.update(&(turn.sovereign_entries.len() as u64).to_le_bytes());
        for e in &turn.sovereign_entries {
            h.update(e.cell_id.as_bytes());
            h.update(&e.old_commitment);
            h.update(&e.new_commitment);
            h.update(&e.effects_hash);
            h.update(&e.balance_delta.to_le_bytes());
            h.update(&(e.proof.len() as u64).to_le_bytes());
            h.update(&e.proof);
        }
        h.update(&(turn.hosted_actions.len() as u64).to_le_bytes());
        for a in &turn.hosted_actions {
            // Hash a stable encoding of each action: target + method + effect
            // count + the per-effect runtime tag (so any structural mutation
            // shows up). The full Action::hash equivalent lives in
            // `crate::forest`; this hash is independent because atomic turns
            // are not call-forests.
            h.update(a.target.as_bytes());
            h.update(&a.method);
            h.update(&(a.effects.len() as u64).to_le_bytes());
            for ef in &a.effects {
                h.update(&[Self::effect_tag_byte(ef)]);
            }
        }
        *h.finalize().as_bytes()
    }

    /// Coarse runtime tag for an `Effect` used inside atomic turn-hash
    /// computation. Distinct values per variant; bound only into receipt
    /// turn-hash, not into any AIR.
    fn effect_tag_byte(e: &Effect) -> u8 {
        use crate::action::Effect as E;
        match e {
            E::Transfer { .. } => 0x01,
            E::Burn { .. } => 0x02,
            E::Mint { .. } => 0x0B,
            E::SetField { .. } => 0x03,
            E::IncrementNonce { .. } => 0x04,
            E::SetVerificationKey { .. } => 0x05,
            E::SetPermissions { .. } => 0x06,
            E::CreateCell { .. } => 0x07,
            E::GrantCapability { .. } => 0x08,
            E::RevokeCapability { .. } => 0x09,
            E::EmitEvent { .. } => 0x0A,
            _ => 0xFF,
        }
    }

    /// Per-entry receipt-extension hash binding the audit-mandated tuple
    /// `(cell_id, old_state_commitment, new_state_commitment, vk_hash,
    /// balance_delta)`. Bound into the receipt's `effects_hash` so a tamper
    /// of any field re-derives a different `receipt_hash`.
    fn atomic_entry_effects_hash(
        cell_id: &CellId,
        old: &[u8; 32],
        new: &[u8; 32],
        vk_hash: Option<[u8; 32]>,
        balance_delta: i64,
    ) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(b"dregg-atomic-entry-effects-v1");
        h.update(cell_id.as_bytes());
        h.update(old);
        h.update(new);
        match vk_hash {
            Some(v) => {
                h.update(&[1u8]);
                h.update(&v);
            }
            None => {
                h.update(&[0u8]);
            }
        }
        h.update(&balance_delta.to_le_bytes());
        *h.finalize().as_bytes()
    }

    /// Build a `TurnReceipt` for one cell-entry in an atomic turn, chain it to
    /// that cell's previous receipt, and sign it (if configured). Each entry
    /// produces its OWN witness receipt: per the central law
    /// `execute_turn(S,T) = (S', R)`, atomic turns produce one R per cell they
    /// advance. The chain-integrity HEAD is recorded by the CALLER, and ONLY for
    /// the submitting AGENT — a merely-touched cell gets its witness receipt but
    /// no gating head, so a touch never locks a causal edge the cell's next
    /// authored turn must thread (and the agent's head stays deterministic: one
    /// cell, fixed data).
    #[allow(clippy::too_many_arguments)]
    fn build_atomic_per_cell_receipt(
        &self,
        turn_hash: [u8; 32],
        cell_id: CellId,
        old_commitment: [u8; 32],
        new_commitment: [u8; 32],
        vk_hash: Option<[u8; 32]>,
        balance_delta: i64,
        was_burn: bool,
        consumed_capabilities: Vec<crate::turn::ConsumedCapWitness>,
    ) -> TurnReceipt {
        // Chain the per-cell receipt to this cell's PROVENANCE head (its own
        // receipt history), not the authority chain — so the per-cell chain stays
        // walkable while the authority head (which gates `previous_receipt_hash`)
        // advances only for the submitting agent (recorded by the caller).
        let prev = self.get_per_cell_head(&cell_id);
        let effects_hash = Self::atomic_entry_effects_hash(
            &cell_id,
            &old_commitment,
            &new_commitment,
            vk_hash,
            balance_delta,
        );
        let mut receipt = TurnReceipt {
            turn_hash,
            forest_hash: turn_hash, // atomic turns have no call-forest; bind to turn-hash
            pre_state_hash: old_commitment,
            post_state_hash: new_commitment,
            timestamp: self.current_timestamp,
            effects_hash,
            computrons_used: 0,
            action_count: 1,
            previous_receipt_hash: prev,
            agent: cell_id,
            federation_id: self.local_federation_id,
            routing_directives: vec![],
            introduction_exports: vec![],
            derivation_records: vec![],
            emitted_events: vec![],
            executor_signature: None,
            finality: Finality::Final,
            // Atomic turns are submitted in the clear today; the encrypted-
            // path wrapper (`apply_encrypted_turn`) only governs single
            // call-forest turns. If/when an EncryptedAtomicTurn lands the
            // wrapper will flip this bit before re-signing.
            was_encrypted: false,
            was_burn,
            consumed_capabilities,
        };
        receipt.executor_signature = self.maybe_sign_receipt(&receipt);
        // NB: the chain-integrity HEAD is no longer recorded here. The caller
        // records it, and ONLY for the submitting AGENT — see the doc comment.
        receipt
    }

    /// Execute an atomic multi-party sovereign turn.
    ///
    /// This verifies ALL proofs atomically and checks cross-cell conservation:
    /// the sum of all `balance_delta` values across entries must be zero.
    ///
    /// On success, all sovereign commitments are updated simultaneously.
    /// On failure (any proof invalid or conservation violated), no state changes.
    pub fn execute_atomic_sovereign(
        &self,
        atomic_turn: &AtomicSovereignTurn,
        ledger: &mut Ledger,
    ) -> Result<(Vec<[u8; 32]>, Vec<TurnReceipt>), AtomicTurnError> {
        use dregg_circuit::field::BabyBear;

        // 0. Basic validation.
        if atomic_turn.proofs.is_empty() {
            return Err(AtomicTurnError::EmptyProofs);
        }

        // Check for duplicate cells.
        let mut seen_cells = std::collections::HashSet::new();
        for entry in &atomic_turn.proofs {
            if !seen_cells.insert(entry.cell_id) {
                return Err(AtomicTurnError::DuplicateCell(entry.cell_id));
            }
        }

        // P0-4: reject any frozen agent or proof-entry cell.
        if self
            .cell_migrations
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .is_frozen(&atomic_turn.agent)
        {
            return Err(AtomicTurnError::FrozenCell(atomic_turn.agent));
        }
        {
            let mig = self
                .cell_migrations
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            for entry in &atomic_turn.proofs {
                if mig.is_frozen(&entry.cell_id) {
                    return Err(AtomicTurnError::FrozenCell(entry.cell_id));
                }
            }
        }

        // 1. Agent validation (fee + nonce).
        let agent_cell = ledger
            .get(&atomic_turn.agent)
            .ok_or(AtomicTurnError::AgentNotFound(atomic_turn.agent))?;
        if agent_cell.state.nonce() != atomic_turn.nonce {
            return Err(AtomicTurnError::NonceMismatch {
                expected: agent_cell.state.nonce(),
                got: atomic_turn.nonce,
            });
        }
        if agent_cell.state.balance() < 0 || (agent_cell.state.balance() as u64) < atomic_turn.fee {
            return Err(AtomicTurnError::InsufficientFee {
                available: agent_cell.state.balance(),
                required: atomic_turn.fee,
            });
        }

        // 2. Verify each proof entry and extract proven balance deltas.
        let mut new_commitments: Vec<(CellId, [u8; 32])> =
            Vec::with_capacity(atomic_turn.proofs.len());
        let mut proven_deltas: Vec<i64> = Vec::with_capacity(atomic_turn.proofs.len());
        // Per-entry PROOF-BOUND asset class (PI[v3::ASSET_CLASS]), the partition
        // key the per-asset conservation gate groups by — read from the proof,
        // not the ledger (light-client soundness).
        let mut proven_assets: Vec<dregg_circuit::field::BabyBear> =
            Vec::with_capacity(atomic_turn.proofs.len());
        // Per-entry (old_commitment, vk_hash) cached for receipt construction
        // at commit time. Indexed parallel to `atomic_turn.proofs`.
        let mut entry_receipt_inputs: Vec<([u8; 32], Option<[u8; 32]>)> =
            Vec::with_capacity(atomic_turn.proofs.len());

        for entry in &atomic_turn.proofs {
            let stored_commitment = if let Some(c) = ledger.get_sovereign_commitment(&entry.cell_id)
            {
                *c
            } else if let Some(reg) = ledger.get_sovereign_registration(&entry.cell_id) {
                reg.commitment
            } else {
                return Err(AtomicTurnError::NotSovereign(entry.cell_id));
            };

            if entry.old_commitment != stored_commitment {
                return Err(AtomicTurnError::CommitmentMismatch {
                    cell: entry.cell_id,
                    expected: stored_commitment,
                    got: entry.old_commitment,
                });
            }

            let wire: AtomicProofWire =
                postcard::from_bytes(&entry.proof).map_err(|e| AtomicTurnError::ProofFailed {
                    cell: entry.cell_id,
                    reason: e.to_string(),
                })?;

            // Phase C: reconstruct Effect VM PI in the PI v3 layout
            // (resolves REVIEW[effect-vm-coord]). Commitments are 8 GENUINE
            // Poseidon2 felts each (~124-bit collision floor, matching FRI);
            // other PIs are forwarded from the wire PI vector and bound by the
            // AIR's boundary/transition constraints + the PI matching loop below.
            let old_commit_8 = Self::commitment_to_8bb(&entry.old_commitment);
            let new_commit_8 = Self::commitment_to_8bb(&entry.new_commitment);

            use dregg_circuit::effect_vm::pi;
            let min_pi_count = pi::ACTIVE_BASE_COUNT;
            if wire.public_inputs.len() < min_pi_count {
                return Err(AtomicTurnError::ProofFailed {
                    cell: entry.cell_id,
                    reason: format!(
                        "proof has {} public inputs, expected at least {} (PI v3 layout)",
                        wire.public_inputs.len(),
                        min_pi_count
                    ),
                });
            }

            // Forward all PI elements from the wire, then override
            // commitment slots with verifier-derived values.
            let mut public_inputs: Vec<BabyBear> = (0..min_pi_count)
                .map(|i| BabyBear::new_canonical(wire.public_inputs[i]))
                .collect();
            public_inputs[pi::OLD_COMMIT_BASE..(pi::OLD_COMMIT_BASE + pi::OLD_COMMIT_LEN)]
                .copy_from_slice(&old_commit_8[..pi::OLD_COMMIT_LEN]);
            public_inputs[pi::NEW_COMMIT_BASE..(pi::NEW_COMMIT_BASE + pi::NEW_COMMIT_LEN)]
                .copy_from_slice(&new_commit_8[..pi::NEW_COMMIT_LEN]);

            // Append custom proof entries from the wire PIs.
            let custom_count_val = public_inputs[pi::CUSTOM_EFFECT_COUNT].0 as usize;
            for i in 0..custom_count_val {
                let base = pi::CUSTOM_PROOFS_BASE + i * pi::CUSTOM_ENTRY_SIZE;
                if base + pi::CUSTOM_ENTRY_SIZE > wire.public_inputs.len() {
                    break;
                }
                for j in 0..pi::CUSTOM_ENTRY_SIZE {
                    public_inputs.push(BabyBear::new_canonical(wire.public_inputs[base + j]));
                }
            }

            // Verify reconstructed commitment PIs match the wire's embedded PIs
            // (all 8 felts each, Phase C widening — the full 8-felt off-AIR match
            // is what lifts the collision floor to ~124 bits).
            for i in 0..pi::OLD_COMMIT_LEN {
                let proof_v = BabyBear::new_canonical(wire.public_inputs[pi::OLD_COMMIT_BASE + i]);
                if proof_v != old_commit_8[i] {
                    return Err(AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: format!(
                            "old_commitment in proof does not match stored value (felt {})",
                            i
                        ),
                    });
                }
            }
            for i in 0..pi::NEW_COMMIT_LEN {
                let proof_v = BabyBear::new_canonical(wire.public_inputs[pi::NEW_COMMIT_BASE + i]);
                if proof_v != new_commit_8[i] {
                    return Err(AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: format!(
                            "new_commitment in proof does not match claimed value (felt {})",
                            i
                        ),
                    });
                }
            }

            // Verify against custom program (lowered to the IR-v2 descriptor).
            let vk_hash = self.get_cell_vk_hash(&entry.cell_id, ledger);
            if let Some(vk) = vk_hash {
                if let Some(program) = self.program_registry.get(&vk) {
                    let desc =
                        dregg_circuit_prove::custom_leaf_adapter::cellprogram_to_descriptor2(
                            program,
                        )
                        .map_err(|e| AtomicTurnError::ProofFailed {
                            cell: entry.cell_id,
                            reason: e,
                        })?;
                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        dregg_circuit::descriptor_ir2::verify_vm_descriptor2(
                            &desc,
                            &wire.proof,
                            &public_inputs,
                        )
                    }))
                    .map_err(|_| AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: "descriptor verifier panicked on malformed proof".to_string(),
                    })?
                    .map_err(|e| AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: e,
                    })?;
                } else {
                    return Err(AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: format!(
                            "cell has vk_hash {:02x}{:02x}... but no matching program",
                            vk[0], vk[1]
                        ),
                    });
                }
            } else {
                // The v1 default hand-AIR (`EffectVmAir`) verify for a no-VK cell is RETIRED.
                // A no-VK cell's transition is attested through the rotated proof-carrying path,
                // so an atomic entry with a v1 default-AIR proof fails closed.
                let _ = &wire;
                return Err(AtomicTurnError::ProofFailed {
                    cell: entry.cell_id,
                    reason: "cell has no custom program VK; the v1 default-AIR verify is retired \
                             (use the rotated proof-carrying path)"
                        .to_string(),
                });
            }

            // Extract proven balance delta from PI.
            let proven_delta =
                dregg_circuit::extract_net_delta(&public_inputs).ok_or_else(|| {
                    AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: "failed to extract balance_delta from proof PI".to_string(),
                    }
                })?;

            // Resolve the per-cell ASSET CLASS the conservation gate partitions
            // on. The proof publishes it at PI[v3::ASSET_CLASS] (light-client
            // path); the executor — which HAS the ledger — reconciles it against
            // the cell's committed token_id (the OWNER_CELL_ID/FEDERATION_ID
            // verifier-reconstruction posture). See `resolve_proof_asset_class`.
            let proven_asset =
                Self::resolve_proof_asset_class(&public_inputs, ledger, &entry.cell_id)?;

            proven_deltas.push(proven_delta);
            proven_assets.push(proven_asset);
            new_commitments.push((entry.cell_id, entry.new_commitment));
            entry_receipt_inputs.push((entry.old_commitment, vk_hash));
        }

        // 3. PER-ASSET conservation using PROVEN deltas (not declared
        //    entry.balance_delta). The old asset-BLIND scalar sum
        //    (`proven_deltas.iter().sum() == 0`) forged value across asset
        //    boundaries: a turn (asset 7 −10, asset 8 +10) netted to 0 and was
        //    accepted. The replacement groups each proven delta by its PROOF-
        //    BOUND asset class (PI[v3::ASSET_CLASS], read from the verified
        //    proof — NOT a ledger lookup) and requires EACH asset's Σδ=0
        //    INDEPENDENTLY through the in-AIR-backed `BlockConservation`
        //    collector. An AtomicSovereignTurn carries no declared mint/burn
        //    rows, so a hidden mint within any asset (or any cross-asset
        //    borrowing) is rejected.
        let conservation_entries: Vec<(dregg_circuit::field::BabyBear, i64)> = proven_assets
            .iter()
            .copied()
            .zip(proven_deltas.iter().copied())
            .collect();
        Self::check_per_asset_conservation_by_asset(&conservation_entries, &[])?;

        // 4. All proofs verified + conservation holds. Commit atomically.
        // Deduct fee and increment nonce. THE EPOCH §5 ("fees as moves"):
        // the fee is a MOVE agent→fee-well, not a burn — with a configured
        // well the atomic turn's total value delta is exactly zero.
        {
            let agent = ledger.get_mut(&atomic_turn.agent).unwrap();
            let prior_balance = agent.state.balance();
            if !agent.state.debit_balance(atomic_turn.fee) {
                return Err(AtomicTurnError::ProofFailed {
                    cell: atomic_turn.agent,
                    reason: format!(
                        "agent balance {prior_balance} cannot cover fee {}",
                        atomic_turn.fee
                    ),
                });
            }
            if !agent.state.increment_nonce() {
                return Err(AtomicTurnError::NonceOverflow(atomic_turn.agent));
            }
        }
        if let Some(well_id) = &self.fee_well_cell {
            if let Some(well) = ledger.get_mut(well_id) {
                let _ = well.state.credit_balance(atomic_turn.fee);
            }
        }

        // Update all sovereign commitments.
        let mut resulting_commitments = Vec::with_capacity(new_commitments.len());
        for (cell_id, new_commitment) in &new_commitments {
            if ledger.is_sovereign(cell_id) {
                let _ = ledger.update_sovereign_commitment(cell_id, *new_commitment);
            } else {
                let old = ledger
                    .get_sovereign_registration(cell_id)
                    .map(|r| r.commitment)
                    .unwrap_or([0u8; 32]);
                let _ = ledger.update_sovereign_registration_commitment(
                    cell_id,
                    old,
                    *new_commitment,
                    self.block_height,
                );
            }
            resulting_commitments.push(*new_commitment);
        }

        // 5. Emit one TurnReceipt per cell touched. Closes
        // AIR-SOUNDNESS-AUDIT.md issue #69 ("atomic-path receipt seam"):
        // the executor-law `execute_turn(S, T) = (S', R)` now produces an
        // R for every sovereign cell advanced. Each receipt chains to that
        // cell's previous receipt and is recorded as the new chain head.
        let turn_hash = Self::atomic_sovereign_turn_hash(atomic_turn);
        let mut receipts = Vec::with_capacity(new_commitments.len());
        for (idx, (cell_id, new_commitment)) in new_commitments.iter().enumerate() {
            let (old_commitment, vk_hash) = entry_receipt_inputs[idx];
            let receipt = self.build_atomic_per_cell_receipt(
                turn_hash,
                *cell_id,
                old_commitment,
                *new_commitment,
                vk_hash,
                proven_deltas[idx],
                // AtomicSovereignTurn has no hosted side, so no runtime
                // Effect::Burn is visible to the executor on this path.
                // (Sovereign cells may implement burn-semantics inside their
                // STARK; that disclosure rides in the proof's PI, not here.)
                false,
                // Sovereign entries authorize via STARK proof, not via a
                // hosted-side capability — no consumed-cap witness.
                vec![],
            );
            // Per-cell PROVENANCE chain advances for EVERY touched cell (a walkable
            // per-cell receipt history); the AUTHORITY head (which gates a turn's
            // previous_receipt_hash) advances ONLY for the submitting agent, so a
            // cell merely advanced by another agent's turn isn't locked to a causal
            // edge it never made (don't lock intended causality).
            self.record_per_cell_head(*cell_id, receipt.receipt_hash());
            if *cell_id == atomic_turn.agent {
                self.record_receipt_hash(*cell_id, receipt.receipt_hash());
            }
            receipts.push(receipt);
        }

        Ok((resulting_commitments, receipts))
    }

    /// Execute a mixed atomic turn containing both sovereign (proof-carrying) and
    /// hosted (federation-executed) cells in a single atomic operation.
    ///
    /// Conservation is enforced across BOTH: sovereign deltas (extracted from proofs)
    /// plus hosted deltas (computed from execution) must sum to zero.
    ///
    /// SECURITY (C1 fix): every hosted action's authorization is verified through
    /// the standard `verify_authorization` pipeline before any of its effects
    /// apply, and ALL hosted mutations are journaled so that any subsequent
    /// failure (auth, precondition, effect-apply, conservation) rolls back the
    /// entire turn atomically. Previously the hosted side could mutate any
    /// cell's balance without authorization.
    pub fn execute_mixed_atomic(
        &self,
        mixed_turn: &MixedAtomicTurn,
        ledger: &mut Ledger,
    ) -> Result<MixedAtomicResult, AtomicTurnError> {
        // Closes AIR-SOUNDNESS-AUDIT.md #69 for the mixed-atomic path: emit
        // one TurnReceipt per cell touched (sovereign + hosted), chain it to
        // that cell's prior receipt, and record the new chain head.
        use dregg_circuit::field::BabyBear;

        if mixed_turn.sovereign_entries.is_empty() && mixed_turn.hosted_actions.is_empty() {
            return Err(AtomicTurnError::EmptyProofs);
        }

        // cap Phase C: fresh consumed-capability buffer for this turn (the
        // hosted side runs `verify_authorization`, which captures witnesses).
        self.consumed_cap_witnesses
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .clear();

        let agent_cell = ledger
            .get(&mixed_turn.agent)
            .ok_or(AtomicTurnError::AgentNotFound(mixed_turn.agent))?;
        if agent_cell.state.nonce() != mixed_turn.nonce {
            return Err(AtomicTurnError::NonceMismatch {
                expected: agent_cell.state.nonce(),
                got: mixed_turn.nonce,
            });
        }
        if agent_cell.state.balance() < 0 || (agent_cell.state.balance() as u64) < mixed_turn.fee {
            return Err(AtomicTurnError::InsufficientFee {
                available: agent_cell.state.balance(),
                required: mixed_turn.fee,
            });
        }

        // P0-4: reject any frozen agent, sovereign-entry cell, or hosted-action
        // target cell.
        {
            let mig = self
                .cell_migrations
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            if mig.is_frozen(&mixed_turn.agent) {
                return Err(AtomicTurnError::FrozenCell(mixed_turn.agent));
            }
            for entry in &mixed_turn.sovereign_entries {
                if mig.is_frozen(&entry.cell_id) {
                    return Err(AtomicTurnError::FrozenCell(entry.cell_id));
                }
            }
            for action in &mixed_turn.hosted_actions {
                if mig.is_frozen(&action.target) {
                    return Err(AtomicTurnError::FrozenCell(action.target));
                }
            }
        }

        // Verify sovereign proofs and extract proven deltas.
        let mut sovereign_deltas: Vec<i64> = Vec::new();
        // Parallel PROOF-BOUND asset class per sovereign entry (PI[v3::ASSET_CLASS]).
        let mut sovereign_assets: Vec<dregg_circuit::field::BabyBear> = Vec::new();
        let mut new_commitments: Vec<(CellId, [u8; 32])> = Vec::new();
        // Parallel to sovereign_entries: (old_commitment, vk_hash) needed at
        // receipt-emission time.
        let mut sovereign_receipt_inputs: Vec<([u8; 32], Option<[u8; 32]>)> =
            Vec::with_capacity(mixed_turn.sovereign_entries.len());

        for entry in &mixed_turn.sovereign_entries {
            let stored_commitment = if let Some(c) = ledger.get_sovereign_commitment(&entry.cell_id)
            {
                *c
            } else if let Some(reg) = ledger.get_sovereign_registration(&entry.cell_id) {
                reg.commitment
            } else {
                return Err(AtomicTurnError::NotSovereign(entry.cell_id));
            };

            if entry.old_commitment != stored_commitment {
                return Err(AtomicTurnError::CommitmentMismatch {
                    cell: entry.cell_id,
                    expected: stored_commitment,
                    got: entry.old_commitment,
                });
            }

            let wire: AtomicProofWire =
                postcard::from_bytes(&entry.proof).map_err(|e| AtomicTurnError::ProofFailed {
                    cell: entry.cell_id,
                    reason: e.to_string(),
                })?;

            // Phase C: reconstruct Effect VM PI in the PI v3 layout
            // (resolves REVIEW[effect-vm-coord]). 8 genuine commitment felts.
            let old_commit_8 = Self::commitment_to_8bb(&entry.old_commitment);
            let new_commit_8 = Self::commitment_to_8bb(&entry.new_commitment);

            use dregg_circuit::effect_vm::pi;
            let min_pi_count = pi::ACTIVE_BASE_COUNT;
            if wire.public_inputs.len() < min_pi_count {
                return Err(AtomicTurnError::ProofFailed {
                    cell: entry.cell_id,
                    reason: format!(
                        "proof has {} public inputs, expected at least {} (PI v3 layout)",
                        wire.public_inputs.len(),
                        min_pi_count
                    ),
                });
            }

            let mut public_inputs: Vec<BabyBear> = (0..min_pi_count)
                .map(|i| BabyBear::new_canonical(wire.public_inputs[i]))
                .collect();
            public_inputs[pi::OLD_COMMIT_BASE..(pi::OLD_COMMIT_BASE + pi::OLD_COMMIT_LEN)]
                .copy_from_slice(&old_commit_8[..pi::OLD_COMMIT_LEN]);
            public_inputs[pi::NEW_COMMIT_BASE..(pi::NEW_COMMIT_BASE + pi::NEW_COMMIT_LEN)]
                .copy_from_slice(&new_commit_8[..pi::NEW_COMMIT_LEN]);

            // Append custom proof entries from the wire PIs.
            let custom_count_val = public_inputs[pi::CUSTOM_EFFECT_COUNT].0 as usize;
            for i in 0..custom_count_val {
                let base = pi::CUSTOM_PROOFS_BASE + i * pi::CUSTOM_ENTRY_SIZE;
                if base + pi::CUSTOM_ENTRY_SIZE > wire.public_inputs.len() {
                    break;
                }
                for j in 0..pi::CUSTOM_ENTRY_SIZE {
                    public_inputs.push(BabyBear::new_canonical(wire.public_inputs[base + j]));
                }
            }

            // Verify commitment PIs match (8 felts each, Phase C).
            for i in 0..pi::OLD_COMMIT_LEN {
                let proof_v = BabyBear::new_canonical(wire.public_inputs[pi::OLD_COMMIT_BASE + i]);
                if proof_v != old_commit_8[i] {
                    return Err(AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: format!(
                            "old_commitment in proof does not match stored value (felt {})",
                            i
                        ),
                    });
                }
            }
            for i in 0..pi::NEW_COMMIT_LEN {
                let proof_v = BabyBear::new_canonical(wire.public_inputs[pi::NEW_COMMIT_BASE + i]);
                if proof_v != new_commit_8[i] {
                    return Err(AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: format!(
                            "new_commitment in proof does not match claimed value (felt {})",
                            i
                        ),
                    });
                }
            }

            // Verify against custom program (lowered to the IR-v2 descriptor).
            let vk_hash = self.get_cell_vk_hash(&entry.cell_id, ledger);
            if let Some(vk) = vk_hash {
                if let Some(program) = self.program_registry.get(&vk) {
                    let desc =
                        dregg_circuit_prove::custom_leaf_adapter::cellprogram_to_descriptor2(
                            program,
                        )
                        .map_err(|e| AtomicTurnError::ProofFailed {
                            cell: entry.cell_id,
                            reason: e,
                        })?;
                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        dregg_circuit::descriptor_ir2::verify_vm_descriptor2(
                            &desc,
                            &wire.proof,
                            &public_inputs,
                        )
                    }))
                    .map_err(|_| AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: "descriptor verifier panicked on malformed proof".to_string(),
                    })?
                    .map_err(|e| AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: e,
                    })?;
                } else {
                    return Err(AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: "program not found for vk_hash".to_string(),
                    });
                }
            } else {
                // The v1 default hand-AIR (`EffectVmAir`) verify for a no-VK cell is RETIRED
                // (the no-VK cell's transition is attested through the rotated proof-carrying
                // path), so it fails closed.
                let _ = &wire;
                return Err(AtomicTurnError::ProofFailed {
                    cell: entry.cell_id,
                    reason: "cell has no custom program VK; the v1 default-AIR verify is retired \
                             (use the rotated proof-carrying path)"
                        .to_string(),
                });
            }

            let proven_delta =
                dregg_circuit::extract_net_delta(&public_inputs).ok_or_else(|| {
                    AtomicTurnError::ProofFailed {
                        cell: entry.cell_id,
                        reason: "failed to extract balance_delta from proof PI".to_string(),
                    }
                })?;

            // PROOF-BOUND asset class from PI[v3::ASSET_CLASS], reconciled
            // against the cell's committed ledger token_id (executor has the
            // ledger; the light client trusts the PI-bound class directly).
            let proven_asset =
                Self::resolve_proof_asset_class(&public_inputs, ledger, &entry.cell_id)?;

            sovereign_deltas.push(proven_delta);
            sovereign_assets.push(proven_asset);
            new_commitments.push((entry.cell_id, entry.new_commitment));
            sovereign_receipt_inputs.push((entry.old_commitment, vk_hash));
        }

        // ====================================================================
        // HOSTED SIDE (C1 FIX): each hosted action is authorized via the same
        // `verify_authorization` pipeline as `execute()` and applied through
        // `apply_effect` with full journaling. On any failure (auth,
        // precondition, effect, conservation) the entire journal is rolled
        // back -- no partial state is left in the ledger.
        // ====================================================================
        let mut journal = LedgerJournal::with_capacity(16);
        let mut hosted_deltas: Vec<i64> = Vec::with_capacity(mixed_turn.hosted_actions.len());
        // Tracks the true per-cell balance change across ALL hosted actions for
        // the cross-domain conservation check. Unlike `hosted_deltas` (which is
        // per-action and only reflects effects targeting that action's cell),
        // this map accounts for every cell touched by any effect (e.g. the `to`
        // side of a Transfer from another action).
        let mut hosted_cell_deltas: HashMap<CellId, i64> = HashMap::new();
        // Parallel to hosted_actions: (cell_id, pre_state_commitment,
        // post_state_commitment, vk_hash, was_burn). Captured around each
        // action's effect application so the per-cell pre/post pair is
        // accurate even though all hosted actions execute on one ledger.
        let mut hosted_receipt_inputs: Vec<(CellId, [u8; 32], [u8; 32], Option<[u8; 32]>, bool)> =
            Vec::with_capacity(mixed_turn.hosted_actions.len());

        for (idx, action) in mixed_turn.hosted_actions.iter().enumerate() {
            // 1. Target cell must exist.
            let target_cell = match ledger.get(&action.target) {
                Some(c) => c.clone(),
                None => {
                    journal.rollback(
                        ledger,
                        &self.bridged_nullifiers,
                        &self.note_nullifiers,
                        &self.note_commitments,
                        &self.note_revoked,
                    );
                    return Err(AtomicTurnError::HostedApplyFailed {
                        cell: action.target,
                        reason: format!("hosted action #{} target cell not found", idx),
                    });
                }
            };

            // 2. Authorization (the C1 fix). Use the same gate as `execute()`.
            let path = vec![idx];
            if let Err((err, _path)) = self.verify_authorization(
                action,
                &target_cell,
                ledger,
                &mixed_turn.agent,
                &path,
                mixed_turn.nonce,
            ) {
                journal.rollback(
                    ledger,
                    &self.bridged_nullifiers,
                    &self.note_nullifiers,
                    &self.note_commitments,
                    &self.note_revoked,
                );
                return Err(AtomicTurnError::HostedAuthorizationFailed {
                    cell: action.target,
                    reason: format!("{err}"),
                });
            }

            // 3. Preconditions.
            if let Err((err, _)) = self.check_preconditions(action, &target_cell, &path) {
                journal.rollback(
                    ledger,
                    &self.bridged_nullifiers,
                    &self.note_nullifiers,
                    &self.note_commitments,
                    &self.note_revoked,
                );
                return Err(AtomicTurnError::HostedApplyFailed {
                    cell: action.target,
                    reason: format!("{err}"),
                });
            }

            // Snapshot the target cell's pre-state commitment for the
            // receipt. Bound into the receipt's pre_state_hash; the
            // post-state is recomputed after applying the action's effects.
            let pre_state_commitment = ledger
                .get(&action.target)
                .map(|c| c.state_commitment())
                .unwrap_or([0u8; 32]);
            let target_vk_hash = self.get_cell_vk_hash(&action.target, ledger);
            // The hosted-side `was_burn` flag is per-cell: any Burn effect
            // *targeting* this action's `target` cell flips the bit. Bound
            // into receipt_hash so executor can't strip the disclosure.
            let mut action_was_burn = false;

            // 4. Apply each effect via apply_effect (which is journaled).
            // Compute the net Transfer delta for this hosted entry for the
            // conservation check after-the-fact.
            let mut net_delta: i64 = 0;
            for effect in &action.effects {
                if let crate::action::Effect::Transfer { from, to, amount } = effect {
                    if from == &action.target {
                        net_delta -= *amount as i64;
                    }
                    if to == &action.target {
                        net_delta += *amount as i64;
                    }
                    *hosted_cell_deltas.entry(*from).or_insert(0) -= *amount as i64;
                    *hosted_cell_deltas.entry(*to).or_insert(0) += *amount as i64;
                }
                // Burn debits the target. SUPPLY-MODEL Stage 1: EVERY asset
                // resolves an ISSUER WELL now (registered override, else the
                // deterministic per-asset well lazily materialized by
                // `apply_burn`), so the burn is ALWAYS a MOVE target→well (the
                // well is credited back toward zero) and contributes ZERO net
                // — `was_burn` stays as the disclosure bit. The well shares the
                // target's asset class (same `token_id`), so the debit/credit
                // net to zero WITHIN the asset (per-asset conservation holds).
                if let crate::action::Effect::Burn { target, amount, .. } = effect {
                    if target == &action.target {
                        net_delta -= *amount as i64;
                        action_was_burn = true;
                    }
                    *hosted_cell_deltas.entry(*target).or_insert(0) -= *amount as i64;
                    if let Some(well_id) = self.issuer_well_for(ledger, target) {
                        *hosted_cell_deltas.entry(well_id).or_insert(0) += *amount as i64;
                        if well_id == action.target {
                            net_delta += *amount as i64;
                        }
                    }
                }
                // Mint is the DUAL (SUPPLY-MODEL Stage 2a): the issuer WELL is
                // DEBITED (going more negative) and the recipient is CREDITED, so
                // the mint is a conserving MOVE well→target contributing ZERO net
                // within the asset (same per-asset conservation as burn, sign-
                // flipped). The well shares the target's asset class.
                if let crate::action::Effect::Mint { target, amount, .. } = effect {
                    if target == &action.target {
                        net_delta += *amount as i64;
                    }
                    *hosted_cell_deltas.entry(*target).or_insert(0) += *amount as i64;
                    if let Some(well_id) = self.issuer_well_for(ledger, target) {
                        *hosted_cell_deltas.entry(well_id).or_insert(0) -= *amount as i64;
                        if well_id == action.target {
                            net_delta -= *amount as i64;
                        }
                    }
                }
                if let Err((err, _)) = self.apply_effect(
                    effect,
                    ledger,
                    &path,
                    &action.target,
                    &mixed_turn.agent,
                    &mut journal,
                ) {
                    journal.rollback(
                        ledger,
                        &self.bridged_nullifiers,
                        &self.note_nullifiers,
                        &self.note_commitments,
                        &self.note_revoked,
                    );
                    return Err(AtomicTurnError::HostedApplyFailed {
                        cell: action.target,
                        reason: format!("{err}"),
                    });
                }
            }
            hosted_deltas.push(net_delta);
            // Capture the post-state commitment AFTER effects apply.
            let post_state_commitment = ledger
                .get(&action.target)
                .map(|c| c.state_commitment())
                .unwrap_or([0u8; 32]);
            hosted_receipt_inputs.push((
                action.target,
                pre_state_commitment,
                post_state_commitment,
                target_vk_hash,
                action_was_burn,
            ));
        }

        // Cross-domain PER-ASSET conservation: sovereign + hosted deltas must
        // conserve to zero WITHIN EACH ASSET (not merely in a single asset-blind
        // scalar sum). Each asset is required to conserve independently — so a
        // turn that nets to zero ACROSS assets but forges value WITHIN an asset
        // (or borrows across asset boundaries) is rejected.
        //
        // The SOVEREIGN side groups by the PROOF-BOUND asset class
        // (PI[v3::ASSET_CLASS], read from each verified proof and reconciled
        // against the ledger above) — the light-client-sound partition key. The
        // HOSTED side carries NO per-cell proof (deltas are derived by the
        // executor from `apply_effect`), so its asset class is read from the
        // committed ledger token_id (token_id is immutable across a turn, so
        // reading after hosted mutations is exact). The hosted side is therefore
        // executor-bound, not proof-bound — the stated residual for a PURELY
        // light-client mixed-turn (no ledger); the sovereign side is fully
        // proof-bound.
        let mut conservation_entries: Vec<(dregg_circuit::field::BabyBear, i64)> = sovereign_assets
            .iter()
            .copied()
            .zip(sovereign_deltas.iter().copied())
            .collect();
        for (cell_id, delta) in &hosted_cell_deltas {
            conservation_entries.push((Self::asset_class_for_cell(ledger, cell_id), *delta));
        }
        if let Err(e) = Self::check_per_asset_conservation_by_asset(&conservation_entries, &[]) {
            // Roll back ALL hosted mutations before returning.
            journal.rollback(
                ledger,
                &self.bridged_nullifiers,
                &self.note_nullifiers,
                &self.note_commitments,
                &self.note_revoked,
            );
            return Err(e);
        }

        // ====================================================================
        // COMMIT: hosted mutations are already in place (in `ledger`) via
        // apply_effect; we just commit fee, nonce, and sovereign commitment
        // updates. We deliberately do NOT call rollback on the journal -- we
        // want to keep the mutations; the journal is dropped on success.
        // ====================================================================
        {
            let agent = ledger.get_mut(&mixed_turn.agent).unwrap();
            let prior_balance = agent.state.balance();
            // THE EPOCH §5: ordinary debit (refuses below zero) instead of a
            // raw subtraction that could underflow.
            if !agent.state.debit_balance(mixed_turn.fee) {
                journal.rollback(
                    ledger,
                    &self.bridged_nullifiers,
                    &self.note_nullifiers,
                    &self.note_commitments,
                    &self.note_revoked,
                );
                return Err(AtomicTurnError::ProofFailed {
                    cell: mixed_turn.agent,
                    reason: format!(
                        "agent balance {prior_balance} cannot cover fee {}",
                        mixed_turn.fee
                    ),
                });
            }
            if !agent.state.increment_nonce() {
                return Err(AtomicTurnError::NonceOverflow(mixed_turn.agent));
            }
        }
        // THE EPOCH §5 ("fees as moves"): the fee MOVES to the fee well.
        if let Some(well_id) = &self.fee_well_cell {
            if let Some(well) = ledger.get_mut(well_id) {
                let _ = well.state.credit_balance(mixed_turn.fee);
            }
        }

        for (cell_id, new_commitment) in &new_commitments {
            if ledger.is_sovereign(cell_id) {
                let _ = ledger.update_sovereign_commitment(cell_id, *new_commitment);
            } else {
                let old = ledger
                    .get_sovereign_registration(cell_id)
                    .map(|r| r.commitment)
                    .unwrap_or([0u8; 32]);
                let _ = ledger.update_sovereign_registration_commitment(
                    cell_id,
                    old,
                    *new_commitment,
                    self.block_height,
                );
            }
        }

        // Emit one TurnReceipt per cell touched: sovereign entries first
        // (in declared order), then hosted actions (in declared order).
        let turn_hash = Self::mixed_atomic_turn_hash(mixed_turn);
        // cap Phase C: drain the consumed-cap witnesses captured by the
        // hosted-side `verify_authorization` calls above; each hosted action
        // ran with `path = vec![idx]`, so `action_path[0]` attributes a
        // witness to its hosted receipt.
        let consumed = self.take_consumed_cap_witnesses();
        let mut receipts = Vec::with_capacity(new_commitments.len() + hosted_receipt_inputs.len());
        for (idx, (cell_id, new_commitment)) in new_commitments.iter().enumerate() {
            let (old_commitment, vk_hash) = sovereign_receipt_inputs[idx];
            let receipt = self.build_atomic_per_cell_receipt(
                turn_hash,
                *cell_id,
                old_commitment,
                *new_commitment,
                vk_hash,
                sovereign_deltas[idx],
                // Sovereign-side Burn rides in the cell's STARK proof, not
                // visible to the executor as a runtime Effect::Burn.
                false,
                // Sovereign entries authorize via STARK proof — no consumed
                // hosted-side capability.
                vec![],
            );
            self.record_per_cell_head(*cell_id, receipt.receipt_hash());
            if *cell_id == mixed_turn.agent {
                self.record_receipt_hash(*cell_id, receipt.receipt_hash());
            }
            receipts.push(receipt);
        }
        for (idx, (cell_id, pre, post, vk_hash, was_burn)) in
            hosted_receipt_inputs.iter().enumerate()
        {
            let receipt = self.build_atomic_per_cell_receipt(
                turn_hash,
                *cell_id,
                *pre,
                *post,
                *vk_hash,
                hosted_deltas[idx],
                *was_burn,
                consumed
                    .iter()
                    .filter(|w| w.action_path.first() == Some(&idx))
                    .cloned()
                    .collect(),
            );
            self.record_per_cell_head(*cell_id, receipt.receipt_hash());
            if *cell_id == mixed_turn.agent {
                self.record_receipt_hash(*cell_id, receipt.receipt_hash());
            }
            receipts.push(receipt);
        }

        Ok(MixedAtomicResult {
            sovereign_commitments: new_commitments.iter().map(|(_, c)| *c).collect(),
            sovereign_deltas,
            hosted_deltas,
            receipts,
        })
    }
}
// =============================================================================
// Adversarial Tests for CRITICAL/P0 fixes (C1, P0-3, P0-4)
// =============================================================================

#[cfg(test)]
mod hardening_tests {
    use super::*;
    use crate::action::{Action, Authorization, DelegationMode, Effect};
    use crate::forest::{CallForest, CallTree};
    use crate::turn::Turn;
    use crate::{ComputronCosts, TurnError, TurnResult};
    use dregg_cell::permissions::{AuthRequired, Permissions};
    use dregg_cell::{Cell, Preconditions};

    fn permissive() -> Permissions {
        Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        }
    }

    fn make_permissive_cell(seed: u8, balance: i64) -> Cell {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        let token = [0u8; 32];
        let mut cell = Cell::with_balance(pk, token, balance);
        cell.permissions = permissive();
        cell
    }

    fn make_signed_cell(seed: u8, balance: i64) -> Cell {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        let token = [0u8; 32];
        // Default permissions: Signature required.
        Cell::with_balance(pk, token, balance)
    }

    /// A permissive cell whose ASSET CLASS (token_id) is set: `asset` seeds the
    /// 32-byte token_id so two cells with different `asset` belong to different
    /// asset classes (the dregg3 "AssetId := issuer-cell" partition).
    fn make_asset_cell(seed: u8, asset: u8, balance: i64) -> Cell {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        let mut token = [0u8; 32];
        token[0] = asset;
        let mut cell = Cell::with_balance(pk, token, balance);
        cell.permissions = permissive();
        cell
    }

    fn build_noop_turn(agent: CellId, nonce: u64) -> Turn {
        let action = Action {
            target: agent,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };
        let tree = CallTree {
            action,
            children: vec![],
            hash: [0u8; 32],
        };
        Turn {
            agent,
            nonce,
            call_forest: CallForest {
                roots: vec![tree],
                forest_hash: [0u8; 32],
            },
            fee: 0,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        }
    }

    // ---------------- P0-3: previous_receipt_hash enforcement ----------------

    /// Submit two turns with the same nonce=0 and `previous_receipt_hash: None`.
    /// The second MUST be rejected -- without the P0-3 fix the executor would
    /// accept both because it never bound the receipt chain at write time.
    #[test]
    fn previous_receipt_hash_replay_blocked() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(1, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        let turn1 = build_noop_turn(agent_id, 0);
        let r1 = executor.execute(&turn1, &mut ledger);
        assert!(r1.is_committed(), "first turn should commit: {:?}", r1);

        // Second turn from same agent with previous_receipt_hash: None.
        // Reset nonce by building with nonce 1 (which is the actual next nonce).
        let turn2 = build_noop_turn(agent_id, 1);
        let r2 = executor.execute(&turn2, &mut ledger);
        match r2 {
            TurnResult::Rejected {
                reason: TurnError::ReceiptChainMismatch { expected, got },
                ..
            } => {
                assert!(expected.is_some(), "expected = Some(prev_receipt_hash)");
                assert!(got.is_none(), "got = None (the bug pattern)");
            }
            other => panic!("expected ReceiptChainMismatch, got: {:?}", other),
        }
    }

    /// Submit a non-genesis turn whose `previous_receipt_hash` doesn't match
    /// the prior receipt -- MUST be rejected (no rebranching the chain).
    #[test]
    fn previous_receipt_hash_wrong_chain_rejected() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(1, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        let turn1 = build_noop_turn(agent_id, 0);
        let r1 = executor.execute(&turn1, &mut ledger);
        assert!(r1.is_committed());

        // Build turn2 with WRONG previous_receipt_hash.
        let mut turn2 = build_noop_turn(agent_id, 1);
        turn2.previous_receipt_hash = Some([0xAB; 32]);
        let r2 = executor.execute(&turn2, &mut ledger);
        match r2 {
            TurnResult::Rejected {
                reason: TurnError::ReceiptChainMismatch { expected, got },
                ..
            } => {
                assert!(expected.is_some());
                assert_eq!(got, Some([0xAB; 32]));
            }
            other => panic!("expected ReceiptChainMismatch, got: {:?}", other),
        }
    }

    /// Properly chained sequential turns MUST commit.
    #[test]
    fn previous_receipt_hash_correct_chain_accepted() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(1, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        let turn1 = build_noop_turn(agent_id, 0);
        let (_, receipt1, _) = executor.execute(&turn1, &mut ledger).unwrap_committed();

        let mut turn2 = build_noop_turn(agent_id, 1);
        turn2.previous_receipt_hash = Some(receipt1.receipt_hash());
        let r2 = executor.execute(&turn2, &mut ledger);
        assert!(
            r2.is_committed(),
            "correctly-chained turn must commit: {:?}",
            r2
        );
    }

    /// A turn that claims a prior receipt when the executor has none on file
    /// MUST be rejected (a cclerk can't fake an established chain).
    #[test]
    fn previous_receipt_hash_genesis_with_some_rejected() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(1, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        let mut turn = build_noop_turn(agent_id, 0);
        turn.previous_receipt_hash = Some([0x42; 32]);
        let r = executor.execute(&turn, &mut ledger);
        match r {
            TurnResult::Rejected {
                reason: TurnError::ReceiptChainMismatch { expected, got },
                ..
            } => {
                assert!(expected.is_none(), "executor has no prior receipt");
                assert_eq!(got, Some([0x42; 32]));
            }
            other => panic!("expected ReceiptChainMismatch, got: {:?}", other),
        }
    }

    // ---------------- P0-4: CellMigrationManager enforcement ----------------

    /// A turn whose agent cell is frozen for migration MUST be rejected.
    #[test]
    fn migration_frozen_agent_blocks_execute() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(1, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        // Freeze the agent cell for migration.
        executor
            .cell_migrations
            .lock()
            .unwrap()
            .begin_migration(agent_id, [0xDD; 32], 0, 100)
            .unwrap();

        let turn = build_noop_turn(agent_id, 0);
        let r = executor.execute(&turn, &mut ledger);
        match r {
            TurnResult::Rejected {
                reason: TurnError::CellFrozen { cell },
                ..
            } => assert_eq!(cell, agent_id),
            other => panic!("expected CellFrozen, got: {:?}", other),
        }
    }

    /// A turn that transfers TO a frozen cell MUST be rejected.
    #[test]
    fn migration_frozen_target_blocks_transfer() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(1, 10_000);
        let agent_id = agent.id();
        let target = make_permissive_cell(2, 0);
        let target_id = target.id();
        // Grant agent capability to target so cross-cell check passes.
        let mut a = agent;
        a.capabilities.grant(target_id, AuthRequired::None);
        ledger.insert_cell(a).unwrap();
        ledger.insert_cell(target).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());
        executor
            .cell_migrations
            .lock()
            .unwrap()
            .begin_migration(target_id, [0xDD; 32], 0, 100)
            .unwrap();

        // Build a transfer turn (agent -> target).
        let action = Action {
            target: agent_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Transfer {
                from: agent_id,
                to: target_id,
                amount: 100,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };
        let tree = CallTree {
            action,
            children: vec![],
            hash: [0u8; 32],
        };
        let mut turn = build_noop_turn(agent_id, 0);
        turn.call_forest = CallForest {
            roots: vec![tree],
            forest_hash: [0u8; 32],
        };
        turn.fee = 0;

        let r = executor.execute(&turn, &mut ledger);
        match r {
            TurnResult::Rejected {
                reason: TurnError::CellFrozen { cell },
                ..
            } => assert_eq!(cell, target_id),
            other => panic!("expected CellFrozen(target), got: {:?}", other),
        }
    }

    /// `execute_atomic_sovereign` MUST reject when a sovereign-entry cell is
    /// frozen.
    #[test]
    fn migration_frozen_blocks_atomic_sovereign() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(1, 1000);
        let agent_id = agent.id();
        let frozen_id = CellId([0xCC; 32]);
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());
        executor
            .cell_migrations
            .lock()
            .unwrap()
            .begin_migration(frozen_id, [0xDD; 32], 0, 100)
            .unwrap();

        let atomic = AtomicSovereignTurn {
            agent: agent_id,
            nonce: 0,
            fee: 0,
            proofs: vec![AtomicProofEntry {
                cell_id: frozen_id,
                proof: vec![1, 2, 3, 4],
                old_commitment: [0u8; 32],
                new_commitment: [1u8; 32],
                effects_hash: [0u8; 32],
                balance_delta: 0,
            }],
        };

        let r = executor.execute_atomic_sovereign(&atomic, &mut ledger);
        match r {
            Err(AtomicTurnError::FrozenCell(cell)) => assert_eq!(cell, frozen_id),
            other => panic!("expected FrozenCell, got: {:?}", other),
        }
    }

    // ---------------- CRITICAL C1: execute_mixed_atomic auth ----------------

    /// The CRITICAL fix: a hosted action targeting a cell the caller has no
    /// authority over MUST be rejected by `execute_mixed_atomic`. Without the
    /// fix, the call would mutate the target cell's balance.
    #[test]
    fn mixed_atomic_hosted_unauthorized_rejected() {
        let mut ledger = Ledger::new();
        // Agent (attacker) and victim cell both exist; victim REQUIRES Signature.
        let agent = make_permissive_cell(0xAA, 1000);
        let agent_id = agent.id();
        let victim = make_signed_cell(0xBB, 1000);
        let victim_id = victim.id();
        ledger.insert_cell(agent).unwrap();
        ledger.insert_cell(victim.clone()).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        // Attacker constructs a hosted action that targets the victim cell but
        // provides `Authorization::Unchecked` (no signature). The victim cell's
        // default permissions require Signature for SetField; verify_authorization
        // MUST reject.
        let malicious_action = Action {
            target: victim_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::SetField {
                cell: victim_id,
                index: 0,
                value: [0xFF; 32],
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };

        let mixed = MixedAtomicTurn {
            agent: agent_id,
            nonce: 0,
            fee: 0,
            sovereign_entries: vec![],
            hosted_actions: vec![malicious_action],
        };

        let r = executor.execute_mixed_atomic(&mixed, &mut ledger);
        assert!(
            matches!(r, Err(AtomicTurnError::HostedAuthorizationFailed { cell, .. }) if cell == victim_id),
            "expected HostedAuthorizationFailed on victim cell, got: {:?}",
            r
        );

        // Victim's state MUST be unchanged.
        let v = ledger.get(&victim_id).unwrap();
        assert_eq!(v.state.fields[0], dregg_cell::state::FIELD_ZERO);
    }

    /// C1 / P1-7: a later hosted-action failure MUST roll back earlier hosted
    /// mutations within the same `execute_mixed_atomic` call.
    #[test]
    fn mixed_atomic_late_failure_rolls_back_hosted_mutations() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(0xAA, 100);
        let agent_id = agent.id();
        let cell_b = make_permissive_cell(0xBB, 1_000);
        let cell_b_id = cell_b.id();
        let cell_c = make_permissive_cell(0xCC, 50);
        let cell_c_id = cell_c.id();
        ledger.insert_cell(agent).unwrap();
        ledger.insert_cell(cell_b).unwrap();
        ledger.insert_cell(cell_c).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        // Action 1: B sends 100 to C (succeeds; both permissive).
        let a1 = Action {
            target: cell_b_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Transfer {
                from: cell_b_id,
                to: cell_c_id,
                amount: 100,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };
        // Action 2: C sends 999_999 to B (FAILS: insufficient balance after first
        // action). Journal MUST roll back action 1.
        let a2 = Action {
            target: cell_c_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Transfer {
                from: cell_c_id,
                to: cell_b_id,
                amount: 999_999,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };

        let mixed = MixedAtomicTurn {
            agent: agent_id,
            nonce: 0,
            fee: 0,
            sovereign_entries: vec![],
            hosted_actions: vec![a1, a2],
        };

        let r = executor.execute_mixed_atomic(&mixed, &mut ledger);
        assert!(r.is_err(), "expected late failure, got: {:?}", r);

        // Balances MUST be unchanged (rollback worked).
        assert_eq!(ledger.get(&cell_b_id).unwrap().state.balance(), 1_000);
        assert_eq!(ledger.get(&cell_c_id).unwrap().state.balance(), 50);
    }

    /// P2-2: set_timestamp MUST silently ignore backwards-in-time updates.
    #[test]
    fn set_timestamp_backwards_no_op() {
        let mut executor = TurnExecutor::new(ComputronCosts::zero());
        executor.set_timestamp(100);
        assert_eq!(executor.current_timestamp, 100);
        executor.set_timestamp(50); // backwards
        assert_eq!(executor.current_timestamp, 100, "must not go backwards");
        executor.set_timestamp(100); // same
        assert_eq!(executor.current_timestamp, 100);
        executor.set_timestamp(200); // forward
        assert_eq!(executor.current_timestamp, 200);
    }

    /// A hosted Transfer from a victim's cell MUST be rejected (the attacker
    /// has no Signature for the victim's Send permission).
    #[test]
    fn mixed_atomic_hosted_unauthorized_transfer_blocked() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(0xAA, 100);
        let agent_id = agent.id();
        let victim = make_signed_cell(0xBB, 10_000);
        let victim_id = victim.id();
        ledger.insert_cell(agent).unwrap();
        ledger.insert_cell(victim).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        // Malicious hosted action: transfer from victim -> agent.
        let action = Action {
            target: victim_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Transfer {
                from: victim_id,
                to: agent_id,
                amount: 5_000,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };

        let mixed = MixedAtomicTurn {
            agent: agent_id,
            nonce: 0,
            fee: 0,
            sovereign_entries: vec![],
            hosted_actions: vec![action],
        };

        let r = executor.execute_mixed_atomic(&mixed, &mut ledger);
        assert!(matches!(
            r,
            Err(AtomicTurnError::HostedAuthorizationFailed { .. })
        ));

        // Both balances UNCHANGED.
        assert_eq!(ledger.get(&victim_id).unwrap().state.balance(), 10_000);
        assert_eq!(ledger.get(&agent_id).unwrap().state.balance(), 100);
    }

    // ---------------- R-4: executor_signature actually populated -----------
    //
    // EFFECT-VM-SHAPE-A.md R-4: previously TurnReceipt.executor_signature was
    // never set, so the federation-exit path could not authenticate receipts
    // as having come from a known executor. These tests pin the new behavior:
    //
    //   1. Without a signing key configured, receipts keep the legacy None.
    //   2. With a signing key configured (via `with_executor_signing_key`),
    //      every committed receipt is signed over receipt_hash().
    //   3. The signature verifies under the executor's matching public key
    //      and is rejected under any other key.

    #[test]
    fn executor_signature_default_none() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(7, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let turn = build_noop_turn(agent_id, 0);
        let result = executor.execute(&turn, &mut ledger);
        match result {
            TurnResult::Committed { receipt, .. } => {
                assert!(
                    receipt.executor_signature.is_none(),
                    "without with_executor_signing_key, executor_signature must remain None"
                );
            }
            other => panic!("expected Committed, got {:?}", other),
        }
    }

    #[test]
    fn executor_signature_populated_and_verifies() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(11, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        // Deterministic key seed for the test.
        let seed: [u8; 32] = *b"dregg-test-executor-sk-r4-fix!!!";
        let sk = ed25519_dalek::SigningKey::from_bytes(&seed);
        let pk_bytes = sk.verifying_key().to_bytes();

        let executor = TurnExecutor::new(ComputronCosts::zero()).with_executor_signing_key(seed);
        let turn = build_noop_turn(agent_id, 0);

        let result = executor.execute(&turn, &mut ledger);
        let receipt = match result {
            TurnResult::Committed { receipt, .. } => receipt,
            other => panic!("expected Committed, got {:?}", other),
        };

        // Signature is present and exactly 64 bytes.
        let sig_bytes = receipt
            .executor_signature
            .as_ref()
            .expect("executor_signature must be populated when signing key configured");
        assert_eq!(sig_bytes.len(), 64);

        // Chain verification accepts the receipt under the matching key.
        crate::verify::verify_receipt_chain_with_keys(&[receipt.clone()], &[pk_bytes])
            .expect("receipt chain must verify under the executor's public key");

        // ...and rejects it under any other key.
        let mut wrong_key = pk_bytes;
        wrong_key[0] ^= 0x80;
        let err = crate::verify::verify_receipt_chain_with_keys(&[receipt], &[wrong_key])
            .expect_err("verification must fail under a foreign key");
        assert!(
            matches!(
                err,
                crate::verify::VerifyError::ExecutorSignatureInvalid { .. }
            ),
            "expected ExecutorSignatureInvalid, got {:?}",
            err
        );
    }

    // =========================================================================
    // Lane-2 honesty sweep: adversarial tests for Authorization::OneOf and
    // Effect::Refusal. Pre-sweep, the structural primitives existed but no
    // executor-side test ever constructed them, so the defensive cascade
    // (executor.rs ~5812 for OneOf; the new Refusal-vs-mutation guard) was
    // dead code from a coverage standpoint.
    // =========================================================================

    use crate::action::RefusalReason;

    /// Build a single-action turn whose action carries `authorization`
    /// and the given `effects`. Target is the agent itself; no
    /// preconditions; permissive cell so authorization is the only
    /// gate the executor checks.
    fn build_single_action_turn(
        agent: CellId,
        nonce: u64,
        authorization: Authorization,
        effects: Vec<Effect>,
    ) -> Turn {
        let action = Action {
            target: agent,
            method: [0u8; 32],
            args: vec![],
            authorization,
            preconditions: Preconditions::default(),
            effects,
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };
        let tree = CallTree {
            action,
            children: vec![],
            hash: [0u8; 32],
        };
        Turn {
            agent,
            nonce,
            call_forest: CallForest {
                roots: vec![tree],
                forest_hash: [0u8; 32],
            },
            fee: 0,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        }
    }

    /// `Authorization::OneOf { candidates, proof_index }` with `proof_index`
    /// past the end of `candidates` MUST be rejected with an
    /// `InvalidAuthorization` whose reason mentions "out of bounds".
    /// Pins the defensive cascade at executor.rs ~5818.
    #[test]
    fn one_of_rejects_out_of_bounds_proof_index() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(0x71, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        // 1 candidate, proof_index=5 -> out of bounds.
        let auth = Authorization::OneOf {
            candidates: vec![Authorization::Signature([0u8; 32], [0u8; 32])],
            proof_index: 5,
        };
        let turn = build_single_action_turn(agent_id, 0, auth, vec![]);

        let r = executor.execute(&turn, &mut ledger);
        match r {
            TurnResult::Rejected {
                reason: TurnError::InvalidAuthorization { reason },
                ..
            } => {
                assert!(
                    reason.contains("out of bounds"),
                    "expected reason to mention 'out of bounds', got: {reason}"
                );
            }
            other => panic!(
                "expected InvalidAuthorization (out of bounds), got: {:?}",
                other
            ),
        }
    }

    /// `Authorization::OneOf` whose indexed candidate is
    /// `Authorization::Unchecked` MUST be rejected — `OneOf` must not
    /// reduce to an auth-bypass-by-naming-Unchecked surface.
    /// Pins the defensive cascade at executor.rs ~5833.
    #[test]
    fn one_of_rejects_unchecked_indexed_slot() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(0x72, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        // Candidates: [Unchecked, Signature]; indexed slot 0 is Unchecked.
        let auth = Authorization::OneOf {
            candidates: vec![
                Authorization::Unchecked,
                Authorization::Signature([0u8; 32], [0u8; 32]),
            ],
            proof_index: 0,
        };
        let turn = build_single_action_turn(agent_id, 0, auth, vec![]);

        let r = executor.execute(&turn, &mut ledger);
        match r {
            TurnResult::Rejected {
                reason: TurnError::InvalidAuthorization { reason },
                ..
            } => {
                assert!(
                    reason.contains("Unchecked"),
                    "expected reason to mention 'Unchecked', got: {reason}"
                );
            }
            other => panic!(
                "expected InvalidAuthorization (Unchecked indexed slot), got: {:?}",
                other
            ),
        }
    }

    /// An action that carries both `Effect::Refusal { cell, .. }` and
    /// `Effect::SetField { cell, .. }` on the SAME cell MUST be rejected
    /// with `RefusalConflictsWithMutation`. Refusal is "evidence of
    /// non-action" — it cannot coexist with a real state mutation
    /// on the same target within a single action.
    #[test]
    fn refusal_conflicts_with_set_field_on_same_cell() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(0x73, 1000);
        let agent_id = agent.id();
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        let refusal = Effect::Refusal {
            cell: agent_id,
            offered_action_commitment: [0xAB; 32],
            refusal_reason: RefusalReason::Declined,
            proof_witness_index: 0,
        };
        let set_field = Effect::SetField {
            cell: agent_id,
            index: 0,
            value: [0xCD; 32],
        };

        let turn = build_single_action_turn(
            agent_id,
            0,
            Authorization::Unchecked,
            vec![refusal, set_field],
        );

        let r = executor.execute(&turn, &mut ledger);
        match r {
            TurnResult::Rejected {
                reason:
                    TurnError::RefusalConflictsWithMutation {
                        cell,
                        ref conflicting_effect,
                    },
                ..
            } => {
                assert_eq!(cell, agent_id);
                assert_eq!(conflicting_effect, "SetField");
            }
            other => panic!("expected RefusalConflictsWithMutation, got: {:?}", other),
        }

        // Agent's slot[0] MUST remain at FIELD_ZERO -- the entire action
        // was rejected closed, no mutation applied.
        assert_eq!(
            ledger.get(&agent_id).unwrap().state.fields[0],
            dregg_cell::state::FIELD_ZERO
        );
    }

    // =========================================================================
    // AIR-SOUNDNESS-AUDIT.md #69: atomic-path receipt emission.
    //
    // The central executor law `execute_turn(S, T) = (S', R)` was previously
    // unimplementable for atomic turns because `execute_atomic_sovereign` /
    // `execute_mixed_atomic` returned only commitments / deltas. These tests
    // pin the new behavior: receipts are emitted per cell touched, chained
    // to each cell's prior head, and bound to the per-entry tuple
    // `(cell_id, old, new, vk_hash, balance_delta)` via `effects_hash`.
    // =========================================================================

    /// A hosted-only `MixedAtomicTurn` (no sovereign entries) emits one
    /// receipt per hosted action's target cell. The receipt's pre/post state
    /// hashes reflect the per-cell state commitment around effect application.
    #[test]
    fn mixed_atomic_emits_receipt_per_hosted_cell() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(0xA0, 1_000);
        let agent_id = agent.id();
        let cell_b = make_permissive_cell(0xB0, 5_000);
        let cell_b_id = cell_b.id();
        let cell_c = make_permissive_cell(0xC0, 1_000);
        let cell_c_id = cell_c.id();
        ledger.insert_cell(agent).unwrap();
        ledger.insert_cell(cell_b).unwrap();
        ledger.insert_cell(cell_c).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        // Two hosted actions: B sends 100 to C, then C sends 100 to B (net zero).
        let a1 = Action {
            target: cell_b_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Transfer {
                from: cell_b_id,
                to: cell_c_id,
                amount: 100,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };
        let a2 = Action {
            target: cell_c_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Transfer {
                from: cell_c_id,
                to: cell_b_id,
                amount: 100,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };

        let mixed = MixedAtomicTurn {
            agent: agent_id,
            nonce: 0,
            fee: 0,
            sovereign_entries: vec![],
            hosted_actions: vec![a1, a2],
        };

        let res = executor.execute_mixed_atomic(&mixed, &mut ledger).unwrap();
        assert_eq!(
            res.receipts.len(),
            2,
            "expected one receipt per hosted action, got {}",
            res.receipts.len()
        );
        assert_eq!(res.receipts[0].agent, cell_b_id);
        assert_eq!(res.receipts[1].agent, cell_c_id);
        // Pre/post-state hashes must differ for each cell because each
        // transfer changes that cell's balance.
        assert_ne!(
            res.receipts[0].pre_state_hash, res.receipts[0].post_state_hash,
            "cell B's state commitment must change"
        );
        assert_ne!(
            res.receipts[1].pre_state_hash, res.receipts[1].post_state_hash,
            "cell C's state commitment must change"
        );
        // The first receipt for each cell is genesis (no prior).
        assert_eq!(res.receipts[0].previous_receipt_hash, None);
        assert_eq!(res.receipts[1].previous_receipt_hash, None);
        // No Burn → was_burn must be false on both receipts.
        assert!(!res.receipts[0].was_burn);
        assert!(!res.receipts[1].was_burn);
    }

    /// Hash-chain extension: a second atomic turn on the same target cell
    /// must link via `previous_receipt_hash` to the cell's prior receipt.
    /// The executor records the new head under the cell's id (not the
    /// submitting agent's id) so the chain is per-cell.
    #[test]
    fn mixed_atomic_receipts_chain_per_cell() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(0xA1, 1_000);
        let agent_id = agent.id();
        let cell_b = make_permissive_cell(0xB1, 5_000);
        let cell_b_id = cell_b.id();
        let cell_c = make_permissive_cell(0xC1, 5_000);
        let cell_c_id = cell_c.id();
        ledger.insert_cell(agent).unwrap();
        ledger.insert_cell(cell_b).unwrap();
        ledger.insert_cell(cell_c).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        let make_swap = |from: CellId, to: CellId, amount: u64| Action {
            target: from,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Transfer { from, to, amount }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };

        // Turn 1: B sends to C, C sends to B (net zero each).
        let mixed1 = MixedAtomicTurn {
            agent: agent_id,
            nonce: 0,
            fee: 0,
            sovereign_entries: vec![],
            hosted_actions: vec![
                make_swap(cell_b_id, cell_c_id, 10),
                make_swap(cell_c_id, cell_b_id, 10),
            ],
        };
        let res1 = executor.execute_mixed_atomic(&mixed1, &mut ledger).unwrap();
        let head_b = res1.receipts[0].receipt_hash();
        let head_c = res1.receipts[1].receipt_hash();

        // Turn 2: same shape; receipts must chain to turn 1's per-cell heads.
        let mixed2 = MixedAtomicTurn {
            agent: agent_id,
            nonce: 1,
            fee: 0,
            sovereign_entries: vec![],
            hosted_actions: vec![
                make_swap(cell_b_id, cell_c_id, 20),
                make_swap(cell_c_id, cell_b_id, 20),
            ],
        };
        let res2 = executor.execute_mixed_atomic(&mixed2, &mut ledger).unwrap();
        assert_eq!(
            res2.receipts[0].previous_receipt_hash,
            Some(head_b),
            "turn 2's B-receipt must chain to turn 1's B-receipt"
        );
        assert_eq!(
            res2.receipts[1].previous_receipt_hash,
            Some(head_c),
            "turn 2's C-receipt must chain to turn 1's C-receipt"
        );
    }

    /// Tampering one delta in a multi-cell atomic must re-derive a
    /// different receipt hash. Built by rebuilding the receipt struct
    /// with a hand-tampered `effects_hash`-input tuple and comparing the
    /// resulting hash to the executor's emitted one.
    #[test]
    fn mixed_atomic_tampered_delta_diverges_receipt_hash() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(0xA2, 1_000);
        let agent_id = agent.id();
        let cell_b = make_permissive_cell(0xB2, 5_000);
        let cell_b_id = cell_b.id();
        let cell_c = make_permissive_cell(0xC2, 1_000);
        let cell_c_id = cell_c.id();
        ledger.insert_cell(agent).unwrap();
        ledger.insert_cell(cell_b).unwrap();
        ledger.insert_cell(cell_c).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let mixed = MixedAtomicTurn {
            agent: agent_id,
            nonce: 0,
            fee: 0,
            sovereign_entries: vec![],
            hosted_actions: vec![
                Action {
                    target: cell_b_id,
                    method: [0u8; 32],
                    args: vec![],
                    authorization: Authorization::Unchecked,
                    preconditions: Preconditions::default(),
                    effects: vec![Effect::Transfer {
                        from: cell_b_id,
                        to: cell_c_id,
                        amount: 50,
                    }],
                    may_delegate: DelegationMode::None,
                    commitment_mode: Default::default(),
                    balance_change: None,
                    witness_blobs: vec![],
                },
                Action {
                    target: cell_c_id,
                    method: [0u8; 32],
                    args: vec![],
                    authorization: Authorization::Unchecked,
                    preconditions: Preconditions::default(),
                    effects: vec![Effect::Transfer {
                        from: cell_c_id,
                        to: cell_b_id,
                        amount: 50,
                    }],
                    may_delegate: DelegationMode::None,
                    commitment_mode: Default::default(),
                    balance_change: None,
                    witness_blobs: vec![],
                },
            ],
        };
        let res = executor.execute_mixed_atomic(&mixed, &mut ledger).unwrap();
        let honest_hash = res.receipts[0].receipt_hash();

        // Build a tampered receipt with everything identical except a
        // shifted balance_delta in the effects_hash binding. cell_b's
        // hosted_delta is -50 (sent 50 to C); we shift it by +1 to
        // -49 and confirm the receipt hash diverges.
        let mut tampered = res.receipts[0].clone();
        tampered.effects_hash = TurnExecutor::atomic_entry_effects_hash(
            &cell_b_id,
            &res.receipts[0].pre_state_hash,
            &res.receipts[0].post_state_hash,
            None,                     // permissive cells have no vk_hash
            res.hosted_deltas[0] + 1, // tamper: shift cell_b's delta by 1
        );
        assert_ne!(
            tampered.receipt_hash(),
            honest_hash,
            "tampering balance_delta in effects_hash must change receipt_hash"
        );
    }

    /// SUPPLY-MODEL Stage 1: a hosted Burn is a CONSERVING holder→well MOVE,
    /// so a Burn-only mixed-atomic turn now COMMITS (it does NOT fail closed):
    /// the per-asset ISSUER WELL is lazily materialized and credited the burned
    /// amount, so the holder debit (−100) and well credit (+100) net to zero
    /// WITHIN the asset and per-asset conservation holds. The test pins (a) the
    /// commit, (b) `was_burn=true` on the burn target's receipt (the disclosure
    /// bit), and (c) the well exists and carries the +100 credit. (Pre-Stage-1
    /// this turn failed with `PerAssetConservationViolation(-100)` because the
    /// well-less burn was a non-conserving destroy.)
    #[test]
    fn mixed_atomic_was_burn_reflected_on_burn_target_receipt() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(0xA3, 1_000);
        let agent_id = agent.id();
        // The agent burns its OWN balance (self-redeem); permissive cells grant
        // the set_balance + increment_nonce the burn writes.
        ledger.insert_cell(agent).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());
        // SUPPLY-MODEL: a single-action hosted Burn now CONSERVES — the burned
        // value moves holder→well (the per-asset well lazily materialized), so
        // this turn commits with per-asset Σδ=0. Stage 3: this is a SELF-REDEEM
        // (the agent burns its OWN balance, `actor == target`), which is
        // permissionless — burning the victim's balance (no cap to reach it) is
        // now correctly REJECTED, so the test exercises the legitimate self-burn.
        let burn_action = Action {
            target: agent_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Burn {
                target: agent_id,
                slot: 0,
                amount: 100,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };
        let mixed = MixedAtomicTurn {
            agent: agent_id,
            nonce: 0,
            fee: 0,
            sovereign_entries: vec![],
            hosted_actions: vec![burn_action],
        };
        let r = executor.execute_mixed_atomic(&mixed, &mut ledger);
        // The conserving burn COMMITS. The receipt-input capture computed the
        // burn target's pre/post snapshots and flipped `was_burn`; the per-asset
        // conservation gate passed because the lazily-created well absorbed the
        // −100 as +100 within the asset.
        let result = r.expect("conserving burn must commit");
        let burn_receipt = result
            .receipts
            .iter()
            .find(|rc| rc.agent == agent_id)
            .expect("a receipt for the burn target");
        assert!(
            burn_receipt.was_burn,
            "the burn target's receipt must carry was_burn=true"
        );

        // Conservation: the holder was debited 100 and the per-asset well was
        // lazily created carrying the +100 credit (the default asset's well).
        assert_eq!(
            ledger.get(&agent_id).unwrap().state.balance(),
            1_000 - 100,
            "holder debited by the burn amount"
        );
        let (_pk, well_id) = TurnExecutor::derive_issuer_well(&[0u8; 32]);
        assert_eq!(
            ledger
                .get(&well_id)
                .expect("issuer well created")
                .state
                .balance(),
            100,
            "the per-asset well carries the burned amount (conserving move)"
        );
    }

    /// Smoke test: when the executor is configured with a signing key,
    /// atomic-emitted receipts carry a 64-byte executor_signature, just
    /// like cleartext turns (closes the R-4 gap on the atomic path).
    #[test]
    fn mixed_atomic_receipts_are_signed_when_key_configured() {
        let mut ledger = Ledger::new();
        let agent = make_permissive_cell(0xA4, 1_000);
        let agent_id = agent.id();
        let cell_b = make_permissive_cell(0xB4, 5_000);
        let cell_b_id = cell_b.id();
        let cell_c = make_permissive_cell(0xC4, 5_000);
        let cell_c_id = cell_c.id();
        ledger.insert_cell(agent).unwrap();
        ledger.insert_cell(cell_b).unwrap();
        ledger.insert_cell(cell_c).unwrap();

        let seed: [u8; 32] = *b"dregg-test-atomic-receipt-sk-#69";
        let executor = TurnExecutor::new(ComputronCosts::zero()).with_executor_signing_key(seed);

        let mixed = MixedAtomicTurn {
            agent: agent_id,
            nonce: 0,
            fee: 0,
            sovereign_entries: vec![],
            hosted_actions: vec![
                Action {
                    target: cell_b_id,
                    method: [0u8; 32],
                    args: vec![],
                    authorization: Authorization::Unchecked,
                    preconditions: Preconditions::default(),
                    effects: vec![Effect::Transfer {
                        from: cell_b_id,
                        to: cell_c_id,
                        amount: 1,
                    }],
                    may_delegate: DelegationMode::None,
                    commitment_mode: Default::default(),
                    balance_change: None,
                    witness_blobs: vec![],
                },
                Action {
                    target: cell_c_id,
                    method: [0u8; 32],
                    args: vec![],
                    authorization: Authorization::Unchecked,
                    preconditions: Preconditions::default(),
                    effects: vec![Effect::Transfer {
                        from: cell_c_id,
                        to: cell_b_id,
                        amount: 1,
                    }],
                    may_delegate: DelegationMode::None,
                    commitment_mode: Default::default(),
                    balance_change: None,
                    witness_blobs: vec![],
                },
            ],
        };
        let res = executor.execute_mixed_atomic(&mixed, &mut ledger).unwrap();
        for (i, r) in res.receipts.iter().enumerate() {
            let sig = r.executor_signature.as_ref().expect(&format!(
                "receipt[{i}] must be signed when key is configured"
            ));
            assert_eq!(sig.len(), 64);
        }
    }

    // =======================================================================
    // THE LIVE CONSERVATION HOLE: per-asset cross-cell conservation
    // =======================================================================
    //
    // The old check `proven_deltas.iter().sum() == 0` was ASSET-BLIND. A turn
    // moving 10 from a cell of asset 7 to a cell of asset 8 nets to 0 in the
    // scalar sum and was ACCEPTED — destroying asset 7 and minting asset 8.
    // These tests prove the replacement (the per-asset, in-AIR-backed
    // `BlockConservation` collector) REJECTS the cross-asset forge while still
    // ACCEPTING honest same-asset multi-cell turns.

    /// THE FORGING TURN, REJECTED. A mixed-atomic hosted Transfer of 10 from a
    /// cell of asset 7 to a cell of asset 8 nets to zero in the OLD scalar sum
    /// (so the old check accepted it), but asset 7 is short −10 and asset 8 is
    /// long +10 — each asset is independently unbalanced. The per-asset check
    /// REJECTS it, and the hosted mutation is rolled back.
    #[test]
    fn cross_asset_forge_rejected_mixed_atomic() {
        let mut ledger = Ledger::new();
        let agent = make_asset_cell(0xAA, 0, 1000); // native-asset agent (pays fee)
        let agent_id = agent.id();
        let cell_a = make_asset_cell(0xB7, 7, 100); // asset 7
        let cell_a_id = cell_a.id();
        let cell_b = make_asset_cell(0xB8, 8, 0); // asset 8
        let cell_b_id = cell_b.id();
        ledger.insert_cell(agent).unwrap();
        ledger.insert_cell(cell_a).unwrap();
        ledger.insert_cell(cell_b).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        // Move 10 from asset-7 cell A to asset-8 cell B. apply_transfer permits
        // a cross-token move (no token check there), so without the per-asset
        // gate this would commit: A −10 (asset 7), B +10 (asset 8), scalar sum 0.
        let forge = Action {
            target: cell_a_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Transfer {
                from: cell_a_id,
                to: cell_b_id,
                amount: 10,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };

        let mixed = MixedAtomicTurn {
            agent: agent_id,
            nonce: 0,
            fee: 0,
            sovereign_entries: vec![],
            hosted_actions: vec![forge],
        };

        let r = executor.execute_mixed_atomic(&mixed, &mut ledger);
        match r {
            Err(AtomicTurnError::PerAssetConservationViolation { imbalance, .. }) => {
                assert!(
                    imbalance == 10 || imbalance == -10,
                    "an asset must be off by ±10, got {imbalance}"
                );
            }
            other => panic!(
                "cross-asset forge MUST be rejected per-asset, got: {:?}",
                other
            ),
        }

        // Rollback: balances unchanged (the forge committed nothing).
        assert_eq!(ledger.get(&cell_a_id).unwrap().state.balance(), 100);
        assert_eq!(ledger.get(&cell_b_id).unwrap().state.balance(), 0);
    }

    /// HONEST SAME-ASSET MULTI-CELL TURN, ACCEPTED. A hosted Transfer of 10
    /// between two cells of the SAME asset (7) conserves within that asset and
    /// MUST still pass (no false reject).
    #[test]
    fn same_asset_transfer_still_accepted_mixed_atomic() {
        let mut ledger = Ledger::new();
        let agent = make_asset_cell(0xAA, 0, 1000);
        let agent_id = agent.id();
        let cell_a = make_asset_cell(0xC7, 7, 100); // asset 7
        let cell_a_id = cell_a.id();
        let cell_b = make_asset_cell(0xD7, 7, 0); // asset 7 (same asset)
        let cell_b_id = cell_b.id();
        ledger.insert_cell(agent).unwrap();
        ledger.insert_cell(cell_a).unwrap();
        ledger.insert_cell(cell_b).unwrap();

        let executor = TurnExecutor::new(ComputronCosts::zero());

        let honest = Action {
            target: cell_a_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Transfer {
                from: cell_a_id,
                to: cell_b_id,
                amount: 10,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };

        let mixed = MixedAtomicTurn {
            agent: agent_id,
            nonce: 0,
            fee: 0,
            sovereign_entries: vec![],
            hosted_actions: vec![honest],
        };

        let r = executor.execute_mixed_atomic(&mixed, &mut ledger);
        assert!(
            r.is_ok(),
            "honest same-asset transfer must NOT be falsely rejected, got: {:?}",
            r
        );
        assert_eq!(ledger.get(&cell_a_id).unwrap().state.balance(), 90);
        assert_eq!(ledger.get(&cell_b_id).unwrap().state.balance(), 10);
    }

    /// THE PER-ASSET COLLECTOR, DIRECT + IN-AIR. Exercises
    /// `check_per_asset_conservation` and the underlying committed per-asset
    /// `cross_cell_conservation_air` (via `BlockConservation::prove_and_verify`)
    /// so the gate is witnessed IN-CIRCUIT, not just as the executor's
    /// boundary-arithmetic pre-flight:
    ///   - asset 7 (A −10 / B +10) + asset 8 (C −5 / D +5): each balances → ACCEPT
    ///   - asset 7 (A −10) / asset 8 (B +10): cross-asset borrow → REJECT
    #[cfg(feature = "prover")]
    #[test]
    fn per_asset_collector_in_air_accept_reject() {
        use dregg_circuit::block_conservation::{BlockConservation, PerCellContribution};
        use dregg_circuit::field::BabyBear;

        let mut ledger = Ledger::new();
        let a = make_asset_cell(0xA1, 7, 100);
        let b = make_asset_cell(0xB1, 7, 0);
        let c = make_asset_cell(0xC1, 8, 100);
        let d = make_asset_cell(0xD1, 8, 0);
        let (a_id, b_id, c_id, d_id) = (a.id(), b.id(), c.id(), d.id());
        for cell in [a, b, c, d] {
            ledger.insert_cell(cell).unwrap();
        }

        // ACCEPT: each asset conserves. Executor boundary pre-flight is clean.
        let balanced = vec![(a_id, -10), (b_id, 10), (c_id, -5), (d_id, 5)];
        assert!(
            TurnExecutor::check_per_asset_conservation(&ledger, &balanced, &[]).is_ok(),
            "balanced multi-asset turn must pass the executor gate"
        );

        // And the SAME partition PROVES + VERIFIES through the committed per-asset
        // AIR (the in-AIR realization the light client runs).
        let mut block = BlockConservation::new();
        for (cell, delta) in &balanced {
            let asset = TurnExecutor::asset_class_for_cell(&ledger, cell);
            let credit = *delta >= 0;
            block.add_contribution(PerCellContribution {
                asset,
                net_delta_mag: BabyBear::new_canonical(delta.unsigned_abs() as u32),
                net_delta_sign: if credit {
                    BabyBear::ZERO
                } else {
                    BabyBear::ONE
                },
            });
        }
        block
            .prove_and_verify()
            .expect("balanced multi-asset block must prove+verify per asset in-AIR");

        // REJECT: cross-asset borrow (asset 7 short −10, asset 8 long +10).
        let forged = vec![(a_id, -10), (c_id, 10)];
        match TurnExecutor::check_per_asset_conservation(&ledger, &forged, &[]) {
            Err(AtomicTurnError::PerAssetConservationViolation { imbalance, .. }) => {
                assert!(imbalance == 10 || imbalance == -10);
            }
            other => panic!("cross-asset borrow must be rejected, got {:?}", other),
        }
    }
}
