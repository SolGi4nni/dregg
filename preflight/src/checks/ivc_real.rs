//! THE ONE REAL TURN MINTER (and the shared honest whole-chain fold) for every
//! preflight IVC check.
//!
//! `mint_real_turn` mints a genuine rotated turn leg on the production
//! descriptor path (`dregg_turn::rotation_witness::mint_rotated_participant_leg`
//! — the SAME producer recipe `lightclient/src/bin/produce_history_envelope.rs`
//! ships), and `honest_chain_proof` folds a continuous 2-turn chain of those
//! legs through the REAL whole-chain recursive prover
//! (`dregg_circuit_prove::ivc_turn_chain::prove_turn_chain_recursive`).
//!
//! This module exists so there is exactly ONE minter: `checks::sovereign`,
//! `checks::composition`, `checks::backends`, and `checks::proofs` all drive
//! the same recipe. A per-file copy would drift into a MIRROR of the producer
//! path — the very thing the mock-IVC purge is killing.
//!
//! The honest fold is computed ONCE per process (`OnceLock`) and its byte
//! envelope + honest-setup VK anchor are shared: proving is the expensive leg,
//! and every consumer still runs the REAL `verify_whole_chain_proof_bytes` on
//! the REAL envelope. If the fold cannot be minted, the cached value is the
//! honest error and every dependent check FAILS CLOSED with it — there is no
//! mock to fall back to.

use std::sync::OnceLock;

use dregg_cell::{AuthRequired, Cell, Permissions};
use dregg_circuit_prove::ivc_turn_chain::{FinalizedTurn, RecursionVk, prove_turn_chain_recursive};
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_turn::rotation_witness::mint_rotated_participant_leg;

fn open_permissions() -> Permissions {
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

/// The transfer actor cell at `(balance, nonce)` with open permissions — the
/// before/after `Cell` the rotated producer-witness path runs over (the same
/// producer shape `lightclient/src/bin/produce_history_envelope.rs` ships).
fn ivc_producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

/// Mint ONE REAL finalized turn on the production descriptor path: the rotated
/// multi-table batch proof from `dregg_turn::rotation_witness`, self-verified at
/// mint. This is the SAME producer recipe the light-client history envelope uses
/// — no fabricated fold deltas, no synthetic chain.
pub(crate) fn mint_real_turn(
    balance: u64,
    nonce: u32,
    amount: u64,
) -> Result<FinalizedTurn, String> {
    use dregg_circuit::effect_vm::{CellState, Effect as VmEffect};

    let state = CellState::new(balance, nonce);
    let effects = vec![VmEffect::Transfer {
        amount,
        direction: 1,
    }];
    // The rotated transfer DEBIT: balance decreases by `amount`; the rotated
    // trace welds the nonce bump from the v1 sub-trace.
    let before_cell = ivc_producer_cell(balance as i64, nonce as u64);
    let after_cell = ivc_producer_cell((balance as i64) - (amount as i64), nonce as u64);
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let leg = mint_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        None,
    )
    .map_err(|e| format!("rotated turn leg failed to mint: {e}"))?;
    Ok(FinalizedTurn::new(DescriptorParticipant::rotated(leg)))
}

/// A REAL whole-chain proof over a REAL continuous 2-turn chain, ready to
/// verify: the wire byte envelope plus the honest-setup trust anchor (the VK
/// fingerprint of the fold's own root circuit).
pub(crate) struct HonestChainProof {
    /// Postcard bytes of the `WholeChainProofBytes` envelope.
    pub bytes: Vec<u8>,
    /// Honest-setup anchor extraction: the fold's own root-VK fingerprint.
    pub vk: RecursionVk,
    /// Number of finalized turns folded (2).
    pub num_turns: usize,
}

/// The shared honest fold: a continuous 2-turn chain (turn 1 = (1000, nonce 0)
/// -7-> 993; turn 2 starts exactly at (993, nonce 1) — the rotated trace bumps
/// the nonce by 1 per Transfer row, so the rotated state-commit anchors chain),
/// folded ONCE by `prove_turn_chain_recursive` and cached for the life of the
/// process. Fail-closed: a mint/fold failure is cached as the honest error and
/// every caller reports it.
pub(crate) fn honest_chain_proof() -> Result<&'static HonestChainProof, String> {
    static PROOF: OnceLock<Result<HonestChainProof, String>> = OnceLock::new();
    PROOF
        .get_or_init(build_honest_chain_proof)
        .as_ref()
        .map_err(Clone::clone)
}

fn build_honest_chain_proof() -> Result<HonestChainProof, String> {
    let step = 7u64;
    let turn1 = mint_real_turn(1_000, 0, step)?;
    let turn2 = mint_real_turn(1_000 - step, 1, step)?;
    let turns = vec![turn1, turn2];

    // THE REAL FOLD: one recursive whole-chain proof over both turns (per-turn
    // execution re-proven IN-CIRCUIT, temporal continuity bound at the 8-felt
    // anchors).
    let proof = prove_turn_chain_recursive(&turns)
        .map_err(|e| format!("real whole-chain recursive fold failed: {e}"))?;
    let vk = proof.root_vk_fingerprint();
    Ok(HonestChainProof {
        bytes: proof.to_bytes(),
        vk,
        num_turns: proof.num_turns,
    })
}
