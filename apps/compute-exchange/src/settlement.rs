//! Atomic escrow-based settlement for compute exchange trades.
//!
//! Settlement creates a pair of escrows atomically:
//! - **Consumer escrow**: Locks payment, released to provider on proof of work done.
//! - **Provider escrow**: Locks SLA bond, released back to provider on completion OR
//!   forfeited to consumer on SLA violation.
//!
//! This ensures neither party can defect without losing their bond.

use pyana_app_framework::{CellId, EscrowCondition, EscrowRecord};
use serde::{Deserialize, Serialize};

// =============================================================================
// Types
// =============================================================================

/// Unique identifier for a settlement.
pub type SettlementId = [u8; 32];

/// A settlement tracking the atomic exchange between consumer and provider.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Settlement {
    /// Unique settlement ID.
    pub id: SettlementId,
    /// The consumer who is paying for compute.
    pub consumer: CellId,
    /// The provider delivering compute.
    pub provider: CellId,
    /// The offering being fulfilled.
    pub offering_id: [u8; 32],
    /// The order being settled.
    pub order_id: [u8; 32],
    /// Payment amount escrowed by the consumer.
    pub payment_amount: u64,
    /// SLA bond amount escrowed by the provider.
    pub sla_bond_amount: u64,
    /// Hours of compute being delivered.
    pub compute_hours: u64,
    /// ID of the consumer's payment escrow.
    pub payment_escrow_id: [u8; 32],
    /// ID of the provider's SLA bond escrow.
    pub sla_bond_escrow_id: [u8; 32],
    /// Block height at which the settlement times out (enables refund).
    pub timeout_height: u64,
    /// Current settlement status.
    pub status: SettlementStatus,
    /// Block height when this settlement was created.
    pub created_at: u64,
}

/// Settlement lifecycle status.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SettlementStatus {
    /// Escrows are created, compute is in progress.
    Active,
    /// Provider has submitted proof of work completion.
    Completed,
    /// Settlement is under dispute.
    Disputed,
    /// Consumer received refund (provider didn't deliver).
    Refunded,
}

/// A dispute against a settlement.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Dispute {
    /// The settlement being disputed.
    pub settlement_id: SettlementId,
    /// Who initiated the dispute.
    pub initiator: CellId,
    /// Reason for the dispute.
    pub reason: String,
    /// Current dispute status.
    pub status: DisputeStatus,
    /// Block height when the dispute was filed.
    pub filed_at: u64,
}

/// Dispute resolution status.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DisputeStatus {
    /// Dispute is open, awaiting resolution.
    Open,
    /// Provider proved delivery via ReleaseEscrow with proof.
    ResolvedForProvider,
    /// Consumer receives refund (provider failed to prove delivery).
    ResolvedForConsumer,
}

// =============================================================================
// Settlement creation
// =============================================================================

/// Compute a settlement ID from its parameters.
pub fn compute_settlement_id(
    consumer: &CellId,
    provider: &CellId,
    order_id: &[u8; 32],
    created_at: u64,
) -> SettlementId {
    let mut hasher = blake3::Hasher::new_derive_key("compute-exchange-settlement-v1");
    hasher.update(consumer.as_bytes());
    hasher.update(provider.as_bytes());
    hasher.update(order_id);
    hasher.update(&created_at.to_le_bytes());
    *hasher.finalize().as_bytes()
}

/// Compute an escrow ID from settlement + role.
pub fn compute_escrow_id(settlement_id: &SettlementId, role: &str) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("compute-exchange-escrow-v1");
    hasher.update(settlement_id);
    hasher.update(role.as_bytes());
    *hasher.finalize().as_bytes()
}

/// Create the pair of escrow records for a settlement.
///
/// Returns (payment_escrow, sla_bond_escrow) with their conditions:
/// - Payment escrow: released to provider when ProofPresented (proof of compute delivery).
/// - SLA bond escrow: released back to provider when SignedByAll (consumer signs off),
///   or forfeited to consumer on timeout.
pub fn create_settlement_escrows(
    consumer: &CellId,
    provider: &CellId,
    payment_amount: u64,
    sla_bond_amount: u64,
    timeout_height: u64,
    settlement_id: &SettlementId,
) -> (EscrowRecord, [u8; 32], EscrowRecord, [u8; 32]) {
    let payment_escrow_id = compute_escrow_id(settlement_id, "payment");
    let sla_bond_escrow_id = compute_escrow_id(settlement_id, "sla_bond");

    // Payment escrow: consumer locks payment, provider claims with proof of delivery.
    let payment_vk = compute_delivery_verification_key(settlement_id);
    let payment_escrow = EscrowRecord {
        creator: *consumer,
        recipient: *provider,
        amount: payment_amount,
        condition: EscrowCondition::ProofPresented {
            verification_key: payment_vk,
        },
        timeout_height,
        resolved: false,
    };

    // SLA bond escrow: provider locks bond, gets it back on successful completion.
    // Released when both parties sign (consumer acknowledges delivery).
    let sla_bond_escrow = EscrowRecord {
        creator: *provider,
        recipient: *consumer, // consumer gets bond if provider fails
        amount: sla_bond_amount,
        condition: EscrowCondition::SignedByAll {
            signers: vec![*consumer.as_bytes(), *provider.as_bytes()],
        },
        timeout_height,
        resolved: false,
    };

    (
        payment_escrow,
        payment_escrow_id,
        sla_bond_escrow,
        sla_bond_escrow_id,
    )
}

/// Derive a verification key for delivery proofs within a settlement.
///
/// The provider must generate a proof that verifies against this key to claim payment.
pub fn compute_delivery_verification_key(settlement_id: &SettlementId) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("compute-exchange-delivery-vk-v1");
    hasher.update(settlement_id);
    *hasher.finalize().as_bytes()
}

/// Build the `Effect::CreateEscrow` for the consumer's payment.
pub fn build_payment_escrow_effect(
    consumer: &CellId,
    provider: &CellId,
    amount: u64,
    timeout_height: u64,
    escrow_id: [u8; 32],
    settlement_id: &SettlementId,
) -> pyana_turn::Effect {
    let vk = compute_delivery_verification_key(settlement_id);
    pyana_turn::Effect::CreateEscrow {
        cell: *consumer,
        recipient: *provider,
        amount,
        condition: EscrowCondition::ProofPresented {
            verification_key: vk,
        },
        timeout_height,
        escrow_id,
    }
}

/// Build the `Effect::CreateEscrow` for the provider's SLA bond.
pub fn build_sla_bond_escrow_effect(
    consumer: &CellId,
    provider: &CellId,
    amount: u64,
    timeout_height: u64,
    escrow_id: [u8; 32],
) -> pyana_turn::Effect {
    pyana_turn::Effect::CreateEscrow {
        cell: *provider,
        recipient: *consumer,
        amount,
        condition: EscrowCondition::SignedByAll {
            signers: vec![*consumer.as_bytes(), *provider.as_bytes()],
        },
        timeout_height,
        escrow_id,
    }
}

/// Build an `Effect::ReleaseEscrow` for when the provider proves delivery.
pub fn build_release_escrow_effect(escrow_id: [u8; 32], proof: Vec<u8>) -> pyana_turn::Effect {
    pyana_turn::Effect::ReleaseEscrow {
        escrow_id,
        proof: Some(proof),
    }
}

/// Build an `Effect::RefundEscrow` for when timeout passes without delivery.
pub fn build_refund_escrow_effect(escrow_id: [u8; 32]) -> pyana_turn::Effect {
    pyana_turn::Effect::RefundEscrow { escrow_id }
}

/// SLA bond is typically 10% of the payment amount.
pub const SLA_BOND_PERCENTAGE: u64 = 10;

/// Default timeout: 100 blocks after settlement creation.
pub const DEFAULT_TIMEOUT_BLOCKS: u64 = 100;
