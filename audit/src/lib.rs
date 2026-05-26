//! `dregg-audit`: Verifiable token audit trail for the dregg ZK token system.
//!
//! This crate implements a privacy-preserving audit trail that proves token usage
//! history without revealing the full history to the auditor. It provides:
//!
//! - **Usage events**: Immutable records of token presentations for authorization.
//! - **Append-only audit log**: A Merkle-committed sequence of usage events.
//! - **Audit receipts**: Proofs issued to token holders confirming event recording.
//! - **Privacy-preserving proofs**:
//!   - `CountProof` — proves "token X was used exactly K times"
//!   - `RangeProof` — proves "all uses are within time range [T1, T2]"
//!   - `ConsistencyProof` — proves "log is append-only, no tampering"
//!   - `BudgetProof` — proves "token X has K remaining uses"
//! - **Budget enforcement**: Integrates audit with usage limits.
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────┐
//! │                    BudgetEnforcer                         │
//! │  ┌───────────────────────────────────────────────────┐  │
//! │  │                  AuditLog                          │  │
//! │  │  ┌─────────────────────────────────────────────┐  │  │
//! │  │  │          4-ary Merkle Tree                  │  │  │
//! │  │  │  ┌───┐ ┌───┐ ┌───┐ ┌───┐ ┌───┐           │  │  │
//! │  │  │  │ E │ │ E │ │ E │ │ E │ │...│  (events)  │  │  │
//! │  │  │  └───┘ └───┘ └───┘ └───┘ └───┘           │  │  │
//! │  │  └─────────────────────────────────────────────┘  │  │
//! │  └───────────────────────────────────────────────────┘  │
//! │                         │                                │
//! │                    append(event)                          │
//! │                         │                                │
//! │                         ▼                                │
//! │  ┌───────────────────────────────────────────────────┐  │
//! │  │               AuditReceipt                         │  │
//! │  │  event_hash + log_root + inclusion_proof           │  │
//! │  └───────────────────────────────────────────────────┘  │
//! └─────────────────────────────────────────────────────────┘
//!                           │
//!                    prove_*() methods
//!                           │
//!                           ▼
//! ┌─────────────────────────────────────────────────────────┐
//! │  CountProof │ RangeProof │ ConsistencyProof │ BudgetProof│
//! │  (privacy-preserving: auditor learns only the claimed    │
//! │   property, not the underlying event details)            │
//! └─────────────────────────────────────────────────────────┘
//! ```
//!
//! # Example
//!
//! ```rust
//! use dregg_audit::budget::{BudgetEnforcer, BudgetSpec};
//! use dregg_audit::event::UsageEvent;
//!
//! let token_id = [0x42; 32];
//! let mut enforcer = BudgetEnforcer::new(token_id, BudgetSpec::total(5));
//!
//! // Record a use.
//! let event = UsageEvent::new(token_id, 1000, [0xAA; 32], [0xBB; 32], 0);
//! let receipt = enforcer.record_use(event).unwrap();
//!
//! // Receipt proves inclusion.
//! assert!(receipt.inclusion_proof.verify(&receipt.log_root_after));
//!
//! // Prove count to an auditor.
//! let count_proof = enforcer.log_mut().prove_count(&token_id);
//! assert_eq!(count_proof.count, 1);
//! assert!(count_proof.verify());
//! ```

pub mod budget;
pub mod event;
pub mod log;
pub mod proofs;

#[cfg(test)]
mod tests;

// Re-export primary types at crate root.
pub use budget::{BudgetEnforcer, BudgetExhausted, BudgetSpec};
pub use event::{AuditReceipt, InclusionProof, UsageEvent};
pub use log::{AuditLog, LogSnapshot};
pub use proofs::{BudgetProof, ConsistencyProof, CountProof, LastUseProof, RangeProof};
