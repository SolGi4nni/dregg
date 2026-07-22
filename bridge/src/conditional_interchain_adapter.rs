//! A fail-closed, statement-bound wrapper around [`InterchainAdapter`].
//!
//! The base adapter intentionally only decides the trust rung and carries a
//! `PortableActionBinding`.  Its former request builder accepted a caller-supplied
//! recipient and did not know which federation the current relayer served, which
//! permitted a proof for recipient A to be assembled into a request crediting B.
//! That builder has been removed from the public trait; this is now the sole
//! request-construction API for `InterchainAdapter` evidence.
//!
//! This module is the narrow closure boundary.  [`ConditionalInterchainAdapter`]
//! extracts the binding exactly once (avoiding a check/use race with a stateful
//! adapter) and admits a request only when:
//!
//! * both the nullifier and local federation are nonzero (Nomad-law defaults);
//! * the proof-bound destination equals the local federation;
//! * proof-bound nullifier, recipient, and amount equal the observed event; and
//! * the request is constructed from those checked values, never caller hints.
//!
//! The trust verdict remains the existing verified Lean decision reached through
//! `TrustRung::reached_consensus`.  This wrapper does not claim foreign-chain
//! finality; it prevents a valid finality verdict for one statement from being
//! replayed as authority for a different local credit.
//!
//! # Maturity
//!
//! The trait cutover is complete in this tree: `InterchainAdapter` exposes no
//! mint constructor, and the production Solana adapter caller routes through this
//! statement-bound API.  Other chain integrations must provide the same
//! `ExpectedCredit` and local-federation identity when they gain live callers.

use dregg_cell::{CellId, Nullifier};
use dregg_turn::BridgeMintRequest;

use crate::action_binding::PortableActionBinding;
use crate::interchain_adapter::{AdapterError, InterchainAdapter};

/// The exact foreign event the local relayer observed and intends to credit.
/// Every value is compared with the proof-bound [`PortableActionBinding`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExpectedCredit {
    pub nullifier: [u8; 32],
    pub recipient: CellId,
    pub amount: u64,
}

/// A statement mismatch detected before constructing a mint request.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConditionalAdapterError {
    /// The local routing identity is the uninitialized/default value.
    EmptyLocalFederation,
    /// The proof-bound destination names another federation.
    WrongDestinationFederation { expected: [u8; 32], found: [u8; 32] },
    /// The proof-bound nullifier differs from the observed event.
    NullifierMismatch,
    /// The proof-bound recipient differs from the cell about to be credited.
    RecipientMismatch,
    /// The proof-bound amount differs from the observed event.
    AmountMismatch,
    /// The underlying adapter refused the attestation (including zero nullifier).
    Adapter(AdapterError),
}

impl core::fmt::Display for ConditionalAdapterError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::EmptyLocalFederation => {
                write!(
                    f,
                    "zero/default local federation is not a routable destination"
                )
            }
            Self::WrongDestinationFederation { .. } => {
                write!(
                    f,
                    "proof-bound destination does not match the local federation"
                )
            }
            Self::NullifierMismatch => {
                write!(f, "proof-bound nullifier does not match the observed event")
            }
            Self::RecipientMismatch => {
                write!(f, "proof-bound recipient does not match the credited cell")
            }
            Self::AmountMismatch => {
                write!(f, "proof-bound amount does not match the observed event")
            }
            Self::Adapter(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for ConditionalAdapterError {}

/// A local-destination condition around any chain-specific adapter.
#[derive(Clone, Debug)]
pub struct ConditionalInterchainAdapter<A> {
    inner: A,
    local_federation: [u8; 32],
}

impl<A> ConditionalInterchainAdapter<A> {
    pub fn new(inner: A, local_federation: [u8; 32]) -> Self {
        Self {
            inner,
            local_federation,
        }
    }

    pub fn inner(&self) -> &A {
        &self.inner
    }

    pub fn local_federation(&self) -> [u8; 32] {
        self.local_federation
    }
}

impl<A: InterchainAdapter> ConditionalInterchainAdapter<A> {
    /// Build a mint request from one checked snapshot of the action binding.
    ///
    /// `to_action_binding` is deliberately called exactly once.  A wrapper that
    /// checked one result and then called `inner.into_mint_request` would ask a
    /// stateful/interior-mutable adapter for the binding a second time, creating
    /// a check/use seam.  Instead this method constructs the request directly
    /// from the already-checked snapshot and the existing verified trust verdict.
    pub fn into_mint_request(
        &self,
        attestation: &A::Attestation,
        actor: CellId,
        ledger_cell: CellId,
        expected: ExpectedCredit,
    ) -> Result<BridgeMintRequest, ConditionalAdapterError> {
        if self.local_federation == [0u8; 32] {
            return Err(ConditionalAdapterError::EmptyLocalFederation);
        }

        let binding: PortableActionBinding = self
            .inner
            .to_action_binding(attestation)
            .map_err(ConditionalAdapterError::Adapter)?;

        if binding.destination_federation != self.local_federation {
            return Err(ConditionalAdapterError::WrongDestinationFederation {
                expected: self.local_federation,
                found: binding.destination_federation,
            });
        }
        if binding.nullifier != expected.nullifier {
            return Err(ConditionalAdapterError::NullifierMismatch);
        }
        if binding.recipient != expected.recipient.0 {
            return Err(ConditionalAdapterError::RecipientMismatch);
        }
        if binding.amount != expected.amount {
            return Err(ConditionalAdapterError::AmountMismatch);
        }

        Ok(BridgeMintRequest {
            actor,
            ledger_cell,
            lock_nullifier: Nullifier(binding.nullifier),
            recipient: CellId(binding.recipient),
            amount: binding.amount,
            consensus_verified: self.inner.trust_rung(attestation).reached_consensus(),
        })
    }
}
