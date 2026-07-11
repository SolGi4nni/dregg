//! `InterchainAdapter`: ONE abstraction over the four per-chain trust dials that
//! all feed the SAME committed mint gate ([`dregg_turn::TurnExecutor::bridge_mint_against_lock`]).
//!
//! Every inbound bridge leg answers two questions before it may mint:
//!
//! - **WHAT** is being minted — the `(nullifier, recipient, destination, amount)`
//!   tuple, carried by a [`PortableActionBinding`] whose IR-v2 proof algebraically
//!   attests those exact bytes.
//! - **HOW TRUSTED** is the evidence — a per-chain dial today spelled four
//!   different ways: Solana's [`LockProofTrust`], Ethereum's [`SnarkSystem`]
//!   (`is_snark_backed`), Midnight's optimistic-watchtower [`Verdict`], and a
//!   committee-finalized [`FinalizedAttestation`] quorum.
//!
//! This module collapses those four dials onto ONE ordinal, [`TrustRung`], with a
//! single fail-closed predicate, [`TrustRung::reached_consensus`], which becomes
//! [`BridgeMintRequest::consensus_verified`]. The gate itself is unchanged: it
//! refuses any request whose `consensus_verified` is `false`
//! ([`BridgeMintError::TrustTooLow`]). The point of the abstraction is that a
//! low-trust dial value (an RPC echo, an unresolved/fraudulent watchtower verdict,
//! a no-quorum committee) CANNOT reach `true` — the mapping is the only bridge
//! from a chain's raw evidence to the mint bool, and it is fail-closed by
//! construction.
//!
//! # The Nomad-law tooth
//!
//! The $190M Nomad hack accepted every unproven message because an uninitialized
//! slot defaulted to "accepted". Two independent teeth here refuse the
//! zero/default input BEFORE a mint request is ever built:
//!
//! 1. [`TrustRung::reached_consensus`] is `false` for [`TrustRung::Rpc`] — the
//!    rung a `StructureOnly` / bare-RPC dial maps to — and `false` for an
//!    unresolved watchtower or a zero-signer committee. The *default*/lowest-trust
//!    dial can never mint.
//! 2. [`InterchainAdapter::to_action_binding`] refuses a binding whose nullifier
//!    is the all-zero (uninitialized) value ([`AdapterError::EmptyAttestation`]),
//!    so an empty attestation cannot even produce a mint request.

use std::marker::PhantomData;

use dregg_cell::{CellId, Nullifier};
use dregg_turn::BridgeMintRequest;

use crate::action_binding::PortableActionBinding;
use crate::ethereum::SnarkSystem;
use crate::midnight_gateway::Verdict;
use crate::solana_trustless::LockProofTrust;

use dregg_lightclient::FinalizedAttestation;

/// The single trust ordinal every inbound bridge leg collapses onto.
///
/// The four per-chain dials ([`LockProofTrust`], [`SnarkSystem`], [`Verdict`],
/// [`FinalizedAttestation`]) each map to exactly one of these. Only three of the
/// four rungs can ever authorize a mint, and even those carry the resolution/quorum
/// bit so an *unresolved* watchtower or a *no-quorum* committee stays fail-closed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrustRung {
    /// A cryptographic proof verified: a Solana `ConsensusVerified` lock proof, or
    /// an Ethereum SNARK (`Groth16`/`PLONK`). The highest, trustless rung — always
    /// reaches consensus.
    Proof,
    /// An optimistic watchtower verdict (Midnight). `resolved_valid` is `true`
    /// only when the challenge window resolved in favor of validity
    /// ([`Verdict::Valid`]); a [`Verdict::Fraud`] leaves it `false`.
    OptimisticWatchtower {
        /// Whether the watchtower resolved the claim as VALID (no fraud).
        resolved_valid: bool,
    },
    /// A BFT committee quorum finalized the root (a [`FinalizedAttestation`]).
    /// `has_quorum` is `true` only when a supermajority of DISTINCT trusted-committee
    /// signers was counted; a zero-signer (default/empty) attestation stays `false`.
    Committee {
        /// Whether a supermajority quorum of trusted-committee signers was reached.
        has_quorum: bool,
    },
    /// A bare RPC echo / structure-only well-formedness check with no consensus
    /// (`StructureOnly`, `BindingOnly`). NEVER trustless — the fail-closed floor.
    Rpc,
}

impl TrustRung {
    /// THE single bool that becomes [`BridgeMintRequest::consensus_verified`].
    ///
    /// Fail-closed: `true` only for [`TrustRung::Proof`], a *resolved-valid*
    /// [`TrustRung::OptimisticWatchtower`], and a *quorum-reached*
    /// [`TrustRung::Committee`]. [`TrustRung::Rpc`] — and an unresolved watchtower
    /// or a no-quorum committee — map to `false`. This is the Nomad-law default:
    /// the lowest-trust / uninitialized dial value cannot mint.
    pub fn reached_consensus(&self) -> bool {
        match self {
            TrustRung::Proof => true,
            TrustRung::OptimisticWatchtower { resolved_valid } => *resolved_valid,
            TrustRung::Committee { has_quorum } => *has_quorum,
            TrustRung::Rpc => false,
        }
    }
}

// ── The four per-chain dials collapse onto the one ordinal ──────────────────

impl From<LockProofTrust> for TrustRung {
    /// Solana: `ConsensusVerified` (real stake-weighted ≥ 2/3 votes) is a
    /// [`TrustRung::Proof`]; `StructureOnly` (an unbacked RPC/structure echo) is
    /// the fail-closed [`TrustRung::Rpc`].
    fn from(t: LockProofTrust) -> Self {
        match t {
            LockProofTrust::ConsensusVerified => TrustRung::Proof,
            LockProofTrust::StructureOnly => TrustRung::Rpc,
        }
    }
}

impl From<SnarkSystem> for TrustRung {
    /// Ethereum: a real SNARK (`Groth16Bn254`/`PlonkBn254`, i.e. `is_snark_backed`)
    /// is a [`TrustRung::Proof`]; the `BindingOnly` scaffold (no SNARK yet) is the
    /// fail-closed [`TrustRung::Rpc`].
    fn from(s: SnarkSystem) -> Self {
        match s {
            SnarkSystem::Groth16Bn254 | SnarkSystem::PlonkBn254 => TrustRung::Proof,
            SnarkSystem::BindingOnly => TrustRung::Rpc,
        }
    }
}

impl From<&Verdict> for TrustRung {
    /// Midnight: a watchtower [`Verdict::Valid`] resolves the optimistic claim as
    /// sound ([`TrustRung::OptimisticWatchtower`] with `resolved_valid = true`); a
    /// [`Verdict::Fraud`] leaves `resolved_valid = false` — fail-closed.
    fn from(v: &Verdict) -> Self {
        TrustRung::OptimisticWatchtower {
            resolved_valid: matches!(v, Verdict::Valid { .. }),
        }
    }
}

impl From<&FinalizedAttestation> for TrustRung {
    /// Committee. PROVENANCE ASSUMPTION (a named seam, not a re-derived check):
    /// the `≥2n/3+1` supermajority is enforced by `verify_finalized_history`,
    /// which is the ONLY sound producer of a `FinalizedAttestation`. This
    /// conversion does NOT re-derive the threshold — `FinalizedAttestation`
    /// carries no committee-size field, so it cannot. It reads `quorum_signers`
    /// only as a fail-closed guard: a defensively/zero-constructed attestation
    /// maps to `has_quorum = false`. Callers MUST obtain the attestation from the
    /// verified light-client path, never hand-construct one.
    fn from(a: &FinalizedAttestation) -> Self {
        TrustRung::Committee {
            has_quorum: a.quorum_signers > 0,
        }
    }
}

/// A per-chain dial that answers "how trusted is this evidence?" as one [`TrustRung`].
///
/// Implemented for all four existing dials, so [`DialAdapter`] can treat any inbound
/// leg uniformly. This is the unification: the executor's mint gate no longer knows
/// which chain an event came from — only its rung.
pub trait TrustDial {
    /// The trust rung this dial value collapses to.
    fn rung(&self) -> TrustRung;
}

impl TrustDial for LockProofTrust {
    fn rung(&self) -> TrustRung {
        (*self).into()
    }
}

impl TrustDial for SnarkSystem {
    fn rung(&self) -> TrustRung {
        (*self).into()
    }
}

impl TrustDial for Verdict {
    fn rung(&self) -> TrustRung {
        self.into()
    }
}

impl TrustDial for FinalizedAttestation {
    fn rung(&self) -> TrustRung {
        self.into()
    }
}

/// Why an attestation could not be turned into a committed mint request.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdapterError {
    /// The attestation carries an all-zero (uninitialized/default) nullifier — the
    /// Nomad-law reject. An empty attestation must never produce a mint request.
    EmptyAttestation,
    /// The attestation's binding was otherwise unusable (chain-specific decode).
    Unbindable(String),
}

impl core::fmt::Display for AdapterError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            AdapterError::EmptyAttestation => write!(
                f,
                "empty/default attestation (all-zero nullifier) refused before minting (Nomad-law)"
            ),
            AdapterError::Unbindable(why) => write!(f, "attestation could not be bound: {why}"),
        }
    }
}

impl std::error::Error for AdapterError {}

/// The single abstraction every inbound bridge leg implements.
///
/// An adapter turns a chain-specific `Attestation` into (a) its [`TrustRung`] and
/// (b) a [`PortableActionBinding`], then the provided [`InterchainAdapter::into_mint_request`]
/// assembles the committed [`BridgeMintRequest`] with
/// `consensus_verified = trust_rung(att).reached_consensus()`. Because that bool is
/// derived solely from the rung, a low-trust attestation CANNOT set it `true`.
pub trait InterchainAdapter {
    /// The chain-specific attestation this adapter consumes.
    type Attestation;

    /// The trust rung this attestation reaches.
    fn trust_rung(&self, att: &Self::Attestation) -> TrustRung;

    /// The `(nullifier, recipient, destination, amount)` binding this attestation
    /// carries. MUST refuse an all-zero/uninitialized binding
    /// ([`AdapterError::EmptyAttestation`]) — the Nomad-law tooth.
    fn to_action_binding(
        &self,
        att: &Self::Attestation,
    ) -> Result<PortableActionBinding, AdapterError>;

    /// Assemble the committed mint request. `consensus_verified` is
    /// [`TrustRung::reached_consensus`] of [`Self::trust_rung`] — NEVER a
    /// caller-supplied bool — and `lock_nullifier` is taken from the binding, so a
    /// low-trust or empty attestation cannot authorize a mint.
    ///
    /// `actor`, `ledger_cell`, and `recipient` are the executor-side cells the
    /// relayer already holds (the mint-cap bearer, the committed mirror-ledger, and
    /// the credited dregg cell); the amount comes from the attested binding.
    ///
    /// CALLER RESPONSIBILITY (named seam): the binding's `destination_federation`
    /// is NOT checked here — the chain-agnostic adapter does not know which
    /// federation it serves. The relayer MUST verify
    /// `binding.destination_federation` matches this node before minting, so a
    /// binding addressed to a different federation is not credited here. (Wiring
    /// this into the relayers is a followup; see HORIZONLOG.)
    fn into_mint_request(
        &self,
        att: &Self::Attestation,
        actor: CellId,
        ledger_cell: CellId,
        recipient: CellId,
    ) -> Result<BridgeMintRequest, AdapterError> {
        let binding = self.to_action_binding(att)?;
        // Defence in depth: the binding refuses a zero nullifier, but re-check here
        // so no path can build a request keyed on the uninitialized default.
        if binding.nullifier == [0u8; 32] {
            return Err(AdapterError::EmptyAttestation);
        }
        let consensus_verified = self.trust_rung(att).reached_consensus();
        Ok(BridgeMintRequest {
            actor,
            ledger_cell,
            lock_nullifier: Nullifier(binding.nullifier),
            recipient,
            amount: binding.amount,
            consensus_verified,
        })
    }
}

/// A chain-agnostic attestation: the WHAT ([`PortableActionBinding`]) bundled with
/// the HOW-TRUSTED (any [`TrustDial`]).
///
/// This is the wire an off-chain relayer produces once it has (a) observed a lock /
/// deposit / payment and built its binding, and (b) run its chain's verify to obtain
/// a dial value.
#[derive(Clone, Debug)]
pub struct ChainAttestation<D: TrustDial> {
    /// The typed `(nullifier, recipient, destination, amount)` binding + its proof.
    pub binding: PortableActionBinding,
    /// The chain's raw trust dial (e.g. [`LockProofTrust`], [`SnarkSystem`], …).
    pub dial: D,
}

/// The one adapter that serves EVERY chain, parameterized by its dial type.
///
/// `DialAdapter::<LockProofTrust>` is the Solana leg, `DialAdapter::<SnarkSystem>`
/// the Ethereum leg, `DialAdapter::<Verdict>` the Midnight leg, and
/// `DialAdapter::<FinalizedAttestation>` the committee leg — all sharing the one
/// fail-closed [`InterchainAdapter::into_mint_request`].
#[derive(Clone, Copy, Debug, Default)]
pub struct DialAdapter<D: TrustDial>(PhantomData<D>);

impl<D: TrustDial> DialAdapter<D> {
    /// A fresh adapter for dial type `D`.
    pub fn new() -> Self {
        DialAdapter(PhantomData)
    }
}

impl<D: TrustDial> InterchainAdapter for DialAdapter<D> {
    type Attestation = ChainAttestation<D>;

    fn trust_rung(&self, att: &Self::Attestation) -> TrustRung {
        att.dial.rung()
    }

    fn to_action_binding(
        &self,
        att: &Self::Attestation,
    ) -> Result<PortableActionBinding, AdapterError> {
        // Nomad-law: an all-zero (uninitialized/default) nullifier is refused here,
        // before any mint request can be built from it.
        if att.binding.nullifier == [0u8; 32] {
            return Err(AdapterError::EmptyAttestation);
        }
        Ok(att.binding.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::field::BabyBear;
    use dregg_circuit_prove::ivc_turn_chain::{SEG_ANCHOR_WIDTH, SEG_DIGEST_WIDTH};
    use dregg_lightclient::AttestedHistory;

    fn cid(seed: u8) -> CellId {
        CellId([seed; 32])
    }

    /// A NON-empty binding (nonzero nullifier + amount). We do NOT call the real
    /// STARK prover here (that needs a full witness); the adapter's decision logic
    /// reads only the plaintext limbs, so a binding with empty `proof_bytes` is a
    /// faithful fixture for the trust/gate decision under test.
    fn nonzero_binding(amount: u64) -> PortableActionBinding {
        PortableActionBinding {
            nullifier: [0x11u8; 32],
            recipient: [0x22u8; 32],
            destination_federation: [0x33u8; 32],
            amount,
            proof_bytes: Vec::new(),
        }
    }

    fn zero_binding() -> PortableActionBinding {
        PortableActionBinding {
            nullifier: [0u8; 32],
            recipient: [0u8; 32],
            destination_federation: [0u8; 32],
            amount: 0,
            proof_bytes: Vec::new(),
        }
    }

    fn committee_attestation(quorum_signers: usize) -> FinalizedAttestation {
        FinalizedAttestation {
            history: AttestedHistory {
                genesis_root: [BabyBear::ZERO; SEG_ANCHOR_WIDTH],
                final_root: [BabyBear::ZERO; SEG_ANCHOR_WIDTH],
                chain_digest: [BabyBear::ZERO; SEG_DIGEST_WIDTH],
                num_turns: 1,
            },
            finalized_root: BabyBear::ZERO,
            quorum_signers,
        }
    }

    // ── rung → bool: the fail-closed predicate itself ──────────────────────

    #[test]
    fn reached_consensus_is_fail_closed_per_rung() {
        assert!(TrustRung::Proof.reached_consensus());
        assert!(
            TrustRung::OptimisticWatchtower {
                resolved_valid: true
            }
            .reached_consensus()
        );
        assert!(TrustRung::Committee { has_quorum: true }.reached_consensus());

        // The false polarity of every non-Proof rung:
        assert!(!TrustRung::Rpc.reached_consensus());
        assert!(
            !TrustRung::OptimisticWatchtower {
                resolved_valid: false
            }
            .reached_consensus()
        );
        assert!(!TrustRung::Committee { has_quorum: false }.reached_consensus());
    }

    // ── the four dials collapse to the right rung ──────────────────────────

    #[test]
    fn four_dials_map_to_expected_rungs() {
        assert_eq!(
            TrustRung::from(LockProofTrust::ConsensusVerified),
            TrustRung::Proof
        );
        assert_eq!(
            TrustRung::from(LockProofTrust::StructureOnly),
            TrustRung::Rpc
        );

        assert_eq!(TrustRung::from(SnarkSystem::Groth16Bn254), TrustRung::Proof);
        assert_eq!(TrustRung::from(SnarkSystem::PlonkBn254), TrustRung::Proof);
        assert_eq!(TrustRung::from(SnarkSystem::BindingOnly), TrustRung::Rpc);

        assert_eq!(
            TrustRung::from(&Verdict::Valid {
                claim_hash: [9u8; 32]
            }),
            TrustRung::OptimisticWatchtower {
                resolved_valid: true
            }
        );
        assert_eq!(
            TrustRung::from(&Verdict::Fraud {
                claim_hash: [9u8; 32],
                reason: crate::midnight_verified::VerifiedBridgeError::NullifierMismatch,
            }),
            TrustRung::OptimisticWatchtower {
                resolved_valid: false
            }
        );

        assert_eq!(
            TrustRung::from(&committee_attestation(5)),
            TrustRung::Committee { has_quorum: true }
        );
        // Nomad default: a zero-signer committee attestation is NOT a quorum.
        assert_eq!(
            TrustRung::from(&committee_attestation(0)),
            TrustRung::Committee { has_quorum: false }
        );
    }

    // ── POLARITY 1 (accept): a Proof / quorum attestation mints ────────────

    #[test]
    fn proof_dial_yields_consensus_verified_true() {
        let adapter = DialAdapter::<LockProofTrust>::new();
        let att = ChainAttestation {
            binding: nonzero_binding(500),
            dial: LockProofTrust::ConsensusVerified,
        };
        let req = adapter
            .into_mint_request(&att, cid(2), cid(9), cid(1))
            .expect("a consensus-verified attestation builds a mint request");
        assert!(
            req.consensus_verified,
            "a Proof-rung attestation sets consensus_verified = true"
        );
        assert_eq!(req.lock_nullifier, Nullifier([0x11u8; 32]));
        assert_eq!(req.amount, 500);
    }

    #[test]
    fn committee_quorum_yields_consensus_verified_true() {
        let adapter = DialAdapter::<FinalizedAttestation>::new();
        let att = ChainAttestation {
            binding: nonzero_binding(700),
            dial: committee_attestation(4),
        };
        let req = adapter
            .into_mint_request(&att, cid(2), cid(9), cid(1))
            .expect("a quorum-finalized attestation builds a mint request");
        assert!(
            req.consensus_verified,
            "a committee quorum reaches consensus"
        );
    }

    // ── POLARITY 2 (fail-closed): low-trust / empty attestation cannot mint ─

    #[test]
    fn structure_only_rpc_yields_consensus_verified_false() {
        // THE fail-closed tooth: a StructureOnly / bare-RPC dial maps to Rpc, whose
        // reached_consensus() is false — the resulting request is refused by the
        // executor's TrustTooLow gate. A forged/MITM RPC that only reaches
        // StructureOnly CANNOT mint.
        let adapter = DialAdapter::<LockProofTrust>::new();
        let att = ChainAttestation {
            binding: nonzero_binding(500),
            dial: LockProofTrust::StructureOnly,
        };
        let req = adapter
            .into_mint_request(&att, cid(2), cid(9), cid(1))
            .expect("the request still BUILDS (the gate, not the adapter, refuses it)");
        assert!(
            !req.consensus_verified,
            "a StructureOnly/Rpc attestation sets consensus_verified = FALSE (fail-closed)"
        );
    }

    #[test]
    fn binding_only_snark_and_fraud_verdict_are_fail_closed() {
        // Ethereum BindingOnly scaffold: no SNARK yet → false.
        let eth = DialAdapter::<SnarkSystem>::new();
        let eth_att = ChainAttestation {
            binding: nonzero_binding(1),
            dial: SnarkSystem::BindingOnly,
        };
        assert!(
            !eth.into_mint_request(&eth_att, cid(2), cid(9), cid(1))
                .unwrap()
                .consensus_verified
        );

        // Midnight watchtower verdict of FRAUD → unresolved → false.
        let mid = DialAdapter::<Verdict>::new();
        let mid_att = ChainAttestation {
            binding: nonzero_binding(1),
            dial: Verdict::Fraud {
                claim_hash: [1u8; 32],
                reason: crate::midnight_verified::VerifiedBridgeError::NullifierMismatch,
            },
        };
        assert!(
            !mid.into_mint_request(&mid_att, cid(2), cid(9), cid(1))
                .unwrap()
                .consensus_verified
        );
    }

    #[test]
    fn empty_attestation_is_refused_before_minting() {
        // THE NOMAD LAW: an all-zero (uninitialized/default) attestation must not
        // mint. Even with the HIGHEST trust dial, the zero-nullifier binding is
        // refused before a request is built — no request keyed on the default slot
        // can exist.
        let adapter = DialAdapter::<LockProofTrust>::new();
        let att = ChainAttestation {
            binding: zero_binding(),
            dial: LockProofTrust::ConsensusVerified,
        };
        assert_eq!(
            adapter
                .to_action_binding(&att)
                .expect_err("a zero-nullifier binding is refused"),
            AdapterError::EmptyAttestation
        );
        assert_eq!(
            adapter
                .into_mint_request(&att, cid(2), cid(9), cid(1))
                .expect_err("no mint request is built from an empty attestation"),
            AdapterError::EmptyAttestation
        );
    }
}
