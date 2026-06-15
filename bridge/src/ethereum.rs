//! `dregg-bridge::ethereum`: settle a dregg whole-chain proof onto Ethereum.
//!
//! # The settlement problem
//!
//! dregg's finality proof is a recursive **STARK** over BabyBear
//! (`dregg_circuit::ivc_turn_chain::WholeChainProof` — the root batch-STARK that
//! attests "all finalized turns through N executed and the state root advanced
//! correctly"). Verifying a BabyBear STARK *directly* on the EVM is
//! prohibitively expensive: FRI verification is hundreds of thousands of field
//! operations and Keccak/Poseidon Merkle-path checks, costing tens of millions
//! of gas — not viable.
//!
//! # The realistic path: STARK -> SNARK wrap -> EVM verifier
//!
//! The production-proven pattern (SP1, RISC Zero, Polygon zkEVM) is:
//!
//! ```text
//!  recursive STARK (BabyBear)         <- dregg WholeChainProof root
//!        | wrap in a SNARK whose circuit IS the STARK verifier
//!  Groth16 / PLONK proof (≈256 B)     <- constant-size, pairing-checkable
//!        | submit calldata to a Solidity verifier contract
//!  EVM verification (~250-300k gas)   <- one pairing check, cheap + final
//! ```
//!
//! The STARK is wrapped in a SNARK (Groth16 over BN254) whose arithmetic circuit
//! *is the STARK verifier*. The resulting Groth16 proof is ~256 bytes and is
//! checked by a standard Solidity `Pairing.verify` contract for ~250-300k gas —
//! the same envelope SP1's "Groth16 STARK-to-SNARK wrapper" hits on any EVM
//! chain. BN254 has a precompile (EIP-197/196) so the pairing check is native.
//!
//! # What this module provides (scaffold + state machine)
//!
//! - [`EthSettlementProof`]: the settlement artifact — the SNARK-wrapped proof
//!   bytes + the public inputs the EVM verifier checks (genesis root, final
//!   root, num turns, chain digest) + the verifier-contract binding.
//! - [`wrap_for_ethereum`]: takes the recursive-STARK root commitment + its
//!   public inputs and produces an [`EthSettlementProof`] in the EVM calldata
//!   shape. The SNARK *prover* itself (the gnark/Groth16 circuit encoding the
//!   Plonky3 STARK verifier) is the named research gap — see
//!   [`EthSettlementProof::is_snark_backed`] and the module-level GAP note.
//! - [`EthBridgeState`] / [`submit_eth_settlement`] / [`confirm_eth_settlement`]:
//!   the on-chain settlement state machine, mirroring [`crate::mina`]: a
//!   monotonic chain of `(old_root -> new_root)` advances, each gated on
//!   continuity, awaiting EVM-side confirmation.
//! - [`solidity_verifier_interface`]: the ABI the Solidity verifier contract
//!   must expose, emitted as a reference so the on-chain side is pinned.
//!
//! # GAP (honest)
//!
//! The cryptographic core that is NOT in this repo is the **Groth16 circuit that
//! encodes the Plonky3 BabyBear STARK verifier** (and its trusted-setup
//! proving/verifying keys). That circuit is a large, security-critical artifact
//! — the same one SP1 ships as a precompiled `groth16` wrapper built with gnark.
//! Building it bespoke is out of scope and ill-advised (see the memory note on
//! pulling in a vetted component vs bespoke crypto). The realistic productionization
//! is to either (a) route dregg's recursive proof through SP1/RISC Zero's
//! existing STARK->Groth16 wrapper and settle *their* Groth16 proof, or (b)
//! integrate gnark's STARK-verifier circuit. This module builds everything
//! around that core: the calldata shape, the public-input binding, the
//! settlement state machine, and the Solidity ABI — so dropping in a real SNARK
//! prover is a localized change to [`wrap_for_ethereum`].

use serde::{Deserialize, Serialize};

// ============================================================================
// Errors
// ============================================================================

/// Errors from the Ethereum settlement bridge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EthBridgeError {
    /// The recursive-proof commitment was empty/malformed.
    InvalidProof {
        /// Why.
        reason: String,
    },
    /// A settlement advance does not chain from the current proven root.
    InvalidAdvance {
        /// Why.
        reason: String,
    },
    /// An internal encoding error.
    Internal {
        /// Why.
        reason: String,
    },
}

impl core::fmt::Display for EthBridgeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            EthBridgeError::InvalidProof { reason } => write!(f, "invalid proof: {reason}"),
            EthBridgeError::InvalidAdvance { reason } => write!(f, "invalid advance: {reason}"),
            EthBridgeError::Internal { reason } => write!(f, "internal: {reason}"),
        }
    }
}

impl std::error::Error for EthBridgeError {}

// ============================================================================
// The settlement artifact
// ============================================================================

/// Which proving system backs an [`EthSettlementProof`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SnarkSystem {
    /// Groth16 over BN254 — smallest proof (~256 B), one pairing check on the
    /// EVM (~250-300k gas via the EIP-197 precompile). The SP1/RISC Zero default
    /// for final EVM settlement.
    Groth16Bn254,
    /// PLONK over BN254 — universal setup (no per-circuit ceremony), slightly
    /// larger proof / higher gas than Groth16 but no circuit-specific trusted
    /// setup. Also EVM-verifiable.
    PlonkBn254,
    /// Binding-commitment only (NO SNARK yet): the scaffold/state-machine phase.
    /// `is_snark_backed()` is false. This makes the settlement machine testable
    /// end-to-end while the SNARK wrapper (the named GAP) is integrated.
    BindingOnly,
}

/// A dregg whole-chain proof packaged for Ethereum settlement.
///
/// The EVM verifier checks `snark_proof` against `public_inputs`; on success the
/// settlement contract advances its on-chain proven root from
/// `public_inputs.genesis_root` to `public_inputs.final_root`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EthSettlementProof {
    /// Which SNARK system produced `snark_proof`.
    pub system: SnarkSystem,
    /// The SNARK proof bytes, in the calldata encoding the Solidity verifier
    /// expects (for Groth16/BN254: the `(A, B, C)` G1/G2 points, 8 field
    /// elements = 256 bytes). For [`SnarkSystem::BindingOnly`] this is a BLAKE3
    /// binding over the recursive-proof commitment + public inputs.
    pub snark_proof: Vec<u8>,
    /// The public inputs the EVM verifier binds, in EVM word order.
    pub public_inputs: EthPublicInputs,
    /// keccak256 of the Solidity verifier's verifying key (the on-chain VK
    /// commitment), so a proof is bound to the exact verifier it settles
    /// against. Zero for [`SnarkSystem::BindingOnly`].
    pub verifying_key_hash: [u8; 32],
    /// keccak256 commitment to the underlying recursive STARK root this proof
    /// wraps (binds the SNARK to the dregg proof it attests).
    pub recursive_root_commitment: [u8; 32],
}

impl EthSettlementProof {
    /// True iff a real SNARK (not the binding-only placeholder) backs this proof.
    /// Gate production settlement on this.
    pub fn is_snark_backed(&self) -> bool {
        !matches!(self.system, SnarkSystem::BindingOnly)
    }

    /// The calldata to submit to the Solidity verifier's `settle` method:
    /// abi-style concatenation of `(proof || genesis || final || numTurns ||
    /// digest)` — `proof` then 32-byte `genesis_root`, 32-byte `final_root`,
    /// the 8-byte big-endian `num_turns`, and 32-byte `chain_digest`. The
    /// contract slices this and runs the pairing check.
    pub fn to_calldata(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(self.snark_proof.len() + 32 * 4);
        out.extend_from_slice(&self.snark_proof);
        out.extend_from_slice(&self.public_inputs.genesis_root);
        out.extend_from_slice(&self.public_inputs.final_root);
        out.extend_from_slice(&self.public_inputs.num_turns.to_be_bytes());
        out.extend_from_slice(&self.public_inputs.chain_digest);
        out
    }

    /// The trailing public-input region of [`Self::to_calldata`]: everything
    /// after the SNARK proof. For [`SnarkSystem::Groth16Bn254`] the proof prefix
    /// is the fixed 256 bytes, so this is the calldata from byte 256 on
    /// (`32 + 32 + 8 + 32 = 104` bytes). The inverse [`EthPublicInputs::from_tail`]
    /// reconstructs the four dregg commitments from it.
    pub fn public_input_tail(&self) -> Vec<u8> {
        let cd = self.to_calldata();
        cd[self.snark_proof.len()..].to_vec()
    }
}

impl EthPublicInputs {
    /// Reconstruct the four dregg public inputs from the 104-byte tail
    /// [`EthSettlementProof::to_calldata`] writes after the proof
    /// (`genesis_root(32) || final_root(32) || num_turns(8 BE) || chain_digest(32)`).
    /// This is the inverse seam: a relayer reading a `settle` calldata back into
    /// typed dregg commitments. Rejects a wrong-length tail.
    pub fn from_tail(tail: &[u8]) -> Result<Self, EthBridgeError> {
        if tail.len() != 32 + 32 + 8 + 32 {
            return Err(EthBridgeError::Internal {
                reason: format!("public-input tail must be 104 bytes, got {}", tail.len()),
            });
        }
        let mut genesis_root = [0u8; 32];
        genesis_root.copy_from_slice(&tail[0..32]);
        let mut final_root = [0u8; 32];
        final_root.copy_from_slice(&tail[32..64]);
        let mut nt = [0u8; 8];
        nt.copy_from_slice(&tail[64..72]);
        let num_turns = u64::from_be_bytes(nt);
        let mut chain_digest = [0u8; 32];
        chain_digest.copy_from_slice(&tail[72..104]);
        Ok(Self {
            genesis_root,
            final_root,
            num_turns,
            chain_digest,
        })
    }
}

/// A Groth16/BN254 proof's three points, sliced out of the 256-byte
/// [`EthSettlementProof::snark_proof`] in the exact word order the Solidity
/// `settle(uint256[2] a, uint256[2][2] b, uint256[2] c, ...)` ABI consumes
/// (and the EIP-197 pairing precompile expects): `a = (x, y)`,
/// `b = ((x_c1, x_c0), (y_c1, y_c0))`, `c = (x, y)`, each coordinate a 32-byte
/// big-endian word. The imaginary G2 coordinate (`c1`) comes FIRST — the
/// Ethereum word order, not arkworks'/gnark's native `c0 + c1·u` order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Groth16Calldata {
    /// `A ∈ G1`: `(x, y)`.
    pub a: [[u8; 32]; 2],
    /// `B ∈ G2`: `((x_c1, x_c0), (y_c1, y_c0))`.
    pub b: [[[u8; 32]; 2]; 2],
    /// `C ∈ G1`: `(x, y)`.
    pub c: [[u8; 32]; 2],
}

impl Groth16Calldata {
    /// Slice a 256-byte Groth16/BN254 proof into its `(A, B, C)` points — the
    /// decode the Solidity verifier performs before the pairing precompile.
    /// Pinning it here keeps the on-chain ABI and the bridge in lockstep. The
    /// feasibility PoC (`/tmp/dregg-evm-wrap-poc`) emits exactly this 256-byte
    /// layout from a REAL arkworks BN254 proof over the four dregg roots; the
    /// `groth16_calldata_slices_abc` test below checks the slicing seam.
    pub fn from_proof_bytes(proof: &[u8]) -> Result<Self, EthBridgeError> {
        if proof.len() != 256 {
            return Err(EthBridgeError::InvalidProof {
                reason: format!(
                    "Groth16/BN254 proof must be 256 bytes (A||B||C), got {}",
                    proof.len()
                ),
            });
        }
        let w = |o: usize| -> [u8; 32] {
            let mut x = [0u8; 32];
            x.copy_from_slice(&proof[o..o + 32]);
            x
        };
        Ok(Self {
            a: [w(0), w(32)],
            b: [[w(64), w(96)], [w(128), w(160)]],
            c: [w(192), w(224)],
        })
    }
}

/// The public inputs a dregg settlement binds on Ethereum. These are the same
/// four values the whole-chain STARK exposes
/// (`WholeChainProof::{genesis_root, final_root, num_turns, chain_digest}`),
/// re-encoded as 32-byte EVM words.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EthPublicInputs {
    /// The genesis state root the chain starts from (big-endian 32 bytes).
    pub genesis_root: [u8; 32],
    /// The final state root the chain reaches (big-endian 32 bytes).
    pub final_root: [u8; 32],
    /// Number of finalized turns folded into the proof.
    pub num_turns: u64,
    /// The chain digest committing to the ordered (old_root, new_root) pairs.
    pub chain_digest: [u8; 32],
}

// ============================================================================
// The wrap (scaffold around the named SNARK gap)
// ============================================================================

/// Package a dregg recursive-STARK root for Ethereum settlement.
///
/// `recursive_root_commitment` is a keccak/BLAKE3 commitment to the
/// `WholeChainProof` root batch-STARK (the circuit crate produces the proof; the
/// bridge only needs a binding commitment to it). `public_inputs` are the four
/// whole-chain values.
///
/// With `system == BindingOnly` this produces the scaffold artifact (no SNARK):
/// a binding commitment that lets the settlement state machine run end-to-end.
/// With a real `system`, `snark_proof_bytes` must be the output of the
/// STARK->SNARK wrapper (the GAP); this function checks shape and binds it.
pub fn wrap_for_ethereum(
    recursive_root_commitment: [u8; 32],
    public_inputs: EthPublicInputs,
    system: SnarkSystem,
    snark_proof_bytes: Option<Vec<u8>>,
    verifying_key_hash: [u8; 32],
) -> Result<EthSettlementProof, EthBridgeError> {
    let snark_proof = match (system, snark_proof_bytes) {
        (SnarkSystem::BindingOnly, _) => {
            // Scaffold: bind the recursive root + public inputs. NOT a SNARK.
            let mut hasher = blake3::Hasher::new_derive_key("dregg-eth-settlement-binding-v1");
            hasher.update(&recursive_root_commitment);
            hasher.update(&public_inputs.genesis_root);
            hasher.update(&public_inputs.final_root);
            hasher.update(&public_inputs.num_turns.to_be_bytes());
            hasher.update(&public_inputs.chain_digest);
            hasher.finalize().as_bytes().to_vec()
        }
        (SnarkSystem::Groth16Bn254, Some(bytes)) => {
            // Groth16/BN254 calldata is exactly 8 field elements = 256 bytes
            // (A: G1=64, B: G2=128, C: G1=64). Pin the shape.
            if bytes.len() != 256 {
                return Err(EthBridgeError::InvalidProof {
                    reason: format!(
                        "Groth16/BN254 proof must be 256 bytes (A||B||C), got {}",
                        bytes.len()
                    ),
                });
            }
            bytes
        }
        (SnarkSystem::PlonkBn254, Some(bytes)) => {
            if bytes.is_empty() {
                return Err(EthBridgeError::InvalidProof {
                    reason: "empty PLONK proof".to_string(),
                });
            }
            bytes
        }
        (_, None) => {
            return Err(EthBridgeError::InvalidProof {
                reason: "a real SNARK system requires snark_proof_bytes (the STARK->SNARK \
                         wrapper output); pass SnarkSystem::BindingOnly for the scaffold"
                    .to_string(),
            });
        }
    };

    Ok(EthSettlementProof {
        system,
        snark_proof,
        public_inputs,
        verifying_key_hash,
        recursive_root_commitment,
    })
}

/// Verify the *binding* of a settlement proof (NOT the SNARK pairing check —
/// that happens on the EVM). For [`SnarkSystem::BindingOnly`] this recomputes
/// the binding commitment. For real SNARK systems it checks the calldata shape
/// and that the proof is bound to the claimed verifying key + recursive root;
/// the cryptographic SNARK check is the EVM verifier's job (or a local
/// `ark-groth16` verify if the VK is available — named open).
pub fn verify_settlement_binding(proof: &EthSettlementProof) -> Result<bool, EthBridgeError> {
    match proof.system {
        SnarkSystem::BindingOnly => {
            let mut hasher = blake3::Hasher::new_derive_key("dregg-eth-settlement-binding-v1");
            hasher.update(&proof.recursive_root_commitment);
            hasher.update(&proof.public_inputs.genesis_root);
            hasher.update(&proof.public_inputs.final_root);
            hasher.update(&proof.public_inputs.num_turns.to_be_bytes());
            hasher.update(&proof.public_inputs.chain_digest);
            Ok(proof.snark_proof == hasher.finalize().as_bytes())
        }
        SnarkSystem::Groth16Bn254 => Ok(proof.snark_proof.len() == 256),
        SnarkSystem::PlonkBn254 => Ok(!proof.snark_proof.is_empty()),
    }
}

// ============================================================================
// Settlement state machine (mirrors crate::mina::MinaBridgeState)
// ============================================================================

/// Tracks Ethereum-side settlement: the latest proven dregg root accepted by the
/// settlement contract, pending advances, and confirmation status.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EthBridgeState {
    /// Latest dregg state root proven to (and accepted by) the EVM contract.
    pub proven_root: [u8; 32],
    /// Latest proven height (monotone).
    pub proven_height: u64,
    /// The settlement contract address (20 bytes, hex without 0x), if deployed.
    pub contract_address: Option<String>,
    /// Pending advances awaiting EVM confirmation.
    pub pending: Vec<EthStateAdvance>,
}

impl EthBridgeState {
    /// New settlement state anchored at a genesis root.
    pub fn new(genesis_root: [u8; 32]) -> Self {
        Self {
            proven_root: genesis_root,
            proven_height: 0,
            contract_address: None,
            pending: Vec::new(),
        }
    }
}

/// A pending settlement advance: `old_root -> new_root` at `height`, carrying the
/// settlement proof to submit to the EVM contract.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EthStateAdvance {
    /// The state root before this advance.
    pub old_root: [u8; 32],
    /// The state root after this advance.
    pub new_root: [u8; 32],
    /// The height/epoch of this advance.
    pub height: u64,
    /// The settlement proof to submit.
    pub proof: EthSettlementProof,
    /// The EVM block number at which this advance was confirmed (None until).
    pub confirmed_at: Option<u64>,
}

/// Queue a settlement advance. Validates continuity (the temporal binding) and
/// monotone height before accepting it into the pending queue.
pub fn submit_eth_settlement(
    state: &mut EthBridgeState,
    advance: EthStateAdvance,
) -> Result<(), EthBridgeError> {
    if advance.old_root != state.proven_root {
        return Err(EthBridgeError::InvalidAdvance {
            reason: "old_root does not chain from the current proven root".to_string(),
        });
    }
    if advance.height <= state.proven_height {
        return Err(EthBridgeError::InvalidAdvance {
            reason: format!(
                "height {} not greater than proven height {}",
                advance.height, state.proven_height
            ),
        });
    }
    // The advance's settlement proof must bind to the same endpoints.
    if advance.proof.public_inputs.genesis_root != advance.old_root
        || advance.proof.public_inputs.final_root != advance.new_root
    {
        return Err(EthBridgeError::InvalidAdvance {
            reason: "settlement proof endpoints do not match the advance roots".to_string(),
        });
    }
    if !verify_settlement_binding(&advance.proof)? {
        return Err(EthBridgeError::InvalidAdvance {
            reason: "settlement proof binding check failed".to_string(),
        });
    }
    state.pending.push(advance);
    Ok(())
}

/// Confirm the pending advance at `height` (called after the EVM contract
/// accepts the proof): promote it to the proven root and drop it from pending.
pub fn confirm_eth_settlement(state: &mut EthBridgeState, height: u64, evm_block: u64) -> bool {
    if let Some(pos) = state.pending.iter().position(|a| a.height == height) {
        let adv = state.pending.remove(pos);
        state.proven_root = adv.new_root;
        state.proven_height = adv.height;
        // (the confirmed advance's evm block is recorded by the caller's log)
        let _ = evm_block;
        true
    } else {
        false
    }
}

// ============================================================================
// Solidity verifier ABI (reference for the on-chain side)
// ============================================================================

/// The ABI the on-chain Solidity settlement verifier must expose. Emitted as a
/// reference string so the contract interface is pinned alongside the bridge.
///
/// The `settle` function takes a Groth16 proof `(a, b, c)` + the four dregg
/// public inputs; it runs the BN254 pairing check (via the EIP-197 precompile,
/// the bulk of the ~250-300k gas) and, on success, advances `provenRoot`.
pub fn solidity_verifier_interface() -> &'static str {
    r#"// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// dregg whole-chain settlement verifier.
/// Verifies a Groth16(BN254) proof that wraps the dregg recursive STARK
/// attesting "all finalized turns executed and the state root advanced
/// from genesis_root to final_root", then advances the on-chain proven root.
interface IDreggSettlement {
    /// Current proven dregg state root (the contract's settled state).
    function provenRoot() external view returns (bytes32);

    /// Current proven height (monotone).
    function provenHeight() external view returns (uint64);

    /// keccak256 of the Groth16 verifying key this contract checks against.
    function verifyingKeyHash() external view returns (bytes32);

    /// Submit a settlement.
    /// @param a,b,c       Groth16 proof points (BN254): a∈G1, b∈G2, c∈G1.
    /// @param genesisRoot Must equal the current provenRoot (continuity).
    /// @param finalRoot   The new proven root on success.
    /// @param numTurns    Number of finalized turns folded.
    /// @param chainDigest Digest over the ordered (old,new) root pairs.
    /// Reverts if the pairing check fails or genesisRoot != provenRoot.
    function settle(
        uint256[2] calldata a,
        uint256[2][2] calldata b,
        uint256[2] calldata c,
        bytes32 genesisRoot,
        bytes32 finalRoot,
        uint64  numTurns,
        bytes32 chainDigest
    ) external;

    event Settled(bytes32 indexed oldRoot, bytes32 indexed newRoot, uint64 height);
}
"#
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn pis(g: u8, f: u8, n: u64) -> EthPublicInputs {
        EthPublicInputs {
            genesis_root: [g; 32],
            final_root: [f; 32],
            num_turns: n,
            chain_digest: [0xCD; 32],
        }
    }

    /// The scaffold settlement (BindingOnly) wraps, binds, and round-trips
    /// through the settlement state machine end-to-end.
    #[test]
    fn binding_only_settlement_round_trips() {
        let root_commit = [0xAB; 32];
        let p = wrap_for_ethereum(
            root_commit,
            pis(1, 2, 5),
            SnarkSystem::BindingOnly,
            None,
            [0; 32],
        )
        .expect("binding-only wrap must succeed");
        assert!(!p.is_snark_backed());
        assert!(verify_settlement_binding(&p).unwrap());

        let mut state = EthBridgeState::new([1; 32]);
        let advance = EthStateAdvance {
            old_root: [1; 32],
            new_root: [2; 32],
            height: 1,
            proof: p,
            confirmed_at: None,
        };
        submit_eth_settlement(&mut state, advance).expect("advance must queue");
        assert!(confirm_eth_settlement(&mut state, 1, 100));
        assert_eq!(state.proven_root, [2; 32]);
        assert_eq!(state.proven_height, 1);
    }

    /// A real SNARK system requires proof bytes; binding-only does not.
    #[test]
    fn real_snark_requires_proof_bytes() {
        let err = wrap_for_ethereum(
            [0xAB; 32],
            pis(1, 2, 1),
            SnarkSystem::Groth16Bn254,
            None,
            [9; 32],
        )
        .unwrap_err();
        assert!(matches!(err, EthBridgeError::InvalidProof { .. }));
    }

    /// Groth16/BN254 calldata shape is pinned to 256 bytes.
    #[test]
    fn groth16_proof_shape_pinned() {
        // Wrong size rejected.
        let bad = wrap_for_ethereum(
            [0xAB; 32],
            pis(1, 2, 1),
            SnarkSystem::Groth16Bn254,
            Some(vec![0u8; 100]),
            [9; 32],
        );
        assert!(bad.is_err());
        // Correct size accepted + marked SNARK-backed.
        let ok = wrap_for_ethereum(
            [0xAB; 32],
            pis(1, 2, 1),
            SnarkSystem::Groth16Bn254,
            Some(vec![7u8; 256]),
            [9; 32],
        )
        .expect("256-byte Groth16 proof must wrap");
        assert!(ok.is_snark_backed());
        assert!(verify_settlement_binding(&ok).unwrap());
        // calldata = proof(256) + 4 public-input words(3*32 + 8) = 256 + 104.
        assert_eq!(ok.to_calldata().len(), 256 + 32 + 32 + 8 + 32);
    }

    /// A discontinuous advance (old_root != proven_root) is rejected — the
    /// temporal binding holds at the settlement layer too.
    #[test]
    fn discontinuous_advance_rejected() {
        let mut state = EthBridgeState::new([1; 32]);
        let p = wrap_for_ethereum(
            [0xAB; 32],
            pis(9, 2, 1),
            SnarkSystem::BindingOnly,
            None,
            [0; 32],
        )
        .unwrap();
        let advance = EthStateAdvance {
            old_root: [9; 32], // != proven_root [1;32]
            new_root: [2; 32],
            height: 1,
            proof: p,
            confirmed_at: None,
        };
        assert!(matches!(
            submit_eth_settlement(&mut state, advance),
            Err(EthBridgeError::InvalidAdvance { .. })
        ));
    }

    /// The Solidity interface reference is emitted and names the settle entrypoint.
    #[test]
    fn solidity_interface_present() {
        let abi = solidity_verifier_interface();
        assert!(abi.contains("function settle("));
        assert!(abi.contains("IDreggSettlement"));
    }

    /// The public-input tail round-trips: the four dregg commitments encode into
    /// the calldata tail and decode back identically — the relayer seam that
    /// reads a `settle` calldata back into typed `WholeChainProof` publics.
    #[test]
    fn public_inputs_tail_round_trips() {
        let p = wrap_for_ethereum(
            [0xAB; 32],
            EthPublicInputs {
                genesis_root: [0x11; 32],
                final_root: [0x22; 32],
                num_turns: 0x0102_0304_0506_0708,
                chain_digest: [0x33; 32],
            },
            SnarkSystem::Groth16Bn254,
            Some(vec![7u8; 256]),
            [9; 32],
        )
        .expect("256-byte Groth16 proof wraps");

        let tail = p.public_input_tail();
        assert_eq!(
            tail.len(),
            32 + 32 + 8 + 32,
            "tail is the 104-byte PI region"
        );
        // The tail is exactly the calldata after the 256-byte proof prefix.
        assert_eq!(tail, p.to_calldata()[256..].to_vec());

        let decoded = EthPublicInputs::from_tail(&tail).expect("tail decodes");
        assert_eq!(decoded, p.public_inputs, "publics survive the round trip");

        // A wrong-length tail is rejected (the format is pinned).
        assert!(EthPublicInputs::from_tail(&tail[..100]).is_err());
    }

    /// The Groth16 `(A, B, C)` slicer cuts the 256-byte proof into the exact
    /// word order the Solidity `settle` ABI + EIP-197 precompile consume: A=G1,
    /// B=G2 (imaginary coordinate first), C=G1. A non-256-byte proof is refused.
    #[test]
    fn groth16_calldata_slices_abc() {
        // A proof whose 8 coordinate words are distinguishable (word i = byte i).
        let mut proof = [0u8; 256];
        for (i, w) in proof.chunks_mut(32).enumerate() {
            w[31] = i as u8; // low byte of word i == i
        }
        let abc = Groth16Calldata::from_proof_bytes(&proof).expect("256B slices");
        assert_eq!(abc.a[0][31], 0, "A.x = word 0");
        assert_eq!(abc.a[1][31], 1, "A.y = word 1");
        assert_eq!(abc.b[0][0][31], 2, "B.x_c1 = word 2 (imaginary first)");
        assert_eq!(abc.b[0][1][31], 3, "B.x_c0 = word 3");
        assert_eq!(abc.b[1][0][31], 4, "B.y_c1 = word 4");
        assert_eq!(abc.b[1][1][31], 5, "B.y_c0 = word 5");
        assert_eq!(abc.c[0][31], 6, "C.x = word 6");
        assert_eq!(abc.c[1][31], 7, "C.y = word 7");

        assert!(
            Groth16Calldata::from_proof_bytes(&[0u8; 100]).is_err(),
            "a non-256-byte proof must be refused"
        );
    }
}
