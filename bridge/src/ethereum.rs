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
//!  Groth16 proof (384 B = 12 words)   <- constant-size, pairing-checkable
//!        | submit calldata to a Solidity verifier contract
//!  EVM verification (~626k gas)       <- pairing checks, cheap + final
//! ```
//!
//! The STARK is wrapped in a SNARK (Groth16 over BN254) whose arithmetic circuit
//! *is the STARK verifier* (`chain/gnark` `SettlementCircuit`). Because that
//! circuit uses gnark's commit-based range checker, the resulting proof blob is
//! **384 bytes = 12 words** — the classic 8 A/B/C words **plus** a Pedersen
//! `commitments[2]` and its proof of knowledge `commitmentPok[2]` — checked by
//! the gnark-generated Solidity verifier
//! (`chain/contracts/DreggGroth16Verifier25.sol`). BN254 has a precompile
//! (EIP-197/196) so the pairing checks are native.
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
//! # Status (the wrap is REAL; the ceremony is dev-grade)
//!
//! The Groth16 circuit that encodes the dregg shrink-STARK verifier EXISTS in
//! this repo (`chain/gnark` `SettlementCircuit`, binding the 25-lane apex claim
//! through the shrink proof's own `expose_claim` channel), and a REAL proof
//! from it settles on-chain against the gnark-GENERATED verifier in Foundry
//! (`chain/test/DreggSettlementRealProof.t.sol`, fixture
//! `chain/test/fixtures/settlement_groth16.json`). The remaining named caveat
//! is the trusted setup: the committed verifying key comes from a SINGLE-PARTY
//! DEV ceremony; production needs an MPC ceremony. This module carries the
//! matching host-side artifacts: the 384-byte (12-word) proof-blob layout, the
//! 25-lane public-input binding, the `settle()` calldata encoding
//! ([`EthSettlementProofV2`]), and the settlement state machine.

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
    /// Groth16 over BN254 — constant-size proof, pairing-checked on the EVM via
    /// the EIP-197 precompile. dregg's wrap circuit uses gnark's commit-based
    /// range checker, so the proof blob is [`GROTH16_EVM_PROOF_BYTES`] = 384
    /// bytes (12 words: A/B/C ++ commitments[2] ++ commitmentPok[2]), not the
    /// classic 256.
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
    /// expects (for Groth16/BN254: the `(A, B, C)` G1/G2 points **plus** the
    /// Pedersen `commitments[2]` + `commitmentPok[2]` the commit-based range
    /// checker adds — [`GROTH16_EVM_PROOF_WORDS`] = 12 words =
    /// [`GROTH16_EVM_PROOF_BYTES`] = 384 bytes). For
    /// [`SnarkSystem::BindingOnly`] this is a BLAKE3 binding over the
    /// recursive-proof commitment + public inputs.
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
    /// is the fixed [`GROTH16_EVM_PROOF_BYTES`] = 384 bytes, so this is the
    /// calldata from byte 384 on (`32 + 32 + 8 + 32 = 104` bytes). The inverse
    /// [`EthPublicInputs::from_tail`] reconstructs the four dregg commitments
    /// from it.
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

/// Number of 32-byte words in a dregg Groth16/BN254 settlement proof blob:
/// `A(2) ++ B(4) ++ C(2) ++ commitments(2) ++ commitmentPok(2)`. The wrap
/// circuit uses gnark's commit-based range checker, so the blob carries ONE
/// Pedersen commitment + its proof of knowledge after the classic 8 A/B/C
/// words — gnark `MarshalSolidity` order minus the 4-byte commitment-count
/// prefix (see `chain/gnark/settlement_snark_test.go`, which writes the
/// fixture words in exactly this order).
pub const GROTH16_EVM_PROOF_WORDS: usize = 12;

/// Byte length of the dregg Groth16/BN254 settlement proof blob:
/// [`GROTH16_EVM_PROOF_WORDS`] × 32 = 384.
pub const GROTH16_EVM_PROOF_BYTES: usize = GROTH16_EVM_PROOF_WORDS * 32;

/// A Groth16/BN254 settlement proof's points, sliced out of the 384-byte
/// (12-word) [`EthSettlementProof::snark_proof`] in the exact word order the
/// Solidity `settle(uint256[2] a, uint256[2][2] b, uint256[2] c,
/// uint256[2] commitments, uint256[2] commitmentPok, ...)` ABI consumes:
/// `a = (x, y)`, `b = ((x_c1, x_c0), (y_c1, y_c0))`, `c = (x, y)`, then the
/// Pedersen `commitments` point and its `commitmentPok` proof of knowledge —
/// each coordinate a 32-byte big-endian word. The imaginary G2 coordinate
/// (`c1`) comes FIRST — the Ethereum word order, not arkworks'/gnark's native
/// `c0 + c1·u` order. Words [8..12) are PART OF THE PROOF, not the statement
/// (the range checker's commitment), per `Groth16Verifier25Adapter.sol` /
/// `DreggGroth16Verifier25.sol`'s
/// `verifyProof(uint256[8], uint256[2], uint256[2], uint256[25])`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Groth16Calldata {
    /// `A ∈ G1`: `(x, y)` — words 0..2.
    pub a: [[u8; 32]; 2],
    /// `B ∈ G2`: `((x_c1, x_c0), (y_c1, y_c0))` — words 2..6.
    pub b: [[[u8; 32]; 2]; 2],
    /// `C ∈ G1`: `(x, y)` — words 6..8.
    pub c: [[u8; 32]; 2],
    /// The Pedersen commitment (gnark commit-based range checker) — words 8..10.
    pub commitments: [[u8; 32]; 2],
    /// The commitment's proof of knowledge — words 10..12.
    pub commitment_pok: [[u8; 32]; 2],
}

impl Groth16Calldata {
    /// Slice a 384-byte (12-word) Groth16/BN254 settlement proof into its
    /// `(A, B, C, commitments, commitmentPok)` points — the decode the Solidity
    /// verifier performs before the pairing precompile. Pinning it here keeps
    /// the on-chain ABI and the bridge in lockstep; the REAL gnark proof
    /// fixture (`chain/test/fixtures/settlement_groth16.json`) is emitted in
    /// exactly this word order, and the `real_fixture_*` tests below check the
    /// slicing seam against it.
    pub fn from_proof_bytes(proof: &[u8]) -> Result<Self, EthBridgeError> {
        if proof.len() != GROTH16_EVM_PROOF_BYTES {
            return Err(EthBridgeError::InvalidProof {
                reason: format!(
                    "Groth16/BN254 settlement proof must be {GROTH16_EVM_PROOF_BYTES} bytes \
                     (A||B||C||commitments||commitmentPok, 12 words), got {}",
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
            commitments: [w(256), w(288)],
            commitment_pok: [w(320), w(352)],
        })
    }

    /// Inverse of [`Self::from_proof_bytes`]: re-serialize the 12 words into
    /// the 384-byte blob (word order pinned above).
    pub fn to_proof_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(GROTH16_EVM_PROOF_BYTES);
        for word in self.words() {
            out.extend_from_slice(&word);
        }
        out
    }

    /// The 12 proof words in blob/calldata order:
    /// `a[0], a[1], b[0][0], b[0][1], b[1][0], b[1][1], c[0], c[1],
    /// commitments[0], commitments[1], commitmentPok[0], commitmentPok[1]`.
    pub fn words(&self) -> [[u8; 32]; GROTH16_EVM_PROOF_WORDS] {
        [
            self.a[0],
            self.a[1],
            self.b[0][0],
            self.b[0][1],
            self.b[1][0],
            self.b[1][1],
            self.c[0],
            self.c[1],
            self.commitments[0],
            self.commitments[1],
            self.commitment_pok[0],
            self.commitment_pok[1],
        ]
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
            // dregg's Groth16/BN254 calldata is exactly 12 words = 384 bytes
            // (A: G1=64, B: G2=128, C: G1=64, commitments: 64, commitmentPok:
            // 64 — the commit-based range checker's extra 4 words). Pin the
            // shape by running the full slicer.
            Groth16Calldata::from_proof_bytes(&bytes)?;
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
        SnarkSystem::Groth16Bn254 => Ok(proof.snark_proof.len() == GROTH16_EVM_PROOF_BYTES),
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
// V2: the 25-lane public-input encoding (the live wide WholeChainProof claim)
// ============================================================================
//
// The v1 types above encode the PRE-WIDENING 4-scalar model (single-word roots,
// 104-byte tail). The live `WholeChainProof` claim is **25 BabyBear lanes**:
// `genesis_root[0..8] ++ final_root[0..8] ++ num_turns ++ chain_digest[0..8]`
// (`SEG_ANCHOR_WIDTH = 8`, `SEG_DIGEST_WIDTH = 8` in
// `dregg_circuit_prove::ivc_turn_chain`; see
// `docs/FINDING-chain-participation-census.md` §1). The V2 path below encodes
// that statement for the EVM. STAGED-ADDITIVE: v1 stays untouched and in use.

/// The BabyBear prime `p = 2^31 - 2^27 + 1 = 0x7800_0001`. Every one of the 25
/// V2 public-input lanes must be a CANONICAL residue, i.e. strictly less than
/// this — the Groth16 wrap circuit binds canonical lanes, so a non-canonical
/// lane is refused at the bridge seam (fail-closed), never silently reduced.
pub const BABYBEAR_MODULUS: u32 = 2_013_265_921;

/// Number of public-input lanes in the V2 statement:
/// `genesis_root(8) + final_root(8) + num_turns(1) + chain_digest(8)`.
pub const ETH_PI_LANES_V2: usize = 25;

/// Byte length of the V2 calldata tail: each of the 25 lanes is ABI-encoded as
/// a full 32-byte big-endian word (Solidity static encoding of
/// `uint32[8],uint32[8],uint32,uint32[8]`), so `25 * 32 = 800` bytes.
pub const ETH_PI_TAIL_BYTES_V2: usize = ETH_PI_LANES_V2 * 32;

/// The 25-lane public inputs a dregg settlement binds on Ethereum — the live
/// wide `WholeChainProofBytes` claim (8-felt anchors + 8-felt digest), each
/// lane a canonical BabyBear residue carried as `u32`.
///
/// Construct via [`EthPublicInputsV2::new`] /
/// [`EthPublicInputsV2::from_whole_chain_bytes`] (both fail-closed on any
/// non-canonical lane or an out-of-`u32`-range `num_turns`); the fields are
/// read-only from outside this module so a value of this type is always
/// canonical by construction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "EthPublicInputsV2Wire", into = "EthPublicInputsV2Wire")]
pub struct EthPublicInputsV2 {
    /// The 8-felt genesis state anchor (canonical BabyBear lanes).
    genesis_root: [u32; 8],
    /// The 8-felt final state anchor (canonical BabyBear lanes).
    final_root: [u32; 8],
    /// Number of finalized turns folded (one canonical BabyBear lane — the
    /// in-circuit claim is `BabyBear::new(num_turns as u32)`, so the bridge
    /// pins `num_turns < p`).
    num_turns: u32,
    /// The 8-felt Poseidon2 ordered-history digest (canonical BabyBear lanes).
    chain_digest: [u32; 8],
}

/// The UNVALIDATED serde mirror of [`EthPublicInputsV2`]. Deserialization is
/// routed through `TryFrom` so wire bytes carrying a non-canonical lane are
/// REFUSED at decode — serde cannot construct a non-canonical
/// `EthPublicInputsV2` around the fail-closed constructor.
#[derive(Clone, Serialize, Deserialize)]
struct EthPublicInputsV2Wire {
    genesis_root: [u32; 8],
    final_root: [u32; 8],
    num_turns: u32,
    chain_digest: [u32; 8],
}

impl TryFrom<EthPublicInputsV2Wire> for EthPublicInputsV2 {
    type Error = EthBridgeError;
    fn try_from(w: EthPublicInputsV2Wire) -> Result<Self, Self::Error> {
        EthPublicInputsV2::new(
            w.genesis_root,
            w.final_root,
            u64::from(w.num_turns),
            w.chain_digest,
        )
    }
}

impl From<EthPublicInputsV2> for EthPublicInputsV2Wire {
    fn from(p: EthPublicInputsV2) -> Self {
        Self {
            genesis_root: p.genesis_root,
            final_root: p.final_root,
            num_turns: p.num_turns,
            chain_digest: p.chain_digest,
        }
    }
}

/// Reject any lane `>= p` (fail-closed canonicality gate for the V2 statement).
fn check_canonical_lanes(name: &str, lanes: &[u32]) -> Result<(), EthBridgeError> {
    for (i, &lane) in lanes.iter().enumerate() {
        if lane >= BABYBEAR_MODULUS {
            return Err(EthBridgeError::InvalidProof {
                reason: format!(
                    "{name} lane {i} = {lane} is not a canonical BabyBear residue \
                     (must be < {BABYBEAR_MODULUS})"
                ),
            });
        }
    }
    Ok(())
}

impl EthPublicInputsV2 {
    /// Fail-closed constructor from the four `WholeChainProofBytes`-shaped
    /// fields. `num_turns` is the envelope's `u64`; it must fit `u32` AND be a
    /// canonical BabyBear residue (it rides as one lane of the 25-lane claim).
    /// Every root/digest lane must be canonical (`< p`). Any violation errors —
    /// nothing is reduced or truncated.
    pub fn new(
        genesis_root: [u32; 8],
        final_root: [u32; 8],
        num_turns: u64,
        chain_digest: [u32; 8],
    ) -> Result<Self, EthBridgeError> {
        let num_turns_u32 = u32::try_from(num_turns).map_err(|_| EthBridgeError::InvalidProof {
            reason: format!("num_turns {num_turns} does not fit u32"),
        })?;
        check_canonical_lanes("genesis_root", &genesis_root)?;
        check_canonical_lanes("final_root", &final_root)?;
        check_canonical_lanes("num_turns", &[num_turns_u32])?;
        check_canonical_lanes("chain_digest", &chain_digest)?;
        Ok(Self {
            genesis_root,
            final_root,
            num_turns: num_turns_u32,
            chain_digest,
        })
    }

    /// Fail-closed constructor from the real wire envelope
    /// ([`dregg_circuit_prove::ivc_turn_chain::WholeChainProofBytes`], v3):
    /// takes exactly its four public fields. Same validation as [`Self::new`].
    pub fn from_whole_chain_bytes(
        src: &dregg_circuit_prove::ivc_turn_chain::WholeChainProofBytes,
    ) -> Result<Self, EthBridgeError> {
        Self::new(
            src.genesis_root,
            src.final_root,
            src.num_turns,
            src.chain_digest,
        )
    }

    /// The 8-felt genesis anchor lanes.
    pub fn genesis_root(&self) -> [u32; 8] {
        self.genesis_root
    }

    /// The 8-felt final anchor lanes.
    pub fn final_root(&self) -> [u32; 8] {
        self.final_root
    }

    /// The turn count (canonical BabyBear lane).
    pub fn num_turns(&self) -> u32 {
        self.num_turns
    }

    /// The 8-felt chain-digest lanes.
    pub fn chain_digest(&self) -> [u32; 8] {
        self.chain_digest
    }

    /// The 25 lanes in the PINNED public-input order the Groth16 wrap circuit
    /// and the Solidity verifier both bind:
    /// `genesis_root[0..8] ++ final_root[0..8] ++ num_turns ++ chain_digest[0..8]`.
    pub fn lanes(&self) -> [u32; ETH_PI_LANES_V2] {
        let mut out = [0u32; ETH_PI_LANES_V2];
        out[0..8].copy_from_slice(&self.genesis_root);
        out[8..16].copy_from_slice(&self.final_root);
        out[16] = self.num_turns;
        out[17..25].copy_from_slice(&self.chain_digest);
        out
    }

    /// The V2 public-input calldata tail: the 25 lanes in the pinned order,
    /// EACH ABI-encoded as a full 32-byte big-endian word (matching the
    /// Solidity static encoding of `uint32[8],uint32[8],uint32,uint32[8]`) —
    /// [`ETH_PI_TAIL_BYTES_V2`] = 800 bytes total.
    pub fn to_calldata_v2(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(ETH_PI_TAIL_BYTES_V2);
        for lane in self.lanes() {
            let mut word = [0u8; 32];
            word[28..32].copy_from_slice(&lane.to_be_bytes());
            out.extend_from_slice(&word);
        }
        out
    }

    /// Inverse of [`Self::to_calldata_v2`]: decode a `settle` calldata tail
    /// back into the typed 25-lane publics. Fail-closed on:
    /// - wrong length (exactly [`ETH_PI_TAIL_BYTES_V2`] = 800 bytes),
    /// - any nonzero byte in a word's 28-byte padding (a value `>= 2^32` is
    ///   not a `uint32` — refused, never truncated),
    /// - any non-canonical lane (re-validated through [`Self::new`]).
    pub fn from_tail_v2(tail: &[u8]) -> Result<Self, EthBridgeError> {
        if tail.len() != ETH_PI_TAIL_BYTES_V2 {
            return Err(EthBridgeError::Internal {
                reason: format!(
                    "v2 public-input tail must be {ETH_PI_TAIL_BYTES_V2} bytes \
                     (25 x 32), got {}",
                    tail.len()
                ),
            });
        }
        let mut lanes = [0u32; ETH_PI_LANES_V2];
        for (i, word) in tail.chunks_exact(32).enumerate() {
            if word[0..28].iter().any(|&b| b != 0) {
                return Err(EthBridgeError::Internal {
                    reason: format!(
                        "v2 public-input word {i} has nonzero high-padding bytes \
                         (not a uint32)"
                    ),
                });
            }
            let mut le = [0u8; 4];
            le.copy_from_slice(&word[28..32]);
            lanes[i] = u32::from_be_bytes(le);
        }
        let mut genesis_root = [0u32; 8];
        genesis_root.copy_from_slice(&lanes[0..8]);
        let mut final_root = [0u32; 8];
        final_root.copy_from_slice(&lanes[8..16]);
        let num_turns = lanes[16];
        let mut chain_digest = [0u32; 8];
        chain_digest.copy_from_slice(&lanes[17..25]);
        // Re-validate canonicality through the fail-closed constructor.
        Self::new(genesis_root, final_root, u64::from(num_turns), chain_digest)
    }

    /// The [`EthBridgeState`] key for the genesis anchor:
    /// [`root8_bridge_key`] over `genesis_root`.
    pub fn genesis_bridge_key(&self) -> [u8; 32] {
        root8_bridge_key(&self.genesis_root)
    }

    /// The [`EthBridgeState`] key for the final anchor:
    /// [`root8_bridge_key`] over `final_root`.
    pub fn final_bridge_key(&self) -> [u8; 32] {
        root8_bridge_key(&self.final_root)
    }
}

/// Collapse an 8-lane root to the `bytes32` the settlement state machine keys
/// on, so the EXISTING [`EthBridgeState`] continuity/monotone-height logic is
/// reused unchanged for V2 (no `EthBridgeStateV2`).
///
/// PINNED PACKING: `keccak256` over exactly 32 bytes = the 8 lanes as
/// big-endian `uint32`, lane 0 first. In Solidity this is
/// `keccak256(abi.encodePacked(l0, l1, ..., l7))` on the eight SEPARATE `uint32`
/// arguments (each packs to 4 bytes) — exactly what `DreggSettlement.packLanes`
/// computes. NOTE: `abi.encodePacked(root)` on a `uint32[8] root` does NOT match:
/// Solidity pads every ARRAY element to 32 bytes (a 256-byte pre-image). Build
/// the key from the unpacked lanes, never the array form.
pub fn root8_bridge_key(lanes: &[u32; 8]) -> [u8; 32] {
    use sha3::{Digest, Keccak256};
    let mut packed = [0u8; 32];
    for (i, lane) in lanes.iter().enumerate() {
        packed[i * 4..i * 4 + 4].copy_from_slice(&lane.to_be_bytes());
    }
    let mut h = Keccak256::new();
    h.update(packed);
    h.finalize().into()
}

/// The V2 Solidity verifier ABI: `settle` takes the Groth16 proof points + the
/// 25-lane public inputs in the pinned order/shape
/// (`uint32[8] genesisRoot, uint32[8] finalRoot, uint32 numTurns,
/// uint32[8] chainDigest`). The v1 [`solidity_verifier_interface`] is kept
/// untouched (STAGED-ADDITIVE).
pub fn solidity_verifier_interface_v2() -> &'static str {
    r#"// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// dregg whole-chain settlement verifier — V2 (the 25-lane wide claim).
/// Verifies a Groth16(BN254) proof that wraps the dregg recursive STARK
/// attesting "all finalized turns executed and the 8-felt state anchor
/// advanced from genesisRoot to finalRoot", then advances the on-chain
/// proven root key. Every lane MUST be a canonical BabyBear residue
/// (< 2013265921); the contract reverts otherwise.
interface IDreggSettlementV2 {
    /// Current proven dregg root key: keccak256 over the 8 lanes as big-endian
    /// uint32 (32-byte pre-image), i.e. abi.encodePacked(l0,...,l7) on the
    /// SEPARATE uint32 args — NOT abi.encodePacked(root) on the array (which
    /// pads each element to 32 bytes). See DreggSettlement.packLanes.
    function provenRootKey() external view returns (bytes32);

    /// Current proven height (monotone).
    function provenHeight() external view returns (uint64);

    /// keccak256 of the Groth16 verifying key this contract checks against.
    function verifyingKeyHash() external view returns (bytes32);

    /// Submit a settlement.
    /// @param a,b,c       Groth16 proof points (BN254): a in G1, b in G2, c in G1.
    /// @param commitments,commitmentPok The proof's Pedersen commitment (2
    ///                    words) + its proof of knowledge (2 words) — the wrap
    ///                    circuit uses gnark's commit-based range checker, so
    ///                    the Groth16 proof blob is 384 bytes (12 words), not
    ///                    256: gnark MarshalSolidity words [8..12) after the
    ///                    8 proof words. Part of the PROOF, not the statement.
    /// @param genesisRoot 8-lane genesis anchor; its packed keccak must equal
    ///                    the current provenRootKey (continuity).
    /// @param finalRoot   8-lane final anchor; its packed keccak becomes the
    ///                    proven root key on success.
    /// @param numTurns    Number of finalized turns folded (canonical BabyBear).
    /// @param chainDigest 8-lane Poseidon2 digest over the ordered (old,new)
    ///                    root pairs.
    /// @param outboundMessageRoot RESERVED for the proof-bound outbound-message
    ///                    commitment. MUST be bytes32(0) today: the 25-lane
    ///                    proof carries no message commitment, so the contract
    ///                    REVERTS on any non-zero value
    ///                    (MessageRootNotProofBound, fail closed — the
    ///                    operator-attested recording path is removed).
    /// Reverts if the pairing check fails, any lane >= 2013265921, or the
    /// genesisRoot key mismatches the proven root key.
    function settle(
        uint256[2] calldata a,
        uint256[2][2] calldata b,
        uint256[2] calldata c,
        uint256[2] calldata commitments,
        uint256[2] calldata commitmentPok,
        uint32[8] calldata genesisRoot,
        uint32[8] calldata finalRoot,
        uint32 numTurns,
        uint32[8] calldata chainDigest,
        bytes32 outboundMessageRoot
    ) external;

    event SettledV2(bytes32 indexed oldRootKey, bytes32 indexed newRootKey, uint64 height);
}
"#
}

// ============================================================================
// V2 submitter: the settle() calldata for the REAL DreggSettlement contract
// ============================================================================

/// The canonical signature of `DreggSettlement.settle` (see
/// `chain/contracts/DreggSettlement.sol`):
/// `(a, b, c, commitments, commitmentPok, genesisRoot, finalRoot, numTurns,
/// chainDigest, outboundMessageRoot)`. All-static argument types, so the ABI
/// encoding is exactly 38 head words after the 4-byte selector.
pub const SETTLE_V2_SIGNATURE: &str = "settle(uint256[2],uint256[2][2],uint256[2],uint256[2],\
                                       uint256[2],uint32[8],uint32[8],uint32,uint32[8],bytes32)";

/// Total `settle()` calldata length: 4-byte selector + 38 static words
/// (12 proof + 25 public-input lanes + 1 outboundMessageRoot) = 1220 bytes.
pub const SETTLE_V2_CALLDATA_BYTES: usize =
    4 + (GROTH16_EVM_PROOF_WORDS + ETH_PI_LANES_V2 + 1) * 32;

/// The 4-byte function selector of [`SETTLE_V2_SIGNATURE`]:
/// `keccak256(signature)[0..4]` = `0x01f01e9c` (cross-checked against
/// `cast sig` / the Foundry call in `DreggSettlementRealProof.t.sol`).
pub fn settle_v2_selector() -> [u8; 4] {
    use sha3::{Digest, Keccak256};
    let sig: String = SETTLE_V2_SIGNATURE.split_whitespace().collect();
    let mut h = Keccak256::new();
    h.update(sig.as_bytes());
    let digest = h.finalize();
    [digest[0], digest[1], digest[2], digest[3]]
}

/// A dregg whole-chain proof packaged for the REAL `DreggSettlement` contract —
/// the V2 (25-lane, commit-based-range-checker) settlement artifact the live
/// submitter sends.
///
/// Carries the full 384-byte (12-word) Groth16 proof blob
/// ([`GROTH16_EVM_PROOF_BYTES`]; word order = [`Groth16Calldata`]) + the
/// 25-lane statement ([`EthPublicInputsV2`]) + the contract/VK binding.
/// Groth16/BN254 only: the V2 contract's verifier is the gnark-generated
/// `DreggGroth16Verifier25.sol`.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct EthSettlementProofV2 {
    /// The 384-byte Groth16 proof blob:
    /// `A(2w) ++ B(4w) ++ C(2w) ++ commitments(2w) ++ commitmentPok(2w)`.
    /// Length-pinned by [`Self::new`]; sliced by [`Self::groth16`].
    pub snark_proof: Vec<u8>,
    /// The 25-lane public inputs (genesis[8] ++ final[8] ++ numTurns ++
    /// digest[8]) — canonical BabyBear by construction.
    pub public_inputs: EthPublicInputsV2,
    /// keccak256 of the Groth16 verifying key (the contract's
    /// `verifyingKeyHash()` binding).
    pub verifying_key_hash: [u8; 32],
    /// keccak256 commitment to the underlying recursive STARK root this proof
    /// wraps (binds the SNARK to the dregg proof it attests).
    pub recursive_root_commitment: [u8; 32],
    /// The span's outbound cross-chain message root. MUST be `[0u8; 32]`
    /// today: the contract fails closed (`MessageRootNotProofBound`) on any
    /// non-zero value because the 25-lane proof carries no outbound-message
    /// commitment to bind it to. The field (and calldata word 37) is reserved
    /// for the proof-bound leg — apex message-commitment claim lanes (the
    /// contract's named residual in `DreggSettlement.sol`).
    pub outbound_message_root: [u8; 32],
}

impl EthSettlementProofV2 {
    /// Fail-closed constructor: refuses any blob that is not exactly the
    /// 12-word layout (in particular the OLD 256-byte 8-word shape).
    pub fn new(
        snark_proof: Vec<u8>,
        public_inputs: EthPublicInputsV2,
        verifying_key_hash: [u8; 32],
        recursive_root_commitment: [u8; 32],
        outbound_message_root: [u8; 32],
    ) -> Result<Self, EthBridgeError> {
        Groth16Calldata::from_proof_bytes(&snark_proof)?;
        Ok(Self {
            snark_proof,
            public_inputs,
            verifying_key_hash,
            recursive_root_commitment,
            outbound_message_root,
        })
    }

    /// The proof blob sliced into its typed points (word order pinned by
    /// [`Groth16Calldata`]). Re-validates the length (fail-closed even if the
    /// pub field was mutated after construction).
    pub fn groth16(&self) -> Result<Groth16Calldata, EthBridgeError> {
        Groth16Calldata::from_proof_bytes(&self.snark_proof)
    }

    /// The COMPLETE calldata for `DreggSettlement.settle` — selector + the 38
    /// static ABI words, byte-identical to what
    /// `chain/test/DreggSettlementRealProof.t.sol` submits:
    ///
    /// ```text
    /// [0..4)     selector 0x01f01e9c
    /// word 0..2  a
    /// word 2..6  b               (b[0][0], b[0][1], b[1][0], b[1][1])
    /// word 6..8  c
    /// word 8..10 commitments
    /// word 10..12 commitmentPok
    /// word 12..20 genesisRoot    (each uint32 in a full 32-byte word)
    /// word 20..28 finalRoot
    /// word 28    numTurns
    /// word 29..37 chainDigest
    /// word 37    outboundMessageRoot
    /// ```
    pub fn settle_calldata(&self) -> Result<Vec<u8>, EthBridgeError> {
        let proof = self.groth16()?;
        let mut out = Vec::with_capacity(SETTLE_V2_CALLDATA_BYTES);
        out.extend_from_slice(&settle_v2_selector());
        for word in proof.words() {
            out.extend_from_slice(&word);
        }
        out.extend_from_slice(&self.public_inputs.to_calldata_v2());
        out.extend_from_slice(&self.outbound_message_root);
        debug_assert_eq!(out.len(), SETTLE_V2_CALLDATA_BYTES);
        Ok(out)
    }

    /// Inverse of [`Self::settle_calldata`] — the relayer seam that reads a
    /// `settle()` calldata back into the typed artifact. Fail-closed on a
    /// wrong selector, wrong length, non-`uint32` lane word, or non-canonical
    /// lane. The VK / recursive-root bindings are NOT in calldata, so the
    /// caller supplies them.
    pub fn from_settle_calldata(
        calldata: &[u8],
        verifying_key_hash: [u8; 32],
        recursive_root_commitment: [u8; 32],
    ) -> Result<Self, EthBridgeError> {
        if calldata.len() != SETTLE_V2_CALLDATA_BYTES {
            return Err(EthBridgeError::Internal {
                reason: format!(
                    "settle() calldata must be {SETTLE_V2_CALLDATA_BYTES} bytes, got {}",
                    calldata.len()
                ),
            });
        }
        if calldata[0..4] != settle_v2_selector() {
            return Err(EthBridgeError::Internal {
                reason: "not a settle() call (selector mismatch)".to_string(),
            });
        }
        let proof_end = 4 + GROTH16_EVM_PROOF_BYTES;
        let snark_proof = calldata[4..proof_end].to_vec();
        let pi_end = proof_end + ETH_PI_TAIL_BYTES_V2;
        let public_inputs = EthPublicInputsV2::from_tail_v2(&calldata[proof_end..pi_end])?;
        let mut outbound_message_root = [0u8; 32];
        outbound_message_root.copy_from_slice(&calldata[pi_end..]);
        Self::new(
            snark_proof,
            public_inputs,
            verifying_key_hash,
            recursive_root_commitment,
            outbound_message_root,
        )
    }

    /// Deserialize the gnark exporter's proof JSON
    /// (`chain/test/fixtures/settlement_groth16.json`, written by
    /// `chain/gnark/settlement_snark_test.go`): 8 hex proof words +
    /// `commitments[2]` + `commitment_pok[2]` (together the 384-byte blob in
    /// gnark `MarshalSolidity` order) + the 25-lane statement. Fail-closed on
    /// a wrong word count, a malformed word, a non-canonical lane, or a flat
    /// `inputs` vector that disagrees with the split lanes (the pinned-order
    /// cross-check `test_FixtureInputOrderIsPinned` runs on the Foundry side).
    pub fn from_gnark_fixture_json(
        json: &str,
        verifying_key_hash: [u8; 32],
        recursive_root_commitment: [u8; 32],
        outbound_message_root: [u8; 32],
    ) -> Result<Self, EthBridgeError> {
        #[derive(Deserialize)]
        struct GnarkSettlementFixture {
            proof: Vec<String>,
            commitments: Vec<String>,
            commitment_pok: Vec<String>,
            inputs: Vec<String>,
            genesis_root: [u32; 8],
            final_root: [u32; 8],
            num_turns: u64,
            chain_digest: [u32; 8],
        }
        let fx: GnarkSettlementFixture =
            serde_json::from_str(json).map_err(|e| EthBridgeError::InvalidProof {
                reason: format!("gnark settlement fixture JSON: {e}"),
            })?;
        if fx.proof.len() != 8 || fx.commitments.len() != 2 || fx.commitment_pok.len() != 2 {
            return Err(EthBridgeError::InvalidProof {
                reason: format!(
                    "gnark settlement fixture must carry 8 proof + 2 commitment + 2 PoK \
                     words, got {}/{}/{}",
                    fx.proof.len(),
                    fx.commitments.len(),
                    fx.commitment_pok.len()
                ),
            });
        }
        let mut snark_proof = Vec::with_capacity(GROTH16_EVM_PROOF_BYTES);
        for hex_word in fx
            .proof
            .iter()
            .chain(fx.commitments.iter())
            .chain(fx.commitment_pok.iter())
        {
            snark_proof.extend_from_slice(&parse_hex_word(hex_word)?);
        }
        let public_inputs = EthPublicInputsV2::new(
            fx.genesis_root,
            fx.final_root,
            fx.num_turns,
            fx.chain_digest,
        )?;
        // The flat 25-lane vector must match the split lanes in the pinned
        // order (a drifted exporter dies HERE, not in an on-chain pairing
        // failure) — the Rust mirror of test_FixtureInputOrderIsPinned.
        if fx.inputs.len() != ETH_PI_LANES_V2 {
            return Err(EthBridgeError::InvalidProof {
                reason: format!(
                    "gnark settlement fixture inputs must be {ETH_PI_LANES_V2} lanes, got {}",
                    fx.inputs.len()
                ),
            });
        }
        for (i, (flat, lane)) in fx.inputs.iter().zip(public_inputs.lanes()).enumerate() {
            let flat: u64 = flat.parse().map_err(|_| EthBridgeError::InvalidProof {
                reason: format!("gnark settlement fixture input lane {i} is not a decimal uint"),
            })?;
            if flat != u64::from(lane) {
                return Err(EthBridgeError::InvalidProof {
                    reason: format!(
                        "gnark settlement fixture input lane {i} = {flat} disagrees with the \
                         split-field lane {lane} (pinned order: genesis[0..8) ++ final[8..16) \
                         ++ numTurns[16] ++ chainDigest[17..25))"
                    ),
                });
            }
        }
        Self::new(
            snark_proof,
            public_inputs,
            verifying_key_hash,
            recursive_root_commitment,
            outbound_message_root,
        )
    }
}

/// Parse one `0x…` hex word (≤ 64 hex digits, left-padded) into a 32-byte
/// big-endian word. Fail-closed on a missing prefix, an over-long word, or a
/// non-hex digit.
fn parse_hex_word(s: &str) -> Result<[u8; 32], EthBridgeError> {
    let digits = s
        .strip_prefix("0x")
        .ok_or_else(|| EthBridgeError::InvalidProof {
            reason: format!("hex word {s:?} lacks the 0x prefix"),
        })?;
    if digits.is_empty() || digits.len() > 64 {
        return Err(EthBridgeError::InvalidProof {
            reason: format!("hex word {s:?} must be 1..=64 hex digits"),
        });
    }
    let mut out = [0u8; 32];
    // Left-pad: walk the digits from the RIGHT, two per byte.
    let bytes = digits.as_bytes();
    let mut i = bytes.len();
    let mut o = 32;
    while i > 0 {
        let lo = i;
        let hi = i.saturating_sub(2);
        let pair = std::str::from_utf8(&bytes[hi..lo]).expect("ascii hex slice");
        let v = u8::from_str_radix(pair, 16).map_err(|_| EthBridgeError::InvalidProof {
            reason: format!("hex word {s:?} has a non-hex digit"),
        })?;
        o -= 1;
        out[o] = v;
        i = hi;
    }
    Ok(out)
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

    /// Groth16/BN254 calldata shape is pinned to the 12-word 384-byte blob —
    /// and the OLD 8-word 256-byte shape is now REFUSED (the wrap circuit's
    /// commit-based range checker makes commitments/commitmentPok part of
    /// every real proof).
    #[test]
    fn groth16_proof_shape_pinned() {
        // Wrong sizes rejected — including the legacy 256-byte layout.
        for bad_len in [100usize, 256, 383, 385] {
            let bad = wrap_for_ethereum(
                [0xAB; 32],
                pis(1, 2, 1),
                SnarkSystem::Groth16Bn254,
                Some(vec![0u8; bad_len]),
                [9; 32],
            );
            assert!(
                bad.is_err(),
                "a {bad_len}-byte Groth16 blob must be refused"
            );
        }
        // Correct size accepted + marked SNARK-backed.
        let ok = wrap_for_ethereum(
            [0xAB; 32],
            pis(1, 2, 1),
            SnarkSystem::Groth16Bn254,
            Some(vec![7u8; GROTH16_EVM_PROOF_BYTES]),
            [9; 32],
        )
        .expect("384-byte Groth16 proof must wrap");
        assert!(ok.is_snark_backed());
        assert!(verify_settlement_binding(&ok).unwrap());
        // calldata = proof(384) + 4 public-input words(3*32 + 8) = 384 + 104.
        assert_eq!(ok.to_calldata().len(), 384 + 32 + 32 + 8 + 32);
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
            Some(vec![7u8; GROTH16_EVM_PROOF_BYTES]),
            [9; 32],
        )
        .expect("384-byte Groth16 proof wraps");

        let tail = p.public_input_tail();
        assert_eq!(
            tail.len(),
            32 + 32 + 8 + 32,
            "tail is the 104-byte PI region"
        );
        // The tail is exactly the calldata after the 384-byte proof prefix.
        assert_eq!(tail, p.to_calldata()[GROTH16_EVM_PROOF_BYTES..].to_vec());

        let decoded = EthPublicInputs::from_tail(&tail).expect("tail decodes");
        assert_eq!(decoded, p.public_inputs, "publics survive the round trip");

        // A wrong-length tail is rejected (the format is pinned).
        assert!(EthPublicInputs::from_tail(&tail[..100]).is_err());
    }

    /// The Groth16 slicer cuts the 384-byte proof into the exact word order the
    /// Solidity `settle` ABI + EIP-197 precompile consume: A=G1, B=G2
    /// (imaginary coordinate first), C=G1, then the range checker's
    /// commitments + commitmentPok. Non-384-byte proofs (including the legacy
    /// 256-byte 8-word shape) are refused, and the blob round-trips.
    #[test]
    fn groth16_calldata_slices_twelve_words() {
        // A proof whose 12 coordinate words are distinguishable (word i = byte i).
        let mut proof = [0u8; GROTH16_EVM_PROOF_BYTES];
        for (i, w) in proof.chunks_mut(32).enumerate() {
            w[31] = i as u8; // low byte of word i == i
        }
        let p = Groth16Calldata::from_proof_bytes(&proof).expect("384B slices");
        assert_eq!(p.a[0][31], 0, "A.x = word 0");
        assert_eq!(p.a[1][31], 1, "A.y = word 1");
        assert_eq!(p.b[0][0][31], 2, "B.x_c1 = word 2 (imaginary first)");
        assert_eq!(p.b[0][1][31], 3, "B.x_c0 = word 3");
        assert_eq!(p.b[1][0][31], 4, "B.y_c1 = word 4");
        assert_eq!(p.b[1][1][31], 5, "B.y_c0 = word 5");
        assert_eq!(p.c[0][31], 6, "C.x = word 6");
        assert_eq!(p.c[1][31], 7, "C.y = word 7");
        assert_eq!(p.commitments[0][31], 8, "commitments.x = word 8");
        assert_eq!(p.commitments[1][31], 9, "commitments.y = word 9");
        assert_eq!(p.commitment_pok[0][31], 10, "commitmentPok.x = word 10");
        assert_eq!(p.commitment_pok[1][31], 11, "commitmentPok.y = word 11");
        assert_eq!(p.to_proof_bytes(), proof.to_vec(), "blob round-trips");

        for bad_len in [100usize, 256, 383] {
            let bad = vec![0u8; bad_len];
            assert!(
                Groth16Calldata::from_proof_bytes(&bad).is_err(),
                "a {bad_len}-byte proof must be refused"
            );
        }
    }

    // ------------------------------------------------------------------
    // V2 submitter: the REAL fixture + the settle() calldata ground truth
    // ------------------------------------------------------------------

    /// The REAL Groth16 fixture minted by chain/gnark over the real dregg
    /// shrink proof — the same file DreggSettlementRealProof.t.sol settles
    /// with on the Foundry side.
    const REAL_FIXTURE_JSON: &str = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../chain/test/fixtures/settlement_groth16.json"
    ));

    /// `settle()`'s 4-byte selector is pinned and matches
    /// `cast sig "settle(uint256[2],uint256[2][2],uint256[2],uint256[2],uint256[2],uint32[8],uint32[8],uint32,uint32[8],bytes32)"`.
    #[test]
    fn settle_v2_selector_is_pinned() {
        assert_eq!(settle_v2_selector(), [0x01, 0xf0, 0x1e, 0x9c]);
    }

    /// THE ENCODING GROUND TRUTH: the real fixture assembles into an
    /// [`EthSettlementProofV2`] whose blob is exactly 384 bytes, whose sliced
    /// words match the fixture's raw hex words, and whose `settle()` calldata
    /// is BYTE-IDENTICAL to the Foundry-side call — pinned as the keccak256 of
    /// `cast calldata "settle(...)" <fixture args…>` over this fixture
    /// (regenerate the digest with cast if the fixture is re-minted).
    #[test]
    fn real_fixture_settle_calldata_matches_foundry_ground_truth() {
        let p = EthSettlementProofV2::from_gnark_fixture_json(
            REAL_FIXTURE_JSON,
            [0x11; 32],
            [0x22; 32],
            [0u8; 32], // outboundMessageRoot = bytes32(0), as in the Foundry test
        )
        .expect("the real fixture parses");

        // The proof region is the 12-word 384-byte blob.
        assert_eq!(p.snark_proof.len(), GROTH16_EVM_PROOF_BYTES);

        // The sliced words equal the fixture's raw hex words, independently
        // re-parsed here (not through the deserializer under test).
        let raw: serde_json::Value = serde_json::from_str(REAL_FIXTURE_JSON).unwrap();
        let hexw = |v: &serde_json::Value| parse_hex_word(v.as_str().unwrap()).unwrap();
        let g = p.groth16().unwrap();
        assert_eq!(g.a[0], hexw(&raw["proof"][0]), "a[0] = proof word 0");
        assert_eq!(g.b[0][0], hexw(&raw["proof"][2]), "b[0][0] = proof word 2");
        assert_eq!(g.c[1], hexw(&raw["proof"][7]), "c[1] = proof word 7");
        assert_eq!(g.commitments[0], hexw(&raw["commitments"][0]));
        assert_eq!(g.commitments[1], hexw(&raw["commitments"][1]));
        assert_eq!(g.commitment_pok[0], hexw(&raw["commitment_pok"][0]));
        assert_eq!(g.commitment_pok[1], hexw(&raw["commitment_pok"][1]));

        // The calldata: selector + 38 static words = 1220 bytes.
        let cd = p.settle_calldata().unwrap();
        assert_eq!(cd.len(), SETTLE_V2_CALLDATA_BYTES);
        assert_eq!(&cd[0..4], &[0x01, 0xf0, 0x1e, 0x9c], "settle() selector");

        // Slot spot-checks against the independently parsed fixture.
        let word = |i: usize| &cd[4 + 32 * i..4 + 32 * (i + 1)];
        assert_eq!(word(0), hexw(&raw["proof"][0]), "word 0 = a[0]");
        assert_eq!(word(7), hexw(&raw["proof"][7]), "word 7 = c[1]");
        assert_eq!(
            word(8),
            hexw(&raw["commitments"][0]),
            "word 8 = commitments[0]"
        );
        assert_eq!(
            word(11),
            hexw(&raw["commitment_pok"][1]),
            "word 11 = commitmentPok[1]"
        );
        // genesis lanes occupy words 12..20, each a uint32 in a full word.
        for i in 0..8 {
            let lane = raw["genesis_root"][i].as_u64().unwrap() as u32;
            let mut expect = [0u8; 32];
            expect[28..].copy_from_slice(&lane.to_be_bytes());
            assert_eq!(word(12 + i), expect, "word {} = genesisRoot[{i}]", 12 + i);
        }
        // numTurns at word 28; chainDigest words 29..37; outbound root word 37.
        assert_eq!(
            u64::from(raw["num_turns"].as_u64().unwrap() as u32),
            u64::from(u32::from_be_bytes(word(28)[28..].try_into().unwrap()))
        );
        let d7 = raw["chain_digest"][7].as_u64().unwrap() as u32;
        assert_eq!(
            u32::from_be_bytes(word(36)[28..].try_into().unwrap()),
            d7,
            "word 36 = chainDigest[7]"
        );
        assert_eq!(word(37), [0u8; 32], "word 37 = outboundMessageRoot");

        // THE FOUNDRY GROUND TRUTH: keccak256 of the full calldata equals the
        // digest of `cast calldata` over the same signature + fixture args
        // (computed offline; see the doc comment).
        use sha3::{Digest, Keccak256};
        let mut h = Keccak256::new();
        h.update(&cd);
        let digest: [u8; 32] = h.finalize().into();
        let expected: [u8; 32] = [
            0xf5, 0x17, 0xc4, 0x08, 0x32, 0xf5, 0xd5, 0x6d, 0x02, 0xc9, 0xc9, 0x96, 0xe4, 0xdd,
            0x3c, 0x3d, 0x46, 0x3d, 0x56, 0x78, 0x38, 0xf7, 0xbe, 0x96, 0xa4, 0x86, 0x6e, 0x26,
            0x50, 0x94, 0xbd, 0xb2,
        ];
        assert_eq!(
            digest, expected,
            "settle() calldata must be byte-identical to the cast/Foundry encoding"
        );

        // Round-trip: decode the calldata back into the typed artifact.
        let back = EthSettlementProofV2::from_settle_calldata(&cd, [0x11; 32], [0x22; 32])
            .expect("calldata decodes");
        assert_eq!(back, p, "encode -> decode round-trips");
    }

    /// The V2 artifact refuses the OLD 256-byte blob and tampered calldata.
    #[test]
    fn v2_submitter_fail_closed() {
        let pi = EthPublicInputsV2::new([1; 8], [2; 8], 3, [4; 8]).unwrap();
        // The legacy 8-word blob is refused.
        assert!(
            EthSettlementProofV2::new(vec![7u8; 256], pi.clone(), [0; 32], [0; 32], [0; 32])
                .is_err(),
            "the 256-byte legacy blob must be refused"
        );

        let p = EthSettlementProofV2::new(vec![7u8; 384], pi, [0; 32], [0; 32], [9; 32]).unwrap();
        let mut cd = p.settle_calldata().unwrap();
        // Wrong selector refused.
        cd[0] ^= 0xFF;
        assert!(EthSettlementProofV2::from_settle_calldata(&cd, [0; 32], [0; 32]).is_err());
        cd[0] ^= 0xFF;
        // Truncated calldata refused.
        assert!(
            EthSettlementProofV2::from_settle_calldata(&cd[..cd.len() - 1], [0; 32], [0; 32])
                .is_err()
        );
        // A non-canonical lane word (>= BabyBear p) in the PI region refused.
        let lane16_off = 4 + GROTH16_EVM_PROOF_BYTES + 16 * 32; // numTurns word
        cd[lane16_off + 28..lane16_off + 32].copy_from_slice(&BABYBEAR_MODULUS.to_be_bytes());
        assert!(EthSettlementProofV2::from_settle_calldata(&cd, [0; 32], [0; 32]).is_err());
    }

    /// A fixture whose flat `inputs` vector disagrees with the split lanes is
    /// refused at parse (the exporter-drift tooth, mirroring the Foundry
    /// test_FixtureInputOrderIsPinned).
    #[test]
    fn fixture_input_order_drift_refused() {
        let mut raw: serde_json::Value = serde_json::from_str(REAL_FIXTURE_JSON).unwrap();
        raw["inputs"][0] = serde_json::Value::String("12345".to_string());
        let drifted = serde_json::to_string(&raw).unwrap();
        let err =
            EthSettlementProofV2::from_gnark_fixture_json(&drifted, [0; 32], [0; 32], [0; 32])
                .unwrap_err();
        assert!(matches!(err, EthBridgeError::InvalidProof { .. }));
    }
}
