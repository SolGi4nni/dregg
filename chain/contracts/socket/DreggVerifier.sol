// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {IGroth16VerifierRegistry} from "../IGroth16VerifierRegistry.sol";

/// @title The OCIP security-provider socket — DREGG as a security provider you
///        PLUG INTO, not a chain you migrate to.
///
/// ## What this is
///
/// A THIRD-PARTY contract, on ANOTHER chain, wants to consume a DREGG
/// attestation — to accept a trade / settlement / solvency claim ONLY if a
/// DREGG proof attests it — WITHOUT migrating its state to DREGG. This is the
/// concrete interface it imports and calls. `DreggVerifier` is the stable
/// entry point; the external contract depends on THIS, never on the
/// gnark-generated verifier's baked-in VK.
///
/// The socket does NOT reimplement the pairing. It WRAPS the existing on-chain
/// verifier — specifically the VK-EPOCH REGISTRY
/// (`DreggGroth16VerifierUpgradeable` / `IGroth16VerifierRegistry`) — so that a
/// VK rotation (a GAP-flip, the nullifier flip, a re-genesis) is a single
/// `advanceEpoch` transaction against the registry and is INVISIBLE to every
/// external consumer: a consumer that calls `verifyStatement` always checks
/// against the registry's CURRENT epoch; a consumer holding a proof minted
/// under an old VK calls `verifyStatementAtEpoch` and it still verifies. The
/// socket is the VK-rotation-absorbing seam.
///
/// ## What a DREGG attestation ATTESTS (the public statement)
///
/// The proof is a Groth16(BN254) wrap of the DREGG whole-history STARK apex
/// (STARK fold → BN254-native shrink → gnark `SettlementCircuit` → Groth16; see
/// `docs/deos/CROSS-CHAIN-SETTLEMENT-REALNESS.md`). Its 25 public inputs are
/// the pinned settlement statement (`IGroth16Verifier25`):
///
///   [0..8)   genesis_root  — 8 BabyBear lanes: the DREGG state the chain
///                            started from (WHICH dregg instance this is about).
///   [8..16)  final_root    — 8 BabyBear lanes: the DREGG state it reached.
///   [16]     num_turns     — how many turns were folded into this transition.
///   [17..25) chain_digest  — 8 BabyBear lanes: the segment accumulator binding
///                            every (old_root, new_root) pair in the fold.
///
/// A valid proof attests: *there exists a sequence of `num_turns` VALID DREGG
/// turns carrying `genesis_root` to `final_root`, each turn the sound exercise
/// of a proof-carrying token over owned state* — i.e. a CONSERVED, rule-abiding
/// state transition. When the folded turns are a uniform-price clearing (the
/// launchpad statement, `Market/Optimality.lean` — every winner pays the same
/// clearing price p*, no leg arbitrages) or a pool settlement, the same proof
/// attests THAT clearing / settlement was fair / solvent / conserved. The
/// semantic content is fixed by the DREGG circuit; the socket verifies the
/// PROOF of it.
///
/// ## Honest scope (read `docs/deos/OCIP-SECURITY-SOCKET.md` §caveats)
///
/// The socket verifies the PROOF. It does NOT assert the semantics are what you
/// assume — that is the DREGG statement (the circuit + its Lean-proved
/// mechanism), and a consumer trusts DREGG for it exactly as it would trust any
/// security provider. And today's proof rides a SINGLE-PARTY DEV Groth16
/// ceremony (toxic-waste-known; `chain/DEPLOYMENTS.md`): a consumer wired to a
/// dev-ceremony registry is a DEMO OF THE INTERFACE, not production trust.
/// Production trust needs the MPC ceremony (ember-gated) — swap the registry's
/// epoch-0 VK for the ceremony VK and every consumer below is unchanged.
library DreggAttestation {
    /// The BabyBear prime p = 2^31 - 2^27 + 1. Every statement lane is a
    /// canonical residue strictly below it (mirrors `DreggSettlement`).
    uint256 internal constant BABYBEAR_P = 2013265921;

    /// A DREGG wrap proof: the Groth16(BN254) proof points plus the single
    /// Pedersen commitment (`commitments`) and its proof of knowledge
    /// (`commitmentPok`) the gnark commit-based range checker carries. Word
    /// order matches EIP-197 / `IGroth16Verifier25` exactly.
    struct Proof {
        uint256[2] a;
        uint256[2][2] b;
        uint256[2] c;
        uint256[2] commitments;
        uint256[2] commitmentPok;
    }

    /// The DREGG settlement statement in typed, human-meaningful form. A
    /// consumer builds the one it EXPECTS (e.g. "a clearing of my trusted dregg
    /// instance's genesis anchor") and the socket binds it into the 25 lanes.
    struct Statement {
        uint32[8] genesisRoot;
        uint32[8] finalRoot;
        uint32 numTurns;
        uint32[8] chainDigest;
    }

    error NonCanonicalLane(uint256 laneIndex, uint32 value);

    /// Assemble the pinned 25-lane public-input vector from a typed statement,
    /// enforcing BabyBear canonicity on every lane. A non-canonical lane makes
    /// the statement ill-formed (NOT a forgery) and reverts here — distinct
    /// from a well-formed statement whose proof simply fails to verify.
    function encode(Statement memory s)
        internal
        pure
        returns (uint256[25] memory inputs)
    {
        for (uint256 i = 0; i < 8; i++) {
            _canonical(i, s.genesisRoot[i]);
            inputs[i] = s.genesisRoot[i];
        }
        for (uint256 i = 0; i < 8; i++) {
            _canonical(8 + i, s.finalRoot[i]);
            inputs[8 + i] = s.finalRoot[i];
        }
        _canonical(16, s.numTurns);
        inputs[16] = s.numTurns;
        for (uint256 i = 0; i < 8; i++) {
            _canonical(17 + i, s.chainDigest[i]);
            inputs[17 + i] = s.chainDigest[i];
        }
    }

    /// keccak over the tight 32-byte packing of 8 lanes — the same key
    /// `DreggSettlement.packLanes` uses, so a consumer's recorded root matches
    /// the settlement contract's off-chain index.
    function packLanes(uint32[8] memory lanes) internal pure returns (bytes32) {
        return keccak256(
            abi.encodePacked(
                lanes[0], lanes[1], lanes[2], lanes[3],
                lanes[4], lanes[5], lanes[6], lanes[7]
            )
        );
    }

    function _canonical(uint256 laneIndex, uint32 value) private pure {
        if (uint256(value) >= BABYBEAR_P) {
            revert NonCanonicalLane(laneIndex, value);
        }
    }
}

/// @title IDreggVerifier — the socket a third-party contract imports.
///
/// The stable, VK-rotation-absorbing entry point. An external contract holds a
/// reference to a `DreggVerifier`, calls `verifyStatement(proof, statement)`,
/// and gates its own logic on the returned bool. It never sees a verifying key,
/// an epoch number, or the pairing — those live behind the socket.
interface IDreggVerifier {
    /// The VK-epoch registry this socket wraps (the underlying verifier).
    function registry() external view returns (IGroth16VerifierRegistry);

    /// The epoch a fresh `verifyStatement` checks against (the registry's
    /// current epoch). Advances by an `advanceEpoch` tx on the registry — a
    /// rotation the consumer never has to react to.
    function currentEpoch() external view returns (uint256);

    /// Verify a DREGG attestation against the CURRENT VK epoch. Returns true
    /// iff `proof` is a valid DREGG wrap proof of the (raw, pre-encoded) 25-lane
    /// statement. Fail-closed: false on a failed pairing, an unset epoch, a
    /// non-canonical public input, or a codeless registry.
    function verifyDreggAttestation(
        DreggAttestation.Proof calldata proof,
        uint256[25] calldata publicInputs
    ) external view returns (bool);

    /// Ergonomic form: verify against a TYPED statement (the socket encodes the
    /// 25 lanes). Reverts `NonCanonicalLane` if the statement is ill-formed;
    /// otherwise returns the accept/reject bool. This is the call an external
    /// consumer typically makes.
    function verifyStatement(
        DreggAttestation.Proof calldata proof,
        DreggAttestation.Statement calldata statement
    ) external view returns (bool);

    /// Verify against a TARGETED epoch's VK — for a proof minted under an old VK
    /// that is still valid at its epoch after the registry pointer advanced.
    function verifyStatementAtEpoch(
        uint256 epoch,
        DreggAttestation.Proof calldata proof,
        DreggAttestation.Statement calldata statement
    ) external view returns (bool);
}

/// @title DreggVerifier — the concrete socket.
///
/// Wraps an `IGroth16VerifierRegistry` (the VK-epoch registry). Deploy ONE per
/// DREGG instance you want to expose; every external consumer on the chain
/// points at it. Rotating DREGG's VK is an `advanceEpoch` tx on the registry —
/// this socket and all its consumers are untouched.
contract DreggVerifier is IDreggVerifier {
    IGroth16VerifierRegistry public immutable _registry;

    error RegistryHasNoCode(address registry);

    constructor(IGroth16VerifierRegistry registry_) {
        // Fail closed: a codeless registry would make the staticcalls below
        // "succeed" and could accept anything. (Same census-flagged pattern the
        // settlement contract refuses.)
        if (address(registry_).code.length == 0) {
            revert RegistryHasNoCode(address(registry_));
        }
        _registry = registry_;
    }

    function registry() external view returns (IGroth16VerifierRegistry) {
        return _registry;
    }

    function currentEpoch() external view returns (uint256) {
        return _registry.currentEpoch();
    }

    function verifyDreggAttestation(
        DreggAttestation.Proof calldata proof,
        uint256[25] calldata publicInputs
    ) external view returns (bool) {
        // Targets the registry's CURRENT epoch — VK rotation absorbed.
        return _registry.verifyProof(
            proof.a, proof.b, proof.c,
            proof.commitments, proof.commitmentPok,
            publicInputs
        );
    }

    function verifyStatement(
        DreggAttestation.Proof calldata proof,
        DreggAttestation.Statement calldata statement
    ) external view returns (bool) {
        uint256[25] memory inputs = DreggAttestation.encode(statement);
        return _registry.verifyProof(
            proof.a, proof.b, proof.c,
            proof.commitments, proof.commitmentPok,
            inputs
        );
    }

    function verifyStatementAtEpoch(
        uint256 epoch,
        DreggAttestation.Proof calldata proof,
        DreggAttestation.Statement calldata statement
    ) external view returns (bool) {
        uint256[25] memory inputs = DreggAttestation.encode(statement);
        return _registry.verifyProofAtEpoch(
            epoch,
            proof.a, proof.b, proof.c,
            proof.commitments, proof.commitmentPok,
            inputs
        );
    }
}
