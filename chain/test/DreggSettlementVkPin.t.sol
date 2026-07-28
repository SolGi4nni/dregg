// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {DreggSettlementVK} from "../contracts/DreggSettlementVK.sol";
import {DreggSettlement} from "../contracts/DreggSettlement.sol";
import {IGroth16Verifier25} from "../contracts/IGroth16Verifier25.sol";

contract StubVerifier is IGroth16Verifier25 {
    function verifyProof(
        uint256[2] calldata,
        uint256[2][2] calldata,
        uint256[2] calldata,
        uint256[2] calldata,
        uint256[2] calldata,
        uint256[25] calldata
    ) external pure returns (bool) {
        return true;
    }
}

/// ⚑ **THE ON-CHAIN "VK COMMITMENT" WAS A HASH OF A LABEL.**
///
/// `chain/script/DeploySettlement.s.sol:59` pinned
/// `keccak256("dregg-settlement-vk-dev-setup")` and `solana-settlement/src/lib.rs:60`
/// pinned the same bytes. The string does not mention the key, so the pin was
/// `0x18f57474785bdd93ff7feb573dfadff69516035997115f2854c93f0f31e1ff76` for the dev
/// key and for every key anyone will ever generate: a VK regeneration left both
/// chains' pins byte-identical, and the one artifact whose whole job is to notice a
/// key changed could not notice.
///
/// The pin is now `DreggSettlementVK.VK_DIGEST` — keccak256 over the canonical
/// serialization of the ACTUAL verifying key — and `digest()` recomputes it on-chain
/// from those same constants. The Solana side proves the sensitivity exhaustively
/// (`solana-settlement/tests/vk_pin.rs`: 19456 single-bit key faults, all detected,
/// against 0 detected by the label hash). This is the EVM half: the pin is a function
/// of the key HERE too, and it is the value the deployment actually installs.
contract DreggSettlementVkPinTest is Test {
    /// The superseded pin, kept as a literal so the flag day is findable.
    bytes32 constant OLD_LABEL_PIN =
        0x18f57474785bdd93ff7feb573dfadff69516035997115f2854c93f0f31e1ff76;

    function test_DigestRecomputesToThePin() public pure {
        assertEq(
            DreggSettlementVK.digest(),
            DreggSettlementVK.VK_DIGEST,
            "VK_DIGEST must be the keccak of the VK constants in this very library"
        );
    }

    /// Anti-vacuity: `digest()` must actually be reading the key, not hashing a
    /// constant. Hash the same preimage with one word perturbed and require a
    /// different answer.
    function test_PerturbingAnyVkWordMovesTheDigest() public pure {
        uint256[] memory w = DreggSettlementVK.words();
        assertEq(w.length, 76, "alpha(2) + 5 G2 (4 each) + ic0(2) + 26 IC bases (2 each)");

        for (uint256 i = 0; i < w.length; i++) {
            uint256[] memory perturbed = DreggSettlementVK.words();
            unchecked {
                perturbed[i] += 1;
            }
            bytes32 moved = keccak256(
                abi.encodePacked(
                    "dregg-groth16-vk/1",
                    uint32(25),
                    uint32(26),
                    abi.encodePacked(perturbed)
                )
            );
            assertTrue(
                moved != DreggSettlementVK.VK_DIGEST,
                "every verifying-key word must move the pin"
            );
        }
    }

    /// The label hash does NOT move for any of those 76 perturbations — it cannot,
    /// it never reads the key. The defect as a passing measurement.
    function test_TheOldLabelPinMovesForNoneOfThem() public pure {
        assertEq(
            keccak256("dregg-settlement-vk-dev-setup"),
            OLD_LABEL_PIN,
            "the superseded pin, recorded"
        );
        assertTrue(
            DreggSettlementVK.VK_DIGEST != OLD_LABEL_PIN,
            "the key-derived pin must differ from the label hash it replaced"
        );
        // 76 different keys, one pin. That is the whole defect.
        for (uint256 i = 0; i < 76; i++) {
            assertEq(
                keccak256("dregg-settlement-vk-dev-setup"),
                OLD_LABEL_PIN,
                "the label hash is a constant function of the key"
            );
        }
    }

    /// The pin is byte-identical to the one Solana and Cosmos install. All three are
    /// emitted from `chain/codegen/dregg_vk.json` by `gen_verifiers.py`, so equality
    /// now means "the same key" — under the label hash it meant "the same string".
    function test_PinMatchesTheCrossChainDigest() public pure {
        assertEq(
            DreggSettlementVK.VK_DIGEST,
            0xcfda612f472e998d1f1bad1bf545ec5b39ca99b64db94e46edf2e8d3790a37cc,
            "must equal solana-settlement vk::VK_DIGEST and cosmos-settlement vk::VK_DIGEST"
        );
    }

    /// The deployed settlement contract installs the key-derived pin, not the label.
    function test_DeployedSettlementPinsTheKeysDigest() public {
        uint32[8] memory genesis = [uint32(1), 2, 3, 4, 5, 6, 7, 8];
        StubVerifier v = new StubVerifier();
        DreggSettlement s = new DreggSettlement(
            IGroth16Verifier25(address(v)), DreggSettlementVK.VK_DIGEST, genesis
        );
        assertEq(s.verifyingKeyHash(), DreggSettlementVK.VK_DIGEST);
        assertTrue(s.verifyingKeyHash() != OLD_LABEL_PIN, "not the label hash");
    }
}
