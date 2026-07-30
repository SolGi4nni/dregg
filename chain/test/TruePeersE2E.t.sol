// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {DreggPeerRegistry} from "../contracts/DreggPeerRegistry.sol";
import {IDreggPeerRegistry} from "../contracts/IDreggPeerRegistry.sol";
import {DreggProofISM} from "../contracts/DreggProofISM.sol";
import {IInterchainSecurityModule} from "../contracts/IInterchainSecurityModule.sol";
import {DreggDVN} from "../contracts/DreggDVN.sol";
import {IReceiveUln} from "../contracts/ILayerZeroDVN.sol";
import {DreggSettlement} from "../contracts/DreggSettlement.sol";
import {AcceptingPeerVerifier, RejectingPeerVerifier} from "./DreggPeerRegistry.t.sol";
import {MockReceiveUln} from "./DreggDVN.t.sol";
import {MockGroth16Verifier25} from "./DreggSettlement.t.sol";
import {DreggSettlementVK} from "../contracts/DreggSettlementVK.sol";

/// TRUE PEERS, INTERACTING — the whole cross-chain flow proven as ONE scenario.
///
/// The pieces exist separately (a peer-finality registry, a Hyperlane ISM, a
/// LayerZero DVN, dregg's own settlement surface). This file wires them into a
/// single narrative and proves the load-bearing claim end to end:
///
///     A MESSAGE CROSSES ONLY WHERE A FINALITY PROOF HAS BEEN VERIFIED.
///
/// Chain X here is COSMOS (chainId 118, SLIP-44 ATOM). The flow:
///   (a) Cosmos submits a light-client finality proof → `DreggPeerRegistry`
///       records `provenPeerRoot(118, H) = R` (the accepting peer verifier stands
///       in for the pairing, exactly as the sibling suites do; the pairing
///       SOUNDNESS is the pinned verifier's job).
///   (b) A cross-chain message from Cosmos, keccak-Merkle-included under that
///       EXACT proven root R, is presented to `DreggProofISM` → it ATTESTS, and
///       it attests ONLY because R is proven.
///   (c) A message under an UNPROVEN root, the WRONG source chain, the ZERO root
///       (THE NOMAD LAW), or a leaf NOT included under R is REFUSED.
///   (d) The symmetric direction exists: `DreggSettlement` records DREGG's OWN
///       proven root (dregg proving its state to peers) — the mirror of the peer
///       registry — and the DVN gives the stateful RECEIPT for a crossing.
///
/// The headline test does (a)→(b) as a strict BEFORE/AFTER with the SAME
/// (root, proof, message): the ONLY state change between "refused" and
/// "attested" is the finality proof. That is the "true peers interact" proof.
///
/// ## Dreggic (verified here, not just asserted in prose)
///
///   * Authority is the PROOF, never an owner/committee: submission is
///     permissionless (a random address advances a root); a forged proof
///     (rejecting verifier) records nothing and NOTHING crosses. There is no
///     owner override anywhere on the accept path.
///   * Every accept leaves a RECEIPT: the registry emits `PeerFinalityProven`
///     (the finality fact) AND `PeerProofReceipt` (the exercised proof's keccak
///     digest bound to the (chainId, height, root) it authorized); the DVN emits
///     `PayloadAttested` (the message-crossing receipt naming the proven root +
///     the payload it authorized).
///
/// ## NAMED RESIDUALS (honest — not laundered green)
///
///   * STATEFUL-ISM RECEIPT: `DreggProofISM.verify` is a `view` (the ISM's
///     boolean gate emits nothing). The message-crossing RECEIPT therefore comes
///     from the DVN's stateful `attestPayload` path (leg d). A stateful-ISM
///     variant that emits its own receipt is a prior-flagged follow-up, not built
///     here.
///   * INCLUSION-UNDER-R SOUNDNESS (keccak-binary vs MPT): the inclusion gate is
///     a keccak Merkle fold, SOUND iff the proven peer root R is itself a keccak
///     message-commitment root the peer light-client proof exposes. If the pinned
///     peer VK instead attests a finalized EXECUTION STATE root, inclusion needs
///     an MPT storage proof under that state root, not this keccak fold. Stated on
///     `DreggProofISM` / `DreggDVN`; this scenario is agnostic to which the VK
///     commits (the registry records whatever 32-byte root the VK attests).
///   * OUTBOUND (dregg→peer) MESSAGE LEG: `DreggSettlement.isProvenMessageRoot`
///     is fail-closed forever (the 25-lane proof binds no outbound-message
///     commitment). The INBOUND (peer→dregg) message leg is live (this file); the
///     outbound leg is the standing dregg-circuit obligation (leg d asserts the
///     fail-closed polarity rather than faking it).
///
/// ## Deeper dreggic-UX ideas (noted as follow-ups, not built)
///
///   * TURN-RECEIPT SEMANTICS: fold the crossing receipt into a turn-shaped
///     record (a proof-carrying token exercised over owned state, leaving a
///     receipt) so a crossing is a first-class turn, not just an event.
///   * CAP-ATTENUATION ON THE ATTESTATION: attenuate the attested capability
///     (e.g. bound to a single recipient / a value ceiling / an expiry height) so
///     a proven root authorizes a NARROWED crossing, not a blanket one.
contract TruePeersE2ETest is Test {
    // Peer chain identifiers (the deploy-pinned convention: EIP-155 for EVM,
    // SLIP-44 coin type for non-EVM peers). Chain X = Cosmos.
    uint256 constant COSMOS = 118; // SLIP-44 ATOM
    uint256 constant ETH = 1; // EIP-155 ETH mainnet (the "wrong chain" foil)

    bytes32 constant VK_HASH = keccak256("dregg-peer-lightclient-vk-v1");
    /// ⚑ WAS `keccak256("dregg-settlement-vk-v1")` until 2026-07-30 — a hash of
    /// a LABEL that `DreggSettlement` accepted because nothing compared the pin.
    bytes32 constant SETTLEMENT_VK_HASH = DreggSettlementVK.VK_DIGEST;

    // A representative Cosmos finalized height.
    uint64 constant H = 19_000_000;

    // The four inbound (Cosmos→dregg) messages the finalized tree commits to.
    bytes constant MSG0 = "cosmos->dregg: transfer 100 ATOM to alice";
    bytes constant MSG1 = "cosmos->dregg: message one";
    bytes constant MSG2 = "cosmos->dregg: message two";
    bytes constant MSG3 = "cosmos->dregg: message three";

    // DVN packet fixtures.
    bytes constant HEADER = hex"0102030405060708";
    uint64 constant CONF = 15;

    AcceptingPeerVerifier verifier;
    DreggPeerRegistry peers;
    DreggProofISM ism;
    MockReceiveUln uln;
    DreggDVN dvn;

    // Re-declared for vm.expectEmit (topic hashes match the contracts').
    event PeerFinalityProven(
        uint256 indexed srcChainId,
        uint64 indexed height,
        bytes32 indexed finalizedRoot,
        address relayer
    );
    event PeerRootAdvanced(
        uint256 indexed srcChainId,
        bytes32 oldRoot,
        bytes32 newRoot,
        uint64 height
    );
    event PeerProofReceipt(
        uint256 indexed srcChainId,
        uint64 indexed height,
        bytes32 indexed finalizedRoot,
        bytes32 proofDigest,
        address relayer
    );
    event PayloadAttested(
        uint256 indexed srcChainId,
        bytes32 indexed root,
        bytes32 indexed payloadHash,
        uint64 confirmations,
        uint256 leafIndex
    );

    function setUp() public {
        verifier = new AcceptingPeerVerifier();
        peers = new DreggPeerRegistry(verifier, VK_HASH);
        ism = new DreggProofISM(peers);
        uln = new MockReceiveUln();
        dvn = new DreggDVN(peers, uln);
    }

    // ==================================================================
    // Proof-word helpers (dummy words; the accepting verifier ignores them,
    // and the capability-receipt digest is computed over exactly these).
    // ==================================================================

    function _a() internal pure returns (uint256[2] memory) {
        return [uint256(1), uint256(2)];
    }
    function _b() internal pure returns (uint256[2][2] memory) {
        return [[uint256(3), uint256(4)], [uint256(5), uint256(6)]];
    }
    function _c() internal pure returns (uint256[2] memory) {
        return [uint256(7), uint256(8)];
    }
    function _cm() internal pure returns (uint256[2] memory) {
        return [uint256(9), uint256(10)];
    }
    function _pok() internal pure returns (uint256[2] memory) {
        return [uint256(11), uint256(12)];
    }

    /// Submit a Cosmos finality proof for `root` at height `h` to `peers`.
    function _proveCosmos(uint64 h, bytes32 root) internal {
        peers.submitPeerFinality(COSMOS, h, root, _a(), _b(), _c(), _cm(), _pok());
    }

    // ==================================================================
    // ISM tree — keccak POSITION-INDEXED (the DreggProofISM fold).
    // ==================================================================

    /// The Cosmos outbound-message tree at height H. `root` is what the Cosmos
    /// light client finalizes; the ISM checks inclusion under it.
    function _ismTree4()
        internal
        pure
        returns (bytes32 root, bytes32 l0, bytes32 l3, bytes32 n01, bytes32 n23)
    {
        l0 = keccak256(MSG0);
        bytes32 l1 = keccak256(MSG1);
        bytes32 l2 = keccak256(MSG2);
        l3 = keccak256(MSG3);
        n01 = keccak256(abi.encodePacked(l0, l1));
        n23 = keccak256(abi.encodePacked(l2, l3));
        root = keccak256(abi.encodePacked(n01, n23));
    }

    /// Mirror of `DreggProofISM._computeRoot` (position-indexed) for fixtures.
    function _ismFold(bytes32 leaf, bytes32[] memory proof, uint256 index)
        internal
        pure
        returns (bytes32)
    {
        bytes32 node = leaf;
        uint256 idx = index;
        for (uint256 i = 0; i < proof.length; i++) {
            if (idx & 1 == 0) {
                node = keccak256(abi.encodePacked(node, proof[i]));
            } else {
                node = keccak256(abi.encodePacked(proof[i], node));
            }
            idx >>= 1;
        }
        return node;
    }

    /// The inclusion proof of MSG0 (leaf 0, index 0) under the ISM tree root.
    function _ismProofForMsg0() internal pure returns (bytes32[] memory p0) {
        (, , , , bytes32 n23) = _ismTree4();
        p0 = new bytes32[](2);
        p0[0] = keccak256(MSG1);
        p0[1] = n23;
    }

    function _ismMeta(uint256 chainId, bytes32 root, bytes32[] memory proof, uint256 idx)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encode(chainId, root, proof, idx);
    }

    // ==================================================================
    // DVN tree — keccak SORTED-PAIR (the DreggDVN fold).
    // ==================================================================

    function _dvnLeaves()
        internal
        pure
        returns (bytes32 l0, bytes32 l1, bytes32 l2, bytes32 l3)
    {
        l0 = keccak256("cosmos->dregg payload zero");
        l1 = keccak256("cosmos->dregg payload one");
        l2 = keccak256("cosmos->dregg payload two");
        l3 = keccak256("cosmos->dregg payload three");
    }

    function _hashPair(bytes32 a, bytes32 b) internal pure returns (bytes32) {
        return a < b
            ? keccak256(abi.encodePacked(a, b))
            : keccak256(abi.encodePacked(b, a));
    }

    function _dvnRoot(bytes32 l0, bytes32 l1, bytes32 l2, bytes32 l3)
        internal
        pure
        returns (bytes32)
    {
        return _hashPair(_hashPair(l0, l1), _hashPair(l2, l3));
    }

    // ==================================================================
    // THE HEADLINE — a message crosses ONLY under a proven finality.
    // Strict BEFORE/AFTER: same root, same proof, same message. The ONLY
    // state change between refusal and attestation is the finality proof.
    // ==================================================================

    function test_TruePeers_MessageCrossesOnlyUnderProvenFinality() public {
        (bytes32 R, , , , ) = _ismTree4();
        bytes32[] memory p0 = _ismProofForMsg0();
        bytes memory meta = _ismMeta(COSMOS, R, p0, 0);

        // Fixture sanity: MSG0 really is included under R at index 0.
        assertEq(_ismFold(keccak256(MSG0), p0, 0), R, "fixture: MSG0 under R");

        // ---- BEFORE: no finality proof ⇒ the message does NOT cross. ----
        assertFalse(peers.isProvenPeerRoot(COSMOS, R), "root unproven pre-finality");
        vm.expectRevert(
            abi.encodeWithSelector(DreggProofISM.UnprovenRoot.selector, COSMOS, R)
        );
        ism.verify(meta, MSG0);

        // ---- THE ONLY STATE CHANGE: verify Cosmos's finality on-chain. ----
        _proveCosmos(H, R);
        assertTrue(peers.isProvenPeerRoot(COSMOS, R), "root proven post-finality");
        assertEq(peers.provenPeerRoot(COSMOS, H), R);

        // ---- AFTER: the SAME (root, proof, message) now crosses. ----
        assertTrue(ism.verify(meta, MSG0), "message crosses under proven finality");
    }

    // ==================================================================
    // LEG (a) — finality submission records the root AND leaves the receipts:
    // the finality fact, the root advance, AND the CAPABILITY RECEIPT (the
    // exercised proof's digest bound to the triple it authorized).
    // ==================================================================

    function test_TruePeers_LegA_FinalityReceiptsAndCapabilityDigest() public {
        (bytes32 R, , , , ) = _ismTree4();

        // The capability receipt's digest is keccak over exactly the proof words.
        bytes32 expectedDigest =
            keccak256(abi.encode(_a(), _b(), _c(), _cm(), _pok()));

        vm.expectEmit(true, true, true, true, address(peers));
        emit PeerFinalityProven(COSMOS, H, R, address(this));
        vm.expectEmit(true, false, false, true, address(peers));
        emit PeerRootAdvanced(COSMOS, bytes32(0), R, H);
        vm.expectEmit(true, true, true, true, address(peers));
        emit PeerProofReceipt(COSMOS, H, R, expectedDigest, address(this));

        _proveCosmos(H, R);

        assertTrue(peers.isProvenPeerRoot(COSMOS, R));
        assertEq(peers.latestPeerRoot(COSMOS), R);
        assertEq(peers.latestPeerHeight(COSMOS), H);
    }

    // ==================================================================
    // LEG (b) — a genuinely-included message attests under the proven root.
    // Both leaf 0 and leaf 3 climb the multi-level path to R.
    // ==================================================================

    function test_TruePeers_LegB_IncludedMessageAttests() public {
        (bytes32 R, bytes32 l0, bytes32 l3, bytes32 n01, bytes32 n23) = _ismTree4();
        _proveCosmos(H, R);

        // leaf 0 (index 0): proof [l1, n23]
        bytes32[] memory p0 = new bytes32[](2);
        p0[0] = keccak256(MSG1);
        p0[1] = n23;
        assertEq(_ismFold(l0, p0, 0), R, "fixture: leaf0");
        assertTrue(ism.verify(_ismMeta(COSMOS, R, p0, 0), MSG0));

        // leaf 3 (index 3): proof [l2, n01]
        bytes32[] memory p3 = new bytes32[](2);
        p3[0] = keccak256(MSG2);
        p3[1] = n01;
        assertEq(_ismFold(l3, p3, 3), R, "fixture: leaf3");
        assertTrue(ism.verify(_ismMeta(COSMOS, R, p3, 3), MSG3));
    }

    // ==================================================================
    // LEG (c) — the refusal battery. A message under an unproven/zero/wrong
    // root, or not included under a proven root, NEVER crosses.
    // ==================================================================

    function test_TruePeers_LegC_RefusalBattery() public {
        (bytes32 R, , , , bytes32 n23) = _ismTree4();
        _proveCosmos(H, R); // R is now proven for Cosmos only

        bytes32[] memory p0 = new bytes32[](2);
        p0[0] = keccak256(MSG1);
        p0[1] = n23;
        bytes32[] memory empty = new bytes32[](0);

        // (c1) ZERO root — THE NOMAD LAW. Rejected before inclusion is examined.
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggProofISM.UnprovenRoot.selector, COSMOS, bytes32(0)
            )
        );
        ism.verify(_ismMeta(COSMOS, bytes32(0), empty, 0), MSG0);

        // (c2) UNPROVEN (non-zero, never proven) root.
        bytes32 stranger = keccak256("a root Cosmos never finalized");
        assertFalse(peers.isProvenPeerRoot(COSMOS, stranger));
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggProofISM.UnprovenRoot.selector, COSMOS, stranger
            )
        );
        ism.verify(_ismMeta(COSMOS, stranger, p0, 0), MSG0);

        // (c3) WRONG source chain — R is proven for Cosmos, not ETH. A valid
        // root + a valid inclusion path is still refused for the wrong chain.
        assertFalse(peers.isProvenPeerRoot(ETH, R));
        vm.expectRevert(
            abi.encodeWithSelector(DreggProofISM.UnprovenRoot.selector, ETH, R)
        );
        ism.verify(_ismMeta(ETH, R, p0, 0), MSG0);

        // (c4) Root PROVEN, but the message is NOT included under it (forged
        // leaf): the proven-root gate passes, the inclusion gate rejects.
        bytes memory forged = "a message Cosmos never committed";
        bytes32 computed = _ismFold(keccak256(forged), p0, 0);
        assertTrue(computed != R);
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggProofISM.InclusionProofInvalid.selector, R, computed
            )
        );
        ism.verify(_ismMeta(COSMOS, R, p0, 0), forged);
    }

    // ==================================================================
    // LEG (d.1) — the DVN's STATEFUL RECEIPT path (the ISM's view can't emit).
    // Same BEFORE/AFTER polarity, and the on-chain PayloadAttested receipt.
    // ==================================================================

    function test_TruePeers_LegD_DVNStatefulReceipt() public {
        (bytes32 l0, bytes32 l1, bytes32 l2, bytes32 l3) = _dvnLeaves();
        bytes32 R = _dvnRoot(l0, l1, l2, l3);

        bytes32[] memory proof = new bytes32[](2);
        proof[0] = l1;
        proof[1] = _hashPair(l2, l3);
        bytes memory meta = abi.encode(COSMOS, R, proof, uint256(0));

        // BEFORE finality: the DVN refuses and the receive-library is untouched.
        vm.expectRevert(
            abi.encodeWithSelector(DreggDVN.RootNotProven.selector, COSMOS, R)
        );
        dvn.attestPayload(HEADER, l0, CONF, meta);
        assertEq(uln.verifyCount(), 0, "ULN never told on the reject path");

        // Prove Cosmos's finality for this payload root.
        _proveCosmos(H + 1, R);

        // AFTER: the DVN attests, calls the ULN exactly once, and emits the
        // PayloadAttested RECEIPT (the stateful message-crossing receipt).
        vm.expectEmit(true, true, true, true, address(dvn));
        emit PayloadAttested(COSMOS, R, l0, CONF, 0);
        dvn.attestPayload(HEADER, l0, CONF, meta);

        assertEq(uln.verifyCount(), 1, "ULN told exactly once on accept");
        assertEq(uln.lastPayloadHash(), l0);
        assertEq(uln.lastConfirmations(), CONF);
    }

    // ==================================================================
    // LEG (d.2) — the SYMMETRIC (mirror) direction exists: DreggSettlement
    // records DREGG's OWN proven root. Referenced, not rebuilt. Also asserts
    // the OUTBOUND-message residual honestly (fail-closed, not faked green).
    // ==================================================================

    function test_TruePeers_LegD_MirrorSettlementSurfaceExists() public {
        MockGroth16Verifier25 sv = new MockGroth16Verifier25();
        uint32[8] memory genesis = _mkLanes(1);
        DreggSettlement settlement =
            new DreggSettlement(sv, SETTLEMENT_VK_HASH, genesis);

        // The mirror of isProvenPeerRoot: dregg's own genesis root is proven on
        // its settlement surface (dregg proving ITS state, the reverse of the
        // peer registry proving a PEER's state). Together = TRUE PEERS.
        bytes32 gRoot = settlement.genesisAnchor();
        assertTrue(
            settlement.isProvenRoot(gRoot),
            "dregg's own root proven on the mirror surface"
        );
        assertEq(settlement.provenRoot(), gRoot);
        // THE NOMAD LAW holds on the mirror too.
        assertFalse(settlement.isProvenRoot(bytes32(0)));

        // NAMED RESIDUAL (honest): the OUTBOUND (dregg→peer) MESSAGE leg is
        // fail-closed forever — the 25-lane settlement proof binds no
        // outbound-message commitment, so no message root is provable this
        // direction. The INBOUND (peer→dregg) message leg is live (this file).
        assertFalse(
            settlement.isProvenMessageRoot(gRoot),
            "outbound message leg fail-closed (named residual)"
        );
        assertFalse(
            settlement.isProvenMessageRoot(keccak256("any outbound root")),
            "outbound message leg fail-closed for every input"
        );
    }

    // ==================================================================
    // DREGGIC — the authority is the PROOF, never an owner/committee.
    // ==================================================================

    function test_TruePeers_AuthorityIsTheProof_NotOwnerOrCommittee() public {
        (bytes32 R, , , , ) = _ismTree4();

        // (1) PERMISSIONLESS: a random, unprivileged address advances the root.
        // The proof is the capability; the caller is recorded only as relayer.
        address randomRelayer = address(0xBEEF);
        vm.expectEmit(true, true, true, true, address(peers));
        emit PeerFinalityProven(COSMOS, H, R, randomRelayer);
        vm.prank(randomRelayer);
        _proveCosmos(H, R);
        assertTrue(peers.isProvenPeerRoot(COSMOS, R));

        // (2) NO valid proof ⇒ NOTHING crosses, for ANY caller. A rejecting
        // verifier (a forged/invalid proof) records no root, and there is no
        // owner override to force it. The same message then cannot cross.
        DreggPeerRegistry rejPeers =
            new DreggPeerRegistry(new RejectingPeerVerifier(), VK_HASH);
        DreggProofISM rejIsm = new DreggProofISM(rejPeers);

        vm.expectRevert(IDreggPeerRegistry.ProofRejected.selector);
        rejPeers.submitPeerFinality(COSMOS, H, R, _a(), _b(), _c(), _cm(), _pok());
        assertFalse(rejPeers.isProvenPeerRoot(COSMOS, R));

        bytes32[] memory empty = new bytes32[](0);
        vm.expectRevert(
            abi.encodeWithSelector(DreggProofISM.UnprovenRoot.selector, COSMOS, R)
        );
        rejIsm.verify(abi.encode(COSMOS, R, empty, uint256(0)), MSG0);
    }

    // ------------------------------------------------------------------
    // Helper: canonical BabyBear genesis lanes for the mirror settlement.
    // ------------------------------------------------------------------
    function _mkLanes(uint32 seed) internal pure returns (uint32[8] memory l) {
        uint32 P = 2013265921; // BabyBear prime
        for (uint32 i = 0; i < 8; i++) {
            l[i] = (seed * 7919 + i * 104729 + 1) % P;
        }
    }
}
