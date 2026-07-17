// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {DreggLaunchpad} from "../contracts/launchpad/DreggLaunchpad.sol";
import {DreggLaunchToken} from "../contracts/launchpad/DreggLaunchToken.sol";
import {DreggSolventPool} from "../contracts/launchpad/DreggSolventPool.sol";
import {DreggDeployerGate} from "../contracts/launchpad/DreggDeployerGate.sol";
import {ILaunchEligibility} from "../contracts/launchpad/ILaunchEligibility.sol";
import {IClearingAttestor} from "../contracts/launchpad/IClearingAttestor.sol";
import {IDeployerGate} from "../contracts/launchpad/IDeployerGate.sol";

/// # THE P0-PARITY LAUNCH LOOP — `docs/deos/P0-DREGGIC.md` Phase 0
///
/// p0 Systems runs the loop **create → launch → trade → lock** as a convenience
/// layer: an AI emits an unaudited token and a deploy button shoves it onto
/// pump.fun/Bags.fm, where the rug doors live in someone else's contract. This
/// suite drives the SAME loop on the dregg pieces — **create → gate → launch →
/// clear → lock** — end to end, and asserts p0's three inherited abuses are
/// UNCONSTRUCTABLE rather than mitigated.
///
/// Every step composes a landed piece; nothing here is a stand-in mechanism:
///
/// | Step | The piece | Where it lives |
/// |------|-----------|----------------|
/// | CREATE | the token-factory's **real** VERIFIED-SAFE artifact (spec → FV'd emit → Halmos-proven cap → audit gate) | `tools/token-factory/artifacts/GOOD/` — READ AND HASHED BY THIS TEST |
/// | GATE | `DreggDeployerGate` (pluggable bond / interview / audit arms) via the `registerLaunch` hook | `contracts/launchpad/DreggDeployerGate.sol` |
/// | LAUNCH | sealed commit→reveal (no peek / no late-switch) | `DreggLaunchpad.commitBid` / `revealBid` |
/// | CLEAR | permutation-checked uniform-price clearing + settlement + graduation into the solvency-floored pool | `DreggLaunchpad.finalizeClearing` / `settleBid` / `graduate` |
/// | LOCK | the disclosed vesting cliff on the creator allocation | `DreggLaunchpad.claimCreatorAllocation` |
///
/// ## The three abuses, each refused by a NAMED reason
/// - **(a) launch-block sniping** → `test_Abuse_A_SnipingRefused_NoTimePriorityEdge`:
///   the sealed book + one uniform price make the clearing ORDER-INVARIANT (proved
///   here by running the identical book in opposite order and getting identical
///   fills at an identical price), so there is no earliest-block edge to buy; and a
///   late/uncommitted sniper is refused `NotCommitPhase` / `NoCommit`.
/// - **(b) hidden supply** → `test_Abuse_B_HiddenSupplyRefused_CapIsAbsolute`:
///   `AlreadyMinted` / `CapExceeded` / `SupplyDoesNotClose`.
/// - **(c) LP / owner drain** → `test_Abuse_C_LpAndOwnerDrainRefused`:
///   `PoolFloorBreached` / `CreatorLockActive` / `AlreadyInitialized`.
///
/// Both polarities throughout, and the HONEST pole runs first
/// (`test_1_HonestLaunch_CreateGateLaunchClearLock`) — a negative asserted against
/// a loop that never worked proves nothing.
contract P0ParityLaunchLoopTest is Test {
    DreggLaunchpad pad; // the DEPLOYER-GATED launchpad
    DreggDeployerGate gate;

    address admin = makeAddr("admin"); // gate admin / attester / auditor / slasher
    address creator = makeAddr("creator"); // the honest, gated deployer
    address scammer = makeAddr("scammer"); // the ungated deployer
    address alice = makeAddr("alice");
    address bob = makeAddr("bob");
    address carol = makeAddr("carol");
    address dave = makeAddr("dave");

    uint64 constant COMMIT_DUR = 100;
    uint64 constant REVEAL_DUR = 100;
    uint256 constant G = 1e9; // gwei — the price unit
    uint256 constant MIN_BOND = 10 ether;

    // Mirrored locally so `_auditCap` / `_bondCap` are PURE: a capability built by
    // reading `gate.ARM_*()` would be an external call in an argument position,
    // which silently consumes a pending `vm.expectRevert`. `setUp` asserts the
    // mirrors are the gate's real arm ids, so they cannot drift into fiction.
    uint8 constant ARM_BOND = 0;
    uint8 constant ARM_AUDIT = 3;

    /// The REAL factory artifacts this test composes (read from disk, hashed).
    string constant GOOD_ARTIFACT = "../tools/token-factory/artifacts/GOOD/GOOD.verified-safe.md";
    string constant RUG_ARTIFACT = "../tools/token-factory/artifacts/RMOON/RMOON.rejected.md";

    /// The cap the factory's GOOD spec discloses and Halmos PROVED (`"cap": 1000000000`).
    /// The launch's disclosed `totalSupply` must be exactly this — the audited
    /// token IS the launched token.
    uint256 constant FACTORY_CAP = 1_000_000_000;

    function setUp() public {
        // The gate: bond OR cleared-audit accepted. The arms stay PLUGGABLE — the
        // launchpad pins the gate, never an arm.
        vm.prank(admin);
        gate = new DreggDeployerGate(admin, MIN_BOND);
        vm.prank(admin);
        gate.setAcceptedArms(uint8((1 << ARM_BOND) | (1 << ARM_AUDIT)));
        assertEq(gate.ARM_BOND(), ARM_BOND, "arm mirror is the real bond arm");
        assertEq(gate.ARM_AUDIT(), ARM_AUDIT, "arm mirror is the real audit arm");

        // The launchpad pins that gate at construction, immutably.
        pad = new DreggLaunchpad(IDeployerGate(address(gate)));
        assertEq(address(pad.deployerGate()), address(gate), "gate pinned immutably at construction");

        vm.deal(creator, 100 ether);
        vm.deal(scammer, 100 ether);
        vm.deal(alice, 100 ether);
        vm.deal(bob, 100 ether);
        vm.deal(carol, 100 ether);
        vm.deal(dave, 100 ether);
    }

    // ══════════════════════════════════════════════════════════════════════════
    // CREATE — the factory artifact is the launch's token
    // ══════════════════════════════════════════════════════════════════════════

    /// The disclosed schedule for the factory's GOOD token: the cap is EXACTLY the
    /// audited spec's cap, and the parts close (no hidden supply).
    /// 1B total = 850M sale + 50M creator (5%, the spec's `creator_allocation_bps`)
    /// + 100M pool.
    function _goodSchedule() internal view returns (DreggLaunchpad.Schedule memory s) {
        s = DreggLaunchpad.Schedule({
            totalSupply: FACTORY_CAP,
            saleSupply: 850_000_000,
            creatorAllocation: 50_000_000,
            poolAllocation: 100_000_000,
            graduationBps: 5000,
            creatorLockUntil: uint64(block.timestamp) + 10_000,
            reservePrice: 1 * G
        });
    }

    function _paramsHash(DreggLaunchpad.Schedule memory s) internal pure returns (bytes32) {
        return keccak256(abi.encode(s));
    }

    /// The factory's VERIFIED-SAFE bundle, hashed — the audit-arm report hash.
    /// Read from the REAL artifact `tools/token-factory/token-factory` emitted.
    function _factoryVerifiedSafeReport() internal view returns (bytes32) {
        string memory artifact = vm.readFile(GOOD_ARTIFACT);
        // The factory GATED it: Halmos proved the cap, no rug door but the
        // disclosed one-shot mint.
        assertTrue(_contains(artifact, "**Verdict: VERIFIED-SAFE.**"), "factory artifact must be VERIFIED-SAFE");
        // The audited cap IS the cap this launch discloses.
        assertTrue(_contains(artifact, '"cap": 1000000000'), "audited spec cap == the launch's disclosed totalSupply");
        return keccak256(bytes(artifact));
    }

    /// The auditor clears the factory bundle FOR THIS EXACT DISCLOSURE. This is
    /// the create→gate seam: the artifact proves the TOKEN (Halmos cap, no doors),
    /// the schedule discloses the SUPPLY SPLIT, and the auditor attests the pair —
    /// so the capability authorizes this launch and nothing else.
    function _clearFactoryAuditFor(DreggLaunchpad.Schedule memory s) internal returns (bytes32 reportHash) {
        reportHash = _factoryVerifiedSafeReport();
        vm.prank(admin); // the auditor oracle
        gate.attestAuditFor(reportHash, _paramsHash(s), true);
    }

    function _auditCap(bytes32 reportHash) internal pure returns (bytes memory) {
        return abi.encode(ARM_AUDIT, abi.encode(reportHash));
    }

    function _bondCap() internal pure returns (bytes memory) {
        return abi.encode(ARM_BOND, bytes(""));
    }

    function _register(address who, DreggLaunchpad.Schedule memory s, bytes memory capability)
        internal
        returns (uint256 id)
    {
        vm.prank(who);
        id = pad.registerLaunch(
            "Good Capped Token",
            "GOOD",
            s,
            COMMIT_DUR,
            REVEAL_DUR,
            ILaunchEligibility(address(0)),
            IClearingAttestor(address(0)),
            capability
        );
    }

    function _commit(uint256 id, address who, uint256 price, uint256 qty, bytes32 salt) internal {
        bytes32 seal = pad.sealOf(price, qty, salt, who);
        vm.prank(who);
        pad.commitBid{value: price * qty}(id, seal, "");
    }

    function _reveal(uint256 id, address who, uint256 price, uint256 qty, bytes32 salt) internal {
        vm.prank(who);
        pad.revealBid(id, price, qty, salt);
    }

    // ══════════════════════════════════════════════════════════════════════════
    // 1 — THE HONEST POLE, FIRST: create → gate → launch → clear → lock
    // ══════════════════════════════════════════════════════════════════════════

    function test_1_HonestLaunch_CreateGateLaunchClearLock() public {
        // ── CREATE: the token-factory's VERIFIED-SAFE artifact, audit-cleared and
        //    BOUND to this disclosure.
        DreggLaunchpad.Schedule memory s = _goodSchedule();
        bytes32 reportHash = _clearFactoryAuditFor(s);
        assertTrue(gate.auditCleared(reportHash), "the factory bundle cleared the audit");
        assertEq(gate.auditScope(reportHash), _paramsHash(s), "the clearance is bound to THIS schedule");

        // ── GATE: the capability admits the deployer; registration is a turn.
        uint256 id = _register(creator, s, _auditCap(reportHash));
        assertEq(uint256(pad.phaseOf(id)), uint256(DreggLaunchpad.Phase.Commit), "launch is live");
        // The disclosure is publicly re-derivable, and it IS the capability's scope.
        assertTrue(pad.checkSchedule(id, s), "schedule matches the on-chain commitment");
        assertEq(pad.scheduleCommitOf(id), _paramsHash(s), "scheduleCommit == the gated capability's scope");

        // The launched token is the FV'd, factory-audited template: hard cap ==
        // the disclosed supply == the artifact's Halmos-proven cap, minted once.
        DreggLaunchToken tok = DreggLaunchToken(pad.tokenOf(id));
        assertEq(tok.cap(), FACTORY_CAP * pad.TOKEN_UNIT(), "token cap == the audited disclosed cap");
        assertEq(tok.totalSupply(), tok.cap(), "the single disclosed mint minted the whole cap");
        assertTrue(tok.minted(), "one-shot mint latched");

        // ── LAUNCH: sealed commits. Nothing about a bid is observable yet.
        _commit(id, alice, 5 * G, 400_000_000, keccak256("a"));
        _commit(id, bob, 4 * G, 400_000_000, keccak256("b"));
        _commit(id, carol, 3 * G, 400_000_000, keccak256("c"));
        _commit(id, dave, 2 * G, 400_000_000, keccak256("d"));
        (, , uint256 hiddenPrice, uint256 hiddenQty, , , ) = pad.getBid(id, alice);
        assertEq(hiddenPrice, 0, "no bid price is readable during the commit window");
        assertEq(hiddenQty, 0, "no bid size is readable during the commit window");

        // Reveal (scrambled order — it does not matter, see abuse (a)).
        vm.warp(block.timestamp + COMMIT_DUR);
        _reveal(id, dave, 2 * G, 400_000_000, keccak256("d")); // index 0
        _reveal(id, alice, 5 * G, 400_000_000, keccak256("a")); // index 1
        _reveal(id, carol, 3 * G, 400_000_000, keccak256("c")); // index 2
        _reveal(id, bob, 4 * G, 400_000_000, keccak256("b")); // index 3

        // ── CLEAR: one uniform price for the whole book. Sale = 850M →
        //    alice 400M, bob 400M, carol 50M (marginal), dave 0. Price = 3 gwei.
        vm.warp(block.timestamp + REVEAL_DUR);
        uint256[] memory order = new uint256[](4);
        order[0] = 1; // alice 5
        order[1] = 3; // bob 4
        order[2] = 2; // carol 3
        order[3] = 0; // dave 2
        pad.finalizeClearing(id, order, "");
        assertEq(pad.clearingPriceOf(id), 3 * G, "ONE uniform price = the marginal winning bid");
        assertEq(pad.soldQtyOf(id), 850_000_000, "the whole disclosed sale supply cleared");

        // Settle: EVERY winner pays the SAME price, whatever they bid.
        _settle(id, alice, 400_000_000, 5 * G, 400_000_000, tok);
        _settle(id, bob, 400_000_000, 4 * G, 400_000_000, tok);
        _settle(id, carol, 50_000_000, 3 * G, 400_000_000, tok); // marginal partial fill
        _settle(id, dave, 0, 2 * G, 400_000_000, tok); // no fill → whole deposit back

        // GRADUATE into the provably-solvent pool with the DISCLOSED seed.
        (uint256 qSeed, uint256 tSeed) = pad.graduationSeed(id);
        assertEq(qSeed, (3 * G * 850_000_000 * 5000) / 10000, "quote seed = disclosed 50% of the canonical proceeds");
        assertEq(tSeed, 100_000_000 * pad.TOKEN_UNIT(), "token seed = the disclosed pool allocation");
        DreggSolventPool pool = DreggSolventPool(pad.graduate(id, qSeed, tSeed));
        assertTrue(pad.isGraduated(id), "the raise graduated into a liquid market");

        // The market TRADES (the honest pole of the solvency tooth).
        vm.prank(alice);
        uint256 out = pool.buy{value: 0.01 ether}(0);
        assertGt(out, 0, "the graduated pool clears a real buy");

        // ── LOCK: the creator allocation is held by the DISCLOSED cliff.
        vm.prank(creator);
        vm.expectRevert(abi.encodeWithSelector(DreggLaunchpad.CreatorLockActive.selector, s.creatorLockUntil));
        pad.claimCreatorAllocation(id);

        vm.warp(s.creatorLockUntil); // …and it releases at the cliff, exactly as disclosed.
        vm.prank(creator);
        pad.claimCreatorAllocation(id);
        assertEq(
            tok.balanceOf(creator), s.creatorAllocation * pad.TOKEN_UNIT(), "creator alloc released at the disclosed cliff"
        );

        // The loop closed: create → gate → launch → clear → lock, all real.
    }

    /// Settle `who` and assert the UNIFORM-price payment: everyone pays the
    /// clearing price, not their bid.
    function _settle(
        uint256 id,
        address who,
        uint256 expFill,
        uint256 bidPrice,
        uint256 bidQty,
        DreggLaunchToken tok
    ) internal {
        uint256 ethBefore = who.balance;
        uint256 clearing = pad.clearingPriceOf(id);
        pad.settleBid(id, who);
        uint256 payment = clearing * expFill;
        uint256 refund = bidPrice * bidQty - payment;
        assertEq(who.balance - ethBefore, refund, "refund = deposit - UNIFORM payment (not the bid)");
        assertEq(tok.balanceOf(who), expFill * pad.TOKEN_UNIT(), "token award = the cleared fill");
    }

    // ══════════════════════════════════════════════════════════════════════════
    // 2 — THE GATE, BOTH POLARITIES (the `registerLaunch` hook)
    // ══════════════════════════════════════════════════════════════════════════

    /// An UNGATED deployer cannot register at all — the p0 "deploy button" is
    /// exactly what is refused here, by name.
    function test_2_Gate_UngatedDeployerRefused() public {
        DreggLaunchpad.Schedule memory s = _goodSchedule();

        // No capability at all.
        vm.prank(scammer);
        vm.expectRevert(abi.encodeWithSelector(DreggLaunchpad.DeployerNotGated.selector, scammer));
        pad.registerLaunch(
            "Rug", "RUG", s, COMMIT_DUR, REVEAL_DUR, ILaunchEligibility(address(0)), IClearingAttestor(address(0)), ""
        );

        // A bond arm with NO bond posted.
        vm.prank(scammer);
        vm.expectRevert(abi.encodeWithSelector(DreggLaunchpad.DeployerNotGated.selector, scammer));
        pad.registerLaunch(
            "Rug",
            "RUG",
            s,
            COMMIT_DUR,
            REVEAL_DUR,
            ILaunchEligibility(address(0)),
            IClearingAttestor(address(0)),
            _bondCap()
        );

        // An audit arm citing a report the auditor never cleared.
        vm.prank(scammer);
        vm.expectRevert(abi.encodeWithSelector(DreggLaunchpad.DeployerNotGated.selector, scammer));
        pad.registerLaunch(
            "Rug",
            "RUG",
            s,
            COMMIT_DUR,
            REVEAL_DUR,
            ILaunchEligibility(address(0)),
            IClearingAttestor(address(0)),
            _auditCap(keccak256("an audit that never ran"))
        );

        assertEq(pad.launchCount(), 0, "no ungated launch exists");
    }

    /// The arms stay PLUGGABLE: the same gate admits a BONDED deployer (arm 0) and
    /// an AUDIT-cleared deployer (arm 3) — the launchpad pins the gate, not an arm.
    function test_2_Gate_PluggableArms_BondAndAuditBothAdmit() public {
        DreggLaunchpad.Schedule memory s = _goodSchedule();

        // Arm 0 — a conduct bond at/above the minimum.
        vm.prank(creator);
        gate.postBond{value: MIN_BOND}();
        uint256 idBond = _register(creator, s, _bondCap());
        assertEq(uint256(pad.phaseOf(idBond)), uint256(DreggLaunchpad.Phase.Commit), "bonded deployer registered");

        // Arm 3 — a cleared token-factory audit (a different deployer, no bond).
        bytes32 reportHash = _clearFactoryAuditFor(s);
        uint256 idAudit = _register(dave, s, _auditCap(reportHash));
        assertEq(uint256(pad.phaseOf(idAudit)), uint256(DreggLaunchpad.Phase.Commit), "audit-cleared deployer registered");

        // A DISABLED arm is refused even when its condition holds: the operator's
        // policy binds (here: drop the bond arm, keep audit).
        vm.prank(admin);
        gate.setAcceptedArms(uint8(1 << 3)); // ARM_AUDIT only
        vm.prank(creator); // still bonded — but the arm is off
        vm.expectRevert(abi.encodeWithSelector(DreggLaunchpad.DeployerNotGated.selector, creator));
        pad.registerLaunch(
            "Good Capped Token",
            "GOOD",
            s,
            COMMIT_DUR,
            REVEAL_DUR,
            ILaunchEligibility(address(0)),
            IClearingAttestor(address(0)),
            _bondCap()
        );
    }

    // ══════════════════════════════════════════════════════════════════════════
    // 3 — CREATE, THE NEGATIVE POLE: a rug-y spec never reaches a launch
    // ══════════════════════════════════════════════════════════════════════════

    /// The factory REJECTED the `owner-refillable` spec by machine counterexample,
    /// so no VERIFIED-SAFE bundle exists for it — and the audit arm has nothing to
    /// clear. The rug is caught at CREATE, before a launch can exist.
    function test_3_Create_RugSpecCannotBeLaunched() public {
        string memory rejected = vm.readFile(RUG_ARTIFACT);
        assertTrue(_contains(rejected, "**Verdict: REJECTED.**"), "the factory rejected the rug-y spec");
        assertTrue(_contains(rejected, "COUNTEREXAMPLE (cap breakable)"), "rejected by a Halmos counterexample, not taste");

        // A scammer presenting the REJECTED bundle as its capability: the auditor
        // never cleared it (the factory never shipped it), so the gate refuses.
        bytes32 rugReport = keccak256(bytes(rejected));
        assertFalse(gate.auditCleared(rugReport), "a rejected bundle is never cleared");

        DreggLaunchpad.Schedule memory s = _goodSchedule();
        vm.prank(scammer);
        vm.expectRevert(abi.encodeWithSelector(DreggLaunchpad.DeployerNotGated.selector, scammer));
        pad.registerLaunch(
            "Refillable Moon Token",
            "RMOON",
            s,
            COMMIT_DUR,
            REVEAL_DUR,
            ILaunchEligibility(address(0)),
            IClearingAttestor(address(0)),
            _auditCap(rugReport)
        );
        assertEq(pad.launchCount(), 0, "the rug never got a launch");
    }

    /// An audit cleared for ONE disclosure cannot be spent on ANOTHER — the
    /// artifact→schedule binding is what makes "the audited token is the launched
    /// token" true on-chain rather than by convention.
    function test_3_Create_AuditCannotBeSpentOnAnotherSchedule() public {
        DreggLaunchpad.Schedule memory audited = _goodSchedule();
        bytes32 reportHash = _clearFactoryAuditFor(audited);

        // The honest pole: the audited schedule registers.
        uint256 id = _register(creator, audited, _auditCap(reportHash));
        assertEq(uint256(pad.phaseOf(id)), uint256(DreggLaunchpad.Phase.Commit), "the AUDITED disclosure launches");

        // The switch: same cleared report, a different disclosure (the creator
        // quietly takes 500M instead of 50M). The capability does not cover it.
        // (A fresh struct — `memory` assignment aliases, it does not copy.)
        DreggLaunchpad.Schedule memory swapped = _goodSchedule();
        swapped.creatorAllocation = 500_000_000;
        swapped.saleSupply = 400_000_000; // still closes to the cap — but NOT audited
        assertTrue(_paramsHash(swapped) != _paramsHash(audited), "a different disclosure");

        vm.prank(creator);
        vm.expectRevert(abi.encodeWithSelector(DreggLaunchpad.DeployerNotGated.selector, creator));
        pad.registerLaunch(
            "Good Capped Token",
            "GOOD",
            swapped,
            COMMIT_DUR,
            REVEAL_DUR,
            ILaunchEligibility(address(0)),
            IClearingAttestor(address(0)),
            _auditCap(reportHash)
        );
    }

    // ══════════════════════════════════════════════════════════════════════════
    // ABUSE (a) — LAUNCH-BLOCK SNIPING: no time-priority edge exists to buy
    // ══════════════════════════════════════════════════════════════════════════

    /// p0 inherits bonding-curve time-priority: the earliest block wins the curve
    /// bottom, so coordinated fresh wallets snipe the launch block. Here the
    /// clearing is a function of the BOOK, not of arrival: the same bids in the
    /// OPPOSITE commit-and-reveal order produce an IDENTICAL uniform price and
    /// IDENTICAL fills. Sniping is not "mitigated" — being first buys nothing,
    /// because ordering is not an input to the clearing.
    function test_Abuse_A_SnipingRefused_NoTimePriorityEdge() public {
        DreggLaunchpad.Schedule memory s = _goodSchedule();
        bytes32 reportHash = _clearFactoryAuditFor(s);
        // Two launches of the identical disclosure, registered in the same block.
        uint256 first = _register(creator, s, _auditCap(reportHash));
        uint256 second = _register(creator, s, _auditCap(reportHash));

        // Launch A: alice commits FIRST, dave LAST. Launch B: exactly reversed.
        _commit(first, alice, 5 * G, 400_000_000, keccak256("a"));
        _commit(first, bob, 4 * G, 400_000_000, keccak256("b"));
        _commit(first, carol, 3 * G, 400_000_000, keccak256("c"));
        _commit(first, dave, 2 * G, 400_000_000, keccak256("d"));

        _commit(second, dave, 2 * G, 400_000_000, keccak256("d"));
        _commit(second, carol, 3 * G, 400_000_000, keccak256("c"));
        _commit(second, bob, 4 * G, 400_000_000, keccak256("b"));
        _commit(second, alice, 5 * G, 400_000_000, keccak256("a"));

        vm.warp(block.timestamp + COMMIT_DUR);

        // THE LATE SNIPER, inside the window where it would strike: the commit
        // phase has closed, so there is no way to join the book (typed)...
        address sniper = makeAddr("sniper");
        vm.deal(sniper, 100 ether);
        bytes32 seal = pad.sealOf(9 * G, 400_000_000, keccak256("s"), sniper);
        vm.prank(sniper);
        vm.expectRevert(DreggLaunchpad.NotCommitPhase.selector);
        pad.commitBid{value: 9 * G * 400_000_000}(first, seal, "");

        // ...nor conjure a bid at reveal time without a sealed commitment (typed).
        vm.prank(sniper);
        vm.expectRevert(DreggLaunchpad.NoCommit.selector);
        pad.revealBid(first, 9 * G, 400_000_000, keccak256("s"));

        // Reveal orders are opposite too (the reveal index IS the book order).
        _reveal(first, alice, 5 * G, 400_000_000, keccak256("a")); // idx 0
        _reveal(first, bob, 4 * G, 400_000_000, keccak256("b")); // idx 1
        _reveal(first, carol, 3 * G, 400_000_000, keccak256("c")); // idx 2
        _reveal(first, dave, 2 * G, 400_000_000, keccak256("d")); // idx 3

        _reveal(second, dave, 2 * G, 400_000_000, keccak256("d")); // idx 0
        _reveal(second, carol, 3 * G, 400_000_000, keccak256("c")); // idx 1
        _reveal(second, bob, 4 * G, 400_000_000, keccak256("b")); // idx 2
        _reveal(second, alice, 5 * G, 400_000_000, keccak256("a")); // idx 3

        vm.warp(block.timestamp + REVEAL_DUR);

        uint256[] memory orderA = new uint256[](4);
        orderA[0] = 0;
        orderA[1] = 1;
        orderA[2] = 2;
        orderA[3] = 3; // alice,bob,carol,dave (already descending)
        pad.finalizeClearing(first, orderA, "");

        uint256[] memory orderB = new uint256[](4);
        orderB[0] = 3;
        orderB[1] = 2;
        orderB[2] = 1;
        orderB[3] = 0; // alice,bob,carol,dave (descending over the reversed book)
        pad.finalizeClearing(second, orderB, "");

        // ORDER-INVARIANCE: the clearing is a function of the book alone.
        assertEq(pad.clearingPriceOf(first), pad.clearingPriceOf(second), "same uniform price regardless of arrival order");
        assertEq(pad.soldQtyOf(first), pad.soldQtyOf(second), "same quantity cleared regardless of arrival order");
        _assertSameFill(first, second, alice);
        _assertSameFill(first, second, bob);
        _assertSameFill(first, second, carol);
        _assertSameFill(first, second, dave);
        // Being LAST in launch B bought alice exactly what being FIRST in launch A
        // did: there is no earliest-block edge for a sniper to take.
    }

    function _assertSameFill(uint256 a, uint256 b, address who) internal view {
        (,,,, uint256 fillA,,) = pad.getBid(a, who);
        (,,,, uint256 fillB,,) = pad.getBid(b, who);
        assertEq(fillA, fillB, "identical fill regardless of arrival order");
    }

    /// The other half of the snipe: you cannot see the book to front-run it, and
    /// you cannot change your bid after you do see it.
    function test_Abuse_A_SnipingRefused_NoPeekNoLateSwitch() public {
        DreggLaunchpad.Schedule memory s = _goodSchedule();
        uint256 id = _register(creator, s, _auditCap(_clearFactoryAuditFor(s)));
        _commit(id, alice, 5 * G, 400_000_000, keccak256("a"));

        // NO PEEK: revealing inside the commit window is refused (typed).
        vm.prank(alice);
        vm.expectRevert(DreggLaunchpad.NotRevealPhase.selector);
        pad.revealBid(id, 5 * G, 400_000_000, keccak256("a"));

        // NO LATE-SWITCH: after seeing the others, alice cannot open her seal to a
        // different bid (typed).
        vm.warp(block.timestamp + COMMIT_DUR);
        vm.prank(alice);
        vm.expectRevert(DreggLaunchpad.BidMismatch.selector);
        pad.revealBid(id, 9 * G, 400_000_000, keccak256("a"));

        // The honest pole: her committed bid opens fine.
        _reveal(id, alice, 5 * G, 400_000_000, keccak256("a"));
        (, bool revealed, uint256 price,,,,) = pad.getBid(id, alice);
        assertTrue(revealed, "the committed bid reveals");
        assertEq(price, 5 * G, "as exactly what was sealed");
    }

    // ══════════════════════════════════════════════════════════════════════════
    // ABUSE (b) — HIDDEN SUPPLY: the cap is absolute
    // ══════════════════════════════════════════════════════════════════════════

    /// p0's AI-emitted contract can carry a hidden mint door. Here the launched
    /// token's cap is Halmos-proven and its mint is one-shot: not even the
    /// launchpad — the sole minter — can add supply after the disclosed mint.
    function test_Abuse_B_HiddenSupplyRefused_CapIsAbsolute() public {
        DreggLaunchpad.Schedule memory s = _goodSchedule();
        uint256 id = _register(creator, s, _auditCap(_clearFactoryAuditFor(s)));
        DreggLaunchToken tok = DreggLaunchToken(pad.tokenOf(id));
        uint256 unit = pad.TOKEN_UNIT(); // read BEFORE any prank/expectRevert

        // HONEST POLE: the disclosed supply exists, exactly and entirely.
        assertEq(tok.totalSupply(), FACTORY_CAP * unit, "the whole disclosed supply is minted");
        assertEq(tok.balanceOf(address(pad)), tok.totalSupply(), "and all of it is in launch custody");

        // (1) The SOLE MINTER cannot mint again — no second door (typed).
        vm.prank(address(pad));
        vm.expectRevert(DreggLaunchToken.AlreadyMinted.selector);
        tok.mint(creator, 1);

        // (2) The creator is not the minter at all (typed).
        vm.prank(creator);
        vm.expectRevert(abi.encodeWithSelector(DreggLaunchToken.NotMinter.selector, creator));
        tok.mint(creator, 1_000_000 * unit);

        // (3) A mint BEYOND THE CAP is refused on a fresh token of the same
        //     template — the cap bound itself, not just the latch (typed).
        DreggLaunchToken fresh = new DreggLaunchToken("Good Capped Token", "GOOD", FACTORY_CAP * 1e18, address(this));
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggLaunchToken.CapExceeded.selector, FACTORY_CAP * 1e18 + 1, FACTORY_CAP * 1e18
            )
        );
        fresh.mint(address(this), FACTORY_CAP * 1e18 + 1);

        // (4) A schedule that HIDES supply cannot even register: the disclosed
        //     parts must account for the whole cap (typed).
        DreggLaunchpad.Schedule memory hidden = _goodSchedule();
        hidden.totalSupply = FACTORY_CAP * 5; // 4B undisclosed
        bytes memory capability = _auditCap(_factoryVerifiedSafeReport()); // built BEFORE the prank
        vm.prank(creator);
        // (the gate is checked after the disclosure math, so this is the supply error)
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggLaunchpad.SupplyDoesNotClose.selector,
                uint256(850_000_000),
                uint256(50_000_000),
                FACTORY_CAP * 5
            )
        );
        pad.registerLaunch(
            "Good Capped Token",
            "GOOD",
            hidden,
            COMMIT_DUR,
            REVEAL_DUR,
            ILaunchEligibility(address(0)),
            IClearingAttestor(address(0)),
            capability
        );
    }

    // ══════════════════════════════════════════════════════════════════════════
    // ABUSE (c) — LP / OWNER DRAIN: no drain path exists
    // ══════════════════════════════════════════════════════════════════════════

    /// p0's target launchpads let a creator pull the LP and dump the allocation.
    /// Here: the graduated pool has NO owner and NO withdraw function at all (the
    /// only exits are `buy`/`sell`, both floor-guarded), and the creator's tokens
    /// sit behind the disclosed cliff.
    function test_Abuse_C_LpAndOwnerDrainRefused() public {
        (uint256 id, DreggSolventPool pool, DreggLaunchpad.Schedule memory s) = _runToGraduated();

        // HONEST POLE FIRST: an ordinary trade clears against the pool.
        (uint256 rq0, uint256 rt0) = pool.reserves();
        vm.prank(bob);
        uint256 out = pool.buy{value: 0.05 ether}(0);
        assertGt(out, 0, "a within-floor buy clears");

        // (1) THE LP DRAIN: a whale buy that would take the token reserve below
        //     the disclosed floor is REFUSED (typed) — the pool cannot be emptied.
        (, uint256 floorToken) = pool.floors();
        vm.prank(bob);
        vm.expectPartialRevert(DreggSolventPool.PoolFloorBreached.selector);
        pool.buy{value: 50 ether}(0);

        (uint256 rq1, uint256 rt1) = pool.reserves();
        assertGe(rt1, floorToken, "the token reserve never went below its floor");
        assertEq(rq1, rq0 + 0.05 ether, "and the refused drain moved nothing");
        assertEq(rt1, rt0 - out, "reserves reflect only the honest trade");

        // (2) THE OWNER DRAIN: the pool has no owner. Its seeding door closed
        //     PERMANENTLY when the graduation created+seeded it in one atomic tx
        //     — re-initialization is typed-refused for everyone, the graduation
        //     included (an un-initialized pool is never observable on-chain).
        vm.prank(creator);
        vm.expectRevert(DreggSolventPool.AlreadyInitialized.selector);
        pool.initialize{value: 1 ether}(address(0), 0, 0, 0, 0, 1);
        vm.prank(address(pad));
        vm.expectRevert(DreggSolventPool.AlreadyInitialized.selector);
        pool.initialize{value: 1 ether}(address(0), 0, 0, 0, 0, 1);
        // (There is no `withdraw`/`skim`/`setOwner` on DreggSolventPool to call —
        // the drain door is absent by construction, not merely guarded.)

        // (3) THE ALLOCATION DUMP: the creator's own tokens are behind the
        //     disclosed cliff (typed).
        vm.prank(creator);
        vm.expectRevert(abi.encodeWithSelector(DreggLaunchpad.CreatorLockActive.selector, s.creatorLockUntil));
        pad.claimCreatorAllocation(id);

        // (4) THE PROCEEDS: the creator gets the raise REMAINDER and cannot reach
        //     the pool's seeded ETH — the seed left its custody at graduation.
        uint256 poolEth = address(pool).balance;
        uint256 remainder = pad.proceedsOf(id);
        uint256 before = creator.balance;
        vm.prank(creator);
        pad.withdrawProceeds(id);
        assertEq(creator.balance - before, remainder, "creator gets only the disclosed remainder");
        assertEq(address(pool).balance, poolEth, "the pool's liquidity is untouched by the creator's withdrawal");

        // …and no second withdrawal (typed).
        vm.prank(creator);
        vm.expectRevert(DreggLaunchpad.AlreadyDone.selector);
        pad.withdrawProceeds(id);
    }

    /// Drive a full honest launch to GRADUATED (the shared fixture for abuse (c)).
    function _runToGraduated()
        internal
        returns (uint256 id, DreggSolventPool pool, DreggLaunchpad.Schedule memory s)
    {
        s = _goodSchedule();
        id = _register(creator, s, _auditCap(_clearFactoryAuditFor(s)));
        _commit(id, alice, 5 * G, 400_000_000, keccak256("a"));
        _commit(id, bob, 4 * G, 400_000_000, keccak256("b"));
        _commit(id, carol, 3 * G, 400_000_000, keccak256("c"));
        _commit(id, dave, 2 * G, 400_000_000, keccak256("d"));
        vm.warp(block.timestamp + COMMIT_DUR);
        _reveal(id, alice, 5 * G, 400_000_000, keccak256("a"));
        _reveal(id, bob, 4 * G, 400_000_000, keccak256("b"));
        _reveal(id, carol, 3 * G, 400_000_000, keccak256("c"));
        _reveal(id, dave, 2 * G, 400_000_000, keccak256("d"));
        vm.warp(block.timestamp + REVEAL_DUR);
        uint256[] memory order = new uint256[](4);
        order[0] = 0;
        order[1] = 1;
        order[2] = 2;
        order[3] = 3;
        pad.finalizeClearing(id, order, "");
        pad.settleBid(id, alice);
        pad.settleBid(id, bob);
        pad.settleBid(id, carol);
        pad.settleBid(id, dave);
        (uint256 qSeed, uint256 tSeed) = pad.graduationSeed(id);
        pool = DreggSolventPool(pad.graduate(id, qSeed, tSeed));
    }

    // ══════════════════════════════════════════════════════════════════════════
    // The sealed-bid seal encoding the frontend must reproduce byte-for-byte.
    // ══════════════════════════════════════════════════════════════════════════

    /// THE CROSS-LANGUAGE SEAL VECTOR. `extension/src/sealedbid.ts`
    /// (`launchpadSeal`) derives the bidder's commitment off-chain; this contract
    /// recomputes it at `commitBid`. If the two ever disagree, no honest bid can
    /// be revealed — so both sides assert the SAME vector, and a drift on either
    /// side turns red here and in `extension/test/sealedbid.test.mjs`.
    function test_SealVector_MatchesTheExtensionDerivation() public view {
        bytes32 seal = pad.sealOf(5 * G, 400, bytes32(uint256(0xd1e55ed)), address(0xA11CE));
        assertEq(seal, SEAL_VECTOR, "the launchpad's canonical seal encoding is stable + matches the extension");
        // …and it is what `commitBid` actually binds (`revealBid` recomputes it).
        assertEq(
            seal, keccak256(abi.encode(uint256(5 * G), uint256(400), bytes32(uint256(0xd1e55ed)), address(0xA11CE)))
        );
    }

    /// keccak256(abi.encode(uint256 5e9, uint256 400, bytes32 0xd1e55ed, address 0xA11CE)).
    bytes32 constant SEAL_VECTOR = 0xc9b84c4f878aeb4b76a6ffa62d14611a5226a9d4015a9eb4818aa04db238c0bb;

    // ── utils ─────────────────────────────────────────────────────────────────

    /// Substring search (the artifacts are read as strings).
    function _contains(string memory haystack, string memory needle) internal pure returns (bool) {
        bytes memory h = bytes(haystack);
        bytes memory n = bytes(needle);
        if (n.length == 0 || n.length > h.length) return false;
        for (uint256 i = 0; i <= h.length - n.length; i++) {
            bool ok = true;
            for (uint256 j = 0; j < n.length; j++) {
                if (h[i + j] != n[j]) {
                    ok = false;
                    break;
                }
            }
            if (ok) return true;
        }
        return false;
    }
}
