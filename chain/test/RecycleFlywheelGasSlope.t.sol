// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Test, console2} from "forge-std/Test.sol";
import {RecycleFlywheel} from "../contracts/flywheel/RecycleFlywheel.sol";
import {DreggLaunchToken} from "../contracts/launchpad/DreggLaunchToken.sol";
import {DreggSolventPool} from "../contracts/launchpad/DreggSolventPool.sol";

/// # THE FINALIZE GAS SLOPE — the measured O(n) cost of the ON-CHAIN clearing
///
/// Reproduces the numbers `docs/reference/GAS-OPTIMIZATION-MEASURED.md` cites:
/// `finalizeRecycle` cold-storage gas at book sizes 3/16/48/128 and the
/// per-ask slope (~10.7k gas/ask cold). `vm.cool` resets the flywheel's and
/// token's access lists before the measured call, so the numbers model a real
/// standalone finalize tx (a forge test otherwise runs the whole lifecycle in
/// one warm tx and under-reports by ~5×).
///
/// The slope is the crossover input for the off-chain-clear + on-chain-proof
/// architecture (`chain/gnark/clearing_snark.go`): a Groth16 clearing verify
/// is flat (~466k measured on the settlement-shaped verifier), so above
/// ~44 asks the proof path wins and grows ~28× cheaper by n=1000.
contract RecycleFlywheelGasSlopeTest is Test {
    DreggLaunchToken token;
    uint256 constant OPERATOR_PK = 0xA11CE;
    address OPERATOR;
    uint256 constant G = 1e9;
    uint256 constant UNIT = 1e18;
    address poolImpl;

    function setUp() public {
        OPERATOR = vm.addr(OPERATOR_PK);
        token = new DreggLaunchToken("T", "T", 1e30, address(this));
        token.mint(address(this), 1e30);
        poolImpl = address(new DreggSolventPool());
        vm.deal(address(this), 100000 ether);
    }

    function _run(uint256 n) internal returns (uint256 gas) {
        RecycleFlywheel fw = new RecycleFlywheel(address(token), 5000, OPERATOR, 100, 100, poolImpl);
        fw.accrueFee{value: 1000 ether}(keccak256("f"));
        for (uint256 i = 0; i < n; i++) {
            address s = address(uint160(0x10000 + i));
            uint256 price = (i + 1) * G;
            uint256 qty = 1_000_000;
            uint256 escrow = qty * UNIT;
            token.transfer(s, escrow);
            bytes32 seal = fw.sealOf(price, qty, bytes32(i), s);
            vm.startPrank(s);
            token.approve(address(fw), escrow);
            fw.commitAsk(seal, escrow);
            vm.stopPrank();
        }
        vm.warp(fw.commitEnd());
        for (uint256 i = 0; i < n; i++) {
            address s = address(uint160(0x10000 + i));
            vm.prank(s);
            fw.revealAsk((i + 1) * G, 1_000_000, bytes32(i));
        }
        vm.warp(fw.revealEnd());
        uint256[] memory order = new uint256[](n);
        for (uint256 i = 0; i < n; i++) order[i] = i;
        gas = _finalize(fw, order);
    }

    function _head(RecycleFlywheel fw, uint256[] memory order) internal view returns (bytes32) {
        (uint256 buyHalf, uint256 poolHalf) = fw.splitOf(fw.accrued());
        (uint256 uP, uint256 bought, uint256 spent, bytes32 bc) = fw.previewClearing(order, buyHalf);
        uint256 qSeed = poolHalf + (buyHalf - spent);
        uint256 tSeed = bought * UNIT;
        RecycleFlywheel.Receipt memory r = RecycleFlywheel.Receipt({
            accrued: fw.accrued(),
            provenanceRoot: fw.provenanceRoot(),
            inflowCount: fw.inflowCount(),
            buyHalf: buyHalf,
            poolHalf: poolHalf,
            buyBps: 5000,
            uniformPrice: uP,
            boughtTokens: bought,
            spentQuote: spent,
            bookCommit: bc,
            quoteSeed: qSeed,
            tokenSeed: tSeed,
            floorQuote: (qSeed * 2000) / 10000,
            floorToken: (tSeed * 2000) / 10000,
            netQuote: int256(0),
            netToken: int256(0)
        });
        return fw.recomputeReceiptHead(r);
    }

    function _finalize(RecycleFlywheel fw, uint256[] memory order) internal returns (uint256 gas) {
        bytes32 head = _head(fw, order);
        (uint8 v, bytes32 sr, bytes32 ss) =
            vm.sign(OPERATOR_PK, keccak256(abi.encodePacked("\x19Ethereum Signed Message:\n32", head)));
        bytes memory sig = abi.encodePacked(sr, ss, v);
        (uint256 buyHalf, uint256 poolHalf) = fw.splitOf(fw.accrued());
        vm.cool(address(fw));
        vm.cool(address(token));
        uint256 g0 = gasleft();
        fw.finalizeRecycle(order, buyHalf, poolHalf, head, sig);
        gas = g0 - gasleft();
    }

    function test_slope() public {
        uint256 g3 = _run(3);
        uint256 g16 = _run(16);
        uint256 g48 = _run(48);
        uint256 g128 = _run(128);
        console2.log("finalize n=3  :", g3);
        console2.log("finalize n=16 :", g16);
        console2.log("finalize n=48 :", g48);
        console2.log("finalize n=128:", g128);
        console2.log("slope 48->128 per ask:", (g128 - g48) / 80);
    }
}
