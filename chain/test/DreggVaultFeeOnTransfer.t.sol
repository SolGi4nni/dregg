// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../contracts/DreggVault.sol";
import {IDreggSettlement} from "../contracts/IDreggSettlement.sol";

/// @dev SP1 verifier stand-in that always accepts.
contract PassSP1Verifier {
    function verifyProof(bytes32, bytes calldata, bytes calldata) external pure {}
}

/// @dev Settlement stand-in with an operator-toggled proven-root set.
contract PassSettlement {
    mapping(bytes32 => bool) public proven;

    function setProven(bytes32 root, bool ok) external {
        proven[root] = ok;
    }

    function isProvenRoot(bytes32 root) external view returns (bool) {
        if (root == bytes32(0)) return false;
        return proven[root];
    }
}

/// @dev A FEE-ON-TRANSFER ERC-20: every transfer skims `feeBps` of the moved
/// amount to a sink, so the recipient receives LESS than `amount`. This is the
/// exact token class that the vault's old `tokenBalances[token] += amount`
/// over-credited (crediting the requested amount, not the delivered delta).
contract FeeOnTransferERC20 {
    string public name = "Fee Token";
    string public symbol = "FEE";
    uint8 public decimals = 18;
    uint256 public immutable feeBps; // basis points skimmed on every transfer
    address public immutable feeSink;
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    constructor(uint256 _feeBps, address _feeSink) {
        feeBps = _feeBps;
        feeSink = _feeSink;
    }

    function mint(address to, uint256 amount) external {
        balanceOf[to] += amount;
    }

    function approve(address spender, uint256 amount) external returns (bool) {
        allowance[msg.sender][spender] = amount;
        return true;
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        return _xfer(msg.sender, to, amount);
    }

    function transferFrom(address from, address to, uint256 amount) external returns (bool) {
        require(allowance[from][msg.sender] >= amount, "allowance");
        allowance[from][msg.sender] -= amount;
        return _xfer(from, to, amount);
    }

    function _xfer(address from, address to, uint256 amount) internal returns (bool) {
        require(balanceOf[from] >= amount, "balance");
        uint256 fee = (amount * feeBps) / 10000;
        uint256 net = amount - fee;
        balanceOf[from] -= amount;
        balanceOf[to] += net;
        balanceOf[feeSink] += fee;
        return true;
    }
}

/// #4 — fee-on-transfer over-crediting. The vault must credit ONLY the measured
/// balance delta, never the requested amount. Proven positively (solvency holds
/// across two depositors of the same fee token) and non-vacuously (the pre-fee
/// amount is NOT withdrawable, because it was never credited).
contract DreggVaultFeeOnTransferTest is Test {
    DreggVault vault;
    PassSP1Verifier verifier;
    PassSettlement settlement;
    FeeOnTransferERC20 feeToken;

    address alice = address(0xA11CE);
    address bob = address(0xB0B);
    address feeSink = address(0xFEE5);
    address recipient = address(0xBEEF);

    uint256 constant FEE_BPS = 1000; // 10% skimmed on transfer

    function setUp() public {
        verifier = new PassSP1Verifier();
        settlement = new PassSettlement();
        vault = new DreggVault(address(verifier), bytes32(uint256(0xdeadbeef)), IDreggSettlement(address(settlement)));
        feeToken = new FeeOnTransferERC20(FEE_BPS, feeSink);
    }

    function _deposit(address who, uint256 amount, bytes32 note) internal {
        feeToken.mint(who, amount);
        vm.startPrank(who);
        feeToken.approve(address(vault), amount);
        vault.deposit(address(feeToken), amount, note);
        vm.stopPrank();
    }

    /// A single fee-on-transfer deposit credits ONLY what arrived, and the credit
    /// exactly equals the vault's real token balance — no phantom over-credit.
    function test_depositCreditsMeasuredDeltaNotRequested() public {
        uint256 requested = 1000 ether;
        uint256 delivered = requested - (requested * FEE_BPS) / 10000; // 900

        _deposit(alice, requested, keccak256("a"));

        assertEq(feeToken.balanceOf(address(vault)), delivered, "vault holds only the delivered amount");
        assertEq(vault.tokenBalances(address(feeToken)), delivered, "credited the delivered delta, not 1000");
        (,, uint256 recordAmount,,) = vault.deposits(keccak256("a"));
        assertEq(recordAmount, delivered, "the deposit record reflects the custodied amount");
    }

    /// The bug this closes: crediting the requested amount would let one depositor
    /// withdraw more than arrived, drawing down another depositor of the same
    /// token. With the delta-credit, `tokenBalances` never exceeds the real
    /// balance, so cross-user solvency holds and BOTH depositors fully exit.
    function test_noCrossUserOverdraw() public {
        _deposit(alice, 1000 ether, keccak256("a"));
        _deposit(bob, 1000 ether, keccak256("b"));

        uint256 delivered = 900 ether; // each, after the 10% fee
        // The pooled credit equals the pooled real balance — never 2000.
        assertEq(vault.tokenBalances(address(feeToken)), 2 * delivered);
        assertEq(feeToken.balanceOf(address(vault)), 2 * delivered);

        // Alice exits her credited 900; solvency leaves Bob's 900 fully intact.
        _withdraw(delivered, keccak256("nA"));
        assertEq(vault.tokenBalances(address(feeToken)), delivered, "only Alice's share left");

        // Bob exits his 900 too — the fix means his balance was never stolen.
        _withdraw(delivered, keccak256("nB"));
        assertEq(vault.tokenBalances(address(feeToken)), 0, "both depositors fully exited");
        assertEq(feeToken.balanceOf(address(vault)), 0, "vault drained to zero - solvent throughout");
    }

    /// Non-vacuity: the requested (pre-fee) amount was NEVER credited, so a
    /// withdrawal for it reverts on solvency. If the old code had credited the
    /// requested amount, this would have succeeded (the theft).
    function test_preFeeAmountIsNotWithdrawable() public {
        _deposit(alice, 1000 ether, keccak256("a"));
        uint256 requested = 1000 ether;
        uint256 delivered = 900 ether;

        // Withdrawing the requested 1000 reverts — only 900 was ever credited.
        bytes memory proof = _proof(requested, keccak256("nBad"));
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggVault.InsufficientVaultBalance.selector, address(feeToken), requested, delivered
            )
        );
        vault.withdraw(address(feeToken), requested, recipient, proof);

        // …but the honestly-delivered 900 withdraws fine.
        _withdraw(delivered, keccak256("nGood"));
        assertEq(vault.tokenBalances(address(feeToken)), 0);
    }

    /// The escrow path shares the fix: `escrowedBalances` and `Escrow.amount` take
    /// the delivered delta, so `escrowRefund` can never pay more than arrived.
    function test_escrowDepositCreditsMeasuredDelta() public {
        uint256 requested = 1000 ether;
        uint256 delivered = 900 ether;
        bytes32 escrowId = keccak256("escrow-1");

        feeToken.mint(alice, requested);
        vm.startPrank(alice);
        feeToken.approve(address(vault), requested);
        vault.escrowDeposit(address(feeToken), requested, block.timestamp + 1 days, escrowId);
        vm.stopPrank();

        assertEq(vault.escrowedBalances(address(feeToken)), delivered, "escrowed only what arrived");
        (,, uint256 escrowAmount,,) = vault.escrows(escrowId);
        assertEq(escrowAmount, delivered, "escrow records the delivered amount");

        // Refund after the deadline pays exactly the delivered 900 — never 1000.
        vm.warp(block.timestamp + 2 days);
        vm.prank(alice);
        vault.escrowRefund(escrowId);
        assertEq(vault.escrowedBalances(address(feeToken)), 0);
        assertEq(feeToken.balanceOf(address(vault)), 0, "vault holds nothing after the refund");
    }

    // ─── helpers ────────────────────────────────────────────────────────────

    function _proof(uint256 amount, bytes32 nullifier) internal view returns (bytes memory) {
        bytes memory publicValues = abi.encode(
            true, nullifier, address(feeToken), amount, recipient, vault.noteTreeRoot()
        );
        return abi.encode(hex"1234", publicValues);
    }

    function _withdraw(uint256 amount, bytes32 nullifier) internal {
        vault.withdraw(address(feeToken), amount, recipient, _proof(amount, nullifier));
    }
}
