// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../contracts/DreggVault.sol";
import {IDreggSettlement} from "../contracts/IDreggSettlement.sol";

/// @dev Mock SP1 Verifier that always succeeds.
contract MockSP1Verifier {
    bool public shouldPass = true;

    function setShouldPass(bool _pass) external {
        shouldPass = _pass;
    }

    function verifyProof(
        bytes32, /* vkey */
        bytes calldata, /* publicValues */
        bytes calldata /* proofBytes */
    ) external view {
        require(shouldPass, "MockSP1Verifier: proof rejected");
    }
}

/// @dev Minimal DreggSettlement stand-in: an operator-toggled proven-root set,
/// enough to exercise the escrow release gate (`isProvenRoot`). The real contract
/// records roots on a verified Groth16 settlement; here we set them directly.
contract MockSettlement {
    mapping(bytes32 => bool) public proven;

    function setProven(bytes32 root, bool ok) external {
        proven[root] = ok;
    }

    function isProvenRoot(bytes32 root) external view returns (bool) {
        if (root == bytes32(0)) return false; // Nomad-law: zero root never proven
        return proven[root];
    }
}

/// @dev Minimal ERC-20 for testing deposits.
contract MockERC20 {
    string public name = "Mock Token";
    string public symbol = "MOCK";
    uint8 public decimals = 18;
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    function mint(address to, uint256 amount) external {
        balanceOf[to] += amount;
    }

    function approve(address spender, uint256 amount) external returns (bool) {
        allowance[msg.sender][spender] = amount;
        return true;
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        require(balanceOf[msg.sender] >= amount, "insufficient balance");
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;
        return true;
    }

    function transferFrom(address from, address to, uint256 amount) external returns (bool) {
        require(allowance[from][msg.sender] >= amount, "insufficient allowance");
        require(balanceOf[from] >= amount, "insufficient balance");
        allowance[from][msg.sender] -= amount;
        balanceOf[from] -= amount;
        balanceOf[to] += amount;
        return true;
    }
}

/// @dev Recipient that attempts to re-enter withdraw() from its receive hook,
/// using a SECOND valid proof (fresh nullifier). Records whether the reentrant
/// call succeeded so tests can assert the guard blocked it.
contract ReentrantRecipient {
    DreggVault public vault;
    bytes public innerProof;
    uint256 public innerAmount;
    bool public reentryAttempted;
    bool public reentrySucceeded;

    constructor(DreggVault _vault) {
        vault = _vault;
    }

    function arm(bytes calldata _innerProof, uint256 _innerAmount) external {
        innerProof = _innerProof;
        innerAmount = _innerAmount;
    }

    receive() external payable {
        if (!reentryAttempted) {
            reentryAttempted = true;
            try vault.withdraw(address(0), innerAmount, address(this), innerProof) {
                reentrySucceeded = true;
            } catch {}
        }
    }
}

contract DreggVaultTest is Test {
    DreggVault public vault;
    MockSP1Verifier public verifier;
    MockSettlement public settlement;
    MockERC20 public token;

    bytes32 constant PROGRAM_VKEY = bytes32(uint256(0xdeadbeef));
    address constant RECIPIENT = address(0xBEEF);

    function setUp() public {
        verifier = new MockSP1Verifier();
        settlement = new MockSettlement();
        vault = new DreggVault(address(verifier), PROGRAM_VKEY, IDreggSettlement(address(settlement)));
        token = new MockERC20();
    }

    // ─── Deposit Tests ──────────────────────────────────────────────────────

    function test_depositERC20() public {
        bytes32 commitment = keccak256("note1");
        uint256 amount = 1 ether;

        token.mint(address(this), amount);
        token.approve(address(vault), amount);

        vault.deposit(address(token), amount, commitment);

        assertEq(vault.depositCount(), 1);
        assertEq(token.balanceOf(address(vault)), amount);
        assertTrue(vault.noteTreeRoot() != bytes32(0));
    }

    function test_depositETH() public {
        bytes32 commitment = keccak256("note2");
        uint256 amount = 0.5 ether;

        vault.depositETH{value: amount}(commitment);

        assertEq(vault.depositCount(), 1);
        assertEq(address(vault).balance, amount);
    }

    function test_depositRevertsOnZeroAmount() public {
        bytes32 commitment = keccak256("note3");
        vm.expectRevert(DreggVault.ZeroAmount.selector);
        vault.deposit(address(token), 0, commitment);
    }

    function test_depositETHRevertsOnZeroAmount() public {
        bytes32 commitment = keccak256("note4");
        vm.expectRevert(DreggVault.ZeroAmount.selector);
        vault.depositETH{value: 0}(commitment);
    }

    function test_depositRevertsDuplicateCommitment() public {
        bytes32 commitment = keccak256("note5");
        uint256 amount = 1 ether;

        token.mint(address(this), 2 * amount);
        token.approve(address(vault), 2 * amount);

        vault.deposit(address(token), amount, commitment);

        vm.expectRevert(DreggVault.DuplicateNoteCommitment.selector);
        vault.deposit(address(token), amount, commitment);
    }

    // ─── Incremental Merkle Tree Tests ──────────────────────────────────────

    function test_merkleRootUpdatesAfterMultipleDeposits() public {
        token.mint(address(this), 10 ether);
        token.approve(address(vault), 10 ether);

        bytes32 root1;
        bytes32 root2;
        bytes32 root3;

        vault.deposit(address(token), 1 ether, keccak256("a"));
        root1 = vault.noteTreeRoot();

        vault.deposit(address(token), 1 ether, keccak256("b"));
        root2 = vault.noteTreeRoot();

        vault.deposit(address(token), 1 ether, keccak256("c"));
        root3 = vault.noteTreeRoot();

        // Each deposit should produce a different root.
        assertTrue(root1 != root2);
        assertTrue(root2 != root3);
        assertTrue(root1 != root3);

        assertEq(vault.depositCount(), 3);
    }

    // ─── Withdrawal Tests ───────────────────────────────────────────────────

    function test_withdrawETH() public {
        // First deposit some ETH.
        bytes32 commitment = keccak256("ethNote");
        vault.depositETH{value: 1 ether}(commitment);

        // Build valid public values for the proof.
        bytes32 nullifier = keccak256("nullifier1");
        bytes memory publicValues = abi.encode(
            true,           // valid
            nullifier,      // nullifier
            address(0),     // token (ETH)
            uint256(0.5 ether), // amount
            RECIPIENT,      // recipient
            vault.noteTreeRoot() // root
        );
        bytes memory proofBytes = hex"1234"; // Mock proof data

        // Encode as SP1 proof format.
        bytes memory sp1Proof = abi.encode(proofBytes, publicValues);

        vault.withdraw(address(0), 0.5 ether, RECIPIENT, sp1Proof);

        assertEq(RECIPIENT.balance, 0.5 ether);
        assertTrue(vault.usedNullifiers(nullifier));
    }

    function test_withdrawERC20() public {
        uint256 amount = 2 ether;
        bytes32 commitment = keccak256("erc20Note");

        token.mint(address(this), amount);
        token.approve(address(vault), amount);
        vault.deposit(address(token), amount, commitment);

        bytes32 nullifier = keccak256("nullifier2");
        bytes memory publicValues = abi.encode(
            true,
            nullifier,
            address(token),
            uint256(1 ether),
            RECIPIENT,
            vault.noteTreeRoot()
        );
        bytes memory proofBytes = hex"5678";
        bytes memory sp1Proof = abi.encode(proofBytes, publicValues);

        vault.withdraw(address(token), 1 ether, RECIPIENT, sp1Proof);

        assertEq(token.balanceOf(RECIPIENT), 1 ether);
        assertTrue(vault.usedNullifiers(nullifier));
    }

    // ─── Double-Spend Prevention ────────────────────────────────────────────

    function test_doubleSpendRejected() public {
        vault.depositETH{value: 2 ether}(keccak256("doubleNote"));

        bytes32 nullifier = keccak256("doublespend");
        bytes memory publicValues = abi.encode(
            true,
            nullifier,
            address(0),
            uint256(0.5 ether),
            RECIPIENT,
            vault.noteTreeRoot()
        );
        bytes memory proofBytes = hex"abcd";
        bytes memory sp1Proof = abi.encode(proofBytes, publicValues);

        // First withdrawal succeeds.
        vault.withdraw(address(0), 0.5 ether, RECIPIENT, sp1Proof);

        // Second withdrawal with same nullifier reverts.
        vm.expectRevert(abi.encodeWithSelector(DreggVault.NullifierAlreadyUsed.selector, nullifier));
        vault.withdraw(address(0), 0.5 ether, RECIPIENT, sp1Proof);
    }

    // ─── Proof Verification Failure ─────────────────────────────────────────

    function test_invalidProofRejected() public {
        vault.depositETH{value: 1 ether}(keccak256("failNote"));

        // Tell the mock verifier to reject proofs.
        verifier.setShouldPass(false);

        bytes32 nullifier = keccak256("failNullifier");
        bytes memory publicValues = abi.encode(
            true,
            nullifier,
            address(0),
            uint256(0.5 ether),
            RECIPIENT,
            vault.noteTreeRoot()
        );
        bytes memory proofBytes = hex"bad0";
        bytes memory sp1Proof = abi.encode(proofBytes, publicValues);

        vm.expectRevert(DreggVault.ProofVerificationFailed.selector);
        vault.withdraw(address(0), 0.5 ether, RECIPIENT, sp1Proof);
    }

    // ─── Frontrunning Protection (proof bound to msg.sender as recipient) ───

    function test_frontrunningProtection_recipientMismatch() public {
        vault.depositETH{value: 1 ether}(keccak256("frNote"));

        bytes32 nullifier = keccak256("frNullifier");
        // Proof is bound to RECIPIENT, but we try to withdraw to a different address.
        bytes memory publicValues = abi.encode(
            true,
            nullifier,
            address(0),
            uint256(0.5 ether),
            RECIPIENT, // proof says RECIPIENT
            vault.noteTreeRoot()
        );
        bytes memory proofBytes = hex"f001";
        bytes memory sp1Proof = abi.encode(proofBytes, publicValues);

        address attacker = address(0xA77AC6);
        // Attacker tries to redirect withdrawal to themselves.
        vm.expectRevert(DreggVault.RecipientMismatch.selector);
        vault.withdraw(address(0), 0.5 ether, attacker, sp1Proof);
    }

    function test_frontrunningProtection_amountMismatch() public {
        vault.depositETH{value: 1 ether}(keccak256("amtNote"));

        bytes32 nullifier = keccak256("amtNullifier");
        bytes memory publicValues = abi.encode(
            true,
            nullifier,
            address(0),
            uint256(0.5 ether), // proof says 0.5 ETH
            RECIPIENT,
            vault.noteTreeRoot()
        );
        bytes memory proofBytes = hex"a171";
        bytes memory sp1Proof = abi.encode(proofBytes, publicValues);

        // Try to withdraw more than the proof commits to.
        vm.expectRevert(DreggVault.AmountMismatch.selector);
        vault.withdraw(address(0), 1 ether, RECIPIENT, sp1Proof);
    }

    function test_frontrunningProtection_tokenMismatch() public {
        vault.depositETH{value: 1 ether}(keccak256("tokNote"));

        bytes32 nullifier = keccak256("tokNullifier");
        bytes memory publicValues = abi.encode(
            true,
            nullifier,
            address(0), // proof says ETH
            uint256(0.5 ether),
            RECIPIENT,
            vault.noteTreeRoot()
        );
        bytes memory proofBytes = hex"70c1";
        bytes memory sp1Proof = abi.encode(proofBytes, publicValues);

        // Try to withdraw a token instead of ETH.
        vm.expectRevert(DreggVault.TokenMismatch.selector);
        vault.withdraw(address(token), 0.5 ether, RECIPIENT, sp1Proof);
    }

    // ─── Fail-Closed Verifier (codeless address must never accept) ──────────

    function test_constructorRejectsCodelessVerifier() public {
        address codeless = address(0x1234);
        vm.expectRevert(DreggVault.VerifierNotContract.selector);
        new DreggVault(codeless, PROGRAM_VKEY, IDreggSettlement(address(settlement)));
    }

    function test_constructorRejectsCodelessSettlement() public {
        address codelessSettlement = address(0x5678);
        vm.expectRevert(DreggVault.SettlementNotContract.selector);
        new DreggVault(address(verifier), PROGRAM_VKEY, IDreggSettlement(codelessSettlement));
    }

    function test_withdrawRevertsWhenVerifierLosesCode() public {
        vault.depositETH{value: 1 ether}(keccak256("codelessNote"));

        bytes memory publicValues = abi.encode(
            true,
            keccak256("codelessNullifier"),
            address(0),
            uint256(0.5 ether),
            RECIPIENT,
            vault.noteTreeRoot()
        );
        bytes memory sp1Proof = abi.encode(hex"1234", publicValues);

        // Strip the verifier's code: the raw staticcall would now succeed
        // vacuously, so the call-time guard must reject.
        vm.etch(address(verifier), "");

        vm.expectRevert(DreggVault.VerifierNotContract.selector);
        vault.withdraw(address(0), 0.5 ether, RECIPIENT, sp1Proof);
    }

    // ─── Solvency ───────────────────────────────────────────────────────────

    function test_withdrawRevertsWhenExceedingEthBalance() public {
        vault.depositETH{value: 0.5 ether}(keccak256("solvNote"));
        // Give the vault raw ETH outside the deposit path -- it must NOT count.
        vm.deal(address(vault), 10 ether);

        bytes memory publicValues = abi.encode(
            true,
            keccak256("solvNullifier"),
            address(0),
            uint256(1 ether),
            RECIPIENT,
            vault.noteTreeRoot()
        );
        bytes memory sp1Proof = abi.encode(hex"1234", publicValues);

        vm.expectRevert(
            abi.encodeWithSelector(
                DreggVault.InsufficientVaultBalance.selector,
                address(0),
                uint256(1 ether),
                uint256(0.5 ether)
            )
        );
        vault.withdraw(address(0), 1 ether, RECIPIENT, sp1Proof);
    }

    function test_withdrawRevertsForTokenNeverDeposited() public {
        // Only ETH was deposited; a token withdrawal has zero solvency.
        vault.depositETH{value: 1 ether}(keccak256("crossNote"));
        token.mint(address(vault), 5 ether); // direct transfer, not a deposit

        bytes memory publicValues = abi.encode(
            true,
            keccak256("crossNullifier"),
            address(token),
            uint256(1 ether),
            RECIPIENT,
            vault.noteTreeRoot()
        );
        bytes memory sp1Proof = abi.encode(hex"1234", publicValues);

        vm.expectRevert(
            abi.encodeWithSelector(
                DreggVault.InsufficientVaultBalance.selector,
                address(token),
                uint256(1 ether),
                uint256(0)
            )
        );
        vault.withdraw(address(token), 1 ether, RECIPIENT, sp1Proof);
    }

    function test_withdrawFullBalanceSucceedsAndUpdatesAccounting() public {
        vault.depositETH{value: 1 ether}(keccak256("fullNote"));
        assertEq(vault.tokenBalances(address(0)), 1 ether);

        bytes memory publicValues = abi.encode(
            true,
            keccak256("fullNullifier"),
            address(0),
            uint256(1 ether),
            RECIPIENT,
            vault.noteTreeRoot()
        );
        bytes memory sp1Proof = abi.encode(hex"1234", publicValues);

        vault.withdraw(address(0), 1 ether, RECIPIENT, sp1Proof);

        assertEq(RECIPIENT.balance, 1 ether);
        assertEq(vault.tokenBalances(address(0)), 0);
    }

    // ─── Root Binding (proof root must be current or recent) ────────────────

    function test_withdrawRejectsUnknownRoot() public {
        vault.depositETH{value: 1 ether}(keccak256("rootNote"));

        bytes32 bogusRoot = keccak256("not a real root");
        bytes memory publicValues = abi.encode(
            true,
            keccak256("rootNullifier"),
            address(0),
            uint256(0.5 ether),
            RECIPIENT,
            bogusRoot
        );
        bytes memory sp1Proof = abi.encode(hex"1234", publicValues);

        vm.expectRevert(abi.encodeWithSelector(DreggVault.UnknownRoot.selector, bogusRoot));
        vault.withdraw(address(0), 0.5 ether, RECIPIENT, sp1Proof);
    }

    function test_withdrawRejectsZeroRoot() public {
        vault.depositETH{value: 1 ether}(keccak256("zeroRootNote"));

        bytes memory publicValues = abi.encode(
            true,
            keccak256("zeroRootNullifier"),
            address(0),
            uint256(0.5 ether),
            RECIPIENT,
            bytes32(0)
        );
        bytes memory sp1Proof = abi.encode(hex"1234", publicValues);

        vm.expectRevert(abi.encodeWithSelector(DreggVault.UnknownRoot.selector, bytes32(0)));
        vault.withdraw(address(0), 0.5 ether, RECIPIENT, sp1Proof);
    }

    function test_withdrawAcceptsRecentHistoricalRoot() public {
        // Deposit, snapshot the root, then deposit again (root moves on).
        vault.depositETH{value: 1 ether}(keccak256("histNote1"));
        bytes32 oldRoot = vault.noteTreeRoot();
        vault.depositETH{value: 1 ether}(keccak256("histNote2"));
        assertTrue(vault.noteTreeRoot() != oldRoot);

        // A proof generated against the old root is still spendable.
        bytes memory publicValues = abi.encode(
            true,
            keccak256("histNullifier"),
            address(0),
            uint256(0.5 ether),
            RECIPIENT,
            oldRoot
        );
        bytes memory sp1Proof = abi.encode(hex"1234", publicValues);

        vault.withdraw(address(0), 0.5 ether, RECIPIENT, sp1Proof);
        assertEq(RECIPIENT.balance, 0.5 ether);
    }

    // ─── Reentrancy ─────────────────────────────────────────────────────────

    function test_reentrantWithdrawBlocked() public {
        vault.depositETH{value: 1 ether}(keccak256("reNote"));
        ReentrantRecipient attacker = new ReentrantRecipient(vault);
        bytes32 root = vault.noteTreeRoot();

        // Inner proof: a fresh nullifier, otherwise valid. Without the
        // nonReentrant guard this reentrant withdrawal would SUCCEED.
        bytes32 innerNullifier = keccak256("reNullInner");
        bytes memory innerProof = abi.encode(
            hex"02",
            abi.encode(true, innerNullifier, address(0), uint256(0.25 ether), address(attacker), root)
        );
        attacker.arm(innerProof, 0.25 ether);

        bytes memory outerProof = abi.encode(
            hex"01",
            abi.encode(true, keccak256("reNullOuter"), address(0), uint256(0.25 ether), address(attacker), root)
        );

        vault.withdraw(address(0), 0.25 ether, address(attacker), outerProof);

        assertTrue(attacker.reentryAttempted());
        assertFalse(attacker.reentrySucceeded());
        assertEq(address(attacker).balance, 0.25 ether); // only the outer withdrawal paid
        assertFalse(vault.usedNullifiers(innerNullifier)); // inner nullifier not consumed
    }

    // ─── View Functions ─────────────────────────────────────────────────────

    function test_isNullifierUsed() public {
        bytes32 nullifier = keccak256("viewNullifier");
        assertFalse(vault.isNullifierUsed(nullifier));
    }

    // ─── Receive ETH (for test contract) ────────────────────────────────────
    receive() external payable {}
}
