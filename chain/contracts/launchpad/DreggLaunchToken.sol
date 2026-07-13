// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @title DreggLaunchToken
/// @notice A minimal, HARD-CAPPED ERC-20 minted exactly ONCE by its launchpad —
///         the on-chain enforcement of the design's "no hidden supply" theorem
///         (`docs/deos/DREGG-LAUNCHPAD-DESIGN.md` §2.1: the supply-authority
///         biconditional `execMintA_iff_spec` — a supply the schedule does not
///         disclose cannot enter circulation, "the ledger has no other mint
///         door"). This is the EVM twin of that door: `cap` is fixed at
///         construction, `mint` fires AT MOST ONCE for the full disclosed supply,
///         and there is no further mint path — so no post-launch inflation and no
///         undisclosed allocation can ever be minted.
///
/// Honest scope: this is the disclosure/cap ENFORCEMENT (BUILT, both polarities
/// tested). The Lean biconditional it mirrors is PROVED off-chain; this contract
/// makes the same guarantee unconstructable on the EVM by having no second mint.
contract DreggLaunchToken {
    // ─── ERC-20 metadata ──────────────────────────────────────────────────────
    string public name;
    string public symbol;
    uint8 public constant decimals = 18;

    // ─── Supply ───────────────────────────────────────────────────────────────
    /// The disclosed hard cap (in base units). Fixed at construction; the only
    /// mint may not exceed it, and after the single mint nothing more can enter
    /// circulation.
    uint256 public immutable cap;
    uint256 public totalSupply;

    /// The sole minter — the launchpad that created this token. Only it may fire
    /// the one-shot mint.
    address public immutable minter;

    /// The one-shot latch: true once the disclosed supply has been minted. A
    /// second mint (a "hidden supply" injection) reverts.
    bool public minted;

    // ─── Balances / allowances ────────────────────────────────────────────────
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    // ─── Events / errors ──────────────────────────────────────────────────────
    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);

    error NotMinter(address caller);
    error AlreadyMinted();
    error CapExceeded(uint256 requested, uint256 cap);
    error ZeroCap();
    error InsufficientBalance();
    error InsufficientAllowance();

    constructor(string memory name_, string memory symbol_, uint256 cap_, address minter_) {
        if (cap_ == 0) revert ZeroCap();
        name = name_;
        symbol = symbol_;
        cap = cap_;
        minter = minter_;
    }

    /// @notice The one and only mint. Fires at most once, for at most `cap` base
    ///         units, callable only by the launchpad. Every path to circulating
    ///         supply is this single disclosed mint — there is no other door.
    function mint(address to, uint256 amount) external {
        if (msg.sender != minter) revert NotMinter(msg.sender);
        if (minted) revert AlreadyMinted();
        if (amount > cap) revert CapExceeded(amount, cap);
        minted = true;
        totalSupply = amount;
        balanceOf[to] += amount;
        emit Transfer(address(0), to, amount);
    }

    // ─── ERC-20 ───────────────────────────────────────────────────────────────
    function transfer(address to, uint256 value) external returns (bool) {
        _transfer(msg.sender, to, value);
        return true;
    }

    function approve(address spender, uint256 value) external returns (bool) {
        allowance[msg.sender][spender] = value;
        emit Approval(msg.sender, spender, value);
        return true;
    }

    function transferFrom(address from, address to, uint256 value) external returns (bool) {
        uint256 a = allowance[from][msg.sender];
        if (a < value) revert InsufficientAllowance();
        if (a != type(uint256).max) allowance[from][msg.sender] = a - value;
        _transfer(from, to, value);
        return true;
    }

    function _transfer(address from, address to, uint256 value) private {
        uint256 bal = balanceOf[from];
        if (bal < value) revert InsufficientBalance();
        unchecked {
            balanceOf[from] = bal - value;
            balanceOf[to] += value;
        }
        emit Transfer(from, to, value);
    }
}
