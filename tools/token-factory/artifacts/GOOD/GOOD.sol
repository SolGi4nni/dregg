// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// ============================================================================
// EMITTED by tools/token-factory from spec "Good Capped Token" (GOOD).
//
// DERIVED from the FV'd template chain/contracts/launchpad/DreggLaunchToken.sol:
// the template file is READ at emit time and transformed by exactly 5
// count-checked substitutions (contract name; name/symbol/decimals/cap made
// compile-time constants from the spec; the constructor reduced to minter-only,
// its zero-cap guard enforced at emit time). Every function body — the one-shot
// `mint` latch and the ERC-20 surface — is carried BYTE-FOR-BYTE from the FV'd
// file and re-verified on every emit (emit_token.py: verify_derivation). The
// template's own doc-comments below are preserved verbatim.
//
// Disclosed tokenomics (a public input, displayed by the launch page):
//   creator allocation: 500 bps · vesting: 12-month linear, launchpad-committed schedule
//
// The emitted token's hard cap is then Halmos-PROVEN downstream over THIS
// contract's own compiled bytecode by the factory's auto-audit before it is
// marked verified-safe.
// ============================================================================
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
contract GoodCappedTokenLaunch {
    // ─── ERC-20 metadata ──────────────────────────────────────────────────────
    string public constant name = "Good Capped Token";
    string public constant symbol = "GOOD";
    uint8 public constant decimals = 18;

    // ─── Supply ───────────────────────────────────────────────────────────────
    /// The disclosed hard cap — 1000000000 whole tokens x 10^18 =
    /// 1000000000000000000000000000 base units, baked as a compile-time LITERAL by the factory emit
    /// (anyone reading the source verifies it). The only mint may not exceed
    /// it, and after the single mint nothing more can enter circulation.
    uint256 public constant cap = 1000000000000000000000000000;
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
    error InsufficientBalance();
    error InsufficientAllowance();

    /// name/symbol/cap are compile-time constants above (the factory's
    /// emit-time parameterization); only the minter — the launchpad that
    /// creates this token — binds at construction. The template's
    /// `cap_ == 0` guard is enforced at emit time (the factory rejects a
    /// non-positive cap before this file exists).
    constructor(address minter_) {
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
