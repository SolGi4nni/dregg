// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// ============================================================================
// EMITTED by tools/token-factory from spec "Good Capped Token" (GOOD).
// Template: the FV'd launch token
//   (parameterization of chain/contracts/launchpad/DreggLaunchToken.sol).
//
// The no-rug invariants are baked in BY CONSTRUCTION:
//   * `cap` is a source-level LITERAL — the disclosed hard cap, 1000000000
//     whole tokens = 1000000000000000000000000000 base units. Anyone reading the source verifies it.
//   * `mint` is a ONE-SHOT latch callable only by the launchpad (`minter`) — the
//     single disclosed mint. There is NO second mint path, so no post-launch
//     inflation and no undisclosed allocation can ever enter circulation.
//   * There is NO owner role, NO seize/drain, NO pause, NO blacklist, NO
//     selfdestruct, NO upgrade proxy, NO fee knob. Those doors do not exist.
//
// Disclosed tokenomics (a public input, displayed by the launch page):
//   creator allocation: 500 bps · vesting: 12-month linear, launchpad-committed schedule
//
// The EVM twin of the Lean supply theorem `execMintA_iff_spec`
// (metatheory/Dregg2/Verify/KeystoneAuditSupply.lean). The cap is Halmos-PROVEN
// by the factory's auto-audit before this token is marked verified-safe.
// ============================================================================
contract GoodCappedTokenLaunch {
    string public constant name = "Good Capped Token";
    string public constant symbol = "GOOD";
    uint8 public constant decimals = 18;

    /// The disclosed hard cap, baked as a compile-time literal (base units).
    uint256 public constant cap = 1000000000000000000000000000;
    uint256 public totalSupply;

    /// The sole minter — the launchpad that created this token.
    address public immutable minter;

    /// One-shot latch: true once the disclosed supply is minted. A second mint reverts.
    bool public minted;

    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);

    error NotMinter(address caller);
    error AlreadyMinted();
    error CapExceeded(uint256 requested, uint256 cap);
    error InsufficientBalance();
    error InsufficientAllowance();

    constructor(address minter_) {
        minter = minter_;
    }

    /// The one and only mint. Fires at most once, for at most `cap` base units,
    /// callable only by the launchpad. Every path to circulating supply is this
    /// single disclosed mint — there is no other door.
    function mint(address to, uint256 amount) external {
        if (msg.sender != minter) revert NotMinter(msg.sender);
        if (minted) revert AlreadyMinted();
        if (amount > cap) revert CapExceeded(amount, cap);
        minted = true;
        totalSupply = amount;
        balanceOf[to] += amount;
        emit Transfer(address(0), to, amount);
    }

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
