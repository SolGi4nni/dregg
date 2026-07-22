// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @title MockStockToken — a TEST/mock ERC-20 standing in for a tokenized stock.
///
/// Rung 3 of the fair market. Robinhood-style tokenized stocks (e.g. a wrapped
/// NVDA) are plain, transferable ERC-20s; this is a minimal stand-in that the
/// coin/stock batch-cleared market (`BatchClearedMarket.sol`) prices trades in.
///
/// ⚠ TEST/DEMO ONLY. Unlike a real tokenized equity, this has an OPEN `mint`
/// (anyone can mint any amount) so a demo can hand every actor some mNVDA without
/// a faucet dance. It carries NO issuer, NO custody, NO KYC, NO redemption — it is
/// a stand-in for the market plumbing, not a security. Do not deploy to mainnet.
///
/// The ERC-20 surface is the same minimal, no-library shape as DreggLaunchToken
/// (transfer/transferFrom/approve, balanceOf/allowance, 18 decimals) so the market
/// can treat both legs uniformly.
contract MockStockToken {
    string public name;
    string public symbol;
    uint8 public constant decimals = 18;

    uint256 public totalSupply;
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);

    error InsufficientBalance();
    error InsufficientAllowance();

    constructor(string memory name_, string memory symbol_) {
        name = name_;
        symbol = symbol_;
    }

    /// @notice OPEN mint — anyone, any amount. TEST-ONLY (see contract notice).
    function mint(address to, uint256 amount) external {
        totalSupply += amount;
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
