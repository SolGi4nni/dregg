// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// ============================================================================
// RECONSTRUCTED KNOWN-RUG SAMPLE — NOT a real project, NOT deployable-with-intent.
//
// This is a *composite* of publicly documented launchpad-token rug mechanisms,
// hand-reconstructed so the `dregg-audit` pipeline can be demonstrated on a
// NON-DREGG, deliberately-hostile contract. Every door below is cited to the
// real case whose mechanism it reproduces (see docs/deos/RUG-FORENSICS-VS-DREGG.md):
//
//   * mintable-supply overdose ....... owner mint() with NO cap / NO one-shot latch
//                                      (Coinmonks/DEXTools mintable-supply classic §1.5)
//   * honeypot sell-block ............ transfer gated by an owner whitelist bypass
//                                      (SQUID `marketersAndDevs`, §1.4)
//   * pausable-then-freeze ........... owner can pause all non-whitelisted transfers
//   * blacklist single-out ........... owner can block a specific holder's transfers
//   * owner-drain / seize ............ owner moves any holder's balance at will
//                                      (HypervaultFi privileged withdrawal class §1.2)
//   * selfdestruct kill .............. owner can destroy the contract
//
// Public block explorers return HTTP 403 to automated fetch (Cloudflare), so the
// verified bytecode of the cited rugs cannot be pulled byte-for-byte into the repo
// (same sourcing constraint documented in RUG-FORENSICS-VS-DREGG.md). This file
// reconstructs the *documented mechanism* rather than inventing a specific victim's
// source. It exists ONLY as an audit target for the pipeline.
// ============================================================================

contract MoonRugToken {
    string public name = "MoonRug";
    string public symbol = "MOON";
    uint8 public constant decimals = 18;

    uint256 public totalSupply;
    uint256 public cap; // "disclosed" hard cap — NOT actually enforced by mint()
    address public owner;

    bool public paused;

    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;
    mapping(address => bool) public isWhitelisted; // SQUID `marketersAndDevs` analogue
    mapping(address => bool) public blacklisted;

    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);

    modifier onlyOwner() {
        require(msg.sender == owner, "not owner");
        _;
    }

    constructor(uint256 cap_) {
        owner = msg.sender;
        cap = cap_;
    }

    // RUG DOOR #1 — mintable supply. onlyOwner, NO one-shot latch, and it does NOT
    // enforce `cap`. The dev waits for the price to rise, mints an overdose to their
    // own wallet, and dumps. `totalSupply` can exceed the "disclosed" `cap` freely.
    function mint(address to, uint256 amount) external onlyOwner {
        totalSupply += amount;
        balanceOf[to] += amount;
        emit Transfer(address(0), to, amount);
    }

    function transfer(address to, uint256 value) external returns (bool) {
        _transfer(msg.sender, to, value);
        return true;
    }

    function transferFrom(address from, address to, uint256 value) external returns (bool) {
        allowance[from][msg.sender] -= value;
        _transfer(from, to, value);
        return true;
    }

    function approve(address spender, uint256 value) external returns (bool) {
        allowance[msg.sender][spender] = value;
        emit Approval(msg.sender, spender, value);
        return true;
    }

    // RUG DOOR #2/#3/#4 — honeypot + pausable + blacklist. A non-whitelisted holder
    // cannot transfer (sell) while `paused`, and any `blacklisted` holder can never
    // transfer. Buyers can buy; the owner flips `paused`/whitelist so only insiders
    // can sell. This is the SQUID transfer-restriction mechanism.
    function _transfer(address from, address to, uint256 value) internal {
        require(!paused || isWhitelisted[from], "trading paused");
        require(!blacklisted[from], "blacklisted");
        balanceOf[from] -= value;
        balanceOf[to] += value;
        emit Transfer(from, to, value);
    }

    // RUG DOOR #5 — owner-drain / seize. The owner can move ANY holder's tokens to
    // itself with no consent, no floor, no disclosure (HypervaultFi privileged path).
    function seize(address from, address to, uint256 value) external onlyOwner {
        balanceOf[from] -= value;
        balanceOf[to] += value;
        emit Transfer(from, to, value);
    }

    function setPaused(bool p) external onlyOwner {
        paused = p;
    }

    function setBlacklist(address a, bool b) external onlyOwner {
        blacklisted[a] = b;
    }

    function setWhitelist(address a, bool b) external onlyOwner {
        isWhitelisted[a] = b;
    }

    // RUG DOOR #6 — selfdestruct kill switch.
    function kill() external onlyOwner {
        selfdestruct(payable(owner));
    }
}
