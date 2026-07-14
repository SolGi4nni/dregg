// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// ============================================================================
// EMITTED by tools/token-factory from spec "Refillable Moon Token" (RMOON).
// Template: UNSAFE variant — the spec requested mint_authority "owner-refillable",
// which the FV'd launch-token template structurally CANNOT express (the safe
// template has exactly one one-shot mint and no owner role).
//
// The factory does not pre-judge the spec: it emits what the spec implies and lets
// the AUDIT be the gate. This contract carries an owner-role uncapped `mint` with
// NO one-shot latch and NO `amount <= cap` guard — the classic mintable-supply rug
// ("mint more later, dump on holders"). The factory's auto-audit CATCHES it (Halmos
// counterexample: totalSupply > cap; rug-forensics: owner door) and REJECTS it.
// It is NEVER shipped as a verified-safe token. This is the differentiator: a rug-y
// spec is caught before it ships, not deployed.
// ============================================================================
contract RefillableMoonTokenLaunch {
    string public constant name = "Refillable Moon Token";
    string public constant symbol = "RMOON";
    uint8 public constant decimals = 18;

    /// The "disclosed" cap — a literal, but NOT enforced by mint() below.
    uint256 public constant cap = 1000000000000000000000000000;
    uint256 public totalSupply;
    address public owner;

    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);

    modifier onlyOwner() {
        require(msg.sender == owner, "not owner");
        _;
    }

    constructor() {
        owner = msg.sender;
    }

    /// UNSAFE: owner-refillable mint. No one-shot latch, no cap check — the owner can
    /// mint an unbounded overdose past the disclosed `cap` and dump. This is exactly
    /// what "owner-refillable" asks for and exactly what the audit rejects.
    function mint(address to, uint256 amount) external onlyOwner {
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
        allowance[from][msg.sender] -= value;
        _transfer(from, to, value);
        return true;
    }

    function _transfer(address from, address to, uint256 value) internal {
        balanceOf[from] -= value;
        balanceOf[to] += value;
        emit Transfer(from, to, value);
    }
}
