#!/usr/bin/env python3
"""emit_token.py — the token-factory EMIT stage.

Given a token SPEC (JSON: name, symbol, decimals, cap, mint_authority, tokenomics)
this emits a concrete launch-token Solidity contract and prints the emitted
template kind to stdout ("fv-safe" or "unsafe-variant").

Two emit paths, decided by `mint_authority`:

  * "launchpad-oneshot"  -> the FV'd template. A parameterization of
    chain/contracts/launchpad/DreggLaunchToken.sol: the hard cap is a source-level
    LITERAL (disclosed by construction), the ONLY mint is a one-shot latch callable
    by the launchpad, and there is NO other door (no owner role, no seize, no pause,
    no blacklist, no selfdestruct, no upgrade). The no-rug invariants are baked in by
    construction; the emitted token's cap is Halmos-PROVEN downstream.

  * anything else (e.g. "owner-refillable") -> an UNSAFE variant. The safe template
    structurally CANNOT express "let the owner mint more later", so a spec that asks
    for it produces a contract with an owner-role uncapped mint. The factory does not
    pre-judge the spec: it emits what the spec implies and lets the AUDIT be the gate.
    This contract is CAUGHT downstream (Halmos counterexample + rug-forensics owner
    door) and REJECTED — never shipped.

This is NOT an LLM. The "AI-assisted" front is the structured spec-builder that
produces the JSON spec (see README "The AI-generation front"); an LLM provider that
drafts the spec from a natural-language prompt is the honestly-labeled wire-later.
The dreggic value is this FV+audit backend, not the spec drafting.
"""
import json
import re
import sys


def sol_str(s: str) -> str:
    # Solidity string literal — reject anything needing escaping (specs are ascii names).
    if '"' in s or "\\" in s or "\n" in s:
        raise SystemExit(f"emit_token: unsafe character in string literal: {s!r}")
    return f'"{s}"'


def solidity_identifier(name: str) -> str:
    ident = re.sub(r"[^A-Za-z0-9]", "", name)
    if not ident or not ident[0].isalpha():
        ident = "Tok" + ident
    return ident


def base_units(cap_whole: int, decimals: int) -> int:
    return cap_whole * (10 ** decimals)


def emit_safe(spec: dict) -> str:
    """Emit the FV'd template, parameterized with the spec. Cap baked as a literal."""
    cname = solidity_identifier(spec["name"]) + "Launch"
    decimals = int(spec["decimals"])
    cap = base_units(int(spec["cap"]), decimals)
    name_lit = sol_str(spec["name"])
    sym_lit = sol_str(spec["symbol"])
    creator_bps = int(spec.get("tokenomics", {}).get("creator_allocation_bps", 0))
    vesting = spec.get("tokenomics", {}).get("vesting", "n/a")
    return f"""// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// ============================================================================
// EMITTED by tools/token-factory from spec "{spec['name']}" ({spec['symbol']}).
// Template: the FV'd launch token
//   (parameterization of chain/contracts/launchpad/DreggLaunchToken.sol).
//
// The no-rug invariants are baked in BY CONSTRUCTION:
//   * `cap` is a source-level LITERAL — the disclosed hard cap, {spec['cap']}
//     whole tokens = {cap} base units. Anyone reading the source verifies it.
//   * `mint` is a ONE-SHOT latch callable only by the launchpad (`minter`) — the
//     single disclosed mint. There is NO second mint path, so no post-launch
//     inflation and no undisclosed allocation can ever enter circulation.
//   * There is NO owner role, NO seize/drain, NO pause, NO blacklist, NO
//     selfdestruct, NO upgrade proxy, NO fee knob. Those doors do not exist.
//
// Disclosed tokenomics (a public input, displayed by the launch page):
//   creator allocation: {creator_bps} bps · vesting: {vesting}
//
// The EVM twin of the Lean supply theorem `execMintA_iff_spec`
// (metatheory/Dregg2/Verify/KeystoneAuditSupply.lean). The cap is Halmos-PROVEN
// by the factory's auto-audit before this token is marked verified-safe.
// ============================================================================
contract {cname} {{
    string public constant name = {name_lit};
    string public constant symbol = {sym_lit};
    uint8 public constant decimals = {decimals};

    /// The disclosed hard cap, baked as a compile-time literal (base units).
    uint256 public constant cap = {cap};
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

    constructor(address minter_) {{
        minter = minter_;
    }}

    /// The one and only mint. Fires at most once, for at most `cap` base units,
    /// callable only by the launchpad. Every path to circulating supply is this
    /// single disclosed mint — there is no other door.
    function mint(address to, uint256 amount) external {{
        if (msg.sender != minter) revert NotMinter(msg.sender);
        if (minted) revert AlreadyMinted();
        if (amount > cap) revert CapExceeded(amount, cap);
        minted = true;
        totalSupply = amount;
        balanceOf[to] += amount;
        emit Transfer(address(0), to, amount);
    }}

    function transfer(address to, uint256 value) external returns (bool) {{
        _transfer(msg.sender, to, value);
        return true;
    }}

    function approve(address spender, uint256 value) external returns (bool) {{
        allowance[msg.sender][spender] = value;
        emit Approval(msg.sender, spender, value);
        return true;
    }}

    function transferFrom(address from, address to, uint256 value) external returns (bool) {{
        uint256 a = allowance[from][msg.sender];
        if (a < value) revert InsufficientAllowance();
        if (a != type(uint256).max) allowance[from][msg.sender] = a - value;
        _transfer(from, to, value);
        return true;
    }}

    function _transfer(address from, address to, uint256 value) private {{
        uint256 bal = balanceOf[from];
        if (bal < value) revert InsufficientBalance();
        unchecked {{
            balanceOf[from] = bal - value;
            balanceOf[to] += value;
        }}
        emit Transfer(from, to, value);
    }}
}}
"""


def emit_unsafe(spec: dict, authority: str) -> str:
    """Emit the variant a rug-y spec implies. CAUGHT by the audit, never shipped.

    A spec that asks for `mint_authority` the FV'd template cannot express (e.g.
    "owner-refillable" — "let me mint more later", the classic memecoin dump setup)
    produces an owner-role uncapped mint with no one-shot latch. Downstream: Halmos
    returns a counterexample (`totalSupply > cap`) and rug-forensics flags the owner
    door. The factory REJECTS it.
    """
    cname = solidity_identifier(spec["name"]) + "Launch"
    decimals = int(spec["decimals"])
    cap = base_units(int(spec["cap"]), decimals)
    name_lit = sol_str(spec["name"])
    sym_lit = sol_str(spec["symbol"])
    return f"""// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// ============================================================================
// EMITTED by tools/token-factory from spec "{spec['name']}" ({spec['symbol']}).
// Template: UNSAFE variant — the spec requested mint_authority "{authority}",
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
contract {cname} {{
    string public constant name = {name_lit};
    string public constant symbol = {sym_lit};
    uint8 public constant decimals = {decimals};

    /// The "disclosed" cap — a literal, but NOT enforced by mint() below.
    uint256 public constant cap = {cap};
    uint256 public totalSupply;
    address public owner;

    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);

    modifier onlyOwner() {{
        require(msg.sender == owner, "not owner");
        _;
    }}

    constructor() {{
        owner = msg.sender;
    }}

    /// UNSAFE: owner-refillable mint. No one-shot latch, no cap check — the owner can
    /// mint an unbounded overdose past the disclosed `cap` and dump. This is exactly
    /// what "{authority}" asks for and exactly what the audit rejects.
    function mint(address to, uint256 amount) external onlyOwner {{
        totalSupply += amount;
        balanceOf[to] += amount;
        emit Transfer(address(0), to, amount);
    }}

    function transfer(address to, uint256 value) external returns (bool) {{
        _transfer(msg.sender, to, value);
        return true;
    }}

    function approve(address spender, uint256 value) external returns (bool) {{
        allowance[msg.sender][spender] = value;
        emit Approval(msg.sender, spender, value);
        return true;
    }}

    function transferFrom(address from, address to, uint256 value) external returns (bool) {{
        allowance[from][msg.sender] -= value;
        _transfer(from, to, value);
        return true;
    }}

    function _transfer(address from, address to, uint256 value) internal {{
        balanceOf[from] -= value;
        balanceOf[to] += value;
        emit Transfer(from, to, value);
    }}
}}
"""


REQUIRED = ["name", "symbol", "decimals", "cap", "mint_authority"]


def main():
    if len(sys.argv) != 3:
        raise SystemExit("usage: emit_token.py <spec.json> <out.sol>")
    spec = json.load(open(sys.argv[1]))
    missing = [k for k in REQUIRED if k not in spec]
    if missing:
        raise SystemExit(f"emit_token: spec missing required fields: {missing}")
    if int(spec["cap"]) <= 0:
        raise SystemExit("emit_token: cap must be positive (a hard cap of 0 is meaningless)")

    authority = spec["mint_authority"]
    if authority == "launchpad-oneshot":
        code, kind = emit_safe(spec), "fv-safe"
    else:
        code, kind = emit_unsafe(spec, authority), "unsafe-variant"

    open(sys.argv[2], "w").write(code)
    print(kind)


if __name__ == "__main__":
    main()
