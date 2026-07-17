#!/usr/bin/env python3
"""emit_token.py — the token-factory EMIT stage.

Given a token SPEC (JSON: name, symbol, decimals, cap, mint_authority, tokenomics)
this emits a concrete launch-token Solidity contract and prints the emitted
template kind to stdout ("fv-safe" or "unsafe-variant").

Two emit paths, decided by `mint_authority`:

  * "launchpad-oneshot"  -> the FV'd template, GENUINELY DERIVED. `emit_safe`
    READS chain/contracts/launchpad/DreggLaunchToken.sol at emit time and applies
    exactly the count-checked substitutions listed in SAFE_SUBSTITUTIONS (contract
    name; name/symbol/decimals/cap storage -> compile-time constants; the 4-arg
    constructor -> a minter-only constructor, with the template's `cap_ == 0`
    guard enforced at emit time instead). EVERY function body (mint, transfer,
    approve, transferFrom, _transfer) is carried BYTE-FOR-BYTE from the FV'd
    file — `verify_derivation` re-checks that on every emit, and a template that
    has drifted from the declared anchors makes the emit FAIL LOUDLY rather than
    silently diverge. The hard cap is baked as a source-level LITERAL (disclosed
    by construction), the ONLY mint is the template's one-shot latch, and there
    is NO other door (no owner role, no seize, no pause, no blacklist, no
    selfdestruct, no upgrade). The emitted token's cap is then Halmos-proven
    downstream over its own compiled bytecode.

  * anything else (e.g. "owner-refillable") -> an UNSAFE variant. The safe
    template structurally CANNOT express "let the owner mint more later", so a
    spec that asks for it produces a contract with an owner-role uncapped mint.
    The factory does not pre-judge the spec: it emits what the spec implies and
    lets the AUDIT be the gate. This contract is CAUGHT downstream (Halmos
    counterexample + rug-forensics owner door) and REJECTED — never shipped.

This is NOT an LLM. The "AI-assisted" front is the structured spec-builder that
produces the JSON spec (see README "The AI-generation front"); an LLM provider that
drafts the spec from a natural-language prompt is the honestly-labeled wire-later.
The dreggic value is this FV+audit backend, not the spec drafting.
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))
TEMPLATE_PATH = os.path.join(REPO, "chain", "contracts", "launchpad", "DreggLaunchToken.sol")

# The function bodies that carry the FV pedigree. Each must appear byte-for-byte
# in BOTH the template and the emitted contract (checked by verify_derivation on
# every emit) — the mint one-shot latch + cap guard and the ERC-20 surface are
# exactly the code the template's audit/Halmos runs exercised.
PEDIGREE_FUNCTIONS = ["mint", "transfer", "approve", "transferFrom", "_transfer"]


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


def read_template() -> str:
    try:
        return open(TEMPLATE_PATH).read()
    except OSError as e:
        raise SystemExit(f"emit_token: cannot read the FV'd template {TEMPLATE_PATH}: {e}")


def subst_once(text: str, old: str, new: str, what: str) -> str:
    """Replace exactly one occurrence of `old`, or fail loudly.

    This is the derivation's honesty tooth: if the FV'd template drifts so that a
    declared anchor no longer matches exactly once, the emit REFUSES rather than
    silently shipping a divergent contract under the template's pedigree.
    """
    n = text.count(old)
    if n != 1:
        raise SystemExit(
            f"emit_token: TEMPLATE DRIFT — expected exactly 1 occurrence of {what} "
            f"in {TEMPLATE_PATH}, found {n}. The declared derivation no longer "
            f"matches the FV'd template; update emit_token.py's SAFE_SUBSTITUTIONS "
            f"against the template (and re-run the audit) instead of emitting a "
            f"divergent contract."
        )
    return text.replace(old, new, 1)


def extract_function(src: str, name: str) -> str:
    """Return the full `function <name>(...) ... { ... }` source text (brace-balanced)."""
    m = re.search(rf"\n(    function {re.escape(name)}\()", src)
    if not m:
        raise SystemExit(f"emit_token: function {name} not found for derivation check")
    start = m.start(1)
    i = src.index("{", start)
    depth = 0
    j = i
    while j < len(src):
        if src[j] == "{":
            depth += 1
        elif src[j] == "}":
            depth -= 1
            if depth == 0:
                return src[start : j + 1]
        j += 1
    raise SystemExit(f"emit_token: unbalanced braces extracting function {name}")


def verify_derivation(template: str, emitted: str) -> None:
    """Assert the emitted contract carries the template's safety shape verbatim.

    Every pedigree function body must appear in the emitted contract exactly as it
    reads in the FV'd template — byte-for-byte. Run on every safe emit; a failure
    is a bug in the emit stage and refuses the emit.
    """
    for fname in PEDIGREE_FUNCTIONS:
        body = extract_function(template, fname)
        if body not in emitted:
            raise SystemExit(
                f"emit_token: DERIVATION VIOLATION — the emitted contract's "
                f"`{fname}` is not byte-identical to the FV'd template's. Refusing "
                f"to emit under the template's pedigree."
            )


def safe_substitutions(spec: dict) -> list:
    """The exact, count-checked substitutions that parameterize the FV'd template.

    Everything NOT listed here is carried byte-for-byte from
    chain/contracts/launchpad/DreggLaunchToken.sol.
    """
    cname = solidity_identifier(spec["name"]) + "Launch"
    decimals = int(spec["decimals"])
    cap = base_units(int(spec["cap"]), decimals)
    name_lit = sol_str(spec["name"])
    sym_lit = sol_str(spec["symbol"])
    return [
        # 1. Contract name.
        (
            "contract DreggLaunchToken {",
            f"contract {cname} {{",
            "the contract declaration",
        ),
        # 2. name/symbol storage -> compile-time constants (the spec's values).
        (
            "    string public name;\n    string public symbol;\n"
            "    uint8 public constant decimals = 18;",
            f"    string public constant name = {name_lit};\n"
            f"    string public constant symbol = {sym_lit};\n"
            f"    uint8 public constant decimals = {decimals};",
            "the name/symbol/decimals declarations",
        ),
        # 3. immutable cap -> a compile-time LITERAL (disclosed in source).
        (
            "    /// The disclosed hard cap (in base units). Fixed at construction; the only\n"
            "    /// mint may not exceed it, and after the single mint nothing more can enter\n"
            "    /// circulation.\n"
            "    uint256 public immutable cap;",
            f"    /// The disclosed hard cap — {spec['cap']} whole tokens x 10^{decimals} =\n"
            f"    /// {cap} base units, baked as a compile-time LITERAL by the factory emit\n"
            f"    /// (anyone reading the source verifies it). The only mint may not exceed\n"
            f"    /// it, and after the single mint nothing more can enter circulation.\n"
            f"    uint256 public constant cap = {cap};",
            "the cap declaration",
        ),
        # 4. The ZeroCap error: its runtime check moves to emit time (the factory
        #    rejects `cap <= 0` before emitting; cap is a compile-time literal here).
        (
            "    error ZeroCap();\n",
            "",
            "the ZeroCap error declaration",
        ),
        # 5. The 4-arg constructor -> minter-only (name/symbol/cap are constants now).
        (
            "    constructor(string memory name_, string memory symbol_, uint256 cap_, address minter_) {\n"
            "        if (cap_ == 0) revert ZeroCap();\n"
            "        name = name_;\n"
            "        symbol = symbol_;\n"
            "        cap = cap_;\n"
            "        minter = minter_;\n"
            "    }",
            "    /// name/symbol/cap are compile-time constants above (the factory's\n"
            "    /// emit-time parameterization); only the minter — the launchpad that\n"
            "    /// creates this token — binds at construction. The template's\n"
            "    /// `cap_ == 0` guard is enforced at emit time (the factory rejects a\n"
            "    /// non-positive cap before this file exists).\n"
            "    constructor(address minter_) {\n"
            "        minter = minter_;\n"
            "    }",
            "the constructor",
        ),
    ]


def emit_banner(spec: dict, n_subst: int) -> str:
    creator_bps = int(spec.get("tokenomics", {}).get("creator_allocation_bps", 0))
    vesting = spec.get("tokenomics", {}).get("vesting", "n/a")
    return f"""\
// ============================================================================
// EMITTED by tools/token-factory from spec "{spec['name']}" ({spec['symbol']}).
//
// DERIVED from the FV'd template chain/contracts/launchpad/DreggLaunchToken.sol:
// the template file is READ at emit time and transformed by exactly {n_subst}
// count-checked substitutions (contract name; name/symbol/decimals/cap made
// compile-time constants from the spec; the constructor reduced to minter-only,
// its zero-cap guard enforced at emit time). Every function body — the one-shot
// `mint` latch and the ERC-20 surface — is carried BYTE-FOR-BYTE from the FV'd
// file and re-verified on every emit (emit_token.py: verify_derivation). The
// template's own doc-comments below are preserved verbatim.
//
// Disclosed tokenomics (a public input, displayed by the launch page):
//   creator allocation: {creator_bps} bps · vesting: {vesting}
//
// The emitted token's hard cap is then Halmos-PROVEN downstream over THIS
// contract's own compiled bytecode by the factory's auto-audit before it is
// marked verified-safe.
// ============================================================================
"""


def emit_safe(spec: dict) -> str:
    """Derive the emitted contract from the FV'd template (see module docstring)."""
    template = read_template()
    out = template
    subs = safe_substitutions(spec)
    for old, new, what in subs:
        out = subst_once(out, old, new, what)
    # Prepend the factory banner right after the license/pragma lines, keeping the
    # template's own @title doc-comment verbatim.
    anchor = "/// @title DreggLaunchToken"
    out = subst_once(
        out,
        anchor,
        emit_banner(spec, len(subs)) + anchor,
        "the template doc-comment anchor",
    )
    verify_derivation(template, out)
    return out


def emit_unsafe(spec: dict, authority: str) -> str:
    """Emit the variant a rug-y spec implies. CAUGHT by the audit, never shipped.

    A spec that asks for `mint_authority` the FV'd template cannot express (e.g.
    "owner-refillable" — "let me mint more later", the classic memecoin dump setup)
    produces an owner-role uncapped mint with no one-shot latch. Downstream: Halmos
    returns a counterexample (`totalSupply > cap`) and rug-forensics flags the owner
    door. The factory REJECTS it. (This variant is hand-written here, NOT derived
    from the FV'd template — by design: the template cannot express it.)
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
