# DREGG-kernel contract audit — `RMOON.sol`

Pipeline: `tools/dregg-audit/dregg-audit` · Generated: 2026-07-17T06:19:44Z
Target: `/Users/ember/dev/breadstuffs/tools/token-factory/artifacts/RMOON/RMOON.sol`

> **Assisted-audit tool, not a certification.** Stages A (rug-forensics) and
> B (formal verification) are machine-decided. Stage C (codex) is an LLM
> adversarial pass whose findings are emitted **TRIAGE-REQUIRED** — a human
> must confirm each against source. This tool finds + proposes; it does **not**
> auto-rewrite to secure, and green here is **not** a security guarantee.

## A. Rug-forensics — the rug-door taxonomy

Deterministic scan for the rug doors dissected in
`docs/deos/RUG-FORENSICS-VS-DREGG.md` (owner-drain / hidden-mint / proxy-upgrade
/ honeypot / blacklist / pause / selfdestruct / fee-manipulation). A door marked
PRESENT is a *surface to review*, not proof of a rug; ABSENT means the pattern
does not occur in source (structural absence, the strongest anti-rug signal).

| # | Rug door | Verdict | Evidence (line:match) |
|---|----------|---------|-----------------------|
| 1 | owner/admin role | **PRESENT** | 34: `modifier onlyOwner() {`<br>35: `require(msg.sender == owner, "not owner");`<br>46: `function mint(address to, uint256 amount) external onlyOwner`<br> |
| 2 | mintable supply (mint fn) | **PRESENT** | 46: `function mint(address to, uint256 amount) external onlyOwner`<br> |
| 3 | proxy / upgradeable | ABSENT | _(no match)_ |
| 4 | selfdestruct / kill | ABSENT | _(no match)_ |
| 5 | honeypot / transfer-gate | ABSENT | _(no match)_ |
| 6 | blacklist | ABSENT | _(no match)_ |
| 7 | pausable / freeze | ABSENT | _(no match)_ |
| 8 | owner-drain / seize | ABSENT | _(no match)_ |
| 9 | fee / tax manipulation | ABSENT | _(no match)_ |

_No mint mitigation detected_: `mint` has **no visible one-shot latch or cap
enforcement** — a likely mintable-supply rug door. Stage B will attempt to
prove or refute the hard cap symbolically.

## B. Formal verification — Halmos symbolic proof

Auto-generated symbolic harness (`fv-workspace/test/GenFV.t.sol`) proving the
standard anti-rug invariants against the real compiled bytecode, all inputs
symbolic: **INV-CAP** (`totalSupply<=cap`, EVM twin of the Lean supply theorem
`execMintA_iff_spec`, `metatheory/Dregg2/Verify/KeystoneAuditSupply.lean:124`),
and — when the shape exposes them — **INV-NODRAIN** (owner-drain/seize),
**INV-REENTRANCY** (ETH-conservation guard) and **INV-ACCESS-CONTROL** (mint
confined to its `minter`/`owner` role). The deep both-polarity re-entry proof is
the hand-written spec `chain/formal-verification/DreggReentrancyFV.t.sol`.

```
Running 5 tests for test/GenFV.t.sol:GenFV
Counterexample: 
[FAIL] check_cap_singleCall(uint8,address,address,address,uint256) (paths: 12, time: 0.29s, bounds: [])
Counterexample: 
Counterexample: 
Counterexample: 
[FAIL] check_cap_twoMints(address,address,uint256,address,address,uint256) (paths: 14, time: 0.23s, bounds: [])
[PASS] check_noReentrancyDrain(address,uint8,address,address,uint256) (paths: 10, time: 0.11s, bounds: [])
[PASS] check_noUnauthorizedDrain(address,uint256,uint8,address,address,address,uint256) (paths: 13, time: 0.32s, bounds: [])
[PASS] check_privilegedOpsAuthorized(address,address,uint256) (paths: 3, time: 0.03s, bounds: [])
Symbolic test result: 3 passed; 2 failed; time: 1.00s
```

| Invariant | Check | Verdict |
|-----------|-------|---------|
| INV-CAP — hard cap `totalSupply<=cap` (door #2, mintable supply) | `check_cap_singleCall` | **COUNTEREXAMPLE** |
| INV-CAP — hard cap `totalSupply<=cap` (door #2, mintable supply) | `check_cap_twoMints` | **COUNTEREXAMPLE** |
| INV-REENTRANCY — no external call drains held ETH (reentrancy, ETH-conservation form) | `check_noReentrancyDrain` | PROVEN |
| INV-NODRAIN — no unauthorized balance drain (door #8, owner-drain/seize) | `check_noUnauthorizedDrain` | PROVEN |
| INV-ACCESS-CONTROL — privileged op confined to its role (door #1, owner/admin) | `check_privilegedOpsAuthorized` | PROVEN |

**Result: HALMOS FOUND 2 COUNTEREXAMPLE(S).** The invariant(s)
below are machine-DISPROVEN (CONFIRMED-REAL, no human triage — it is a proof):
- INV-CAP — hard cap `totalSupply<=cap` (door #2, mintable supply)
- INV-CAP — hard cap `totalSupply<=cap` (door #2, mintable supply)

Still PROVEN (hold over all inputs, bounded): check_noReentrancyDrain check_noUnauthorizedDrain check_privilegedOpsAuthorized .
(A door can pass one invariant and fail another — e.g. a mint that respects
the cap but is missing its access-check passes INV-CAP and fails
INV-ACCESS-CONTROL.)

## C. Adversarial audit — codex hostile pass (TRIAGE-REQUIRED)

_Skipped (`--no-codex`)._

## D. Triage summary

| Source | Finding | Verdict | Severity | Proposed fix |
|--------|---------|---------|----------|--------------|
| A (auto) | Rug doors present: owner/admin role mintable supply (mint fn) | **REVIEW** | High | Remove/constrain each present door; see §A |
| B (auto/proof) | Hard-cap invariant | COUNTEREXAMPLE (2 invariant(s) violated) | Critical | If COUNTEREXAMPLE: add one-shot latch + `amount<=cap` guard (see `DreggLaunchToken.mint`) |
| C (codex) | see §C | **TRIAGE-REQUIRED** | per-finding | per-finding; human confirms vs source |

**Verdict legend.** Stage A/B rows are machine-decided. Stage C rows require a
human to mark each finding CONFIRMED-REAL / FALSE-POSITIVE / KNOWN-RESIDUAL
against the source (the `docs/deos/LAUNCHPAD-CONTRACT-AUDIT.md` division of labor:
codex hunts + reasons; a human verifies + reproduces). A confirmed bug should be
reproduced with a failing test before the proposed fix is applied by a developer.

---
_Assisted-audit tool — finds vulns + proposes fixes with a proof where a standard
invariant applies. NOT a push-button certification (needs human review); does NOT
auto-rewrite to secure (audit + propose; a developer applies)._
