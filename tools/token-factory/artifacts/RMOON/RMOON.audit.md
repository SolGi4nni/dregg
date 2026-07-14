# DREGG-kernel contract audit — `RMOON.sol`

Pipeline: `tools/dregg-audit/dregg-audit` · Generated: 2026-07-14T23:53:32Z
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
**hard-cap** invariant (INV-CAP: `totalSupply <= cap` after any call, and over a
two-mint sequence) against the real compiled bytecode, all inputs symbolic. This
is the EVM twin of the Lean supply theorem `execMintA_iff_spec`
(`metatheory/Dregg2/Verify/KeystoneAuditSupply.lean:124`).

```
Running 2 tests for test/GenFV.t.sol:GenFV
Counterexample: 
[FAIL] check_cap_singleCall(uint8,address,address,address,uint256) (paths: 12, time: 0.08s, bounds: [])
Counterexample: 
Counterexample: 
Counterexample: 
[FAIL] check_cap_twoMints(address,address,uint256,address,address,uint256) (paths: 13, time: 0.10s, bounds: [])
Symbolic test result: 0 passed; 2 failed; time: 0.19s
```

**Result: HALMOS FOUND A COUNTEREXAMPLE — the hard cap is NOT enforced.**
Symbolic execution reached a state where `totalSupply > cap`. This is a
machine-proved mintable-supply defect (CONFIRMED-REAL, no human triage needed
— it is a proof, not a heuristic).

## C. Adversarial audit — codex hostile pass (TRIAGE-REQUIRED)

_Skipped (`--no-codex`)._

## D. Triage summary

| Source | Finding | Verdict | Severity | Proposed fix |
|--------|---------|---------|----------|--------------|
| A (auto) | Rug doors present: owner/admin role mintable supply (mint fn) | **REVIEW** | High | Remove/constrain each present door; see §A |
| B (auto/proof) | Hard-cap invariant | COUNTEREXAMPLE (invariant violated) | Critical | If COUNTEREXAMPLE: add one-shot latch + `amount<=cap` guard (see `DreggLaunchToken.mint`) |
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
