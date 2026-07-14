# DREGG-kernel contract audit — `GOOD.sol`

Pipeline: `tools/dregg-audit/dregg-audit` · Generated: 2026-07-14T23:53:21Z
Target: `/Users/ember/dev/breadstuffs/tools/token-factory/artifacts/GOOD/GOOD.sol`

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
| 1 | owner/admin role | ABSENT | _(no match)_ |
| 2 | mintable supply (mint fn) | **PRESENT** | 59: `function mint(address to, uint256 amount) external {`<br> |
| 3 | proxy / upgradeable | ABSENT | _(no match)_ |
| 4 | selfdestruct / kill | ABSENT | _(no match)_ |
| 5 | honeypot / transfer-gate | ABSENT | _(no match)_ |
| 6 | blacklist | ABSENT | _(no match)_ |
| 7 | pausable / freeze | ABSENT | _(no match)_ |
| 8 | owner-drain / seize | ABSENT | _(no match)_ |
| 9 | fee / tax manipulation | ABSENT | _(no match)_ |

_Mint mitigation detected_ (one-shot latch / cap enforcement): the `mint`
door appears **bounded** — `37:    /// One-shot latch: true once the disclosed supply is minted. A`. Confirm in stage B.

## B. Formal verification — Halmos symbolic proof

Auto-generated symbolic harness (`fv-workspace/test/GenFV.t.sol`) proving the
**hard-cap** invariant (INV-CAP: `totalSupply <= cap` after any call, and over a
two-mint sequence) against the real compiled bytecode, all inputs symbolic. This
is the EVM twin of the Lean supply theorem `execMintA_iff_spec`
(`metatheory/Dregg2/Verify/KeystoneAuditSupply.lean:124`).

```
Running 2 tests for test/GenFV.t.sol:GenFV
[PASS] check_cap_singleCall(address,uint8,address,address,address,uint256) (paths: 13, time: 0.08s, bounds: [])
[PASS] check_cap_twoMints(address,address,address,uint256,address,address,uint256) (paths: 13, time: 0.08s, bounds: [])
Symbolic test result: 2 passed; 0 failed; time: 0.17s
```

**Result: PROVEN.** No counterexample — the hard cap holds over all inputs
for the bounded call depth. (Bounded proof; see `chain/formal-verification/`
README §The honest gap for the depth/overflow bounds this shares.)

## C. Adversarial audit — codex hostile pass (TRIAGE-REQUIRED)

_Skipped (`--no-codex`)._

## D. Triage summary

| Source | Finding | Verdict | Severity | Proposed fix |
|--------|---------|---------|----------|--------------|
| A (auto) | Rug doors present: mintable supply (mint fn) | **REVIEW** | High | Remove/constrain each present door; see §A |
| B (auto/proof) | Hard-cap invariant | PROVEN (hard cap holds, bounded) | Info | If COUNTEREXAMPLE: add one-shot latch + `amount<=cap` guard (see `DreggLaunchToken.mint`) |
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
