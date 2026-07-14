# MoonRugToken — human triage of the `dregg-audit` run

Companion to the auto-generated `MoonRugToken.audit.md`. The pipeline emits stage-C
(codex) findings as **TRIAGE-REQUIRED**; this file is the human step (the
`docs/deos/LAUNCHPAD-CONTRACT-AUDIT.md` division of labor: codex hunts and reasons;
a human verifies each against source and assigns a verdict). Every verdict below was
checked against `samples/MoonRugToken.sol` at the cited line.

## Convergence — the headline

Three independent stages agree on the load-bearing defect, the **mintable-supply
rug door**:
- **Stage A** (grep): `mint` PRESENT with *no one-shot latch or cap enforcement*.
- **Stage B** (Halmos): a **machine-checked counterexample** — `mint` with `v = 2^255`
  by the owner drives `totalSupply > cap` (`check_cap_singleCall` + `check_cap_twoMints`
  both FAIL). This is a proof, not a heuristic.
- **Stage C** (codex): "Owner can mint unlimited supply and drain market liquidity"
  (Critical).

That convergence is the value of the multi-stage pipeline: the deterministic scan
flags the surface, the symbolic prover *proves* it exploitable, and the LLM explains
the exploit path and proposes the fix.

## Triage table (all 15 codex findings, verified vs source)

| # | codex finding | Sev | Verdict | Source check |
|---|---------------|-----|---------|--------------|
| 1 | Owner mints unlimited supply | Critical | **CONFIRMED-REAL** | `mint` (:61-66) `onlyOwner`, no latch, no `amount<=cap`. Also Halmos-proved (§B). |
| 2 | Owner seizes any balance | Critical | **CONFIRMED-REAL** | `seize` (:98-102) moves any `balanceOf[from]`, `onlyOwner`, no consent. |
| 3 | Pause+whitelist honeypot | Critical | **CONFIRMED-REAL** | `_transfer` (:89) `require(!paused || isWhitelisted[from])` + `setPaused`/`setWhitelist` (:104,:113). |
| 4 | Selective blacklist | High | **CONFIRMED-REAL** | `_transfer` (:90) `require(!blacklisted[from])` + `setBlacklist` (:108). |
| 5 | Indefinite freeze (DoS) | High | **CONFIRMED-REAL** | `setPaused` (:104) has no deadline/auto-unpause; overlaps #3 on the DoS axis. |
| 6 | selfdestruct kill | Medium | **CONFIRMED-REAL** | `kill` (:117-119) `selfdestruct`. codex's post-Cancun EIP-6780 nuance is correct and honest. |
| 7 | ERC-20 approve-race | Medium | **CONFIRMED-REAL (known-class)** | `approve` (:79) sets allowance directly; the classic approve front-run. Standard ERC-20 residual, not MoonRug-specific. |
| 8 | Zero-address transfers | Low | **CONFIRMED-REAL** | no `to != address(0)` guard in `mint`/`_transfer`/`seize`; codex's "owner can `seize` from `address(0)`" note is accurate. |
| 9 | Catastrophic centralization | Info | **CONFIRMED-REAL (context)** | correct — modifiers are present; the danger is the *granted* powers, not a missing modifier. |
| 10 | No LP-removal fn | Info | **VERIFIED-ABSENT** | no AMM/LP logic in source (agrees with §A). |
| 11 | No proxy/delegatecall | Info | **VERIFIED-ABSENT** | agrees with §A door 3 ABSENT. |
| 12 | No transfer-tax | Info | **VERIFIED-ABSENT** | agrees with §A door 9 ABSENT; `_transfer` moves equal `value` in/out. |
| 13 | No reentrancy | Info | **VERIFIED-SAFE** | no external calls / receiver callbacks in the token surface. |
| 14 | Checked arithmetic | Info | **VERIFIED-SAFE** | 0.8.20 checked math, no `unchecked` blocks. |
| 15 | No oracle/pricing | Info | **VERIFIED-ABSENT** | no price-dependent accounting in source. |

## False-positive rate on this run

**Zero false positives.** On this deliberately-hostile sample codex was accurate on
every call, including correctly reporting the *absent* classes (proxy, LP-removal,
tax, reentrancy) rather than hallucinating them. That is not a guarantee for every
contract — in the launchpad self-audit (`docs/deos/LAUNCHPAD-CONTRACT-AUDIT.md`)
codex both over-called (a blanket "no asset can be lost") and under-called (missed
the concrete stuck-funds bug), which is exactly why the human triage step is
mandatory and not skippable. Here it confirms; there it corrected.

## Proposed remediation (audit + propose — a developer applies)

The contract is an intentional rug composite; the honest remediation is not a
one-line patch but a redesign toward the DREGG anti-rug shape:
- **mint**: one-shot latch + `amount <= cap` + immutable `minter` (the
  `chain/contracts/launchpad/DreggLaunchToken.sol` shape — Halmos-proven safe).
- **seize / kill / setPaused / setBlacklist / setWhitelist**: delete. There is no
  legitimate anti-rug design in which an owner can move arbitrary balances, freeze
  holders, or destroy the contract.
- **approve**: adopt increase/decrease-allowance or a reviewed ERC-20 base.
- **zero-address**: reject `address(0)` recipients; add an explicit supply-reducing
  burn if burning is intended.

This is the honest boundary of the tool: it **audits and proposes**; a developer
applies the fixes and re-runs the pipeline (a fixed token would flip §B from
COUNTEREXAMPLE to PROVEN and clear the §A mint door).
