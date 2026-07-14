# The DREGG contract-audit service — onboard any contract through a DREGG-kernel audit

A repeatable pipeline that takes a Solidity contract and produces a structured audit
report: the rug doors it contains, the invariants it does or does not satisfy (with a
machine proof where one applies), the adversarial findings triaged against source, and
a proposed fix for each. It is the productized form of the ad-hoc audit we ran on our
own launchpad — the rug-forensics scrape (`RUG-FORENSICS-VS-DREGG.md`), the Halmos
formal verification (`chain/formal-verification/`), and the codex adversarial pass
(`LAUNCHPAD-CONTRACT-AUDIT.md`) — made pointable at any contract.

Tool: `tools/dregg-audit/dregg-audit`. Sample run: `tools/dregg-audit/reports/`.

## What it is — and what it is NOT (read first)

This is an **assisted-audit tool**. It **finds** vulnerabilities and **proposes**
fixes, with a **machine proof** where a standard invariant applies.

- It is **NOT a push-button certification.** A real audit needs human judgment; the
  pipeline's LLM stage is emitted *triage-required*, not *approved*. Green here is not
  a clean bill of health, and no output should be marketed as "DREGG-certified safe".
- It does **NOT auto-rewrite the contract to secure.** Automatically transforming an
  insecure contract into a secure one is a research problem, not this tool. The
  pipeline **audits and proposes**; a developer applies the fix and re-runs. When the
  service says "fix/rewrite under DREGG," that assistance is *analysis + a proposed
  patch a human applies* — never an automatic secure rewrite.
- Its guarantees are **bounded** exactly as the underlying tools are (the Halmos proof
  is symbolic-bounded in call depth and reserve magnitude; the grep scan reasons about
  *source as written*, not deployed bytecode or proxy status). Those bounds travel with
  every report.

## The four stages

| Stage | Tool | Decided by | What it produces |
|-------|------|-----------|------------------|
| **A. Rug-forensics** | deterministic `grep` over the rug-door taxonomy | machine | each of 9 rug doors PRESENT / ABSENT with evidence lines |
| **B. Formal verification** | Halmos symbolic EVM on the real bytecode | machine (proof) | INV-CAP PROVEN / COUNTEREXAMPLE, or scaffold-only |
| **C. Adversarial audit** | `codex exec --sandbox read-only` hostile pass | LLM | severity-ranked findings, each **TRIAGE-REQUIRED** |
| **D. Triage + report** | assembler + human verifier | human confirms C | one markdown report + a triage verdict per finding |

### A — rug-forensics (the taxonomy check)
Scans for the nine rug doors dissected in `RUG-FORENSICS-VS-DREGG.md`: owner/admin
role, mintable supply, proxy/upgradeable, selfdestruct, honeypot transfer-gate,
blacklist, pausable, owner-drain/seize, fee/tax manipulation. Deterministic and
machine-decided: **ABSENT** means the pattern does not occur in source (a structural
absence — the strongest anti-rug signal); **PRESENT** flags a surface to review (a
`mint` fn is a door only *absent* a one-shot latch + cap guard, which the scan also
checks for and notes).

### B — formal verification (the proof)
Auto-generates a Halmos harness for the ERC-20 **supply-cap** shape (a `mint` fn plus
public `cap`/`totalSupply`) and proves `totalSupply <= cap` over **all inputs** against
the **real compiled bytecode** — the EVM twin of the Lean supply theorem
`execMintA_iff_spec` (`metatheory/Dregg2/Verify/KeystoneAuditSupply.lean:124`). A
hard-capped one-shot token is *proven*; an uncapped/owner-mintable token yields a
*counterexample* (a concrete witness that the cap is not enforced). Halmos is chosen
over solc's CHC because CHC is *unsound* on custom-error guards (documented in
`chain/formal-verification/README.md`). Non-token shapes (e.g. pool-solvency, which
needs a contract-specific init sequence) are reported **scaffold-only** with the
hand-written `chain/formal-verification/` harness as the named next step — FV is
deliberately not push-button for arbitrary contracts.

### C — adversarial audit (the hunt)
Runs `codex exec` (GPT-5.6-class, reasoning xhigh, read-only sandbox) with a hostile-
auditor prompt (`tools/dregg-audit/prompts/hostile-audit.txt`) covering every vuln
class: the rug vectors, access control, reentrancy, integer/precision, DoS/stuck
funds, and mechanism-level economics. codex errs both ways, so every finding is
emitted **TRIAGE-REQUIRED** — it is raw material, not a verdict.

### D — triage + report (the verdict)
Assembles the report and requires a human to mark each stage-C finding **CONFIRMED-
REAL / FALSE-POSITIVE / KNOWN-RESIDUAL** against source, with a reproduction (a
failing test) before any fix is applied. Stages A and B are machine-decided and need
no triage. This is the exact division of labor from the launchpad self-audit: codex
hunts and reasons about the design; a human verifies against source and reproduces.

## The report format

Each run writes `reports/<name>.audit.md`:

1. **Header** — the assisted-audit-tool caveat, target path, timestamp.
2. **§A Rug-forensics table** — `# | rug door | PRESENT/ABSENT | evidence (line:match)`,
   plus a mint-mitigation note.
3. **§B Formal verification** — the harness description, the raw Halmos PASS/FAIL
   output, and the verdict (PROVEN / COUNTEREXAMPLE / scaffold-only).
4. **§C Adversarial findings** — codex's `FINDING/SEVERITY/CLASS/LOCATION/WHY/FIX`
   blocks (triage-required) and its overall verdict.
5. **§D Triage summary** — a table with a per-stage verdict, severity, and proposed
   fix, and the legend that A/B are machine-decided while C needs a human verdict.

A companion `reports/<name>.triage.md` (the human step) records the confirmed verdict
per finding. See `reports/MoonRugToken.audit.md` + `reports/MoonRugToken.triage.md`.

## How a project submits a contract

```sh
tools/dregg-audit/dregg-audit path/to/YourContract.sol
# options: --out DIR  --no-fv  --no-codex  --reuse-codex  --codex-timeout N
```

The pipeline copies the contract read-only into an isolated Halmos workspace, runs the
four stages, and writes the report. No contract is edited. Requirements: Halmos
(`uvx --from halmos halmos`), Foundry (`forge`/`solc` 0.8.30), codex-cli. Stages
degrade gracefully — a missing tool or an unmatched FV shape is reported, not fatal.

## The sample run (a non-DREGG contract)

`samples/MoonRugToken.sol` is a reconstruction of publicly documented launchpad-token
rug mechanisms (SQUID honeypot, mintable-supply overdose, HypervaultFi owner-drain,
pausable/blacklist, selfdestruct — cited in `RUG-FORENSICS-VS-DREGG.md`; block
explorers 403 automated fetch, so the *mechanism* is reconstructed rather than a
victim's bytecode invented). Running the pipeline on it:

- **§A** flags **7 of 9 rug doors PRESENT** (owner-role, mintable supply, selfdestruct,
  honeypot, blacklist, pausable, owner-drain); proxy and fee ABSENT.
- **§B** returns a **machine-checked counterexample** — the owner can `mint` past the
  cap (`totalSupply > cap`), so the hard cap is *proven* not enforced.
- **§C** codex returns 15 findings — 3 Critical (mint, seize, honeypot), 2 High
  (blacklist, freeze), Medium (selfdestruct, approve-race), Low (zero-address), and
  correctly reports the absent classes — with the verdict "this contract is an explicit
  rug."
- **§D / triage** — all Critical/High findings **CONFIRMED-REAL** against source; zero
  false positives on this hostile sample (though triage stays mandatory — on our own
  launchpad codex both over- and under-called).

**Headline:** the pipeline runs any contract through the DREGG-kernel audit and, on the
sample, three independent stages converge on the mintable-supply rug — with Halmos
supplying a *machine proof* that the cap is breakable. That is the service working on a
contract that is not ours.

## Honest scope, restated

The service makes contract onboarding real as an **assisted audit**: it finds vulns and
proposes fixes, with a proof where a standard invariant applies. It is **not** a
certification (needs human review) and it does **not** auto-rewrite to secure (audit +
propose; a developer applies). Sold honestly, it is a force-multiplier on a human
auditor — not a replacement for one.
