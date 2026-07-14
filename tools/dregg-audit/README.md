# `dregg-audit` — a repeatable DREGG-kernel contract-audit pipeline

Point it at any Solidity contract; it runs the same four-stage audit we ran ad-hoc
for our own launchpad this session, and produces a structured markdown report.

```sh
tools/dregg-audit/dregg-audit <contract.sol> [--out DIR] [--no-fv] [--no-codex] [--codex-timeout N]
```

**What it is:** an *assisted-audit tool*. It finds vulnerabilities and proposes
fixes, with a machine proof where a standard invariant applies. **It is not a
push-button certification** (a real audit needs human review), and it does **not**
auto-rewrite the contract to secure (that is a research problem — this AUDITS and
PROPOSES; a developer applies the fix). See `docs/deos/DREGG-AUDIT-SERVICE.md`.

## The four stages

| Stage | Tool | Decided by | Output |
|-------|------|-----------|--------|
| **A. rug-forensics** | `grep` over the rug-door taxonomy | **machine (deterministic)** | each door PRESENT/ABSENT (`docs/deos/RUG-FORENSICS-VS-DREGG.md`) |
| **B. formal verify** | Halmos symbolic EVM | **machine (proof)** | INV-CAP PROVEN / COUNTEREXAMPLE, or scaffold-only |
| **C. adversarial** | `codex exec` hostile audit | LLM (needs triage) | severity-ranked findings, **TRIAGE-REQUIRED** |
| **D. triage + report** | assembler | human confirms C | one markdown report |

- **A** scans for the nine documented rug doors (owner/admin role, mintable supply,
  proxy-upgrade, selfdestruct, honeypot transfer-gate, blacklist, pausable,
  owner-drain/seize, fee/tax manipulation). Deterministic — an ABSENT door is a
  structural absence in source; a PRESENT door is a *surface to review*.
- **B** auto-generates a Halmos harness for the ERC-20 **supply-cap** shape (a `mint`
  fn + public `cap`/`totalSupply`) and proves `totalSupply <= cap` over all inputs
  against the real compiled bytecode — the EVM twin of the Lean supply theorem
  `execMintA_iff_spec`. A hard-capped one-shot token *proves*; an uncapped/owner-
  mintable token yields a *counterexample*. Non-token shapes report scaffold-only
  (FV is deliberately not push-button for arbitrary contracts — pool-solvency
  contracts use the hand-written harness in `chain/formal-verification/`).
- **C** runs `codex exec --sandbox read-only` with a hostile-auditor prompt covering
  every vuln class (`prompts/hostile-audit.txt`). codex errs both ways, so its
  findings are emitted **TRIAGE-REQUIRED** — a human confirms each against source.
- **D** assembles the report: the rug-door table (A, auto), the FV verdict (B, auto),
  the codex findings (C, triage-required), and a triage summary. A/B rows are
  machine-decided; C rows carry the codex severity and a proposed fix but require a
  human verdict (CONFIRMED-REAL / FALSE-POSITIVE / KNOWN-RESIDUAL).

## Layout

```
tools/dregg-audit/
  dregg-audit              # the orchestrator
  gen_fv_harness.py        # Stage-B harness generator (supply-cap shape)
  prompts/hostile-audit.txt# Stage-C codex prompt template
  samples/MoonRugToken.sol # a reconstructed known-rug sample (audit target)
  fv-workspace/            # Halmos foundry project (harness+target generated per run)
  reports/                 # generated audit reports (+ the committed sample run)
```

## The sample run

`reports/MoonRugToken.audit.md` is a real run against `samples/MoonRugToken.sol`, a
reconstruction of publicly documented launchpad-token rug mechanisms (SQUID honeypot,
mintable-supply overdose, HypervaultFi owner-drain, pausable/blacklist, selfdestruct).
The pipeline flags 7 rug doors, and **Halmos returns a machine-checked counterexample
proving the hard cap is not enforced** (an uncapped owner `mint`). This demonstrates
the service on a NON-DREGG contract.

Reproduce:

```sh
tools/dregg-audit/dregg-audit tools/dregg-audit/samples/MoonRugToken.sol
```

## Requirements

`halmos` (`uvx --from halmos halmos`, 0.3.3+), `forge`/`solc` (Foundry 1.7.1, solc
0.8.30), `codex` (codex-cli 0.144.1). Stages degrade gracefully: `--no-fv` /
`--no-codex` skip their stage, and a missing tool is reported, not fatal.
