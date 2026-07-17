# `token-factory` — the dreggic AI-token-factory (p0, but proven-safe)

p0 Systems is an *AI Token Factory for Solana*: describe a coin, an AI configures it,
deploy to a launchpad in 60 seconds. The token it emits **can rug** — a hidden mint,
an owner drain, an uncapped supply can sit in the AI-emitted code, and the launchpad
it deploys to is where ~98.6% of tokens show rug traits (`docs/deos/P0-DREGGIC.md` §2).

This is the same job, backwards where it matters: a token SPEC becomes a
**proven-safe** launch token, and a **rug-y spec is caught by the audit before it
ships**. The factory emits from the formally-verified launch-token template and runs
the DREGG-kernel audit as a *gate* — every token that leaves the factory is
Halmos-proven cap-safe with the rug doors absent by construction, or it is rejected.

```sh
tools/token-factory/token-factory <spec.json> [--out DIR] [--codex]
```

## The pipeline (spec → derived-emit → auto-audit → gate → capability → deploy-ready)

| Stage | What | Tool | Decided by |
|-------|------|------|-----------|
| 1. **EMIT** | spec → concrete launch-token `.sol`, **derived** from the FV'd template | `emit_token.py` | template selection + derivation check |
| 2. **AUDIT** | rug-forensics (9 doors) + Halmos symbolic proofs (4 invariant families) | `tools/dregg-audit/dregg-audit` | **machine** |
| 3. **GATE** | proven-safe or rejected | `token-factory` | **machine** |
| 4. **GATE-WIRE** | report hash → deployer-gate registry → real macaroon capability issued+authorized (or refused) | `deploy-gate` CLI (`tools/deployer-gate`) | **machine** |
| 5. **ARTIFACT** | verified-safe bundle + capability + the **ember-gated, NOT executed** deploy invocation — or a rejection citing the counterexample | `token-factory` | — |

**EMIT** genuinely **derives** the safe contract from the FV'd launch token: it
**reads** `chain/contracts/launchpad/DreggLaunchToken.sol` at emit time and applies
exactly five **count-checked substitutions** (contract name; name/symbol/decimals/cap
made compile-time constants from the spec; the constructor reduced to minter-only,
its zero-cap guard enforced at emit time). **Every function body — the one-shot
`mint` latch and the ERC-20 surface — is carried byte-for-byte** from the FV'd file
and re-verified on every emit (`verify_derivation`); a template whose anchors drift
makes the emit **fail loudly** instead of silently diverging (tested:
`test_emit_token.py`). The result: the hard cap is a **source-level literal**
(disclosed by construction), the mint is the template's **one-shot** latch callable
only by the launchpad, and **no other door exists** — no owner role, seize, pause,
blacklist, selfdestruct, upgrade proxy, or fee knob. This is the EVM twin of the Lean
supply theorem `execMintA_iff_spec`
(`metatheory/Dregg2/Verify/KeystoneAuditSupply.lean`).

**AUDIT** runs the real `dregg-audit` pipeline: Stage A greps the documented 9-door
rug taxonomy (`docs/deos/RUG-FORENSICS-VS-DREGG.md`), Stage B auto-generates a Halmos
symbolic-EVM harness and proves — against the real compiled bytecode, all inputs
symbolic — **INV-CAP** (`totalSupply <= cap`), **INV-NODRAIN** (no unauthorized
balance drain), **INV-REENTRANCY** (ETH-conservation form), and
**INV-ACCESS-CONTROL** (mint confined to its role). (Stage C, the codex adversarial
LLM pass, is **off by default** — the gate is the machine-decided A+B; pass `--codex`
for the deep triage-required pass.)

**GATE** marks a token **VERIFIED-SAFE** iff Halmos *proves* the invariants **and**
no dangerous rug door is present. The disclosed one-shot `mint` is the only allowed
door, and it is allowed *only* because the cap is proven and the one-shot latch is
detected — so no second mint and no over-cap mint can occur. Anything else is
**REJECTED**.

**GATE-WIRE** connects the verdict to the deployer-gate: on VERIFIED-SAFE the fresh
audit report's sha256 is registered in the gate's audit registry and a **real deploy
capability** (a `dregg-macaroon`, `Audit` arm, scoped to the spec's launch params,
expiring) is issued and authorized (deploy-time re-check). On REJECTED the hash is
never registered and issuance is demonstrably **refused** (`NotGated`) — no
capability can exist for a rejected token. Requires the CLI:
`cargo build -p dregg-deployer-gate --bins` (skipped with an honest note if unbuilt).

**The factory never deploys.** The verified-safe artifact carries the exact
`forge create` + `DreggLaunchpad.registerLaunch` invocation as a **proposed,
ember-gated** step; executing it is a separate, deliberate act.

## Both polarities (the differentiator, demonstrated)

Run against the two committed specs (`specs/`), real runs, artifacts in `artifacts/`:

**(a) A good spec → VERIFIED-SAFE + capability.** `specs/good-capped-token.json` (a
1B hard-capped token, single disclosed mint, 5% creator allocation vested):

```
$ token-factory specs/good-capped-token.json
VERIFIED-SAFE  template: fv-safe (derived from DreggLaunchToken.sol)
  Halmos: 5 passed; 0 failed — INV-CAP, INV-NODRAIN, INV-REENTRANCY,
          INV-ACCESS-CONTROL all PROVEN over all symbolic inputs
  rug doors present: only the disclosed one-shot mint (latch detected)
  gate-wire: report hash registered · capability issued · AUTHORIZED
→ artifacts/GOOD/GOOD.verified-safe.md   (+ GOOD.sol + GOOD.audit.md + GOOD.halmos.log)
```

**(b) A rug-y spec → CAUGHT, REJECTED, no capability.** `specs/rugpull-refillable.json`
asks for `mint_authority: "owner-refillable"` — "let me mint more later," the classic
dump setup. The FV'd template cannot express it; the factory emits the variant the
spec implies and the audit catches it:

```
$ token-factory specs/rugpull-refillable.json
REJECTED  template: unsafe-variant
  Halmos: 3 passed; 2 failed — COUNTEREXAMPLE, totalSupply > cap reachable
          (the drain/reentrancy/access checks honestly PASS — the rug is the
          uncapped owner mint, and each invariant closes its own door)
  rug doors present: owner/admin role, mintable supply (no one-shot latch)
  gate-wire: unregistered hash → issuance REFUSED (NotGated)
→ artifacts/RMOON/RMOON.rejected.md   (cites the machine counterexample)
```

The gate is the **audit**, not a human's read of the spec — and it caught the rug by
*proof*. (`tools/dregg-audit/samples/MoonRugToken.sol` is a second, hand-supplied rug
contract the same audit backend rejects, if you want to feed the factory-audit an
external contract rather than an emitted one.)

**Honest scope of the spec space:** the emit's safe/unsafe fork is decided by one
field (`mint_authority == "launchpad-oneshot"` → derived-safe; anything else → the
owner-refillable unsafe variant). "A rug-y spec is caught" is demonstrated over this
two-template space, not over arbitrary spec→contract mappings; broadening the spec
space (more mint-authority / tokenomics shapes) is a named next step. What *is*
general: the **audit** stage accepts any contract and its verdicts are
machine-decided.

## The AI-generation front (honest scope)

p0's distinctive feature is *"AI generates the token."* Here, the AI front is the UX
layer that produces the **spec** (name / symbol / cap / decimals / mint authority /
tokenomics) which feeds this pipeline. Honest scope:

- **Now (real):** a **structured spec-builder** — the JSON specs in `specs/`, validated
  by `emit_token.py` (required fields, positive cap, safe string literals). This is
  real and it is what the pipeline consumes.
- **Wire-later (labeled):** an **LLM provider** that drafts the spec from a
  natural-language prompt ("a 1B capped dog coin, 5% team, 12-month vest"). That is
  commodity — it needs a real provider (grain-jail / a hosted model), wired later. We
  do **not** fake an LLM; the spec-builder is real, the "AI" is the named front.

**The dreggic value is the FV+audit backend, not the AI.** p0's AI is the whole
product and the safety is nobody's; here the AI is the commodity front and the
**proven-safe emit** is the product. Every token from this factory is proven-safe or
caught.

## Layout

```
tools/token-factory/
  token-factory            # the orchestrator (emit → audit → gate → gate-wire → artifact)
  emit_token.py            # spec → launch-token .sol (derived from the FV'd template
                           #   by count-checked substitution / unsafe variant)
  test_emit_token.py       # the derivation honesty teeth (byte-identity, drift, divergence)
  specs/                   # example specs (good + rug-y) — the spec-builder's output
  artifacts/               # per-token bundles: <SYM>.sol, .audit.md, .halmos.log,
                           #   and <SYM>.{verified-safe,rejected}.md
```

Requires `python3`, `forge`/`solc` (Foundry), and `halmos` (`uvx --from halmos`) — the
same toolchain as `tools/dregg-audit/` — plus, for the gate-wire stage,
`cargo build -p dregg-deployer-gate --bins` (skipped with an honest note if unbuilt).
Composes the landed pieces; it does not edit them. Tests:
`python3 tools/token-factory/test_emit_token.py`.
