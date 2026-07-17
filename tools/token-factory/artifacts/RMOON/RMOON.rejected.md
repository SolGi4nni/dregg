# REJECTED token artifact — Refillable Moon Token (`RMOON`)

Pipeline: `tools/token-factory/token-factory` · Generated: 2026-07-17T06:19:44Z
Spec: `/Users/ember/dev/breadstuffs/tools/token-factory/specs/rugpull-refillable.json`
Emitted contract: `/Users/ember/dev/breadstuffs/tools/token-factory/artifacts/RMOON/RMOON.sol`  ·  template: **unsafe-variant**
Audit report: `/Users/ember/dev/breadstuffs/tools/token-factory/artifacts/RMOON/RMOON.audit.md`

> **REJECTED — not shipped.** The audit caught a rug property in the
> contract this spec implies. The factory only outputs proven-safe tokens;
> this one is cited below and stopped here.

## Token spec

```json
{
  "name": "Refillable Moon Token",
  "symbol": "RMOON",
  "decimals": 18,
  "cap": 1000000000,
  "mint_authority": "owner-refillable",
  "tokenomics": {
    "creator_allocation_bps": 500,
    "vesting": "none"
  },
  "notes": "A rug-y spec: it asks for 'owner-refillable' mint authority ('let me mint more later'). The FV'd template cannot express this; the factory emits the variant the spec implies and the audit CATCHES it (Halmos counterexample + owner door) -> REJECTED, never shipped."
}
```

## The proof (machine-decided)

| Check | Source | Result |
|-------|--------|--------|
| Hard cap `totalSupply <= cap` | Halmos symbolic EVM (Stage B) | **COUNTEREXAMPLE (cap breakable)** |
| One-shot mint latch | rug-forensics mint-mitigation (Stage A) | ABSENT |
| Rug doors present | rug-forensics 9-door taxonomy (Stage A) | owner/admin role, mintable supply (mint fn) |
| Dangerous doors (owner/seize/pause/blacklist/selfdestruct/proxy/fee) | Stage A | owner/admin role |

**Verdict: REJECTED.** Halmos did not PROVE the hard cap; Halmos found a COUNTEREXAMPLE (cap breakable); dangerous rug door(s) present: owner/admin role; a mint fn without a one-shot latch.

The differentiator, demonstrated: a rug-y spec does not become a shipped
token. The audit — not a human's read of the spec — is the gate, and it
caught this by proof/flag.

## The deploy gate (capability arm)

This token's audit-report hash was **never registered**, and the
deployer-gate demonstrably **refuses to issue** a capability for it:

- report hash (unregistered): `931f5072c54ca15499429d00f6b5801356f61cf76098a9148d763bab8d6d20f2`
- issue attempt: **REFUSED** — `deploy-gate: issuance refused: deployer is not gated for the requested arm (issuance refused)`

No capability exists for a rejected token; the launchpad's
`DeployerNotGated` arm has nothing to accept.

## Deploy (EMBER-GATED — proposed, NOT executed)

Nothing to deploy: the token was rejected and holds no capability.

## The full audit report

See `tools/token-factory/artifacts/RMOON/RMOON.audit.md` (rug-forensics table + Halmos log).

---
_The dreggic value is this FV+audit backend (proven-safe emit), not the spec
drafting. The AI-generation front is a structured spec-builder now; an LLM
provider that drafts the spec from natural language is the honestly-labeled
wire-later (see tools/token-factory/README.md)._
