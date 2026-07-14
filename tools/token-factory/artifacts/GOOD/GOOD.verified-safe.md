# VERIFIED-SAFE token artifact — Good Capped Token (`GOOD`)

Pipeline: `tools/token-factory/token-factory` · Generated: 2026-07-14T23:53:21Z
Spec: `/Users/ember/dev/breadstuffs/tools/token-factory/specs/good-capped-token.json`
Emitted contract: `/Users/ember/dev/breadstuffs/tools/token-factory/artifacts/GOOD/GOOD.sol`  ·  template: **fv-safe**
Audit report: `/Users/ember/dev/breadstuffs/tools/token-factory/artifacts/GOOD/GOOD.audit.md`

> **VERIFIED-SAFE — ready for the anti-rug launchpad.** Every token that
> leaves this factory carries this bundle: the emitted contract, the audit
> report, and the machine proof below. The rug doors are absent by
> construction; the hard cap is Halmos-proven.

## Token spec

```json
{
  "name": "Good Capped Token",
  "symbol": "GOOD",
  "decimals": 18,
  "cap": 1000000000,
  "mint_authority": "launchpad-oneshot",
  "tokenomics": {
    "creator_allocation_bps": 500,
    "vesting": "12-month linear, launchpad-committed schedule"
  },
  "notes": "A reasonable hard-capped memecoin: 1B supply, single disclosed mint by the launchpad, 5% creator allocation vested. The FV'd template path."
}
```

## The proof (machine-decided)

| Check | Source | Result |
|-------|--------|--------|
| Hard cap `totalSupply <= cap` | Halmos symbolic EVM (Stage B) | **PROVEN (hard cap holds over all symbolic inputs)** |
| One-shot mint latch | rug-forensics mint-mitigation (Stage A) | detected |
| Rug doors present | rug-forensics 9-door taxonomy (Stage A) | mintable supply (mint fn) |
| Dangerous doors (owner/seize/pause/blacklist/selfdestruct/proxy/fee) | Stage A | none |

**Verdict: VERIFIED-SAFE.** The only rug-forensics door present is the
disclosed one-shot `mint` (a `function mint` exists) — and it is allowed
*only* because the cap is Halmos-proven and the one-shot latch is detected,
so no second mint and no over-cap mint can occur. No owner role, seize,
pause, blacklist, selfdestruct, proxy, or fee door exists. Proven-safe.

## The full audit report

See `tools/token-factory/artifacts/GOOD/GOOD.audit.md` (rug-forensics table + Halmos log).

---
_The dreggic value is this FV+audit backend (proven-safe emit), not the spec
drafting. The AI-generation front is a structured spec-builder now; an LLM
provider that drafts the spec from natural language is the honestly-labeled
wire-later (see tools/token-factory/README.md)._
