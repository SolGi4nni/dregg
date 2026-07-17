# VERIFIED-SAFE token artifact — Good Capped Token (`GOOD`)

Pipeline: `tools/token-factory/token-factory` · Generated: 2026-07-17T06:19:10Z
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

## The deploy gate (capability arm)

The fresh audit report's sha256 was **registered** in the deployer-gate
audit registry and a real deploy capability (a `dregg-macaroon`, `Audit`
arm, scoped to this spec's launch params, 24h expiry) was **issued and
authorized** (deploy-time re-check of scope + expiry + registry membership):

- report hash: `6d62ff7d54383d74238439781591d43d824e1eab037df7c9d66e41e2419b49a5`
- capability (macaroon, truncated): `em2_lJPcACDMkVc_LhN8fszyQcz7zNvMrszFzM9_zKPMs1NZVMyyZMyjzO_M4szX…`
- authorize: **AUTHORIZED**

_The registry/state is the PoC operator file (`deploy-gate.state`,
gitignored — it holds the issuing root key). The on-chain twin of this
gate is the landed `DreggLaunchpad.registerLaunch` hook
(`DeployerNotGated`)._

## Deploy (EMBER-GATED — proposed, NOT executed)

This factory does **not** deploy. The deploy-ready invocation, to be run
deliberately (ember-gated) once a target chain + launchpad minter address
exist, presenting the capability above to the launchpad gate:

```sh
forge create tools/token-factory/artifacts/GOOD/GOOD.sol:GoodCappedTokenLaunch \
  --constructor-args $LAUNCHPAD_MINTER_ADDR \
  --rpc-url $RPC_URL --private-key $DEPLOYER_KEY
# then: DreggLaunchpad.registerLaunch(...) — the landed on-chain gate
# reverts DeployerNotGated unless the deploy capability clears.
```

## The full audit report

See `tools/token-factory/artifacts/GOOD/GOOD.audit.md` (rug-forensics table + Halmos log).

---
_The dreggic value is this FV+audit backend (proven-safe emit), not the spec
drafting. The AI-generation front is a structured spec-builder now; an LLM
provider that drafts the spec from natural language is the honestly-labeled
wire-later (see tools/token-factory/README.md)._
