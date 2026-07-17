# The verifiable recycle-flywheel — MEASURED (dregg vs a faithful CIRC mock)

*Status: a built + adversarially-measured A/B. This turns "we surpass CIRC" (the
design in `docs/reference/CIRC-COMPETITIVE-ANALYSIS.md` §4–§6) into a **number**.
Everything below is produced by `chain/test/RecycleFlywheelAB.t.sol` (`forge test`,
LOCAL, no deploy) against two real contracts on identical token infrastructure:
`chain/contracts/flywheel/RecycleFlywheel.sol` (dregg) and
`chain/contracts/flywheel/MockCircFlywheel.sol` (a faithful CIRC-style flywheel).
The gas/latency premium is reported PLAINLY — dregg is not cheaper or faster; it is
front-run-immune, deviation-proof, conserving, and re-checkable at a stated bounded
premium.*

---

## 0. What was built (composition of landed launchpad pieces, not new science)

- **`RecycleFlywheel.sol`** — the dregg verifiable recycle: fees **accrue** tagged
  with a source-receipt hash (provenance) → a **contract-enforced split** (committed
  `buyBps`; a wrong/hidden split reverts `SplitMismatch`, the exact
  `DreggLaunchpad.GraduationSeedMismatch` pattern) → the "buy" is a **sealed-bid
  uniform-price clearing** over sellers' asks (permutation-checked ascending sort +
  marginal fill — the dual of `DreggLaunchpad._runClearing` / `_assertPermutation`,
  order-invariant, nothing to front-run) → the result **seeds a `DreggSolventPool`**
  (floor-guarded, rung-6) → the recycle **asserts per-asset `netFlow = 0`** and emits
  a **prev-hash-chained, operator-signed receipt** a non-witness re-derives.
- **`MockCircFlywheel.sol` + `MockAmm.sol`** — a faithful CIRC-style flywheel: an
  **owner-key-settable** split (`setSplitBps`), a **front-runnable market buy** against
  a pump-style constant-product AMM, an LP-add, **no** conservation cert, **no**
  receipt. Not a strawman: it prices exactly like a Raydium/PumpSwap pool and its
  LP-add is real (matching CIRC's 100%-locked-LP credit, analysis §2.2).
- **`RecycleFlywheelAB.t.sol`** — 9 adversarial A/B tests (a real `SandwichBot`, a
  real deviating tx). `forge test`: **9/9 green**; the full `chain/` suite stays
  **269/269 green** (268 prior + the `RecycleFlywheelGasSlope` measurement test).

---

## 1. THE MEASURED TABLE (every metric a number)

| Axis | dregg (`RecycleFlywheel`) | CIRC mock (`MockCircFlywheel`) | Test |
|---|---|---|---|
| **MEV from the recycle buy** | **0 wei** — sealed, order-invariant batch; no swap to sandwich | **1,781,027,284,951,285,741 wei ≈ 1.781 ETH** extracted by a real sandwich bot (front-run 5 ETH + back-run around a 20 ETH recycle) | `test_1` |
| **Order-invariance / envy** | **Δ = 0** — identical book in opposite reveal order → identical uniform price, identical quantity, identical per-seller fills | **order-dependent** — same two 5-ETH buyers, opposite order: buyer-X gets **90,661,089…** tokens FIRST vs **75,569,800…** LAST (**~16.6% front-run edge**) | `test_1`, `test_2` |
| **Split deviation** | **REVERTS** `SplitMismatch(40e18, 40e18)` on a 90/10 skim attempt against the committed 50/50 | **SUCCEEDS** — `setSplitBps(9000)` re-weights the split via the owner key; you learn after | `test_3` |
| **Conservation** | **`netQuote = 0`, `netToken = 0`** asserted on-chain; `accrued 80 = spent 30 (→sellers) + quoteSeed 50 (→pool)`; flywheel drains to **0** ETH / **0** token residue | **no cert** — a sandwiched recycle **leaks 1.781 ETH to MEV** with nothing to catch it | `test_4` |
| **Re-checkability** | **non-witness verifies** — recompute head from public bundle `== receiptHead`; operator signature verifies; any tamper (price −, seed −) breaks the chain | **raw transfer + event** — no signed chain, no verify-only path (no such surface) | `test_5` |
| **Provenance** | **measurable** — `provenanceBps = 10000` when every inflow is tagged; **6666** with one opaque inflow | **0** — `recycle` takes raw ETH, no source-receipt parameter | `test_6` |
| **Gas (headline step)** | `finalizeRecycle` (clear + split + seed + conserve + sign) = **372,485 gas** (`gasleft`) / **437,063** cold (`--gas-report`) — down from 1,627,006 / 1,623,240 pre-optimization (`docs/reference/GAS-OPTIMIZATION-MEASURED.md`) | `recycle` (market-buy + LP-add) = **~84,597 gas** (`gasleft`) / **96,084** report → dregg premium **≈ 4.4×** on this step | `test_7` |
| **Gas (whole turn) + latency** | whole verifiable turn ≈ **~1.27M gas** across a **commit→reveal→clear→settle** lifecycle (multiple txns + a commit→reveal window); was ~2.68M pre-optimization | **~96k gas**, a **single tx**, no commit→reveal wait → dregg premium **≈ 13×** + a real latency the mock skips | per-op table below |

### 1.1 Per-operation dregg gas (`forge test --gas-report`)

| `RecycleFlywheel` op | gas (avg / max) |
|---|---|
| `accrueFee` | 71,324 / 92,960 |
| `commitAsk` | 110,031 / 121,435 |
| `revealAsk` | 75,496 / 100,312 |
| `finalizeRecycle` | **437,063** (the clearing + cert + signature step) |
| `settleAsk` | 45,546 |

The premium concentrates in `finalizeRecycle` — the on-chain permutation-checked
clearing + pool seeding + conservation + signature verification. It is **real and
bounded** (~4.4× the mock's step after the measured optimization campaign —
storage-redundancy elimination, packing, EIP-1167 pool clones; per-change
numbers in `docs/reference/GAS-OPTIMIZATION-MEASURED.md`), and it is the price
of the four guarantees the mock cannot make. For large books the O(n) walk is
replaced by a FLAT Groth16 clearing proof (prototyped:
`chain/gnark/clearing_snark.go`; crossover ≈ 44 asks).

---

## 2. What this PROVES vs what stays a NAMED WELD

### Demonstrated, adversarially, as numbers (surpasses CIRC here — today)

1. **Front-run resistance.** A real `SandwichBot` extracts **1.781 ETH** from the
   mock's telegraphed market buy; the dregg recycle exposes **no swap to wrap** and
   its clearing is order-invariant, so the ordering lever yields **0 by construction**
   (not "mitigated"). This is the sharpest CIRC failure (analysis §2.1e), measured.
2. **Split enforcement.** A deviating split is **unconstructable** on dregg (reverts
   against a committed public input) and **trivial** on the mock (an owner-key setter).
3. **Conservation.** dregg's recycle carries an on-chain `netFlow = 0` cert (the twin
   of `Market/Priced.lean priced_clearing_keystone`) and drains to zero residue; the
   mock has no conservation statement and demonstrably leaks value to MEV.
4. **Re-checkability.** A non-witness re-derives dregg's prev-hash-chained, signed
   receipt from public data and detects any tamper; the mock offers only a
   block-explorer trace. Ex-ante verification vs ex-post trust.
5. **Provenance.** dregg's inflows carry a re-checkable source-receipt fraction; the
   mock's are opaque transfers (0).

### Honest edges — NAMED, not claimed (per analysis §4.3; do NOT overclaim)

- **The receipt does NOT bind the clearing to an in-circuit price proof.** A
  non-witness re-derives the uniform price from the **public** book (rung-1
  REPLAYABLE), so a corrupt operator can **withhold** but cannot **misprice**. Binding
  the clearing tuple inside a Groth16 statement is **prototyped at the circuit
  level** (`chain/gnark/clearing_snark.go`: the clearing tuple proved against the
  contract's exact book-fold layout, adversarial mutations rejected) — the weld
  stays open until the on-chain verify entry point lands
  (`docs/reference/GAS-OPTIMIZATION-MEASURED.md` §4).
- **`.sol ↔ Lean` correspondence is prose, not mechanized** (§4.3.2). The Lean proves
  the *mechanism* (`uniform_price_no_arbitrage`, `priced_clearing_keystone`,
  `pool_solvent_forever`); this contract is a faithful **REPLAYABLE** realization, not
  itself the Lean statement.
- **The measured MEV/order-dependence numbers are pool-size specific** — they scale
  with trade-size-to-liquidity, not universal constants. The *sign* is what is
  structural: mock **> 0**, dregg **= 0**.
- **dregg is NOT cheaper or faster.** The ~4.4× headline / ~13× whole-turn gas
  premium (post-optimization; was ~16–28×) and the commit→reveal
  latency are real. The claim is precisely: *front-run-immune + deviation-proof +
  conserving + re-checkable, at a stated bounded premium.*
- **A fairly-recycled worthless token is still worthless** (`DREGG-LAUNCHPAD-DESIGN`
  §5.3) — dregg neutralizes the *mechanism* abuses, not token quality.

---

## 3. Reproduce

```
cd chain
forge test --match-contract RecycleFlywheelABTest -vv          # the A/B, with logged numbers
forge test --match-contract RecycleFlywheelABTest --gas-report # the per-op gas premium
forge test                                                     # full suite: 268/268 green
```

Contracts: `chain/contracts/flywheel/{RecycleFlywheel,MockCircFlywheel,MockAmm}.sol`.
Reused, unchanged: `chain/contracts/launchpad/{DreggSolventPool,DreggLaunchToken}.sol`
and the sealed-clearing / `GraduationSeedMismatch` patterns of `DreggLaunchpad.sol`.
