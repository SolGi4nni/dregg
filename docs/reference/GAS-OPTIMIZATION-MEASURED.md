# Recycle-flywheel gas optimization — MEASURED (the fairness tax, driven down)

*Status: landed + measured. The verifiable recycle's headline step
(`RecycleFlywheel.finalizeRecycle`) cost **1,627,006 gas** — a ~16–19× premium
over the CIRC-style mock — with the premium concentrated in redundant storage
and a per-recycle pool code-deposit, NOT in the guarantees. Three measured
optimization stages cut it to **372,485 gas (−77%, a ~4.4× premium)** with
every proven property intact: the A/B adversarial suite
(`chain/test/RecycleFlywheelAB.t.sol`, 9/9) and the full `chain/` suite
(**269/269**, incl. the new gas-slope test) are green at HEAD. A fourth,
architectural lever — clear off-chain, verify a Groth16 proof of the clearing
on-chain — is PROTOTYPED end-to-end in `chain/gnark/clearing_snark.go` and
takes the premium FLAT in book size (crossover ≈ 44 asks, ~28× cheaper at
n=1000), while also closing the §4.3.1 price-binding weld.*

Baselines and afters were measured on the same HEAD with the same commands;
every number below is from `forge test` (`gasleft` bracket or `--gas-report`),
`chain/test/RecycleFlywheelGasSlope.t.sol` (cold-storage slope via `vm.cool`),
or `chain/gnark` (`go test -run TestRecycleClearingGroth16EndToEnd -v`).

---

## 1. The headline (measured, same harness before/after)

| Metric | before | after | Δ |
|---|---|---|---|
| `finalizeRecycle` (`gasleft`, `test_7`) | **1,627,006** | **372,485** | **−77.1%** |
| `finalizeRecycle` (`--gas-report` max) | 1,623,240 | 437,063 | −73.1% |
| premium vs mock `recycle` (84,597 `gasleft`) | ~19.2× | **~4.4×** | |
| whole verifiable turn (Σ per-op avg × count) | ~2,683,000 | **~1,273,000** | −52.6% |
| whole-turn premium vs mock single tx (96,084) | ~28× | **~13.2×** | |

The premium that remains is the price of the four guarantees the mock cannot
make (sealed order-invariant clearing, enforced split, on-chain conservation,
signed re-checkable receipt) — now a bounded ~4.4× on the headline step, not
~19×.

### Per-operation (`--gas-report`, avg / max)

| op | before | after | Δ avg |
|---|---|---|---|
| `accrueFee` | 85,827 / 114,917 | 71,324 / 92,960 | −17% |
| `commitAsk` | 109,830 / 121,234 | 110,031 / 121,435 | **+0.2%** (the range check — honest regression) |
| `revealAsk` | 119,519 / 144,335 | 75,496 / 100,312 | −37% |
| `finalizeRecycle` | 1,623,240 max | 437,063 max | −73% |
| `settleAsk` | 66,842 | 45,546 | −32% |

Free-rider from the shared lever: the launchpad's `graduate` dropped
**925,218 → 333,126** (max) with zero launchpad-logic change.

---

## 2. The three stages, each measured and correctness-preserving

### Stage A — stop storing what is derivable (−508,744; 1,627,006 → 1,118,262)

The 16-field `Receipt` struct was persisted to storage at finalize (~14
nonzero cold SSTOREs) although **every field is a pure function of state that
is already public**: `spentQuote ≡ uniformPrice·boughtTokens` (exact by
construction of the walk), `buyHalf/poolHalf ≡ splitOf(accrued)`,
`quoteSeed ≡ poolHalf + buyHalf − spent`, floors are BPS functions, the nets
are 0 or finalize reverted. The struct is now REBUILT in memory
(`_liveReceipt`) by `verifyReceipt`/`receiptBundle`; the derivable cleared
vars became view functions with identical ABI and identical pre/post-clear
values; the 65-byte signature `bytes` (4 storage slots) became `(r,s,v)`.
This *strengthens* the receipt's own thesis: a non-witness re-derives it from
public data — now the contract does too, and the two cannot diverge.

### Stage B — packing + one-pass clearing (−134,145; 1,118,262 → 984,117)

- `Ask` 7 slots → 3 (`sealedHash` | `escrow,filled,settled` | `price,qty,flags`):
  reveal writes price+qty+flag into the slot commit already opened (~49k →
  ~7k), the clearing's fill write lands in the escrow slot (~22k → ~5k cold),
  settle's flag write is warm (~22k → ~5k).
- `phase | sigV | pool` share one slot; `inflowCount | provenancedCount`
  share one slot; `uniformPrice | boughtTokens` share one slot. All getters
  keep their selectors (return-type width is not part of a selector).
- The permutation check (`_assertPermutation`) is FUSED into the walk — same
  property (order is a permutation of [0,n), checked index-by-index via
  `_markSeen` bitmap words), one pass instead of two, no `bool[]` allocation.
- `unchecked` only where the guard proves safety (loop index; `affordable >
  bought` ⇒ safe subtraction; `bought+fill ≤ affordable ≤ budget`).
- NARROWING IS ALWAYS CHECKED, never truncating: `ValueOutOfRange` reverts at
  entry for price ≥ 2^128 wei/token (~3.4e20 ETH/token), qty ≥ 2^96 whole
  tokens (~7.9e28), escrow ≥ 2^128 base units — documented bounds
  astronomically above any real book (and now the SNARK circuit's range
  assumptions, made real on-chain).

### Stage C — EIP-1167 pool clones (−611,632; 984,117 → 372,485)

`new DreggSolventPool` was **713,883 gas measured** — almost entirely the
3,562-byte runtime code deposit, paid per recycle (and per graduation).
Every pool is now a 45-byte EIP-1167 minimal proxy (`LibClone1167`, the
canonical EIP bytes assembled transparently via `abi.encodePacked`) of ONE
inert implementation:

- the implementation self-bricks in its constructor (`initialized = true`) —
  only clones can ever be seeded;
- the config that was constructor-set immutables (token, floors, fee,
  launchId) is SET ONCE in `initialize`, which also seeds — there is still no
  setter, and creation + funding + seeding are ATOMIC in the creator's tx, so
  an un-initialized pool is never observable on-chain (no front-run window);
- the launchpad deploys the implementation in its own constructor (one-time,
  amortized over every graduation); the flywheel takes it as a committed
  constructor input like `token`/`buyBps`.

**Swap-path cost, measured honestly** (old direct pool vs new clone, same
seeds, one-off A/B): `buy` 15,402 → 15,931 (**+529**), `sell` 16,622 → 17,157
(**+535**) warm; a fully cold swap additionally pays ~2.6k (cold impl account
for the delegatecall) + ~4.2k (two config slots that were immutables). A
~0.5–7k per-swap cost against ~612k saved per pool creation.

---

## 3. Guarantees preserved (the gate, cited)

- **A/B adversarial suite 9/9 green** (`forge test --match-contract
  RecycleFlywheelABTest`): sandwich-MEV = 0 by construction, order-invariance
  Δ=0 with per-seller fill equality, `SplitMismatch` on the 90/10 skim,
  `netQuote = netToken = 0` + zero residue, non-witness receipt re-derivation
  + tamper-evidence, provenance fractions, the permutation/sort teeth.
- **Full `chain/` suite 269/269 green** (`forge test`) — 268 prior + the new
  `RecycleFlywheelGasSlope` measurement test.
- Semantics deltas, exhaustively: (1) the documented `ValueOutOfRange` bounds
  (unreachable for real values; revert-not-truncate); (2) pool floors/config
  are set-once-at-initialize instead of constructor immutables — same
  no-setter unchangeability, enforced by `AlreadyInitialized` + atomic
  create-and-seed (P0Parity's owner-drain probe now expects
  `AlreadyInitialized` where it expected `NotGraduation`; the door is closed
  to *everyone*, the graduation included); (3) `receiptBundle`/derived views
  return the identical values, all-zero before Cleared as before;
  (4) `RecycleFlywheel`'s constructor takes `poolImplementation_` (a new
  committed public input).
- **Lean model** (`metatheory/Market/RecycleFlywheel.lean`): untouched, and no
  assumption is invalidated — the model quantifies over the *mechanism*
  (committed split, uniform-price clearing over the book multiset,
  conservation, receipt re-derivability from turn data), not storage layout,
  deployment shape, or hashing schedule. Two notes for the prose
  `.sol ↔ Lean` weld (§4.3.2, still prose): the packed-field bounds introduce
  an entry-gate domain restriction the model doesn't have (asks beyond the
  bounds are REJECTED at commit/reveal, never mis-cleared), and
  `pool_solvent_forever`'s realization now reads its floor from set-once
  storage rather than an immutable — the floor-guard check itself is
  byte-identical.

---

## 4. The architectural lever — off-chain clear, on-chain proof (PROTOTYPED)

**Verdict: FEASIBLE, prototyped end-to-end at the circuit level; the on-chain
integration is scoped, not built.**

The optimized walk still costs **~10,668 gas per ask cold** (measured,
`RecycleFlywheelGasSlope.t.sol`: 416k @ n=3 → 1,747k @ n=128, `vm.cool`d so
the slots are cold as in a real finalize tx). A Groth16 verify is FLAT:
**466,163 gas measured** for the repo's real settlement-shaped verifier
(25 publics + gnark commitment, `DreggSettlementRealProof.t.sol` replaying a
real gnark proof).

| book size n | on-chain walk (measured/extrap.) | proof path (verify + fixed) |
|---|---|---|
| 3 | 416k | ~880k — walk wins |
| 44 | ~854k | ~854k — crossover |
| 128 | 1,747k (measured) | ~880k |
| 1000 | ~11.1M (extrapolated slope) | ~880k — **~12.6× cheaper** |

`chain/gnark/clearing_snark.go` + `clearing_snark_test.go` — run `go test
-run TestRecycleClearingGroth16EndToEnd -v` — prove the statement *"(price,
bought, spent, fills) is THE uniform-price marginal-fill clearing of the book
committed by the keccak fold, under the committed budget"*:

- **binding**: the circuit recomputes the book's keccak chain with the
  contract's exact `abi.encodePacked(prev32, seller20, price32, qty32)`
  layout — it binds the commitment the contract already emits, not a mirror;
- **permutation** (`_assertPermutation`'s twin): grand-product multiset
  argument at Fiat–Shamir challenges keccak-derived in-circuit from BOTH the
  arrival-order and sorted-order folds (both committed before the challenge);
- **the walk**: sortedness asserted pairwise; division witnessed as
  quotient/remainder and constrained; fills capped exactly as
  `_runAskClearing`; zero-price asks skipped; outputs asserted against the
  public claim. Ranges = the .sol packed bounds.
- **Measured at N=4**: 689,116 R1CS constraints (keccak-dominated), compile
  4.4s, prove **2.8s**, verify 2ms; the honest clearing verifies and all four
  adversarial mutations — mispriced, skimmed spend, stolen fill, swapped book
  — are **REJECTED**. This is also the closure shape for the §4.3.1 NAMED
  WELD: the clearing tuple lives inside the proof's public statement.

**Named remaining work** (the honest gap between prototype and deployed):
1. `finalizeRecycleWithProof` on the contract: verify proof + re-derive the
   reveal-time book fold (accumulate it at `revealAsk`, ~+5k/reveal) + seed
   pool; fills become a `fillsRoot` public with Merkle-proof `settleAsk`.
2. A purpose-built exported Solidity verifier (the 466k number is the
   25-public settlement verifier; ~8 publics lands near ~410–440k).
3. Fixed circuit size: one Groth16 setup per book size — production options
   are a size ladder (16/64/256/1024), in-circuit length selection to a
   max-N, or routing through the dregg STARK→shrink→BN254 wrap (no
   per-statement ceremony, and keccak is cheap there). The dev single-party
   setup here is UNSAFE by construction, exactly like the settlement fixture
   flow.
4. Prover-side keccak dominates constraints (~172k/ask): fine to ~n=1000
   natively (minutes), the STARK wrap or a keccak lookup argument shrinks it.

---

## 5. Reproduce

```
cd chain
forge test                                                      # 269/269
forge test --match-contract RecycleFlywheelABTest --gas-report  # per-op + premium
forge test --match-contract RecycleFlywheelGasSlopeTest -vv     # the cold O(n) slope
cd gnark && go test -run TestRecycleClearingGroth16EndToEnd -v  # the clearing SNARK e2e
```

Contracts: `chain/contracts/flywheel/RecycleFlywheel.sol`,
`chain/contracts/launchpad/{DreggSolventPool,DreggLaunchpad,LibClone1167}.sol`.
Circuit: `chain/gnark/clearing_snark.go`. Prior measurements:
`docs/reference/RECYCLE-FLYWHEEL-MEASURED.md` (updated with the new numbers).
