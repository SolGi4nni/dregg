# Launchpad formal verification — closing the hand-written-Solidity gap

The launchpad `.sol` was hand-written Solidity with adversarial forge tests
(16/16 + 29/29). Tests exercise *chosen* inputs. This directory replaces that with
a **symbolic proof over ALL inputs** for the two load-bearing anti-rug invariants,
run against the **real compiled bytecode** of the STABLE core contracts.

- **`DreggLaunchToken.sol`** — hard-cap, single-mint ("no hidden supply").
- **`DreggSolventPool.sol`** — never drainable below the disclosed reserve floor.

These two are the load-bearing anti-rug guarantees and they are stable (the live
backstop lane does not change them). `DreggLaunchpad.sol` is spec-only here (it is
mid-edit by the backstop lane) — see §The honest gap.

No `.sol` contract was edited. The harnesses are separate files that import the
contracts read-only.

---

## 1. Tooling assessment (what is actually runnable in this env)

| Tool | Availability here | Verdict |
|------|-------------------|---------|
| **Halmos** (a16z) | `uvx --from halmos halmos` → **0.3.3** (z3 4.16.0, yices bundled). Foundry 1.7.1, solc 0.8.30 (svm). **RUNNABLE.** | **CHOSEN.** Symbolic EVM: executes the real compiled bytecode, all inputs symbolic, bounded call depth. |
| **solc SMTChecker (CHC)** | `solc --model-checker-engine chc` on solc 0.8.26 / 0.8.30 (bundled z3). Runs. | **REJECTED — UNSOUND on these contracts.** See below. |
| **Certora** | needs a cloud prover key — none present. | Not runnable. |
| **Kontrol / KEVM** | not installed (heavy K-framework setup). | Not runnable. |

### Why solc SMTChecker/CHC was rejected (a real finding, not a preference)

CHC is in principle the *strongest* engine (unbounded, inductive Horn clauses). But
it is **unsound on these specific contracts** because they use **custom errors** for
every critical guard (`revert CapExceeded(...)`, `revert AlreadyMinted()`,
`revert PoolFloorBreached(...)`).

Reproduced empirically (solc 0.8.26 **and** 0.8.30):

- A guard written `require(amount <= cap); ...; assert(totalSupply <= cap)` →
  **CHC proves it safe.**
- The *same* guard written `if (amount > cap) revert CapExceeded(amount, cap); ...`
  → CHC reports a **spurious counterexample** in which `mint` accepts `amount=2` at
  `cap=1` (`totalSupply=2 > cap`) — **impossible** given the source guard.
- `revert()` and `revert("string")` are modeled correctly; only `revert CustomError()`
  falls through. Confirmed minimal-repro isolating the flip as the sole cause.

CHC treats a `revert CustomError()` as a **non-blocking fall-through**, so it reports
violations of invariants the contract actually enforces. The only way to make CHC
apply to these contracts would be to **rewrite the guards as `require`** — i.e. verify
a `require`-based *reconstruction*, not the deployed `.sol`. That is a mirror, not a
proof, so it was not done.

Halmos does not have this problem: it runs the compiled bytecode, where a custom-error
revert is a plain `REVERT` opcode. **Halmos is the strongest SOUND runnable tool here.**

---

## 2. The invariant specs (derived from the Lean-proven theorems)

Each on-chain property is the EVM twin of a Lean theorem the metatheory already proves.

### DreggLaunchToken — hard cap + single mint
Lean: **`execMintA_iff_spec`** (`metatheory/Dregg2/Verify/KeystoneAuditSupply.lean:124`,
via `Dregg2.Circuit.Spec.SupplyCreation`) — the supply-authority biconditional, "a
supply the schedule does not disclose cannot enter circulation; the ledger has no
other mint door."

- **INV-CAP**: after ANY call, and after any sequence of calls, `totalSupply ≤ cap`.
- **INV-SINGLE-MINT**: the `minted` latch is one-shot; there is never a second
  successful mint (any caller, any amount) — supply is frozen at the first minted
  amount (≤ cap) or 0.
- **INV-MINTER**: only `minter` can ever mint (a non-minter mint always reverts).

### DreggSolventPool — never drainable below the floor
Lean: **`pool_solvent_forever`** (`metatheory/Market/Liquidity.lean:145`) +
**`graduated_pool_solvent_forever`** (`metatheory/Market/GraduationPool.lean:116`),
whose `PoolFillValidFloor` discipline **refines** rung-6 `PoolFillValid`
(`poolFillValidFloor_refines`, `GraduationPool.lean:66`).

- **INV-FLOOR-BUY**: after any `buy` (any input), `reserveToken ≥ floorToken`.
- **INV-FLOOR-SELL**: after any `sell` (any input), `reserveQuote ≥ floorQuote`.
- **INV-FLOOR-SEQ**: a `buy → sell` sequence keeps BOTH reserves ≥ their floors.
  No trade, and no sequence of trades, by ANYONE, can drain a reserve below its floor.

### DreggLaunchpad — escrow (SPEC-ONLY, see §4)
Lean: **`created_value_conservation`** (`metatheory/Dregg2/Exec/ShieldedValue`) +
**`uniform_price_no_arbitrage`** (`metatheory/Market/Optimality.lean:130`). Invariants
ESC-1..ESC-5 (escrow conservation, settle-xor-refund, no over-allocation,
no-owner-drain, graduation-seed honesty) are written in
`launchpad-spec/test/DreggLaunchpadFV.spec.t.sol`.

---

## 3. Proof results (real Halmos runs)

`uvx --from halmos halmos` in this directory (`solc 0.8.30`, `--solver-timeout-assertion 0`):

```
DreggLaunchTokenFV:
  [PASS] check_cap_singleCall            (paths: 14)
  [PASS] check_cap_seq3                  (paths: 682)   # hard cap over a 3-call arbitrary sequence
  [PASS] check_singleMint_noSecondSupply (paths: 12)    # no 2nd mint / no hidden supply
  [PASS] check_onlyMinterMints           (paths: 4)     # only minter mints
  → 4 passed; 0 failed

DreggSolventPoolFV:
  [PASS] check_buy_neverBelowFloor       (paths: 17)    # token reserve ≥ floor after any buy
  [PASS] check_sell_neverBelowFloor      (paths: 21)    # quote reserve ≥ floor after any sell
  [PASS] check_buyThenSell_neverBelowFloor (paths: 222) # both floors hold over buy→sell
  → 3 passed; 0 failed
```

**Non-vacuity (mutation canary — green-is-not-verification discipline).** Each proof was
checked to be non-vacuous by negating the load-bearing assertion and confirming Halmos
then finds a **counterexample** (i.e. reachable non-reverting success paths exist, and
the invariant holds on all of them):
- Pool `check_buy_neverBelowFloor` with the assert flipped to `reserveToken < floor` →
  **FAIL / Counterexample** (paths: 18). Restored to green.
- Token `check_cap_singleCall` with the assert flipped to `totalSupply == 0` →
  **FAIL / Counterexample** (paths: 14). Restored to green.

**Answer to the gate question:** the **hard-cap + single-mint** (Token) and the
**never-drain floor** (Pool) are now **formally PROVEN symbolically** — over ALL inputs,
against the real bytecode, non-vacuously — for the stated call-depth bound. **No
counterexample / no bug** was found in the two core contracts.

---

## 4. The honest gap (proven vs bounded vs remaining)

**PROVEN (symbolic, all-inputs):**
- Token hard-cap + single-mint + minter-authority, over an arbitrary **3-call**
  sequence across the full external surface (mint/transfer/approve/transferFrom),
  all callers/args symbolic.
- Pool never-drain floor for buy, sell, and a **buy→sell** sequence, all trade
  inputs symbolic.

**BOUNDED (the honest limits of this proof — symbolic-bounded ≠ unbounded):**
- **Call depth is bounded** (Token: 3 steps; Pool: 2 steps). Halmos proves "no
  sequence of ≤ k calls violates the invariant," not the unbounded ∀-sequence
  statement. The invariants are inductive (each function preserves them), so the
  bounded result is strong evidence, but the machine-checked claim is depth-bounded.
- **Pool reserves/amounts are bounded to `~1e30`** to keep the nonlinear
  constant-product (`x·y`) arithmetic tractable for the SMT solver — well above any
  realistic launch, well below the uint256 `x·y` overflow band. Trade amounts within
  that band are fully symbolic.

**REMAINING (named next steps):**
- **DreggLaunchpad escrow** (ESC-1..ESC-5): SPEC written
  (`launchpad-spec/`), compiles against the current ABI, **proof to be RUN after the
  backstop lane lands** (CommitteeAttestor + timeout-refund) — its timeout-refund
  path IS the escrow-conservation surface, so proving now would race a mid-edit
  contract. Deliberately isolated in its own sub-profile so it can never break the
  green Token/Pool proofs.
- **Unbounded proof.** The depth bound is lifted either by (a) an inductive-invariant
  proof (Certora/`certoraRun` with an explicit `invariant`, or Kontrol proving the
  EVM bytecode against a K spec), or (b) **deriving the Solidity from the Lean** so
  the `.sol` inherits the unbounded theorem by construction. Neither tool is present
  in this env; both are the named path to full FV.

---

## Reproduce

```sh
cd chain/formal-verification
uvx --from halmos halmos --solver-timeout-assertion 0      # Token + Pool (the proven core)

# Launchpad spec (compiles; proof pending backstops):
cd launchpad-spec && forge build
```
