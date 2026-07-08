# Alg-complexity audit — Lean exec / circuit / storage / polis

Scope: `metatheory/Dregg2/Exec/**` (minus `DistributedExports.lean` — another lane),
`metatheory/Dregg2/Circuit/**`, `metatheory/Dregg2/Storage/**`, `metatheory/Polis/**`.
Read-only; no source edits. Ranked by complexity × frequency × what-grows, hot first.

## Structural context

The executor's state (`RecordKernelState`) is a **function-as-map** model: `cell : CellId →
Value`, `caps : CellId → List Cap`, `delegate`, `lifecycle`, … are all *functions*, and the
set-shaped side-tables (`nullifiers`, `commitments`, `revoked`) are `List Nat`
(`RecordKernel.lean:317,332`). There is **exactly one** `@[implemented_by]` in the whole scope
(`Exec/Gas.lean`) and **no** `Std.HashMap`/`Std.HashSet` on any executor path. Every "map lookup"
is therefore either an O(depth) walk down a chain of `fun c => if c = … then … else k.cell c`
update-closures, bottoming out in an O(n) `List.find?` over the wire cells; every "set membership"
is an O(n) `List` scan.

The known perf-bomb (`stateOfWState`'s `w.cells.find?`, `FFI.lean:2685`) is **scoped** because
`build_pre_ledger` only puts *touched* cells on the wire, so its O(n²) is O(touched²) per turn.
The findings below are the scans that are **NOT** scoped that way — they run over collections that
grow with **all history** (the nullifier / revocation / commitment sets, which by nature cannot be
scoped to a turn's touched set: a double-spend check needs the whole set).

---

## Top findings

### 1. Nullifier double-spend gate — linear scan over all-history nullifier set  ⟵ HOTTEST
- **`metatheory/Dregg2/Exec/RecordKernel.lean:935`**
  ```lean
  if nf ∈ k.nullifiers then none
  else some { k with nullifiers := nf :: k.nullifiers }
  ```
- **Complexity:** O(|nullifiers|) per note-spend. `nf ∈ (k.nullifiers : List Nat)` compiles to a
  linear `List` membership scan.
- **Hot path?** YES — live per-turn commit path. `execFullTurn → execFullA (noteSpendA) →
  noteSpendChainA (TurnExecutorFull.lean:2160) → noteSpendNullifier`, reached from the
  `@[export] dregg_exec_full…` entry. Fires once per note-spend action in a turn.
- **What grows:** `k.nullifiers` is append-only over **all history** — every note ever spent is
  `cons`'d on and never pruned/scoped. A turn with *p* spends against a chain with *N* historical
  nullifiers is O(p·N), and N grows unboundedly. The full set crosses the wire verbatim
  (`FFI.lean` `nullifiers := w.nullifiers`), so it is never scoped down.
- **FIX:** back the spent-set with `Std.HashSet Nat` via `@[implemented_by]` (membership O(1),
  insert O(1) amortized). The `∈`/`::` proofs (`note_no_double_spend`, `CellNullifier`'s ⊆
  monotonicity) are stated over the `List`/`∈` model and are preserved; only the runtime
  representation changes. This is the single highest-value swap in the executor.

### 2. Credential-revocation gate — linear scan over all-history revoked set
- **`metatheory/Dregg2/Exec/FullForestAuth.lean:481`**
  ```lean
  !(s.kernel.revoked.contains na.credNul)
  ```
  (same pattern at `:500`, `:648`; also `UniversalBridge.lean:189` `n ∈ k.revoked`)
- **Complexity:** O(|revoked|) per authorized action — `revoked.contains` is a linear `List Nat`
  scan.
- **Hot path?** YES — this is the revocation check "read off COMMITTED state" for the forest-auth
  turn, live over `@[export] dregg_exec_full_forest_auth` (`FFI.lean:2067`). Fires per
  credential-bearing action.
- **What grows:** `revoked : List Nat` (`RecordKernel.lean`) is append-only over all history —
  every credential ever revoked. Unbounded, and (like nullifiers) inherently un-scopable: the check
  needs the whole set.
- **FIX:** `Std.HashSet Nat` for `revoked` via `@[implemented_by]`; the `.contains`/`∈` gate proofs
  (`FullForestAuth` revocation-refusal theorems) stay over the model.

### 3. Full-state readback + function-as-map closure chain (per-turn marshal-back)
- **`metatheory/Dregg2/Exec/FFI.lean:2754`** (`wstateOfState`) and **`:387`** (`cellsOfState`):
  ```lean
  cells := cellIds.map (fun c => (c, k.cell c))
  ```
  where `k.cell` after a turn is a stack of *m* update-closures
  (`recCreditCell`/`recSetField`/`sovereignRebind`/…, e.g. `TurnExecutorFull.lean:101,1217,1605`)
  over an O(n) `find?` base (`stateOfWState.cell`, `FFI.lean:2685`).
- **Complexity:** each of the *n* readbacks costs O(n) (find? base) + O(m) (closure depth) →
  **O(n² + n·m)** per turn, n = cells on the wire, m = effects applied this turn.
- **Hot path?** YES — the commit-path marshalling on every turn. **Mitigated:** because
  `build_pre_ledger` scopes the wire to *touched* cells, n = touched-count, so in practice this is
  O(touched² ) — bounded per turn but still quadratic in the touched set, and the closure chain is
  rebuilt fresh each turn.
- **What grows:** the per-turn touched-cell set (scoped) and the per-turn effect count.
- **FIX:** thread the mutable cell/caps state as a `Std.HashMap CellId Value` behind
  `@[implemented_by]` (readback O(n), update O(1)) so lookups don't walk the closure chain and the
  readback isn't quadratic; the `cell`-as-function model and its refinement proofs are unchanged.
  Lower priority than #1/#2 since it's already touched-scoped.

### 4. Circuit descriptor trace-log build — `memOpsOf`/`mapOpsOf`/`umemOpsOf` recomputed per row
- **`metatheory/Dregg2/Circuit/DescriptorIR2.lean:563`** (also `:571`, `:771`):
  ```lean
  def memLog (d) (t : VmTrace) : List MemTraceOp :=
    t.rows.flatMap fun a => (memOpsOf d).filterMap (MemOp.opAt? a)
  ```
  `memOpsOf d = d.constraints.filterMap …` (`:553`) is O(C) over **all** descriptor constraints and
  is recomputed **inside** the `flatMap` for **every** trace row.
- **Complexity:** O(T · (C + M)) = **O(T·C)**, where T = trace rows, C = total constraints, M = mem
  ops. Should be O(C + T·M): hoist `memOpsOf d` out of the loop.
- **Hot path?** Per-turn circuit descriptor / witness build **when proving is on** (the
  verification-mode-lattice's full/re-exec rungs), not the µs symbolic-commit fast path. Same shape
  in `mapLog` (`:571`) and `umemLog` (`:771`).
- **What grows:** T (trace length ~ turn complexity) and C (descriptor size).
- **FIX:** `let ops := memOpsOf d` once before the `flatMap` (pure hoist — a `let`-lift, no proof
  change; `memOpsOf d` is closed in `a`). Same for `mapLog`/`umemLog`.

### 5. Polis Datalog closure — `List.contains` membership + non-dedup accumulation
- **`metatheory/Polis/PolisDatalog.lean:35`**
  ```lean
  def fire (rules) (known : List Atom) : List Atom :=
    known ++ (rules.filter (fun r => r.body.all (fun a => known.contains a))).map (·.head)
  ```
- **Complexity:** each round is O(R · b · |known|) — `known.contains a` (`:35`) is a linear scan,
  run for every body atom of every rule. Worse, `fire` accumulates with `known ++ …` and **never
  dedups**, so `known` re-grows by up to R (with duplicates) each round; over the k-round
  `deriveWithin` closure this compounds to roughly **O(k² · R² · b)**. `PolisAuthReach.lean:43`
  (`heldAuths` + `.any`) and `PolisAuthReachDatalog` sit on the same object.
- **Hot path?** Governance / viability-derivation checks (non-domination layer) — not the per-turn
  commit path; medium-to-rare frequency, but the input (rule-base, fact-set) can be large.
- **What grows:** the fact/known set (grows every round) and the rule-base.
- **FIX:** carry `known` as `Std.HashSet Atom` (O(1) membership) and dedup the per-round additions
  (only insert genuinely-new heads) so the set doesn't accumulate duplicates — turns the closure
  into the standard semi-naïve O(rounds · R · b). `@[implemented_by]` keeps the `∈`/`Derivable`
  proofs over the `List` model.

---

## Honorable mentions (lower rank)

- **`FFI.lean:957` `observedLabels`** — O(k²) dedup: `foldl (fun acc l => if acc.contains l then
  acc else l :: acc)` then `mergeSort`. Scoped to a turn's labels (caps+cells+action operands), so
  bounded per turn; the quadratic `contains`-dedup could be a `HashSet` pass but the constant is
  small. Rubric-4, minor.
- **`Storage/BucketCommitment.lean:47` `contentRoot` → `Lightclient/MMR.lean:167` `peaksOf`** —
  `peaksOf L = L.foldl appendLeaf []` rebuilds the whole MMR forest from the **full** object list on
  every `contentRoot` call (O(n)); called per object-add it's O(n²) to fill a bucket. The file's own
  note says the *deployed* implementation maintains the peaks incrementally and `peaksOf_append`
  proves the two agree — so this is a recompute-in-the-model, not a shipped hot loop. Storage-market
  path, not per-turn commit. Rubric-3, deferred to the incremental impl.
- **`Storage/Deployed.lean:33`** — `xs.foldl (fun acc x => p2compress …)` is a single O(n) hash
  fold (fine); flagged only against being called in an outer loop.

## Summary ranking

| # | Site | Complexity | Frequency | Grows with | Fix |
|---|------|-----------|-----------|-----------|-----|
| 1 | `RecordKernel.lean:935` nullifier gate | O(history)/spend | per-turn commit | all spent nullifiers | `Std.HashSet` |
| 2 | `FullForestAuth.lean:481` revoke gate | O(history)/action | per-turn commit | all revoked creds | `Std.HashSet` |
| 3 | `FFI.lean:2754/387` readback + closure chain | O(n²+nm)/turn (touched-scoped) | per-turn commit | touched cells, effects | `Std.HashMap` state |
| 4 | `DescriptorIR2.lean:563/571/771` trace logs | O(T·C) vs O(C+T·M) | per-turn (proving on) | trace, constraints | hoist `memOpsOf` |
| 5 | `PolisDatalog.lean:35` `fire` closure | ~O(k²R²b) | governance | facts, rules | `HashSet` + dedup |

All fixes are `@[implemented_by]`/`let`-hoist shaped — the `List`/`∈`/function-map **models and
their proofs are preserved**; only the runtime representation changes. Nos. 1 and 2 are the two that
grow **unboundedly with chain history on the live commit path** and should be swapped first.
