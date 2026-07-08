# Alg-complexity audit — Lean consensus/distributed

**Scope.** `metatheory/Dregg2/Distributed/**` (25 files, ~12.2k lines) + the `@[export]`s in
`metatheory/Dregg2/Exec/DistributedExports.lean`. Read-only recon; NO source edits. HEAD `58663962f`.

**The hunted class** (from `docs/PERF-BOMB-AUDIT.md` / the `tauOrderFast` kill `02c4e1709`): a `List`
used where a `HashMap`/`HashSet` belongs (`.find?`/`.contains`/`.dedup`/`.filter`-as-lookup scanned
per element), or a value recomputed from scratch each call whose input grows with state (causal-past,
log, committee), with no memo/incremental — O(n²)/O(n³) that worsens as the network runs.

**Already known — not re-reported as primary (siblings noted where they appear):**
- `mkPastCache`/`cachedPast`/`roundLookup` (`BlocklaceFinality.lean`) — the List-cache the `fast*`
  `Std.HashMap`/`HashSet` twins + `@[implemented_by tauOrderFastImpl]` (`:734`) fixed in `02c4e1709`.
  The exported finality path (`dregg_blocklace_finalize`/`dregg_tau_order` via `tauGoldenFast`/
  `tauOrderFast`) rides the twin — **covered**.
- `directDepsOf`/`hbReach` (`DistributedExports.lean:545`/`:561`, export `dregg_coord_causal_order`) —
  Tier-2 in the perf-bomb doc. `directDepsOf` is an O(|turns|) `List.filter` re-scanned per frontier
  node per BFS layer; `hbReach`'s per-layer `.dedup` (`:565`) is O(k²). Same recipe fix. **Known.**

---

## Framing that matters for triage

The distributed tree has **two populations** of executable code, and they must be triaged differently:

1. **Live FFI-export paths** — the eight `@[export]`s (`FinalityGate` ×2, `StrandAdmission` ×1,
   `DistributedExports` ×5). These are the only functions the node/coord runtime actually calls.
   Result: the finality exports ride the `tauOrderFast` twin (covered); `handoff`/`drop`/`pipeline`/
   `2pc` are O(1) scalar tallies; `causal` is the known `hbReach`; `budget`'s `resolveOrdered` is a
   single fold over the per-query debit list (bounded). The **one genuinely-new live export suspect is
   `dregg_strand_admit` → `admitted`** (finding #3), and it is O(committee²).

2. **Denotational MODEL code** (the other ~20 files) — executable Lean that mirrors a Rust runtime
   structure but is **not** `@[export]`ed. Several model a finite map / receipt index as a plain
   `List` (assoc-list `Dir`, whole-log `logRoot`, per-vote `causalPastIncl`). These are O(n)/O(n²) **if
   the Lean is evaluated at scale** (differential / `#guard` / any future `@[export]`), while the
   deployed Rust already uses a `BTreeMap`/`HashMap`/MMR. They are the exact hunted class and are
   fixable in-Lean the `tauOrderFast` way (an `@[implemented_by]` HashMap/MMR twin, proofs untouched),
   but they are NOT presently on the live commit path. Findings #1/#2/#4/#5 are this population; ranked
   by how closely they match the class and how load-bearing the mirrored structure is.

The `@[implemented_by]` twin recipe applies to every finding below: swap the `List` op for the
`Std.HashMap`/`HashSet`/MMR op on a runtime twin, attach `attribute [implemented_by …]` to the pure
def, leave every theorem alone (runtime-only, axiom-clean — `#assert_axioms` stays green).

---

## Ranked findings

| # | name | file:line | complexity | live hot-path? | what grows | fix |
|---|------|-----------|-----------|----------------|-----------|-----|
| 1 | `distinctApprovers` recomputes `causalPastIncl` per vote | `MembershipSafety.lean:200`/`:208` | O(\|votes\|·\|B\|²) | model (mirrors `constitution.rs::VoteTracker`); per governance proposal | votes × DAG | hoist `causalPastIncl` once → HashSet membership; twin |
| 2 | `logRoot` re-maps+re-sponges the WHOLE log every commit | `HistoryAggregation.lean:112` (in `chainedCommit:122`) | O(N)/turn ⇒ O(N²) | per-turn-commit SHAPE (model; deployed = incremental MMR) | receipt log N | incremental MMR twin (matches deployed `iroot`) |
| 3 | `admitted`/`distinctVouchersFor` — `isRoot`-per-vouch + O(k²) dedup | `StrandAdmission.lean:127`/`:143` | O(\|vouches\|·(\|seeds\|+\|bonds\|) + k²) | **LIVE** — `@[export] dregg_strand_admit` | committee / registry | HashSet roots + HashSet dedup twin |
| 4 | `Dir.get`/`upsert` — association-list finite map | `DirectoryLaws.lean:107`/`:111` | O(n) get/put ⇒ O(n²) build | model (mirrors `BTreeMap` in `directory.rs`) | # registered names | `@[implemented_by]` BTreeMap/HashMap twin |
| 5 | `applyDelta` filter-by-`contains` + Join `dedup` | `EpochReconfig.lean:135` · `MembershipSafety.lean:166` | O(\|old\|·\|removed\|) · O(n²) dedup | model; per epoch/membership change (rare) | committee | HashSet-diff; incremental threshold recount |

---

### 1. `distinctApprovers` recomputes the causal past **per vote** — the "recompute where a cache belongs" class, verbatim

`MembershipSafety.lean:200`
```
def inPastOf (B : Lace) : InPast :=
  fun proposalBlock voteBlock => (causalPastIncl B proposalBlock).contains voteBlock
```
`MembershipSafety.lean:208`
```
def distinctApprovers (c : Constitution) (proposalBlock : BlockId)
    (votes : List VoteRec) (inPast : InPast) : List AuthorId :=
  ((votes.filter (fun v => c.isParticipant v.voter && inPast proposalBlock v.voteBlock)).map (·.voter)).dedup
```
`inPast proposalBlock v.voteBlock` is applied **once per vote** inside the `filter`, and with the
`inPastOf B` instance that node uses (`:200`, the `finality.rs::causal_past` closure) it recomputes
`causalPastIncl B proposalBlock` — the **whole** causal-past walk of `BlocklaceFinality` (List-backed:
`causalPastAux`'s `acc.dedup`/`acc.contains`, itself ~O(\|B\|²)) — from scratch on every vote. The
proposal block's causal past is **invariant across all votes**: it should be computed once. Two extra
teeth: `c.isParticipant` (`:121`) is a `.contains` O(\|participants\|) per vote, and the trailing
`.dedup` (`:211`) is O(\|votes\|²). Net O(\|votes\|·\|B\|²).

- **Class:** recompute-where-a-cache-belongs (like `cachedPast`) **and** List-where-HashSet-belongs.
- **Hot-path:** model code — `distinctApprovers`/`hasPassed` are not `@[export]`ed (governance vote
  counting runs in Rust `constitution.rs`, whose docstring already says "per-proposal `HashSet<voter>`").
  Cadence *if run*: once per membership-proposal evaluation. Not the live commit path today.
- **Fix:** hoist `let past := fastCausalPastIncl B proposalBlock` (the HashSet twin already in
  `BlocklaceFinality`, `:596`) once, membership-test votes against it, and dedup voters through a
  `Std.HashSet AuthorId`. Or an `@[implemented_by]` twin over `distinctApprovers`. Proofs untouched.

### 2. `logRoot` rebuilds the entire receipt index every per-turn commit

`HistoryAggregation.lean:112`
```
def logRoot (log : List Dregg2.Exec.Turn) : ℤ :=
  compressN (logFelts compressN log)          -- logFelts = log.map (turnReceipt …)
```
`chainedCommit` (`:122`) — documented as "THE DEPLOYED ROTATED per-turn commitment" — calls
`logRoot compressN st.log`, and `st.log` is the **append-only receipt log that grows by one every
turn**. So committing turn N re-maps `turnReceipt` over and re-sponges all N receipts: O(N) per turn,
O(N²) cumulative over a chain — the receipt-index analogue of the `tauOrder` whole-DAG rebuild.

- **Class:** recompute-from-scratch where the input grows with state; per-turn-commit **shape**.
- **Hot-path:** the shape is the commit path, but this is the MODEL — the deployed side is an
  **incremental MMR** ("faithful stand-in for the deployed receipt-index MMR root", `:110`), which
  appends in O(log N). So the live node is fine; the exposure is the Lean model being non-incremental
  (any at-scale `#eval`/differential is O(N²), and it blocks ever putting `chainedCommit` on-path).
- **Fix:** an incremental MMR/rolling-sponge twin that folds only the new turn's receipt onto a carried
  accumulator (`@[implemented_by]`), so the model matches the deployed `iroot` cost profile.

### 3. `admitted` — the one LIVE export suspect: `isRoot` re-scanned per vouch + O(k²) dedup

`StrandAdmission.lean:127`
```
def distinctVouchersFor (fed : AdmissionState) (candidate : AuthorId) : List AuthorId :=
  ((fed.vouches.filter (fun v => v.candidate == candidate && isRoot fed v.voucher)).map (·.voucher)).dedup
```
`admitGate` → `admitted fed q` (`:143`, `@[export dregg_strand_admit]` `:573`) reaches
`vouchedToThreshold` → `vouchedBy` → `distinctVouchersFor`. For every vouch the `filter` calls
`isRoot fed v.voucher` = `isSeed` (`fed.seeds.contains`, O(\|seeds\|)) `||` `hasValidBond`
(`fed.bonds.filter …`, O(\|bonds\|)) — an O(\|seeds\|+\|bonds\|) scan **per vouch** — then the result
is `.dedup`'d (O(k²)). Net O(\|vouches\|·(\|seeds\|+\|bonds\|) + k²), quadratic in committee/registry
size, on the **live** admission export.

- **Hot-path:** LIVE (`dregg_strand_admit`), but cadence is per-admission (rare) and bounded by the
  current committee, so at realistic N the constant wins — the perf-bomb doc's "REFUTED (bounded by
  committee)" holds *today*. Flagged because the committee grows over the network's life and it is the
  only genuinely-new quadratic on an export.
- **Fix:** precompute the root set into a `Std.HashSet AuthorId` once (seeds ∪ bonded), test `isRoot`
  in O(1), and dedup vouchers through a HashSet — an `@[implemented_by]` twin, proofs untouched.

### 4. `DirectoryLaws` models a name directory as an association `List`

`DirectoryLaws.lean:107`/`:111`
```
def Dir.get (d : Dir) (name : Name) : Option Entry := (d.entries.find? (fun p => p.1 = name)).map (·.2)
def upsert : List (Name × Entry) → Name → Entry → List (Name × Entry)
  | [],      name, e => [(name, e)]
  | p :: ps, name, e => if p.1 = name then (name, e) :: ps else p :: upsert ps name e
```
Every `get`/`register`/`lookup`/`resolves`/`revoke` does an O(\|entries\|) `find?`/`upsert` scan;
populating a directory of n names is O(n²); a resolve storm is O(n) each. Classic List-where-a-map.

- **Hot-path:** model — no `@[export]`; the docstrings say it mirrors `BTreeMap::get/insert`
  (`directory.rs:231/248`), i.e. the deployed side is already O(log n). Exposure is only the Lean model
  at scale. Included because it is the cleanest structural instance of the hunted pattern.
- **Fix:** `@[implemented_by]` a `Std.HashMap Name Entry` (or `Std.TreeMap` to keep the ordered
  semantics `upsert`'s "first binding" relies on) twin; proofs read the pure `List` def unchanged.

### 5. Membership/epoch reconfig — `contains`-filter diff + O(n²) dedup on every change

`EpochReconfig.lean:135`
```
def applyDelta (old : List K) (d : Delta K) : List K :=
  (old.filter (fun m => !(d.removed.contains m))) ++ d.added        -- O(|old|·|removed|)
```
`MembershipSafety.lean:166` (Join branch of `applyProposal`) and `Constitution.new` (`:116`) rebuild
the participant set with `(c.participants ++ [k]).dedup` — O(n²) — and recompute the threshold over the
deduped list from scratch each change. Per epoch transition / membership change (rare, small committee),
so low severity, but the same class.

- **Hot-path:** model; per-reconfig (rare).
- **Fix:** HashSet-based set-difference for `applyDelta`; keep the participant set as a HashSet and do an
  incremental insert + O(1) size-driven threshold recount instead of `++.dedup`.

**Tail note (not ranked).** `EntangledJoint.entangleWith` (`:312`) appends `cliqueEdges` (O(cells²),
`:306`) to an **ever-growing, never-deduped** `g.edges` List, and `entangled` (`:283`) tests membership
by O(\|edges\|) `List` scan — a growing-List membership scan per query. Per joint-turn / small cell
sets, so minor, but if the entangle graph is ever queried on a hot path it wants a `HashSet` edge set.
