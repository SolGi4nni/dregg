# MUTABLE-MAP-SORTEDNESS-INVESTIGATION — does the cell/accounts `.insert` (op=3) force sortedness?

**Read-only soundness investigation, grounded at HEAD (branch `mldsa-sign-route`, 2026-07-13); every
claim cites file:line. Sibling emit WIP is live — this file edits NO code.**

Target: gap #5 (`CANONICAL-HEAP-TREE-INVESTIGATION.md`) found the append-only set-insert
(`nullifierInsertOp`/`commitmentsInsertOp`/`revokedInsertOp`) was an UNFORCED compacted-array
placement → forge-absence → double-spend, and closed it by flipping those three to `MapKind::AafiInsert`
(op=4, the pointer-preserving `imtInsert` that forces the `ImtSorted` well-linked invariant). The
MUTABLE accounts/cell path (`createCell`/`CreateCellFromFactory`/`Spawn` + the heap value-writes)
DELIBERATELY stayed op=3. Question: does op=3 on the cell tree have the SAME gap?

## VERDICT: ✅ GAP #6 — SAME CLASS AS #5, DEPLOYED, **NOW CLOSED** (forged cell creation / cell takeover)

**CLOSURE (2026-07-13):** `cellsInsertOp` flipped from `.insert` (op=3) to `.aafiInsert` (op=4) in
`EffectVmEmitRotationV3.lean:2704` — so createCell/factory/spawn (and the cap-open spawn variants
`spawnCapOpen`/`spawnWriteCapOpen`, which all route through the one `cellsInsertOp` def) now force the
two-path `imtInsert` gate that installs the `ImtSorted` well-linked invariant `cellsFreshOp`'s
pointer-bracket presupposes. Rust producers flipped to the append-at-free-index AAFI fold: the narrow
`generate_rotated_create_cell_trace_with_accounts_tree` commits `insert_witness_aafi(entry(key,key))
.new_root`, and the wide `generate_rotated_create_cell_wide` lays `lay_accum_insert_read_appendix(…,
aafi=true)` (wide == narrow == the §J′ capRoot-column read input, all the AAFI root). The deployed
descriptor artifacts (`rotation-v3-staged-registry.tsv` + the two wide registries) carry the cell
inserts at `aafi_insert`. Soundness/liveness teeth land in `rotated_create_cell_pins_accounts_and_refuses_tamper`
(forged-cell-birth over a present addr is UNSAT; honest createCell proves+verifies). Rides the same
VK regen as gaps 1-5 (the accounts-root lineage changed sorted→AAFI). Value-updates (op=1 `.write`)
were untouched (already position-stable/sound).

The mutable accounts tree is the **same `CanonicalHeapTree8`**, opened through the **same shared
`Ir2Air::MapOps` / `Ir2Air::MapAbsent` AIRs**, but its insert emitter was **left at op=3 while the
three append-only siblings were flipped to op=4**. The `.absent` freshness gate the cell path relies on
is sound ONLY relative to the `ImtSorted` well-linked invariant — and op=3 does not install it. So a
malicious prover forges a cell absence on a present addr → forged `createCell`/`factory`/`spawn` over
an existing cell.

---

## 1. The deployed op=3 cell insert does NOT force sorted placement (the gate, read)

`cellsInsertOp` (`EffectVmEmitRotationV3.lean:2704-2710`) emits `op := .insert` (op=3). Contrast the
three siblings now at `op := .aafiInsert` (op=4): `nullifierInsertOp:2288`,
`commitmentsInsertOp:2483`, `revokedInsertOp:2583` — each carrying `-- gap-#5 AAFI … two-path forces
sorted-preservation`. **Cells alone stayed op=3.**

What op=3 forces in the deployed AIR (`descriptor_ir2.rs:2883-3052`, read directly):

* `not_insert = 1 − inv6·op·(op−1)` is **0 at op=3** (`:2907`). Hence `rw_sel = not_insert + s = 0`
  (`:2928`, s=0 off-AAFI) → the **old-leaf absorb is suppressed** (`:2989`), and `not_insert3 =
  not_insert + 2s = 0` (`:2929`) → the **old-chain fold to the pre-root is OFF** (`:3035`).
* Only the new-leaf chain fires (gated `is_real·not_aafi`, `:3049`): it folds the arity-3 IMT leaf `hash[key, value, next_addr]` (`map_leaf_input_cols`) up the
  witnessed sibling path to `MAP_NEW_ROOT` (`:3038-3051`).

So the **entire op=3 constraint is: "the AFTER root contains `(key,value)` at the witnessed path."**
It does NOT bind the after-root to the before-root, does NOT force sorted placement, does NOT force
`next_addr` relinking, and does NOT force dedup. Everything that makes the tree sorted-canonical
(`sort + dedup + relink_next_addrs`, `heap_root.rs:162-175`) is **producer-side inside
`CanonicalHeapTree8::new`** (`trace_rotated.rs:1571`) — never a gate. This is exactly the gap #5
`.insert` picture; the Lean models it as an in-place `writesTo` (`RotatedKernelRefinementBirth.lean:510`),
NOT a sorted splice.

## 2. The cell FRESH/absence check PRESUPPOSES sortedness (does not force it)

`cellsFreshOp` (`EffectVmEmitRotationV3.lean:2699`) emits `op := .absent`, routed to the deployed
`Ir2Air::MapAbsent` — the **IMT pointer-bracket** (`descriptor_ir2.rs:3196-3313`): a single low-leaf
`hash[lo_addr, lo_value, low_next]` opens to the committed root, and `lo_addr < key < low_next` is
checked as integers (`:3216-3252`). The AIR comment is candid (`:3213-3216`):

> *"Sound relative to the maintained well-linked (`ImtSorted`) invariant the insert-preservation gate
> installs; here the pointer is a committed leaf field."*

For the three op=4 sets that insert-preservation gate now EXISTS (their `.aafiInsert` two-path forces
`imtInsert`). **For cells it does not** — `cellsInsertOp` stayed op=3. So on the accounts tree the
`next_addr` pointers are a producer-trust artifact; the pointer-bracket brackets whatever committed
`low_next` the prover supplies.

## 3. The concrete forged-cell witness (verdict-C shape)

Adversary controls the committed BEFORE accounts tree (their witness). Target addr `X` is ALREADY a
present cell they want to seize.

* Commit an accounts leaf set containing `X`'s real leaf, but **forge the `next_addr` links** of a
  neighboring low leaf `L = (lo_addr, v, low_next)` so that `lo_addr < X < low_next`, while `X`'s own
  leaf sits elsewhere in the (non-well-linked) tree. Compute the genuine `node8` root over these leaves
  → put it in the `cells_root` limb (`B_CELLS_ROOT = 0`, `trace_rotated.rs:1515`).
* `cellsFreshOp .absent`: open `L` to the committed root (genuine member ✓), integer-check
  `lo_addr < X < low_next` ✓. Every deployed gate ACCEPTS → `X` "proven fresh / no id collision".
* `cellsInsertOp .insert`: publish any after-root containing `(X,X)` (op=3 asks nothing else).
* → `createCell`/`CreateCellFromFactory`/`Spawn` on the **already-present addr `X`** succeeds:
  **forged cell birth over an existing cell** — identity/state takeover, re-birth, or overwrite.

Companion read-forge (unforced dedup): commit `X` at two positions with different values; a cell READ
(op=0 `.read`) opens either path to the root, returning the adversary-favorable value — **wrong cell
read**. Both are the gap #5 exploit shape, now against the accounts set.

## 4. What is SAFE — value updates (heap writes, op=1 `.write`)

The heap value-write (`.write`, op=1) opens the OLD leaf `(key,vOld)` to the pre-root and the NEW leaf
`(key,vNew)` to the post-root over the SAME siblings (`descriptor_ir2.rs:3018-3051`, old-chain ON via
`not_insert3`≠0 at op∈{0,1}). It therefore **requires the addr to be a genuine member** and rebinds
both roots — its own soundness does not depend on global sortedness. The only sortedness-linked risk it
inherits is the §3 duplicate-addr ambiguity, which the same fix closes. So the mutable VALUE-UPDATE
semantics do **not** need a separate remedy beyond the insert fix.

## 5. Is the cell tree shared with the (fixed) append-only tree?

**Same TYPE, separate INSTANCE.** All accumulators are `CanonicalHeapTree8` (`heap_root.rs`) opened
through the one shared `MapOps`/`MapAbsent` AIR pair. They are distinct committed limbs: cells =
`cells_root` limb 0 (`B_CELLS_ROOT`, `trace_rotated.rs:1515`); nullifier/commitments ride limb 26/27;
revoked rides 82..88. The op=4 flip was applied **per-emitter** to the three append-only instances and
simply **not routed to `cellsInsertOp`**. The machinery to fix cells already exists on the shared AIR
(op=4 + `AafiInsertWitness8`, `descriptor_ir2.rs:2909-3196`, `heap_root.rs`).

## 6. Fix — SAME as gap #5 (extend the op=4 flip to `cellsInsertOp`), with the same representation caveat

The remedy is the SAME as #5: flip `cellsInsertOp` (and its `createCell`/`factory`/`spawn` call sites)
from `.insert` (op=3) to `.aafiInsert` (op=4), so the two-path `imtInsert` gate installs the
`ImtSorted` well-linked invariant the `cellsFreshOp` pointer-bracket already depends on. This closes
the forged-cell-creation gap by exactly the mechanism that closed the double-spend.

The one MUTABLE-specific caveat is the representation caveat gap #5 already surfaced
(`CANONICAL-HEAP-TREE-INVESTIGATION.md` §"GAP #5 CLOSURE OBSTRUCTION"): AAFI op=4 mirrors `imtInsert`
with **stable positions (append-at-free-index / sparse-by-addr)**, whereas today's cells tree is the
**compacted-sorted-array** (`CanonicalHeapTree8::new` re-sorts + shifts the suffix, `heap_root.rs:162`).
So the cell flip must accompany the SAME append-at-free-index / sparse-by-addr representation the
append-only sets migrated to — it is **not a new, separate sparse-by-addr decision**, it is that one
migration extended to the accounts tree. Value-updates (`.write`) are already position-stable and ride
the AAFI representation unchanged.

## Honest scope of the mutable-map soundness

The accounts/cell membership (READ), value-update (WRITE), and path-binding are sound under
`Poseidon2SpongeCR`. The mutable-map **freshness (cell creation) is a PRODUCER-TRUST assumption**,
identical in class to gap #5's insert arm: the committed accounts tree's well-linked/sorted/dedup
structure is maintained by the honest producer (`CanonicalHeapTree8`), NOT forced by the deployed op=3
gate. Under the full-adversary SNARK model this is a **sixth deployed gap (forged cell creation / cell
takeover / wrong cell read)**, closed by extending the gap-#5 AAFI op=4 flip to `cellsInsertOp`.
