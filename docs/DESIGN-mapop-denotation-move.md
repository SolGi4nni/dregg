# DESIGN — moving the map-op DENOTATION onto the deployed indexed-Merkle commitment

**Status:** scoping doc + landed first step (`Dregg2/Circuit/MapDenotationSchema.lean`).
**Date:** 2026-07-25.
**Refutation this responds to:** `metatheory/Dregg2/Circuit/MapReconcileImtRepoint.lean` (commit
`234de11e91`, 826 lines) — verified green in this tree, `#assert_axioms`-clean.

---

## 0. The finding, restated at its real resolution

The deployed map tree commits **arity-3** indexed-Merkle leaves `hash[addr, value, next_addr]` for
every map-op kind. Two independent confirmations in the deployed Rust, both read this session:

* `circuit/src/descriptor_ir2.rs:2198` — `fn map_leaf_input_cols(value_col) -> [usize; 3]`, body
  `[MAP_KEY, value_col, MAP_NEXT]`, comment *"IMT leaf `hash[addr, value, next_addr]` (arity 2 → 3)"*.
  ⚠ The doc-comment **above** that function still describes the arity-2 shape ("Today the `MapOp`
  leaf is the 2-field sorted-`Heap` leaf `hash[key, value]` … the denotation `MapOp.holdsAt` opens
  against"). That stale comment IS the drift, still in the tree.
* `circuit/src/heap_root.rs:143` — `HeapLeaf::digest` = `hash_many(&[addr, value, next_addr])`.

Lean's `DescriptorIR2.opensTo` / `writesTo` commit **arity-2** `Heap.leafOf` leaves. The refutation
lifts the leaf separation to roots (`imtRoot_ne_mapRoot`) and concludes, at a deployed pre-root:
`ReconcileGatesAt` is empty **for every op kind**, and — the wall —
`mapOpHoldsAt_unsat_at_imtRoot`: **`MapOp.holdsAt` itself is refuted**. Since `MapOp.holdsAt` is what
`Satisfied2`'s `.mapOp` arm asserts and what every `AlgoStarkSound*` theorem concludes about, no
premise repointing can help. The denotation must move.

**One correction to the framing, and it matters.** The separation theorems carry
`hCR : Poseidon2SpongeCR hash`, and that hypothesis is **PROVED FALSE at deployed BabyBear
parameters** (`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`; see commit `3245e88148`, which
began cutting the map/heap opening spine off it). So the refutation is machine-checked *at
`refSponge`*, an injective idealisation, not at the deployed sponge. This does not weaken the
verdict — it sharpens it. Read at deployed parameters the statement is: *at any injective hash the
apex conclusion is FALSE at the deployed commitment; at the actual sponge it can only be true via a
collision the prover cannot exhibit.* Either way the apex says nothing about a real turn. Any work
downstream of this doc must be authored in the **post-cutover idiom** (`_or_collides` + a total
extractor + a bounded collision event), not under `Poseidon2SpongeCR` — otherwise it is priced at
nothing.

---

## 1. THE SURFACE — everything that moves, in dependency order

The single most important structural fact, and it is good news:

> Everything between the denotation and the apex treats `MapOp.holdsAt` as an **opaque `Prop`**.
> `VmConstraint2.holdsAt`, `Satisfied2`, `MemoryLegs`, `algoStarkSound_of_mapShape` and all its
> fan-outs never look inside it. So the move is **one definition body plus its producers and its
> destructuring consumers** — not a rewrite of the apex.

### (a) Definitions whose BODY changes — 3, and none changes TYPE

| # | Declaration | file:line | note |
|---|---|---|---|
| a1 | `DescriptorIR2.opensTo` | `Dregg2/Circuit/DescriptorIR2.lean:534` | body → schema instance |
| a2 | `DescriptorIR2.writesTo` | `Dregg2/Circuit/DescriptorIR2.lean:539` | body → schema instance |
| a3 | `DescriptorIR2.MapOp.holdsAt` | `Dregg2/Circuit/DescriptorIR2.lean:577` | **the cutover line** |

Rebinding a3's body to `MapOp.holdsAtS (imtSchema …)` is sufficient; a1/a2 can be rebound with it or
retired. Because the *type* is unchanged, `Satisfied2` needs **no new parameter** — which is what
keeps the blast radius finite. Parameterising `Satisfied2` by a schema would be the obvious move and
it is the wrong one: it would touch every `Satisfied2` mention in the tree.

### (b) Declarations that merely RE-ELABORATE (statement and proof unchanged)

| Declaration | file:line |
|---|---|
| `VmConstraint2.holdsAt` (`.mapOp` arm: `m.holdsAt hash env`) | `DescriptorIR2.lean:656` |
| `Satisfied2` (`rowConstraints`) | `DescriptorIR2.lean:674` |
| `Satisfied2Public` / `Satisfied2U` / `Satisfied2Custom` | `DescriptorIR2.lean:690, 875, 1077` |
| `AlgoStarkSoundGeneral.MemoryLegs` | `AlgoStarkSoundGeneral.lean:223` |
| `AlgoStarkSoundFanoutMemory.algoStarkSound_of_mapShape` | `AlgoStarkSoundFanoutMemory.lean:266` |
| `…_of_mapShape_noOodShape` | `AlgoStarkSoundFanoutMemory.lean:581` |
| the **8 per-effect fan-outs** — noteSpendV3, noteCreateV3, createCellV3, factoryV3, spawnV3, spawnWriteV3, refusalFieldsWriteV3, heapWriteV3 | `AlgoStarkSoundFanoutMemory.lean:400, 417, 434, 451, 468, 486, 503, 521` |
| the `Rfix` route | `AlgoStarkSoundKernelAvail.lean:155` |
| `AlgoStarkSound` (the class) | `FriVerifierBridge.lean:75` |

This is the category the brief expected to be large. It is large **and free**: these are exactly the
"one denotation change, not eight" the refutation lane predicted, and the prediction holds.

### (c) Declarations whose STATEMENT genuinely changes — the ones needing argument

**Producers** (must be *re-proved* at the new commitment; today they produce the arity-2 object):

| Declaration | file:line | what changes |
|---|---|---|
| `MapOpsColumnLayout.ReconcileGatesAt` | `MapOpsColumnLayout.lean:807` | the arity-2 gate model; the `.absent` arm already has an arity-3 twin (`MapAbsentImtGate.AbsentImtGatesAt`), the other **four kinds do not** |
| `MapOpsColumnLayout.reconcileGates_force_opening` | same file, §5 | the per-kind opener law |
| `MapOpsColumnLayout.mapOp_holds_of_mapReconcile` | `MapOpsColumnLayout.lean:900` | |
| `MapOpsColumnLayout.mapOpsArm_of_modeler` | `MapOpsColumnLayout.lean:922` | the `.mapOp` arm ∀ d |
| `MapReconcileFamily` | `AlgoStarkSoundFanoutMemory.lean:119` | its body names `ReconcileGatesAt` |
| `memoryLegs_of_mapShape` | `AlgoStarkSoundFanoutMemory.lean` §3 | assembles the arm |

**Consumers that destructure the arity-2 content** (a proof, not a statement, breaks — except where
noted):

| Declaration | file:line | note |
|---|---|---|
| `MapOpWideKeyGate.narrow_holdsAt_is_instance` | `MapOpWideKeyGate.lean:625` | ⚠ **an existing `Iff.rfl` whose STATEMENT becomes FALSE.** It asserts `MapOp.holdsAt ↔ HoldsKindMerkleW narrowEnc …`, i.e. that the deployed denotation IS the arity-2 wide-key instance. After the cutover that is not a broken proof, it is a wrong claim; it must be restated over `holdsAtS narrowSchema`. This is the single named `rfl` casualty. |
| `DecideMapMerkle.mapDecMerkle` + soundness | `DecideMapMerkle.lean:153, 210` | the only two `unfold MapOp.holdsAt` sites in the tree |
| `Satisfied2Faithful`, `DecideSatisfied2`, `DecideSatisfied2Golden` | 1 mention each | decision-procedure legs |
| per-effect teeth (`*_grow_gate_forces_set_insert`, `*_forces_write`, `heapWrite_splice_forced`) | `Emit/*`, `RotatedKernelRefinement*` | consume `Satisfied2`; they re-elaborate unless they open the opening |

**Size of the surface, measured:** 14 `.lean` files mention `MapOp.holdsAt`; 23 mention
`opensTo`/`writesTo`. Only **2** sites in the whole tree `unfold MapOp.holdsAt`, and only **1**
existing `rfl` punches through it. That is the honest number, and it is much smaller than the file
counts suggest.

---

## 2. CONSERVATIVITY — **YES, the move exists, and it is landed**

The wide-key epoch's trick (fold the new obligation into a *field* of a structure whose narrow
instance already *is* the old thing — `LaneEnc.HeapOk`) has an analogue here, and it is **cleaner
than that one**.

The reason it is cleaner is a fact about the deployed prover, confirmed in
`heap_root.rs::relink_next_addrs` (line 172): the leaves are stored **in sorted-by-`addr` position
order**, each `next_addr` is **assigned from the sorted successor**, and the terminal pointer is the
**constant** `SENTINEL_MAX`. So the arity-3 leaf's third field carries **no committed datum that the
`Heap.FeltHeap` does not already determine**. The relink is a *function*, and it is invertible:
`imtChainOf_imtToHeap` proves the relink inverts the projection. Therefore the arity-3 commitment is
a **function** of the same heap the arity-2 one folds — no existential is needed, and the schema
field can be a plain function.

```lean
structure MapLeafSchema where
  HeapOk        : Heap.FeltHeap → Prop            -- narrow: Heap.SortedKeys
  heapOk_sorted : ∀ h, HeapOk h → Heap.SortedKeys h
  SizeOk        : Nat → Heap.FeltHeap → Prop      -- narrow: fun d h => h.length = 2 ^ d
  commit        : (List ℤ → ℤ) → Nat → Heap.FeltHeap → ℤ   -- narrow: mapRoot
```

All three narrow fields **are** the deployed objects, so:

* `opensToMerkleS narrowSchema … = opensToMerkle …` — **`rfl`** ✓
* `writesToMerkleS narrowSchema … = writesToMerkle …` — **`rfl`** ✓
* `MapOp.holdsAtS narrowSchema … ↔ DescriptorIR2.MapOp.holdsAt …` — proved ✓

### ⚠ The one real cost: the `rfl` cannot be re-checked at `MAP_TREE_DEPTH`

**Measured, not guessed.** The two conservativity equations are `rfl` at a *generic* depth `d`.
Stating the *same* equation with `MAP_TREE_DEPTH` substituted and closing it with a **fresh** `rfl`
**dies at the heartbeat limit** — with a concrete depth the elaborator can make progress inside
`perfectRoot hash 16 _` and starts splitting the symbolic leaf vector. This is
`MapReconcileImtRepoint` §4a's discipline (`MAP_TREE_DEPTH` is a reducible abbrev of a literal),
now shown to bite the conservativity layer too.

The fix is to **transport** the generic `rfl` by rewriting rather than re-deriving it —
`narrow_holdsAtS_is_instance` is two lines:

```lean
unfold MapOp.holdsAtS DescriptorIR2.MapOp.holdsAt DescriptorIR2.opensTo DescriptorIR2.writesTo
cases m.op <;> simp only [opensToMerkleS_narrow, writesToMerkleS_narrow]
```

**Pricing transport vs `rfl`, honestly.** The brief's worry is that transport turns a mechanical
port into a rewrite, because every downstream `Iff.rfl` needs the transport threaded. Measured
against this tree, that worry does **not** materialise, for a specific structural reason:

* The `rfl`s that matter — the two at generic depth — **survive as genuine kernel certificates**.
  Nothing is weakened; the kernel still certifies that the generalisation changed no meaning.
* Downstream sites do **not** pay the transport, because they never punch through
  `MapOp.holdsAt` to the opening. The transport is paid **once**, in the bridging keystone.
* The tree contains exactly **one** existing `Iff.rfl` that does punch through
  (`MapOpWideKeyGate.narrow_holdsAt_is_instance:625`) and **two** `unfold` sites
  (`DecideMapMerkle:153,210`). Those three are the entire transport bill.

So the answer to question 2 is: **there is an `rfl`-preserving move, it is landed, and the transport
caveat costs three sites, not a rewrite.** What does *not* survive is the wide-key epoch's
particular luck of "all six conservativity `rfl`s untouched" — here one of the six-equivalents
(`narrow_holdsAt_is_instance`) becomes a *false statement* at cutover and must be restated. That is
a restatement, not a re-proof: its content moves to `holdsAtS narrowSchema`, where it is still `rfl`.

---

## 3. ⚑ THE SIXTH OBSTRUCTION — arity is not the only shape gap, and it is not the biggest

The brief asked me to hunt early for a sixth impossibility. I found one, and it changes the scoping.
It is not an impossibility of *this* design — the design absorbs it — but it **refutes the premise
that moving the leaf arity is sufficient**.

`opensToMerkle` demands `Heap.SortedKeys h ∧ h.length = 2 ^ d`: a **dense** vector of `2^16`
**strictly increasing** keys. The deployed tree holds `n ≪ 2^16` real leaves and pads every position
`≥ n` with the literal constant `BabyBear::ZERO`:

> `heap_root.rs:72` — *"`EMPTY_SUBTREE_ROOTS[0]` is the empty-leaf digest (`BabyBear::ZERO`, the
> padding marker `CanonicalHeapTree::new` uses)"*

`BabyBear::ZERO` is not the `leafOf` image of any entry, nor the `imtLeafHash` image of any leaf —
it is not a hash output at all. And a dense sorted heap would need 65 536 distinct increasing
addresses, which the prover does not have. **So the deployed prover fails the denotation's `∃ h` for
a second, entirely independent reason, and moving the leaf arity does not touch it.**

Consequences, stated plainly:

* The refutation's verdict is **correct but under-scoped**. Closing arity alone leaves
  `AlgoStarkSound` still vacuous on every real turn.
* `MapReconcileImtRepoint`'s named residual #1 ("the unpadded commitment form") is not a polish item.
  It is a **co-equal prerequisite**, and it is arguably the larger one, because the arity gap has a
  function-shaped fix while density changes the *quantifier's domain*.
* The §4 payoff exhibit in the landed module is honest but synthetic: `depSpine` genuinely has `2^16`
  distinct sorted addresses. It demonstrates the denotation is *inhabitable* at the deployed leaf
  shape. It is not yet a statement about a tree `heap_root.rs` would produce.

**Why the design survives it.** Because `commit` and `SizeOk` are free fields, the sparse/padded
tree is simply a **third instance** of the same structure — a `commit` that folds a prefix against
the constant-zero padding, and a `SizeOk` reading `h.length ≤ 2 ^ d`. No structural change is
needed. `SizeOk` was added to the landed schema for exactly this reason (both current instances
still read `h.length = 2 ^ d`, so every `rfl` survives).

---

## 4. ATOMIC OR STAGED — **staged, in three; only stage 3 is atomic, and it is small**

The two shapes are incomparable (`imtLeafHash_ne_heapLeafOf`; `models_are_incomparable`), so there
is no period in which both denotations hold. But that argues only that the *rebinding* is atomic —
not that the whole programme is.

| Stage | Content | Atomic? | Size |
|---|---|---|---|
| **1 — landed** | `MapLeafSchema` + `narrowSchema` + `imtSchema` + conservativity + the relink weld + the payoff exhibit | no — purely additive | 1 file, 21 decls, **19 s** to elaborate |
| **2** | arity-3 gate laws for the four kinds `MapAbsentImtGate` did not cover (`.read`, `.write`, `.insert`, `.aafiInsert`); an `ImtReconcileFamily` twin of `MapReconcileFamily`; the arm `mapOpsArmImt_of_modeler` extended off `.absent` | no — additive alongside the existing model | the bulk of the labour; 4 opener laws + 1 arm |
| **2b** | the **density/padding** instance of §3 | no — additive | co-equal prerequisite, unscoped |
| **3** | rebind `MapOp.holdsAt`'s body (1 line) + re-point the 6 producers of §1(c) + repair the 3 punch-through sites | **yes, atomic** | 1 def body, 6 producer theorems, 3 consumer sites |

**Size of the atomic commit:** ~10 declarations across ~5 files, plus whatever the full-tree build
surfaces in the (b) category — which should be nothing, since (b) is `Prop`-opaque, but per the
project's own "per-file green hides a red umbrella" lesson, must be checked with a whole-tree
`lake build`, not per-file.

Stage 2 is where the real work is and it is **not** blocked by anything: the four missing arity-3
opener laws are the same shape as `MapAbsentImtGate`'s `.absent` one, which exists and is proved.

---

## 5. THE ORPHAN QUESTION — a separate prerequisite, and it is **cheap**

**Both claims verified.**

* 6 of the 9 STARK-apex modules are allowlisted orphans: `AcceptanceDischarge`,
  `AlgoStarkSoundKernel`, `AlgoStarkSoundKernelAvail`, `AlgoStarkSoundFanoutMemory`,
  `AlgoStarkSoundFanoutMemFree`, `AlgoStarkSoundFanoutSetField` —
  `scripts/lean-orphans-allow.txt:77–82`. Only `AlgoStarkSound{General,Instance,TransferV3}` are in
  CI's closure. `scripts/check-lean-orphans.sh` states the consequence itself: *"An allowlisted
  module's own checks still do not run in CI."* They are **not** in the checker's
  `STALE (now-reachable)` list, so they are still genuinely unreachable.
* So the apex has indeed been both vacuous on the ordinary path **and** outside the build.

**Correction to the record:** `MapReconcileImtRepoint`'s header says `AlgoStarkSoundFanoutMemory` is
RED (`noteSpendV3_shape`, maximum recursion depth). **That is now stale** — it was fixed earlier the
same day with a `set_option maxRecDepth 8192`, and I measured all nine apex modules **GREEN** in
this tree.

**Does the denotation move land them?** **No.** Rooting is orthogonal and is a strict prerequisite:
until they are in CI, stage 3's repairs to them are not build-checked, and the project's own
"SWEPT ≠ VERIFIED" lesson applies directly.

**The measured price of rooting — and it is not a decision.** Full elaboration of each orphan,
imports warm, `LEAN_NUM_THREADS=3`, this box:

| module | elaboration |
|---|---|
| `AcceptanceDischarge` | 24 s |
| `AlgoStarkSoundKernel` | 26 s |
| `AlgoStarkSoundKernelAvail` | 21 s |
| `AlgoStarkSoundFanoutMemory` | 26 s |
| `AlgoStarkSoundFanoutMemFree` | 29 s |
| `AlgoStarkSoundFanoutSetField` | 30 s |
| **total** | **≈ 156 s** |

For contrast the sibling's PQ-stack figure was ~48 min, and `VerifyCoreEqSpecW` alone clocked
2901 s cold. **Rooting the apex costs about two and a half minutes.** It is not a decision with a
price; it is an oversight to correct. Recommend doing it **before** stage 2, not after.

---

## 6. THE PAYOFF, honestly

**Today.** `AlgoStarkSound`'s conclusion is `Satisfied2`, whose `.mapOp` arm is `MapOp.holdsAt`,
which is *refutable* at the deployed commitment. A conclusion that is false at the object the system
actually commits is not a weak guarantee — it is no guarantee. The apex says **nothing about any
real turn**. (And on the ordinary path — a fresh nullifier or cell-id above the committed maximum —
it is refuted by two independent mechanisms, per `topGap_old_model_false` and
`topGap_old_model_false_bracket`.)

**After stage 1 (landed).** There now **exists** a map-op denotation inhabited at the deployed leaf
shape: `topGap_holdsAtS_holds_where_holdsAt_is_refuted` proves, on the very deployed-depth top-gap
row where `MapOp.holdsAt` is refuted, that `MapOp.holdsAtS (imtSchema _)` **holds**. That is the
precise increment: the target of the move is proved non-empty before the move is attempted. Nothing
downstream consumes it yet.

**After stage 3 (+2b).** `AlgoStarkSound` would say: *for every accepting batch, on every fired
declared map-op row, the row's `(root, key, value, new_root)` columns are a genuine opening of the
indexed-Merkle tree the deployed prover commits* — i.e. a `.absent` row forces the key off the whole
committed address spine, a `.write` row forces the post-root to be the true update. That is a
statement about a real turn.

**Floors that remain — none of them discharged by this work.**

1. **The hash floor.** `Poseidon2SpongeCR` is **refuted** at deployed parameters, so stage-2/3 work
   must be authored in the `_or_collides` + total-extractor idiom of commit `3245e88148`. Anything
   stated under `Poseidon2SpongeCR` is priced at nothing. The landed module assumes **no** hash
   property at all (`imtSchema` is a fold; no injectivity is used).
2. **`ImtSorted` stays a HYPOTHESIS, and must not be promoted.** The chain invariant rides in the
   knowledge-extraction slot that `ReconcileGatesAt`'s own `∃ h, Heap.SortedKeys h` already
   occupies — same species, no new floor. Its cross-turn induction (that the prover's chain *stays*
   sorted across turns) is **not** proved here and **must not be re-labelled a floor**: a floor is a
   named cryptographic assumption; this is an unproved invariant of the deployed prover, and calling
   it a floor would launder it. In the landed module `imtSchema_chain_imtSorted` derives the chain
   invariant *from the schema's `HeapOk` field* on a single commitment — which is per-commitment,
   not cross-turn.
3. **The witness-generation perimeter.** A STARK proves the trace, not the witness generator. Under
   `air_accepts ⇔ spec` the proven set is empty; the roots are trusted Rust. Orthogonal to all of
   this and untouched.
4. **The FRI/STARK floor** underneath `AcceptsFull` — unchanged.
5. **Density/padding** (§3) — an open shape gap, not a floor, and a prerequisite.

---

## 7. HONEST UNKNOWNS, and what would settle each

| # | Unknown | What settles it |
|---|---|---|
| 1 | Do the four missing arity-3 opener laws (`.read`/`.write`/`.insert`/`.aafiInsert`) go through as smoothly as `.absent` did? The `.write`/`.insert` kinds must move a root, so they need `pathRecompute_binds_updates` at the arity-3 leaf — which exists post-cutover but was proved for the arity-2 leaf. | Attempt `.read` first (the easiest: one membership path, root preserved). If it lands in a day, stage 2 is a week; if the update law does not transfer, stage 2 is the whole programme. |
| 2 | Does the **padded** `commit` admit a `SizeOk`/`HeapOk` pair that still leaves the two narrow `rfl`s intact? I argued yes structurally but did not build it. | Land the padded instance and re-run the two conservativity `rfl`s. Half a day. |
| 3 | ~~Is the category-(b) claim — that `MemoryLegs` and the 8 fan-outs are truly `Prop`-opaque and re-elaborate for free — true against the *kernel*?~~ **SETTLED — the falsifier RAN; see §10.** (b) IS free: 522 of the 536 downstream modules are indifferent. But the transport bill is **20 sites across 10 modules**, not 3, and the whole-tree `lake build` the falsifier called for would have MISSED the tier it was aimed at. | — |
| 4 | ~~Does the AIR enforce the relink?~~ **SETTLED this session — see below.** | — |
| 5 | Whether rooting the 6 orphans surfaces failures that the allowlist has been hiding — they are green *in isolation*, which is not the same as green under CI's flags/targets. | Root them and run CI once. ~156 s of elaboration plus one CI cycle. |

### Unknown #4, settled: the AIR binds the pointer but does not gate the LINKAGE

Read this session in `circuit/src/descriptor_ir2.rs`. `MAP_NEXT` (col 21) is a witness column that
is **bound inside the arity-3 committed digest** — `map_leaf_input_cols` puts it in the leaf absorb
(`:2202`), and the low-leaf digest for the `.absent` bracket absorbs
`[MAP_LOW_ADDR, MAP_LOW_VALUE, MAP_NEXT]` (`:3353`). The deployment even carries an adversarial
test that widening `MAP_NEXT` breaks the digest (`:8133–8159`). So a prover **cannot forge the
pointer relative to the committed leaf**.

What the AIR does **not** carry is any cross-row gate forcing `MAP_NEXT` to equal the successor
leaf's `MAP_KEY`. The linkage is established by the *builder* (`heap_root.rs::relink_next_addrs`),
and a builder is not a constraint.

This is the right answer for the design rather than a new wound: it is precisely why `ImtSorted`
**must** ride in the knowledge-extraction slot as a hypothesis, and why promoting it to a floor
would be laundering. It also means the landed `imtSchema` is faithful in the right direction — its
`commit` *derives* the pointers from the successor, so it describes exactly the chains an honest
builder produces, and a prover committing an unlinked chain simply falls outside the denotation's
`∃ h` rather than satisfying it dishonestly.

---

## 8. WHAT WAS LANDED

`metatheory/Dregg2/Circuit/MapDenotationSchema.lean` — new, additive, 21 declarations,
`lake build` exit 0 (19 s), `#assert_axioms` clean on all 11 asserted theorems, no
`sorry`/`admit`/`native_decide`, **no new floor and no floor assumed**, no deployed byte touched.

* §1 `MapLeafSchema` / `narrowSchema` / `imtChainOf` / `imtSchema`
* §2 `opensToMerkleS`, `writesToMerkleS`, `MapOp.holdsAtS`, and the three conservativity results —
  two by `rfl`, the keystone `narrow_holdsAtS_is_instance` by transport
* §3 the weld: `imtChainOf_imtToHeap` (the relink inverts the projection),
  `imtSchema_chain_imtSorted` (admissible heaps commit genuine `ImtSorted` chains),
  `imtSchema_commit_of_chain` (the new denotation and the arity-3 gate family name the same felt)
* §4 `topGap_holdsAtS_holds_where_holdsAt_is_refuted` — the payoff, at `MAP_TREE_DEPTH = 16`,
  reusing `MapReconcileImtRepoint`'s `spineC` kit so nothing is enumerated

**Not done, named:** the module is not yet registered in `metatheory/Dregg2.lean` (a one-line
`import Dregg2.Circuit.MapDenotationSchema`), because a sibling lane was mid-rooting that file this
session. Until that line lands, this module is itself an orphan and its `#assert_axioms` do not run
in CI — the same disease §5 documents. **That import is the first follow-up action.**

## 9. THE NEXT LANE

In order:

1. **Root the 6 apex orphans** (~156 s; §5) and register `MapDenotationSchema`. Cheap, unblocks
   everything, and makes stage 2/3 repairs build-checked.
2. ~~**Run unknown #3's falsifier**~~ — **DONE, §10.** (b) confirmed free; §1(c)'s tail repriced ~7×.
   Its verdict re-orders what follows: restate the per-effect teeth over `MapOp.holdsAtS S`
   **additively during stage 2**, or stage 3 stops being small.
3. **Stage 2**: `.read` opener at the arity-3 leaf first, as the difficulty probe.
4. **Stage 2b**: the padded/sparse instance (§3) — do not defer it; without it stage 3 buys nothing
   on a real turn.

---

## 10. MEASURED — unknown #3's falsifier RAN. §1(b) is CONFIRMED FREE; the transport bill is 20 sites, not 3

**Date:** 2026-07-25, same day. **Isolation:** an APFS `clonefile` copy of `metatheory/` — sources *and*
the 4.6 GB warm `.lake` — into a scratch dir. The shared checkout was never mutated, which mattered:
~10 lanes were live in it, and `DescriptorIR2.lean` is upstream of **536** modules.

### 10.1 The falsifier AS WRITTEN would have printed a FALSE GREEN

"Rebind to `True` and run a whole-tree `lake build`" does not work as written. Two reasons, both found
on contact:

1. **`lake build` does not reach the tier under test.** Its default targets are the import closures of
   `Dregg2`/`Metatheory`/`Polis`/`Market`/`Bfv`. Of the modules §1(b) names as the free tier, **six sit
   outside that closure as allowlisted orphans** — `AlgoStarkSoundFanoutMemory` (which holds
   `algoStarkSound_of_mapShape` *and* the 8 per-effect fan-outs), `AlgoStarkSoundFanoutMemFree`,
   `AlgoStarkSoundFanoutSetField`, `AlgoStarkSoundKernel`, `AlgoStarkSoundKernelAvail` (the `Rfix`
   route), `AcceptanceDischarge` — as does `MapDenotationSchema` itself (§8's unlanded import). §5 and
   §7-#3 were written independently; this is where they collide.
2. **`lake build` cascades and would have suppressed the evidence.** `MapOpsColumnLayout` is a §1(c)
   producer, so it is *expected* to break — and it is upstream of the apex modules, so under
   `lake build` its failure stops theirs from being built at all.

**The instrument actually used.** Rebuild **only** `DescriptorIR2.olean` with the rebound body into a
cloned build-lib dir, then elaborate every downstream module **independently** (`lean <file>` with
`LEAN_PATH` pointed at the rebound dir). No cascade, complete coverage, and the only difference from
baseline is one definition body. Verified by a positive control both ways: `MapOp.holdsAt ↔ True` is
**not** `Iff.rfl` against the baseline olean and **is** `Iff.rfl` against the rebound one, so every green
below is a green *under the rebinding*.

**Probe set = the complete reverse-import cone of `Dregg2.Circuit.DescriptorIR2`: 536 modules** (460 in
the root closure, 76 orphan-side) — every module in the tree that can see the definition.

**Hardened against `True`'s one false-negative mode.** `True` cannot catch a producer whose goal is
closable by `trivial`/`simp`. So the 24 named/apex modules were probed a **second** time with the body
rebound to `False`, under which every producer must break and every consumer is only strengthened.
**The `True` and `False` break sets are identical, module for module** — nothing was accidentally green.

### 10.2 The result

| | count |
|---|---|
| modules probed under the rebinding | **536** |
| green under the rebinding | **522** |
| red under the rebinding | 14 |
| — FOREIGN (red in baseline too) | 4 |
| — **GENUINE** (baseline green, rebound red) | **10 modules / 20 punch-through sites / 40 asserted theorems** |

The four foreign reds were separated by re-running each module against the unmodified
`DescriptorIR2.olean`, and all four are **byte-identical** between the two passes: the `Dregg2` root
module trips `FloorRatchet`'s gate ("1559 NEW declaration(s) take a REFUTED floor" — 115 552 bytes of
output, identical), `Emit.MerkleMembershipRung2` and `FriPositiveRadiusSchedule` are RED-AT-HEAD in this
dirty tree, and `Dregg2.Claims` only reports the missing `Dregg2.olean` its own root failure implies.
None of them is a finding of this experiment.

### 10.3 §1(b) IS FREE — and the green is meaningful, not vacuous

Every module §1(b) names re-elaborated **green** under both rebindings: `AlgoStarkSoundGeneral`
(`MemoryLegs`:223) · `AlgoStarkSoundFanoutMemory` (`MapReconcileFamily`, `memoryLegs_of_mapShape`,
`algoStarkSound_of_mapShape`, **all 8 per-effect fan-outs**) · `AlgoStarkSoundFanoutMemFree` ·
`AlgoStarkSoundFanoutSetField` · `AlgoStarkSoundKernel` · `AlgoStarkSoundKernelAvail` (the `Rfix`
route) · `AcceptanceDischarge` · `FriVerifierBridge` (`AlgoStarkSound`, the class) ·
`AlgoStarkSoundInstance` · `AlgoStarkSoundTransferV3` · `DecideSatisfied2` · `DecideSatisfied2Golden` ·
`Satisfied2Faithful` · `CustomApex` · `CustomCarrierAttack`.

The green is *meaningful* rather than an artefact of not touching the arm:
`AlgoStarkSoundFanoutMemory.lean:240` discharges the `.mapOp` arm by
`exact mapOpsArm_of_modeler hash hCRh d (tr pi π) (hrec pi π hacc) i hi m hc` — a bare lemma application
whose statement the rebinding does not change. **`Satisfied2` needs no schema parameter and the apex is
not a rewrite.** That is the load-bearing half of §1, and it now has a machine check behind it instead of
a grep.

Also measured, and it cuts the *other* way from §1(c): of the six named producers, only **one** —
`mapOp_holds_of_mapReconcile`:900 — is definitionally coupled to the denotation. `ReconcileGatesAt`:807
and `reconcileGates_force_opening`:847 restate the per-kind match over `opensToMerkle`/`writesToMerkle`
directly and are indifferent to the rebinding; `MapReconcileFamily` and `memoryLegs_of_mapShape` are in
the green apex module. Their cost is real but it is **stage 2's gate-model cost**, which this experiment
does not measure at all.

### 10.4 What the grep MISSED — a FOURTH punch-through idiom, and it is the dominant one

§1 counted punch-throughs by grepping `unfold MapOp.holdsAt` (2 hits) and `Iff.rfl` (1 hit). That method
is structurally blind to the idiom that actually dominates: **applying the hypothesis to a proof of the
guard.** The body is `guard = 1 → match m.op with …`, so `hfresh hspend` / `hc hfire` / `hh hguard` /
`intro hg` all read *through* the definition without ever naming it. **15 of the 20 break sites are this
idiom.**

**Every genuine break, classified:**

| file:line | declaration | idiom | §1's tier |
|---|---|---|---|
| `DecideMapMerkle.lean:154` | `mapDecMerkle_sound` | `unfold MapOp.holdsAt` | predicted |
| `DecideMapMerkle.lean:211` | `mapDecMerkle_complete` | `unfold … at hhold` + guard application | predicted |
| `MapOpWideKeyGate.lean:630` | `narrow_holdsAt_is_instance` | `Iff.rfl` — §1's named casualty | predicted |
| `MapOpsColumnLayout.lean:904` | `mapOp_holds_of_mapReconcile` | producer: `intro` on the guard arrow | predicted |
| `MapDenotationSchema.lean:218` | `narrow_holdsAtS_is_instance` | `unfold … MapOp.holdsAt … opensTo … writesTo` | §2's transport |
| `MapReconcileImtRepoint.lean:196` | `mapOpHoldsAt_unsat_at_imtRoot` | **guard application** | **NOT in §1** |
| `Emit/RotWideCompactS2.lean:670` (+`:698`) | `holdsAt_transport` (`.mapOp` case) | **`intro hg` + `simp only [MapOp.holdsAt]` + per-kind `cases`** | **NOT in §1** |
| `Metatheory/EffectVmDescriptor2PassiveOptimization.lean:290` | `holdsAt_project` (a documented copy of `holdsAt_transport`) | **same** | **NOT in §1 — a whole tier §1 never mentions** |
| `RotatedKernelRefinementExercise.lean:327` | `heapWrite_splice_forced` (**tooth: heapWriteV3**) | **guard application** + `.write`-arm content | §1(c) last row, understated |
| `Emit/EffectVmEmitV2.lean:1077` | `attenuateV2_held_determined`, `attenuateV2_non_amp` | **guard application** ×2 + `.read`-arm `.1` | idem |
| `Emit/EffectVmEmitV2.lean:1164` | `revokeV2_removes` / `_held_determined` / `_post_determined` | **guard application** ×2 | idem |
| `Emit/EffectVmEmitRotationV3.lean:2466` | `noteSpendV3_grow_gate_forces_set_insert` (**noteSpendV3**) | **guard application** ×2 | idem |
| `…:2488` | `noteSpendV3_opens_delegation_ancestor` | **guard application** | idem |
| `…:2681` | `noteCreateV3_grow_gate_forces_set_insert` (**noteCreateV3**) | **guard application** | idem |
| `…:2780` | `revokeV3_grow_gate_forces_set_insert` | **guard application** ×2 | idem |
| `…:2973` | `createCellV3_grow_gate_forces_set_insert` (**createCellV3**) | **guard application** ×2 | idem |
| `…:2993` | `factoryV3_grow_gate_forces_set_insert` (**factoryV3**) | **guard application** ×2 | idem |
| `…:3013` | `spawnV3_grow_gate_forces_set_insert` (**spawnV3**) | **guard application** ×2 | idem |
| `…:3035` | `spawnWriteV3_grow_gate_forces_set_insert` (**spawnWriteV3**) | **guard application** ×2 | idem |
| `…:4971` | `refusalFieldsWriteV3_forces_write` (**refusalFieldsWriteV3**) | **guard application** | idem |

**The symmetry is exact and it is the headline.** §1(b) lists the 8 per-effect fan-outs —
noteSpendV3, noteCreateV3, createCellV3, factoryV3, spawnV3, spawnWriteV3, refusalFieldsWriteV3,
heapWriteV3 — as free. They *are* free **at the apex**. **All eight break at the tooth.** The doc priced
the fan-out and did not notice that each fan-out has a same-named tooth reaching into the row denotation.

### 10.5 VERDICT — (b) CONFIRMED; §1(c)'s tail REPRICED ~7×

* **Confirmed, and it is the important half.** `VmConstraint2.holdsAt`, `Satisfied2`,
  `Satisfied2Public/U/Custom`, `MemoryLegs`, `algoStarkSound_of_mapShape` and its 8 fan-outs, the `Rfix`
  route and the `AlgoStarkSound` class are genuinely `Prop`-opaque. **522 of 536** downstream modules do
  not care. Stage 3 does **not** touch the apex, and `Satisfied2` needs no new parameter. §1's single most
  important structural fact is true.
* **Repriced.** §1's "the tree contains exactly one `Iff.rfl` … and two `unfold` sites. Those three are
  the entire transport bill" is wrong by ~7×: it is **20 sites across 10 modules**, with **40 asserted
  theorems** (`#assert_axioms` targets) sitting on them. The extra sites are concentrated in the
  **per-effect teeth**, which §1's last table row dismissed with "they re-elaborate unless they open the
  opening." **Measured: every one of them opens it.**
* **And they are RESTATEMENTS, not re-proofs.** Their conclusions name `DescriptorIR2.opensTo` /
  `writesTo` *directly*, so after the cutover they are claims about the arity-2 commitment the deployed
  prover does not build — the same species of casualty as `narrow_holdsAt_is_instance`, which §1 called
  the *single* one of its kind. There are at least **fourteen**, and they are exactly the theorems cited
  as "the deployed descriptor FORCES the nullifier insert / the commitment insert / the refusal audit
  write."
* **The refutation module is itself a cutover casualty, and §1 does not list it.**
  `mapOpHoldsAt_unsat_at_imtRoot`, `topGap_mapOpHoldsAt_false` and `topGap_apex_premise_repointed` break
  — as they must, since the cutover is precisely what makes `¬ MapOp.holdsAt` false at the deployed
  pre-root. That is the intended outcome, but it is three more asserted theorems to retire in the same
  atomic commit, not zero.
* **The probe is a LOWER BOUND on the cutover bill.** It measures *definitional* dependence on
  `MapOp.holdsAt`. Declarations that name `opensTo`/`writesTo` without going through `holdsAt` stay green
  and still need moving — notably the seven `*TraceReadout` witness-decode structures carrying arity-2
  `writesTo`/`opensTo` **fields** (`NoteSpendTraceReadout.growthDecodes`:449,
  `NoteCreateTraceReadout`:523, `CreateCellTraceReadout`:549, `CreateFromFactoryTraceReadout`:625,
  `SpawnTraceReadout`:696, `RefusalTraceReadout`:993, and `HeapWriteTraceReadout` in
  `RotatedKernelRefinementExercise`), together with their `*_forced_sat` users, which apply the field to
  a broken-but-unchanged-in-statement tooth and therefore stay green under a per-module probe.
  Comment-stripped, **48 code mentions of `opensTo`/`writesTo` across 9 files** is the true
  statement-level surface.
* **Effect on §4's staging table.** Stage 3's "1 def body, 6 producer theorems, 3 consumer sites, ~10
  declarations across ~5 files" becomes **1 def body, 1 definitionally-coupled producer, 20 consumer
  sites across 10 files, ~40 asserted theorems**. Still atomic, still tractable — but not "small". **The
  fix is to move the per-effect teeth out of stage 3:** restate them over the schema-parametric
  `MapOp.holdsAtS S` *additively, during stage 2*, so stage 3 rebinds one body and only the producer plus
  the four bridge/decision/transport sites move with it. Do that and §4's "the atomic commit is small"
  becomes true again instead of aspirational.

### 10.6 BONUS, measured: the DENSITY surface is NOT an opacity surface at all

The same trick was pointed at §3's density obstruction: relax `opensToMerkle`/`writesToMerkle`'s
`h.length = 2 ^ d` to `h.length ≤ 2 ^ d` — exactly the `SizeOk` generalisation §3 proposes for the padded
instance — and re-elaborate. **It does not survive its own defining module:**

```
MapMerkleRoot.lean:238:52  Application type mismatch: hl₁ : List.length m₁ ≤ 2 ^ d
                           but is expected to have type  List.length m₁ = 2 ^ d
                           in the application  mapRoot_injective hash hCR d hl₁
MapMerkleRoot.lean:255:52  (idem)
⇒ opensToMerkle_functional, opensToMerkle_some_excludes_none, writesToMerkle_functional  ALL RED
```

So the density equation is nowhere carried opaquely — it is **the hypothesis of `mapRoot_injective`**,
hence proof content in the three FUNCTIONAL / anti-ghost teeth, plus their `DescriptorIR2` re-exports
(`opensTo_functional`:546, `opensTo_some_excludes_none`:553, `writesTo_functional`:560) and the
completeness producer `opensTo_none_of_gap`:568.

**This corrects §3's "why the design survives it."** It is true that `SizeOk` lets the padded tree be a
third *instance* with no structural change. It is **not** true that the instance arrives free: at a
relaxed `SizeOk` the openings are **no longer functional**, and functionality is the entire anti-ghost
argument (root + key determine the value; the `new_root` column cannot be forged) — the property
`refusalFieldsWriteV3_forces_write`'s own docstring leans on by name. The landed `MapDenotationSchema`
carries **no** schema-level functional theorem at all. So stage 2b must supply injectivity at the padded
commitment before any tooth can be stated there, and `perfectRoot_injective` is stated for equal-length
dense vectors. **Stage 2b is strictly larger than §7-#2's "half a day," and §3 is right to call it
co-equal.**

### 10.7 Method note

Both rebindings and the density relaxation were built into throwaway olean dirs and discarded;
**nothing from this experiment is landed** and `DescriptorIR2.lean` / `MapMerkleRoot.lean` are
byte-identical to before. The `axiom-hygiene FAIL` lines in the rebound passes are *consequences* of the
broken proofs above (a failed proof leaves `sorryAx`), not independent findings; they were excluded when
diffing failure sets, and are what the 40-theorem blast radius is counted from.

Unknown #3 is **SETTLED**: (b) free and confirmed against the kernel; (c)'s tail ~7× the estimate and
concentrated in the per-effect teeth plus a descriptor-optimizer transport tier the doc never named; and
the falsifier had to be run per-module rather than as one `lake build`, because six of the modules it was
aimed at are in no build target at all.
