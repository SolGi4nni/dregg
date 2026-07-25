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
| 3 | Is the category-(b) claim — that `MemoryLegs` and the 8 fan-outs are truly `Prop`-opaque and re-elaborate for free — true against the *kernel*, or does some proof accidentally rely on the arity-2 body? | The falsifier is cheap and decisive: temporarily rebind `MapOp.holdsAt` to `True` and run a whole-tree `lake build`. Every site that breaks is a site that was *not* opaque. This costs one build and would have caught a wrong scoping estimate before commit 40. **Recommend doing this before stage 2.** |
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
2. **Run unknown #3's falsifier** (rebind `MapOp.holdsAt` to `True`, whole-tree build). One build;
   it either confirms the (b) category is free or reprices the whole programme. Do this *before*
   committing to stage 2.
3. **Stage 2**: `.read` opener at the arity-3 leaf first, as the difficulty probe.
4. **Stage 2b**: the padded/sparse instance (§3) — do not defer it; without it stage 3 buys nothing
   on a real turn.
