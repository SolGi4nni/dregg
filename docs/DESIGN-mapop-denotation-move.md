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
| 2 | ~~Does the **padded** `commit` admit a `SizeOk`/`HeapOk` pair that still leaves the two narrow `rfl`s intact? Half a day.~~ **SETTLED — see §11. The `SizeOk`/`HeapOk` pair is free, the two `rfl`s are untouched (nothing landed touches `MapDenotationSchema`), and conservativity is stronger than hoped: the padded `commit` is *equal* to the dense one on a full tree. But the framing of the question was wrong, and "half a day" was wrong for the right reason: what the padded instance lacks is not a `SizeOk` but INJECTIVITY, and padded injectivity is REFUTED — at a hash that IS injective.** | — |
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
| `metatheory/Dregg2/Metatheory/EffectVmDescriptor2PassiveOptimization.lean:225` | `holdsAt_project` (a documented copy of `holdsAt_transport`) | **same** | **NOT in §1 — a whole tier §1 never mentions** |
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

---

## 11. ⚑⚑ STAGE 2b IS LANDED — and the obvious route was REFUTED, not merely unproved

**Date:** 2026-07-25, same day. **Module:** `metatheory/Dregg2/Circuit/MapPaddedDenotation.lean` (NEW,
additive, rooted in `metatheory/Dregg2.lean` on the line after `MapDenotationSchema`). `lake build`
exit 0 at 24 s; 36 `#assert_axioms` all clean (⊆ propext/Classical.choice/Quot.sound); no
`sorry`/`admit`/`native_decide`; **no new floor and `Poseidon2SpongeCR` appears in no type in the
file.** No landed file was edited — `MapDenotationSchema.lean`'s two conservativity `rfl`s and its
eleven asserts are byte-identical, so §2's kernel certificates are untouched by construction.

### 11.1 The work order's option (a) is REFUTED — and CR does not save it

§10.6 measured *that* the three functional teeth die at a relaxed `SizeOk`. This settles *why*, and
the reason forecloses the fix the falsifier proposed:

> `heap_root.rs` pads with the **literal** `BabyBear::ZERO` (`EMPTY_SUBTREE_ROOTS[0]`,
> `heap_root.rs:72–87`; real leaves are a contiguous sorted prefix, `CanonicalHeapTree::new:213–262`).
> **If a live leaf digest equals the padding constant, its entry becomes invisible.** `h ++ [e]` with
> `leafOf hash e = 0` pads to the *same* digest vector as `h`, hence to the same root — while
> `Heap.get` disagrees at `e.1`: one heap PRESENTS the key, the other reports it ABSENT. That is
> exactly what `opensToMerkle_some_excludes_none` forbids.

And the event is **orthogonal to the hash floor.** `Poseidon2SpongeCR hash` is
`∀ xs ys, hash xs = hash ys → xs = ys`; it says nothing about whether the padding constant lies in the
leaf-digest image. Machine-checked, at a hash that satisfies exactly that injectivity:

* `padded_ghost2` / `padded_ghost3` — two distinct sorted heaps of admissible sparse occupancy with
  **equal padded roots** and a **some/none split at the same key**, at every depth, at the arity-2
  fold and at the deployed arity-3 relinked fold.
* `padded_injectivity_is_refuted` / `padded_imt_injectivity_is_refuted` — the negations, the second at
  `MAP_TREE_DEPTH = 16` and the deployed leaf. (Both are anti-floor content: conclusion `False`.)

So **the seventh obvious approach was also impossible**, and stating the result "at `refSponge`" would
not have removed the ghost — that is the whole content of the refutation. The witness hash is
`ghostSpongeAt pre := fun xs => refSponge xs - refSponge pre`: injective because subtracting a constant
is a bijection of ℤ, and `ghostSpongeAt pre pre = 0`. It models the one fact about the deployed hash
that matters — a hash whose range covers BabyBear certainly has a preimage of `0`, and the deployed
builder never checks that no live leaf hits it.

**Priced at deployed parameters, this is a single-target preimage, not a birthday event.** An adversary
needs one `(addr, value, next)` with `hash[addr, value, next] = 0`. At the **1-felt** scalar commitment
this denotation layer uses (`MapLeafSchema.commit : … → ℤ`, BabyBear `p ≈ 2^31`) that is ~2^31 hash
evaluations with `next = SENTINEL_MAX` fixed and `value` free — **feasible on a laptop**, and the same
species as the felt-width finding. At the deployed 8-felt tree (`HEAP_ZERO8`, `CanonicalHeapTree8`) the
same event costs ~2^124.

### 11.2 What was landed instead: (c), the `_or_collides` idiom applied to the PADDING event

Option (b) — the functional theorems as schema hypotheses — was rejected: it pushes the obligation onto
the one instance that cannot discharge it. What is landed binds the padded root **unconditionally** and
names the residual:

* `padImtRoot_binds_or_ghost_or_collides` (and its arity-2 twin) — **no hypothesis on `hash` at all**,
  at neither the node nor the leaf. Residuals: `PadGhost3` (*the actual committed digest vector
  contains the padding constant* — a bounded, decidable property of committed data, deliberately NOT
  `∃ e, leafOf hash e = 0`, which pigeonhole makes unconditionally true and which would carry no more
  content than `True`) and `SpongeColl hash (…Find …)` at the pair a **total extractor** returns.
* The 1-felt scalar layer's whole binding spine had to be cured to get there, and that is a bonus
  deliverable: `mapNode_binds_or_collides`, `foldLevel_binds_or_collides`,
  `perfectRoot_binds_or_collides`, `mapRoot_binds_or_collides` — floor-free replacements for
  `MapMerkleRoot`'s `*_injective` chain, mechanically mirroring the 8-felt §5b tower that already
  existed. **`mapRoot_injective`'s refuted floor is now optional at the dense instance too.**
* `perfectRoot_all_padding` welds the model to `heap_root.rs`'s precomputed `EMPTY_SUBTREE_ROOTS`
  (`e 0 = ZERO`, `e (k+1) = heap_node(e k, e k)`), which is what makes "dense fold of a zero-padded
  vector" a faithful model of the deployed **sparse** fold.

### 11.3 The schema-level teeth the landed schema had nothing of

`MapLeafTeeth S` is a bundle an instance must EARN, and it is deliberately not a bag of hypotheses:
besides `binds` it carries **two anti-laundering fields** — `resid_refuted` (the residual VANISHES at a
hash-level `Good` predicate) and `good_inhabited` (`Good` is non-empty, so `resid_refuted` is not
discharged by an empty premise). Together these make `Resid := True` and `Resid := (h₁ ≠ h₂)`
unbuildable. The three anti-ghost theorems are proved ONCE over the bundle:

| tooth | schema-level statement |
|---|---|
| `opensToMerkleS_functional_or_resid` / `…_of_good` | root + key determine the read |
| `opensToMerkleS_some_excludes_none_or_resid` / `…_of_good` | presence excludes claimed absence |
| `writesToMerkleS_functional_or_resid` / `…_of_good` | root + key + value determine `new_root` |

Per §5b.E's discipline the `_or_resid` forms take the two witness heaps **explicitly** — the extractor's
output is a function of the witnesses, so `… ∨ ∃ residual` would be the free pass the idiom exists to
avoid. The `_of_good` forms are the existential-level statements over `opensToMerkleS`/`writesToMerkleS`,
i.e. exactly the three theorems this doc named, now existing at schema level for the first time.

**Three instances, all inhabited** (a schema-level tooth with no inhabited instance would be the
∃-image mistake): `narrowTeeth` (dense arity-2, deployed-today), `padNarrowTeeth` (arity-2 padded), and
`padImtTeeth` (**the deployed shape: arity-3 IMT leaves over `relink_next_addrs` + zero padding**). The
padded instances' `Good` is `Function.Injective hash ∧ PadFree hash`; `good_inhabited` is witnessed by
`oddSponge xs := 2 * refSponge xs + 1`, injective and never `0`.

⚠ **`HeapOk` is NOT where pad-freeness went.** Putting it there would have been option (b) wearing a
hat — the deployed builder cannot discharge it. It rides in the CONCLUSION as a named residual.

### 11.4 Conservativity is EQUALITY, and §10.6's breakage does not recur

* `padMapRoot_dense` / `padImtRoot_dense` — on a **full** tree the padded `commit` *is* the dense one.
  The padded schema EXTENDS the landed pair rather than rivalling it. `opensToMerkle_to_padded`: every
  dense opening is a padded opening.
* `narrow_opensToMerkle_functional`, `narrow_opensToMerkle_some_excludes_none`,
  `narrow_writesToMerkle_functional` — the three dense theorems, re-derived **from** the schema-level
  teeth at `narrowTeeth`, at `MapMerkleRoot`'s own statement shape with the refuted floor spelled as
  the injectivity it definitionally is. The measured §10.6 red is gone in both directions.
* The two landed `rfl`s are untouched because nothing landed edits `MapDenotationSchema.lean`.

### 11.5 The teeth BITE, at the deployed padding constant and the deployed depth

* `bite_presents` — a **sparse** one-live-leaf tree at `MAP_TREE_DEPTH = 16` PRESENTS its key under the
  deployed padded arity-3 denotation. The dense `opensToMerkle` has no witness for such a tree at all;
  this is the first map-op opening inhabited at a tree `heap_root.rs` would actually build.
* `bite_absence_is_refused` — **the anti-ghost tooth**: that same committed root cannot be opened at
  that same key as ABSENT. `bite_write_is_functional` — the `new_root` column cannot be forged.
* `ghost_pair_is_the_named_resid` — `padded_ghost3`'s colliding pair, fed to the tooth, lands **on the
  named residual** rather than escaping unnamed. Both directions of the disjunction are live.

Nothing in §9 of the module evaluates a root: `biteRoot` is *named* as the schema's own `commit`, per
`MapReconcileImtRepoint` §4a's discipline.

### 11.6 STAGE 2b: UNBLOCKED, with one deployed-side residual named

Stage 2b's blocking question — "can a padded instance carry the anti-ghost teeth?" — is **answered
yes**, and it is landed with the teeth attached rather than assumed. Stage 3 can now cut over to a
schema that is faithful in **both** shape dimensions (arity *and* occupancy) instead of only one, which
is what §3 called co-equal and §6 said the apex needs before it says anything about a real turn.

What is **not** closed, and must not be laundered:

1. **The deployed builder does not check pad-freeness.** `PadFree` is a decidable per-commitment
   property; `heap_root.rs` never tests it (the only `assert_ne!` against `ZERO` is a test about the
   empty *root*, `heap_root.rs:1294`). **The cheap deployed fix is to pad with a DOMAIN-SEPARATED
   digest instead of a literal zero** — then padding-vs-leaf separation is the *same named CR floor*
   the tower already carries, and this residual disappears rather than being priced. Binding the live
   occupancy count into the root would also close it. Either is a small change to
   `EMPTY_SUBTREE_ROOTS[0]`'s definition plus its 8-felt twin.
2. **The 1-felt scalar denotation layer remains the wrong width.** At 1 felt the ghost costs ~2^31; the
   deployed tree is 8-felt. This is `MapMerkleRoot`'s own named residue (the §2–§5 scalar model vs the
   §5b `node8` model), and stage 3 should cut the denotation to the 8-felt objects, not the scalar ones.
3. ~~**Stage 2 proper is untouched** — `.read`/`.write`/`.insert`/`.aafiInsert` still have no arity-3
   opener law, so the modeller still cannot DERIVE `holdsAtS` for them (§7-#1).~~ **CLOSED — §12.
   Two of the four got the law the `.absent` arm has; the other two got a REFUTATION instead, and
   the reason is a deployed-AIR gap, not a proof gap.**
4. **§10.5's repricing stands.** The 20 punch-through sites / 40 asserted theorems are unaffected by
   this lane; the recommendation to restate the per-effect teeth over `MapOp.holdsAtS S` additively
   *during* stage 2 is unchanged and is now cheaper, because the teeth they lean on by name
   (functionality) exist at schema level.
5. **⚑ THE PADDING-GHOST CLASS IS A SPREAD, NOT LOCAL TO THE MAP TREE.** Read this session:
   `cap_root.rs:137–188` pads with the same literal constant (`CAP_ZERO8 = [BabyBear::ZERO; …]`,
   `EMPTY_SUBTREE_ROOTS[0]`) under the same contiguous-prefix sparse fold, and `heap_root.rs:48–51`
   states the sentinels are shared by "the sorted openable trees (heap / cap / fields)". Grepped both
   files: **there is no leaf-digest-vs-padding guard anywhere** — the only `assert_ne!(_, ZERO)` is a
   test about the *empty root* (`heap_root.rs:1294`), and the dense reference build literally
   `leaf_digests.resize(capacity, BabyBear::ZERO)` (`heap_root.rs:1554`), which is exactly the `padTo`
   the Lean models. So the same "a live leaf digest that hits the padding constant makes its entry
   invisible" argument applies verbatim to the CAP tree and the fields tree. **The domain-separated
   padding fix in item 1 should be applied to all three at once**, and until it is, every padded
   sorted-tree denotation in this family owes the same named residual.


---

## 12. ⚑⚑ STAGE 2 PROPER IS LANDED — two openers, two REFUTATIONS, and the eighth impossibility

**Date:** 2026-07-25, same day. **Module:** `metatheory/Dregg2/Circuit/MapKindImtGates.lean` (NEW,
additive, 1370 lines, rooted in `metatheory/Dregg2.lean` on the line after `MapPaddedDenotation`).
`lake build Dregg2.Circuit.MapKindImtGates` exit 0 at **155 s**; 43 `#assert_axioms` all clean
(⊆ propext/Classical.choice/Quot.sound); no `sorry`/`admit`/`native_decide`; **no new floor and
`Poseidon2SpongeCR` appears in no type in the file.** No landed file edited.

### 12.1 The work order said "ground each arm against the deployed AIR". Three of four DIVERGE.

Read this session in `circuit/src/descriptor_ir2.rs` (`Ir2Air::MapOps`, `:3232-3541`) and
`circuit/src/heap_root.rs`:

| kind | op | the DEPLOYED gates | divergence from `ReconcileGatesAt` |
|---|---|---|---|
| `.read` | 0 | old-leaf `hash[key, old_value, next]` folds PATH1 → `MAP_ROOT`; new-leaf `hash[key, value, next]` folds the **same** PATH1 → `MAP_NEW_ROOT`; `MAP_OLD_VALUE = MAP_VALUE` forced (`:3283`) | arity, and **`new_root = root` is DERIVED, never a column** — the model asserts a gate the AIR does not write |
| `.write` | 1 | the same minus `old_value = value`; `MAP_NEXT` is ONE column shared by both absorbs | arity + the shared pointer |
| `.insert` | 3 | `rw_sel = 0`, `not_insert3 = 0` (`:3277-3278`) ⇒ **no old-leaf absorb and no fold to `MAP_ROOT` at all**; the only gate is new-leaf → `MAP_NEW_ROOT` | ⚑⚑ the model demands a PRE-root opening the AIR does not carry, at a key `insert_witness` REQUIRES to be absent |
| `.aafiInsert` | 4 | low-open → root, bracket, low-update → `R1`, free slot **pinned to `ZERO8`** (`:3493-3495`) → `R1`, append → `new_root` | the Lean `AafiGatesAt` leaves `freeEmpty` FREE; the AIR pins it to the **padding constant** |

`map_leaf_input_cols(v) = [MAP_KEY, v, MAP_NEXT]` (`:2198`) is arity-3 for every kind, as the
brief said — but arity was the *smallest* of the four gaps.

### 12.2 The two openers that exist

Both are stated at `MapPaddedDenotation.padImtSchema` (arity-3 relinked leaves + zero padding, the
deployed shape in BOTH dimensions), and both come in the post-cutover idiom:

* `readImtGates_opens_or_resid` / `readImtRow_opens_of_good` — an accepting deployed read row FORCES
  `opensToMerkleS (padImtSchema sent) hash dep root key (some value)` **and** `newRoot = root`.
* `writeImtGates_writes_or_resid` / `writeImtRow_writes_of_good` — an accepting deployed write row
  FORCES `writesToMerkleS (padImtSchema sent) hash dep root key value newRoot`: the `new_root`
  column is the genuine padded commitment of `Heap.set h key value`.

**The write proof pins a deployed design decision as load-bearing.** It runs through
`imtChainOf_set` — "a positional VALUE update leaves every pointer alone" — which is available only
because the deployed old- and new-leaf absorbs read ONE `MAP_NEXT` column. `unshared_pointer_write_is_not_a_relink`
states the converse: a row free to move the pointer produces a digest vector **outside the image of
`relink_next_addrs`**, i.e. the commitment of no heap at all. The column sharing is not an
optimisation; it is what makes the write denotation derivable.

### 12.3 ⚑ `.insert` — REFUTED, and the model was already unsatisfiable

`insertImtGates_cannot_force_the_write_denotation`: there is **no** `.insert` opener law of the shape
the other arms enjoy, because op=3 constrains only the post-root. The same accepting gate data sits
beside a pre-root at which `writesToMerkleS` is FALSE — exhibited at `MAP_TREE_DEPTH = 16` by
`bite_insert_preroot_is_unforced`. What IS forced is the post side:
`insertImtRow_post_opens_of_good` (the committed post-tree opens the key to the written value).
The deployment agrees with the verdict in its own words: *"Freshness must be established separately,
e.g. by a paired `MapKind::Absent` opening against the same pre-root"* (`descriptor_ir2.rs:540-542`).

And the mirror image, which nobody had looked at: `reconcileGates_insert_forces_key_present` proves
the EXISTING arity-2 `.insert` model demands the row's key ALREADY committed, so
`reconcileGates_insert_unsat_at_fresh_key` — **on every honest deployed insert row the model's
hypothesis is FALSE**, exactly the `.absent` top-gap finding on a second arm. ⚠ The epoch's own
`.insert` non-vacuity exhibit did not catch it: `MapOpsColumnLayout.toy_insert_gates` wrote key
`20`, which `toyHeap` HOLDS (`toyGrown = Heap.set toyHeap 20 9` is an in-place update, same length).
It is now `toy_insert_op_value_update_gates` / `_fires`, with
`toy_insert_op_key_is_already_committed` as a theorem; see §13.
**The `.insert` teeth have only ever been exercised on a value update.**

### 12.4 `.aafiInsert` — the pre-side law, and ⚑⚑ THE EIGHTH IMPOSSIBILITY

`aafiImtRow_forces_absence_of_good` re-derives the double-spend tooth at the deployed padded
commitment: an accepting AAFI row forces `opensToMerkleS … oldRoot key none`. It is *cheaper* than
the `.absent` arm's law — `ImtSorted` on the pre-chain is DERIVED from the schema's own `HeapOk`
field (`imtSchema_chain_imtSorted`) rather than taken as a hypothesis.

The POST side is where the eighth impossibility lives, and it is **structural, not cryptographic**.
`heap_root.rs::insert_witness_aafi` (`:1077-1156`) appends at `next_free_index` and folds
`append_order_after` — the code calls it *"a distinct commitment lineage from the sorted-compacted
`root8` (same leaf SET, different positions)"* (`:1139-1141`). But
`MapLeafSchema.commit : (List ℤ → ℤ) → Nat → Heap.FeltHeap → ℤ` is a **function of the logical
sorted map**, and the append-order fold depends on insertion HISTORY.

> `no_schema_commits_the_append_order_layout` — for EVERY schema `S`, at every depth ≥ 1, at a hash
> that is injective AND pad-free, *"the padded fold of the physical layout equals `S.commit` of the
> logical chain"* is **FALSE**. Witness: one sorted chain and its own transposition.
> `aafi_post_is_not_the_sorted_commit` exhibits the separation concretely at the deployed arity-3
> leaf (insert `5` into `[(1,7),(9,3)]`: append order ≠ sorted order ⇒ different roots).

So the `.aafiInsert` arm of `MapOp.holdsAtS S` — which is `writesToMerkleS S`, a statement about the
logical map — **cannot** be the deployed AAFI post-condition at ANY instance of the landed schema.
The pre-side absence law is what that arm can have; the post side needs either an order-carrying
denotation (`IndexedMerkleTree.ImtVecCorr`'s `phys ~ c` shape) or a deployed change that re-sorts.
⚠ This corrects the framing under which `padImtTeeth` was called "the deployed shape": it is faithful
to `CanonicalHeapTree::new`'s sorted-prefix build (which is what the pre-root is), **not** to the
AAFI post-layout.

### 12.5 The insert/write GROWTH question, answered

The sibling's finding is confirmed *and moved*:

* `denseSchema_write_forces_key_present` — at any schema whose `SizeOk` is `h.length = 2 ^ d`, a
  `writesToMerkleS` witness must have the written key ALREADY committed (a fresh key would grow the
  heap by one). Instantiated at `narrowSchema` (`narrow_write_forces_key_present`, i.e. the deployed
  `DescriptorIR2.writesTo` today) and at `imtSchema`. So `.write`/`.insert` denote an in-place
  UPDATE at every dense instance, exactly as reported.
* `padImt_write_admits_growth` — at `padImtSchema`, `SizeOk` is `≤`, and here is a `writesToMerkleS`
  witness **at `MAP_TREE_DEPTH = 16` whose key is FRESH and whose heap gains one entry**.

**So yes: stage 2b changed what these laws can say.** Genuine fresh-key growth is representable at
the padded instance and was not at the dense one, and `bite_aafi_grows` shows the deployed AAFI row
realising it at the deployed depth (there the appended key is the new maximum, so append order and
sorted order coincide — §12.4 is precisely the statement that this coincidence does not generalise).

### 12.6 Non-vacuity, all four arms, at `MAP_TREE_DEPTH = 16` over a SPARSE tree

Every exhibit is on a `2^16`-leaf commitment holding ONE live leaf — the occupancy `heap_root.rs`
builds and the one the dense `opensToMerkle` has no witness for at all. Nothing is enumerated: the
depth-16 membership paths are the symbolic `leftPadPath` / `slot1Path` cons-recursions (whose
siblings are `heap_root.rs`'s `EMPTY_SUBTREE_ROOTS`, welded by stage 2b's `perfectRoot_all_padding`),
and every root is NAMED as the schema's own `commit`.

| arm | accepting row | tooth that REFUSES |
|---|---|---|
| `.read` | `bite_read_row` → `bite_read_fires` | `bite_read_forged_value_refused` (a forged value has no accepting row, for any post-root and any pointer) |
| `.write` | `bite_write_row` → `bite_write_fires` | `bite_write_frozen_root_refused` (the frozen post-root forgery) |
| `.insert` | `bite_insert_row` → `bite_insert_post_opens` | `bite_insert_preroot_is_unforced` (the impossibility, concrete) |
| `.aafiInsert` | `bite_aafi_row` → `bite_aafi_absence_fires` | `bite_aafi_present_key_refused` (a present key has no bracket) |

Plus `aafi_free_slot_is_padding`: gate (d1)'s pinned `ZERO8` opens a PADDING cell, so the deployed
AAFI append grows into exactly the padding stage 2b modelled.

### 12.7 Floors and the disposition, stated at the current resolution

`Poseidon2SpongeCR` appears in **no type** in the module. Every extraction law is a pair:

* `…_or_resid` — **no hypothesis on `hash` at all**, with three NAMED, per-row, refutable residuals
  bundled as `OpenResid`: a genuine collision at the pair `pathCollFind` returns for THIS path and
  THIS committed vector; a genuine collision at the arity-3 leaf pair the TOTAL extractor `chainAt`
  names; and `imtLeafHash hash l = padDigest` — the opened digest IS `heap_root.rs`'s padding
  constant, which is stage 2b's ghost localized to one row (a FIXED-TARGET PREIMAGE of a literal,
  which collision-resistance does not exclude).
* `…_of_good` — the strength bridge at `MapGood hash := Function.Injective hash ∧ PadFree3 hash`,
  which is `padImtTeeth`'s own `Good` FIELD by `Iff.rfl` (`mapGood_is_teeth_good`). **No new hash
  property is introduced**, and `good_inhabited` is inherited (`oddSponge`). ⚠ LABELLED: the bridge
  is at an injective idealisation; only the `_or_resid` halves are statements about the deployed
  sponge.

`ImtSorted` / the committed heap behind a root stays a HYPOTHESIS, in the same knowledge-extraction
slot `ReconcileGatesAt`'s `∃ h` occupies — and on the `.aafiInsert` arm it is *derived* rather than
assumed. No floor carrier added; the FloorRatchet gate is unaffected.

### 12.8 What stage 3 now faces, repriced

* **Two arms can be cut over on gate-forced grounds** (`.read`, `.write`), and `.absent` already
  could. Three of five.
* **`.insert` cannot**, and no amount of Lean fixes it: the deployed op=3 row must be paired with an
  `.absent`/AAFI row, or the AIR must gate the pre-root. That is a **deployed-side action item**,
  and it is the same species as stage 2b's "pad with a domain-separated digest".
* **`.aafiInsert`'s post side cannot at any `MapLeafSchema`**, by §12.4. Either the denotation grows
  an order coordinate or the deployed AAFI re-sorts. Also a deployed-side decision.
* §10.5's 20 punch-through sites / 40 asserted theorems are untouched by this lane; the
  recommendation to restate the per-effect teeth over `MapOp.holdsAtS S` additively still stands and
  is now backed by two arms' worth of gate-forced denotation.

---

## 13. ⚑⚑ THE EMIT SIDE — an arity-2 leaf site is in the DEPLOYED DESCRIPTOR BYTES (2026-07-25)

Everything above §12 is about the **denotation**: Lean objects consumed by theorems. §1's surface is a
list of *declarations*. It does not cover the **emit** side — the Lean that AUTHORS descriptor bytes a
prover runs — and that is where the third recurrence of this divergence was found.

### 13.1 The site, and the reach (established first, because it changes everything downstream)

`Emit/EffectVmEmitHeapRoot.siteHeapLeaf` is an arity-2 `hash[addr, value]` hash site. It is **not**
Lean-side-only. The reach, evidence in order:

| hop | artifact |
|---|---|
| author | `EffectVmEmitHeapRoot.heapWriteSpliceVmDescriptor` (`hashSites := [siteHeapAddr, siteHeapLeaf]`) |
| rotate+graduate | `RotatedKernelRefinementExercise.heapWriteV3 = graduateV1 (rotateV3 heapWriteSpliceVmDescriptor) ++ [.mapOp heapSpliceWriteOp]` |
| emit | `metatheory/EmitRotationV3.lean:140` (`v3rot` line) and `EmitWideRegistryProbe.lean` |
| serialize | `scripts/emit_descriptors.py` → `circuit/descriptors/rotation-v3-staged-registry.tsv` (narrow, line 47) and `rotation-wide-registry-staged.tsv` (WIDE) |
| **live verify** | `turn/src/executor/proof_verify.rs:1088` resolves the member out of `WIDE_REGISTRY_STAGED_TSV`; `:1145`'s `LIVE_ONLY_BARE_KEYS` contains `"heapWriteVmDescriptor2R24"`, so the **bare wide member is what the light client checks** |
| executed | `circuit/tests/heap_write_roundtrip.rs` proves + light-client-verifies against that exact member |

NOT a by-name descriptor: it is absent from `EmitByName.byNameDescriptors` and `descriptor_by_name.rs`
has no arm for it. So the "Lean-side only" disposition that applies to the attested-automaton family
does **not** apply here.

The site is in the bytes. Decoded from the committed TSVs, the `poseidon2_chip` lookups are:

```
narrow (dregg-effectvm-heapWrite-splice-v1-rot24-v3-staged, trace_width 1633):
  arity 2, in0 70 (COLL),      in1 71 (KEY),   out0 102   ← siteHeapAddr
  arity 2, in0 102 (HEAP_ADDR), in1 72 (VALUE), out0 103   ← siteHeapLeaf   ⚠ ARITY 2
  map_op write  key 102  value 72  root [216, 247..253]  new_root [455, 486..492]

wide (dregg-effectvm-heapWrite-v1-rot24-v3-write-heapopen, trace_width 1963):
  arity 2, in0 70,  in1 71, out0 90                        ← siteHeapAddr  (compacted)
  arity 2, in0 90,  in1 72, out0 91                        ← siteHeapLeaf  (compacted) ⚠ ARITY 2
  map_op write  key 90  value 72  root [120, 151..157]  new_root [299, 330..336]
```

### 13.2 The disposition: a DEAD PIN, not a wrong binding — and the reason matters

The urgent worry was that a descriptor might *model* an arity-2 leaf while `heap_root.rs` folds arity-3,
i.e. that a refinement theorem would be about an object the prover never runs (the `.absent` pattern).
Measured, the answer is narrower and better:

* **The authenticating leaf in this descriptor is ALREADY arity-3, and correct.** The heap-open READ
  appendix and the after-spine absorb `[addr, value, next_addr]` at NATIVE 8-felt width:
  `Emit.HeapOpenEmit.heapLeafInputs` (`#guard`-pinned at length 3, with an explicit regression comment
  naming the arity-2 emit as the drift it catches), `heapLeafDigest_sound8`, `afterSpineColsH`; Rust
  side `fill_heap_open_read` / `fill_heap_after_spine` fold `HeapLeaf::digest8()`. That leg **was** moved
  with the tree on 2026-07-12.
* **Nothing reads `HEAP_LEAF`.** `EffectVmEmitHeapRoot.heapSpliceSites_never_read_HEAP_LEAF` decides it
  over the emitted input lists; the splice `MapOp`'s key is `HEAP_ADDR` and its value is `prmCol VALUE`,
  confirmed against the committed bytes by `heap_write_deployed_root_forced.rs`. ★ And measured across the
  WHOLE committed constraint list, not just the hash layer: decoding both TSVs, the leaf column is
  referenced by **exactly one** of the 161 (narrow, col 103) / 253 (wide, col 91) constraints — its own
  arity-2 chip lookup — and there only at tuple position 17, the `out0` DIGEST slot. It is an input to
  nothing; no gate, no boundary, no PI binding, no map-op mentions it.
* So `siteHeapLeaf` **relaxes nothing**. It costs one Poseidon2 chip request per row and it makes a false
  claim in the Lean. It is a vestige of the pre-IMT design that the 2026-07-12 sweep missed because the
  sweep was scoped to Rust `HeapLeaf` sites.

The residual is therefore a **naming/scope wound plus prover cost**, not a soundness hole — stated at
that resolution deliberately, since the emit-side worry justified assuming worse until measured.

### 13.3 The FLAG-DAY (authored, NOT taken — it moves deployed descriptor bytes)

`EffectVmEmitHeapRoot.heapSpliceSitesImt = [siteHeapAddr]` and `heapWriteSpliceVmDescriptorImt` are
authored in Lean now, unrouted, so the shape exists before the bytes move (house law #1). Taking it:

1. flip `heapWriteSpliceVmDescriptor.hashSites` to `heapSpliceSitesImt`;
2. `lake env lean --run EmitRotationV3.lean` → `scripts/emit_descriptors.py` — rewrites **both** TSVs
   and `circuit/descriptors/PROVENANCE.json`;
3. drop the producer's `leaf_digest_col` fill in
   `trace_rotated.rs::generate_rotated_heap_write_wide_raw` (Rust calls the emission, so it follows);
4. `heap_write_deployed_root_forced.rs` keeps its negative assertion on `HEAP_LEAF` and gains a positive
   one that no arity-2 lookup targets it at all;
5. ⚠ **VK EPOCH.** Descriptor bytes change ⇒ the VK for `heapWriteVmDescriptor2R24` changes ⇒ every
   already-committed heapWrite turn was proven under the OLD VK. This is a VK-epoch flip, not a byte
   tidy-up. **ember-gated.**

What survives the flip is proved: `heapSpliceImt_addr_forced` (the splice KEY binding — the only thing
this descriptor is relied on for), `goodSpliceRow_recomputes_imt` (the honest producer is not stranded),
`forgedAddrRow_refused_imt` (the tooth still bites).

### 13.4 The blast radius — theorems about the retired arity-2 heap commitment

These are TRUE about `mapRoot`/`leafOf` and are **not** about the tree the prover folds. Any citation of
them as a statement about `heap_root` is wrong.

| theorem | file | why it is about the retired shape |
|---|---|---|
| `heapWrite_splice_forced` | `RotatedKernelRefinementExercise.lean:317` | concludes `writesTo` = `writesToMerkle` = arity-2 `mapRoot` |
| `heapWrite_newRoot_splice_forced` | `:391` | same conclusion, through the readout |
| `heapWrite_sat_rejects_wrong_splice_root` | `:420` | via `writesTo_functional` → `mapRoot_injective` |
| `heapWrite_realizes_heapSet` | `:444` | conclusion names `mapRoot hash MAP_TREE_DEPTH` explicitly |
| `heapWrite_sat_rejects_forged_root` | `:472` | hypothesis AND conclusion name `mapRoot`; uses `mapRoot_injective` |
| `heapSplice_leaf_forced` | `EffectVmEmitHeapRoot` §4 | forces the arity-2 `leafOf` digest — the vestige |
| `tampered_value_moves_leaf` / `tampered_addr_moves_leaf` | `EffectVmEmitHeapRoot` §6 | anti-ghosts on `leafOf`, arity 2 |

Two facts that BOUND the radius, both checked:

* **The vestige theorem has ZERO downstream consumers.** `RotatedKernelRefinementExercise`'s `open` list
  imports `heapSpliceSites` and `heapSplice_addr_forced` and **not** `heapSplice_leaf_forced`, `leafOf`,
  or `siteHeapLeaf`. Nothing outside the authoring module cites it.
* The five `heapWrite_*` rows are the `writesTo` denotation's problem, not the emit side's — they are
  exactly what §12's `MapKindImtGates.writeImtRow_writes_of_good` (at `padImtSchema`) is the replacement
  for. Restating them over `MapOp.holdsAtS (padImtSchema sent)` is the stage-3 work already priced in
  §12.8, not new scope.

### 13.5 Prose asserting the retired shape — corrected in place

Nine sites, each a comment claiming a shape that stopped existing on 2026-07-12. All were false at HEAD
and are now corrected with the correction stated (not silently rewritten), because a doc-comment naming
the wrong object is precisely how the `.absent` model went thirteen days unquestioned:

* `Emit/EffectVmEmitHeapRoot.lean` — header (`leaf = hash[addr,value]`, `root = mapRoot`,
  `SAT ⟹ mapRoot (Heap.set …)`, the cell≡circuit leaf leg), §2, §2.E, §3 `leafOf`, §4, §5
* `Substrate/Heap.lean` — `leafOf` documented as "the heap LEAF"
* `metatheory/Dregg2/Circuit/MapMerkleRoot.lean` — §4 title "the deployed map COMMITMENT" and `mapRoot`'s
  **"BYTE-IDENTICAL to `heap_root.rs`'s `CanonicalHeapTree::root`"** (a byte-identity claim to a Rust
  object that moved — the sharpest of the nine)
* `metatheory/Dregg2/Circuit/MapDenotationSchema.lean` — `narrowSchema` documented **"The DEPLOYED-TODAY schema"** (see
  §13.6) and `imtSchema` documented "The DEPLOYED-ACTUAL schema" (right leaf, DENSE occupancy — a
  way-point, not the deployed instance)
* `metatheory/Dregg2/Circuit/MapPaddedDenotation.lean` — `narrowTeeth` documented "(deployed-today)", inheriting the above
* `metatheory/Dregg2/Circuit/MapOpsColumnLayout.lean:69` — "MIN/MAX sentinels are real entries of the modeled heap"
  (deployed occupancy is `HEAP_SENTINEL_LEAVES = 1`: MIN only, MAX survives as the terminal pointer)
* `metatheory/Dregg2/Circuit/MapOpsColumnLayout.lean:575` — `leafOf_injective` documented as "The heap leaf"
* `metatheory/Dregg2/Circuit/Emit/CapInsertEmit.lean:17` — "`accumInsert_writesTo8` for the arity-2 heap tree"
* `metatheory/Dregg2/Circuit/Emit/AccumulatorOpenEmit.lean:70` — "the generic arity-2 `(key, value)` node8 membership",
  describing an appendix (`effHeapOpenV3`) that absorbs THREE leaf columns
* `Exec/UniversalBridge.lean:35,863` — `Heap.leafOf` called "the universal map's generic leaf". This one
  is **correct at its own object** (the umem boundary tree genuinely is arity-2, `UMemCodec`'s
  `rootWith (leafOf hash)`); it gained the scope qualifier so it is not read as covering `heap_root`.
* `metatheory/Dregg2.lean:1028` — the orientation index's `heapWrite` annotation, **twice stale**: it
  claimed heapWrite is "OUT-OF-LIVE-APEX (ABSENT from v3Registry)" with "RUST SCOPE … NOT done" (it is
  in both registries, the apex ranges over it, and the light client resolves the wide member), and it
  described the retired prepend-accumulator advance over `leafOf(addrOf coll key) value`.

### 13.6 ⚑ `narrowSchema` was NAMED "DEPLOYED-TODAY" and that name was load-bearing

`MapDenotationSchema.narrowSchema`'s doc-comment read **"The DEPLOYED-TODAY schema"**. It is not, and has
not been since 2026-07-12 — in the same file whose header opens with the refutation
(`imtRoot_ne_mapRoot`) that makes it false. A schema named "deployed" that is not deployed is the exact
mechanism this document exists to unwind.

Resolved by **re-documentation, not rename** — `MapKindImtGates.lean:113,1009` and
`MapPaddedDenotation.lean:108,799` reference the identifier, and `MapKindImtGates` is another lane's
live file; a rename would be churn for no gain, and the identifier `narrowSchema` is *accurate*
(it is the narrow, arity-2 schema). What was wrong was only the word "deployed". It now reads "The
RETIRED arity-2 schema — the CONSERVATIVITY ANCHOR, and NOT the deployed one", states the correction and
its date, and names the deployed one.

★ **THE DEPLOYED SCHEMA IS `MapPaddedDenotation.padImtSchema sent`** — arity-3 IMT leaves over the
deployed relink AND the deployed SPARSE occupancy (`length ≤ 2 ^ d`), teeth `padImtTeeth sent`, arm laws
in `MapKindImtGates`. Not `narrowSchema` (wrong leaf) and not `imtSchema` (right leaf, dense occupancy).

**One citation leaned on the false name and was also wrong:** `MapPaddedDenotation.narrowTeeth`'s
doc-comment said "TEETH FOR THE DENSE arity-2 schema (deployed-today)". Corrected. No *theorem* rested
on it — the two uses of `narrowSchema` in `MapKindImtGates` (`:113` open, `:1009`
`denseSchema_write_forces_key_present narrowSchema`) are legitimate instantiations of a general dense-
schema law at the narrow instance, and say nothing about deployment.
