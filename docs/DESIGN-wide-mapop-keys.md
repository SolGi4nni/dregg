# DESIGN — widening `MapOp.key` to 8 felts: closing the felt-width **kind-D** class at its root

**Opened 2026-07-24.** Companion to `docs/WOUND-felt-width-boundaries-2026-07-19.md` (the
catalogue) and `docs/DESIGN-felt-width-rotation-epoch-2026-07-19.md` (the kind-E epoch). This
document is about kind **D** only: *31-bit KEYS inside accumulators, where widening the root did
nothing.*

**Substrate, said out loud:** everything below is **Lean-authored AIR**. The IR type, the widened
gate model, the bracket comparison and its soundness live in `metatheory/`; Rust decodes the emitted
bytes and fills the trace. No constraint in this design is hand-written in Rust.

---

## 0. The root cause, in one line of type

```lean
-- metatheory/Dregg2/Circuit/DescriptorIR2.lean:301-313
structure MapOp where
  guard   : EmittedExpr
  root    : Fin 8 → EmittedExpr        -- ← faithful 8-felt digest group
  key     : EmittedExpr                -- ← ONE FELT, by construction
  value   : EmittedExpr
  newRoot : Fin 8 → EmittedExpr        -- ← faithful 8-felt digest group
  op      : MapOpKind
```

The v10 / `Faithful8` campaign widened **roots**. It never widened **keys**, and this type line is
why: a map-op key is one felt *in the IR*, so a producer physically cannot hand eight felts to a
one-felt column. Every kind-D site is un-widenable *producer-side* for this single reason. The Rust
mirror is `circuit/src/descriptor_ir2.rs:571-586` (`MapOpSpec { root: Vec<LeanExpr>, key: LeanExpr,
… }`) — same shape, same waist.

The consequence is not hypothetical. Wound **#20** (logged 2026-07-24, commit `22bde06e89`) is the
current instance: `spendAncestorFreshOp`'s `.absent` open keys on
`undelegated_spend_ancestor()` = `fold_bytes32_to_bb(cred_nul(mint_provenance()))`
(`circuit/src/effect_vm/trace_rotated.rs:1402,1415`) — a BLAKE3 nullifier squeezed to one felt, in a
**grow-only** set whose key domain is **attacker-writable** (`CellId::derive_raw`,
`types/src/lib.rs:891`, BLAKE3 over an attacker-chosen `(public_key, token_id)`, grindable
**offline**). ~2^31 offline hashes plus one legitimate create+delegate+revoke permanently bricks
every undelegated `NoteSpend`.

---

## 1. What must change — the surface list

Named per surface, with the file that owns it. **★** marks a surface this session's Lean lane
already authored or proved.

### 1.1 The IR type (Lean, authoritative)

| # | Surface | File | Change |
|---|---------|------|--------|
| S1 ★ | The IR node | `metatheory/Dregg2/Circuit/DescriptorIR2.lean:301-313` | `key : EmittedExpr` → `key : Fin 8 → EmittedExpr`. Authored **beside** the deployed node as `MapOpW` in `metatheory/Dregg2/Circuit/MapOpWideKey.lean` §1. |
| S2 ★ | The row / bus face | `DescriptorIR2.lean:633-641` (`MapOp.rowAt`, `mapLog`) | The map-log tuple grows `19 → 26` felts (`MapOpW.rowAt`, `rowAt_length`). |
| S3 | The JSON face | `DescriptorIR2.lean:1548` (`MapOp.toJson`) | `"key"` becomes an 8-element array, exactly as `"root"`/`"new_root"` already are. **Not authored** — writing it is the cutover commit. |
| S4 | The scalar denotation | `DescriptorIR2.lean:534-590` (`opensTo`/`writesTo`/`MapOp.holdsAt`) | `holdsAt` currently reads `(m.root 0)` and a scalar `m.key` and denotes into `MapMerkleRoot.opensToMerkle` at `Heap.FeltHeap = List (ℤ × ℤ)`. Widening means re-keying at `Digest8Key`. **See §2 — this is cheaper than it looks.** |

### 1.2 The AIR gate model (Lean, authoritative)

| # | Surface | File | Change |
|---|---------|------|--------|
| S5 ★ | The `.absent` bracket | `MapOpsColumnLayout.lean:587-594` (`ReconcileGatesAt`, `.absent` arm) | `klo < m.key.eval a ∧ m.key.eval a < khi` — two ℤ compares — become two **8-limb lex** compares. The gadget exists: `Emit/LexCompare8Emit.lean::lexLt8_refines`. **The weld is authored**: `MapOpWideKey.absentBracket_of_lexBlocks` (+ its anti-DoS twin `absentBracket_realizable`). |
| S6 ★ | The AAFI pointer bracket | `MapOpsColumnLayout.lean:1047-1058` (`AafiGatesAt` gate (b), `lowAddr < k ∧ k < lowNext`) | Same substitution. The surrounding law `aafiInsert_forces_imtInsert` **never uses ℤ arithmetic on the key** — it rides `pathRecompute_binds_updates` on the *digest vector*. Mechanical `[LinearOrder K]` generalization. |
| S7 ★ | The leaf schema | `MapOpsColumnLayout.lean:1028` (`aafiLeafHash`), `IndexedMerkleTree.lean:129-131` (`imtLeafHash`), `Substrate/Heap.lean:375` (`leafOf`) | `hash[addr, value, next_addr]` (arity 3) → `hash[addr8 ‖ value ‖ next8]` (arity **17**). Both the address **and** the pointer widen — the pointer *is* the absence bracket, so a wide addr with a narrow pointer re-opens the waist on the high side of every gap. **Authored**: `MapOpWideKey.imtLeafHash8` + `imtLeafHash8_injective` under the same named `Poseidon2SpongeCR` floor, with the anti-launder pair `narrowLeaf_conflates` / `wideLeaf_separates`. |
| S8 | The Merkle layer | `MapMerkleRoot.lean` (`mapRoot`, `opensToMerkle`, `writesToMerkle`) + `MapOpsColumnLayout.lean:466-566` (the three per-kind openers) | Re-key `Heap.FeltHeap` → `List (Digest8Key × ℤ)`. **`mapNode`/`foldLevel`/`perfectRoot`/`perfectRoot_injective`/`pathRecompute`/`pathRecompute_binds_updates` are untouched** — they operate on the ℤ *digest* vector, which does not widen. Only `leafOf` and its injectivity move. |

### 1.3 The Rust decode + AIR + trace (calls into Lean; hand-writes nothing)

| # | Surface | File:line | Change |
|---|---------|-----------|--------|
| S9 | The spec mirror | `circuit/src/descriptor_ir2.rs:571-586` | `key: LeanExpr` → `key: Vec<LeanExpr>` (length `CHIP_OUT_LANES`), exactly like `root`/`new_root`. |
| S10 | The canonical codec | `circuit/src/descriptor_ir2_canonical.rs:361-383` (write), `:778-790` (read) | `writer.sequence("MapOpSpec.key", …)` / `reader.sequence(…)` — one line each side, mirroring the existing `root`/`new_root` sequences. |
| S11 | The MapOps column layout | `circuit/src/descriptor_ir2.rs:2010-2066` | `MAP_KEY` (1 col) → 8-col group; `MAP_NEXT` (1) → 8; `MAP_LOW_ADDR` (1) → 8; the AAFI compare blocks `MAP_A_DEC0/MAP_K_DEC0/MAP_B_DEC0/MAP_CMP_LO0/MAP_CMP_HI0` (`MA_DECOMP_COLS = 13`, `MA_CMP_COLS = 13`) are replaced by two `LexCompare8Emit` blocks (`LEX_WIDTH = 40` each). |
| S12 | The map-log bus tuple | `circuit/src/descriptor_ir2.rs:2077` (`MAP_LOG_WIDTH = 2·CHIP_OUT_LANES + 3 = 19`), `:2129-2149` (`map_log_tuple`) | `19 → 26`; the declared `map_ops` table arity in every emitted descriptor JSON moves with it. |
| S13 | The leaf absorb | `circuit/src/descriptor_ir2.rs:2160-2170` (`map_leaf_input_cols`) | `[MAP_KEY, value_col, MAP_NEXT]` → the 17-column list. **The header already says this is the seam** ("the function is the single seam a wider declared map leaf would extend; the absorb code paths are already arity-generic"). |
| S14 | The MapAbsent AIR | `circuit/src/descriptor_ir2.rs:1974-1995` (`MA_*`), `:3196+` (`Ir2Air::MapOps` eval) | Same substitutions on the dedicated absent table. |
| S15 | The heap tree | `circuit/src/heap_root.rs:114-149` (`HeapLeaf { addr, value, next_addr }`, `digest`/`digest8`), `:100` (`heap_addr`) | `addr`/`next_addr` become `[BabyBear; 8]`. |
| S16 | The producers | `circuit/src/effect_vm/trace_rotated.rs` (the `.absent`/`.aafiInsert` fills), `sdk/src/full_turn_proof.rs` (`spent_nullifiers` threading) | Fill 8 lanes instead of one; drop `fold_bytes32_to_bb` at every map-op key site (`trace_rotated.rs:1377,1402,1415,1575,1661`). |

---

## 2. Already proven vs genuinely new — the honest split

**Verdict: (a) widening the IR type + emitted constraints and instantiating. NOT (b) new
combinatorics.** The 07-20 scoping call on site #10 was right and it generalizes to the whole class.

### 2.1 Already proven — COMPOSE, do not re-derive

| Object | Where | What it already gives at 8 felts |
|--------|-------|----------------------------------|
| `sorted_gap_excludes` | `Crypto/NonMembership.lean` | `[LinearOrder Digest]`-generic — the bracketing heart, free at any key type. |
| `Digest8Key`, `sorted_gap_excludes_digest8`, `imtAbsent_excludes_digest8`, `imtInsert_preserves_digest8` | `Crypto/Digest8KeySpike.lean` | The 8-felt lex key with its `LinearOrder`, and the **deployed** IMT keystones instantiated at it — same objects the felt chain deploys, no twin. |
| `SpineCommitsW` / `keysOfW` / `GapOpenW` / `nonMembership_soundW` | `Circuit/SortedTreeNonMembershipWide8.lean` | The whole non-membership wrapper, `[LinearOrder K]`-generic, instantiated at `Digest8Key`. Plus `security_delta` — the lane-0 collision made concrete. |
| `sortedInsertW` / `update_soundW` / `update_preserves_sortedW` / `insert_then_no_nonmembershipW` | `Circuit/SortedTreeInsertWide8.lean` | The insert side and the insert/exclude duality at `Digest8Key`. |
| `lexLt8Descriptor` / `lexLt8_refines` | `Circuit/Emit/LexCompare8Emit.lean` | The **emitted** in-AIR lex-`<` block over canonical 8-felt keys, as a proven iff, with the p-boundary canary and the LSB-decider tooth. |
| `Substrate.Heap` | `Substrate/Heap.lean:68` | **Already `[LinearOrder κ]`-generic** (`keys`, `SortedKeys`, `get`, `set`, `set_sorted`, `get_none_of_gap`, `ext_get`). Only `FeltHeap`/`leafOf` (`:367,375`) are ℤ-pinned. |
| `mapNode` / `foldLevel` / `perfectRoot` / `perfectRoot_injective` / `pathRecompute` / `pathRecompute_binds_updates` | `MapMerkleRoot.lean`, `MapOpsColumnLayout.lean` | Operate on the ℤ **digest** vector. The key width never enters. Reusable verbatim. |
| `aafiInsert_forces_imtInsert` | `MapOpsColumnLayout.lean:1075` | The two-path append-order law. Its proof uses the key only to carry the bracket through — generalizes by substitution. |

### 2.2 Genuinely new — and all of it is small

1. **The IR type + its row/JSON face.** Mechanical. ★ `MapOpW` authored.
2. **The wide leaf hash + its injectivity.** ★ `imtLeafHash8_injective`, under the **same** named
   `Poseidon2SpongeCR` floor — no new cryptographic assumption. Plus the anti-launder tooth: ★
   `narrowLeaf_conflates` shows that pre-folding the address to lane 0 and *then* hashing still
   conflates `keyE`/`keyLo`, for **every** hash, with no CR hypothesis at all — the
   `finalSqueezeOnly_still_conflates` shape (#12) at the map leaf.
3. **The weld: emitted lex compare ↔ widened bracketing keystone.** ★
   `absentBracket_of_lexBlocks`: two satisfied `lexLt8` blocks plus a committed low leaf FORCE
   absence at the full 8-felt key; ★ `absentBracket_realizable`: an honest bracket ADMITS both
   blocks (the widened gate is not a DoS). Before this session these two halves existed and had
   never touched.
4. **The `ℤ → [LinearOrder K]` generalization of the three per-kind openers** (`opensToMerkle_of_path`,
   `opensToMerkle_none_of_bracket`, `writesToMerkle_of_path`) and of `mapRoot`. Not authored here.
   Mechanical: their proofs use `Heap.SortedKeys` / `get_none_of_gap` / `heapSet_eq_listSet` /
   `length_set_mem` (all already κ-generic) plus `leafOf_injective` (item 2 supplies the wide twin).
5. **Nothing else.** There is no new bracketing math, no new tree combinatorics, no new
   probabilistic argument, and no new crypto floor anywhere in this design.

### 2.3 What the new Lean module proves (this session, byte-safe)

`metatheory/Dregg2/Circuit/MapOpWideKey.lean` — new file, rooted in `Dregg2.lean`,
`#assert_axioms`-clean (27 keystones), no `sorry`/`admit`/`native_decide`, `lake build Dregg2`
exit 0. Nothing deployed is touched: no descriptor registered, no emit path, no JSON face.

* `MapOpW` — the widened node; `MapOpW.narrow` — the deployed node; **`narrow_key_is_lane0` (`rfl`)**:
  the deployed `MapOp.key` is *exactly* lane 0 of the wide key. The widening is a conservative
  extension, not a parallel universe.
* **The embedding** `embed1 : ℤ → Digest8Key` (felt in lane 0, zeros elsewhere) with
  **`embed1_lt : embed1 a < embed1 b ↔ a < b`** — lane 0 is the most-significant limb, so the lex
  order on embedded keys **is** the ℤ order. `MapOpW.ofNarrow` lifts any deployed node;
  `narrow_ofNarrow` is the round trip. This is the epoch-shape fact (§4).
* `imtLeafHash8` / `imtLeafHash8_injective` / `narrowLeaf_conflates` / `wideLeaf_separates`.
* `absentBracket_of_lexBlocks` / `absentBracket_realizable` — the weld, both directions.
* `HoldsKindW` + `absentW_sound` / `insertW_sound` / `aafiInsertW_sound` — the per-kind widened
  denotation, each one `nonMembership_soundW` / `update_soundW` *instantiated*.
* `insertW_then_absentW_unsat` — the duality, and the formal statement of §5's blocker.
* **Wound #20 priced in both directions as theorems** (§3 below).
* Non-vacuity: `demoAncestorOpW` reads a real 8-felt key off columns 0..7 (`keyAt = keyE`, whose
  distinguishing limb is felt **7**) while its lane-0 projection reads the *colliding* felt.

---

## 3. Which wound sites this closes

The class statement in the wound doc (kind **D**) lists **#5, #9, #11, #20**. Reading the deployed
emit sites, the map-op-keyed population is:

| Wound # | Deployed map-op(s) | Key expression | Key domain | Closed by the widening? | Residual afterwards |
|---------|--------------------|----------------|-----------|-------------------------|---------------------|
| **#20** | `spendAncestorFreshOp` (`.absent`), `EffectVmEmitRotationV3.lean:2407` | `.var (prmCol 3)` (col 71) | `hash_to_8(child_id)[0]`, `child_id` = BLAKE3 over attacker-chosen `(public_key, token_id)` | **YES — this is the site the design targets.** | The **col-71 lineage weld** (an unbound witness column: a prover parks any non-revoked felt). Width-independent, zero-cost, `7d49b0f449`'s named follow-up. Neither closes the other; both land in this epoch. |
| **#11** | `revokedFreshOp` (`.absent`) / `revokedInsertOp` (`.aafiInsert`), `:2734` | `.var (prmCol 0)` = `child_hash[0]` | same attacker-writable domain | **YES** — and #20 opens against exactly the set #11 inserts into, so they *must* close together. | None specific to width. Capacity (14 → 65534) already handled. |
| **#5** | `nullifierFreshOp` (`.absent`) / `nullifierInsertOp` (`.aafiInsert`), `:2368`; `commitmentsInsertOp` (`.aafiInsert`), `:2634`; producer fills `trace_rotated.rs:1377,1575,1661` | `.var NULLIFIER_PARAM_COL` / `COMMITMENT_KEY_PARAM_COL` | folded nullifier / note commitment | **YES for the KEY half.** | The **value** widening (note commitment / nullifier *value*, `cell/src/note.rs:329,243`) is a separate site — kind C, `hash_many → hash_many_8`. And the **ember-gated frozen kernel flip** (`NullifierAccumulator.lean:12-23`, "do NOT fire piecemeal"). |
| **#9** | *none* | — | — | **NO.** `turn/src/executor/membership_verifier.rs:105` is an **executor-side** authorized-set root, not a descriptor map-op. Kind D/E, closes in the kind-E rotation epoch, not here. | Whole site. |
| **#10** | (shielded pool) | — | — | **Partially — the key half only.** The wound's own 07-19 correction stands: #10 is "port the Rust-authored `spend_circuit` AIR to Lean + pin `merkle_root` to the committed accumulator + fold the value-link into the AIR + resolve the PQ-commitment story". Felt-width is the entry point, not the fix. | Everything else in that list. |

### 3.1 A kind-D site the catalogue does **not** yet number

**The accounts/cells tree.** `cellsFreshOp` (`.absent`) / `cellsInsertOp` (`.aafiInsert`)
(`EffectVmEmitRotationV3.lean:2850,2861`) key on `.var (prmCol 0)` = `create_hash[0]` for
createCell/spawn and `prmCol 1` (the derived child VK) for factory — the **same** one-felt
projection of a 32-byte hash, in a **grow-only** set, guarding "no account-id collision". The
`.absent` leg has #20's exact availability shape: grind a colliding `create_hash[0]`, revoke-style
plant it once, and the victim cell id can never be created. **Recommend logging it as wound #21**
and folding it into this epoch; it costs nothing extra once `MapOp.key` is 8 felts.

### 3.2 What the widening does **not** touch

The heap-write family (`setField*`, `transfer`, `mint`, `burn`, `refusalFieldsWriteOp`, the
cap-crown attenuate write, `heapSpliceWriteOp`) keys on `heap_addr(coll, key) = hash[coll, key]`
(`heap_root.rs:100`) — a *derived address*, and the ops are `.write`/`.read` (in-place update at an
existing key), not `.absent` membership boundaries. They are not in kind D. They ride the epoch
because the bus is shared (§4), not because they are wounded.

---

## 4. Cost and epoch shape

**One VK epoch for all map-op-bearing descriptors. Flag day, not migration.**

**Why one epoch and not staged per site.** `map_ops` is a single shared LogUp table
(`TID_MAP_OPS = 4`, `descriptor_ir2.rs:251`), one `Ir2Air::MapOps` instance, one leaf format. Every
descriptor's map ops receive on the same bus with the same tuple width. **32 committed descriptor
JSONs** carry `map_op` constraints today (`circuit/descriptors/*.json` +
`circuit/descriptors/by-name/*.json`), plus the staged rotation TSV registries. Widening the tuple
re-bases all of them. Two ways out, and only one is good:

* **(A) Second table `map_ops_wide`.** Fork the bus and the AIR so kind-D ops widen and the rest
  don't. **Rejected.** It doubles the map AIR, splits the leaf format, and creates exactly the
  narrow/wide twin pair the catalogue exists to catch (`#3`, `#12`, `#13` are all "a wide twin
  exists 19 lines away and the narrow one is still reachable"). It is a debt hole.
* **(B) One widened table; narrow ops embed. ✅ Chosen.** Pin lanes 1..7 to `.const 0` for every op
  that does not need a digest key. **This is safe and it is proved**:
  `MapOpWideKey.embed1_lt : embed1 a < embed1 b ↔ a < b` — lane 0 is the most-significant limb, so
  the lex order on embedded keys **is** the ℤ order. Every `Sorted` / `ImtSorted` / gap-bracket fact
  about a deployed narrow tree transports across the lift with **no re-proof**;
  `narrow_ofNarrow : (MapOpW.ofNarrow m).narrow = m` is the round trip. So there is **no key-space
  migration and no dual AIR** — the two key spaces are related by an order-isomorphism onto the
  lane-1..7-zero subspace, and every existing narrow tree *is already* a wide tree read at lane 0.

**Wire cost** (theorems, not estimates — `MapOpWideKey` §1c):

| Quantity | Now | After | Delta |
|----------|-----|-------|-------|
| map-log bus tuple | 19 | 26 | **+7** per map-op row |
| IMT leaf absorb arity | 3 | 17 | **+14** per leaf |
| `.absent` bracket compare | 2 × (`MA_DECOMP_COLS`+`MA_CMP_COLS`) ≈ 2 × 26 cols | 2 × `LEX_WIDTH` = 2 × 40 cols | +28 cols per absent/AAFI row |
| MapOps AIR width | `MAP_WIDTH = 897` | ~`897 + 7·(8−1)` for the widened `MAP_KEY`/`MAP_NEXT`/`MAP_LOW_ADDR` groups + the compare-block swap | ≈ +70 cols |

The Poseidon2 chip cost is the real one: an arity-17 absorb is two sponge blocks instead of one, at
every map leaf, on every path level that recomputes a leaf. Budget for roughly **2×** the leaf-hash
chip rows in map-op-bearing descriptors. Everything else is column count, which is cheap.

**What breaks meanwhile: nothing, because nothing is deployed.** `docs/…/no-greenfield-migration-theater`
applies literally here — there is no live ledger to migrate, the devnet games' ledger is not durable
(hbox `:8420`, lost on reboot), and the wound doc's own kind-E note says the same: "Cheap now
(nothing deployed), only gets more expensive." The epoch is: re-emit the Lean descriptors, regenerate
the VKs, re-baseline the committed roots. Every committed root changes (the leaf format moves), which
is precisely why it is one flag day and why it should happen **before** anything is deployed.

**Staging inside the epoch** (all in one commit-series, one VK bump at the end):

* **W1** — the Lean IR: `MapOp.key : Fin 8 → EmittedExpr`, `rowAt`, `toJson`. (`MapOpW` is the
  authored, byte-safe rehearsal of exactly this.)
* **W2** — the Lean gate model: the `ℤ → [LinearOrder K]` generalization of the three per-kind
  openers, `AafiGatesAt`, and `mapRoot`/`leafOf`; the `.absent`/AAFI brackets repointed onto
  `lexLt8Descriptor` via the authored weld.
* **W3** — the Rust decode (S9-S10) and the MapOps/MapAbsent AIR + trace (S11-S15).
* **W4** — the producers (S16), including deleting `fold_bytes32_to_bb` at every map-op key site.
* **W5** — the **col-71 lineage weld** (#20's separate soundness hole) and, if logged, the
  accounts-tree site (§3.1). These are width-independent but land in the same AIR epoch.
* **W6** — the ember-gated `NullifierAccumulator` kernel flip. **Not** to be fired piecemeal.

---

## 5. The honest blockers

1. **The insert side and the open side must move together — and this is now a theorem, not folklore.**
   `MapOpWideKey.insertW_then_absentW_unsat` states the duality: after a widened insert of `k`, any
   widened `.absent` open for `k` is contradictory. Read contrapositively: if the insert stays narrow
   and the open widens, the `.absent` op is keyed at a *different width* from the set it opens
   against, so it is **unopenable** rather than safer — a total liveness break for every spend, not a
   hardening. #20's own site note says this ("widening only the open side makes the `.absent` op
   unopenable rather than safer"), and #11's insert (`revokedInsertOp`) is the set #20's open reads.
   **They are one commit.**

2. **The pointer widens too, or the gap is still 31 bits on the high side.** The IMT absence bracket
   is `low.addr < k < low.next_addr`. Widening `addr` while leaving `next_addr` a felt leaves every
   gap's upper bound projected — the attacker aims at the *pointer*. Hence arity **17**, not 9.

3. **The `Opens` predicate is still abstract; the realizing chip row is Rust work in the epoch.**
   Same honest boundary the Wide8 modules declare. `absentBracket_of_lexBlocks` proves what the AIR
   row *means*; that the emitted row *is* that shape is W3.

4. **The `.absent` gate's canonicality envelope is a real hypothesis.** `lexLt8_refines` needs
   `0 ≤ cell < p` on all 16 key cells (`KeyCanon`). The deployed range-check discipline supplies it
   today for one felt; the widened emit must range-check **eight**, or the compare is unsound at the
   `p`-boundary (the gadget's own canary tooth). Sixteen extra range lookups per bracket compare.

5. **Every committed root changes.** The leaf format moves, so the accounts / nullifier /
   commitments / revoked / heap roots all re-baseline, and so does every pinned descriptor byte,
   every `#guard`ed `emitVmJson2`, every staged-registry TSV row, and every VK. This is the
   "rotated cohort re-baselines" cost, and it is only cheap while nothing is deployed.

6. **`decomp_cols(KEY_LO_BITS)`-based compares are deleted, not extended.** The existing AAFI/absent
   compare blocks (`MA_DECOMP_COLS`, `MA_CMP_COLS`) are a 1-felt construction. Extending them
   eight-fold would be a hand-written Rust AIR — **the drift this repo's law #1 forbids.** They are
   replaced by instantiations of the Lean-authored `lexLt8Descriptor`.

7. **Width is not the only thing wrong at some of these sites, and closing width must not be reported
   as closing them.** #20's unbound-witness col-71 hole, #10's `merkle_root`-not-pinned and
   value-link seams, #4's value widening — all survive this epoch. Say so at the sites.

---

## 6. Verdict

**Do it, and do it as one epoch, now.** The argument:

* The class's root cause is one type line, and the machinery to repair it is already on disk,
  proved, and `#assert_axioms`-clean. The remaining work is **instantiation plus a leaf widening** —
  the 07-20 scoping call, confirmed at the class level.
* The soundness ledger is honest: at `.absent` sites the narrow key costs **nothing** in soundness
  (`narrow_only_over_revokes` — proved: a projection is a function, so collisions only ever
  over-include). So this is not a theft-vector fix and must not be sold as one.
* The **availability** ledger is where it bites, and it is real, cheap, permanent and system-wide:
  `narrowAbsent_unprovable` refutes **every** narrow gap witness for an honest fresh key — for every
  spine and every gap shape — once one lane-0 collision is planted. ~2^31 **offline** hashes.
* The cheaper alternatives are all worse. A producer-side "refuse to revoke a colliding key" guard is
  the laundering shape the catalogue exists to catch (an adversarial prover mints the same trace; the
  AIR accepts any key) — rejected at the site and rejected again here. A second wide table forks the
  AIR and leaves the narrow path reachable. Doing nothing gets monotonically more expensive: the cost
  is bounded today only because nothing is deployed.

**The first lane, if this is picked up:** W1+W2 as one Lean commit — widen `MapOp.key` in
`DescriptorIR2.lean`, generalize `MapMerkleRoot`/`MapOpsColumnLayout` to `[LinearOrder K]` (the
digest-vector layer is already generic; only `leafOf` and the three openers move), and repoint the
`.absent`/AAFI brackets onto `lexLt8Descriptor` through the authored weld. The authored `MapOpW` is
the rehearsal of that commit's every step, so the lane has a compiling target to match rather than a
prose spec to reconstruct.
