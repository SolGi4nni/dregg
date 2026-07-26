/-
# `Dregg2.Circuit.MapAbsentImtGateWide` — the WIDE/epoch `.absent` family, REPOINTED onto the
  shape the prover actually runs.

## The premise this file acts on (verified at HEAD, not inherited)

`MapAbsentImtGate` established, on the NARROW arm, that the Lean `.absent` model and the deployed
`Ir2Air::MapAbsent` table are **incomparable**:

  * DEPLOYED (`circuit/src/descriptor_ir2.rs`, `Ir2Air::MapAbsent`): ONE arity-3 chip absorb
    `[3, MA_LO_ADDR, MA_LO_VALUE, MA_LO_NEXT, 0…, MA_LO_LEAF[0..8]]` — **the pointer is INSIDE the
    committed digest** — `HEAP_TREE_DEPTH` `node8` folds up ONE path to `MA_ROOT`,
    `MA_NEW_ROOT[i] = MA_ROOT[i]` on all 8 lanes, plus `eval_canon_decomp` ×3 and `eval_lex_lt` ×2
    giving `lo_addr < key < low_next` on unique canonical lifts. **No second leaf, no `pathPos`
    adjacency.**
  * LEAN (`MapOpsColumnLayout.ReconcileGatesAt` `.absent`, and `MapOpWideKeyGate`'s
    `ReconcileGatesAtW` `.absent` at ANY `LaneEnc`): TWO paths at
    `pathPos stepsHi = pathPos stepsLo + 1` opening `leafOfW` leaves (arity 2 narrow, arity 9 wide).
  * The divergence is ONE-SIDED and it is the bad one: above the largest committed key the adjacency
    arm has NO gate data at all (`adjacentBracket_unsat_above_max`), while the deployed terminal
    `SENTINEL_MAX` pointer brackets exactly those keys. `imtLeafHash_ne_heapLeafOf` rules out
    equivalence: the two systems commit DIFFERENT leaf objects.

This file does the WIDE half of the repointing. **The pointer-shaped results below are PRIMARY for
W3 and for every `.absent` consumer; the adjacency-shaped ones in `MapOpWideKeyGate` /
`MapOpWideKeyWeld` / `MapOpWideKeyRowBoundary` are RETAINED — they are the right target for a
future model in which the AIR does open two adjacent leaves — but they are no longer the statements
to quote about the deployed `.absent` arm.**

## What this file authors (ADDITIVE — every adjacency-shaped theorem is untouched)

  * **§1 `AbsentImtGatesAtW`** — the DEPLOYED `.absent` gate at the WIDENED key: ONE path to the
    pre-root at the **arity-17** IMT leaf `imtLeafHash8Of hash ⟨addr8, value, next8⟩`, the pointer
    bracket at the FULL 8-felt lex order, root preservation. The pointer rides at 8 felts ALONGSIDE
    the key because `MapOpWideKeyGate.halfWideLeaf_forges_absence_of_present` proves — for EVERY
    hash, with NO CR hypothesis — that widening the key alone is a non-membership FORGERY. A
    half-wide pointer is not an option, so there is no `LaneEnc`-style width knob here: the schema is
    17 felts or it is broken.
    Then ★ `absentImtGatesW_force_absence`: under the single named `Poseidon2SpongeCR` floor and a
    committed `ImtSorted` chain behind the pre-root, an accepting deployed wide row FORCES
    `key ∉ imtAddrs c` and `Heap.get (imtToHeapW c) key = none`.

  * **§2 the ARITY SEPARATION AT THE WIDE WIDTH** (`imtLeafHash8Of_ne_leafOfW`) — under CR an
    arity-17 IMT leaf digest is never an arity-9 wide map-tree leaf digest. So the IMT pre-root and
    the map-tree root of the SAME logical map are two DIFFERENT commitments, and the repointed
    `keysOfW`-shaped results in §4 must carry both explicitly. This is not bookkeeping: conflating
    them would be exactly the error `imtLeafHash_ne_heapLeafOf` caught narrow.

  * **§3 the WIDE ADJACENCY MODEL, ISOLATED AND MEASURED** — `AdjacentBracketGatesW` is
    definitionally `ReconcileGatesW … .absent`'s first conjunct at `wideEnc`;
    `adjacentBracketW_forces_committed_pair` and ★ `adjacentBracketW_unsat_above_max` port the
    narrow finding to the 8-felt key (the incompleteness is a property of the SHAPE, not of the
    width); `interiorW_pointerBracket_iff_adjacent` ports the interior equivalence, so the wide
    residue is likewise exactly ONE SLOT — the top gap.

  * **§4 the REPOINTED EPOCH FAMILY.** Each of `MapOpWideKeyWeld`'s / `MapOpWideKeyRowBoundary`'s
    `.absent` results gets a pointer-shaped twin, composed out of §1 rather than re-derived:
    `absentImtGatesW_force_keysOfW_absence`, `imtGates_force_holdsKindW_absent`,
    `absentImtGatesW_force_row_absence`, `absentImtGateW_of_lexBlocks_canon` (the W3 emission
    surface), `absentImtRow_of_lexBlocks_forces_absence`, `absentImtGate_forces_residue_absence`,
    and the `.absent` leg of the joint-unsat family (`aafiInsertW_then_absentImtW_unsat`).

  * **§5 NON-VACUITY IN THE TOP GAP** — the slot the adjacency model CANNOT reach, at the wide key,
    on `MapOpWideKeyGate`'s own `forgeChain` (whose terminal pointer `ptrHi` is a `SENTINEL_MAX`
    face, not a committed address). The deployed wide gate ACCEPTS `ptrMid`; the wide adjacency model
    has NO witness at any heap and any pair of paths; the key really is absent. Plus the anti-ghost.

## COVERAGE, PER THEOREM (the honest table)

DEPLOYED-SHAPE (a pointer-shaped twin now exists and is primary):

| adjacency-shaped original                            | pointer-shaped primary                          |
| ---------------------------------------------------- | ----------------------------------------------- |
| `MapOpWideKeyGate.opensToMerkleW_none_of_bracket`    | `absentImtGatesW_force_absence` (§1)            |
| `ReconcileGatesAtW` `.absent` arm                    | `AbsentImtGatesAtW` (§1)                        |
| `MapOpWideKeyGate.absentGateW_of_lexBlocks`          | `absentImtGateW_of_lexBlocks` (§4)              |
| `MapOpWideKeyCanonDischarge.absentGateW_of_lexBlocks_canon` | `absentImtGateW_of_lexBlocks_canon` (§4) |
| `MapOpWideKeyWeld.absentGatesW_force_keysOfW_absence`| `absentImtGatesW_force_keysOfW_absence` (§4)    |
| `MapOpWideKeyWeld.gates_force_holdsKindW_absent`     | `imtGates_force_holdsKindW_absent` (§4)         |
| `MapOpWideKeyRowBoundary.absentGatesW_force_row_absence` | `absentImtGatesW_force_row_absence` (§4)    |
| `MapOpWideKeyRowBoundary.absentRow_of_lexBlocks_forces_absence` | `absentImtRow_of_lexBlocks_forces_absence` (§4) |
| `MapOpWideKeyRowBoundary.absentGate_forces_residue_absence` | `absentImtGate_forces_residue_absence` (§4) |
| `.absent` leg of `gates_{insertW,aafiInsertW}_absentW_jointly_unsat` | `aafiInsertW_then_absentImtW_unsat` (§4) |

ADJACENCY-ONLY, AND REACHABLE ON A DEPLOYED ROW — so the original statement is VACUOUS exactly
there and the pointer twin is the one to use:

  * every theorem above, read at its ORIGINAL statement, on any key ABOVE the largest committed
    address. `topGapW_model_rejects` (§5) exhibits the wide instance; `adjacentBracketW_unsat_above_max`
    makes it general. This is the ORDINARY path — a fresh nullifier / cell-id above the current
    maximum lands there on every turn.

ADJACENCY-ONLY BUT INTERIOR-COVERED — the original statement is not vacuous, and on an `ImtSorted`
chain it is the SAME predicate as the deployed bracket:

  * `MapOpWideKeyGate.deployed_bracket_opener_is_instance`, `narrow_gates_is_instance` — these are
    CONSERVATIVITY facts (`narrow_gates_is_instance` is `Iff.rfl`), not `.absent` soundness claims.
    They remain exactly as true as before: they say the narrow model IS the wide model at
    `narrowEnc`, which is a statement about the MODEL and is unaffected by the model being the wrong
    shape. They are listed in the blast radius because anything QUOTING them about the deployed arm
    inherits the mismatch — the fix is to quote §1/§4, not to change them.
  * `interiorW_pointerBracket_iff_adjacent` (§3) is the theorem that makes "interior-covered"
    precise: at every low leaf WITH a physical successor the two brackets coincide, so the residue is
    the single top slot and nothing else.

NOT REPOINTED HERE, BY INSTRUCTION — `AlgoStarkSoundFanoutMemory` carries
`MapReconcileModelOkOfAccepts` into `Satisfied2` at the NARROW model, so it inherits the narrow
`.absent` arm's incompleteness verbatim: on a turn containing a top-gap `.absent` row its
`MapReconcileModelOk` hypothesis is FALSE (`MapAbsentImtGate.topGap_reconcileGates_unsat`), hence
the apex conclusion is vacuous on exactly those turns. Repointing it needs `MapReconcileModelOk`'s
per-row body to dispatch `.absent` to `AbsentImtGatesAt` and the chain-symbol premise
(`MapOpsColumnLayout` §8's named REMAINING WIRE) to reach the apex's `∃ h` slot — a scoped
follow-up, NOT done here.

## ⚠ NAMED PREMISE (unchanged, deliberately): `ImtSorted` at a deployed pre-root

Every law here takes `ImtSorted c` as a hypothesis, in the SAME slot `ReconcileGatesAtW`'s
`∃ h, E.HeapOk h` already occupies. What the deployed AIR forces PER TURN is real (write/read hold
the pointer fixed by column sharing; the AAFI flip has landed on every set an `.absent` op brackets;
the surviving sorted-splice `.insert`s write only `cap_root`, which no `.absent` op brackets). What
is NOT forced is the INDUCTION. **This is NOT promoted to a floor** — it stays a hypothesis, exactly
as `MapAbsentImtGate` carries it, and `Poseidon2SpongeCR` remains the only named floor in the file.

## ⚠ TWO RESIDUALS, NAMED (neither claimed closed)

  1. **No padding.** Every law here is stated at `c.length = 2 ^ dep` with
     `oldRoot = perfectRoot hash dep (c.map (imtLeafHash8Of hash))` — the chain IS the committed
     vector. This is `MapAbsentImtGate.absentImtGates_force_absence`'s shape verbatim, and it is a
     MODELLING SEAM the whole `.absent`/AAFI family already sits on: the deployment pads a
     `2 ^ HEAP_TREE_DEPTH` vector with a sentinel, for which `IndexedMerkleTree.imtLayout` /
     `ImtVecCorr` / `PreRootModelsChain` are the existing bridge. Lifting the pointer-shaped laws to
     the padded form is the SAME follow-up the AAFI side carries (`aafiGates_force_imtAbsent_layout`
     exists narrow; there is no wide twin), and it is not done here.
  2. **`aafiInsertW_then_absentImtW_unsat` has no single-trace witness.** Both legs are separately
     inhabited (`MapOpWideKeyWeld.demoAafiGateW_accepts` for the AAFI leg, `topGapW_deployed_accepts`
     for the `.absent` leg), but exhibiting BOTH on one chain needs a pre-chain of length `2 ^ d - 1`
     (an `imtInsert` grows the chain by one leaf, so a `2 ^ d` pre-chain has a `2 ^ d + 1` post-chain
     and residual 1 above bites immediately). Stated, not witnessed on a shared trace.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; sorry-free; no `native_decide`. Crypto
enters ONLY as the named `Poseidon2SpongeCR` floor — NO new floor. Every concrete object is a
literal ≤2-element list; `MAP_TREE_DEPTH` is never unfolded. NEW file; every import read-only; no
deployed descriptor / emit / JSON / Rust byte touched.
-/
import Dregg2.Circuit.MapOpWideKeyRowBoundary
import Dregg2.Circuit.MapAbsentImtGate

namespace Dregg2.Circuit.MapAbsentImtGateWide

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (MapOpKind)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.Emit.LexCompare8Emit (lexBlockHolds lexTf)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.MapMerkleRoot (mapNode perfectRoot perfectRoot_injective)
open Dregg2.Circuit.MapOpsColumnLayout (pathPos pathRecompute pathRecompute_binds_updates
  noPathColl_of_CR)
open Dregg2.Circuit.IndexedMerkleTree (ImtLeaf ImtSorted ImtAbsent imtAddrs imtInsert)
open Dregg2.Crypto.Digest8KeySpike (Digest8Key keyLo keyE imtAbsent_excludes_digest8)
open Dregg2.Circuit.SortedTreeNonMembershipWide8 (keysOfW)
open Dregg2.Circuit.MapOpWideKey (KeyCanon MapOpW HoldsKindW imtLeafHash8 imtLeafHash8_injective)
open Dregg2.Circuit.MapOpWideKeyGate (wideEnc CanonHeapW leafOfW leafOfW_injective mapRootW
  mapRootW_injective ReconcileGatesW ReconcileGatesAtW AafiGatesAtW imtLeafHash8Of
  imtLeafHash8Of_injective ptrMid ptrHi keyE_lt_ptrMid ptrMid_lt_ptrHi keyE_lt_ptrHi
  keyE_present_in_forgeChain keyLo_canon keyE_canon)
open Dregg2.Circuit.MapOpWideKeyWeld (opensAtW keysOfW_opensAtW imtToHeapW keys_imtToHeapW
  heapOkW_imtToHeapW aafiGatesW_force_sortedChainW aafiGatesW_force_spine_growthW)
open Dregg2.Circuit.MapOpWideKeyCanonDischarge (canonKey keyAtCanon keyAtCanon_of_block
  lexLt8_refines_canon)
open Dregg2.Circuit.MapOpWideKeyRowBoundary (RowKeyWiredW)
open Dregg2.Circuit.MapAbsentImtGate (imtSorted_next_eq_succ_addr)
open Dregg2.Substrate

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — THE DEPLOYED `.absent` GATE AT THE WIDENED KEY: arity-17 leaf, pointer bracket.

The deployed narrow row's three widening obligations, all forced by
`MapOpWideKeyGate.halfWideLeaf_forges_absence_of_present`:

  * `MA_LO_ADDR` → 8 felts,
  * `MA_KEY` → 8 felts,
  * `MA_LO_NEXT` → **8 felts** — NOT optional. With a lane-0 pointer, two pointers colliding on
    lane 0 share a leaf digest, so a prover opens the committed digest and claims the WIDER gap,
    proving a PRESENT address absent. That theorem needs no CR hypothesis at all.

Hence the leaf absorb is arity **17** (`imtLeafInput8 = addr8 ‖ value ‖ next8`) and there is no
width knob: `AbsentImtGatesAtW` is stated at that one schema. -/

/-- **`AbsentImtGatesAtW`** — the deployed `Ir2Air::MapAbsent` acceptance for ONE row at the
WIDENED key (depth-generic; the deployment pins `MAP_TREE_DEPTH = 16`). Existentially carries the
committed digest vector `xs` behind the pre-root — the knowledge-extraction premise, NAMED exactly
as `ReconcileGatesAtW`'s `∃ h` and `AafiGatesAtW`'s `∃ xs` — and asserts the gates: ONE low-leaf
open at the arity-17 IMT leaf, the POINTER bracket at the FULL 8-felt lex order, and root
preservation. The `MapAbsentImtGate.AbsentImtGatesAt` shape with both key groups widened; the
digest-vector layer is untouched, which is why this is a substitution and not a re-derivation. -/
def AbsentImtGatesAtW (hash : List ℤ → ℤ) (dep : Nat) (oldRoot newRoot : ℤ)
    (key lowAddr : Digest8Key) (lowValue : ℤ) (lowNext : Digest8Key) : Prop :=
  ∃ (xs : List ℤ) (steps : List (Bool × ℤ)),
    xs.length = 2 ^ dep ∧
    steps.length = dep ∧
    oldRoot = perfectRoot hash dep xs ∧
    -- the low-leaf opening (ONE path, arity-17 leaf: the pointer is INSIDE the committed digest)
    pathRecompute hash (imtLeafHash8Of hash ⟨lowAddr, lowValue, lowNext⟩) steps = oldRoot ∧
    -- the POINTER bracket, at the FULL 8-felt lex order (the emitted `lexLt8` blocks)
    lowAddr < key ∧
    key < lowNext ∧
    -- `MA_NEW_ROOT = MA_ROOT`, lane by lane
    newRoot = oldRoot

/-- **The deployed wide gate BINDS the arity-17 low leaf to the committed vector.** The single path
recomputing to the pre-root forces the widened low-leaf digest — all 17 felts, pointer included — to
BE the committed digest at the path's position; a forged pointer is a Poseidon2 collision.
`pathRecompute_binds_updates` used ONCE (the deployed table opens once). -/
theorem absentImtGatesW_bind_low (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (dep : Nat)
    {oldRoot newRoot : ℤ} {key lowAddr : Digest8Key} {lowValue : ℤ} {lowNext : Digest8Key}
    (hg : AbsentImtGatesAtW hash dep oldRoot newRoot key lowAddr lowValue lowNext) :
    ∃ (xs : List ℤ) (p : Nat),
      xs.length = 2 ^ dep ∧
      oldRoot = perfectRoot hash dep xs ∧
      xs[p]? = some (imtLeafHash8Of hash ⟨lowAddr, lowValue, lowNext⟩) ∧
      lowAddr < key ∧ key < lowNext ∧ newRoot = oldRoot := by
  obtain ⟨xs, steps, hlen, hsl, hor, hp, hlk, hkn, hnr⟩ := hg
  have e1 : xs.length = 2 ^ steps.length := by rw [hsl]; exact hlen
  have hroot1 : pathRecompute hash (imtLeafHash8Of hash ⟨lowAddr, lowValue, lowNext⟩) steps
      = perfectRoot hash steps.length xs := by rw [hp, hor, hsl]
  obtain ⟨hmem, _⟩ := pathRecompute_binds_updates hash steps xs
    (imtLeafHash8Of hash ⟨lowAddr, lowValue, lowNext⟩) e1 hroot1 (noPathColl_of_CR hCR)
  exact ⟨xs, pathPos steps, hlen, hor, hmem, hlk, hkn, hnr⟩

/-- **The deployed wide gate yields the `ImtAbsent` witness at the FULL 8-felt key** — the pointer
bracket IS the witness the sorted-chain keystone consumes. No CR needed: this is the bracket half.
The `.absent` twin of `MapOpWideKeyGate.aafiGatesW_force_imtAbsentW`. -/
theorem absentImtGatesW_force_imtAbsentW (hash : List ℤ → ℤ) (dep : Nat)
    {oldRoot newRoot : ℤ} {key lowAddr : Digest8Key} {lowValue : ℤ} {lowNext : Digest8Key}
    {c : List (ImtLeaf Digest8Key ℤ)}
    (hg : AbsentImtGatesAtW hash dep oldRoot newRoot key lowAddr lowValue lowNext)
    (hlow : (⟨lowAddr, lowValue, lowNext⟩ : ImtLeaf Digest8Key ℤ) ∈ c) : ImtAbsent c key := by
  obtain ⟨_, _, _, _, _, _, hlk, hkn, _⟩ := hg
  exact ⟨⟨lowAddr, lowValue, lowNext⟩, hlow, hlk, hkn⟩

/-- **★ THE DEPLOYED WIDE `.absent` LAW, on the shape that ships.** Given the committed `ImtSorted`
chain behind the pre-root (the NAMED per-deployment premise — see the header's ⚠), an accepting
widened `Ir2Air::MapAbsent` row FORCES the 8-felt key ABSENT from the whole committed address spine,
hence `Heap.get` on the projected wide map to be `none`, and the post-root to equal the pre-root.
The low leaf's membership in the chain is DERIVED here (`imtLeafHash8Of_injective` + root
injectivity), not assumed: the row cannot open a leaf the commitment does not hold.

This is the `.absent` result the epoch's wide theorems SHOULD have been stated over. -/
theorem absentImtGatesW_force_absence (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (dep : Nat)
    {oldRoot newRoot : ℤ} {key lowAddr : Digest8Key} {lowValue : ℤ} {lowNext : Digest8Key}
    {c : List (ImtLeaf Digest8Key ℤ)}
    (hs : ImtSorted c) (hlen : c.length = 2 ^ dep)
    (hroot : oldRoot = perfectRoot hash dep (c.map (imtLeafHash8Of hash)))
    (hg : AbsentImtGatesAtW hash dep oldRoot newRoot key lowAddr lowValue lowNext) :
    key ∉ imtAddrs c ∧ Heap.get (imtToHeapW c) key = none ∧ newRoot = oldRoot := by
  obtain ⟨xs, p, hxlen, hor, hmem, hlk, hkn, hnr⟩ := absentImtGatesW_bind_low hash hCR dep hg
  -- The opened vector IS the chain's arity-17 leaf-digest image: same length, same perfect root.
  have hxs : xs = c.map (imtLeafHash8Of hash) :=
    perfectRoot_injective hash hCR dep hxlen (by rw [List.length_map]; exact hlen)
      (by rw [← hor, hroot])
  subst hxs
  -- The bound digest decodes to a chain leaf (CR on the arity-17 leaf: all 17 felts bind).
  simp only [List.getElem?_map] at hmem
  have hlow : (⟨lowAddr, lowValue, lowNext⟩ : ImtLeaf Digest8Key ℤ) ∈ c := by
    cases he : c[p]? with
    | none => rw [he] at hmem; simp at hmem
    | some l =>
      rw [he] at hmem
      simp only [Option.map_some, Option.some.injEq] at hmem
      -- ⛑ `imtLeafHash8Of_injective` was cut over off `Poseidon2SpongeCR` to a per-instance,
      -- refutable non-collision at the two NAMED 17-felt preimages. This row still carries the
      -- refuted floor, and the floor IMPLIES that side condition, so nothing is lost here.
      obtain rfl := imtLeafHash8Of_injective hash (fun hc => hc.1 (hCR _ _ hc.2)) hmem
      exact List.mem_of_getElem? he
  have hnotin : key ∉ imtAddrs c :=
    imtAbsent_excludes_digest8 hs ⟨⟨lowAddr, lowValue, lowNext⟩, hlow, hlk, hkn⟩
  refine ⟨hnotin, ?_, hnr⟩
  rw [Heap.get_eq_none_iff, keys_imtToHeapW]
  exact hnotin

/-! ## §2 — THE ARITY SEPARATION AT THE WIDE WIDTH: two commitments, not one.

Narrow, `MapAbsentImtGate.imtLeafHash_ne_heapLeafOf` said arity 3 ≠ arity 2. Wide it is 17 ≠ 9 —
and the consequence is the same: the IMT pre-root the deployed `.absent` row opens and the
`mapRootW` the `keysOfW`/`opensAtW` wrapper layer speaks about are DIFFERENT commitments over the
same logical map. §4's repointed `keysOfW` results therefore name BOTH roots explicitly and bridge
them through the chain's projection (`imtToHeapW`), exactly as
`MapOpWideKeyWeld.aafiGatesW_post_chain_commitsW` already does for the AAFI side. -/

/-- **★ An arity-17 wide IMT leaf digest is NEVER an arity-9 wide map-tree leaf digest** (under CR:
equal digests would be equal preimage LISTS, and `17 ≠ 9`). So the deployed widened `.absent`
opening and `ReconcileGatesAtW`'s `.absent` opening at `wideEnc` cannot be satisfied by one
committed vector at one position: neither constraint system refines the other at the wide key
either. §3's interior equivalence is an equivalence of BRACKET PREDICATES on a shared chain — never
a translation of gate data. -/
theorem imtLeafHash8Of_ne_leafOfW (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (l : ImtLeaf Digest8Key ℤ) (e : Digest8Key × ℤ) :
    imtLeafHash8Of hash l ≠ leafOfW hash wideEnc e := by
  intro h
  have h' : hash (Dregg2.Circuit.MapOpWideKeyGate.imtLeafInput8 l)
      = hash (wideEnc.enc e.1 ++ [e.2]) := h
  have hl := congrArg List.length (hCR _ _ h')
  rw [Dregg2.Circuit.MapOpWideKeyGate.imtLeafInput8_length, List.length_append,
    wideEnc.enc_length, List.length_singleton] at hl
  have hw : wideEnc.width = 8 := rfl
  rw [hw] at hl
  exact absurd hl (by norm_num)

/-! ## §3 — THE WIDE ADJACENCY MODEL, ISOLATED: the incompleteness is the SHAPE, not the width.

`AdjacentBracketGatesW` is definitionally `ReconcileGatesW hash wideEnc dep r k v r .absent`'s
first conjunct. The narrow §2 of `MapAbsentImtGate`, ported: the same theorem, the same one-sided
direction, now at the 8-felt key. -/

/-- **`AdjacentBracketGatesW`** — the wide `.absent` gate body `ReconcileGatesAtW` actually
requires: TWO paths at CONSECUTIVE positions opening arity-9 wide map leaves whose keys strictly
bracket `k` at the 8-felt lex order. -/
def AdjacentBracketGatesW (hash : List ℤ → ℤ) (dep : Nat) (r : ℤ) (k : Digest8Key) : Prop :=
  ∃ (stepsLo stepsHi : List (Bool × ℤ)) (klo : Digest8Key) (vlo : ℤ) (khi : Digest8Key) (vhi : ℤ),
    stepsLo.length = dep ∧ stepsHi.length = dep ∧
    pathPos stepsHi = pathPos stepsLo + 1 ∧
    pathRecompute hash (leafOfW hash wideEnc (klo, vlo)) stepsLo = r ∧
    pathRecompute hash (leafOfW hash wideEnc (khi, vhi)) stepsHi = r ∧
    klo < k ∧ k < khi

/-- **`AdjacentBracketGatesW` IS the wide model's `.absent` body** — the isolation is definitional,
so nothing below is a statement about a lookalike. -/
theorem adjacentBracketGatesW_is_model_body (hash : List ℤ → ℤ) (dep : Nat) (r : ℤ)
    (k : Digest8Key) (v : ℤ) :
    ReconcileGatesW hash wideEnc dep r k v r MapOpKind.absent
      ↔ (AdjacentBracketGatesW hash dep r k ∧ r = r) :=
  Iff.rfl

/-- **The wide model's gate can only fire on a PHYSICALLY ADJACENT committed pair.** Under CR,
accepted wide adjacency gate data forces two entries of the committed wide heap at positions `p` and
`p+1` whose 8-felt keys bracket the row's key. -/
theorem adjacentBracketW_forces_committed_pair (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) {r : ℤ} {k : Digest8Key} (h : List (Digest8Key × ℤ)) (hlen : h.length = 2 ^ dep)
    (hroot : mapRootW hash wideEnc dep h = r) (hg : AdjacentBracketGatesW hash dep r k) :
    ∃ (p : Nat) (klo : Digest8Key) (vlo : ℤ) (khi : Digest8Key) (vhi : ℤ),
      h[p]? = some (klo, vlo) ∧ h[p + 1]? = some (khi, vhi) ∧ klo < k ∧ k < khi := by
  obtain ⟨sLo, sHi, klo, vlo, khi, vhi, hlLo, hlHi, hadj, hpLo, hpHi, hklo, hkhi⟩ := hg
  subst hroot
  have hbindLo := (pathRecompute_binds_updates hash sLo (h.map (leafOfW hash wideEnc))
    (leafOfW hash wideEnc (klo, vlo))
    (by rw [List.length_map, hlen, hlLo]) (by rw [hlLo]; exact hpLo)
    (noPathColl_of_CR hCR)).1
  have hbindHi := (pathRecompute_binds_updates hash sHi (h.map (leafOfW hash wideEnc))
    (leafOfW hash wideEnc (khi, vhi))
    (by rw [List.length_map, hlen, hlHi]) (by rw [hlHi]; exact hpHi)
    (noPathColl_of_CR hCR)).1
  simp only [List.getElem?_map] at hbindLo hbindHi
  cases heLo : h[pathPos sLo]? with
  | none => rw [heLo] at hbindLo; simp at hbindLo
  | some eLo =>
    rw [heLo] at hbindLo
    simp only [Option.map_some, Option.some.injEq] at hbindLo
    obtain rfl := leafOfW_injective hash hCR wideEnc hbindLo
    cases heHi : h[pathPos sHi]? with
    | none => rw [heHi] at hbindHi; simp at hbindHi
    | some eHi =>
      rw [heHi] at hbindHi
      simp only [Option.map_some, Option.some.injEq] at hbindHi
      obtain rfl := leafOfW_injective hash hCR wideEnc hbindHi
      rw [hadj] at heHi
      exact ⟨pathPos sLo, klo, vlo, khi, vhi, heLo, heHi, hklo, hkhi⟩

/-- **★ THE WIDE INCOMPLETENESS, GENERAL.** ABOVE the largest committed 8-felt key the wide
adjacency model has NO gate data — for ANY heap behind the root and ANY pair of paths. The hi
bracket would have to be a committed entry strictly GREATER than the key, and there is none. The
deployed pointer bracket has no such trouble: the last leaf's `next_addr` is the terminal
`SENTINEL_MAX`, which brackets every key above the maximum and which `heap_root.rs` deliberately
does not store as a leaf. Widening the key did not fix this; only changing the SHAPE does. -/
theorem adjacentBracketW_unsat_above_max (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) {r : ℤ} {k : Digest8Key} (h : List (Digest8Key × ℤ)) (hlen : h.length = 2 ^ dep)
    (hroot : mapRootW hash wideEnc dep h = r) (hmax : ∀ x ∈ Heap.keys h, x < k) :
    ¬ AdjacentBracketGatesW hash dep r k := by
  intro hg
  obtain ⟨p, klo, vlo, khi, vhi, _, hhi, _, hkhi⟩ :=
    adjacentBracketW_forces_committed_pair hash hCR dep h hlen hroot hg
  have hmem : (khi, vhi) ∈ h := List.mem_of_getElem? hhi
  have hkey : khi ∈ Heap.keys h := List.mem_map.mpr ⟨(khi, vhi), hmem, rfl⟩
  exact absurd hkhi (not_lt.mpr (le_of_lt (hmax khi hkey)))

/-- **★ THE WIDE INTERIOR EQUIVALENCE.** On an `ImtSorted` chain at the 8-felt key, at any low leaf
that HAS a physical successor, the DEPLOYED pointer bracket and the MODEL's adjacency bracket are
the SAME condition — `MapAbsentImtGate.imtSorted_next_eq_succ_addr` is already key-generic, so this
is that theorem instantiated, not a re-derivation. Hence the wide residue is likewise exactly ONE
SLOT: the top gap. -/
theorem interiorW_pointerBracket_iff_adjacent {c : List (ImtLeaf Digest8Key ℤ)} (hs : ImtSorted c)
    {p : Nat} {l l' : ImtLeaf Digest8Key ℤ} (hl : c[p]? = some l) (hl' : c[p + 1]? = some l')
    (k : Digest8Key) :
    (l.addr < k ∧ k < l.nextAddr) ↔ (l.addr < k ∧ k < l'.addr) := by
  rw [imtSorted_next_eq_succ_addr hs p l l' hl hl']

/-- The projected wide map sees the chain positionally (the bridge the wide adjacency model's
committed pair would have to land in). -/
theorem imtToHeapW_getElem? {c : List (ImtLeaf Digest8Key ℤ)} {p : Nat} {l : ImtLeaf Digest8Key ℤ}
    (h : c[p]? = some l) : (imtToHeapW c)[p]? = some (l.addr, l.value) := by
  simp only [imtToHeapW, List.getElem?_map, h, Option.map_some]

/-- **The interior wide bracket DOES produce the model's committed pair.** On an `ImtSorted` chain,
an interior deployed wide bracket hands the adjacency model exactly the two consecutive projected
entries it demands — the one-directional bridge, valid wherever a physical successor exists. -/
theorem interiorW_bracket_gives_adjacent_pair {c : List (ImtLeaf Digest8Key ℤ)} (hs : ImtSorted c)
    {p : Nat} {l l' : ImtLeaf Digest8Key ℤ} (hl : c[p]? = some l) (hl' : c[p + 1]? = some l')
    {k : Digest8Key} (hlo : l.addr < k) (hhi : k < l.nextAddr) :
    (imtToHeapW c)[p]? = some (l.addr, l.value) ∧
    (imtToHeapW c)[p + 1]? = some (l'.addr, l'.value) ∧ l.addr < k ∧ k < l'.addr :=
  ⟨imtToHeapW_getElem? hl, imtToHeapW_getElem? hl', hlo,
    ((interiorW_pointerBracket_iff_adjacent hs hl hl' k).mp ⟨hlo, hhi⟩).2⟩

/-! ## §4 — THE REPOINTED EPOCH FAMILY.

Every statement below is `MapOpWideKeyWeld`'s / `MapOpWideKeyRowBoundary`'s `.absent` result with
its gate hypothesis replaced by `AbsentImtGatesAtW` and (where the conclusion speaks in `keysOfW`)
the two commitments of §2 named separately: the IMT pre-root the row opens, and the `mapRootW` of
the chain's projection that the wrapper layer speaks about. Nothing is re-derived — §1 composed with
the existing weld lemmas. -/

/-- **★ THE REPOINTED WELD RESULT (`absentGatesW_force_keysOfW_absence`).** An accepting DEPLOYED
wide `.absent` row over an `ImtSorted`, canonically-addressed committed chain forces the key absent
from the wrapper layer's committed key set at the chain's PROJECTED map root. Both commitments are
named because §2 proves they are different objects; the chain is the single logical map behind them.
`spineCommitsW_of_heap` (through `keysOfW_opensAtW`) and `heapOkW_imtToHeapW` composed — the exact
bridge `aafiGatesW_post_chain_commitsW` uses on the AAFI side. -/
theorem absentImtGatesW_force_keysOfW_absence (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep d : Nat) {oldRoot newRoot : ℤ} {key lowAddr : Digest8Key} {lowValue : ℤ}
    {lowNext : Digest8Key} {c : List (ImtLeaf Digest8Key ℤ)}
    (hs : ImtSorted c) (hlen : c.length = 2 ^ dep)
    (hroot : oldRoot = perfectRoot hash dep (c.map (imtLeafHash8Of hash)))
    (hmlen : (imtToHeapW c).length = 2 ^ d)
    (hc : ∀ x ∈ imtAddrs c, KeyCanon (ofLex x))
    (hg : AbsentImtGatesAtW hash dep oldRoot newRoot key lowAddr lowValue lowNext) :
    key ∉ keysOfW (opensAtW hash wideEnc d) (mapRootW hash wideEnc d (imtToHeapW c))
      ∧ newRoot = oldRoot := by
  obtain ⟨hnotin, _, hnr⟩ := absentImtGatesW_force_absence hash hCR dep hs hlen hroot hg
  refine ⟨fun hmem => ?_, hnr⟩
  have hb := keysOfW_opensAtW hash hCR wideEnc d (imtToHeapW c)
    (heapOkW_imtToHeapW hs hc) hmlen (r := mapRootW hash wideEnc d (imtToHeapW c)) rfl
  rw [keys_imtToHeapW] at hb
  exact hnotin ((hb key).mp hmem)

/-- **★ THE REPOINTED `HoldsKindW` `.absent` LEG (`gates_force_holdsKindW_absent`).** The `.absent`
leg of the denotation the whole Wide8 wrapper layer speaks in, now forced by the DEPLOYED
pointer-bracket gate rather than by the adjacency gate. -/
theorem imtGates_force_holdsKindW_absent (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep d : Nat) {oldRoot newRoot : ℤ} {key lowAddr : Digest8Key} {lowValue : ℤ}
    {lowNext : Digest8Key} {c : List (ImtLeaf Digest8Key ℤ)} (v : ℤ)
    (hs : ImtSorted c) (hlen : c.length = 2 ^ dep)
    (hroot : oldRoot = perfectRoot hash dep (c.map (imtLeafHash8Of hash)))
    (hmlen : (imtToHeapW c).length = 2 ^ d)
    (hc : ∀ x ∈ imtAddrs c, KeyCanon (ofLex x))
    (hg : AbsentImtGatesAtW hash dep oldRoot newRoot key lowAddr lowValue lowNext) :
    HoldsKindW (opensAtW hash wideEnc d) (mapRootW hash wideEnc d (imtToHeapW c))
      (mapRootW hash wideEnc d (imtToHeapW c)) key v MapOpKind.absent :=
  ⟨(absentImtGatesW_force_keysOfW_absence hash hCR dep d hs hlen hroot hmlen hc hg).1, rfl⟩

/-- **★ THE REPOINTED ROW-LEVEL ABSENCE (`absentGatesW_force_row_absence`).** An accepting DEPLOYED
wide `.absent` gate at the ROW's key — as the compare block reads it — forces that key off the whole
committed address spine, and `Heap.get` on the projected map to be `none`. -/
theorem absentImtGatesW_force_row_absence (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) (m : MapOpW) (a : Assignment) {oldRoot newRoot : ℤ} {lowAddr : Digest8Key}
    {lowValue : ℤ} {lowNext : Digest8Key} {c : List (ImtLeaf Digest8Key ℤ)}
    (hs : ImtSorted c) (hlen : c.length = 2 ^ dep)
    (hroot : oldRoot = perfectRoot hash dep (c.map (imtLeafHash8Of hash)))
    (hg : AbsentImtGatesAtW hash dep oldRoot newRoot (keyAtCanon m a) lowAddr lowValue lowNext) :
    keyAtCanon m a ∉ imtAddrs c
      ∧ Heap.get (imtToHeapW c) (keyAtCanon m a) = none ∧ newRoot = oldRoot :=
  absentImtGatesW_force_absence hash hCR dep hs hlen hroot hg

/-- **★ THE REPOINTED EMISSION SURFACE (`absentGateW_of_lexBlocks`) — what W3 must emit.** Two
satisfied `lexLt8` blocks over the FULL 8 lanes (`low.addr < k`, `k < low.next`) plus **ONE**
committed path at the **arity-17** leaf ARE a deployed wide `.absent` gate. Compare
`MapOpWideKeyGate.absentGateW_of_lexBlocks`: the `stepsHi` path, the `hadj` position-adjacency
obligation and the arity-9 `leafOfW` leaf are all GONE; the pointer moves inside the committed
digest. That is the whole emission delta. -/
theorem absentImtGateW_of_lexBlocks (hash : List ℤ → ℤ) (dep : Nat) (oldRoot : ℤ)
    (envLo envHi : VmRowEnv) (lowAddr kk lowNext : Fin 8 → ℤ) (lowValue : ℤ)
    (hcLow : KeyCanon lowAddr) (hcK : KeyCanon kk) (hcNext : KeyCanon lowNext)
    (hLoA : ∀ i : Fin 8, envLo.loc i.val = lowAddr i)
    (hLoB : ∀ i : Fin 8, envLo.loc (8 + i.val) = kk i)
    (hLoBlk : lexBlockHolds lexTf envLo)
    (hHiA : ∀ i : Fin 8, envHi.loc i.val = kk i)
    (hHiB : ∀ i : Fin 8, envHi.loc (8 + i.val) = lowNext i)
    (hHiBlk : lexBlockHolds lexTf envHi)
    (xs : List ℤ) (steps : List (Bool × ℤ))
    (hxlen : xs.length = 2 ^ dep) (hsl : steps.length = dep)
    (hor : oldRoot = perfectRoot hash dep xs)
    (hp : pathRecompute hash
      (imtLeafHash8Of hash ⟨toLex lowAddr, lowValue, toLex lowNext⟩) steps = oldRoot) :
    AbsentImtGatesAtW hash dep oldRoot oldRoot (toLex kk) (toLex lowAddr) lowValue
      (toLex lowNext) :=
  ⟨xs, steps, hxlen, hsl, hor, hp,
   (Dregg2.Circuit.Emit.LexCompare8Emit.lexLt8_refines lowAddr kk hcLow hcK).mp
     ⟨envLo, hLoA, hLoB, hLoBlk⟩,
   (Dregg2.Circuit.Emit.LexCompare8Emit.lexLt8_refines kk lowNext hcK hcNext).mp
     ⟨envHi, hHiA, hHiB, hHiBlk⟩, rfl⟩

/-- **★ THE SAME, WITH NO CANONICITY HYPOTHESIS** (`absentGateW_of_lexBlocks_canon`'s repointed
twin): the blocks are read AS THE COMPARE BLOCK READS THEM, so `KeyCanon` is discharged rather than
assumed. This is the form W3 consumes. -/
theorem absentImtGateW_of_lexBlocks_canon (hash : List ℤ → ℤ) (dep : Nat) (oldRoot : ℤ)
    (envLo envHi : VmRowEnv) (lowAddr kk lowNext : Fin 8 → ℤ) (lowValue : ℤ)
    (hLoA : ∀ i : Fin 8, envLo.loc i.val = lowAddr i)
    (hLoB : ∀ i : Fin 8, envLo.loc (8 + i.val) = kk i)
    (hLoBlk : lexBlockHolds lexTf envLo)
    (hHiA : ∀ i : Fin 8, envHi.loc i.val = kk i)
    (hHiB : ∀ i : Fin 8, envHi.loc (8 + i.val) = lowNext i)
    (hHiBlk : lexBlockHolds lexTf envHi)
    (xs : List ℤ) (steps : List (Bool × ℤ))
    (hxlen : xs.length = 2 ^ dep) (hsl : steps.length = dep)
    (hor : oldRoot = perfectRoot hash dep xs)
    (hp : pathRecompute hash
      (imtLeafHash8Of hash
        ⟨toLex (canonKey lowAddr), lowValue, toLex (canonKey lowNext)⟩) steps = oldRoot) :
    AbsentImtGatesAtW hash dep oldRoot oldRoot (toLex (canonKey kk))
      (toLex (canonKey lowAddr)) lowValue (toLex (canonKey lowNext)) :=
  ⟨xs, steps, hxlen, hsl, hor, hp,
   (lexLt8_refines_canon lowAddr kk).mp ⟨envLo, hLoA, hLoB, hLoBlk⟩,
   (lexLt8_refines_canon kk lowNext).mp ⟨envHi, hHiA, hHiB, hHiBlk⟩, rfl⟩

/-- **★ THE FULL REPOINTED COMPOSITION (`absentRow_of_lexBlocks_forces_absence`).** Two satisfied
EMITTED `lexLt8` blocks + the row wiring + a committed `ImtSorted` chain + **ONE** arity-17 Merkle
path ⇒ the ROW's key, as the compare block reads it, is absent from the whole committed spine, with
no canonicity hypothesis anywhere in the chain. Note the hypothesis list against the original: no
`stepsHi`, no `hadj`, no second `pathRecompute`. -/
theorem absentImtRow_of_lexBlocks_forces_absence (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (dep : Nat) (oldRoot : ℤ) (m : MapOpW) (a : Assignment)
    (envLo envHi : VmRowEnv) (lowAddr kk lowNext : Fin 8 → ℤ) (lowValue : ℤ)
    (w : RowKeyWiredW m a envLo envHi kk)
    (hLoA : ∀ i : Fin 8, envLo.loc i.val = lowAddr i)
    (hLoBlk : lexBlockHolds lexTf envLo)
    (hHiB : ∀ i : Fin 8, envHi.loc (8 + i.val) = lowNext i)
    (hHiBlk : lexBlockHolds lexTf envHi)
    (c : List (ImtLeaf Digest8Key ℤ)) (hs : ImtSorted c) (hlen : c.length = 2 ^ dep)
    (xs : List ℤ) (steps : List (Bool × ℤ))
    (hxlen : xs.length = 2 ^ dep) (hsl : steps.length = dep)
    (hroot : oldRoot = perfectRoot hash dep (c.map (imtLeafHash8Of hash)))
    (hor : oldRoot = perfectRoot hash dep xs)
    (hp : pathRecompute hash
      (imtLeafHash8Of hash
        ⟨toLex (canonKey lowAddr), lowValue, toLex (canonKey lowNext)⟩) steps = oldRoot) :
    keyAtCanon m a ∉ imtAddrs c
      ∧ Heap.get (imtToHeapW c) (keyAtCanon m a) = none := by
  have hgate : AbsentImtGatesAtW hash dep oldRoot oldRoot (toLex (canonKey kk))
      (toLex (canonKey lowAddr)) lowValue (toLex (canonKey lowNext)) :=
    absentImtGateW_of_lexBlocks_canon hash dep oldRoot envLo envHi lowAddr kk lowNext lowValue
      hLoA w.loCol hLoBlk w.hiCol hHiB hHiBlk xs steps hxlen hsl hor hp
  have hAt : AbsentImtGatesAtW hash dep oldRoot oldRoot (keyAtCanon m a)
      (toLex (canonKey lowAddr)) lowValue (toLex (canonKey lowNext)) := by
    rw [w.keyAtCanon_eq]; exact hgate
  obtain ⟨h1, h2, _⟩ :=
    absentImtGatesW_force_row_absence hash hCR dep m a hs hlen hroot hAt
  exact ⟨h1, h2⟩

/-- **★ THE REPOINTED RESIDUE-CLASS ABSENCE (`absentGate_forces_residue_absence`).** Whatever
committed chain the extraction produced behind an accepting DEPLOYED wide `.absent` row's pre-root,
none of its addresses ALIASES the row's canonical key. The IMT-layer form of the L3 statement W3
consumes, on the shape that ships. Chain-address canonicity is the IMT layer's extraction premise,
exactly as `wideEnc.HeapOk` is the map layer's — the bracket is a raw-order fact and cannot force it
(`MapOpWideKeyCanonDischarge.gate_teeth_cannot_force_canonicity`). -/
theorem absentImtGate_forces_residue_absence (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) (m : MapOpW) (a : Assignment) {oldRoot newRoot : ℤ} {lowAddr : Digest8Key}
    {lowValue : ℤ} {lowNext : Digest8Key} {c : List (ImtLeaf Digest8Key ℤ)}
    (hs : ImtSorted c) (hlen : c.length = 2 ^ dep)
    (hroot : oldRoot = perfectRoot hash dep (c.map (imtLeafHash8Of hash)))
    (hc : ∀ x ∈ imtAddrs c, KeyCanon (ofLex x))
    (hg : AbsentImtGatesAtW hash dep oldRoot newRoot (keyAtCanon m a) lowAddr lowValue lowNext) :
    ∀ x ∈ imtAddrs c, canonKey (ofLex x) ≠ ofLex (keyAtCanon m a) := by
  have habs := (absentImtGatesW_force_row_absence hash hCR dep m a hs hlen hroot hg).1
  intro x hx heq
  have hxc : canonKey (ofLex x) = ofLex x :=
    Dregg2.Circuit.MapOpWideKeyCanonDischarge.canonKey_id (hc x hx)
  have hxeq : x = keyAtCanon m a := by
    have h1 : (ofLex x : Fin 8 → ℤ) = ofLex (keyAtCanon m a) := by rw [← hxc, heq]
    exact congrArg (toLex : (Fin 8 → ℤ) → Digest8Key) h1
  exact habs (hxeq ▸ hx)

/-- **★ THE REPOINTED `.absent` LEG OF THE JOINT-UNSAT FAMILY.** An accepting widened AAFI insert of
the 8-felt key `k` and an accepting DEPLOYED wide `.absent` row for the SAME `k` against the
resulting chain are jointly UNSAT under the single named CR floor. This is the double-spend refusal
`gates_aafiInsertW_absentW_jointly_unsat` states over the adjacency gate, restated over the shape
that ships — and it is now stated at ONE commitment (the IMT chain), because both legs open arity-17
leaves. `aafiGatesW_force_sortedChainW` supplies the post-chain sortedness the `.absent` law needs;
`aafiGatesW_force_spine_growthW` puts `k` on the post-spine. -/
theorem aafiInsertW_then_absentImtW_unsat (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep depPost : Nat) {oldRoot newRoot postRoot absNewRoot : ℤ} {k : Digest8Key} {v : ℤ}
    {lowAddr : Digest8Key} {lowValue : ℤ} {lowNext : Digest8Key} {freeEmpty : ℤ}
    {lowAddr2 : Digest8Key} {lowValue2 : ℤ} {lowNext2 : Digest8Key}
    {c : List (ImtLeaf Digest8Key ℤ)} (hs : ImtSorted c)
    (hins : AafiGatesAtW hash dep oldRoot newRoot k v lowAddr lowValue lowNext freeEmpty)
    (hlow : (⟨lowAddr, lowValue, lowNext⟩ : ImtLeaf Digest8Key ℤ) ∈ c)
    (hlenPost : (imtInsert c k v).length = 2 ^ depPost)
    (hrootPost : postRoot
      = perfectRoot hash depPost ((imtInsert c k v).map (imtLeafHash8Of hash)))
    (habs : AbsentImtGatesAtW hash depPost postRoot absNewRoot k lowAddr2 lowValue2 lowNext2) :
    False := by
  have hpost : ImtSorted (imtInsert c k v) :=
    (aafiGatesW_force_sortedChainW hash hCR dep hs hins hlow).1
  have hgrow := aafiGatesW_force_spine_growthW hash hCR dep hins hlow
  have hnotin :=
    (absentImtGatesW_force_absence hash hCR depPost hpost hlenPost hrootPost habs).1
  exact hnotin ((hgrow k).mpr (Or.inl rfl))

/-! ## §5 — NON-VACUITY IN THE TOP GAP, at the WIDE key: the slot the model cannot reach.

`MapOpWideKeyGate.forgeChain = [⟨keyLo, 1, keyE⟩, ⟨keyE, 2, ptrHi⟩]` is REUSED verbatim (it is an
honest `ImtSorted` chain — it was authored as the half-wide-pointer canary's committed object). Its
committed addresses are `[keyLo, keyE]`; its terminal pointer `ptrHi` is a `SENTINEL_MAX` FACE, not
a stored leaf. `ptrMid` sits in the top gap: `keyE < ptrMid < ptrHi`, and `ptrMid` is above BOTH
committed addresses — so the deployed pointer bracket reaches it and the adjacency model cannot.
Every path obligation closes by `rfl` over an ARBITRARY hash; the law is then fired at the CR-proved
`refSponge`. -/

section TopGapW

open Dregg2.Circuit.MapOpWideKeyGate (forgeChain forgeChain_sorted)
open Dregg2.Circuit.Poseidon2Binding.Reference (refSponge refSponge_CR)

theorem keyLo_lt_ptrMid : keyLo < ptrMid := Dregg2.Crypto.Digest8KeySpike.keyLo_lt_keyE.trans
  keyE_lt_ptrMid

/-- `ptrMid` and `ptrHi` are canonical field-keyed digests (limbs `2` and `3`), so the projected
top-gap map is an ADMISSIBLE wide commitment and the residue statement fires on it. -/
theorem ptrMid_canon : KeyCanon (ofLex ptrMid) := by
  show ∀ i : Fin 8, 0 ≤ (if i = 7 then (2 : ℤ) else 0)
    ∧ (if i = 7 then (2 : ℤ) else 0) < 2013265921
  decide

theorem ptrHi_canon : KeyCanon (ofLex ptrHi) := by
  show ∀ i : Fin 8, 0 ≤ (if i = 7 then (3 : ℤ) else 0)
    ∧ (if i = 7 then (3 : ℤ) else 0) < 2013265921
  decide

/-- The chain's committed addresses are canonical — the IMT-layer extraction premise, discharged on
this concrete chain. -/
theorem forgeChain_addrs_canon : ∀ x ∈ imtAddrs forgeChain, KeyCanon (ofLex x) := by
  intro x hx
  have hx' : x ∈ [keyLo, keyE] := hx
  rcases List.mem_cons.mp hx' with rfl | hx''
  · exact keyLo_canon
  · rw [List.mem_singleton.mp hx'']; exact keyE_canon

/-- The arity-17 committed digest vector behind the chain, and its IMT root (depth 1, two leaves —
no padding seam). -/
def topLeavesW (hash : List ℤ → ℤ) : List ℤ := forgeChain.map (imtLeafHash8Of hash)

def topRootW (hash : List ℤ → ℤ) : ℤ := perfectRoot hash 1 (topLeavesW hash)

/-- The position-1 membership path (root-first: RIGHT — `pathPos = 2^0 + 0 = 1`, the LAST leaf). -/
def topStepsW (hash : List ℤ → ℤ) : List (Bool × ℤ) :=
  [(true, imtLeafHash8Of hash ⟨keyLo, 1, keyE⟩)]

theorem topStepsW_recompute (hash : List ℤ → ℤ) :
    pathRecompute hash (imtLeafHash8Of hash ⟨keyE, 2, ptrHi⟩) (topStepsW hash) = topRootW hash :=
  rfl

/-- **★ HALF ONE — THE DEPLOYED WIDE TABLE ACCEPTS THE HONEST TOP-GAP ROW.** `ptrMid` is above
every committed 8-felt address; the last leaf's terminal pointer brackets it
(`keyE < ptrMid < ptrHi`), ONE arity-17 path authenticates the low leaf, the root is preserved.
Over an ARBITRARY hash, every obligation by `rfl`: this is an ordinary row, not a shape. -/
theorem topGapW_deployed_accepts (hash : List ℤ → ℤ) :
    AbsentImtGatesAtW hash 1 (topRootW hash) (topRootW hash) ptrMid keyE 2 ptrHi :=
  ⟨topLeavesW hash, topStepsW hash, rfl, rfl, rfl, topStepsW_recompute hash,
    keyE_lt_ptrMid, ptrMid_lt_ptrHi, rfl⟩

/-- **★ HALF TWO — THE WIDE ADJACENCY MODEL REJECTS THE SAME ROW**, at every committed heap and
every pair of paths. `ptrMid` exceeds every key of the projected map, so `AdjacentBracketGatesW` has
no witness: the hi path would have to open a committed entry above `ptrMid`. -/
theorem topGapW_model_rejects :
    ¬ AdjacentBracketGatesW refSponge 1 (mapRootW refSponge wideEnc 1 (imtToHeapW forgeChain))
        ptrMid := by
  refine adjacentBracketW_unsat_above_max refSponge refSponge_CR 1 (imtToHeapW forgeChain)
    rfl rfl ?_
  intro x hx
  rw [keys_imtToHeapW] at hx
  have hx' : x ∈ [keyLo, keyE] := hx
  rcases List.mem_cons.mp hx' with rfl | hx''
  · exact keyLo_lt_ptrMid
  · rw [List.mem_singleton.mp hx'']; exact keyE_lt_ptrMid

/-- **⚑ THE REFUSAL BELOW IS TARGETED, NOT BLANKET.** The projected top-gap map is an ADMISSIBLE
wide commitment (`wideEnc.HeapOk` = sorted AND canonically keyed), so `topGapW_reconcileGatesW_unsat`
cannot be the `aliasRoot_admits_no_gate` mechanism — the extraction premise is satisfiable at that
root and the model still has no `.absent` witness. The refusal is the BRACKET, and only the
bracket. -/
theorem topGapHeapW_ok : wideEnc.HeapOk (imtToHeapW forgeChain) :=
  heapOkW_imtToHeapW forgeChain_sorted forgeChain_addrs_canon

/-- **★ THE BLAST RADIUS, CONCRETE AT THE WIDE KEY — the epoch's `.absent` gate hypothesis is
UNSATISFIABLE on an honest deployed row.** There is NO wide gate data, at any admissible heap and
any paths, for the top-gap row the deployed table accepts. Every theorem whose hypothesis is
`ReconcileGatesAtW … .absent` (and, by `MapOpWideKeyGate.narrow_gates_is_instance`, every one whose
hypothesis is `ReconcileGatesAt … .absent`) therefore says NOTHING about these rows. -/
theorem topGapW_reconcileGatesW_unsat (v r' : ℤ) :
    ¬ ReconcileGatesAtW refSponge wideEnc 1
        (mapRootW refSponge wideEnc 1 (imtToHeapW forgeChain)) ptrMid v r'
        MapOpKind.absent := by
  rintro ⟨h, hok, hlen, hroot, hgb, -⟩
  have hh : h = imtToHeapW forgeChain :=
    mapRootW_injective refSponge refSponge_CR wideEnc 1 hlen rfl hroot
  refine adjacentBracketW_unsat_above_max refSponge refSponge_CR 1 h hlen hroot ?_ hgb
  intro x hx
  rw [hh, keys_imtToHeapW] at hx
  have hx' : x ∈ [keyLo, keyE] := hx
  rcases List.mem_cons.mp hx' with rfl | hx''
  · exact keyLo_lt_ptrMid
  · rw [List.mem_singleton.mp hx'']; exact keyE_lt_ptrMid

/-- **★ RESPECTING TOOTH — THE REPOINTED WIDE LAW FIRES on the row the model cannot see.** The
shipped pointer-bracket gate plus the named `ImtSorted` premise forces `ptrMid` off the whole
committed 8-felt spine and `Heap.get` to be `none` on the projected map. -/
theorem topGapW_deployed_law_fires :
    ptrMid ∉ imtAddrs forgeChain
      ∧ Heap.get (imtToHeapW forgeChain) ptrMid = none
      ∧ topRootW refSponge = topRootW refSponge :=
  absentImtGatesW_force_absence refSponge refSponge_CR 1 forgeChain_sorted rfl rfl
    (topGapW_deployed_accepts refSponge)

/-- **★ …AND SO DOES THE REPOINTED WELD RESULT, in the top gap.** The `keysOfW` form — the predicate
the whole Wide8 wrapper layer speaks in — fires at the chain's projected map root on the very slot
the adjacency model has no witness for. This is the point of the repointing, on a concrete row. -/
theorem topGapW_keysOfW_absence_fires :
    ptrMid ∉ keysOfW (opensAtW refSponge wideEnc 1)
        (mapRootW refSponge wideEnc 1 (imtToHeapW forgeChain))
      ∧ topRootW refSponge = topRootW refSponge :=
  absentImtGatesW_force_keysOfW_absence refSponge refSponge_CR 1 1 forgeChain_sorted rfl rfl
    rfl forgeChain_addrs_canon (topGapW_deployed_accepts refSponge)

/-- The top-gap `.absent` ROW at the wide key: a real `MapOpW` whose eight key columns carry
`ptrMid`'s cells (`MapOpWideKeyRowBoundary.rowOfKey`, the epoch's own non-vacuity vehicle). -/
def topGapRowW : MapOpW :=
  Dregg2.Circuit.MapOpWideKeyRowBoundary.rowOfKey ptrMid MapOpKind.absent

theorem topGapRowW_keyAtCanon (a : Assignment) : keyAtCanon topGapRowW a = ptrMid :=
  Dregg2.Circuit.MapOpWideKeyRowBoundary.rowOfKey_keyAtCanon_of_canon ptrMid_canon _ a

private theorem topGapRowW_gate (a : Assignment) :
    AbsentImtGatesAtW refSponge 1 (topRootW refSponge) (topRootW refSponge)
      (keyAtCanon topGapRowW a) keyE 2 ptrHi := by
  rw [topGapRowW_keyAtCanon]
  exact topGapW_deployed_accepts refSponge

/-- **★ THE REPOINTED ROW-LEVEL ABSENCE FIRES IN THE TOP GAP.** A real widened `.absent` row, its
key read exactly as the emitted compare block reads it, on the slot the adjacency model cannot
reach. -/
theorem topGapW_row_absence_fires (a : Assignment) :
    keyAtCanon topGapRowW a ∉ imtAddrs forgeChain
      ∧ Heap.get (imtToHeapW forgeChain) (keyAtCanon topGapRowW a) = none
      ∧ topRootW refSponge = topRootW refSponge :=
  absentImtGatesW_force_row_absence refSponge refSponge_CR 1 topGapRowW a
    forgeChain_sorted rfl rfl (topGapRowW_gate a)

/-- **★ THE REPOINTED RESIDUE-CLASS ABSENCE FIRES IN THE TOP GAP** — no committed address of the
chain aliases the row's canonical key, on the same slot. -/
theorem topGapW_residue_absence_fires (a : Assignment) :
    ∀ x ∈ imtAddrs forgeChain, canonKey (ofLex x) ≠ ofLex (keyAtCanon topGapRowW a) :=
  absentImtGate_forces_residue_absence refSponge refSponge_CR 1 topGapRowW a
    forgeChain_sorted rfl rfl forgeChain_addrs_canon (topGapRowW_gate a)

/-- **★ THE REPOINTED `HoldsKindW` `.absent` LEG FIRES IN THE TOP GAP** — the denotation the whole
Wide8 wrapper layer consumes, delivered at the chain's projected map root by the shipped gate. -/
theorem topGapW_holdsKindW_fires (v : ℤ) :
    HoldsKindW (opensAtW refSponge wideEnc 1)
      (mapRootW refSponge wideEnc 1 (imtToHeapW forgeChain))
      (mapRootW refSponge wideEnc 1 (imtToHeapW forgeChain)) ptrMid v MapOpKind.absent :=
  imtGates_force_holdsKindW_absent refSponge refSponge_CR 1 1 v forgeChain_sorted rfl rfl rfl
    forgeChain_addrs_canon (topGapW_deployed_accepts refSponge)

/-- **★ ANTI-GHOST — a PRESENT 8-felt key admits NO deployed wide gate data.** For ANY claimed low
leaf and ANY claimed post-root, the shipped wide gate cannot open `keyE` (which the chain HOLDS) as
absent. The repointed model is not vacuously accepting. -/
theorem present_keyW_has_no_deployed_gate (newRoot : ℤ) (lowAddr lowNext : Digest8Key)
    (lowValue : ℤ) :
    ¬ AbsentImtGatesAtW refSponge 1 (topRootW refSponge) newRoot keyE lowAddr lowValue lowNext :=
  fun hg =>
    (absentImtGatesW_force_absence refSponge refSponge_CR 1 forgeChain_sorted rfl rfl hg).1
      keyE_present_in_forgeChain

/-- **★ THE MISMATCH AND ITS REPAIR, in one statement at the WIDE key.** On ONE logical map, for ONE
honest absent 8-felt key in the top gap: the deployed wide table ACCEPTS, the wide adjacency model
has NO witness, the epoch's `ReconcileGatesAtW` `.absent` hypothesis is FALSE, and the repointed law
delivers the absence anyway — both at the chain and at the wrapper layer's `keysOfW`. -/
theorem absentW_model_is_incomplete_at_the_top_gap (v r' : ℤ) :
    AbsentImtGatesAtW refSponge 1 (topRootW refSponge) (topRootW refSponge) ptrMid keyE 2 ptrHi ∧
    ¬ AdjacentBracketGatesW refSponge 1
        (mapRootW refSponge wideEnc 1 (imtToHeapW forgeChain)) ptrMid ∧
    ¬ ReconcileGatesAtW refSponge wideEnc 1
        (mapRootW refSponge wideEnc 1 (imtToHeapW forgeChain)) ptrMid v r' MapOpKind.absent ∧
    ptrMid ∉ imtAddrs forgeChain ∧
    ptrMid ∉ keysOfW (opensAtW refSponge wideEnc 1)
        (mapRootW refSponge wideEnc 1 (imtToHeapW forgeChain)) :=
  ⟨topGapW_deployed_accepts refSponge, topGapW_model_rejects, topGapW_reconcileGatesW_unsat v r',
   topGapW_deployed_law_fires.1, topGapW_keysOfW_absence_fires.1⟩

/-- The INTERIOR agrees, on the same wide chain: `keyE`'s own pointer `ptrHi` — no; the interior low
leaf is position 0, whose pointer `keyE` IS position 1's address, so there the deployed bracket and
the model's adjacency bracket are the same condition (`interiorW_pointerBracket_iff_adjacent`
instantiated). -/
theorem interiorW_agrees (k : Digest8Key) :
    ((⟨keyLo, 1, keyE⟩ : ImtLeaf Digest8Key ℤ).addr < k
        ∧ k < (⟨keyLo, 1, keyE⟩ : ImtLeaf Digest8Key ℤ).nextAddr) ↔
      ((⟨keyLo, 1, keyE⟩ : ImtLeaf Digest8Key ℤ).addr < k
        ∧ k < (⟨keyE, 2, ptrHi⟩ : ImtLeaf Digest8Key ℤ).addr) :=
  interiorW_pointerBracket_iff_adjacent forgeChain_sorted (p := 0) rfl rfl k

end TopGapW

/-! ## §6 — AXIOM HYGIENE. -/

#assert_axioms absentImtGatesW_bind_low
#assert_axioms absentImtGatesW_force_imtAbsentW
#assert_axioms absentImtGatesW_force_absence
#assert_axioms imtLeafHash8Of_ne_leafOfW
#assert_axioms adjacentBracketGatesW_is_model_body
#assert_axioms adjacentBracketW_forces_committed_pair
#assert_axioms adjacentBracketW_unsat_above_max
#assert_axioms interiorW_pointerBracket_iff_adjacent
#assert_axioms interiorW_bracket_gives_adjacent_pair
#assert_axioms absentImtGatesW_force_keysOfW_absence
#assert_axioms imtGates_force_holdsKindW_absent
#assert_axioms absentImtGatesW_force_row_absence
#assert_axioms absentImtGateW_of_lexBlocks
#assert_axioms absentImtGateW_of_lexBlocks_canon
#assert_axioms absentImtRow_of_lexBlocks_forces_absence
#assert_axioms absentImtGate_forces_residue_absence
#assert_axioms aafiInsertW_then_absentImtW_unsat
#assert_axioms topGapW_deployed_accepts
#assert_axioms topGapW_model_rejects
#assert_axioms topGapHeapW_ok
#assert_axioms topGapW_reconcileGatesW_unsat
#assert_axioms topGapW_deployed_law_fires
#assert_axioms topGapW_keysOfW_absence_fires
#assert_axioms topGapW_row_absence_fires
#assert_axioms topGapW_residue_absence_fires
#assert_axioms topGapW_holdsKindW_fires
#assert_axioms present_keyW_has_no_deployed_gate
#assert_axioms absentW_model_is_incomplete_at_the_top_gap
#assert_axioms interiorW_agrees

end Dregg2.Circuit.MapAbsentImtGateWide
