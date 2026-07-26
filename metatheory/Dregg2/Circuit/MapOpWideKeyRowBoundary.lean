/-
# Dregg2.Circuit.MapOpWideKeyRowBoundary — the WELD's gate-forced results READ OFF A REAL ROW,
  through `keyAtCanon`. The row boundary of the wide-MapOp-key epoch, closed — and the NEXT
  boundary down, named and canaried.

**This is Lean-authored AIR.** Nothing here is a new constraint; it is the composition point
between two existing Lean objects.

## The gap this closes (as the canonicity lane stated it)

`MapOpWideKeyWeld`'s gate-forced results (`absentGatesW_force_keysOfW_absence`,
`gates_insertW_absentW_jointly_unsat` + its `.aafiInsert` twin, the per-kind
`gates_force_holdsKindW_*`) speak in an ABSTRACT `k : K`. `keyAt` and `keyAtCanon` appear ZERO
times in that file. The point where `k` gets read off an actual trace row is
`MapOpWideKeyGate.gatesAtW` / `holdsAtW`, and BOTH read the row's key with `MapOpW.keyAt` — the
RAW reading of eight ℤ cells. `MapOpWideKeyCanonDischarge` proved (`gate_teeth_cannot_force_canonicity`,
`lexBlock_invariant_under_p_shift`) that `KeyCanon` on a raw cell is not derivable from the emitted
object and cannot be made so by adding teeth; so a row-level statement phrased at `MapOpW.keyAt`
re-imports exactly the hypothesis that lane deleted. **That located site is the gap.**

## What the row-level composition is

`RowKeyWiredW m a envLo envHi kk` is the W3 wiring obligation as one proposition: the row's eight
key columns ARE the a-side key cells of the HIGH compare block (`wire` + `hiCol`) and the b-side
cells of the LOW one (`loCol`) — and `RowKeyWiredW.wireLo` DERIVES that the same row key feeds both
blocks, so the two brackets are provably about one key rather than two. From it,
`RowKeyWiredW.keyAtCanon_eq` (`keyAtCanon_of_block`, composed) gives

    keyAtCanon m a = toLex (canonKey kk)

with NO hypothesis on the row's cells, and every weld result gains a row-level form at that key:

  * `absentGatesW_force_row_absence` / ★ `absentRow_of_lexBlocks_forces_absence` — the latter is the
    WHOLE composition: two satisfied emitted `lexLt8` blocks + the row wiring + a committed heap +
    two adjacent Merkle paths ⇒ the ROW's key, as the compare block reads it, is absent from the
    gate's own committed key set. The `.absent` gate is BUILT here, not assumed.
  * `gates_force_holdsKindW_{absent,read,insert,aafiInsert}_row` and the row denotation
    `holdsAtWCanon`, forced by `gatesAtWCanon` (`mapOpW_gatesCanon_force_holdsCanon`).
  * `gates_insertW_absentW_jointly_unsat_row` (+ `.aafiInsert` twin, + the `via_abstract` routings)
    — the double-spend refusal between two ROWS whose CANONICAL keys agree.
  * `aafiGatesW_no_rewitnessW_row` — the chain-level refusal at the row's canonical key.

The abstract versions are untouched and still exported by the weld; these are the primary ones for
W3.

## Agree where they should, differ where they must

  * `readings_agree` — on a row whose key cells are canonical, `keyAtCanon m a = m.keyAt a`
    (`keyAtCanon_eq_keyAt`, verified and reused). The discharge costs a deployed row nothing.
  * `gatesAtWCanon_eq_gatesAtW` — hence at canonical cells the canonical row gate IS
    `MapOpWideKeyGate.gatesAtW`. Nothing downstream changes meaning on an honest row.
  * ⚑ `forgeRow_readings_differ` — the row whose lane-0 cell is `p + 5` reads `5` canonically and
    `p + 5` raw: two DIFFERENT keys. `keyAtCanon_row_isCanon` says the canonical reading always
    lands in `[0, p)`; `forgeRow_cells_not_canon` says the raw one need not.
  * ⚑⚑ `rowRawBracketClaim_false` — `RowRawBracketClaim` is the row-level bracket weld VERBATIM with
    the conclusion read at `MapOpW.keyAt` instead of `keyAtCanon`. It is FALSE, and the refutation
    is `MapOpWideKeyCanonDischarge.rawBracketClaim_false`'s own trace lifted to a row
    (`rowOfKey (toLex forgeKk)`): the row-level raw statement proves the key `p + 5` ABSENT from a
    chain that PRESENTS it. `forgeRow_canon_survives` is the same row's canonical statement, TRUE.
    So routing through `keyAtCanon` is load-bearing at the row boundary, not stylistic.

## ⚑ L3 — the WITNESS boundary, now CLOSED BY DEFINITION (and what that cost)

Composing the weld at the row surfaced the NEXT unforced hypothesis one level down, at the
extraction premise rather than the trace row: `ReconcileGatesAtW` opened with `∃ h : List (K × ℤ)`
and nothing made that heap's KEYS canonical, so `heapAlias_row_absence_is_not_residue_absence`
exhibited a REAL accepting widened `.absent` gate over `[0 ↦ 1, (p+5) ↦ 1]` whose forced absence of
`5` coexisted with a committed key aliasing `5`.

That is now cured in `MapOpWideKeyGate`, non-additively: `LaneEnc` carries the admissible
committed-heap shape as a FIELD (`HeapOk`), `opensToMerkleW`/`writesToMerkleW`/`ReconcileGatesAtW`
quantify over it, and `wideEnc.HeapOk = Heap.SortedKeys ∧ CanonHeapW`. §6 records the consequences:
`row_absence_is_residue_absence_of_canonHeap` LOSES its canonicity hypothesis,
`absentGate_forces_residue_absence` is the hypothesis-free form W3 consumes, and
⚑ `aliasRoot_admits_no_gate` says the alias root now admits NO widened gate at all — the old
counterexample is unconstructible, kept as that `¬`-form plus its intact evidence
(`aliasHeap_not_canon`, `aliasHeap_not_heapOk`). `canonAliasRoot_refuses_absence_of_five` is the
discrimination side: the CANONICAL twin heap is admissible and refuses for the honest reason.

⚠ Status, stated plainly: `CanonHeapW` did not become gate-FORCED (it cannot —
`gate_teeth_cannot_force_canonicity`), it became DEFINITIONAL, sitting exactly where
`Heap.SortedKeys` already sat. `narrowEnc.HeapOk` is definitionally `Heap.SortedKeys`, so every
conservativity `rfl` to the deployed narrow objects survived.

## ⚑⚑⚑ §9 — QUESTION ZERO: the DEPLOYED narrow map-op has the SAME alias hole

`narrowAliasGate_accepts` / `narrow_deployed_alias_hole` build the construction at
`MapOpsColumnLayout.ReconcileGatesAt` and `MapMerkleRoot.opensToMerkle` — the deployed, ℤ-keyed
objects, nothing widened — and `deployed_narrow_heapOk_is_only_sortedness` (a `rfl`) shows the
deployed extraction premise says nothing about canonical keys. CLASSIFICATION: **(ii) a model-level
artifact**, not a deployed wound; §9's header carries the full argument, and
`residueBlind_collapses_alias` + `residueBlind_refutes_spongeCR` are its decisive half — the alias
root differs from the canonical root only for a hash that separates residues, which is precisely the
capability `Poseidon2Binding` already records the deployed sponge as NOT having.

## Non-vacuity

Every row-level statement fires on the epoch's existing concrete accepting rows —
`demoAbsentGateW_accepts`, `demoValueUpdateGateW_accepts`, `demoAafiGateW_accepts`,
`demoAbsentGateW2_accepts`, `demo_concrete_excludes` — through `rowOfKey`, which builds a real
`MapOpW` whose eight key columns are the constant cells of a given key.

## Floors

`Poseidon2SpongeCR` ONLY, and only where the weld already carried it. NO new floor. The canonical
reading is arithmetic (`% p`); the compare block's content is structural.

## Byte safety

No descriptor, emit, golden or JSON byte is touched. No `sorry`/`admit`/`native_decide`.
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. `ResidueBlindLeaf` (§9a) is a
theorem HYPOTHESIS, never a floor: no keystone depends on it, and it is a property the deployed
sponge has by construction rather than a hardness assumption.
-/
import Dregg2.Circuit.MapOpWideKeyWeld
import Dregg2.Circuit.MapOpWideKeyCanonDischarge

namespace Dregg2.Circuit.MapOpWideKeyRowBoundary

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2 (MapOpKind)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.Emit.LexCompare8Emit (lexBlockHolds lexTf)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.MapOpsColumnLayout (pathPos pathRecompute)
open Dregg2.Circuit.IndexedMerkleTree (ImtLeaf ImtSorted ImtAbsent imtAddrs imtInsert)
open Dregg2.Crypto.Digest8KeySpike (Digest8Key keyLo keyE keyHi)
open Dregg2.Circuit.SortedTreeNonMembershipWide8 (keysOfW)
open Dregg2.Circuit.MapOpWideKey (KeyCanon MapOpW HoldsKindW)
open Dregg2.Circuit.MapOpWideKeyGate (wideEnc CanonHeapW heapOk_canon leafOfW mapRootW
  mapRootW_injective opensToMerkleW opensToMerkleW_functional ReconcileGatesW
  ReconcileGatesAtW AafiGatesAtW gatesAtW demoRootW demoAbsentGateW_accepts)
open Dregg2.Circuit.MapMerkleRoot (mapRoot mapRoot_injective opensToMerkle
  opensToMerkle_functional)
open Dregg2.Circuit.MapOpsColumnLayout (ReconcileGatesAt reconcileGates_force_opening)
open Dregg2.Circuit.DescriptorIR2 (MapOp)
open Dregg2.Circuit.MapOpWideKeyWeld (opensAtW keysOfW_opensAtW absentGatesW_force_keysOfW_absence
  gates_force_holdsKindW_absent gates_force_holdsKindW_read gates_force_holdsKindW_insert
  gates_force_holdsKindW_aafiInsert gates_insertW_absentW_jointly_unsat
  gates_aafiInsertW_absentW_jointly_unsat gates_jointly_unsat_via_abstract
  gates_jointly_unsat_via_abstract' aafiGatesW_no_rewitnessW aafiGatesW_force_sortedChainW
  imtToHeapW demoRootW2 demoValueUpdateGateW_accepts demoAbsentGateW2_accepts demo_concrete_excludes
  demoAafiChainW demoAafiChainW_sorted demoAafiChainW_low_mem demoAafiGateW_accepts)
open Dregg2.Circuit.MapOpWideKeyCanonDischarge (canonFelt canonKey canonKey_isCanon canonKey_id
  canonKey_idem keyAtCanon keyAtCanon_eq_keyAt keyAtCanon_of_block absentGateW_of_lexBlocks_canon
  absentBracket_of_lexBlocks_canon forgeLow forgeKk forgeNext forgeChain forgeChain_sorted
  forgeLow_leaf_mem forgeKk_present forge_blocks_hold forge_readings_differ forgeKk_canon0
  canon_weld_survives forgeLow_canon forgeNext_canon)
open Dregg2.Substrate

set_option autoImplicit false

/-! ## §1 — THE ROW BOUNDARY: the row's key, as the emitted compare block reads it. -/

/-- **`RowKeyWiredW m a envLo envHi kk`** — the W3 wiring obligation for ONE widened `.absent` row,
as a proposition. The row's eight key columns are the a-side key cells of the HIGH compare block
(`wire` composed with `hiCol`) and the b-side cells of the LOW one (`loCol`). This is exactly what
the emit must arrange — the SAME columns into the block and into the map-op key group — and it is
the only thing `keyAtCanon_of_block` needs. -/
structure RowKeyWiredW (m : MapOpW) (a : Assignment) (envLo envHi : VmRowEnv)
    (kk : Fin 8 → ℤ) : Prop where
  /-- The LOW bracket compares `low.addr < k`: the queried key sits on its b-side, columns 8..15. -/
  loCol : ∀ i : Fin 8, envLo.loc (8 + i.val) = kk i
  /-- The HIGH bracket compares `k < low.next`: the queried key sits on its a-side, columns 0..7. -/
  hiCol : ∀ i : Fin 8, envHi.loc i.val = kk i
  /-- The ROW's key group feeds the high block's a-side columns. -/
  wire : ∀ i : Fin 8, (m.key i).eval a = envHi.loc i.val

/-- **★ THE ROW BOUNDARY, CROSSED WITHOUT A HYPOTHESIS.** Under the wiring, the row's key AS THE
COMPARE BLOCK READS IT is `toLex (canonKey kk)` — the exact key every `*_canon` weld result speaks
in. No `KeyCanon` on the row's cells: `keyAtCanon` is a total reading, not a guarded one. -/
theorem RowKeyWiredW.keyAtCanon_eq {m : MapOpW} {a : Assignment} {envLo envHi : VmRowEnv}
    {kk : Fin 8 → ℤ} (w : RowKeyWiredW m a envLo envHi kk) :
    keyAtCanon m a = toLex (canonKey kk) :=
  keyAtCanon_of_block m a envHi kk w.hiCol w.wire

/-- **The two brackets are about ONE key — derived, not assumed.** The wiring pins only the HIGH
block's a-side to the row; that the LOW block's b-side carries the same cells follows. Without this
the emit could feed two different keys to the two compares and still satisfy both blocks. -/
theorem RowKeyWiredW.wireLo {m : MapOpW} {a : Assignment} {envLo envHi : VmRowEnv}
    {kk : Fin 8 → ℤ} (w : RowKeyWiredW m a envLo envHi kk) :
    ∀ i : Fin 8, (m.key i).eval a = envLo.loc (8 + i.val) := by
  intro i
  rw [w.wire i, w.hiCol i, w.loCol i]

/-- **The canonical row key is ALWAYS canonical** — `KeyCanon` at the row boundary is a theorem, for
every row and every assignment. This is what makes the row-level statements hypothesis-free. -/
theorem keyAtCanon_row_isCanon (m : MapOpW) (a : Assignment) :
    KeyCanon (ofLex (keyAtCanon m a)) :=
  canonKey_isCanon _

/-- **AGREE.** On a row whose key cells are canonical the two readings COINCIDE — an honest
deployed row loses nothing to the discharge. (`keyAtCanon_eq_keyAt`, verified and reused.) -/
theorem readings_agree (m : MapOpW) (a : Assignment)
    (h : KeyCanon fun i : Fin 8 => (m.key i).eval a) : keyAtCanon m a = m.keyAt a :=
  keyAtCanon_eq_keyAt m a h

/-! ### §1a — `rowOfKey`: a real widened row at a given key (the non-vacuity vehicle). -/

/-- **`rowOfKey k op`** — a widened map-op row whose eight key columns are the CONSTANT cells of
`k`. A real `MapOpW`, not a shape: `keyAt` and `keyAtCanon` both compute on it by `rfl`. -/
def rowOfKey (k : Digest8Key) (op : MapOpKind) : MapOpW where
  guard := .const 1
  root := fun _ => .const 0
  key := fun i => .const (ofLex k i)
  value := .const 0
  newRoot := fun _ => .const 0
  op := op

theorem rowOfKey_keyAt (k : Digest8Key) (op : MapOpKind) (a : Assignment) :
    (rowOfKey k op).keyAt a = k := rfl

theorem rowOfKey_keyAtCanon (k : Digest8Key) (op : MapOpKind) (a : Assignment) :
    keyAtCanon (rowOfKey k op) a = toLex (canonKey (ofLex k)) := rfl

/-- On a canonical key the row reads it back exactly, either way. -/
theorem rowOfKey_keyAtCanon_of_canon {k : Digest8Key} (h : KeyCanon (ofLex k)) (op : MapOpKind)
    (a : Assignment) : keyAtCanon (rowOfKey k op) a = k := by
  rw [rowOfKey_keyAtCanon, canonKey_id h]
  rfl

/-- The row's key columns really carry the key's cells (the wiring side of `rowOfKey`). -/
theorem rowOfKey_cells (k : Digest8Key) (op : MapOpKind) (a : Assignment) (i : Fin 8) :
    ((rowOfKey k op).key i).eval a = ofLex k i := rfl

/-- **`rowOfVars op`** — the row the EMIT actually produces: its eight key columns ARE the trace
columns `0..7`, i.e. literally the a-side key group of the high compare block. `rowOfKey`'s constant
cells make the wiring trivially satisfiable; this one makes it the real column-SHARING obligation,
so every statement fired on it is a statement about a row that reads the block's own columns. -/
def rowOfVars (op : MapOpKind) : MapOpW where
  guard := .const 1
  root := fun _ => .const 0
  key := fun i => .var i.val
  value := .const 0
  newRoot := fun _ => .const 0
  op := op

/-- The column-sharing row IS wired to any block pair whose key cells agree — `wire` is `rfl`
because the row and the block name the SAME columns. -/
theorem rowOfVars_wired (op : MapOpKind) (envLo envHi : VmRowEnv) (kk : Fin 8 → ℤ)
    (hlo : ∀ i : Fin 8, envLo.loc (8 + i.val) = kk i)
    (hhi : ∀ i : Fin 8, envHi.loc i.val = kk i) :
    RowKeyWiredW (rowOfVars op) envHi.loc envLo envHi kk :=
  ⟨hlo, hhi, fun _ => rfl⟩

theorem rowOfVars_keyAt (op : MapOpKind) (a : Assignment) :
    (rowOfVars op).keyAt a = toLex (fun i : Fin 8 => a i.val) := rfl

theorem rowOfVars_keyAtCanon (op : MapOpKind) (a : Assignment) :
    keyAtCanon (rowOfVars op) a = toLex (canonKey fun i : Fin 8 => a i.val) := rfl

/-! ### §1b — ⚑ DIFFER: the non-canonical row where the two readings are different keys. -/

/-- ⚑ **THE NON-CANONICAL ROW.** Its lane-0 key column carries `p + 5` — residue `5`, raw value
above the modulus. This is `MapOpWideKeyCanonDischarge`'s `forgeKk` at the row boundary. -/
def forgeRow : MapOpW := rowOfKey (toLex forgeKk) MapOpKind.absent

/-- The canonical reading of that row is the key `5`; the raw reading is the key `p + 5`. -/
theorem forgeRow_keyAtCanon (a : Assignment) :
    keyAtCanon forgeRow a = toLex (canonKey forgeKk) := rfl

theorem forgeRow_keyAt (a : Assignment) : forgeRow.keyAt a = toLex forgeKk := rfl

/-- ⚑ **THE TWO READINGS ARE DIFFERENT KEYS ON THIS ROW** (`forge_readings_differ`, at the row). -/
theorem forgeRow_readings_differ (a : Assignment) : keyAtCanon forgeRow a ≠ forgeRow.keyAt a :=
  forge_readings_differ

/-- …and the row's cells are genuinely NOT canonical, so `readings_agree` does not apply — the
divergence is not an artifact of a degenerate row. -/
theorem forgeRow_cells_not_canon (a : Assignment) :
    ¬ KeyCanon fun i : Fin 8 => (forgeRow.key i).eval a := by
  intro h
  have h0 := (h 0).2
  have : (2013265926 : ℤ) < 2013265921 := h0
  omega

/-! ## §2 — THE ROW DENOTATION AND GATE AT THE CANONICAL READING.

`MapOpWideKeyGate.gatesAtW` / `holdsAtW` read the row key with `MapOpW.keyAt`. That is the located
re-import site; the twins below are the same objects at `keyAtCanon`. -/

/-- **`gatesAtWCanon`** — the widened gate acceptance for a row's evaluated columns, with the key
read AS THE COMPARE BLOCK READS IT. The `keyAtCanon` twin of `MapOpWideKeyGate.gatesAtW`. -/
def gatesAtWCanon (hash : List ℤ → ℤ) (dep : Nat) (a : Assignment) (m : MapOpW) : Prop :=
  ReconcileGatesAtW hash wideEnc dep ((m.root 0).eval a) (keyAtCanon m a) (m.value.eval a)
    ((m.newRoot 0).eval a) m.op

/-- **`holdsAtWCanon`** — the widened per-row denotation at the CONCRETE opening predicate, keyed
canonically: the `HoldsKindW` the whole Wide8 wrapper layer speaks in, about THIS row. -/
def holdsAtWCanon (hash : List ℤ → ℤ) (dep : Nat) (env : VmRowEnv) (m : MapOpW) : Prop :=
  m.guard.eval env.loc = 1 →
    HoldsKindW (opensAtW hash wideEnc dep) ((m.root 0).eval env.loc)
      ((m.newRoot 0).eval env.loc) (keyAtCanon m env.loc) (m.value.eval env.loc) m.op

/-- **AGREE, AT THE GATE.** On canonical key cells the canonical row gate IS the deployed-shaped
`MapOpWideKeyGate.gatesAtW`. Nothing downstream changes meaning on an honest row. -/
theorem gatesAtWCanon_eq_gatesAtW (hash : List ℤ → ℤ) (dep : Nat) (a : Assignment) (m : MapOpW)
    (h : KeyCanon fun i : Fin 8 => (m.key i).eval a) :
    gatesAtWCanon hash dep a m = gatesAtW hash dep a m := by
  show ReconcileGatesAtW hash wideEnc dep _ (keyAtCanon m a) _ _ _
    = ReconcileGatesAtW hash wideEnc dep _ (m.keyAt a) _ _ _
  rw [readings_agree m a h]

/-! ## §3 — THE WELD'S GATE-FORCED RESULTS, IN ROW-LEVEL FORM. -/

section Row

/-- **★ THE ROW-LEVEL ABSENCE.** An accepting widened `.absent` gate at the ROW's key — as the
compare block reads it — forces that key absent from the gate's own committed key set. The abstract
`absentGatesW_force_keysOfW_absence` at the one instantiation a trace row can supply. -/
theorem absentGatesW_force_row_absence (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) (m : MapOpW) (a : Assignment) (r v r' : ℤ)
    (hg : ReconcileGatesAtW hash wideEnc dep r (keyAtCanon m a) v r' MapOpKind.absent) :
    keyAtCanon m a ∉ keysOfW (opensAtW hash wideEnc dep) r ∧ r' = r :=
  absentGatesW_force_keysOfW_absence hash hCR wideEnc dep r (keyAtCanon m a) v r' hg

/-- The `.absent` leg of `HoldsKindW` at the row's canonical key. -/
theorem gates_force_holdsKindW_absent_row (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) (m : MapOpW) (a : Assignment) (r v r' : ℤ)
    (hg : ReconcileGatesAtW hash wideEnc dep r (keyAtCanon m a) v r' MapOpKind.absent) :
    HoldsKindW (opensAtW hash wideEnc dep) r r' (keyAtCanon m a) v MapOpKind.absent :=
  gates_force_holdsKindW_absent hash hCR wideEnc dep r (keyAtCanon m a) v r' hg

/-- The `.read` leg of `HoldsKindW` at the row's canonical key. -/
theorem gates_force_holdsKindW_read_row (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) (m : MapOpW) (a : Assignment) (r v r' : ℤ)
    (hg : ReconcileGatesAtW hash wideEnc dep r (keyAtCanon m a) v r' MapOpKind.read) :
    HoldsKindW (opensAtW hash wideEnc dep) r r' (keyAtCanon m a) v MapOpKind.read :=
  gates_force_holdsKindW_read hash hCR wideEnc dep r (keyAtCanon m a) v r' hg

/-- The `.insert` leg of `HoldsKindW` at the row's canonical key. -/
theorem gates_force_holdsKindW_insert_row (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) (m : MapOpW) (a : Assignment) (r v r' : ℤ)
    (hg : ReconcileGatesAtW hash wideEnc dep r (keyAtCanon m a) v r' MapOpKind.insert) :
    HoldsKindW (opensAtW hash wideEnc dep) r r' (keyAtCanon m a) v MapOpKind.insert :=
  gates_force_holdsKindW_insert hash hCR wideEnc dep r (keyAtCanon m a) v r' hg

/-- The `.aafiInsert` leg of `HoldsKindW` at the row's canonical key. -/
theorem gates_force_holdsKindW_aafiInsert_row (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) (m : MapOpW) (a : Assignment) (r v r' : ℤ)
    (hg : ReconcileGatesAtW hash wideEnc dep r (keyAtCanon m a) v r' MapOpKind.aafiInsert) :
    HoldsKindW (opensAtW hash wideEnc dep) r r' (keyAtCanon m a) v MapOpKind.aafiInsert :=
  gates_force_holdsKindW_aafiInsert hash hCR wideEnc dep r (keyAtCanon m a) v r' hg

/-- **★ THE ROW LAW AT THE CANONICAL READING.** An accepting `gatesAtWCanon` row forces
`holdsAtWCanon` — the `keyAtCanon` twin of `MapOpWideKeyGate.mapOpW_gates_force_holds`, now landing
in the CONCRETE opening predicate the weld supplies rather than an abstract `Opens`. -/
theorem mapOpW_gatesCanon_force_holdsCanon (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (dep : Nat) (env : VmRowEnv) (m : MapOpW)
    (hg : gatesAtWCanon hash dep env.loc m) : holdsAtWCanon hash dep env m := by
  intro _
  have hg' : ReconcileGatesAtW hash wideEnc dep ((m.root 0).eval env.loc)
      (keyAtCanon m env.loc) (m.value.eval env.loc) ((m.newRoot 0).eval env.loc) m.op := hg
  show HoldsKindW (opensAtW hash wideEnc dep) ((m.root 0).eval env.loc)
    ((m.newRoot 0).eval env.loc) (keyAtCanon m env.loc) (m.value.eval env.loc) m.op
  cases hop : m.op with
  | read =>
      rw [hop] at hg'
      exact gates_force_holdsKindW_read_row hash hCR dep m env.loc _ _ _ hg'
  | absent =>
      rw [hop] at hg'
      exact gates_force_holdsKindW_absent_row hash hCR dep m env.loc _ _ _ hg'
  | insert =>
      rw [hop] at hg'
      exact gates_force_holdsKindW_insert_row hash hCR dep m env.loc _ _ _ hg'
  | aafiInsert =>
      rw [hop] at hg'
      exact gates_force_holdsKindW_aafiInsert_row hash hCR dep m env.loc _ _ _ hg'
  | write => trivial

/-- **★ THE DOUBLE-SPEND REFUSAL BETWEEN TWO ROWS (`.insert`).** Two accepting widened rows whose
CANONICAL keys agree — an insert moving `r → r'` and an `.absent` against `r'` — are jointly UNSAT.
The key equality is at `keyAtCanon`, which is the equality the deployed field-element columns
induce; stating it at `MapOpW.keyAt` would let `k` and `k + p` evade the refusal. -/
theorem gates_insertW_absentW_jointly_unsat_row (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (dep : Nat) (r r' v v' : ℤ) (mI mA : MapOpW)
    (aI aA : Assignment) (hkey : keyAtCanon mI aI = keyAtCanon mA aA)
    (hins : ReconcileGatesAtW hash wideEnc dep r (keyAtCanon mI aI) v r' MapOpKind.insert)
    (habs : ReconcileGatesAtW hash wideEnc dep r' (keyAtCanon mA aA) v' r' MapOpKind.absent) :
    False := by
  rw [← hkey] at habs
  exact gates_insertW_absentW_jointly_unsat hash hCR wideEnc dep r (keyAtCanon mI aI) v r' v'
    hins habs

/-- The `.aafiInsert` twin of the row-level refusal. -/
theorem gates_aafiInsertW_absentW_jointly_unsat_row (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (dep : Nat) (r r' v v' : ℤ) (mI mA : MapOpW)
    (aI aA : Assignment) (hkey : keyAtCanon mI aI = keyAtCanon mA aA)
    (hins : ReconcileGatesAtW hash wideEnc dep r (keyAtCanon mI aI) v r' MapOpKind.aafiInsert)
    (habs : ReconcileGatesAtW hash wideEnc dep r' (keyAtCanon mA aA) v' r' MapOpKind.absent) :
    False := by
  rw [← hkey] at habs
  exact gates_aafiInsertW_absentW_jointly_unsat hash hCR wideEnc dep r (keyAtCanon mI aI) v r' v'
    hins habs

/-- The row-level refusal ROUTED THROUGH THE ABSTRACT blocker-#1 theorem (`.insert`) — so the
abstract statement is inhabited by rows, not merely by keys. -/
theorem gates_jointly_unsat_via_abstract_row' (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (dep : Nat) (r r' v v' : ℤ) (mI mA : MapOpW)
    (aI aA : Assignment) (hkey : keyAtCanon mI aI = keyAtCanon mA aA)
    (hins : ReconcileGatesAtW hash wideEnc dep r (keyAtCanon mI aI) v r' MapOpKind.insert)
    (habs : ReconcileGatesAtW hash wideEnc dep r' (keyAtCanon mA aA) v' r' MapOpKind.absent) :
    False := by
  rw [← hkey] at habs
  exact gates_jointly_unsat_via_abstract' hash hCR dep r (keyAtCanon mI aI) v r' v' hins habs

/-- …and the `.aafiInsert` twin of the abstract routing. -/
theorem gates_jointly_unsat_via_abstract_row (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (dep : Nat) (r r' v v' : ℤ) (mI mA : MapOpW)
    (aI aA : Assignment) (hkey : keyAtCanon mI aI = keyAtCanon mA aA)
    (hins : ReconcileGatesAtW hash wideEnc dep r (keyAtCanon mI aI) v r' MapOpKind.aafiInsert)
    (habs : ReconcileGatesAtW hash wideEnc dep r' (keyAtCanon mA aA) v' r' MapOpKind.absent) :
    False := by
  rw [← hkey] at habs
  exact gates_jointly_unsat_via_abstract hash hCR dep r (keyAtCanon mI aI) v r' v' hins habs

/-- **★ THE CHAIN-LEVEL REFUSAL AT THE ROW'S KEY.** After an accepting widened AAFI insert whose
key is the row's canonical key, no pointer-bracket absence witness for that key exists against the
post-chain. -/
theorem aafiGatesW_no_rewitnessW_row (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) (m : MapOpW) (a : Assignment) {oldRoot newRoot : ℤ} {v : ℤ}
    {lowAddr : Digest8Key} {lowValue : ℤ} {lowNext : Digest8Key} {freeEmpty : ℤ}
    {c : List (ImtLeaf Digest8Key ℤ)} (hs : ImtSorted c)
    (hg : AafiGatesAtW hash dep oldRoot newRoot (keyAtCanon m a) v lowAddr lowValue lowNext
      freeEmpty)
    (hlow : (⟨lowAddr, lowValue, lowNext⟩ : ImtLeaf Digest8Key ℤ) ∈ c) :
    ¬ ImtAbsent (imtInsert c (keyAtCanon m a) v) (keyAtCanon m a) :=
  aafiGatesW_no_rewitnessW hash hCR dep hs hg hlow

end Row

/-! ## §4 — ★ THE FULL COMPOSITION: emitted blocks + row wiring ⇒ the row's key is absent.

This is the theorem W3 needs. The `.absent` gate is BUILT from the emitted `lexLt8` blocks
(`absentGateW_of_lexBlocks_canon`) rather than assumed, the row's key is read through
`keyAtCanon_of_block`, and the conclusion is the weld's gate-forced absence — at one key, with no
canonicity hypothesis anywhere in the chain. -/

theorem absentRow_of_lexBlocks_forces_absence (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) (r v : ℤ) (m : MapOpW) (a : Assignment) (envLo envHi : VmRowEnv)
    (lowAddr kk lowNext : Fin 8 → ℤ)
    (w : RowKeyWiredW m a envLo envHi kk)
    (hLoA : ∀ i : Fin 8, envLo.loc i.val = lowAddr i)
    (hLoBlk : lexBlockHolds lexTf envLo)
    (hHiB : ∀ i : Fin 8, envHi.loc (8 + i.val) = lowNext i)
    (hHiBlk : lexBlockHolds lexTf envHi)
    (h : List (Digest8Key × ℤ)) (hs : wideEnc.HeapOk h) (hlen : h.length = 2 ^ dep)
    (hroot : mapRootW hash wideEnc dep h = r)
    (stepsLo stepsHi : List (Bool × ℤ)) (vlo vhi : ℤ)
    (hlLo : stepsLo.length = dep) (hlHi : stepsHi.length = dep)
    (hadj : pathPos stepsHi = pathPos stepsLo + 1)
    (hpLo : pathRecompute hash (leafOfW hash wideEnc (toLex (canonKey lowAddr), vlo)) stepsLo = r)
    (hpHi : pathRecompute hash (leafOfW hash wideEnc (toLex (canonKey lowNext), vhi)) stepsHi = r) :
    keyAtCanon m a ∉ keysOfW (opensAtW hash wideEnc dep) r := by
  have hgate : ReconcileGatesW hash wideEnc dep r (toLex (canonKey kk)) v r MapOpKind.absent :=
    absentGateW_of_lexBlocks_canon hash dep r v envLo envHi lowAddr kk lowNext
      hLoA w.loCol hLoBlk w.hiCol hHiB hHiBlk stepsLo stepsHi vlo vhi hlLo hlHi hadj hpLo hpHi
  have hAt : ReconcileGatesAtW hash wideEnc dep r (keyAtCanon m a) v r MapOpKind.absent := by
    rw [w.keyAtCanon_eq]
    exact ⟨h, hs, hlen, hroot, hgate⟩
  exact (absentGatesW_force_row_absence hash hCR dep m a r v r hAt).1

/-- The IMT-chain half of the same composition: the emitted blocks plus the row wiring put the ROW's
canonical key off the whole committed address spine. -/
theorem absentRow_of_lexBlocks_forces_chain_absence
    (m : MapOpW) (a : Assignment) (envLo envHi : VmRowEnv) (lowAddr kk lowNext : Fin 8 → ℤ)
    (w : RowKeyWiredW m a envLo envHi kk)
    (hLoA : ∀ i : Fin 8, envLo.loc i.val = lowAddr i)
    (hLoBlk : lexBlockHolds lexTf envLo)
    (hHiB : ∀ i : Fin 8, envHi.loc (8 + i.val) = lowNext i)
    (hHiBlk : lexBlockHolds lexTf envHi)
    (c : List (ImtLeaf Digest8Key ℤ)) (hs : ImtSorted c) (val : ℤ)
    (hmem : (⟨toLex (canonKey lowAddr), val, toLex (canonKey lowNext)⟩ : ImtLeaf Digest8Key ℤ) ∈ c) :
    keyAtCanon m a ∉ imtAddrs c := by
  rw [w.keyAtCanon_eq]
  exact absentBracket_of_lexBlocks_canon envLo envHi lowAddr kk lowNext
    hLoA w.loCol hLoBlk w.hiCol hHiB hHiBlk c hs val hmem

/-! ## §5 — ⚑⚑ THE RAW ROW-LEVEL CLAIM IS FALSE (the choice of `keyAtCanon` is load-bearing). -/

/-- **`RowRawBracketClaim`** — `absentRow_of_lexBlocks_forces_chain_absence` VERBATIM with the
conclusion read at `MapOpW.keyAt` instead of `keyAtCanon`: the statement W3 would have if the row
boundary re-imported the raw reading. -/
def RowRawBracketClaim : Prop :=
  ∀ (m : MapOpW) (a : Assignment) (envLo envHi : VmRowEnv) (lowAddr kk lowNext : Fin 8 → ℤ),
    RowKeyWiredW m a envLo envHi kk →
    (∀ i : Fin 8, envLo.loc i.val = lowAddr i) →
    lexBlockHolds lexTf envLo →
    (∀ i : Fin 8, envHi.loc (8 + i.val) = lowNext i) →
    lexBlockHolds lexTf envHi →
    ∀ (c : List (ImtLeaf Digest8Key ℤ)), ImtSorted c → ∀ val : ℤ,
      (⟨toLex (canonKey lowAddr), val, toLex (canonKey lowNext)⟩ : ImtLeaf Digest8Key ℤ) ∈ c →
      m.keyAt a ∉ imtAddrs c

/-- **⚑⚑ THE ROW-BOUNDARY CANARY, ACCEPT SIDE.** The raw row-level claim is FALSE, on the emitted
object's OWN accepting trace (`forge_blocks_hold`) lifted to a real row (`forgeRow`): it "proves"
the key `p + 5` ABSENT from a chain that PRESENTS it. This is
`MapOpWideKeyCanonDischarge.rawBracketClaim_false` at the row boundary — the same forgery, now
committed by a `MapOpW` reading its own key columns. -/
theorem rowRawBracketClaim_false : ¬ RowRawBracketClaim := by
  intro H
  obtain ⟨⟨envLo, hLoA, hLoB, hLoBlk⟩, ⟨envHi, hHiA, hHiB, hHiBlk⟩⟩ := forge_blocks_hold
  have hcells : (fun i : Fin 8 => envHi.loc i.val) = forgeKk := funext hHiA
  have hkeyAt : (rowOfVars MapOpKind.absent).keyAt envHi.loc = toLex forgeKk := by
    rw [rowOfVars_keyAt, hcells]
  have habs := H (rowOfVars MapOpKind.absent) envHi.loc envLo envHi forgeLow forgeKk forgeNext
    (rowOfVars_wired MapOpKind.absent envLo envHi forgeKk hLoB hHiA) hLoA hLoBlk hHiB hHiBlk
    forgeChain forgeChain_sorted 1
    (by rw [forgeLow_canon, forgeNext_canon]; exact forgeLow_leaf_mem)
  rw [hkeyAt] at habs
  exact habs forgeKk_present

/-- **⚑⚑ THE ROW-BOUNDARY CANARY, REFUSE SIDE.** The SAME row, read through `keyAtCanon`, gives a
TRUE absence on the SAME trace: it excludes the key the emitted block actually compared (`5`), which
the chain does not present. -/
theorem forgeRow_canon_survives (a : Assignment) :
    keyAtCanon forgeRow a ∉ imtAddrs forgeChain :=
  canon_weld_survives

/-! ## §6 — ⚑ THE WITNESS BOUNDARY, CLOSED BY DEFINITION (L3).

**What this section said before, and what changed.** `ReconcileGatesAtW` used to open with
`∃ h : List (K × ℤ)` and `Heap.SortedKeys h` — nothing made that extracted heap's KEYS canonical,
so the row-level absence was absence from a RAW-keyed spine, which is NOT absence of the residue
class the deployed field-element columns identify. This file exhibited the hole with an accepting
`.absent` gate over `aliasHeap = [0 ↦ 1, (p+5) ↦ 1]` (`heapAlias_row_absence_is_not_residue_absence`)
and declined to fix it, because the cure was a DEFINITION change rather than a tooth.

That definition change is now made, one module down: `MapOpWideKeyGate.LaneEnc` carries the
admissible committed-heap shape as a FIELD (`HeapOk`), and `wideEnc.HeapOk h` is
`Heap.SortedKeys h ∧ CanonHeapW h`. `opensToMerkleW` / `writesToMerkleW` / `ReconcileGatesAtW` all
quantify over `E.HeapOk`, so the committed spine is canonically keyed **by definition** — and
`narrowEnc.HeapOk` is definitionally `Heap.SortedKeys`, so every conservativity `rfl` to the
deployed narrow objects survived untouched (`opensToMerkleW_narrow`, `mapRootW_narrow`,
`leafOfW_narrow`, `writesToMerkleW_narrow`, `narrow_holdsAt_is_instance`, `narrow_gates_is_instance`).

Consequences, machine-checked below:

  * `row_absence_is_residue_absence_of_canonHeap` loses its `hcanon` hypothesis (STRICTLY stronger).
  * `aliasHeap_not_heapOk` — the alias heap is not an admissible commitment; and
    ⚑ `aliasRoot_admits_no_gate` — under CR, the alias root admits NO widened gate AT ALL, for any
    key, value, post-root or kind, because the ONLY `2`-leaf heap behind it is the inadmissible one.
    So `heapAlias_row_absence_is_not_residue_absence` is now UNCONSTRUCTIBLE by construction; its
    `¬`-form is `aliasRoot_admits_no_gate`, and its evidence (`aliasHeap`, `aliasHeap_sorted`,
    `aliasHeap_not_canon`) is kept so the closed hole stays legible.

⚠ NOTE THE STATUS HONESTLY. `CanonHeapW` did not become *forced*; it became *definitional*. It now
sits where `Heap.SortedKeys` already sat — inside the knowledge-extraction premise, i.e. a property
of the prover's committed heap rather than a consequence of any gate. That is the only place it can
live: `MapOpWideKeyCanonDischarge.gate_teeth_cannot_force_canonicity` proves no enlargement of the
gate set can force it. What the change buys is that no use site can now *forget* it, that the
statement forced at every row is the one deployment needs, and that the model can no longer certify
an acceptance whose deployed reading is a forgery. -/

/-- **★ THE ROW-LEVEL ABSENCE IS RESIDUE-CLASS ABSENCE** — the statement deployment actually needs:
no committed key has the row's canonical key as its canonical reading. The `hcanon : CanonHeapW h`
this theorem used to carry is GONE: `wideEnc.HeapOk` supplies it (`heapOk_canon`). -/
theorem row_absence_is_residue_absence_of_canonHeap (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (dep : Nat) (m : MapOpW) (a : Assignment)
    (h : List (Digest8Key × ℤ)) (hs : wideEnc.HeapOk h) (hlen : h.length = 2 ^ dep) {r : ℤ}
    (hroot : mapRootW hash wideEnc dep h = r)
    (habs : keyAtCanon m a ∉ keysOfW (opensAtW hash wideEnc dep) r) :
    ∀ k ∈ Heap.keys h, canonKey (ofLex k) ≠ ofLex (keyAtCanon m a) := by
  intro k hk heq
  have hkc : canonKey (ofLex k) = ofLex k := canonKey_id (heapOk_canon hs k hk)
  have hkeq : k = keyAtCanon m a := by
    have : (ofLex k : Fin 8 → ℤ) = ofLex (keyAtCanon m a) := by rw [← hkc, heq]
    exact congrArg (toLex : (Fin 8 → ℤ) → Digest8Key) this
  exact habs (hkeq ▸ (keysOfW_opensAtW hash hCR wideEnc dep h hs hlen hroot k).mpr hk)

/-- **★ THE SAME, WITHOUT NAMING A HEAP.** Whatever admissible heap the extraction produced behind
an accepting `.absent` row's pre-root, none of its committed keys aliases the row's canonical key.
This is the L3 statement in the form W3 consumes: gate acceptance ⇒ residue-class absence, with no
canonicity hypothesis anywhere in the chain. -/
theorem absentGate_forces_residue_absence (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) (m : MapOpW) (a : Assignment) (r v r' : ℤ)
    (hg : ReconcileGatesAtW hash wideEnc dep r (keyAtCanon m a) v r' MapOpKind.absent) :
    ∀ h : List (Digest8Key × ℤ), wideEnc.HeapOk h → h.length = 2 ^ dep →
      mapRootW hash wideEnc dep h = r →
      ∀ k ∈ Heap.keys h, canonKey (ofLex k) ≠ ofLex (keyAtCanon m a) := by
  intro h hs hlen hroot
  exact row_absence_is_residue_absence_of_canonHeap hash hCR dep m a h hs hlen hroot
    (absentGatesW_force_row_absence hash hCR dep m a r v r' hg).1

/-! ### §6a — ⚑ THE ALIAS INSTANCE, NOW REFUSED (the evidence of what was closed). -/

private theorem lex_lt_at0 {x y : Fin 8 → ℤ} (h : x 0 < y 0) : (toLex x : Digest8Key) < toLex y :=
  ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), h⟩

/-- The committed heap of the alias instance: `[0 ↦ 1, (p+5) ↦ 1]`. Sorted at the raw lex order,
two leaves, depth 1. Its second key is NON-canonical — which the widened gate now REFUSES. -/
def aliasHeap : List (Digest8Key × ℤ) := [(toLex forgeLow, 1), (toLex forgeKk, 1)]

theorem aliasHeap_sorted : Heap.SortedKeys aliasHeap := by
  show List.Pairwise (· < ·) [(toLex forgeLow : Digest8Key), toLex forgeKk]
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)
  · intro b hb
    rw [List.mem_singleton.mp hb]
    exact lex_lt_at0 (by decide)
  · intro b hb
    simp at hb

theorem aliasHeap_length : aliasHeap.length = 2 ^ 1 := rfl

/-- The committed root of the alias heap. -/
noncomputable def aliasRoot (hash : List ℤ → ℤ) : ℤ := mapRootW hash wideEnc 1 aliasHeap

/-- The alias heap's key spine is NOT canonical — the fact that made the old hole, unchanged. -/
theorem aliasHeap_not_canon : ¬ CanonHeapW aliasHeap := by
  intro H
  have hmem : (toLex forgeKk : Digest8Key) ∈ Heap.keys aliasHeap := by
    show (toLex forgeKk : Digest8Key) ∈ [(toLex forgeLow : Digest8Key), toLex forgeKk]
    simp
  have h0 := (H _ hmem 0).2
  have : (2013265926 : ℤ) < 2013265921 := h0
  omega

/-- **⚑ …AND IT IS THEREFORE NOT AN ADMISSIBLE WIDE COMMITMENT.** `wideEnc.HeapOk` is exactly
sortedness AND canonical keying; the alias heap has the first and not the second. -/
theorem aliasHeap_not_heapOk : ¬ wideEnc.HeapOk aliasHeap := fun h => aliasHeap_not_canon h.2

/-- **⚑⚑ THE L3 CLOSURE, AS A REFUSAL.** Under the one named CR floor, the alias root admits NO
widened gate whatsoever — any key, any value, any post-root, any kind. The extraction premise alone
kills it: a `2`-leaf heap with that root IS `aliasHeap` (`mapRootW_injective`), and `aliasHeap` is
inadmissible. This is the `¬`-form of the deleted `heapAlias_row_absence_is_not_residue_absence`:
the model can no longer certify an acceptance whose deployed reading is a non-membership forgery. -/
theorem aliasRoot_admits_no_gate (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (k : Digest8Key) (v r' : ℤ) (op : MapOpKind) :
    ¬ ReconcileGatesAtW hash wideEnc 1 (aliasRoot hash) k v r' op := by
  rintro ⟨h, hok, hlen, hroot, -⟩
  have : h = aliasHeap :=
    mapRootW_injective hash hCR wideEnc 1 hlen aliasHeap_length (hroot.trans rfl)
  exact aliasHeap_not_heapOk (this ▸ hok)

/-- …in particular the exact old counterexample — the `.absent` gate at `forgeRow`'s canonical key
`5` against the alias root — is refused. `heapAlias_row_absence_is_not_residue_absence` is
UNCONSTRUCTIBLE. -/
theorem aliasAbsentGate_refused (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (a : Assignment) :
    ¬ ReconcileGatesAtW hash wideEnc 1 (aliasRoot hash) (keyAtCanon forgeRow a) 0 (aliasRoot hash)
        MapOpKind.absent :=
  aliasRoot_admits_no_gate hash hCR _ _ _ _

/-- **⚑ THE DISCRIMINATION SIDE — the refusal is TARGETED, not blanket.** The CANONICAL twin of the
alias heap, `[0 ↦ 1, 5 ↦ 1]`, IS admissible; and against ITS root the `.absent` gate for the key `5`
is refused for the RIGHT reason — `5` is present there, so absence and membership at one root
collide (`opensToMerkleW_functional`). Alias and canonical heap are refused by two DIFFERENT
mechanisms, which is what says the closure did not simply outlaw the whole neighbourhood. -/
def canonAliasHeap : List (Digest8Key × ℤ) := [(toLex forgeLow, 1), (toLex (canonKey forgeKk), 1)]

theorem canonAliasHeap_sorted : Heap.SortedKeys canonAliasHeap := by
  show List.Pairwise (· < ·) [(toLex forgeLow : Digest8Key), toLex (canonKey forgeKk)]
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)
  · intro b hb
    rw [List.mem_singleton.mp hb]
    refine lex_lt_at0 ?_
    show (0 : ℤ) < canonKey forgeKk 0
    rw [forgeKk_canon0]
    norm_num
  · intro b hb
    simp at hb

theorem canonAliasHeap_length : canonAliasHeap.length = 2 ^ 1 := rfl

theorem canonAliasHeap_ok : wideEnc.HeapOk canonAliasHeap := by
  refine ⟨canonAliasHeap_sorted, ?_⟩
  intro k hk
  have hk' : k ∈ [(toLex forgeLow : Digest8Key), toLex (canonKey forgeKk)] := hk
  rcases List.mem_cons.mp hk' with h1 | h1
  · rw [h1]
    show KeyCanon forgeLow
    intro i
    show 0 ≤ (0 : ℤ) ∧ (0 : ℤ) < 2013265921
    norm_num
  · rw [List.mem_singleton.mp h1]
    exact canonKey_isCanon forgeKk

noncomputable def canonAliasRoot (hash : List ℤ → ℤ) : ℤ := mapRootW hash wideEnc 1 canonAliasHeap

/-- The canonical twin really OPENS at the key `5`. -/
theorem canonAliasHeap_opens_five (hash : List ℤ → ℤ) :
    opensToMerkleW hash wideEnc 1 (canonAliasRoot hash) (toLex (canonKey forgeKk)) (some 1) :=
  ⟨canonAliasHeap, canonAliasHeap_ok, canonAliasHeap_length, rfl, by
    show Heap.get [((toLex forgeLow : Digest8Key), (1 : ℤ)),
        ((toLex (canonKey forgeKk) : Digest8Key), (1 : ℤ))] (toLex (canonKey forgeKk)) = some 1
    rw [Heap.get_cons_ne (1 : ℤ) [((toLex (canonKey forgeKk) : Digest8Key), (1 : ℤ))]]
    · exact Heap.get_cons_self _ 1 []
    · refine fun hEq => absurd hEq.symm (ne_of_lt (lex_lt_at0 ?_))
      show (0 : ℤ) < canonKey forgeKk 0
      rw [forgeKk_canon0]
      norm_num⟩

/-- **★ …AND THE `.absent` GATE FOR `5` IS REFUSED THERE TOO, FOR THE HONEST REASON.** No absence
opening can coexist with that membership opening at one root. -/
theorem canonAliasRoot_refuses_absence_of_five (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) :
    ¬ opensToMerkleW hash wideEnc 1 (canonAliasRoot hash) (toLex (canonKey forgeKk)) none :=
  fun habs => Dregg2.Circuit.MapOpWideKeyGate.opensToMerkleW_some_excludes_none hash hCR wideEnc 1
    (canonAliasHeap_opens_five hash) habs

/-! ## §7 — NON-VACUITY: every row-level statement fires on the epoch's existing accepting rows. -/

theorem keyE_canon : KeyCanon (ofLex keyE) := by
  show ∀ i : Fin 8, 0 ≤ (if i = 7 then (1 : ℤ) else 0) ∧ (if i = 7 then (1 : ℤ) else 0) < 2013265921
  decide

theorem keyLo_canon : KeyCanon (ofLex keyLo) := by
  show ∀ i : Fin 8, 0 ≤ (0 : ℤ) ∧ (0 : ℤ) < 2013265921
  decide

/-- The row of the epoch's honest fresh key `keyE` — a real `MapOpW`, canonical cells. -/
def demoRowE : MapOpW := rowOfKey keyE MapOpKind.absent

/-- The row of the epoch's committed key `keyLo`. -/
def demoRowLo (op : MapOpKind) : MapOpW := rowOfKey keyLo op

theorem demoRowE_keyAtCanon (a : Assignment) : keyAtCanon demoRowE a = keyE :=
  rowOfKey_keyAtCanon_of_canon keyE_canon _ a

theorem demoRowLo_keyAtCanon (op : MapOpKind) (a : Assignment) :
    keyAtCanon (demoRowLo op) a = keyLo :=
  rowOfKey_keyAtCanon_of_canon keyLo_canon _ a

/-- On these honest rows BOTH readings agree — the discharge is invisible to a deployed row. -/
theorem demoRowE_readings_agree (a : Assignment) : keyAtCanon demoRowE a = demoRowE.keyAt a := by
  rw [demoRowE_keyAtCanon]; rfl

/-- **★ ROW-LEVEL FIRING #1** — the gate lane's accepting `.absent` row, read as a ROW: its
canonical key is off the committed key set. -/
theorem demoRowE_absence (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (a : Assignment) :
    keyAtCanon demoRowE a ∉ keysOfW (opensAtW hash wideEnc 1) (demoRootW hash) :=
  (absentGatesW_force_row_absence hash hCR 1 demoRowE a (demoRootW hash) 0 (demoRootW hash)
    (by rw [demoRowE_keyAtCanon]; exact demoAbsentGateW_accepts hash)).1

/-- **★ ROW-LEVEL FIRING #2** — the same row's full `.absent` denotation at the concrete predicate. -/
theorem demoRowE_holdsKindW (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (a : Assignment) :
    HoldsKindW (opensAtW hash wideEnc 1) (demoRootW hash) (demoRootW hash)
      (keyAtCanon demoRowE a) 0 MapOpKind.absent :=
  gates_force_holdsKindW_absent_row hash hCR 1 demoRowE a (demoRootW hash) 0 (demoRootW hash)
    (by rw [demoRowE_keyAtCanon]; exact demoAbsentGateW_accepts hash)

/-- **★ ROW-LEVEL FIRING #3** — the abstract keystone's route (`demo_concrete_excludes`) lands on
the SAME row-level statement: two independent routes agreeing at the row boundary. -/
theorem demoRowE_absence_via_keystone (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (a : Assignment) :
    keyAtCanon demoRowE a ∉ keysOfW (opensAtW hash wideEnc 1) (demoRootW hash) := by
  rw [demoRowE_keyAtCanon]
  exact demo_concrete_excludes hash hCR

/-- **★ ROW-LEVEL FIRING #4** — the anti-DoS tooth at the row: the SAME post-write root still
accepts absence for the genuinely-fresh row key. The row-level refusal is TARGETED, not blanket. -/
theorem demoRowE_absence_post_write (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (a : Assignment) :
    keyAtCanon demoRowE a ∉ keysOfW (opensAtW hash wideEnc 1) (demoRootW2 hash) :=
  (absentGatesW_force_row_absence hash hCR 1 demoRowE a (demoRootW2 hash) 0 (demoRootW2 hash)
    (by rw [demoRowE_keyAtCanon]; exact demoAbsentGateW2_accepts hash)).1

/-- **★ ROW-LEVEL FIRING #5 — THE DOUBLE-SPEND, BETWEEN TWO ROWS.** The gate lane's accepting
widened VALUE-UPDATE row (`demoValueUpdateGateW_accepts`, key `keyLo`, which `demoHeapW` ALREADY HOLDS) and ANY `.absent` row whose CANONICAL key
matches it are jointly UNSAT at the post-write root, for every claimed value. -/
theorem demoRow_insert_then_absent_unsat (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (aI aA : Assignment) (v' : ℤ) :
    ¬ ReconcileGatesAtW hash wideEnc 1 (demoRootW2 hash)
        (keyAtCanon (demoRowLo MapOpKind.absent) aA) v' (demoRootW2 hash) MapOpKind.absent := by
  intro habs
  refine gates_insertW_absentW_jointly_unsat_row hash hCR 1 (demoRootW hash) (demoRootW2 hash) 5 v'
    (demoRowLo MapOpKind.insert) (demoRowLo MapOpKind.absent) aI aA ?_ ?_ habs
  · rw [demoRowLo_keyAtCanon, demoRowLo_keyAtCanon]
  · rw [demoRowLo_keyAtCanon]
    exact demoValueUpdateGateW_accepts hash

/-- …and the same refusal routed through the ABSTRACT blocker-#1 theorem, at the row. -/
theorem demoRow_insert_then_absent_unsat_via_abstract (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (aI aA : Assignment) (v' : ℤ) :
    ¬ ReconcileGatesAtW hash wideEnc 1 (demoRootW2 hash)
        (keyAtCanon (demoRowLo MapOpKind.absent) aA) v' (demoRootW2 hash) MapOpKind.absent := by
  intro habs
  refine gates_jointly_unsat_via_abstract_row' hash hCR 1 (demoRootW hash) (demoRootW2 hash) 5 v'
    (demoRowLo MapOpKind.insert) (demoRowLo MapOpKind.absent) aI aA ?_ ?_ habs
  · rw [demoRowLo_keyAtCanon, demoRowLo_keyAtCanon]
  · rw [demoRowLo_keyAtCanon]
    exact demoValueUpdateGateW_accepts hash

/-- **★ ROW-LEVEL FIRING #6 — THE AAFI ROW.** The gate lane's accepting widened AAFI row, keyed at
a ROW's canonical key: after it, no pointer-bracket absence witness for that key exists against the
post-chain. -/
theorem demoRowE_aafi_no_rewitness (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (a : Assignment) :
    ¬ ImtAbsent (imtInsert demoAafiChainW (keyAtCanon demoRowE a) 7) (keyAtCanon demoRowE a) :=
  aafiGatesW_no_rewitnessW_row hash hCR 1 demoRowE a demoAafiChainW_sorted
    (by rw [demoRowE_keyAtCanon]; exact demoAafiGateW_accepts hash) demoAafiChainW_low_mem

/-- …and the post-chain the same accepting AAFI row produces is still `ImtSorted` at the full
8-felt key, with its heap projection sorted — item 2 of the weld, at the row. -/
theorem demoRowE_aafi_preserves_sorted (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (a : Assignment) :
    ImtSorted (imtInsert demoAafiChainW (keyAtCanon demoRowE a) 7)
      ∧ Heap.SortedKeys (Dregg2.Circuit.MapOpWideKeyWeld.imtToHeapW
          (imtInsert demoAafiChainW (keyAtCanon demoRowE a) 7)) :=
  aafiGatesW_force_sortedChainW hash hCR 1 demoAafiChainW_sorted
    (by rw [demoRowE_keyAtCanon]; exact demoAafiGateW_accepts hash) demoAafiChainW_low_mem

/-- **★ ROW-LEVEL FIRING #7 — the full §4 composition on a concrete trace.** `forgeRow`'s two
emitted blocks and its wiring put the ROW's canonical key off the committed chain. The blocks are
the discharge lane's accepting pair; nothing about the row's cells is assumed. -/
theorem varRow_composition_fires :
    ∃ envLo envHi : VmRowEnv,
      RowKeyWiredW (rowOfVars MapOpKind.absent) envHi.loc envLo envHi forgeKk
      ∧ lexBlockHolds lexTf envLo ∧ lexBlockHolds lexTf envHi
      ∧ keyAtCanon (rowOfVars MapOpKind.absent) envHi.loc ∉ imtAddrs forgeChain := by
  obtain ⟨⟨envLo, hLoA, hLoB, hLoBlk⟩, ⟨envHi, hHiA, hHiB, hHiBlk⟩⟩ := forge_blocks_hold
  refine ⟨envLo, envHi, rowOfVars_wired MapOpKind.absent envLo envHi forgeKk hLoB hHiA,
    hLoBlk, hHiBlk, ?_⟩
  refine absentRow_of_lexBlocks_forces_chain_absence (rowOfVars MapOpKind.absent) envHi.loc
    envLo envHi forgeLow forgeKk forgeNext
    (rowOfVars_wired MapOpKind.absent envLo envHi forgeKk hLoB hHiA) hLoA hLoBlk hHiB hHiBlk
    forgeChain forgeChain_sorted 1 ?_
  rw [forgeLow_canon, forgeNext_canon]
  exact forgeLow_leaf_mem

/-! ## §9 — ⚑⚑⚑ QUESTION ZERO: THE SAME ALIAS, AT THE **DEPLOYED NARROW** MAP-OP.

The wide modules are conservative extensions of the deployed narrow objects (`opensToMerkleW_narrow`,
`mapRootW_narrow`, `narrow_gates_is_instance`, all `rfl`). So the obvious question is whether the L3
alias is a wide-epoch artifact at all, or whether the DEPLOYED, currently-shipping ℤ-keyed map-op has
it too. It has it, and it is EASIER there — no `keyAtCanon` is needed, because a narrow row key is a
single ℤ cell.

`narrowEnc.HeapOk` is definitionally nothing but `Heap.SortedKeys` (`deployed_narrow_heapOk_is_only_sortedness`,
a `rfl`): the deployed extraction premise says NOTHING about the committed keys' canonicity. Below,
a REAL accepting deployed `ReconcileGatesAt` row (depth 1, arbitrary hash, every path obligation
`rfl`) over the committed heap `[0 ↦ 1, (p+5) ↦ 1]`, whose key column carries `5`, forcing
`opensToMerkle … 5 none` while the committed spine holds a key whose residue IS `5`.

**⚠ CLASSIFICATION — read this before treating it as a wound.** This is (ii), a MODEL-LEVEL
ARTIFACT, and the two blockers must not be conflated:

  (1) TYPE-LEVEL, i.e. the Lean statement is over-general. In deployment a committed heap key is a
      BabyBear element; there is no inhabitant `p + 5` distinct from `5`. Every leaf in the tree was
      written by a row whose key column is a field element. `narrowAliasHeap` is not a state the
      deployed prover can be in — the same reason `MapOpWideKeyCanonDischarge` gives for raw trace
      cells, one level down at the extraction premise.
  (2) STRONGER THAN (1), AND SPECIFIC TO THIS SITE: the alias root and the canonical root are
      DISTINCT ONLY FOR A HASH THAT SEPARATES RESIDUES. `residueBlind_collapses_alias` shows that a
      residue-blind leaf absorb — which is what a sponge over field elements IS — gives
      `mapRoot hash 1 narrowAliasHeap = mapRoot hash 1 narrowCanonHeap`; and against the canonical
      root the absence of `5` is refused for the honest reason
      (`narrowCanonRoot_refuses_absence_of_five`). The construction therefore lives ENTIRELY in the
      gap between the ℤ model and the field, and `residueBlind_refutes_spongeCR` shows that gap is
      the SAME one `Poseidon2Binding` already flags: no residue-blind hash satisfies
      `Poseidon2SpongeCR`. Building the alias root needs a hash the deployed system does not have.

  NOT (i): there is no live deployed soundness wound here, and no wound-doc entry is warranted.
  NOT (iii): nothing in the Lean model closes it — `ReconcileGatesAt` is unchanged and still admits
  the construction below; what closes it in deployment is the FIELD, plus (independently) a real
  deployed tooth the Lean model does not carry at all: `circuit/src/descriptor_ir2.rs`
  `eval_canon_decomp` (`MA_A_DEC0`/`MA_K_DEC0`/`MA_B_DEC0`, 13 columns each) pins each of
  `lo_addr`, `key`, `low_next` to its UNIQUE canonical lift `hi4 · 2^27 + lo27` — nibble lookup on
  `hi4`, 27-bit decomposition of `lo27`, and the uniqueness tooth `is15 · lo27 = 0` (`p − 1 =
  15 · 2^27`, so `hi4 = 15` admits only `lo27 = 0`) — and `eval_lex_lt` compares THOSE lifts. That
  tooth is a genuine constraint, and `ReconcileGatesAt` does not model it: the Lean narrow `.absent`
  arm carries bare `klo < key < khi` over ℤ with no decomposition data. So the deployed narrow AIR
  is STRICTLY STRONGER than its Lean model on this axis, which is the actionable finding here.
  (⚠ It does not force ℤ-canonicity of a raw cell either — the decomposition equation is a mod-`p`
  gate and the lookups sit on `hi4`/`lo27`, so `gate_teeth_cannot_force_canonicity` still applies
  verbatim. What it forces is IN THE FIELD: a unique lift, hence a well-defined integer order.) -/

/-- **★ THE DEPLOYED NARROW EXTRACTION PREMISE, MEASURED.** `narrowEnc.HeapOk` — the shape of the
committed heap the deployed `ReconcileGatesAt` / `opensToMerkle` quantify over — is EXACTLY
`Heap.SortedKeys`, by `rfl`. Not one word about canonical keys. This is the deployed half of the L3
gap, read off the object rather than asserted. -/
theorem deployed_narrow_heapOk_is_only_sortedness (h : Heap.FeltHeap) :
    Dregg2.Circuit.MapOpWideKeyGate.narrowEnc.HeapOk h = Heap.SortedKeys h := rfl

/-- The deployed-narrow twin of `aliasHeap`: the ℤ-keyed committed heap `[0 ↦ 1, (p+5) ↦ 1]`. -/
def narrowAliasHeap : Heap.FeltHeap := [(0, 1), (2013265926, 1)]

theorem narrowAliasHeap_sorted : Heap.SortedKeys narrowAliasHeap := by
  show List.Pairwise (· < ·) [(0 : ℤ), 2013265926]
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)
  · intro b hb
    rw [List.mem_singleton.mp hb]
    norm_num
  · intro b hb
    simp at hb

theorem narrowAliasHeap_length : narrowAliasHeap.length = 2 ^ 1 := rfl

/-- The DEPLOYED committed root of the alias heap (`MapMerkleRoot.mapRoot`, the object
`heap_root.rs::CanonicalHeapTree::root` is pinned to). -/
def narrowAliasRoot (hash : List ℤ → ℤ) : ℤ := mapRoot hash 1 narrowAliasHeap

/-- **The DEPLOYED narrow `.absent` row** whose one-felt key column carries `5`. A real
`DescriptorIR2.MapOp` — the deployed IR node, not a widened twin. -/
def narrowAliasOp (hash : List ℤ → ℤ) : MapOp where
  guard := .const 1
  root := fun _ => .const (narrowAliasRoot hash)
  key := .const 5
  value := .const 0
  newRoot := fun _ => .const (narrowAliasRoot hash)
  op := MapOpKind.absent

/-- **⚑⚑⚑ QUESTION ZERO, ACCEPT SIDE: THE DEPLOYED NARROW GATE ACCEPTS.** Depth 1, an ARBITRARY
hash, both bracket leaves committed at adjacent positions, every path obligation `rfl`, and the
bracket `0 < 5 < p+5` decided over ℤ — exactly `MapOpsColumnLayout.ReconcileGatesAt`, the deployed
gate model, with nothing widened. -/
theorem narrowAliasGate_accepts (hash : List ℤ → ℤ) (a : Assignment) :
    ReconcileGatesAt hash 1 a (narrowAliasOp hash) :=
  ⟨narrowAliasHeap, narrowAliasHeap_sorted, narrowAliasHeap_length, rfl,
   ⟨[(false, Heap.leafOf hash (2013265926, 1))], [(true, Heap.leafOf hash (0, 1))],
    0, 1, 2013265926, 1, rfl, rfl, rfl, rfl, rfl,
    by show (0 : ℤ) < 5; norm_num, by show (5 : ℤ) < 2013265926; norm_num⟩, rfl⟩

/-- **⚑⚑⚑ QUESTION ZERO, FORCE SIDE: …AND FORCES A DEPLOYED NON-MEMBERSHIP OF `5`.** The deployed
MapOps law (`reconcileGates_force_opening`) turns that accepting row into `opensToMerkle … 5 none`
against the committed root. -/
theorem narrowAliasGate_forces_absence (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (a : Assignment) : opensToMerkle hash 1 (narrowAliasRoot hash) 5 none :=
  (reconcileGates_force_opening hash hCR 1 a (narrowAliasOp hash)
    (narrowAliasGate_accepts hash a)).1

/-- …while the committed spine HOLDS a key whose canonical reading is that very `5`. -/
theorem narrowAliasHeap_holds_an_alias :
    (2013265926 : ℤ) ∈ Heap.keys narrowAliasHeap ∧ (2013265926 : ℤ) ≠ 5
      ∧ canonFelt 2013265926 = 5 := by
  refine ⟨?_, by norm_num, ?_⟩
  · show (2013265926 : ℤ) ∈ [(0 : ℤ), 2013265926]
    simp
  · show (2013265926 : ℤ) % 2013265921 = 5
    norm_num

/-- **⚑⚑⚑ QUESTION ZERO, PACKAGED.** The DEPLOYED, currently-shipping narrow 1-felt map-op has the
SAME alias hole as the wide one had, in the Lean model: an accepting deployed `.absent` gate whose
forced non-membership of `5` coexists with a committed key `p+5` whose residue is `5`. Nothing about
the widening created it; the wide epoch merely made it visible. See the §9 header for why this is
(ii) — a model-level artifact — and not a deployed wound. -/
theorem narrow_deployed_alias_hole (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (a : Assignment) :
    ReconcileGatesAt hash 1 a (narrowAliasOp hash)
      ∧ opensToMerkle hash 1 (narrowAliasRoot hash) 5 none
      ∧ ∃ k ∈ Heap.keys narrowAliasHeap, k ≠ 5 ∧ canonFelt k = 5 :=
  ⟨narrowAliasGate_accepts hash a, narrowAliasGate_forces_absence hash hCR a,
   2013265926, narrowAliasHeap_holds_an_alias.1, narrowAliasHeap_holds_an_alias.2.1,
   narrowAliasHeap_holds_an_alias.2.2⟩

/-! ### §9a — WHY IT IS (ii): the construction needs a hash the deployment does not have. -/

/-- The CANONICAL twin of the alias heap: `[0 ↦ 1, 5 ↦ 1]` — the state a deployed prover with
field-element keys is actually in. -/
def narrowCanonHeap : Heap.FeltHeap := [(0, 1), (5, 1)]

theorem narrowCanonHeap_sorted : Heap.SortedKeys narrowCanonHeap := by
  show List.Pairwise (· < ·) [(0 : ℤ), 5]
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)
  · intro b hb
    rw [List.mem_singleton.mp hb]
    norm_num
  · intro b hb
    simp at hb

theorem narrowCanonHeap_length : narrowCanonHeap.length = 2 ^ 1 := rfl

def narrowCanonRoot (hash : List ℤ → ℤ) : ℤ := mapRoot hash 1 narrowCanonHeap

/-- The canonical twin OPENS at `5`. -/
theorem narrowCanonHeap_opens_five (hash : List ℤ → ℤ) :
    opensToMerkle hash 1 (narrowCanonRoot hash) 5 (some 1) :=
  ⟨narrowCanonHeap, narrowCanonHeap_sorted, narrowCanonHeap_length, rfl, by
    show Heap.get [((0 : ℤ), (1 : ℤ)), ((5 : ℤ), (1 : ℤ))] 5 = some 1
    rw [Heap.get_cons_ne (1 : ℤ) [((5 : ℤ), (1 : ℤ))] (by norm_num)]
    exact Heap.get_cons_self 5 1 []⟩

/-- **★ …SO THE DEPLOYED GATE REFUSES ABSENCE OF `5` THERE.** Against the state the deployed prover
is actually in, `.absent` for `5` is UNSAT for the honest reason: the key is present, and one root
cannot both open and not-open at it. -/
theorem narrowCanonRoot_refuses_absence_of_five (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) : ¬ opensToMerkle hash 1 (narrowCanonRoot hash) 5 none := by
  intro habs
  have := opensToMerkle_functional hash hCR 1 (narrowCanonHeap_opens_five hash) habs
  simp at this

/-- **`ResidueBlindLeaf hash`** — the leaf absorb sees only RESIDUES. ⚠ This is a HYPOTHESIS of the
two theorems below and NOT a floor: nothing in the epoch assumes it, no `#assert_axioms` target
depends on it, and it is a PROPERTY (not a hardness assumption) — the deployed Poseidon2 sponge eats
BabyBear elements, so it has this property by construction. -/
def ResidueBlindLeaf (hash : List ℤ → ℤ) : Prop :=
  ∀ x₁ x₂ y : ℤ, x₁ ≡ x₂ [ZMOD 2013265921] → hash [x₁, y] = hash [x₂, y]

private theorem alias_modEq : (2013265926 : ℤ) ≡ 5 [ZMOD 2013265921] := by
  show (2013265926 : ℤ) % 2013265921 = 5 % 2013265921
  norm_num

/-- **⚑ THE DECISIVE HALF OF THE CLASSIFICATION.** For a residue-blind leaf absorb — i.e. for a hash
that behaves like the deployed field sponge — the alias heap and its canonical twin publish the SAME
committed root. The two "different" heaps of `narrow_deployed_alias_hole` are ONE deployed
commitment, and against it the absence of `5` is refused
(`narrowCanonRoot_refuses_absence_of_five`). The alias hole is not something the field forgets to
forbid; it is something the ℤ model can express and the field cannot. -/
theorem residueBlind_collapses_alias (hash : List ℤ → ℤ) (hres : ResidueBlindLeaf hash) :
    narrowAliasRoot hash = narrowCanonRoot hash := by
  show mapRoot hash 1 narrowAliasHeap = mapRoot hash 1 narrowCanonHeap
  show Dregg2.Circuit.MapMerkleRoot.perfectRoot hash 1
      (narrowAliasHeap.map (Heap.leafOf hash))
    = Dregg2.Circuit.MapMerkleRoot.perfectRoot hash 1 (narrowCanonHeap.map (Heap.leafOf hash))
  have hleaf : hash [(2013265926 : ℤ), 1] = hash [(5 : ℤ), 1] := hres _ _ _ alias_modEq
  have hmap : narrowAliasHeap.map (Heap.leafOf hash)
      = narrowCanonHeap.map (Heap.leafOf hash) := by
    show [hash [(0 : ℤ), 1], hash [(2013265926 : ℤ), 1]] = [hash [(0 : ℤ), 1], hash [(5 : ℤ), 1]]
    rw [hleaf]
  rw [hmap]

/-- **⚑⚑ AND THE TWO MODEL ASSUMPTIONS ARE INCOMPATIBLE.** No residue-blind hash satisfies
`Poseidon2SpongeCR` — the ℤ-list injectivity the whole Merkle layer carries. So the alias
construction is powered by exactly the part of the floor that `Poseidon2Binding` already records as
FALSE at deployed BabyBear parameters: separating `p+5` from `5` is not a capability the deployed
sponge has, and the model's own crypto hypothesis is what pretends otherwise. That is the sharpest
statement of "over-general model", and it applies verbatim to the wide `aliasHeap` too.

⚑ Spelled `¬ Poseidon2SpongeCR hash`, not `… → Poseidon2SpongeCR hash → False`. Definitionally the
same and every use site is unchanged, but `Verify.FloorRatchet.antiFloor` stopped consulting binder
POSITION when the B4 hole closed — under the old, order-keyed rule an uncurried refutation and a
reordered soundness claim were the same `Expr`, and two signature-unforgeability theorems
(`HermineMSIS.no_forgery_under_msis` and its SelfTargetMSIS twin) were riding out of the census on
that. The negation is the spelling that says which one this is. -/
theorem residueBlind_refutes_spongeCR (hash : List ℤ → ℤ) (hres : ResidueBlindLeaf hash) :
    ¬ Poseidon2SpongeCR hash := by
  intro hCR
  have hleaf : hash [(2013265926 : ℤ), 1] = hash [(5 : ℤ), 1] := hres _ _ _ alias_modEq
  have hl : [(2013265926 : ℤ), 1] = [(5 : ℤ), 1] := hCR _ _ hleaf
  injection hl with h1 _
  norm_num at h1

/-! ## §8 — axiom hygiene. -/

#assert_axioms RowKeyWiredW.keyAtCanon_eq
#assert_axioms RowKeyWiredW.wireLo
#assert_axioms keyAtCanon_row_isCanon
#assert_axioms readings_agree
#assert_axioms rowOfKey_keyAt
#assert_axioms rowOfKey_keyAtCanon
#assert_axioms rowOfKey_keyAtCanon_of_canon
#assert_axioms forgeRow_readings_differ
#assert_axioms forgeRow_cells_not_canon
#assert_axioms gatesAtWCanon_eq_gatesAtW
#assert_axioms absentGatesW_force_row_absence
#assert_axioms gates_force_holdsKindW_absent_row
#assert_axioms gates_force_holdsKindW_read_row
#assert_axioms gates_force_holdsKindW_insert_row
#assert_axioms gates_force_holdsKindW_aafiInsert_row
#assert_axioms mapOpW_gatesCanon_force_holdsCanon
#assert_axioms gates_insertW_absentW_jointly_unsat_row
#assert_axioms gates_aafiInsertW_absentW_jointly_unsat_row
#assert_axioms gates_jointly_unsat_via_abstract_row
#assert_axioms gates_jointly_unsat_via_abstract_row'
#assert_axioms aafiGatesW_no_rewitnessW_row
#assert_axioms absentRow_of_lexBlocks_forces_absence
#assert_axioms absentRow_of_lexBlocks_forces_chain_absence
#assert_axioms rowRawBracketClaim_false
#assert_axioms forgeRow_canon_survives
#assert_axioms row_absence_is_residue_absence_of_canonHeap
#assert_axioms absentGate_forces_residue_absence
#assert_axioms aliasHeap_sorted
#assert_axioms aliasHeap_not_canon
#assert_axioms aliasHeap_not_heapOk
#assert_axioms aliasRoot_admits_no_gate
#assert_axioms aliasAbsentGate_refused
#assert_axioms canonAliasHeap_ok
#assert_axioms canonAliasHeap_opens_five
#assert_axioms canonAliasRoot_refuses_absence_of_five
#assert_axioms demoRowE_keyAtCanon
#assert_axioms demoRowE_absence
#assert_axioms demoRowE_holdsKindW
#assert_axioms demoRowE_absence_via_keystone
#assert_axioms demoRowE_absence_post_write
#assert_axioms demoRow_insert_then_absent_unsat
#assert_axioms demoRow_insert_then_absent_unsat_via_abstract
#assert_axioms demoRowE_aafi_no_rewitness
#assert_axioms demoRowE_aafi_preserves_sorted
#assert_axioms rowOfVars_wired
#assert_axioms rowOfVars_keyAtCanon
#assert_axioms varRow_composition_fires
-- §9 — Question Zero, at the DEPLOYED narrow map-op.
#assert_axioms deployed_narrow_heapOk_is_only_sortedness
#assert_axioms narrowAliasHeap_sorted
#assert_axioms narrowAliasGate_accepts
#assert_axioms narrowAliasGate_forces_absence
#assert_axioms narrowAliasHeap_holds_an_alias
#assert_axioms narrow_deployed_alias_hole
#assert_axioms narrowCanonHeap_opens_five
#assert_axioms narrowCanonRoot_refuses_absence_of_five
#assert_axioms residueBlind_collapses_alias
#assert_axioms residueBlind_refutes_spongeCR

end Dregg2.Circuit.MapOpWideKeyRowBoundary
