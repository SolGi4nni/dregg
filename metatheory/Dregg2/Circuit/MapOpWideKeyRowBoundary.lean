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

## ⚑ THE FINDING: the row boundary closes, the WITNESS boundary does not

Composing the weld at the row surfaced the NEXT unforced hypothesis one level down, at the
extraction premise rather than the trace row. `ReconcileGatesAtW` opens with `∃ h : List (K × ℤ)`;
nothing makes that heap's KEYS canonical, and `keysOfW` is a set of raw `Digest8Key`s. So:

  ⚑ `heapAlias_row_absence_is_not_residue_absence` — a REAL accepting widened `.absent` gate
  (depth 1, arbitrary hash, every path obligation `rfl`) whose committed heap is
  `[0 ↦ 1, (p+5) ↦ 1]`, for the row whose canonical key is `5`. The bracket `0 < 5 < p+5` accepts;
  the weld forces `5 ∉ keysOfW`; and the committed spine HOLDS a key (`p+5`) whose canonical
  reading IS `5`. In the deployed prover that leaf's key column carries the field element `5` — the
  same key — so the accepted row is a non-membership forgery *there* while the model theorem is
  true *here*.

  * `row_absence_is_residue_absence_of_canonHeap` — with `CanonHeapW h` the row-level absence DOES
    upgrade to absence of the whole residue class (the statement deployment needs).
  * `heapAlias_heap_not_canon` — and the accepting gate above has `¬ CanonHeapW`, so `CanonHeapW`
    is not gate-forced: it is a MODEL ARTIFACT of the same class `gate_teeth_cannot_force_canonicity`
    identified for trace cells, one level down. Its cure is the same shape (read the committed heap
    canonically) but it lives in `MapOpWideKeyGate`'s `opensToMerkleW`/`mapRootW` definitions, not
    in any tooth — so it is a DEFINITION change, deliberately not made here (this file is additive).

## Non-vacuity

Every row-level statement fires on the epoch's existing concrete accepting rows —
`demoAbsentGateW_accepts`, `demoInsertGateW_accepts`, `demoAafiGateW_accepts`,
`demoAbsentGateW2_accepts`, `demo_concrete_excludes` — through `rowOfKey`, which builds a real
`MapOpW` whose eight key columns are the constant cells of a given key.

## Floors

`Poseidon2SpongeCR` ONLY, and only where the weld already carried it. NO new floor. The canonical
reading is arithmetic (`% p`); the compare block's content is structural.

## Byte safety

NEW file, additive. No descriptor, emit, golden or JSON byte is touched. No `sorry`/`admit`/
`native_decide`. `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}.
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
open Dregg2.Circuit.MapOpWideKeyGate (wideEnc leafOfW mapRootW opensToMerkleW ReconcileGatesW
  ReconcileGatesAtW AafiGatesAtW gatesAtW demoRootW demoAbsentGateW_accepts)
open Dregg2.Circuit.MapOpWideKeyWeld (opensAtW keysOfW_opensAtW absentGatesW_force_keysOfW_absence
  gates_force_holdsKindW_absent gates_force_holdsKindW_read gates_force_holdsKindW_insert
  gates_force_holdsKindW_aafiInsert gates_insertW_absentW_jointly_unsat
  gates_aafiInsertW_absentW_jointly_unsat gates_jointly_unsat_via_abstract
  gates_jointly_unsat_via_abstract' aafiGatesW_no_rewitnessW aafiGatesW_force_sortedChainW
  imtToHeapW demoRootW2 demoInsertGateW_accepts demoAbsentGateW2_accepts demo_concrete_excludes
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
    (h : List (Digest8Key × ℤ)) (hs : Heap.SortedKeys h) (hlen : h.length = 2 ^ dep)
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

/-! ## §6 — ⚑ THE FINDING: the row boundary closes; the WITNESS boundary does not.

`ReconcileGatesAtW` opens with `∃ h : List (K × ℤ)` — the extracted committed heap. Nothing makes
its KEYS canonical, and `keysOfW` is a set of RAW `Digest8Key`s. The row-level absence is therefore
absence from a raw-keyed spine, which is NOT absence of the residue class the deployed field-element
columns identify. -/

/-- **`CanonHeapW h`** — every committed key of the heap is canonical: the property the deployed
prover has for free (its heap keys ARE field elements) and the model does not state. -/
def CanonHeapW (h : List (Digest8Key × ℤ)) : Prop := ∀ k ∈ Heap.keys h, KeyCanon (ofLex k)

/-- **★ WITH `CanonHeapW`, THE ROW-LEVEL ABSENCE IS RESIDUE-CLASS ABSENCE** — the statement
deployment actually needs: no committed key has the row's canonical key as its canonical reading. -/
theorem row_absence_is_residue_absence_of_canonHeap (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (dep : Nat) (m : MapOpW) (a : Assignment)
    (h : List (Digest8Key × ℤ)) (hs : Heap.SortedKeys h) (hlen : h.length = 2 ^ dep) {r : ℤ}
    (hroot : mapRootW hash wideEnc dep h = r) (hcanon : CanonHeapW h)
    (habs : keyAtCanon m a ∉ keysOfW (opensAtW hash wideEnc dep) r) :
    ∀ k ∈ Heap.keys h, canonKey (ofLex k) ≠ ofLex (keyAtCanon m a) := by
  intro k hk heq
  have hkc : canonKey (ofLex k) = ofLex k := canonKey_id (hcanon k hk)
  have hkeq : k = keyAtCanon m a := by
    have : (ofLex k : Fin 8 → ℤ) = ofLex (keyAtCanon m a) := by rw [← hkc, heq]
    exact congrArg (toLex : (Fin 8 → ℤ) → Digest8Key) this
  exact habs (hkeq ▸ (keysOfW_opensAtW hash hCR wideEnc dep h hs hlen hroot k).mpr hk)

/-! ### §6a — ⚑ the ALIAS INSTANCE: an accepting gate whose committed heap is NOT canonical. -/

private theorem lex_lt_at0 {x y : Fin 8 → ℤ} (h : x 0 < y 0) : (toLex x : Digest8Key) < toLex y :=
  ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), h⟩

/-- The committed heap of the alias instance: `[0 ↦ 1, (p+5) ↦ 1]`. Sorted at the raw lex order,
two leaves, depth 1. Its second key is NON-canonical — and nothing in the gate forbids that. -/
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
def aliasRoot (hash : List ℤ → ℤ) : ℤ := mapRootW hash wideEnc 1 aliasHeap

/-- **★ A REAL ACCEPTING WIDENED `.absent` GATE FOR `forgeRow`'s CANONICAL KEY.** The bracket is
`0 < 5 < p+5` at the raw lex order, both bracket leaves are committed at adjacent positions, every
path obligation closes by `rfl`, over an ARBITRARY hash. -/
theorem aliasAbsentGate_accepts_canonKey (hash : List ℤ → ℤ) :
    ReconcileGatesAtW hash wideEnc 1 (aliasRoot hash) (toLex (canonKey forgeKk)) 0
      (aliasRoot hash) MapOpKind.absent :=
  ⟨aliasHeap, aliasHeap_sorted, aliasHeap_length, rfl,
   ⟨[(false, leafOfW hash wideEnc (toLex forgeKk, 1))],
    [(true, leafOfW hash wideEnc (toLex forgeLow, 1))],
    toLex forgeLow, 1, toLex forgeKk, 1, rfl, rfl, rfl, rfl, rfl,
    lex_lt_at0 (by decide), lex_lt_at0 (by decide)⟩, rfl⟩

/-- …stated at the ROW: the accepting gate is a gate for `forgeRow`'s key AS THE COMPARE BLOCK
READS IT. -/
theorem aliasAbsentGate_accepts (hash : List ℤ → ℤ) (a : Assignment) :
    ReconcileGatesAtW hash wideEnc 1 (aliasRoot hash) (keyAtCanon forgeRow a) 0 (aliasRoot hash)
      MapOpKind.absent := by
  rw [forgeRow_keyAtCanon]
  exact aliasAbsentGate_accepts_canonKey hash

/-- The alias heap's key spine is NOT canonical — so `CanonHeapW` is not gate-forced: the accepting
row above is a counterexample to "the extraction premise supplies canonical keys". -/
theorem aliasHeap_not_canon : ¬ CanonHeapW aliasHeap := by
  intro H
  have hmem : (toLex forgeKk : Digest8Key) ∈ Heap.keys aliasHeap := by
    show (toLex forgeKk : Digest8Key) ∈ [(toLex forgeLow : Digest8Key), toLex forgeKk]
    simp
  have h0 := (H _ hmem 0).2
  have : (2013265926 : ℤ) < 2013265921 := h0
  omega

/-- **⚑ THE FINDING, MACHINE-CHECKED.** On one accepting widened `.absent` row: (i) the gate
ACCEPTS, (ii) the weld forces the ROW's canonical key `5` absent from the committed key set, and
(iii) the committed spine HOLDS a key (`p+5`) whose canonical reading IS that very key. The model
statement is true; the deployed reading of the same trace is a non-membership forgery, because there
that leaf's key column carries the field element `5`. Routing the ROW through `keyAtCanon` closes
the row boundary and does NOT close the extraction premise — the heap must be read canonically too,
which is a change to `opensToMerkleW`/`mapRootW`, not a tooth. -/
theorem heapAlias_row_absence_is_not_residue_absence (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (a : Assignment) :
    ReconcileGatesAtW hash wideEnc 1 (aliasRoot hash) (keyAtCanon forgeRow a) 0 (aliasRoot hash)
        MapOpKind.absent
      ∧ keyAtCanon forgeRow a ∉ keysOfW (opensAtW hash wideEnc 1) (aliasRoot hash)
      ∧ ∃ k ∈ Heap.keys aliasHeap,
          k ≠ keyAtCanon forgeRow a ∧ canonKey (ofLex k) = ofLex (keyAtCanon forgeRow a) := by
  refine ⟨aliasAbsentGate_accepts hash a,
    (absentGatesW_force_row_absence hash hCR 1 forgeRow a (aliasRoot hash) 0 (aliasRoot hash)
      (aliasAbsentGate_accepts hash a)).1,
    toLex forgeKk, ?_, ?_, ?_⟩
  · show (toLex forgeKk : Digest8Key) ∈ [(toLex forgeLow : Digest8Key), toLex forgeKk]
    simp
  · exact fun hcontra => forgeRow_readings_differ a (hcontra.symm)
  · show canonKey forgeKk = canonKey forgeKk
    rfl

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
widened write row (`demoInsertGateW_accepts`, key `keyLo`) and ANY `.absent` row whose CANONICAL key
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
    exact demoInsertGateW_accepts hash

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
    exact demoInsertGateW_accepts hash

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
#assert_axioms aliasHeap_sorted
#assert_axioms aliasAbsentGate_accepts_canonKey
#assert_axioms aliasAbsentGate_accepts
#assert_axioms aliasHeap_not_canon
#assert_axioms heapAlias_row_absence_is_not_residue_absence
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

end Dregg2.Circuit.MapOpWideKeyRowBoundary
