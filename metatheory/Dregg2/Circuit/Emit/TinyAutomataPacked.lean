/-
# Dregg2.Circuit.Emit.TinyAutomataPacked — `s` DFA STEPS PER TRACE ROW.

**This is Lean-authored AIR.** The packed descriptor is an `EffectVmDescriptor2` value authored
here; the witness is a concrete `VmTrace`; the satisfaction and the classification-preservation
are theorems over the EMITTED object. Rust parses the emitted IR2 bytes and supplies the witness
this file constructs; Rust authors no constraint.

## The lever

`circuit/tests/tiny_automata_prove_time_attack.rs` measured a composed tiny-automata prove at
`k = 4, n = 1024` to spend 97.9% of its 153 ms of user CPU inside Poseidon2 Merkle commitment of
the trace (first digest layer 55.9% + build merkle tree 42.0%), with LDE ~1.3%, LogUp < 0.02 ms
and quotient < 0.10 ms. Prove time is therefore ~linear in TRACE ROWS.
`TinyAutomataSatisfiable`'s run-table discipline spends exactly ONE trace row per input symbol
(`runRows`), so an `n`-symbol word costs `n` rows.

This file spends `s` symbols per row: the row carries the `s + 1` states and the `s` symbols of a
chunk, interleaved, and asserts `s` transition lookups against the SAME declared table. An
`n`-symbol word then occupies `n / s` rows.

  * §1 — the packed layout and `packedDesc name s tbl`. `packedDesc name 1 tbl` is DEFINITIONALLY
    `DfaRoutingTableEmit.tableRoutingDesc name tbl` (`packed_one_eq_tableRouting`, `rfl`), so the
    family strictly generalises the deployed 3-column shape rather than forking it.
  * §2 — the packed rows, and the two structural facts about them (`tupsFrom_rowVals`: the row's
    `s` lookup tuples ARE the run table of its chunk, in order; `rowVals_last`: the row's last
    state column IS `classifyFrom` of its chunk).
  * §3 — ⚑ THE GATE: `packWit_satisfies`, a real `Satisfied2Public` witness for the packed
    descriptor, GENERAL in `s`, in the chunk count `m` and in the word (given `|w| = m · s`).
    As in the run-table discipline the LogUp balance is an EQUALITY, hence `List.Perm.refl` —
    the Eulerian obstruction never arises.
  * §4 — the CORRECTNESS theorem: `packWit_final_state` — the packed descriptor's exposed public
    `final_state` is `classifyFrom d q0 w` for the SAME word `w`. Packing does not change the
    verdict.
  * §5 — the concrete packed instances, their witnesses, and the measured shape.

## Two residuals, named up front

  * **The general (soundness) direction at `s > 1` is NOT proved here.** `packed_one_refines_classify`
    gives it at `s = 1` by inheriting `tableRouting_refines_classify`. For `s > 1` this file
    establishes the CONSTRUCTED-witness direction at every `s` (`packWit_final_state`) and the
    descriptor-level shape; the "any satisfying trace of `packedDesc name s` classifies" statement
    is work NOT DONE.
  * **Packing does not move the declared-table cap.** Packing divides TRACE ROWS by `s`; the
    DECLARED table still carries one row per input symbol (the run table). `forced_trace_length`
    reads `rows · lookupCount = declaredRows`, and the packed descriptor has `lookupCount = s`,
    so `rows = n / s` — the declared side is invariant in `s`. The deployed Rust prover
    (`circuit/src/descriptor_ir2.rs`) pushes ONE batch AIR instance per DECLARED exact-public row
    and caps the manifest at `MAX_EXACT_PUBLIC_ROWS = 128`; neither is touched by `s`.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem below. NEW file;
every import is read-only. Every `#guard` is COMPILED EVALUATION of a closed `Bool` — it proves
NO `Prop`; it pins measured numbers and nothing more. The load-bearing objects are the theorems.
-/
import Dregg2.Circuit.Emit.TinyAutomataSatisfiable

namespace Dregg2.Circuit.Emit.TinyAutomataPacked

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmConstraint VmRow VmRowEnv holdsVm_piFirst_true holdsVm_piLast_true)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Crypto.DfaAcceptanceAir (TableDfa classifyFrom)
open Dregg2.Circuit.Emit.DfaRoutingTableEmit
  (CURRENT SYMBOL NEXT TRT_TID TRT_PI_COUNT PI_INITIAL PI_FINAL
   tableRoutingDesc transitionTableDef envAt_loc envAt_nxt hash0
   tableRouting_refines_classify)
open Dregg2.Circuit.Emit.TinyAutomataCompose
  (runTable costOf DescCost.area ForcedRows jsonBytes prodListDfa encodeDigits
   costOf_forced_sound)
open Dregg2.Circuit.Emit.TinyAutomataSatisfiable
  (IRADIX famI prodI probeW prodRunWit_k4_components)

set_option autoImplicit false

/-! ## §0 — three list facts the packing needs. -/

/-- Reading past a prefix. -/
theorem getD_append (l : List Nat) : ∀ (pre : List Nat) (i : Nat),
    (pre ++ l).getD (pre.length + i) 0 = l.getD i 0 := by
  intro pre
  induction pre with
  | nil => intro i; simp
  | cons a pre ih =>
    intro i
    have hidx : (a :: pre).length + i = (pre.length + i) + 1 := by
      simp only [List.length_cons]; omega
    rw [hidx, List.cons_append]
    show (pre ++ l).getD (pre.length + i) 0 = l.getD i 0
    exact ih i

/-- `runTable` splits along a word split, threading the intermediate state. -/
theorem runTable_append (d : TableDfa Nat Nat) : ∀ (a b : List Nat) (q : Nat),
    runTable d q (a ++ b) = runTable d q a ++ runTable d (classifyFrom d q a) b
  | [],      _, _ => rfl
  | y :: ys, b, q => by
    show [q, y, d.step q y] :: runTable d (d.step q y) (ys ++ b)
      = [q, y, d.step q y] :: (runTable d (d.step q y) ys ++ runTable d (classifyFrom d q (y :: ys)) b)
    rw [runTable_append d ys b (d.step q y)]
    rfl

/-- `classifyFrom` splits along a word split. -/
theorem classifyFrom_append (d : TableDfa Nat Nat) : ∀ (a b : List Nat) (q : Nat),
    classifyFrom d q (a ++ b) = classifyFrom d (classifyFrom d q a) b
  | [],      _, _ => rfl
  | y :: ys, b, q => classifyFrom_append d ys b (d.step q y)

/-! ## §1 — THE PACKED LAYOUT.

Row columns, interleaved: `q₀, y₀, q₁, y₁, …, y_{s-1}, q_s`. State `j` sits at column `2j`, symbol
`j` at column `2j + 1`, so the trace width is `2s + 1`. At `s = 1` this IS the deployed
`(current, symbol, next) = (0, 1, 2)` layout, which is why §1's last theorem is `rfl`. -/

/-- The packed trace width for `s` steps per row. -/
def packWidth (s : Nat) : Nat := 2 * s + 1

/-- The column of the LAST state of a packed row (the chunk's exit state). -/
def packLastCol (s : Nat) : Nat := 2 * s

/-- `packLookups o j` — `j` transition lookups against the ONE declared table, at column offsets
`o, o + 2, …`. Each asserts `(state, symbol, next state) ∈ table` for one in-row step. -/
def packLookups : Nat → Nat → List VmConstraint2
  | _, 0     => []
  | o, j + 1 => .lookup ⟨TRT_TID, [.var o, .var (o + 1), .var (o + 2)]⟩ :: packLookups (o + 2) j

/-- The packed continuity window: the NEXT row's first state is THIS row's last state. -/
def packContWindow (s : Nat) : VmConstraint2 :=
  .windowGate ⟨.add (.nxt 0) (.mul (.const (-1)) (.loc (packLastCol s))), true⟩

/-- The three non-lookup constraints: continuity + the two boundary pins. -/
def packTail (s : Nat) : List VmConstraint2 :=
  [ packContWindow s
  , .base (.piBinding VmRow.first 0 PI_INITIAL)
  , .base (.piBinding VmRow.last (packLastCol s) PI_FINAL) ]

/-- **`packedDesc name s tbl`** — the packed table-routing descriptor: `s` transition lookups
against ONE declared `exactPublicRows` table, the cross-row continuity window, and the two
boundary pins (first row's `q₀` = `pi[initial_state]`, last row's `q_s` = `pi[final_state]`). -/
def packedDesc (name : String) (s : Nat) (tbl : List (List Nat)) : EffectVmDescriptor2 :=
  { name        := name
  , traceWidth  := packWidth s
  , piCount     := TRT_PI_COUNT
  , tables      := [transitionTableDef tbl]
  , constraints := packLookups 0 s ++ packTail s
  , hashSites   := []
  , ranges      := [] }

/-- **The packed family STRICTLY GENERALISES the deployed shape**: at `s = 1` the packed
descriptor IS `tableRoutingDesc`, definitionally — same width, same four constraints, same table,
same wire bytes. Packing is a new point on one family, not a fork. -/
theorem packed_one_eq_tableRouting (name : String) (tbl : List (List Nat)) :
    packedDesc name 1 tbl = tableRoutingDesc name tbl := rfl

/-! ## §2 — THE PACKED ROWS. -/

/-- The interleaved column values of ONE packed row running `ys` from `q`. -/
def rowVals (d : TableDfa Nat Nat) (q : Nat) : List Nat → List Nat
  | []      => [q]
  | y :: ys => q :: y :: rowVals d (d.step q y) ys

/-- A `List Nat` read as an `Assignment` (off-the-end reads are `0`, never load-bearing: every
column the descriptor mentions is `< 2s + 1 = |rowVals|`). -/
def asgOf (l : List Nat) : Assignment := fun c => Int.ofNat (l.getD c 0)

theorem rowVals_head (d : TableDfa Nat Nat) (q : Nat) : ∀ ys : List Nat,
    (rowVals d q ys).getD 0 0 = q
  | []     => rfl
  | _ :: _ => rfl

theorem rowVals_length (d : TableDfa Nat Nat) : ∀ (ys : List Nat) (q : Nat),
    (rowVals d q ys).length = 2 * ys.length + 1
  | [],      _ => rfl
  | y :: ys, q => by
    show (rowVals d (d.step q y) ys).length + 1 + 1 = 2 * (ys.length + 1) + 1
    rw [rowVals_length d ys (d.step q y)]
    omega

/-- **The packed row's LAST state column IS `classifyFrom` of its chunk.** -/
theorem rowVals_last (d : TableDfa Nat Nat) : ∀ (ys : List Nat) (q : Nat),
    (rowVals d q ys).getD (2 * ys.length) 0 = classifyFrom d q ys
  | [],      _ => rfl
  | y :: ys, q => by
    have hidx : 2 * (y :: ys).length = 2 * ys.length + 2 := by
      simp only [List.length_cons]; omega
    rw [hidx]
    show (rowVals d (d.step q y) ys).getD (2 * ys.length) 0 = classifyFrom d (d.step q y) ys
    exact rowVals_last d ys (d.step q y)

/-- The per-row lookup-tuple list: `j` triples starting at column offset `o`. -/
def tupsFrom : Nat → Nat → Assignment → Table
  | _, 0,     _   => []
  | o, j + 1, row => [row o, row (o + 1), row (o + 2)] :: tupsFrom (o + 2) j row

/-- The `lookupLog` selector at `TRT_TID`, named so it can be rewritten. -/
def tupSel (row : Assignment) : VmConstraint2 → Option (List ℤ)
  | .lookup l => if l.table = TRT_TID then some (l.tuple.map (·.eval row)) else none
  | _         => none

/-- Every packed lookup is a `TRT_TID` lookup. -/
theorem packLookups_form : ∀ (j o : Nat) (c : VmConstraint2), c ∈ packLookups o j →
    ∃ l : Lookup, c = .lookup l ∧ l.table = TRT_TID
  | 0,     _, _, h => absurd h (List.not_mem_nil)
  | j + 1, o, c, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨⟨TRT_TID, [.var o, .var (o + 1), .var (o + 2)]⟩, rfl, rfl⟩
    · exact packLookups_form j (o + 2) c h

/-- **The packed lookups' evaluated tuples ARE `tupsFrom`** — the selector keeps exactly them. -/
theorem filterMap_packLookups : ∀ (j o : Nat) (row : Assignment),
    (packLookups o j).filterMap (tupSel row) = tupsFrom o j row
  | 0,     _, _   => rfl
  | j + 1, o, row => by
    show [row o, row (o + 1), row (o + 2)] :: (packLookups (o + 2) j).filterMap (tupSel row)
      = [row o, row (o + 1), row (o + 2)] :: tupsFrom (o + 2) j row
    rw [filterMap_packLookups j (o + 2) row]

/-- Any selector that ignores lookups is empty on `packLookups`. -/
theorem packLookups_filterMap_none {α : Type} (f : VmConstraint2 → Option α)
    (hf : ∀ l : Lookup, f (.lookup l) = none) : ∀ (j o : Nat),
    (packLookups o j).filterMap f = []
  | 0,     _ => rfl
  | j + 1, o => by
    have hh := hf ⟨TRT_TID, [(.var o : EmittedExpr), .var (o + 1), .var (o + 2)]⟩
    show (List.filterMap f
      ((.lookup ⟨TRT_TID, [(.var o : EmittedExpr), .var (o + 1), .var (o + 2)]⟩ : VmConstraint2)
        :: packLookups (o + 2) j)) = []
    rw [List.filterMap_cons, hh]
    exact packLookups_filterMap_none f hf j (o + 2)

/-- **THE ROW LEMMA**: the `s` lookup tuples of a packed row ARE the run table of its chunk, in
order. Stated over an arbitrary prefix so the offset arithmetic is an append, not an index shift. -/
theorem tupsFrom_rowVals (d : TableDfa Nat Nat) : ∀ (ys : List Nat) (q : Nat) (pre : List Nat),
    tupsFrom pre.length ys.length (asgOf (pre ++ rowVals d q ys))
      = exactPublicTable (runTable d q ys)
  | [],      _, _   => rfl
  | y :: ys, q, pre => by
    have hA0 : asgOf (pre ++ rowVals d q (y :: ys)) pre.length = Int.ofNat q := by
      show Int.ofNat ((pre ++ (q :: y :: rowVals d (d.step q y) ys)).getD (pre.length + 0) 0) = _
      rw [getD_append]
      rfl
    have hA1 : asgOf (pre ++ rowVals d q (y :: ys)) (pre.length + 1) = Int.ofNat y := by
      show Int.ofNat ((pre ++ (q :: y :: rowVals d (d.step q y) ys)).getD (pre.length + 1) 0) = _
      rw [getD_append]
      rfl
    have hA2 : asgOf (pre ++ rowVals d q (y :: ys)) (pre.length + 2)
        = Int.ofNat (d.step q y) := by
      show Int.ofNat ((pre ++ (q :: y :: rowVals d (d.step q y) ys)).getD (pre.length + 2) 0) = _
      rw [getD_append]
      exact congrArg Int.ofNat (rowVals_head d (d.step q y) ys)
    have hpre : (pre ++ [q, y]).length = pre.length + 2 := by
      rw [List.length_append]
      rfl
    have hcat : (pre ++ [q, y]) ++ rowVals d (d.step q y) ys
        = pre ++ rowVals d q (y :: ys) := by
      rw [List.append_assoc]
      rfl
    have htail : tupsFrom (pre.length + 2) ys.length (asgOf (pre ++ rowVals d q (y :: ys)))
        = exactPublicTable (runTable d (d.step q y) ys) := by
      rw [← hcat, ← hpre]
      exact tupsFrom_rowVals d ys (d.step q y) (pre ++ [q, y])
    show [asgOf (pre ++ rowVals d q (y :: ys)) pre.length,
          asgOf (pre ++ rowVals d q (y :: ys)) (pre.length + 1),
          asgOf (pre ++ rowVals d q (y :: ys)) (pre.length + 2)]
        :: tupsFrom (pre.length + 2) ys.length (asgOf (pre ++ rowVals d q (y :: ys)))
      = exactPublicTable ([q, y, d.step q y] :: runTable d (d.step q y) ys)
    rw [hA0, hA1, hA2, htail]
    rfl

/-- The `pre = []` instance: a packed row's tuples ARE its chunk's run table. -/
theorem tupsFrom_rowVals_nil (d : TableDfa Nat Nat) (ys : List Nat) (q : Nat) :
    tupsFrom 0 ys.length (asgOf (rowVals d q ys)) = exactPublicTable (runTable d q ys) := by
  have h := tupsFrom_rowVals d ys q []
  simpa using h

/-! ### §2a — the whole trace: `m` chunks of `s`. -/

/-- **The packed trace rows**: `m` rows, each consuming the next `s` symbols. -/
def packRowsN (d : TableDfa Nat Nat) (s : Nat) : Nat → Nat → List Nat → List Assignment
  | 0,     _, _ => []
  | m + 1, q, w =>
      asgOf (rowVals d q (w.take s))
        :: packRowsN d s m (classifyFrom d q (w.take s)) (w.drop s)

theorem packRowsN_length (d : TableDfa Nat Nat) (s : Nat) : ∀ (m q : Nat) (w : List Nat),
    (packRowsN d s m q w).length = m
  | 0,     _, _ => rfl
  | m + 1, q, w => by
    show (packRowsN d s m (classifyFrom d q (w.take s)) (w.drop s)).length + 1 = m + 1
    rw [packRowsN_length d s m (classifyFrom d q (w.take s)) (w.drop s)]

/-- The chunk's last state column, read off the row assignment. -/
theorem packRow_lastCol (d : TableDfa Nat Nat) (s : Nat) (q : Nat) (w : List Nat)
    (hta : (w.take s).length = s) :
    asgOf (rowVals d q (w.take s)) (packLastCol s)
      = Int.ofNat (classifyFrom d q (w.take s)) := by
  have h := rowVals_last d (w.take s) q
  rw [hta] at h
  show Int.ofNat ((rowVals d q (w.take s)).getD (2 * s) 0) = _
  rw [h]

/-- **THE TRACE LEMMA**: the whole trace's lookup tuples ARE the declared run table, IN ORDER —
an EQUALITY, so the unit-capacity LogUp receive is discharged by `List.Perm.refl`. -/
theorem packRowsN_flat (d : TableDfa Nat Nat) (s : Nat) :
    ∀ (m q : Nat) (w : List Nat), w.length = m * s →
      (packRowsN d s m q w).flatMap (fun row => tupsFrom 0 s row)
        = exactPublicTable (runTable d q w)
  | 0,     q, w, hw => by
    have hnil : w = [] := List.eq_nil_of_length_eq_zero (by simpa using hw)
    subst hnil
    rfl
  | m + 1, q, w, hw => by
    have hlen : w.length = s + m * s := by rw [hw]; ring
    have hs : s ≤ w.length := by omega
    have hta : (w.take s).length = s := by simp only [List.length_take]; omega
    have htb : (w.drop s).length = m * s := by simp only [List.length_drop]; omega
    have hsplit : w.take s ++ w.drop s = w := List.take_append_drop s w
    have hfirst : tupsFrom 0 s (asgOf (rowVals d q (w.take s)))
        = exactPublicTable (runTable d q (w.take s)) := by
      have h := tupsFrom_rowVals_nil d (w.take s) q
      rwa [hta] at h
    have hrt : runTable d q w
        = runTable d q (w.take s) ++ runTable d (classifyFrom d q (w.take s)) (w.drop s) := by
      have h := runTable_append d (w.take s) (w.drop s) q
      rwa [hsplit] at h
    show tupsFrom 0 s (asgOf (rowVals d q (w.take s)))
        ++ (packRowsN d s m (classifyFrom d q (w.take s)) (w.drop s)).flatMap
             (fun row => tupsFrom 0 s row)
      = exactPublicTable (runTable d q w)
    rw [packRowsN_flat d s m (classifyFrom d q (w.take s)) (w.drop s) htb, hfirst, hrt]
    simp only [exactPublicTable, List.map_append]

/-- The FIRST packed row's first state column is the start state. -/
theorem packRowsN_head (d : TableDfa Nat Nat) (s : Nat) (m q : Nat) (w : List Nat)
    (h : 0 < (packRowsN d s m q w).length) : ((packRowsN d s m q w)[0]'h) 0 = Int.ofNat q := by
  cases m with
  | zero => simp [packRowsN] at h
  | succ m' => exact congrArg Int.ofNat (rowVals_head d q (w.take s))

/-- Adjacent packed rows CHAIN: row `i+1`'s first state is row `i`'s last state. -/
theorem packRowsN_chain (d : TableDfa Nat Nat) (s : Nat) :
    ∀ (m q : Nat) (w : List Nat), w.length = m * s →
      ∀ (i : Nat) (h : i + 1 < (packRowsN d s m q w).length),
        ((packRowsN d s m q w)[i + 1]'h) 0
          = ((packRowsN d s m q w)[i]'(Nat.lt_of_succ_lt h)) (packLastCol s)
  | 0,     _, _, _,  i, h => by simp [packRowsN] at h
  | m + 1, q, w, hw, i, h => by
    have hlen : w.length = s + m * s := by rw [hw]; ring
    have hta : (w.take s).length = s := by simp only [List.length_take]; omega
    have htb : (w.drop s).length = m * s := by simp only [List.length_drop]; omega
    cases i with
    | zero =>
      cases m with
      | zero => simp only [packRowsN_length] at h; omega
      | succ m' =>
        have hpos : 0 < (packRowsN d s (m' + 1) (classifyFrom d q (w.take s)) (w.drop s)).length := by
          simp only [packRowsN_length]; omega
        show ((packRowsN d s (m' + 1) (classifyFrom d q (w.take s)) (w.drop s))[0]'hpos) 0
          = asgOf (rowVals d q (w.take s)) (packLastCol s)
        rw [packRowsN_head d s (m' + 1) (classifyFrom d q (w.take s)) (w.drop s) hpos,
          packRow_lastCol d s q w hta]
    | succ j =>
      exact packRowsN_chain d s m (classifyFrom d q (w.take s)) (w.drop s) htb j
        (by simpa [packRowsN] using h)

/-- The LAST packed row's last state column IS the classification of the WHOLE word. -/
theorem packRowsN_last (d : TableDfa Nat Nat) (s : Nat) :
    ∀ (m q : Nat) (w : List Nat), w.length = m * s →
      ∀ (i : Nat) (h : i < (packRowsN d s m q w).length),
        i + 1 = (packRowsN d s m q w).length →
        ((packRowsN d s m q w)[i]'h) (packLastCol s) = Int.ofNat (classifyFrom d q w)
  | 0,     _, _, _,  i, h, _ => by simp [packRowsN] at h
  | m + 1, q, w, hw, i, h, hlast => by
    have hlen : w.length = s + m * s := by rw [hw]; ring
    have hta : (w.take s).length = s := by simp only [List.length_take]; omega
    have htb : (w.drop s).length = m * s := by simp only [List.length_drop]; omega
    have hsplit : w.take s ++ w.drop s = w := List.take_append_drop s w
    cases i with
    | zero =>
      have hm : m = 0 := by simp only [packRowsN_length] at hlast; omega
      subst hm
      have hw0 : w.drop s = [] := List.eq_nil_of_length_eq_zero (by simpa using htb)
      have hwe : w.take s = w := by
        conv_rhs => rw [← hsplit]
        rw [hw0, List.append_nil]
      show asgOf (rowVals d q (w.take s)) (packLastCol s) = _
      rw [packRow_lastCol d s q w hta, hwe]
    | succ j =>
      have hcf : classifyFrom d q w
          = classifyFrom d (classifyFrom d q (w.take s)) (w.drop s) := by
        have h' := classifyFrom_append d (w.take s) (w.drop s) q
        rwa [hsplit] at h'
      rw [hcf]
      exact packRowsN_last d s m (classifyFrom d q (w.take s)) (w.drop s) htb j
        (by simpa [packRowsN] using h) (by simpa [packRowsN] using hlast)

/-! ## §3 — ⚑ THE GATE: a real `Satisfied2Public` witness for the PACKED descriptor. -/

/-- The witness's public inputs: `pi[initial_state] = q`, `pi[final_state] = f`. -/
def packPub (q f : Nat) : Assignment :=
  fun k => if k = 1 then Int.ofNat f else Int.ofNat q

/-- The witness's table family: the declared run table at `TRT_TID`, empty elsewhere. -/
def packTf (tbl : List (List Nat)) : TraceFamily :=
  fun id => if id = TRT_TID then exactPublicTable tbl else []

/-- **THE PACKED WITNESS**: `m` rows, `s` steps each, running `d` from `q` on `w`. -/
def packWit (d : TableDfa Nat Nat) (s m q : Nat) (w : List Nat) : VmTrace :=
  { rows := packRowsN d s m q w
  , pub  := packPub q (classifyFrom d q w)
  , tf   := packTf (runTable d q w) }

/-- `memOpsOf` at the constraint-list level (the SAME matcher, so no re-elaboration drift). -/
def memOpsL (cs : List VmConstraint2) : List MemOp :=
  memOpsOf { name := "", traceWidth := 0, piCount := 0, tables := []
           , constraints := cs, hashSites := [], ranges := [] }

/-- `mapOpsOf` at the constraint-list level. -/
def mapOpsL (cs : List VmConstraint2) : List MapOp :=
  mapOpsOf { name := "", traceWidth := 0, piCount := 0, tables := []
           , constraints := cs, hashSites := [], ranges := [] }

theorem memOpsL_append (a b : List VmConstraint2) : memOpsL (a ++ b) = memOpsL a ++ memOpsL b :=
  List.filterMap_append

theorem mapOpsL_append (a b : List VmConstraint2) : mapOpsL (a ++ b) = mapOpsL a ++ mapOpsL b :=
  List.filterMap_append

theorem memOpsL_packLookups : ∀ (j o : Nat), memOpsL (packLookups o j) = []
  | 0,     _ => rfl
  | j + 1, o => memOpsL_packLookups j (o + 2)

theorem mapOpsL_packLookups : ∀ (j o : Nat), mapOpsL (packLookups o j) = []
  | 0,     _ => rfl
  | j + 1, o => mapOpsL_packLookups j (o + 2)

theorem packed_memOps (name : String) (s : Nat) (tbl : List (List Nat)) :
    memOpsOf (packedDesc name s tbl) = [] := by
  show memOpsL (packLookups 0 s ++ packTail s) = []
  rw [memOpsL_append, memOpsL_packLookups]
  rfl

theorem packed_mapOps (name : String) (s : Nat) (tbl : List (List Nat)) :
    mapOpsOf (packedDesc name s tbl) = [] := by
  show mapOpsL (packLookups 0 s ++ packTail s) = []
  rw [mapOpsL_append, mapOpsL_packLookups]
  rfl

theorem packed_memLog (name : String) (s : Nat) (tbl : List (List Nat)) (t : VmTrace) :
    memLog (packedDesc name s tbl) t = [] := by
  simp [memLog, packed_memOps]

theorem packed_mapLog (name : String) (s : Nat) (tbl : List (List Nat)) (t : VmTrace) :
    mapLog (packedDesc name s tbl) t = [] := by
  simp [mapLog, packed_mapOps]

/-- The packed descriptor's whole per-row selector output IS `tupsFrom 0 s`. -/
theorem packed_rowSel (name : String) (s : Nat) (tbl : List (List Nat)) (row : Assignment) :
    (packedDesc name s tbl).constraints.filterMap (tupSel row) = tupsFrom 0 s row := by
  have hcs : (packedDesc name s tbl).constraints = packLookups 0 s ++ packTail s := rfl
  have htail : (packTail s).filterMap (tupSel row) = [] := rfl
  rw [hcs, List.filterMap_append, filterMap_packLookups, htail, List.append_nil]

/-- The packed descriptor's lookup log IS the trace's per-row tuples, flattened. -/
theorem packed_lookupLog (name : String) (s : Nat) (tbl : List (List Nat)) (t : VmTrace) :
    lookupLog (packedDesc name s tbl) t TRT_TID
      = t.rows.flatMap (fun row => tupsFrom 0 s row) := by
  show t.rows.flatMap (fun row => (packedDesc name s tbl).constraints.filterMap (tupSel row)) = _
  induction t.rows with
  | nil => rfl
  | cons a rest ih =>
    rw [List.flatMap_cons, List.flatMap_cons, ih, packed_rowSel]

/-- ⚑ **THE GATE.** The packed witness PROVABLY satisfies the emitted packed descriptor —
GENERAL in the automaton `d`, the pack factor `s`, the chunk count `m`, the start state `q`, the
word `w` (subject only to `|w| = m · s`), and the descriptor name. -/
theorem packWit_satisfies (d : TableDfa Nat Nat) (s m q : Nat) (w : List Nat)
    (hw : w.length = m * s) (name : String) :
    Satisfied2Public hash0 (packedDesc name s (runTable d q w))
      (fun _ => 0) (fun _ => (0, 0)) [] (packWit d s m q w) where
  rowConstraints := by
    intro i hi c hc
    have hrows : (packWit d s m q w).rows = packRowsN d s m q w := rfl
    have hi' : i < (packRowsN d s m q w).length := hi
    have hloc : (envAt (packWit d s m q w) i).loc = (packRowsN d s m q w)[i]'hi' :=
      envAt_loc (t := packWit d s m q w) hi
    rw [show (packedDesc name s (runTable d q w)).constraints
        = packLookups 0 s ++ packTail s from rfl] at hc
    rcases List.mem_append.mp hc with hlk | htl
    · -- ONE OF THE `s` TRANSITION LOOKUPS: the evaluated tuple is a DECLARED row, by construction.
      obtain ⟨l, rfl, hlt⟩ := packLookups_form s 0 c hlk
      show l.tuple.map (·.eval (envAt (packWit d s m q w) i).loc)
        ∈ (packWit d s m q w).tf l.table
      rw [hlt]
      show _ ∈ packTf (runTable d q w) TRT_TID
      rw [show packTf (runTable d q w) TRT_TID = exactPublicTable (runTable d q w) from rfl,
        ← packRowsN_flat d s m q w hw, hloc]
      have hmemRow : l.tuple.map (·.eval ((packRowsN d s m q w)[i]'hi'))
          ∈ tupsFrom 0 s ((packRowsN d s m q w)[i]'hi') := by
        rw [← filterMap_packLookups s 0]
        exact List.mem_filterMap.mpr ⟨.lookup l, hlk, by simp [tupSel, hlt]⟩
      exact List.mem_flatMap.mpr ⟨(packRowsN d s m q w)[i]'hi', List.getElem_mem hi', hmemRow⟩
    · simp only [packTail, List.mem_cons, List.not_mem_nil, or_false] at htl
      rcases htl with rfl | rfl | rfl
      · -- THE CONTINUITY WINDOW: adjacent rows chain.
        show WindowConstraint.holdsAt (envAt (packWit d s m q w) i)
          (i + 1 == (packWit d s m q w).rows.length)
          ⟨.add (.nxt 0) (.mul (.const (-1)) (.loc (packLastCol s))), true⟩
        simp only [WindowConstraint.holdsAt, if_true]
        intro hnl
        have hlt : i + 1 < (packRowsN d s m q w).length := by
          have hne' : ¬ (i + 1 = (packRowsN d s m q w).length) := by
            intro hEq
            rw [hrows, hEq] at hnl
            simp at hnl
          omega
        have hnxt : (envAt (packWit d s m q w) i).nxt = (packRowsN d s m q w)[i + 1]'hlt :=
          envAt_nxt (t := packWit d s m q w) hlt
        have hch : ((packRowsN d s m q w)[i + 1]'hlt) 0
            = ((packRowsN d s m q w)[i]'hi') (packLastCol s) :=
          packRowsN_chain d s m q w hw i hlt
        show (WindowExpr.add (.nxt 0) (.mul (.const (-1)) (.loc (packLastCol s)))).eval
          (envAt (packWit d s m q w) i) ≡ 0 [ZMOD 2013265921]
        simp only [WindowExpr.eval]
        rw [hloc, hnxt, hch]
        have hz : ((packRowsN d s m q w)[i]'hi') (packLastCol s)
            + (-1) * ((packRowsN d s m q w)[i]'hi') (packLastCol s) = 0 := by ring
        rw [hz]
      · -- B1: the FIRST row's `q₀` IS `pi[initial_state]`.
        show (i == 0) = true → (envAt (packWit d s m q w) i).loc 0
          ≡ (envAt (packWit d s m q w) i).pub PI_INITIAL [ZMOD 2013265921]
        intro hf
        have hi0 : i = 0 := by simpa using hf
        subst hi0
        rw [hloc, packRowsN_head d s m q w hi']
        exact Int.ModEq.refl _
      · -- B2: the LAST row's `q_s` IS `pi[final_state]` — the classification.
        show (i + 1 == (packWit d s m q w).rows.length) = true →
          (envAt (packWit d s m q w) i).loc (packLastCol s)
            ≡ (envAt (packWit d s m q w) i).pub PI_FINAL [ZMOD 2013265921]
        intro hl
        have hlast : i + 1 = (packRowsN d s m q w).length := by
          rw [hrows] at hl; simpa using hl
        rw [hloc, packRowsN_last d s m q w hw i hi' hlast]
        exact Int.ModEq.refl _
  rowHashes := by intro i _; trivial
  rowRanges := by
    intro i _ r hr
    simp only [packedDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by rw [packed_memLog]; simp
  memDisciplined := by rw [packed_memLog]; trivial
  memBalanced := by rw [packed_memLog]; exact memCheck_nil _ _
  memTableFaithful := by rw [packed_memLog]; rfl
  mapTableFaithful := by rw [packed_mapLog]; rfl
  publicTablesFaithful := by
    intro td htd
    simp only [packedDesc, List.mem_singleton] at htd
    subst htd
    show packTf (runTable d q w) TRT_TID = exactPublicTable (runTable d q w)
    rfl
  publicLookupBalanced := by
    intro td htd
    simp only [packedDesc, List.mem_singleton] at htd
    subst htd
    show (lookupLog (packedDesc name s (runTable d q w)) (packWit d s m q w) TRT_TID).Perm
      (exactPublicTable (runTable d q w))
    rw [packed_lookupLog]
    show ((packRowsN d s m q w).flatMap (fun row => tupsFrom 0 s row)).Perm _
    rw [packRowsN_flat d s m q w hw]

/-! ## §4 — ⚑ PACKING DOES NOT CHANGE THE VERDICT. -/

/-- **THE CORRECTNESS THEOREM (constructed witness).** The packed witness's exposed public
`final_state` IS `classifyFrom d q w` — the SAME word, the SAME verdict, at `n / s` rows instead
of `n`. Its trace has exactly `m = |w| / s` rows. -/
theorem packWit_final_state (d : TableDfa Nat Nat) (s m q : Nat) (w : List Nat) :
    (packWit d s m q w).pub PI_FINAL = Int.ofNat (classifyFrom d q w)
      ∧ (packWit d s m q w).rows.length = m :=
  ⟨rfl, packRowsN_length d s m q w⟩

/-- **THE GENERAL (soundness) DIRECTION AT `s = 1`.** For ANY trace satisfying the emitted packed
descriptor at `s = 1` — not merely the constructed one — the exposed public `final_state` IS the
genuine classification of the word the trace's symbol column reads. Inherited by `rfl` from
`tableRouting_refines_classify`, which is what `packed_one_eq_tableRouting` buys. The `s > 1`
general direction is a NAMED RESIDUAL (module note). -/
theorem packed_one_refines_classify
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {name : String} {tbl : List (List Nat)} {t : VmTrace}
    (d : TableDfa Nat Nat)
    (htbl : ∀ r ∈ tbl, ∃ s y, r = [s, y, d.step s y])
    (hsmall : ∀ r ∈ tbl, ∀ v ∈ r, v < 2013265921)
    (hsat : Satisfied2Public hash (packedDesc name 1 tbl) minit mfin maddrs t)
    (hne : t.rows ≠ [])
    (q0 : ℕ) (hstart : t.pub PI_INITIAL = Int.ofNat q0) (hq0 : q0 < 2013265921)
    (fN : ℕ) (hfin : t.pub PI_FINAL = Int.ofNat fN) (hfN : fN < 2013265921) :
    fN = classifyFrom d q0 (t.rows.map (fun a => (a SYMBOL).toNat)) :=
  (tableRouting_refines_classify d htbl hsmall
    (by rwa [packed_one_eq_tableRouting] at hsat) hne q0 hstart hq0 fN hfin hfN).2

/-! ## §5 — THE CONCRETE PACKED INSTANCES + the measured shape.

`probeW` is the 8-symbol probe word of `TinyAutomataSatisfiable`; `prodI 4` is the 4-fold product
of the four independent tiny automata. `packK4 s` is the packed descriptor at pack factor `s`;
`packK4Wit s m` its witness. `s ∈ {1, 2, 4, 8}` all divide 8. -/

/-- The packed 4-automaton product descriptor at pack factor `s`, over the 8-symbol probe word. -/
def packK4 (s : Nat) : EffectVmDescriptor2 :=
  packedDesc s!"tiny-automata-indep-product-packed-s{s}::exact-public-v1" s
    (runTable (prodI 4) 0 probeW)

/-- Its witness (`8 / s` rows). -/
def packK4Wit (s m : Nat) : VmTrace := packWit (prodI 4) s m 0 probeW

/-- ⚑ **THE GATE, FIRED at `s = 1, 2, 4, 8` on the composed 4-automaton product.** Every cost
quoted below is the cost of an object with THIS satisfying trace. -/
theorem packK4_satisfies_s1 :
    Satisfied2Public hash0 (packK4 1) (fun _ => 0) (fun _ => (0, 0)) [] (packK4Wit 1 8) :=
  packWit_satisfies (prodI 4) 1 8 0 probeW (by decide) _

theorem packK4_satisfies_s2 :
    Satisfied2Public hash0 (packK4 2) (fun _ => 0) (fun _ => (0, 0)) [] (packK4Wit 2 4) :=
  packWit_satisfies (prodI 4) 2 4 0 probeW (by decide) _

theorem packK4_satisfies_s4 :
    Satisfied2Public hash0 (packK4 4) (fun _ => 0) (fun _ => (0, 0)) [] (packK4Wit 4 2) :=
  packWit_satisfies (prodI 4) 4 2 0 probeW (by decide) _

theorem packK4_satisfies_s8 :
    Satisfied2Public hash0 (packK4 8) (fun _ => 0) (fun _ => (0, 0)) [] (packK4Wit 8 1) :=
  packWit_satisfies (prodI 4) 8 1 0 probeW (by decide) _

/-- ⚑ **THE CORRECTED COST NUMBER, AS A `Prop` — NON-VACUITY of the repaired cost model.**
`TinyAutomataCompose.costOf_forced_sound` FIRES on this file's own `s = 4` witness: the cost
record's `forcedTraceRows` is `pinned` at the row count the witness ACTUALLY carries. This is the
descriptor that broke the old model (which reported the declared count, 8, at every `s`), and the
agreement is now a theorem rather than two `#guard`s that happen to match. -/
theorem packK4_forced_rows_s4 :
    (costOf (packK4 4)).forcedTraceRows
      = .pinned (packK4Wit 4 2).rows.length := by
  have hval : (costOf (packK4 4)).forcedTraceRows = .pinned 2 := by rfl
  refine (costOf_forced_sound packK4_satisfies_s4).resolve_right ?_
  rw [hval]
  exact fun h => ForcedRows.noConfusion h

/-- …and that row count is `2` — `n / s` = 8 / 4, the packing genuinely happening. -/
theorem packK4_forced_rows_s4_value : (packK4Wit 4 2).rows.length = 2 :=
  (packWit_final_state (prodI 4) 4 2 0 probeW).2

/-- ⚑ **AND THE VERDICT IS UNCHANGED AT EVERY PACK FACTOR.** All four witnesses expose the SAME
public `final_state`, and it is `classifyFrom (prodI 4) 0 probeW` — the composed 4-automaton
classification of the SAME 8-symbol word. Trace lengths `8, 4, 2, 1`. -/
theorem packK4_same_verdict :
    ((packK4Wit 1 8).pub PI_FINAL = Int.ofNat (classifyFrom (prodI 4) 0 probeW)
      ∧ (packK4Wit 1 8).rows.length = 8)
    ∧ ((packK4Wit 2 4).pub PI_FINAL = Int.ofNat (classifyFrom (prodI 4) 0 probeW)
      ∧ (packK4Wit 2 4).rows.length = 4)
    ∧ ((packK4Wit 4 2).pub PI_FINAL = Int.ofNat (classifyFrom (prodI 4) 0 probeW)
      ∧ (packK4Wit 4 2).rows.length = 2)
    ∧ ((packK4Wit 8 1).pub PI_FINAL = Int.ofNat (classifyFrom (prodI 4) 0 probeW)
      ∧ (packK4Wit 8 1).rows.length = 1) :=
  ⟨packWit_final_state (prodI 4) 1 8 0 probeW, packWit_final_state (prodI 4) 2 4 0 probeW,
   packWit_final_state (prodI 4) 4 2 0 probeW, packWit_final_state (prodI 4) 8 1 0 probeW⟩

/-- ⚑ **AND THE PACKED VERDICT IS THE COMPONENTWISE ONE.** The exposed `final_state` decodes,
mixed-radix, to every one of the FOUR component automata's own classification of `probeW` —
inherited unchanged from `TinyAutomataSatisfiable.prodRunWit_k4_components`, because the packed
witness exposes the SAME `pi[final_state]` as the unpacked one. -/
theorem packK4_exposes_components :
    (packK4Wit 4 2).pub PI_FINAL
      = Int.ofNat (encodeDigits IRADIX (List.zipWith (fun d q => classifyFrom d q probeW)
          (famI 4) (List.replicate 4 0))) := by
  show Int.ofNat (classifyFrom (prodI 4) 0 probeW) = _
  rw [prodRunWit_k4_components.2]

/-! ### §5a — the measured shape of the packed family (compiled evaluation, NO `Prop`).

⚠ Every `#guard` below is COMPILED EVALUATION of a closed `Bool`. It proves NO `Prop`. The `Prop`
content is `packK4_satisfies_s{1,2,4,8}` (the witnesses), `packK4_same_verdict` (the verdict is
preserved) and `TinyAutomataCompose.forced_trace_length` (why the declared table pins the length). -/

-- ⚑ THE PACK LAW in the descriptor's own cost record: trace width `2s + 1`; `s + 3` constraints;
-- ONE table of 8 declared rows AT EVERY `s` (packing does NOT shrink the declared table) — and
-- `forcedTraceRows = .pinned (8 / s)` = 8, 4, 2, 1, because the packed descriptor targets that one
-- table with `lookupCount = s` lookups and `forced_trace_length` reads `rows × lookupCount =
-- declaredRows`.
-- (HISTORY: this record used to report `forcedTraceRows := 8` at EVERY `s` — a `Nat` field that
-- carried the DECLARED row count and was therefore correct only at `lookupCount = 1`. The model was
-- repaired in `TinyAutomataCompose` §1a; `costOf_forced_sound` now proves the published number is
-- the row count of any trace that satisfies the descriptor, so it agrees with the witnesses below
-- by THEOREM rather than by the two `#guard`s happening to match.)
#guard (List.map (fun s => costOf (packK4 s)) [1, 2, 4, 8]) ==
  [ { traceWidth := 3,  piCount := 2, constraints := 4,  tables := 1
    , declaredRows := 8, forcedTraceRows := .pinned 8, nonlinearMults := 0 }
  , { traceWidth := 5,  piCount := 2, constraints := 5,  tables := 1
    , declaredRows := 8, forcedTraceRows := .pinned 4, nonlinearMults := 0 }
  , { traceWidth := 9,  piCount := 2, constraints := 7,  tables := 1
    , declaredRows := 8, forcedTraceRows := .pinned 2, nonlinearMults := 0 }
  , { traceWidth := 17, piCount := 2, constraints := 11, tables := 1
    , declaredRows := 8, forcedTraceRows := .pinned 1, nonlinearMults := 0 } ]

-- ⚑ THE ACTUAL TRACE LENGTHS the four WITNESSES carry: 8, 4, 2, 1 — `n / s`. The cost record above
-- now reads the SAME four numbers off the descriptor alone.
#guard (List.map (fun p => ((packK4Wit p.1 p.2).rows.length))
  [(1, 8), (2, 4), (4, 2), (8, 1)]) == [8, 4, 2, 1]

-- ⚑ AREA: `(2s + 1) · (n / s)` = 24, 20, 18, 17, computed BOTH ways — off the cost record (left)
-- and off the witness's own trace length (right) — and they agree. The area FALLS with `s` but only
-- towards the `2n + s` floor: the width grows as the height shrinks. This is why the profile's
-- width-sensitive first-digest layer predicts a SUBLINEAR time win.
#guard (List.map (fun p => ((costOf (packK4 p.1)).area,
    some ((packWidth p.1) * ((packK4Wit p.1 p.2).rows.length))))
  [(1, 8), (2, 4), (4, 2), (8, 1)])
  == [(some 24, some 24), (some 20, some 20), (some 18, some 18), (some 17, some 17)]

-- The emitted WIRE BYTES of the packed descriptors (the verifier-held object).
#guard (List.map (fun s => jsonBytes (packK4 s)) [1, 2, 4, 8]) == [673, 763, 943, 1316]

-- Byte identity of the `s = 1` packed descriptor with the UNPACKED run-table descriptor — the
-- family really does contain the deployed shape.
#guard emitVmJson2 (packK4 1) ==
  emitVmJson2 (tableRoutingDesc "tiny-automata-indep-product-packed-s1::exact-public-v1"
    (runTable (prodI 4) 0 probeW))

/-! ## §5b — ⚑ THE MEASUREMENT FAMILY: a packed descriptor at ANY `(n, s)` with `s ∣ n`, and its
witness. `EmitTinyAutomataPacked.lean` dumps `emitVmJson2 (packMeas n s)` together with the
COLUMN VALUES of `packMeasWit n s`, and `circuit/tests/tiny_automata_packed_rows_measure.rs`
proves and verifies exactly those bytes. So every prove-time number quoted for `packMeas n s` is
the cost of an object carrying `packMeas_satisfies`. -/

/-- A deterministic `n`-symbol probe word over `Σ = {0, 1}`. -/
def probeN (n : Nat) : List Nat := (List.range n).map (fun i => (i * 7 + i / 3) % 2)

theorem probeN_length (n : Nat) : (probeN n).length = n := by
  simp [probeN]

/-- The measured packed descriptor: the 4-fold independent product, `n` symbols, `s` per row. -/
def packMeas (n s : Nat) : EffectVmDescriptor2 :=
  packedDesc s!"tiny-automata-packed-n{n}-s{s}::exact-public-v1" s
    (runTable (prodI 4) 0 (probeN n))

/-- Its witness: `n / s` rows of width `2s + 1`. -/
def packMeasWit (n s : Nat) : VmTrace := packWit (prodI 4) s (n / s) 0 (probeN n)

/-- ⚑ **THE GATE FOR EVERY MEASURED POINT.** For any `n` and any `s ∣ n`, the emitted
`packMeas n s` HAS a satisfying trace — `packMeasWit n s`, with exactly `n / s` rows. -/
theorem packMeas_satisfies (n s : Nat) (hdvd : s ∣ n) :
    Satisfied2Public hash0 (packMeas n s) (fun _ => 0) (fun _ => (0, 0)) []
      (packMeasWit n s) :=
  packWit_satisfies (prodI 4) s (n / s) 0 (probeN n)
    (by rw [probeN_length]; exact (Nat.div_mul_cancel hdvd).symm) _

/-- …and its trace length is exactly `n / s`, with the verdict `classifyFrom (prodI 4) 0` of the
SAME `n`-symbol word at every `s`. -/
theorem packMeas_rows_and_verdict (n s : Nat) :
    (packMeasWit n s).pub PI_FINAL = Int.ofNat (classifyFrom (prodI 4) 0 (probeN n))
      ∧ (packMeasWit n s).rows.length = n / s :=
  packWit_final_state (prodI 4) s (n / s) 0 (probeN n)

/-! ## §6 — axiom tripwires. -/

#assert_axioms getD_append
#assert_axioms runTable_append
#assert_axioms classifyFrom_append
#assert_axioms packed_one_eq_tableRouting
#assert_axioms rowVals_head
#assert_axioms rowVals_length
#assert_axioms rowVals_last
#assert_axioms packLookups_form
#assert_axioms filterMap_packLookups
#assert_axioms packLookups_filterMap_none
#assert_axioms tupsFrom_rowVals
#assert_axioms tupsFrom_rowVals_nil
#assert_axioms packRowsN_length
#assert_axioms packRow_lastCol
#assert_axioms packRowsN_flat
#assert_axioms packRowsN_head
#assert_axioms packRowsN_chain
#assert_axioms packRowsN_last
#assert_axioms packed_memLog
#assert_axioms packed_mapLog
#assert_axioms packed_rowSel
#assert_axioms packed_lookupLog
#assert_axioms packWit_satisfies
#assert_axioms packWit_final_state
#assert_axioms packed_one_refines_classify
#assert_axioms packK4_satisfies_s1
#assert_axioms packK4_satisfies_s2
#assert_axioms packK4_satisfies_s4
#assert_axioms packK4_satisfies_s8
#assert_axioms packK4_forced_rows_s4
#assert_axioms packK4_forced_rows_s4_value
#assert_axioms packK4_same_verdict
#assert_axioms packK4_exposes_components
#assert_axioms probeN_length
#assert_axioms packMeas_satisfies
#assert_axioms packMeas_rows_and_verdict

end Dregg2.Circuit.Emit.TinyAutomataPacked
