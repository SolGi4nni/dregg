/-
# Dregg2.Circuit.Emit.UnforcedPiPins — the PI pins that bind NOTHING, censused and SUBTRACTED.

## The wound

A `.piBinding row col k` is `local[col] ≡ pi[k]` on the tagged row. That is a BINDING only when
something ELSE in the descriptor forces `local[col]`. When no other constraint, hash site or range
tooth reads `col`, the prover chooses BOTH sides: it picks the column value, publishes it at `pi[k]`,
and the pin is satisfied by construction. The published value is then host trust wearing an AIR's
clothes — a full node compensates by OVERWRITING `pi[k]` from its own trusted turn before
verifying, but **a light client has no host to do the overwriting**.

MEASURED over the three deployed registries (`circuit/descriptors/rotation-{v3-staged,wide-
registry-staged,wide-umem-welded-registry-staged}.tsv`): of 1639 pins in the 57 wide members, **167
pin a column that NOTHING else in the member references at all**, and a further 48 pin a column
that is referenced only on a DIFFERENT row than the pin fires on (the `.transition` continuity
chain: the first row's before-commit, the last row's after-commit). 215 published slots in all.

⚑ **A CENSUS IS A MEASUREMENT, NOT A VERDICT ON THE PIN.** 144 of the 159 this module deleted from
`v3Registry` were the `withDfaRcPins` DFA route-commitment quartet, and deleting them took the
`CarrierWitness::Dsl` fold arm down with them (`ivc_turn_chain::dsl_rc_claim_pi_lo` locates the rc
slot BY the pin and fails closed). The deletion was still RIGHT: the carrier was read by nothing,
so the pin bound nothing. The repair was to make the columns FORCED — the rc carrier is now folded
into the published caveat commitment (`EffectVmEmitRotationCaveat.caveatCommitRc`,
`EffectVmEmitRotationV3.caveatV3SitesAt`'s two new sites) — after which the SAME unchanged
subtraction keeps the pins. **Never exempt a pin from this census to bring one back.**

## What this module is

The library twin of `RotWideCompactE1`'s DERIVED kill-set, one level up: `RotWideCompactE1` deletes
columns no constraint references; this deletes PINS whose column no NON-PIN constraint references.
The two compose — after `dropUnforcedPins` the columns those pins named are provably DEAD
(`dropUnforcedPins_col_dead`), so the existing E1 compaction removes them with its already-proven
`compactE1_expand` bridge.

  * `forcedCols M`    — every column a NON-pin constraint / hash site / range tooth reads.
  * `unforcedPins M`  — the census: the pins whose column is not in `forcedCols M`.
  * `dropUnforcedPins M` — the subtraction. Constraints only: `piCount` is UNCHANGED, so the PI
    vector shape every producer builds is untouched (the slot survives as what it always was — a
    verifier-supplied input the AIR ignores — instead of a pin that pretends to bind it).

## The evidence: `unforced_pin_admits_any_value`

The gate for a NEW binding is "a proof publishing a value inconsistent with the trace is REFUSED by
the AIR alone". The gate for a DELETION is the dual, and it is what this module proves: taking any
satisfying witness and overwriting the column AND its published slots with an ARBITRARY `v` yields
another satisfying witness of the SAME descriptor. So the pin refuses nothing; deleting it removes
no refusal. That is the machine-checked statement that these 215 slots are prover-chosen.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Dregg2.Circuit.Emit.RotWideCompactS2

namespace Dregg2.Circuit.Emit.UnforcedPiPins

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.RotWideCompactS2 (refsE refsW refsC refs2 refsSite)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the census. -/

/-- Is this constraint a PI pin? -/
def isPin : VmConstraint2 → Bool
  | .base (.piBinding _ _ _) => true
  | _                        => false

/-- Every PI pin of a descriptor, as `(row, column, pi index)`. -/
def pinsOf (M : EffectVmDescriptor2) : List (VmRow × Nat × Nat) :=
  M.constraints.filterMap fun c => match c with
    | .base (.piBinding r col k) => some (r, col, k)
    | _                          => none

/-- **`forcedCols M`** — every column some NON-PIN constraint, hash site or range tooth reads.
A column outside this list is touched by pins ONLY: no equation of the descriptor relates it to
anything, so the prover may set it to whatever it likes. -/
def forcedCols (M : EffectVmDescriptor2) : List Nat :=
  (M.constraints.filter (fun c => !isPin c)).flatMap refs2
    ++ M.hashSites.flatMap refsSite
    ++ M.ranges.map (fun r => r.wire)

/-- Decidable "this pinned column is forced by nothing else". -/
def pinUnforced (M : EffectVmDescriptor2) (col : Nat) : Bool :=
  !(forcedCols M).contains col

/-- **The census** — every pin whose column no non-pin constraint reads. -/
def unforcedPins (M : EffectVmDescriptor2) : List (VmRow × Nat × Nat) :=
  (pinsOf M).filter (fun p => pinUnforced M p.2.1)

/-- The PI slots the census condemns (what a light client is told is bound and is not). -/
def unforcedPiSlots (M : EffectVmDescriptor2) : List Nat :=
  (unforcedPins M).map (fun p => p.2.2)

/-- **The subtraction.** Drop exactly the unforced pins; keep `piCount`, `tables`, `hashSites`,
`ranges` and every other constraint verbatim. The dropped slots do not disappear from the PI
vector — they become what they always were, verifier-supplied inputs the AIR ignores — so no
producer's PI vector shape changes. -/
def dropUnforcedPins (M : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { M with
    constraints := M.constraints.filter (fun c => match c with
      | .base (.piBinding _ col _) => !pinUnforced M col
      | _                          => true) }

/-! ## §2 — structural facts about the subtraction. -/

/-- Every surviving constraint was already a constraint of `M`. -/
theorem dropUnforcedPins_mem {M : EffectVmDescriptor2} {c : VmConstraint2}
    (hc : c ∈ (dropUnforcedPins M).constraints) : c ∈ M.constraints :=
  List.mem_of_mem_filter hc

/-- The subtraction touches only the constraint list. -/
theorem dropUnforcedPins_shape (M : EffectVmDescriptor2) :
    (dropUnforcedPins M).traceWidth = M.traceWidth
    ∧ (dropUnforcedPins M).piCount = M.piCount
    ∧ (dropUnforcedPins M).hashSites = M.hashSites
    ∧ (dropUnforcedPins M).ranges = M.ranges
    ∧ (dropUnforcedPins M).tables = M.tables :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A NON-pin constraint always survives the subtraction. -/
theorem dropUnforcedPins_keeps_nonpin {M : EffectVmDescriptor2} {c : VmConstraint2}
    (hc : c ∈ M.constraints) (hnp : isPin c = false) : c ∈ (dropUnforcedPins M).constraints := by
  refine List.mem_filter.mpr ⟨hc, ?_⟩
  cases c with
  | base b => cases b with
    | piBinding r col k => simp [isPin] at hnp
    | gate _ => rfl
    | transition _ _ => rfl
    | boundary _ _ => rfl
  | lookup _ => rfl
  | memOp _ => rfl
  | mapOp _ => rfl
  | umemOp _ => rfl
  | proofBind _ => rfl
  | windowGate _ => rfl

/-- The subtraction removes no mem-op (it removes only `.base` pins). -/
theorem dropUnforcedPins_memOpsOf (M : EffectVmDescriptor2) :
    memOpsOf (dropUnforcedPins M) = memOpsOf M := by
  show List.filterMap _ (List.filter _ M.constraints) = List.filterMap _ M.constraints
  induction M.constraints with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | base b =>
      cases b with
      | piBinding r col k => by_cases h : pinUnforced M col <;> simp [h, ih]
      | gate _ => simpa using ih
      | transition _ _ => simpa using ih
      | boundary _ _ => simpa using ih
    | lookup _ => simpa using ih
    | memOp m => simpa using ih
    | mapOp _ => simpa using ih
    | umemOp _ => simpa using ih
    | proofBind _ => simpa using ih
    | windowGate _ => simpa using ih

/-- The subtraction removes no map-op. -/
theorem dropUnforcedPins_mapOpsOf (M : EffectVmDescriptor2) :
    mapOpsOf (dropUnforcedPins M) = mapOpsOf M := by
  show List.filterMap _ (List.filter _ M.constraints) = List.filterMap _ M.constraints
  induction M.constraints with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | base b =>
      cases b with
      | piBinding r col k => by_cases h : pinUnforced M col <;> simp [h, ih]
      | gate _ => simpa using ih
      | transition _ _ => simpa using ih
      | boundary _ _ => simpa using ih
    | lookup _ => simpa using ih
    | memOp _ => simpa using ih
    | mapOp m => simpa using ih
    | umemOp _ => simpa using ih
    | proofBind _ => simpa using ih
    | windowGate _ => simpa using ih

/-- **THE PEEL** — a satisfying witness of `M` satisfies the subtracted descriptor. (Dropping
constraints only weakens; the mem/map legs are literally the same logs.) -/
theorem satisfied2_dropUnforcedPins (hash : List ℤ → ℤ) (M : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash M minit mfin maddrs t) :
    Satisfied2 hash (dropUnforcedPins M) minit mfin maddrs t := by
  have hmem : memLog (dropUnforcedPins M) t = memLog M t := by
    unfold memLog; rw [dropUnforcedPins_memOpsOf]
  have hmap : mapLog (dropUnforcedPins M) t = mapLog M t := by
    unfold mapLog; rw [dropUnforcedPins_mapOpsOf]
  refine
    { rowConstraints := ?_, rowHashes := ?_, rowRanges := ?_
    , memAddrsNodup := h.memAddrsNodup, memClosed := ?_, memDisciplined := ?_
    , memBalanced := ?_, memTableFaithful := ?_, mapTableFaithful := ?_ }
  · intro i hi c hc; exact h.rowConstraints i hi c (dropUnforcedPins_mem hc)
  · intro i hi; exact h.rowHashes i hi
  · intro i hi r hr; exact h.rowRanges i hi r hr
  · intro op hop; exact h.memClosed op (by rwa [hmem] at hop)
  · rw [hmem]; exact h.memDisciplined
  · rw [hmem]; exact h.memBalanced
  · rw [hmem]; exact h.memTableFaithful
  · rw [hmap]; exact h.mapTableFaithful

/-! ## §2a — the subtraction is COMPLETE in one pass (it cannot leave a censused pin behind). -/

/-- The forced surface is invariant under the subtraction: it counts NON-pin constraints, and the
subtraction removes only pins. -/
theorem filter_nonpin_dropUnforcedPins (M : EffectVmDescriptor2) :
    (dropUnforcedPins M).constraints.filter (fun c => !isPin c)
      = M.constraints.filter (fun c => !isPin c) := by
  show List.filter _ (List.filter _ M.constraints) = List.filter _ M.constraints
  rw [List.filter_filter]
  refine List.filter_congr (fun c _ => ?_)
  cases c with
  | base b =>
    cases b with
    | piBinding r col k => simp [isPin]
    | gate _ => simp [isPin]
    | transition _ _ => simp [isPin]
    | boundary _ _ => simp [isPin]
  | lookup _ => simp [isPin]
  | memOp _ => simp [isPin]
  | mapOp _ => simp [isPin]
  | umemOp _ => simp [isPin]
  | proofBind _ => simp [isPin]
  | windowGate _ => simp [isPin]

/-- The forced surface is invariant under the subtraction. -/
theorem forcedCols_dropUnforcedPins (M : EffectVmDescriptor2) :
    forcedCols (dropUnforcedPins M) = forcedCols M := by
  unfold forcedCols
  rw [filter_nonpin_dropUnforcedPins]
  rfl

/-- **The subtraction is a FIXPOINT**: no unforced pin survives it. A second pass finds nothing —
so the census number after the re-emit is ZERO by theorem, not by re-measurement. -/
theorem unforcedPins_dropUnforcedPins (M : EffectVmDescriptor2) :
    unforcedPins (dropUnforcedPins M) = [] := by
  have hf : ∀ col, pinUnforced (dropUnforcedPins M) col = pinUnforced M col := by
    intro col; unfold pinUnforced; rw [forcedCols_dropUnforcedPins]
  unfold unforcedPins
  refine List.filter_eq_nil_iff.mpr ?_
  intro p hp
  simp only [hf]
  -- `p` came from a pin the drop KEPT, i.e. one whose column is forced
  unfold pinsOf at hp
  obtain ⟨c, hc, hval⟩ := List.mem_filterMap.mp hp
  have hkeep := (List.mem_filter.mp hc).2
  cases c with
  | base b =>
    cases b with
    | piBinding r col k =>
      have hp2 : p = (r, col, k) := by simpa using hval.symm
      subst hp2
      simpa using hkeep
    | gate _ => simp at hval
    | transition _ _ => simp at hval
    | boundary _ _ => simp at hval
  | lookup _ => simp at hval
  | memOp _ => simp at hval
  | mapOp _ => simp at hval
  | umemOp _ => simp at hval
  | proofBind _ => simp at hval
  | windowGate _ => simp at hval

/-! ## §3 — after the subtraction the column is DEAD (so E1 deletes it).

`RotWideCompactE1.liveCols` is the reference surface the derived kill-set complements. An
unforced pin's column is not in the NON-pin surface by definition, and after `dropUnforcedPins`
no pin names it either — so it is not live at all, and `deadColsE1` picks it up. -/

/-- Every reference of the SUBTRACTED descriptor's constraints lands in `forcedCols M`. -/
theorem dropUnforcedPins_refs_forced (M : EffectVmDescriptor2) (c : VmConstraint2)
    (hc : c ∈ (dropUnforcedPins M).constraints) (x : Nat) (hx : x ∈ refs2 c) :
    x ∈ forcedCols M := by
  have hmemM : c ∈ M.constraints := dropUnforcedPins_mem hc
  have hkeep := (List.mem_filter.mp hc).2
  by_cases hp : isPin c
  · -- a SURVIVING pin: its column is forced (that is exactly the filter's predicate)
    cases c with
    | base b =>
      cases b with
      | piBinding r col k =>
        have : (!pinUnforced M col) = true := by simpa using hkeep
        have hcol : (forcedCols M).contains col = true := by
          simp only [pinUnforced, Bool.not_not] at this; exact this
        have : x = col := by
          simpa [refs2, refsC] using hx
        subst this
        exact List.mem_of_elem_eq_true (by simpa using hcol)
      | gate _ => simp [isPin] at hp
      | transition _ _ => simp [isPin] at hp
      | boundary _ _ => simp [isPin] at hp
    | lookup _ => simp [isPin] at hp
    | memOp _ => simp [isPin] at hp
    | mapOp _ => simp [isPin] at hp
    | umemOp _ => simp [isPin] at hp
    | proofBind _ => simp [isPin] at hp
    | windowGate _ => simp [isPin] at hp
  · -- a NON-pin constraint: its references are the first component of `forcedCols`
    have hnp : isPin c = false := by simpa using hp
    refine List.mem_append_left _ (List.mem_append_left _ ?_)
    exact List.mem_flatMap.mpr ⟨c, List.mem_filter.mpr ⟨hmemM, by simp [hnp]⟩, hx⟩

/-- **The deadness certificate** — an unforced pin's column is referenced by NO constraint of the
subtracted descriptor. (Hash sites and range teeth are already excluded by `forcedCols`.) -/
theorem dropUnforcedPins_col_dead (M : EffectVmDescriptor2) (r : VmRow) (col k : Nat)
    (hmem : (r, col, k) ∈ unforcedPins M)
    (c : VmConstraint2) (hc : c ∈ (dropUnforcedPins M).constraints) : col ∉ refs2 c := by
  intro hx
  have hforced := dropUnforcedPins_refs_forced M c hc col hx
  have hun : pinUnforced M col = true := by
    have := (List.mem_filter.mp hmem).2
    simpa using this
  simp only [pinUnforced, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hun
  exact hun hforced

/-! ## §4 — THE EVIDENCE: an unforced pin admits ANY published value.

The congruence spine: an expression's value depends only on the columns it reads. -/

/-- Overwrite one column of an assignment. -/
def setCol (a : Assignment) (col : Nat) (v : ℤ) : Assignment :=
  fun x => if x = col then v else a x

theorem setCol_off {a : Assignment} {col : Nat} {v : ℤ} {x : Nat} (h : x ≠ col) :
    setCol a col v x = a x := by simp [setCol, h]

/-- The PI slots that `col`'s pins publish. -/
def pinSlotsOf (M : EffectVmDescriptor2) (col : Nat) : List Nat :=
  M.constraints.filterMap fun c => match c with
    | .base (.piBinding _ c' k) => if c' = col then some k else none
    | _                         => none

theorem mem_pinSlotsOf {M : EffectVmDescriptor2} {r : VmRow} {col k : Nat}
    (h : VmConstraint2.base (.piBinding r col k) ∈ M.constraints) : k ∈ pinSlotsOf M col :=
  List.mem_filterMap.mpr ⟨_, h, by simp⟩

theorem pinSlotsOf_spec {M : EffectVmDescriptor2} {col k : Nat} (h : k ∈ pinSlotsOf M col) :
    ∃ r : VmRow, VmConstraint2.base (.piBinding r col k) ∈ M.constraints := by
  obtain ⟨c, hc, hval⟩ := List.mem_filterMap.mp h
  cases c with
  | base b =>
    cases b with
    | piBinding r c' k' =>
      by_cases hcc : c' = col
      · subst hcc
        simp only [ite_true] at hval
        exact ⟨r, by simpa [Option.some_inj.mp hval] using hc⟩
      · simp [hcc] at hval
    | gate _ => simp at hval
    | transition _ _ => simp at hval
    | boundary _ _ => simp at hval
  | lookup _ => simp at hval
  | memOp _ => simp at hval
  | mapOp _ => simp at hval
  | umemOp _ => simp at hval
  | proofBind _ => simp at hval
  | windowGate _ => simp at hval

/-- Overwrite every PI slot `col`'s pins publish. -/
def setPub (M : EffectVmDescriptor2) (col : Nat) (a : Assignment) (v : ℤ) : Assignment :=
  fun k => if k ∈ pinSlotsOf M col then v else a k

/-- `EmittedExpr.eval` depends only on the columns the expression reads. -/
theorem evalE_congr (e : EmittedExpr) (a b : Assignment) (h : ∀ x ∈ refsE e, a x = b x) :
    e.eval a = e.eval b := by
  induction e with
  | var v => simpa [EmittedExpr.eval] using h v (by simp [refsE])
  | const k => rfl
  | add p q ihp ihq =>
    have hp : ∀ x ∈ refsE p, a x = b x := fun x hx => h x (by simp [refsE, hx])
    have hq : ∀ x ∈ refsE q, a x = b x := fun x hx => h x (by simp [refsE, hx])
    simp [EmittedExpr.eval, ihp hp, ihq hq]
  | mul p q ihp ihq =>
    have hp : ∀ x ∈ refsE p, a x = b x := fun x hx => h x (by simp [refsE, hx])
    have hq : ∀ x ∈ refsE q, a x = b x := fun x hx => h x (by simp [refsE, hx])
    simp [EmittedExpr.eval, ihp hp, ihq hq]

/-- The `setCol` corollary: a column the expression never reads cannot change its value. -/
theorem evalE_setCol (e : EmittedExpr) (a : Assignment) (col : Nat) (v : ℤ)
    (h : col ∉ refsE e) : e.eval (setCol a col v) = e.eval a :=
  evalE_congr e _ _ (fun x hx => setCol_off (fun hxe => h (hxe ▸ hx)))

/-- `WindowExpr.eval` depends only on the columns the expression reads (both rows). -/
theorem evalW_congr (w : WindowExpr) (e f : VmRowEnv)
    (hl : ∀ x ∈ refsW w, e.loc x = f.loc x) (hn : ∀ x ∈ refsW w, e.nxt x = f.nxt x) :
    w.eval e = w.eval f := by
  induction w with
  | loc c => simpa [WindowExpr.eval] using hl c (by simp [refsW])
  | nxt c => simpa [WindowExpr.eval] using hn c (by simp [refsW])
  | const k => rfl
  | add p q ihp ihq =>
    simp [WindowExpr.eval,
      ihp (fun x hx => hl x (by simp [refsW, hx])) (fun x hx => hn x (by simp [refsW, hx])),
      ihq (fun x hx => hl x (by simp [refsW, hx])) (fun x hx => hn x (by simp [refsW, hx]))]
  | mul p q ihp ihq =>
    simp [WindowExpr.eval,
      ihp (fun x hx => hl x (by simp [refsW, hx])) (fun x hx => hn x (by simp [refsW, hx])),
      ihq (fun x hx => hl x (by simp [refsW, hx])) (fun x hx => hn x (by simp [refsW, hx]))]

/-- **`unforced_pin_row_admits_any_value`** — the row-level no-op. On any row window, if `col` is
read by no constraint of `M` except pins, then overwriting `col` (in BOTH row slices) and every PI
slot pinned to `col` with an ARBITRARY `v` preserves every constraint of `M` — provided no OTHER
column shares a PI slot with `col` (`hsole`, true of every censused pin: each is the only pin on
its slot).

This is the exact dual of a forgery tooth. A binding REFUSES an inconsistent publication; this pin
ACCEPTS every publication, so it refuses nothing and deleting it removes no refusal. -/
theorem unforced_pin_row_admits_any_value
    (hash : List ℤ → ℤ) (tf : TraceFamily) (M : EffectVmDescriptor2) (col : Nat) (v : ℤ)
    (hcol : col ∉ forcedCols M)
    -- the PI slots reached by `col`'s pins are reached by NO other column's pin
    (hsole : ∀ (r' : VmRow) (c' k' : Nat),
      VmConstraint2.base (.piBinding r' c' k') ∈ M.constraints →
      (∃ r'' : VmRow, VmConstraint2.base (.piBinding r'' col k') ∈ M.constraints) → c' = col)
    (env : VmRowEnv) (isFirst isLast : Bool)
    (h : ∀ c ∈ M.constraints, c.holdsAt hash tf env isFirst isLast) :
    ∀ c ∈ M.constraints,
      c.holdsAt hash tf
        { loc := setCol env.loc col v
        , nxt := setCol env.nxt col v
        , pub := setPub M col env.pub v } isFirst isLast := by
  intro c hc
  set env' : VmRowEnv :=
    { loc := setCol env.loc col v
    , nxt := setCol env.nxt col v
    , pub := setPub M col env.pub v } with henv'
  -- a NON-pin constraint of `M` never reads `col`
  have hnotref : ∀ d ∈ M.constraints, isPin d = false → col ∉ refs2 d := by
    intro d hd hnp hx
    exact hcol (List.mem_append_left _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨d, List.mem_filter.mpr ⟨hd, by simp [hnp]⟩, hx⟩)))
  have hbase := h c hc
  cases c with
  | base b =>
    cases b with
    | gate body =>
      have hb : col ∉ refsE body := by
        have := hnotref _ hc rfl; simpa [refs2, refsC] using this
      cases isLast with
      | true => trivial
      | false =>
        show body.eval env'.loc ≡ 0 [ZMOD 2013265921]
        have : body.eval env'.loc = body.eval env.loc := evalE_setCol body env.loc col v hb
        rw [this]; exact hbase
    | transition hi lo =>
      have href := hnotref _ hc rfl
      have hhi : col ≠ sbCol hi := by intro hh; exact href (by simp [refs2, refsC, hh])
      have hlo : col ≠ saCol lo := by intro hh; exact href (by simp [refs2, refsC, hh])
      cases isLast with
      | true => trivial
      | false =>
        show env'.nxt (sbCol hi) ≡ env'.loc (saCol lo) [ZMOD 2013265921]
        have h1 : env'.nxt (sbCol hi) = env.nxt (sbCol hi) := setCol_off (Ne.symm hhi)
        have h2 : env'.loc (saCol lo) = env.loc (saCol lo) := setCol_off (Ne.symm hlo)
        rw [h1, h2]; exact hbase
    | boundary rr body =>
      have hb : col ∉ refsE body := by
        have := hnotref _ hc rfl; simpa [refs2, refsC] using this
      have heq : body.eval env'.loc = body.eval env.loc := evalE_setCol body env.loc col v hb
      cases rr with
      | first => intro hf; rw [heq]; exact hbase hf
      | last  => intro hl; rw [heq]; exact hbase hl
    | piBinding rr c' k' =>
      by_cases hcc : c' = col
      · -- the pin lands on `col` itself: BOTH sides are now `v`, so it holds unconditionally
        subst hcc
        have hpub : env'.pub k' = v := by
          show setPub M c' env.pub v k' = v
          exact if_pos (mem_pinSlotsOf hc)
        have hloc : env'.loc c' = v := by
          show setCol env.loc c' v c' = v
          simp [setCol]
        cases rr with
        | first => intro _; rw [hloc, hpub]
        | last  => intro _; rw [hloc, hpub]
      · -- a pin on a DIFFERENT column: its slot is untouched (`hsole`), its column is untouched
        have hslot : k' ∉ pinSlotsOf M col := by
          intro hk
          exact hcc (hsole rr c' k' hc (pinSlotsOf_spec hk))
        have hpub : env'.pub k' = env.pub k' := by
          show setPub M col env.pub v k' = env.pub k'
          exact if_neg hslot
        have hloc : env'.loc c' = env.loc c' := setCol_off hcc
        cases rr with
        | first => intro hf; rw [hloc, hpub]; exact hbase hf
        | last  => intro hl; rw [hloc, hpub]; exact hbase hl
  | lookup l =>
    have href := hnotref _ hc rfl
    show (l.tuple.map (·.eval env'.loc)) ∈ tf l.table
    have : l.tuple.map (·.eval env'.loc) = l.tuple.map (·.eval env.loc) := by
      refine List.map_congr_left ?_
      intro e he
      exact evalE_setCol e env.loc col v (fun hx =>
        href (by simpa [refs2] using List.mem_flatMap.mpr ⟨e, he, hx⟩))
    rw [this]; exact hbase
  | memOp _ => trivial
  | mapOp m =>
    have href := hnotref _ hc rfl
    have hguard : col ∉ refsE m.guard := fun hx => href (by simp [refs2, hx])
    have hkey : col ∉ refsE m.key := fun hx => href (by simp [refs2, hx])
    have hval : col ∉ refsE m.value := fun hx => href (by simp [refs2, hx])
    have hroot : ∀ i : Fin 8, col ∉ refsE (m.root i) := by
      intro i hx
      have hin : col ∈ (List.ofFn m.root).flatMap refsE :=
        List.mem_flatMap.mpr ⟨m.root i, List.mem_ofFn.mpr ⟨i, rfl⟩, hx⟩
      refine href ?_
      simp only [refs2, List.mem_append]
      tauto
    have hnew : ∀ i : Fin 8, col ∉ refsE (m.newRoot i) := by
      intro i hx
      have hin : col ∈ (List.ofFn m.newRoot).flatMap refsE :=
        List.mem_flatMap.mpr ⟨m.newRoot i, List.mem_ofFn.mpr ⟨i, rfl⟩, hx⟩
      refine href ?_
      simp only [refs2, List.mem_append]
      tauto
    have hall : m.holdsAt hash env' = m.holdsAt hash env := by
      unfold MapOp.holdsAt
      rw [evalE_setCol m.guard env.loc col v hguard, evalE_setCol m.key env.loc col v hkey,
        evalE_setCol m.value env.loc col v hval,
        evalE_setCol (m.root 0) env.loc col v (hroot 0),
        evalE_setCol (m.newRoot 0) env.loc col v (hnew 0)]
    show m.holdsAt hash env'
    rw [hall]; exact hbase
  | umemOp _ => trivial
  | proofBind _ => trivial
  | windowGate w =>
    have href := hnotref _ hc rfl
    have hb : col ∉ refsW w.body := fun hx => href (by simpa [refs2] using hx)
    have heq : w.body.eval env' = w.body.eval env :=
      evalW_congr w.body env' env
        (fun x hx => setCol_off (fun hxe => hb (hxe ▸ hx)))
        (fun x hx => setCol_off (fun hxe => hb (hxe ▸ hx)))
    show WindowConstraint.holdsAt env' isLast w
    have hb2 : WindowConstraint.holdsAt env isLast w := hbase
    unfold WindowConstraint.holdsAt at hb2 ⊢
    rw [heq]; exact hb2

/-! ## §5 — THE CENSUS, machine-checked on the deployed registry object.

`v3Registry` is the library object the emit driver renders into
`circuit/descriptors/rotation-v3-staged-registry.tsv` (and, through `wideAppend`, into the two wide
registries). These `#guard`s are the census: they cannot rot, and they go RED the moment a member
gains or loses an unforced pin. -/

/-- Total PI pins over the registry. -/
def registryPinCount (R : List (String × EffectVmDescriptor2)) : Nat :=
  (R.map (fun p => (pinsOf p.2).length)).foldl (· + ·) 0

/-- Total UNFORCED PI pins over the registry — the number this module exists to drive to zero. -/
def registryUnforcedCount (R : List (String × EffectVmDescriptor2)) : Nat :=
  (R.map (fun p => (unforcedPins p.2).length)).foldl (· + ·) 0

open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (v3Registry)

-- MEASURED 2026-07-31 on `v3Registry` (36 members), AFTER the rc FOLD: 607 pins, of which **15
-- bind nothing**. It was 159 on 2026-07-30; the 144 that left the census are the `withDfaRcPins`
-- DFA route-commitment quartet on each of the 36 members, and they left it by becoming FORCED —
-- `EffectVmEmitRotationV3.caveatV3SitesAt` now absorbs the carrier into the PUBLISHED caveat
-- commitment, so a chip site reads those columns. NOT by an exemption: `dropUnforcedPins` is
-- unchanged and still drops every pin whose column no non-pin constraint reads.
#guard v3Registry.length == 36
#guard registryPinCount v3Registry == 607
#guard registryUnforcedCount v3Registry == 15

-- The classes, per member. `transfer` is now **0** — its only unforced pins WERE the rc quartet.
-- `custom` carries 14: the limbs of the 8-felt program-VK / proof-commitment octets that
-- `proofBind` does NOT reach (it binds limb 0 of each). `mint` carries 1.
#guard ((v3Registry.lookup "transferVmDescriptor2R24").map (fun M => (unforcedPins M).length))
  == some 0
#guard ((v3Registry.lookup "customVmDescriptor2R24").map (fun M => (unforcedPins M).length))
  == some 14
#guard ((v3Registry.lookup "mintVmDescriptor2R24").map (fun M => (unforcedPins M).length))
  == some 1
-- ...and NO other member has an unforced pin left at all.
#guard (v3Registry.filter (fun p => (unforcedPins p.2).length != 0)).map (·.1)
  == ["mintVmDescriptor2R24", "customVmDescriptor2R24"]

-- THE SUBTRACTION, executed on the registry object: zero unforced pins survive.
#guard registryUnforcedCount (v3Registry.map (fun p => (p.1, dropUnforcedPins p.2))) == 0
-- and it costs exactly the 15 pins, no others.
#guard registryPinCount (v3Registry.map (fun p => (p.1, dropUnforcedPins p.2))) == 607 - 15
-- ⚑ THE rc-FOLD DELTA, arithmetic and machine-checked: the emit now KEEPS 592 pins where it kept
-- 448 before (`607 - 159`), and the difference is EXACTLY four per member — the rc quartet, on all
-- 36. This is the line that would go red if a future edit restored the pins by exempting them
-- instead of by forcing their columns: an exemption would change `unforcedPins`, not this delta.
#guard registryPinCount (v3Registry.map (fun p => (p.1, dropUnforcedPins p.2)))
  - (607 - 159) == 4 * v3Registry.length

#assert_axioms dropUnforcedPins_mem
#assert_axioms filter_nonpin_dropUnforcedPins
#assert_axioms forcedCols_dropUnforcedPins
#assert_axioms unforcedPins_dropUnforcedPins
#assert_axioms satisfied2_dropUnforcedPins
#assert_axioms dropUnforcedPins_col_dead
#assert_axioms evalE_congr
#assert_axioms evalW_congr
#assert_axioms unforced_pin_row_admits_any_value

end Dregg2.Circuit.Emit.UnforcedPiPins
