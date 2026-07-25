/-
# Dregg2.Games.DungeonCompleteness — uniform capability and completeness laws.

This file closes two named seams between the native Lean model (`Dungeon`) and its
Lean-authored `Exec.RecordProgram` model (`DungeonProgram`):

* the key-exhibition inversion is uniform over every deployed keyed way (2, 3, 4),
  rather than a theorem specialized to way 2;
* the exact boundary of honest model-to-program completeness is formalized: the
  coarse `Inv` is insufficient, while every actually replay-reachable state
  preserves the stronger per-relic provenance relation the program requires.

Honest scope: every theorem here is about the name-keyed, signed-`Int`
`Exec.RecordProgram` model.  It does not claim refinement to the deployed unsigned
evaluator; `DungeonProgram.lean` records that separate substrate seam.
-/
import Dregg2.Games.DungeonProgram

namespace Dregg2.Games.Dungeon.Prog

open Dregg2.Exec (Value)

/-! ⚑ Every law below is stated over the DAY'S WORLD (`Dungeon.WorldParam`): the map is
drawn from the committed day-seed, so `homeCode` and `guardHp` are parameters, not
constants. The completeness boundary (`ModelProgramInv`) is therefore uniform over the
whole drawn family, not a fact about one shipped layout. -/
variable [WorldParam]

-- The world parameter is blanket-scoped over the file (every rule and law is stated over
-- the day's drawn map); a handful of pure list/count helpers legitimately do not mention
-- it, and the section-variable linter would otherwise report each one.
set_option linter.unusedSectionVars false

/-! ## 1. Every deployed way exercises its corresponding key capability. -/

open Dregg2.Exec in
/-- Negative tooth: changing any deployed keyed way while mutating/omitting its
required carried-key exhibit is refused. -/
theorem way_flip_key_mutation_refused (w : Nat) (hwLo : 2 ≤ w) (hwHi : w ≤ FLOORS)
    {m : Nat} (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6)
    {o n : Value}
    (hflip : (o.scalar (wayName w) == n.scalar (wayName w)) = false)
    (hmut : n.scalar (relicName (keyFor w)) ≠ some (CARRIED : Int)) :
    RecordProgram.admits dungeonExec m o n = false := by
  cases hadm : RecordProgram.admits dungeonExec m o n with
  | false => rfl
  | true =>
    have hwHi' : w ≤ 4 := hwHi
    have hw : w = 2 ∨ w = 3 ∨ w = 4 := by omega
    exact False.elim (hmut ((way_flip_exhibits_key w hw hm hadm hflip).1))

-- The generic theorem bites away from the old way-2-only canary: way 3 cannot be
-- opened from genesis while its key relic remains in the deep — driven on EVERY day of
-- the drawn family, not just the shipped map.
#guard (List.range dayCount).all (fun k =>
  (Dregg2.Exec.RecordProgram.admits (@dungeonExec (instAt k)) 2
      (encode (@genesisState (instAt k)))
      (setF (setF (encode (@genesisState (instAt k))) (wayName 3) 1) "spent" 1)) == false)

/-! ## 2. The exact model-to-program completeness boundary. -/

-- `Nat.repr` is opaque to the ordinary simplifier.  These tiny byte-level pins let
-- the proofs below reduce lookups in the fixed, deployed 4-floor/8-relic schema.
@[simp] private theorem wayName_2 : wayName 2 = "way_2" := by decide
@[simp] private theorem wayName_3 : wayName 3 = "way_3" := by decide
@[simp] private theorem wayName_4 : wayName 4 = "way_4" := by decide
@[simp] private theorem hoardName_1 : hoardName 1 = "hoard_1" := by decide
@[simp] private theorem hoardName_2 : hoardName 2 = "hoard_2" := by decide
@[simp] private theorem hoardName_3 : hoardName 3 = "hoard_3" := by decide
@[simp] private theorem hoardName_4 : hoardName 4 = "hoard_4" := by decide
@[simp] private theorem relicName_0 : relicName 0 = "relic_0" := by decide
@[simp] private theorem relicName_1 : relicName 1 = "relic_1" := by decide
@[simp] private theorem relicName_2 : relicName 2 = "relic_2" := by decide
@[simp] private theorem relicName_3 : relicName 3 = "relic_3" := by decide
@[simp] private theorem relicName_4 : relicName 4 = "relic_4" := by decide
@[simp] private theorem relicName_5 : relicName 5 = "relic_5" := by decide
@[simp] private theorem relicName_6 : relicName 6 = "relic_6" := by decide
@[simp] private theorem relicName_7 : relicName 7 = "relic_7" := by decide
@[simp] private theorem range_relics :
    List.range RELICS = [0, 1, 2, 3, 4, 5, 6, 7] := by decide

open Dregg2.Exec in
private theorem encode_scalar_depth (s : DState) :
    (encode s).scalar "depth" = some (s.depth : Int) := by
  simp [encode, Value.scalar, Value.field]

open Dregg2.Exec in
private theorem encode_scalar_spent (s : DState) :
    (encode s).scalar "spent" = some (s.spent : Int) := by
  simp [encode, Value.scalar, Value.field]

open Dregg2.Exec in
private theorem encode_scalar_wounds (s : DState) :
    (encode s).scalar "wounds" = some (s.wounds : Int) := by
  simp [encode, Value.scalar, Value.field]

open Dregg2.Exec in
private theorem encode_scalar_harm (s : DState) :
    (encode s).scalar "harm" = some (s.harm : Int) := by
  simp [encode, Value.scalar, Value.field]

open Dregg2.Exec in
private theorem encode_scalar_fate (s : DState) :
    (encode s).scalar "fate" = some (s.fate : Int) := by
  simp [encode, Value.scalar, Value.field]

open Dregg2.Exec in
private theorem encode_scalar_pack (s : DState) :
    (encode s).scalar "pack" = some (pack s : Int) := by
  simp [encode, Value.scalar, Value.field]

open Dregg2.Exec in
private theorem encode_scalar_bank (s : DState) :
    (encode s).scalar "bank" = some (bank s : Int) := by
  simp [encode, Value.scalar, Value.field]

open Dregg2.Exec in
private theorem encode_scalar_way (s : DState) (w : Nat) (hwLo : 2 ≤ w)
    (hwHi : w ≤ FLOORS) :
    (encode s).scalar (wayName w) = some (s.ways.getD (w - 2) 0 : Int) := by
  have hwHi' : w ≤ 4 := hwHi
  have hw : w = 2 ∨ w = 3 ∨ w = 4 := by omega
  rcases hw with rfl | rfl | rfl <;>
    simp [encode, Value.scalar, Value.field]

open Dregg2.Exec in
private theorem encode_scalar_hoard (s : DState) (d : Nat) (hdLo : 1 ≤ d)
    (hdHi : d ≤ FLOORS) :
    (encode s).scalar (hoardName d) = some (hoardAt s d : Int) := by
  have hdHi' : d ≤ 4 := hdHi
  have hd : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by omega
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp [encode, Value.scalar, Value.field]

open Dregg2.Exec in
private theorem encode_scalar_relic (s : DState) (i : Nat) (hi : i < RELICS) :
    (encode s).scalar (relicName i) = some (s.custody.getD i 0 : Int) := by
  have hi' : i < 8 := hi
  have hiCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    omega
  rcases hiCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [encode, Value.scalar, Value.field]

attribute [simp] encode_scalar_depth encode_scalar_spent encode_scalar_wounds
  encode_scalar_harm encode_scalar_fate encode_scalar_pack encode_scalar_bank

open Dregg2.Exec in
@[simp] private theorem encode_scalar_way2 (s : DState) :
    (encode s).scalar "way_2" = some (s.ways.getD 0 0 : Int) := by
  simpa using encode_scalar_way s 2 (by decide) (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_way3 (s : DState) :
    (encode s).scalar "way_3" = some (s.ways.getD 1 0 : Int) := by
  simpa using encode_scalar_way s 3 (by decide) (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_way4 (s : DState) :
    (encode s).scalar "way_4" = some (s.ways.getD 2 0 : Int) := by
  simpa using encode_scalar_way s 4 (by decide) (by decide)

open Dregg2.Exec in
@[simp] private theorem encode_scalar_hoard1 (s : DState) :
    (encode s).scalar "hoard_1" = some (hoardAt s 1 : Int) := by
  simpa using encode_scalar_hoard s 1 (by decide) (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_hoard2 (s : DState) :
    (encode s).scalar "hoard_2" = some (hoardAt s 2 : Int) := by
  simpa using encode_scalar_hoard s 2 (by decide) (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_hoard3 (s : DState) :
    (encode s).scalar "hoard_3" = some (hoardAt s 3 : Int) := by
  simpa using encode_scalar_hoard s 3 (by decide) (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_hoard4 (s : DState) :
    (encode s).scalar "hoard_4" = some (hoardAt s 4 : Int) := by
  simpa using encode_scalar_hoard s 4 (by decide) (by decide)

open Dregg2.Exec in
@[simp] private theorem encode_scalar_relic0 (s : DState) :
    (encode s).scalar "relic_0" = some (s.custody.getD 0 0 : Int) := by
  simpa using encode_scalar_relic s 0 (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_relic1 (s : DState) :
    (encode s).scalar "relic_1" = some (s.custody.getD 1 0 : Int) := by
  simpa using encode_scalar_relic s 1 (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_relic2 (s : DState) :
    (encode s).scalar "relic_2" = some (s.custody.getD 2 0 : Int) := by
  simpa using encode_scalar_relic s 2 (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_relic3 (s : DState) :
    (encode s).scalar "relic_3" = some (s.custody.getD 3 0 : Int) := by
  simpa using encode_scalar_relic s 3 (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_relic4 (s : DState) :
    (encode s).scalar "relic_4" = some (s.custody.getD 4 0 : Int) := by
  simpa using encode_scalar_relic s 4 (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_relic5 (s : DState) :
    (encode s).scalar "relic_5" = some (s.custody.getD 5 0 : Int) := by
  simpa using encode_scalar_relic s 5 (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_relic6 (s : DState) :
    (encode s).scalar "relic_6" = some (s.custody.getD 6 0 : Int) := by
  simpa using encode_scalar_relic s 6 (by decide)
open Dregg2.Exec in
@[simp] private theorem encode_scalar_relic7 (s : DState) :
    (encode s).scalar "relic_7" = some (s.custody.getD 7 0 : Int) := by
  simpa using encode_scalar_relic s 7 (by decide)

/-- Every relic's minted home is a real floor — now a consequence of the DAY'S world law
(`Dungeon.wf_home_floor`), where it used to be a `decide` on a hard-wired list. -/
private theorem homeCode_le_floors (i : Nat) (hi : i < RELICS) :
    homeCode i ≤ FLOORS := by
  have hlen : homeFloors.length = RELICS := wf_homes_length
  have hi' : i < homeFloors.length := by rw [hlen]; exact hi
  show homeFloors.getD i 0 ≤ FLOORS
  rw [← List.getElem_eq_getD (l := homeFloors) (i := i) (h := hi') 0]
  exact (wf_home_floor (List.getElem_mem hi')).2

/-- The extra relation the authored program enforces beyond `Dungeon.Inv`: each
relic may occupy its own minted home, carried, or banked -- never another relic's
home floor.  `Dungeon.Inv` intentionally says only "some floor" and is therefore
too weak for universal model-to-program completeness (counterexample below). -/
def CustodyHomeWF (s : DState) : Prop :=
  ∀ i, i < RELICS →
    s.custody[i]? = some (homeCode i) ∨
    s.custody[i]? = some CARRIED ∨
    s.custody[i]? = some BANKED

/-- The exact model-side invariant needed by the current authored program. -/
def ModelProgramInv (s : DState) : Prop := Inv s ∧ CustodyHomeWF s

theorem modelProgramInv_genesis : ModelProgramInv genesisState := by
  refine ⟨inv_genesis, ?_⟩
  intro i hi
  left
  have hlen : homeFloors.length = RELICS := wf_homes_length
  have hi' : i < homeFloors.length := by rw [hlen]; exact hi
  show homeFloors[i]? = some (homeFloors.getD i 0)
  rw [List.getElem?_eq_getElem hi', List.getElem_eq_getD (0 : Nat)]

/-- The home-specific custody alphabet is preserved by every legal model move. -/
theorem modelProgramInv_step {s s' : DState} {m : Move}
    (hInv : ModelProgramInv s) (hstep : step s m = some s') :
    ModelProgramInv s' := by
  refine ⟨inv_step hInv.1 hstep, ?_⟩
  intro i hi
  have hhome := hInv.2 i hi
  cases m with
  | delve =>
    simp only [step] at hstep
    split at hstep
    · cases hstep; exact hhome
    · exact absurd hstep (by simp)
  | unlock w =>
    simp only [step] at hstep
    split at hstep
    · cases hstep; exact hhome
    · exact absurd hstep (by simp)
  | smite =>
    simp only [step] at hstep
    split at hstep
    · cases hstep; exact hhome
    · exact absurd hstep (by simp)
  | lunge =>
    simp only [step] at hstep
    split at hstep
    · cases hstep; exact hhome
    · exact absurd hstep (by simp)
  | loot r =>
    simp only [step] at hstep
    split at hstep
    · cases hstep
      by_cases hir : i = r
      · subst r
        have hlen : i < s.custody.length := by
          have := hInv.1.1.1
          omega
        rw [List.getElem?_set_self hlen]
        exact Or.inr (Or.inl rfl)
      · rw [List.getElem?_set_ne (by omega)]
        exact hhome
    · exact absurd hstep (by simp)
  | flee =>
    simp only [step] at hstep
    split at hstep
    · cases hstep
      rcases hhome with hh | hc | hb
      · rw [List.getElem?_map, hh]
        left
        have hHomeLt : homeCode i < CARRIED := by
          have := homeCode_le_floors i hi
          have hFloorNum : FLOORS < CARRIED := by decide
          omega
        simp [show homeCode i ≠ CARRIED by omega]
      · rw [List.getElem?_map, hc]
        right; right; rfl
      · rw [List.getElem?_map, hb]
        right; right
        simp [show BANKED ≠ CARRIED by decide]
    · exact absurd hstep (by simp)

/-! ### Why `Inv` alone cannot imply completeness. -/

/-- An `Inv` state in which relic 1 sits at floor 2 rather than its minted home 1.
The model's coarse custody alphabet permits this state; the authored program's
provenance tooth deliberately does not. -/
def wrongHomeState : DState :=
  { depth := 0, spent := 0, wounds := 0, harm := 0, fate := 0, ways := [0, 0, 0],
    custody := [4, 2, 2, 3, 1, 1, 2, 3] }

theorem wrongHomeState_inv : Inv wrongHomeState := by
  simp [wrongHomeState, Inv, CustodyWF, pack, bank, FLOORS, RELICS,
        CAP, CARRIED, BANKED]

/-- The obstruction is exhibited on DAY 0's map (`instAt 0`, the shipped layout): a
concrete counterexample needs a concrete world. Nothing about it is special to day 0 —
`Inv` is world-blind, while the provenance tooth is minted per-relic on whatever map the
day drew. -/
theorem wrongHomeState_delve_legal :
    @step (instAt 0) wrongHomeState .delve = some { wrongHomeState with
      depth := 1, wounds := 0, spent := 1 } := by decide

theorem wrongHomeState_delve_refused :
    Dregg2.Exec.RecordProgram.admits (@dungeonExec (instAt 0)) (moveIdx .delve)
      (encode wrongHomeState)
      (encode { wrongHomeState with depth := 1, wounds := 0, spent := 1 }) = false := by
  decide

/-! ### Count/custody bridge used by every honest verb. -/

private theorem custody_count_partition (l : List Nat)
    (hcodes : ∀ c ∈ l, (1 ≤ c ∧ c ≤ FLOORS) ∨ c = CARRIED ∨ c = BANKED) :
    l.countP (· == CARRIED) + l.countP (· == BANKED) +
      l.countP (· == 1) + l.countP (· == 2) +
      l.countP (· == 3) + l.countP (· == 4) = l.length := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    have ha := hcodes a (by simp)
    have hrest : ∀ c ∈ rest,
        (1 ≤ c ∧ c ≤ FLOORS) ∨ c = CARRIED ∨ c = BANKED := by
      intro c hc
      exact hcodes c (by simp [hc])
    have hpart := ih hrest
    have haCases : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = CARRIED ∨ a = BANKED := by
      rcases ha with hfloor | hcarried | hbanked
      · have hFloor : a ≤ 4 := hfloor.2
        omega
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcarried))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hbanked))))
    rcases haCases with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [CARRIED, BANKED] at hpart ⊢ <;> omega

private theorem zones_total_of_inv {s : DState} (hInv : Inv s) :
    pack s + bank s + hoardAt s 1 + hoardAt s 2 + hoardAt s 3 + hoardAt s 4 = RELICS := by
  have hpart := custody_count_partition s.custody hInv.1.2
  have hlen : s.custody.length = RELICS := hInv.1.1
  simp only [pack, bank, hoardAt] at *
  omega

open Dregg2.Exec in
private theorem encode_sum_zones_of_inv {s : DState} (hInv : Inv s) :
    sumScalars (encode s) zones = some (RELICS : Int) := by
  have htotal := zones_total_of_inv hInv
  have htotalZ : (pack s : Int) + (bank s : Int) + (hoardAt s 1 : Int) +
      (hoardAt s 2 : Int) + (hoardAt s 3 : Int) + (hoardAt s 4 : Int) =
      (RELICS : Int) := by
    exact_mod_cast htotal
  simp [sumScalars, zones]
  simpa [RELICS, add_comm, add_left_comm, add_assoc] using htotalZ

open Dregg2.Exec in
@[simp] private theorem encode_scalar_sentinel (s : DState) :
    (encode s).scalar sentinelField = some 1 := by
  simp [encode, Value.scalar, Value.field, sentinelField]

private theorem legal_step_fate {s s' : DState} {m : Move}
    (hstep : step s m = some s') :
    s.fate = 0 ∧ (s'.fate = 0 ∨ s'.fate = 1) := by
  cases m <;> simp only [step] at hstep <;> split at hstep
  all_goals first | (cases hstep; simp_all) | exact absurd hstep (by simp)

private theorem legal_step_spent_eq {s s' : DState} {m : Move}
    (hstep : step s m = some s') : s'.spent = s.spent + price m := by
  cases m <;> simp only [step] at hstep <;> split at hstep
  all_goals first | (cases hstep; rfl) | exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem coreTeeth_honest {s s' : DState} {m : Move}
    (hInv : ModelProgramInv s) (hstep : step s m = some s') :
    ∀ c ∈ coreTeeth, evalConstraint c.toExec (encode s) (encode s') = true := by
  intro c hc
  have hPost := modelProgramInv_step hInv hstep
  have hsum := encode_sum_zones_of_inv hPost.1
  have hspend := step_spends hstep
  have hfate := legal_step_fate hstep
  simp only [coreTeeth, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · simp [Constraint.toExec, evalConstraint, hsum]
  · apply (evalConstraint_affineLe_iff _ _ _ _).2
    refine ⟨(pack s' : Int) + (s'.depth : Int) + (s'.harm : Int), ?_, ?_⟩
    · simp only [affineSum, List.map_cons, List.map_nil, List.foldr_cons,
        List.foldr_nil, encode_scalar_pack, encode_scalar_depth, encode_scalar_harm,
        Option.some.injEq]
      ring
    · exact_mod_cast hPost.1.2.2.2.2.2.1
  · exact (evalSimple_strictMono_iff "spent" (encode s) (encode s')).2
      ⟨s.spent, s'.spent, by simp, by simp, by exact_mod_cast hspend⟩
  · simp only [Constraint.toExec, evalConstraint]
    unfold evalSimple
    rw [encode_scalar_spent]
    change decide ((s'.spent : Int) ≤ (BREATH : Int)) = true
    exact decide_eq_true (by exact_mod_cast hPost.1.2.1)
  · simp only [Constraint.toExec, evalConstraint, encode_scalar_fate]
    rcases hfate with ⟨ho, hn | hn⟩ <;> simp [ho, hn]

private theorem getElem?_eq_some_getD {l : List Nat} {i bound : Nat}
    (hlen : l.length = bound) (hi : i < bound) : l[i]? = some (l.getD i 0) := by
  have hil : i < l.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil]
  rfl

private theorem custody_getD_mono {s s' : DState} {m : Move}
    (hInv : ModelProgramInv s) (hstep : step s m = some s')
    (i : Nat) (hi : i < RELICS) : s.custody.getD i 0 ≤ s'.custody.getD i 0 := by
  have hPost := modelProgramInv_step hInv hstep
  exact custody_ratchet hInv.1 hstep i (s.custody.getD i 0) (s'.custody.getD i 0)
    (getElem?_eq_some_getD hInv.1.1.1 hi)
    (getElem?_eq_some_getD hPost.1.1.1 hi)

private theorem custody_getD_home {s : DState} (hInv : ModelProgramInv s)
    (i : Nat) (hi : i < RELICS) :
    s.custody.getD i 0 = homeCode i ∨
      s.custody.getD i 0 = CARRIED ∨ s.custody.getD i 0 = BANKED := by
  have hget := getElem?_eq_some_getD hInv.1.1.1 hi
  rcases hInv.2 i hi with h | h | h <;> rw [hget] at h
  · exact Or.inl (Option.some.inj h)
  · exact Or.inr (Or.inl (Option.some.inj h))
  · exact Or.inr (Or.inr (Option.some.inj h))

open Dregg2.Exec in
private theorem rangeTeeth_honest {s : DState} (hInv : Inv s) (o : Value) :
    ∀ c ∈ rangeTeeth, evalConstraint c.toExec o (encode s) = true := by
  intro c hc
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hc
  apply (evalSimple_inRangeTwoSided_iff z 0 RELICS o (encode s)).2
  have hlen := hInv.1.1
  simp only [zones, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨pack s, by simp, by exact_mod_cast Nat.zero_le _, ?_⟩
    simp only [pack]
    exact_mod_cast (List.countP_le_length (l := s.custody)).trans_eq hlen
  · refine ⟨bank s, by simp, by exact_mod_cast Nat.zero_le _, ?_⟩
    simp only [bank]
    exact_mod_cast (List.countP_le_length (l := s.custody)).trans_eq hlen
  · refine ⟨hoardAt s 1, by simp, by exact_mod_cast Nat.zero_le _, ?_⟩
    simp only [hoardAt]
    exact_mod_cast (List.countP_le_length (l := s.custody)).trans_eq hlen
  · refine ⟨hoardAt s 2, by simp, by exact_mod_cast Nat.zero_le _, ?_⟩
    simp only [hoardAt]
    exact_mod_cast (List.countP_le_length (l := s.custody)).trans_eq hlen
  · refine ⟨hoardAt s 3, by simp, by exact_mod_cast Nat.zero_le _, ?_⟩
    simp only [hoardAt]
    exact_mod_cast (List.countP_le_length (l := s.custody)).trans_eq hlen
  · refine ⟨hoardAt s 4, by simp, by exact_mod_cast Nat.zero_le _, ?_⟩
    simp only [hoardAt]
    exact_mod_cast (List.countP_le_length (l := s.custody)).trans_eq hlen

open Dregg2.Exec in
private theorem custodyTeeth_honest {s s' : DState} {m : Move}
    (hInv : ModelProgramInv s) (hstep : step s m = some s') :
    ∀ c ∈ custodyTeeth, evalConstraint c.toExec (encode s) (encode s') = true := by
  intro c hc
  obtain ⟨i, hiRange, hc⟩ := List.mem_flatMap.mp hc
  have hi : i < RELICS := List.mem_range.mp hiRange
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · simp only [Constraint.toExec, HeapAtom.toExec, HeapKeyRef.field, evalConstraint]
    unfold evalSimple
    rw [encode_scalar_relic s i hi, encode_scalar_relic s' i hi]
    change decide ((s.custody.getD i 0 : Int) ≤ (s'.custody.getD i 0 : Int)) = true
    exact decide_eq_true (by exact_mod_cast custody_getD_mono hInv hstep i hi)
  · apply (evalSimple_memberOf_iff (relicName i)
      [homeCode i, CARRIED, BANKED] (encode s) (encode s')).2
    refine ⟨(s'.custody.getD i 0 : Int), encode_scalar_relic s' i hi, ?_⟩
    rcases custody_getD_home (modelProgramInv_step hInv hstep) i hi with h | h | h
    · rw [h]
      simp
    · rw [h]
      simp
    · rw [h]
      simp

/-- A fixed eight-relic world can be exposed elementwise without assuming
anything about the elements.  This is only plumbing for reducing the deployed
fixed-key aggregate against `List.countP`; no game rule is hidden here. -/
private theorem list_length_eight {l : List Nat} (hlen : l.length = RELICS) :
    ∃ a b c d e f g h, l = [a, b, c, d, e, f, g, h] := by
  rcases l with _ | ⟨a, l⟩
  · simp at hlen
  rcases l with _ | ⟨b, l⟩
  · simp at hlen
  rcases l with _ | ⟨c, l⟩
  · simp at hlen
  rcases l with _ | ⟨d, l⟩
  · simp at hlen
  rcases l with _ | ⟨e, l⟩
  · simp at hlen
  rcases l with _ | ⟨f, l⟩
  · simp at hlen
  rcases l with _ | ⟨g, l⟩
  · simp at hlen
  rcases l with _ | ⟨h, tail⟩
  · simp at hlen
  cases tail with
  | nil => exact ⟨a, b, c, d, e, f, g, h, rfl⟩
  | cons x xs => simp [RELICS] at hlen

/-- The executor aggregate compares signed scalars, while the native game counts
`Nat` custody codes.  `Int.ofNat` is injective, so these are exactly the same
census -- no modular or truncating representation step is present. -/
private def countNatsAsIntsEq (l : List Nat) (needle : Nat) : Nat :=
  l.foldr (fun (x : Nat) n => if (x : Int) = (needle : Int) then n + 1 else n) 0

private theorem countNatsAsIntsEq_eq_countP (l : List Nat) (needle : Nat) :
    countNatsAsIntsEq l needle = l.countP (fun x => x == needle) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [countNatsAsIntsEq, List.foldr, List.countP_cons]
    change (if (a : Int) = (needle : Int)
      then countNatsAsIntsEq rest needle + 1
      else countNatsAsIntsEq rest needle) =
        rest.countP (fun x => x == needle) + if (a == needle) = true then 1 else 0
    rw [ih]
    by_cases h : a = needle
    · subst needle
      simp
    · have hcast : (a : Int) ≠ (needle : Int) := fun heq => h (Int.ofNat_inj.mp heq)
      simp [h, hcast]

open Dregg2.Exec in
private theorem countScalarsEq_relicKeys_encode (s : DState) (hInv : Inv s)
    (needle : Nat) :
    countScalarsEq (encode s) (relicKeys.map HeapKeyRef.field) (needle : Int) =
      some (s.custody.countP (fun x => x == needle)) := by
  obtain ⟨a, b, c, d, e, f, g, h, hcustody⟩ := list_length_eight hInv.1.1
  have hcount := congrArg some
    (countNatsAsIntsEq_eq_countP [a, b, c, d, e, f, g, h] needle)
  simpa [countScalarsEq, countNatsAsIntsEq, relicKeys, range_relics,
    HeapKeyRef.field, hcustody] using hcount

open Dregg2.Exec in
private theorem projectionTeeth_honest {s : DState} (hInv : Inv s) (o : Value) :
    ∀ c ∈ projectionTeeth, evalConstraint c.toExec o (encode s) = true := by
  intro c hc
  simp only [projectionTeeth, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · apply (evalConstraint_countFieldsEq_iff _ _ _ _ _).2
    exact ⟨pack s, countScalarsEq_relicKeys_encode s hInv CARRIED, encode_scalar_pack s⟩
  · apply (evalConstraint_countFieldsEq_iff _ _ _ _ _).2
    exact ⟨bank s, countScalarsEq_relicKeys_encode s hInv BANKED, encode_scalar_bank s⟩
  · apply (evalConstraint_countFieldsEq_iff _ _ _ _ _).2
    exact ⟨hoardAt s 1, countScalarsEq_relicKeys_encode s hInv 1,
      encode_scalar_hoard s 1 (by decide) (by decide)⟩
  · apply (evalConstraint_countFieldsEq_iff _ _ _ _ _).2
    exact ⟨hoardAt s 2, countScalarsEq_relicKeys_encode s hInv 2,
      encode_scalar_hoard s 2 (by decide) (by decide)⟩
  · apply (evalConstraint_countFieldsEq_iff _ _ _ _ _).2
    exact ⟨hoardAt s 3, countScalarsEq_relicKeys_encode s hInv 3,
      encode_scalar_hoard s 3 (by decide) (by decide)⟩
  · apply (evalConstraint_countFieldsEq_iff _ _ _ _ _).2
    exact ⟨hoardAt s 4, countScalarsEq_relicKeys_encode s hInv 4,
      encode_scalar_hoard s 4 (by decide) (by decide)⟩

open Dregg2.Exec in
private theorem spentRider_honest {s s' : DState} {m : Move}
    (hInv : ModelProgramInv s) (hstep : step s m = some s') :
    ∀ c ∈ spentRider.constraints,
      evalConstraint c.toExec (encode s) (encode s') = true := by
  intro c hc
  change c ∈ coreTeeth ++ rangeTeeth ++ custodyTeeth ++ projectionTeeth ++
    [.heapField .sentinel .immutable] at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with (((hc | hc) | hc) | hc) | rfl
  · exact coreTeeth_honest hInv hstep c hc
  · exact rangeTeeth_honest (modelProgramInv_step hInv hstep).1 (encode s) c hc
  · exact custodyTeeth_honest hInv hstep c hc
  · exact projectionTeeth_honest (modelProgramInv_step hInv hstep).1 (encode s) c hc
  · simp [Constraint.toExec, HeapAtom.toExec, HeapKeyRef.field, evalConstraint,
      evalSimple]

open Dregg2.Exec in
private theorem case_all_of_constraints
    {cs : List Constraint} {o n : Value}
    (h : ∀ c ∈ cs, evalConstraint c.toExec o n = true) :
    (cs.map Constraint.toExec).all (fun c => evalConstraint c o n) = true := by
  apply List.all_eq_true.mpr
  intro ec hec
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hec
  exact h c hc

-- Guard-projection pins keep dispatch proofs from unfolding each case's large
-- constraint payload merely to expose its tiny guard.
@[simp] private theorem genesisCase_guard :
    genesisCase.guard = .methodIs "genesis" := rfl
@[simp] private theorem delveCase_guard : delveCase.guard = .methodIs "delve" := rfl
@[simp] private theorem unlockCase_guard : unlockCase.guard = .methodIs "unlock" := rfl
@[simp] private theorem smiteCase_guard : smiteCase.guard = .methodIs "smite" := rfl
@[simp] private theorem lootCase_guard : lootCase.guard = .methodIs "loot" := rfl
@[simp] private theorem fleeCase_guard : fleeCase.guard = .methodIs "flee" := rfl
@[simp] private theorem lungeCase_guard : lungeCase.guard = .methodIs "lunge" := rfl
@[simp] private theorem harmRider_guard :
    harmRider.guard = .slotChangedForMethods "harm" verbs := rfl
@[simp] private theorem depthRider_guard :
    depthRider.guard = .slotChangedForMethods "depth" verbs := rfl
@[simp] private theorem wayRider_guard (w : Nat) :
    (wayRider w).guard = .slotChangedForMethods (wayName w) verbs := rfl
@[simp] private theorem fateRider_guard :
    fateRider.guard = .slotChangedForMethods "fate" verbs := rfl
@[simp] private theorem bankRider_guard :
    bankRider.guard = .slotChangedForMethods "bank" verbs := rfl
@[simp] private theorem spentRider_guard :
    spentRider.guard = .slotChangedForMethods "spent" verbs := rfl

open Dregg2.Exec in
private theorem cases_admit_of {tcs : List TransitionCase} {method : Nat}
    {o n : Value}
    (hsome : ∃ tc ∈ tcs, tc.guard.matches method o n = true)
    (hall : ∀ tc ∈ tcs, tc.guard.matches method o n = true →
      tc.constraints.all (fun c => evalConstraint c o n) = true) :
    RecordProgram.admits (.cases tcs) method o n = true := by
  simp only [RecordProgram.admits]
  cases hf : tcs.filter (fun tc => tc.guard.matches method o n) with
  | nil =>
    obtain ⟨tc, hmem, hmatch⟩ := hsome
    have hmemf : tc ∈ tcs.filter (fun tc => tc.guard.matches method o n) :=
      List.mem_filter.mpr ⟨hmem, hmatch⟩
    rw [hf] at hmemf
    exact absurd hmemf (by simp)
  | cons first rest =>
    apply List.all_eq_true.mpr
    intro tc htc
    have htcFilter : tc ∈ tcs.filter (fun tc => tc.guard.matches method o n) := by
      rw [hf]
      exact htc
    apply hall tc
    · exact (List.mem_filter.mp htcFilter).1
    · exact (List.mem_filter.mp htcFilter).2

private theorem wayOpen_getD_one {s : DState} {d : Nat} (hd : 2 ≤ d)
    (hopen : wayOpen s d = true) : s.ways.getD (d - 2) 0 = 1 := by
  have hdNot : ¬ d ≤ 1 := by omega
  rw [wayOpen, if_neg hdNot] at hopen
  cases hget : s.ways[d - 2]? with
  | none => simp [hget] at hopen
  | some v =>
    have hv : v = 1 := by simpa [hget] using hopen
    rw [List.getD_eq_getElem?_getD, hget]
    exact hv

private theorem getD_eq_of_getElem?_eq_some {l : List Nat} {i v : Nat}
    (h : l[i]? = some v) : l.getD i 0 = v := by
  rw [List.getD_eq_getElem?_getD, h]
  rfl

private theorem getD_set_self {l : List Nat} {i v : Nat} (hi : i < l.length) :
    (l.set i v).getD i 0 = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hi]
  rfl

private theorem countP_set_bump_local {l : List Nat} {i a v : Nat}
    (p : Nat → Bool) (hget : l[i]? = some a) (hpa : p a = false)
    (hpv : p v = true) : (l.set i v).countP p = l.countP p + 1 := by
  induction l generalizing i with
  | nil => simp at hget
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp [List.set, hpa, hpv]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hget
      simp only [List.set, List.countP_cons, ih hget]
      omega

private theorem countP_set_same_local {l : List Nat} {i a v : Nat}
    (p : Nat → Bool) (hget : l[i]? = some a) (heq : p a = p v) :
    (l.set i v).countP p = l.countP p := by
  induction l generalizing i with
  | nil => simp at hget
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp only [List.set, List.countP_cons, heq]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hget
      simp only [List.set, List.countP_cons, ih hget]

private theorem countP_flee_carried_local (l : List Nat) :
    (l.map (fun c => if c = CARRIED then BANKED else c)).countP
      (· == CARRIED) = 0 := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.map_cons, List.countP_cons, ih]
    by_cases h : hd = CARRIED
    · simp [h, show BANKED ≠ CARRIED by decide]
    · simp [h]

private theorem countP_flee_banked_local (l : List Nat) :
    (l.map (fun c => if c = CARRIED then BANKED else c)).countP
      (· == BANKED) =
      l.countP (· == CARRIED) + l.countP (· == BANKED) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.map_cons, List.countP_cons, List.countP_cons, List.countP_cons, ih]
    by_cases hC : hd = CARRIED
    · subst hd
      simp [show CARRIED ≠ BANKED by decide]
      omega
    · by_cases hB : hd = BANKED
      · subst hd
        simp [hC]
        omega
      · simp [hC, hB]

private theorem countP_flee_floor_local (l : List Nat) (d : Nat)
    (hdC : d ≠ CARRIED) (hdB : d ≠ BANKED) :
    (l.map (fun c => if c = CARRIED then BANKED else c)).countP (· == d) =
      l.countP (· == d) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.map_cons, List.countP_cons, List.countP_cons, ih]
    by_cases hC : hd = CARRIED
    · subst hd
      simp [Ne.symm hdC, Ne.symm hdB]
    · simp [hC]

open Dregg2.Exec in
private theorem delve_wayTooth_honest {s s' : DState}
    (hstep : step s .delve = some s') (d : Nat) (hdLo : 2 ≤ d)
    (hdHi : d ≤ FLOORS) :
    evalConstraint (wayTooth d).toExec (encode s) (encode s') = true := by
  simp only [step] at hstep
  split at hstep
  · rename_i hc
    cases hstep
    by_cases heq : s.depth + 1 = d
    · have hopen : wayOpen s d = true := by simpa [heq] using hc.2.2.2.1
      have hway := wayOpen_getD_one hdLo hopen
      simp only [wayTooth, Constraint.toExec, List.map_cons, List.map_nil,
        Simple.toExec, evalConstraint, List.any_cons, List.any_nil, Bool.or_false]
      simp only [Bool.or_eq_true]
      right
      unfold evalSimple
      rw [encode_scalar_way _ d hdLo hdHi, hway]
      rfl
    · simp only [wayTooth, Constraint.toExec, List.map_cons, List.map_nil,
        Simple.toExec, evalConstraint, List.any_cons, List.any_nil, Bool.or_false]
      simp only [Bool.or_eq_true]
      left
      simp only [evalSimple]
      rw [encode_scalar_depth]
      have hz : ((s.depth + 1 : Nat) : Int) ≠ (d : Int) := by
        exact_mod_cast heq
      simpa using hz
  · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem delveCase_honest {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .delve = some s') :
    (delveCase.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++
    [.fieldDelta "spent" 1, .fieldDelta "depth" 1,
      .fieldEquals "wounds" 0, .fieldEquals "fate" 0,
      wayTooth 2, wayTooth 3, wayTooth 4] ++
    frozen ["pack", "bank", wayName 2, wayName 3, wayName 4,
      hoardName 1, hoardName 2, hoardName 3, hoardName 4, "harm"] ++ relicFreeze at hc
  simp only [List.mem_append] at hc
  rcases hc with ((hcore | hverb) | hfrozen) | hrelic
  · exact coreTeeth_honest hInv hstep c hcore
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hverb
    rcases hverb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [Constraint.toExec, evalConstraint]
      unfold evalSimple
      rw [encode_scalar_spent, encode_scalar_spent]
      rw [legal_step_spent_eq hstep]
      simp [price]
    · simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, hlegal.1]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · have hf := (legal_step_fate hstep).1
      simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple, hf]
      · exact absurd hstep (by simp)
    · exact delve_wayTooth_honest hstep 2 (by decide) (by decide)
    · exact delve_wayTooth_honest hstep 3 (by decide) (by decide)
    · exact delve_wayTooth_honest hstep 4 (by decide) (by decide)
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hfrozen
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [step] at hstep
      split at hstep
      · cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, pack, bank, hoardAt]
      · exact absurd hstep (by simp)
  · obtain ⟨i, hiRange, rfl⟩ := List.mem_map.mp hrelic
    have hi : i < RELICS := List.mem_range.mp hiRange
    simp only [step] at hstep
    split at hstep
    · cases hstep
      simp only [Constraint.toExec, HeapAtom.toExec, HeapKeyRef.field, evalConstraint]
      unfold evalSimple
      rw [encode_scalar_relic s i hi, encode_scalar_relic _ i hi]
      change (some (s.custody.getD i 0 : Int) ==
        some (s.custody.getD i 0 : Int)) = true
      simp
    · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem depthRider_delve_honest {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .delve = some s') :
    (depthRider.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++ [.fieldDelta "depth" 1, .fieldEquals "wounds" 0,
    wayTooth 2, wayTooth 3, wayTooth 4] at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hcore | rfl | rfl | rfl | rfl | rfl
  · exact coreTeeth_honest hInv hstep c hcore
  · simp only [step] at hstep
    split at hstep
    · cases hstep
      simp [Constraint.toExec, evalConstraint, evalSimple]
    · exact absurd hstep (by simp)
  · simp only [step] at hstep
    split at hstep
    · cases hstep
      simp [Constraint.toExec, evalConstraint, evalSimple]
    · exact absurd hstep (by simp)
  · exact delve_wayTooth_honest hstep 2 (by decide) (by decide)
  · exact delve_wayTooth_honest hstep 3 (by decide) (by decide)
  · exact delve_wayTooth_honest hstep 4 (by decide) (by decide)

open Dregg2.Exec in
/-- First positive completeness rung: every honest model delve satisfies its verb
arm and every matching cross-method rider in the authored record program. -/
theorem modelProgram_delve_admitted {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .delve = some s') :
    RecordProgram.admits dungeonExec (moveIdx .delve)
      (encode s) (encode s') = true := by
  have hDelve := delveCase_honest hInv hstep
  have hDepth := depthRider_delve_honest hInv hstep
  have hSpent : (spentRider.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true :=
    case_all_of_constraints (spentRider_honest hInv hstep)
  simp only [step] at hstep
  split at hstep
  · have hs' : s' =
        { depth := s.depth + 1, spent := s.spent + 1, wounds := 0, harm := s.harm,
          fate := s.fate, ways := s.ways, custody := s.custody } :=
      (Option.some.inj hstep).symm
    have hfilter :
        (programCases.map Case.toExec).filter (fun tc =>
          tc.guard.matches (moveIdx .delve) (encode s)
            (encode s')) =
          [delveCase.toExec, depthRider.toExec, spentRider.toExec] := by
      simp [programCases, genesisCase, delveCase, unlockCase, smiteCase, lootCase,
        fleeCase, lungeCase, depthRider, wayRider, fateRider, bankRider, harmRider,
        spentRider,
        Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
        Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch, verbs, bank, moveIdx, hs']
    simp only [dungeonExec, dungeonProgram, CellProgram.toExec,
      RecordProgram.admits, hfilter, List.all_cons, List.all_nil,
      Bool.and_true, hDelve, hDepth, hSpent]
  · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem unlockCase_honest {s s' : DState} {w : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.unlock w) = some s') :
    (unlockCase.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++ [.fieldDelta "spent" 1, .fieldEquals "fate" 0] ++
    frozen ["depth", "wounds", "pack", "bank", hoardName 1, hoardName 2,
      hoardName 3, hoardName 4, "harm"] ++ relicFreeze at hc
  simp only [List.mem_append] at hc
  rcases hc with ((hcore | hverb) | hfrozen) | hrelic
  · exact coreTeeth_honest hInv hstep c hcore
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hverb
    rcases hverb with rfl | rfl
    · simp only [Constraint.toExec, evalConstraint]
      unfold evalSimple
      rw [encode_scalar_spent, encode_scalar_spent, legal_step_spent_eq hstep]
      simp [price]
    · simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, hlegal.1]
      · exact absurd hstep (by simp)
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hfrozen
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [step] at hstep
      split at hstep
      · cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, pack, bank, hoardAt]
      · exact absurd hstep (by simp)
  · obtain ⟨i, hiRange, rfl⟩ := List.mem_map.mp hrelic
    have hi : i < RELICS := List.mem_range.mp hiRange
    simp only [step] at hstep
    split at hstep
    · cases hstep
      simp only [Constraint.toExec, HeapAtom.toExec, HeapKeyRef.field,
        evalConstraint, evalSimple]
      rw [encode_scalar_relic s i hi, encode_scalar_relic _ i hi]
      simp
    · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem wayRider_unlock_honest {s s' : DState} {w : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.unlock w) = some s') :
    ((wayRider w).toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++
    [.allowedTransitions (wayName w) [(0, 1)],
      .heapField (.named (relicName (keyFor w))) (.equals CARRIED)] at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hcore | rfl | rfl
  · exact coreTeeth_honest hInv hstep c hcore
  · simp only [step] at hstep
    split at hstep
    · rename_i hlegal
      have hwLo : 2 ≤ w := hlegal.2.2.1
      have hwHi : w ≤ FLOORS := hlegal.2.2.2.1
      have hidx : w - 2 < s.ways.length := by
        have hlen := hInv.1.2.2.2.2.1
        omega
      have hold : s.ways.getD (w - 2) 0 = 0 :=
        getD_eq_of_getElem?_eq_some hlegal.2.2.2.2.1
      have hnew : (s.ways.set (w - 2) 1).getD (w - 2) 0 = 1 :=
        getD_set_self hidx
      cases hstep
      simp only [Constraint.toExec, evalConstraint]
      rw [encode_scalar_way s w hwLo hwHi,
        encode_scalar_way _ w hwLo hwHi, hold, hnew]
      simp
    · exact absurd hstep (by simp)
  · simp only [step] at hstep
    split at hstep
    · rename_i hlegal
      have hwLo : 2 ≤ w := hlegal.2.2.1
      have hwHi : w ≤ FLOORS := hlegal.2.2.2.1
      have hkeyLt : keyFor w < RELICS := by
        have hwHi' : w ≤ 4 := hwHi
        have hw : w = 2 ∨ w = 3 ∨ w = 4 := by omega
        rcases hw with rfl | rfl | rfl <;> decide
      have hkey : s.custody.getD (keyFor w) 0 = CARRIED :=
        getD_eq_of_getElem?_eq_some hlegal.2.2.2.2.2
      cases hstep
      simp only [Constraint.toExec, HeapAtom.toExec, HeapKeyRef.field,
        evalConstraint, evalSimple]
      rw [encode_scalar_relic _ (keyFor w) hkeyLt, hkey]
      simp
    · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- Every honest keyed unlock satisfies the unlock arm, exactly the rider selected
by its legal way parameter, and the universal spent rider. -/
theorem modelProgram_unlock_admitted {s s' : DState} {w : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.unlock w) = some s') :
    RecordProgram.admits dungeonExec (moveIdx (.unlock w))
      (encode s) (encode s') = true := by
  have hUnlock := unlockCase_honest hInv hstep
  have hWay := wayRider_unlock_honest hInv hstep
  have hSpent : (spentRider.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true :=
    case_all_of_constraints (spentRider_honest hInv hstep)
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    have hwLo : 2 ≤ w := hlegal.2.2.1
    have hwHi : w ≤ FLOORS := hlegal.2.2.2.1
    have hwHi' : w ≤ 4 := hwHi
    have hw : w = 2 ∨ w = 3 ∨ w = 4 := by omega
    rcases hw with rfl | rfl | rfl
    all_goals cases hstep
    all_goals
      simp only [dungeonExec, dungeonProgram, CellProgram.toExec]
      apply cases_admit_of
      · refine ⟨unlockCase.toExec, ?_, ?_⟩
        · simp [programCases]
        · simp [Case.toExec, Guard.toExec, methodIdx,
            TransitionGuard.matches, moveIdx]
      · intro tc htc hmatch
        simp only [programCases, List.map_cons, List.map_nil, List.mem_cons,
          List.not_mem_nil, or_false] at htc
        rcases htc with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exfalso
          simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
            moveIdx] at hmatch
        · exfalso
          simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
            moveIdx] at hmatch
        · exact hUnlock
        · exfalso
          simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
            moveIdx] at hmatch
        · exfalso
          simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
            moveIdx] at hmatch
        · exfalso
          simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
            moveIdx] at hmatch
        · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
            TransitionGuard.matches, moveIdx] at hmatch
        · exfalso
          simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
            Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch, verbs, moveIdx] at hmatch
        · first
          | exact hWay
          | exfalso
            simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
              Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch, verbs, moveIdx,
              hlegal] at hmatch
        · first
          | exact hWay
          | exfalso
            simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
              Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch, verbs, moveIdx,
              hlegal] at hmatch
        · first
          | exact hWay
          | exfalso
            simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
              Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch, verbs, moveIdx,
              hlegal] at hmatch
        · exfalso
          simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
            Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch, verbs, moveIdx,
            hlegal] at hmatch
        · exfalso
          simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches,
            Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch, verbs, bank, moveIdx,
            hlegal] at hmatch
        · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
            TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
            verbs, moveIdx] at hmatch
        · exact hSpent
  · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem smite_guardCap_honest {s s' : DState}
    (hstep : step s .smite = some s') (d : Nat) :
    evalConstraint (guardCapTooth d).toExec (encode s) (encode s') = true := by
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    cases hstep
    by_cases heq : s.depth = d
    · simp only [guardCapTooth, Constraint.toExec, List.map_cons, List.map_nil,
        Simple.toExec, evalConstraint, List.any_cons, List.any_nil, Bool.or_false,
        Bool.or_eq_true]
      right
      unfold evalSimple
      rw [encode_scalar_wounds]
      change decide (((s.wounds + 1 : Nat) : Int) ≤ (guardHp d : Int)) = true
      apply decide_eq_true
      exact_mod_cast (heq ▸ hlegal.2.2.2)
    · simp only [guardCapTooth, Constraint.toExec, List.map_cons, List.map_nil,
        Simple.toExec, evalConstraint, List.any_cons, List.any_nil, Bool.or_false,
        Bool.or_eq_true]
      left
      simp only [evalSimple]
      rw [encode_scalar_depth]
      have hz : (s.depth : Int) ≠ (d : Int) := by exact_mod_cast heq
      simpa using hz
  · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem smiteCase_honest {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .smite = some s') :
    (smiteCase.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++
    [.fieldDelta "spent" 2, .fieldDelta "wounds" 1,
      .fieldGte "depth" 1, .fieldEquals "fate" 0,
      guardCapTooth 1, guardCapTooth 2, guardCapTooth 3, guardCapTooth 4] ++
    frozen ["depth", "pack", "bank", wayName 2, wayName 3, wayName 4,
      hoardName 1, hoardName 2, hoardName 3, hoardName 4, "harm"] ++ relicFreeze at hc
  simp only [List.mem_append] at hc
  rcases hc with ((hcore | hverb) | hfrozen) | hrelic
  · exact coreTeeth_honest hInv hstep c hcore
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hverb
    rcases hverb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [Constraint.toExec, evalConstraint]
      unfold evalSimple
      rw [encode_scalar_spent, encode_scalar_spent, legal_step_spent_eq hstep]
      simp [price]
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        cases hstep
        simp only [Constraint.toExec, evalConstraint]
        unfold evalSimple
        rw [encode_scalar_depth]
        change decide ((1 : Int) ≤ (s.depth : Int)) = true
        exact decide_eq_true (by exact_mod_cast hlegal.2.2.1)
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, hlegal.1]
      · exact absurd hstep (by simp)
    · exact smite_guardCap_honest hstep 1
    · exact smite_guardCap_honest hstep 2
    · exact smite_guardCap_honest hstep 3
    · exact smite_guardCap_honest hstep 4
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hfrozen
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [step] at hstep
      split at hstep
      · cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, pack, bank, hoardAt]
      · exact absurd hstep (by simp)
  · obtain ⟨i, hiRange, rfl⟩ := List.mem_map.mp hrelic
    have hi : i < RELICS := List.mem_range.mp hiRange
    simp only [step] at hstep
    split at hstep
    · cases hstep
      simp only [Constraint.toExec, HeapAtom.toExec, HeapKeyRef.field,
        evalConstraint, evalSimple]
      rw [encode_scalar_relic s i hi, encode_scalar_relic _ i hi]
      simp
    · exact absurd hstep (by simp)

open Dregg2.Exec in
theorem modelProgram_smite_admitted {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .smite = some s') :
    RecordProgram.admits dungeonExec (moveIdx .smite)
      (encode s) (encode s') = true := by
  have hSmite := smiteCase_honest hInv hstep
  have hSpent : (spentRider.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true :=
    case_all_of_constraints (spentRider_honest hInv hstep)
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    cases hstep
    simp only [dungeonExec, dungeonProgram, CellProgram.toExec]
    apply cases_admit_of
    · refine ⟨smiteCase.toExec, by simp [programCases], ?_⟩
      simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches, moveIdx]
    · intro tc htc hmatch
      simp only [programCases, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at htc
      rcases htc with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exact hSmite
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx, hlegal.1] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, bank, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exact hSpent
  · exact absurd hstep (by simp)

/-! ### The LUNGE — the second blow, and the only verb that may move `harm`.

`lunge` is `smite`'s twin everywhere except the two registers that are the whole design:
it pays `1` breath instead of `2`, and it writes `harm += 1`. So its completeness rung
is the smite rung plus (a) the `harm` delta and range teeth on its own arm and (b) the
`harmRider`, which fires on ANY method that moves the slot and therefore has to be
discharged here rather than assumed. -/

open Dregg2.Exec in
private theorem lunge_guardCap_honest {s s' : DState}
    (hstep : step s .lunge = some s') (d : Nat) :
    evalConstraint (guardCapTooth d).toExec (encode s) (encode s') = true := by
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    cases hstep
    by_cases heq : s.depth = d
    · simp only [guardCapTooth, Constraint.toExec, List.map_cons, List.map_nil,
        Simple.toExec, evalConstraint, List.any_cons, List.any_nil, Bool.or_false,
        Bool.or_eq_true]
      right
      unfold evalSimple
      rw [encode_scalar_wounds]
      change decide (((s.wounds + 1 : Nat) : Int) ≤ (guardHp d : Int)) = true
      apply decide_eq_true
      exact_mod_cast (heq ▸ hlegal.2.2.2.1)
    · simp only [guardCapTooth, Constraint.toExec, List.map_cons, List.map_nil,
        Simple.toExec, evalConstraint, List.any_cons, List.any_nil, Bool.or_false,
        Bool.or_eq_true]
      left
      simp only [evalSimple]
      rw [encode_scalar_depth]
      have hz : (s.depth : Int) ≠ (d : Int) := by exact_mod_cast heq
      simpa using hz
  · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- The two teeth that ARE the lunge: an exact `+1` on `harm`, inside the ratchet's
`[0, HARMCAP]` range. Both are discharged from the model gate `s.harm + 1 ≤ HARMCAP`. -/
private theorem lunge_harm_eq {s s' : DState} (hstep : step s .lunge = some s') :
    s'.harm = s.harm + 1 ∧ s.harm + 1 ≤ HARMCAP := by
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    cases hstep
    exact ⟨rfl, hlegal.2.2.2.2.1⟩
  · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem lunge_harm_honest {s s' : DState}
    (hstep : step s .lunge = some s') :
    evalConstraint (Constraint.fieldDelta "harm" 1).toExec (encode s) (encode s') = true
      ∧ evalConstraint (Constraint.inRangeTwoSided "harm" 0 HARMCAP).toExec
          (encode s) (encode s') = true := by
  obtain ⟨hdelta, hcapH⟩ := lunge_harm_eq hstep
  refine ⟨?_, ?_⟩
  · simp only [Constraint.toExec, evalConstraint]
    unfold evalSimple
    rw [encode_scalar_harm, encode_scalar_harm, hdelta]
    simp
  · apply (evalSimple_inRangeTwoSided_iff "harm" (0 : Int) ((HARMCAP : Nat) : Int)
      (encode s) (encode s')).2
    refine ⟨(s'.harm : Int), encode_scalar_harm s', by exact_mod_cast Nat.zero_le _, ?_⟩
    rw [hdelta]
    exact_mod_cast hcapH

open Dregg2.Exec in
private theorem lungeCase_honest {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .lunge = some s') :
    (lungeCase.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++
    [.fieldDelta "spent" 1, .fieldDelta "wounds" 1, .fieldDelta "harm" 1,
      .inRangeTwoSided "harm" 0 HARMCAP,
      .fieldGte "depth" 1, .fieldEquals "fate" 0,
      guardCapTooth 1, guardCapTooth 2, guardCapTooth 3, guardCapTooth 4] ++
    frozen ["depth", "pack", "bank", wayName 2, wayName 3, wayName 4,
      hoardName 1, hoardName 2, hoardName 3, hoardName 4] ++ relicFreeze at hc
  simp only [List.mem_append] at hc
  rcases hc with ((hcore | hverb) | hfrozen) | hrelic
  · exact coreTeeth_honest hInv hstep c hcore
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hverb
    rcases hverb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [Constraint.toExec, evalConstraint]
      unfold evalSimple
      rw [encode_scalar_spent, encode_scalar_spent, legal_step_spent_eq hstep]
      simp [price]
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · exact (lunge_harm_honest hstep).1
    · exact (lunge_harm_honest hstep).2
    · simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        cases hstep
        simp only [Constraint.toExec, evalConstraint]
        unfold evalSimple
        rw [encode_scalar_depth]
        change decide ((1 : Int) ≤ (s.depth : Int)) = true
        exact decide_eq_true (by exact_mod_cast hlegal.2.2.1)
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, hlegal.1]
      · exact absurd hstep (by simp)
    · exact lunge_guardCap_honest hstep 1
    · exact lunge_guardCap_honest hstep 2
    · exact lunge_guardCap_honest hstep 3
    · exact lunge_guardCap_honest hstep 4
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hfrozen
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [step] at hstep
      split at hstep
      · cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, pack, bank, hoardAt]
      · exact absurd hstep (by simp)
  · obtain ⟨i, hiRange, rfl⟩ := List.mem_map.mp hrelic
    have hi : i < RELICS := List.mem_range.mp hiRange
    simp only [step] at hstep
    split at hstep
    · cases hstep
      simp only [Constraint.toExec, HeapAtom.toExec, HeapKeyRef.field,
        evalConstraint, evalSimple]
      rw [encode_scalar_relic s i hi, encode_scalar_relic _ i hi]
      simp
    · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- ⚑ THE ANTI-STAPLE RIDER, DISCHARGED. `harmRider` fires on any method that moves the
`harm` slot; the honest lunge satisfies its whole law, so the rider costs the legal verb
nothing while making the slot unstapleable onto every other one. -/
private theorem harmRider_lunge_honest {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .lunge = some s') :
    (harmRider.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++
    [.fieldDelta "harm" 1, .inRangeTwoSided "harm" 0 HARMCAP,
      .fieldDelta "wounds" 1, .fieldGte "depth" 1, .fieldEquals "fate" 0] at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hcore | rfl | rfl | rfl | rfl | rfl
  · exact coreTeeth_honest hInv hstep c hcore
  · exact (lunge_harm_honest hstep).1
  · exact (lunge_harm_honest hstep).2
  · simp only [step] at hstep
    split at hstep
    · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
    · exact absurd hstep (by simp)
  · simp only [step] at hstep
    split at hstep
    · rename_i hlegal
      cases hstep
      simp only [Constraint.toExec, evalConstraint]
      unfold evalSimple
      rw [encode_scalar_depth]
      change decide ((1 : Int) ≤ (s.depth : Int)) = true
      exact decide_eq_true (by exact_mod_cast hlegal.2.2.1)
    · exact absurd hstep (by simp)
  · simp only [step] at hstep
    split at hstep
    · rename_i hlegal
      cases hstep
      simp [Constraint.toExec, evalConstraint, evalSimple, hlegal.1]
    · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- **Every honest lunge is admitted** — its own arm, the `harmRider` its write summons,
and the universal spent rider. -/
theorem modelProgram_lunge_admitted {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .lunge = some s') :
    RecordProgram.admits dungeonExec (moveIdx .lunge)
      (encode s) (encode s') = true := by
  have hLunge := lungeCase_honest hInv hstep
  have hHarm := harmRider_lunge_honest hInv hstep
  have hSpent : (spentRider.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true :=
    case_all_of_constraints (spentRider_honest hInv hstep)
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    cases hstep
    simp only [dungeonExec, dungeonProgram, CellProgram.toExec]
    apply cases_admit_of
    · refine ⟨lungeCase.toExec, by simp [programCases], ?_⟩
      simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches, moveIdx]
    · intro tc htc hmatch
      simp only [programCases, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at htc
      rcases htc with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exact hLunge
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx, hlegal.1] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, bank, moveIdx] at hmatch
      · exact hHarm
      · exact hSpent
  · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem loot_guardSlain_honest {s s' : DState} {r : Nat}
    (hstep : step s (.loot r) = some s') (d : Nat) :
    evalConstraint (guardSlainTooth d).toExec (encode s) (encode s') = true := by
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    cases hstep
    by_cases heq : s.depth = d
    · simp only [guardSlainTooth, Constraint.toExec, List.map_cons,
        List.map_nil, Simple.toExec, evalConstraint, List.any_cons, List.any_nil,
        Bool.or_false, Bool.or_eq_true]
      right
      unfold evalSimple
      rw [encode_scalar_wounds]
      change decide ((guardHp d : Int) ≤ (s.wounds : Int)) = true
      apply decide_eq_true
      exact_mod_cast (heq ▸ hlegal.2.2.2.2.1).ge
    · simp only [guardSlainTooth, Constraint.toExec, List.map_cons,
        List.map_nil, Simple.toExec, evalConstraint, List.any_cons, List.any_nil,
        Bool.or_false, Bool.or_eq_true]
      left
      simp only [evalSimple]
      rw [encode_scalar_depth]
      have hz : (s.depth : Int) ≠ (d : Int) := by exact_mod_cast heq
      simpa using hz
  · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem loot_hoardFrame_honest {s s' : DState} {r d : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.loot r) = some s')
    (hdLo : 1 ≤ d) (hdHi : d ≤ FLOORS) :
    evalConstraint (hoardFrameTooth d).toExec (encode s) (encode s') = true := by
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    by_cases heq : s.depth = d
    · cases hstep
      simp only [hoardFrameTooth, Constraint.toExec, List.map_cons,
        List.map_nil, Simple.toExec, evalConstraint, List.any_cons, List.any_nil,
        Bool.or_false, Bool.or_eq_true]
      left
      unfold evalSimple
      rw [encode_scalar_depth]
      have hz : (s.depth : Int) = (d : Int) := by exact_mod_cast heq
      simpa using hz
    · have hdepthLt : s.depth ≤ FLOORS := hInv.1.2.2.1
      have holdFalse : (s.depth == d) = false := beq_eq_false_iff_ne.mpr heq
      have hcarriedFalse : (CARRIED == d) = false := by
        apply beq_eq_false_iff_ne.mpr
        have hFloorCarried : FLOORS < CARRIED := by decide
        omega
      have hsame : (s.custody.set r CARRIED).countP (· == d) =
          s.custody.countP (· == d) :=
        countP_set_same_local _ hlegal.2.2.2.1 (by rw [holdFalse, hcarriedFalse])
      cases hstep
      simp only [hoardFrameTooth, Constraint.toExec, List.map_cons,
        List.map_nil, Simple.toExec, evalConstraint, List.any_cons, List.any_nil,
        Bool.or_false, Bool.or_eq_true]
      right
      unfold evalSimple
      rw [encode_scalar_hoard s d hdLo hdHi,
        encode_scalar_hoard _ d hdLo hdHi]
      simpa [hoardAt] using hsame
  · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem lootCase_honest {s s' : DState} {r : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.loot r) = some s') :
    (lootCase.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++
    [.fieldDelta "spent" 1, .fieldDelta "pack" 1,
      .fieldGte "depth" 1, .fieldEquals "fate" 0,
      guardSlainTooth 1, guardSlainTooth 2, guardSlainTooth 3, guardSlainTooth 4,
      hoardFrameTooth 1, hoardFrameTooth 2, hoardFrameTooth 3,
      hoardFrameTooth 4] ++
    frozen ["depth", "wounds", "bank", wayName 2, wayName 3, wayName 4, "harm"] at hc
  simp only [List.mem_append] at hc
  rcases hc with (hcore | hverb) | hfrozen
  · exact coreTeeth_honest hInv hstep c hcore
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hverb
    rcases hverb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · simp only [Constraint.toExec, evalConstraint]
      unfold evalSimple
      rw [encode_scalar_spent, encode_scalar_spent, legal_step_spent_eq hstep]
      simp [price]
    · simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        have hdepthLt : s.depth ≤ FLOORS := hInv.1.2.2.1
        have hdepthCarried : (s.depth == CARRIED) = false := by
          apply beq_eq_false_iff_ne.mpr
          have hFloorCarried : FLOORS < CARRIED := by decide
          omega
        have hpack : pack (DState.mk s.depth (s.spent + 1) s.wounds s.harm s.fate
              s.ways (s.custody.set r CARRIED)) = pack s + 1 := by
          simp only [pack]
          exact countP_set_bump_local _ hlegal.2.2.2.1 hdepthCarried (by simp)
        cases hstep
        simp only [Constraint.toExec, evalConstraint]
        unfold evalSimple
        rw [encode_scalar_pack, encode_scalar_pack, hpack]
        simp
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        cases hstep
        simp only [Constraint.toExec, evalConstraint]
        unfold evalSimple
        rw [encode_scalar_depth]
        change decide ((1 : Int) ≤ (s.depth : Int)) = true
        exact decide_eq_true (by exact_mod_cast hlegal.2.2.1)
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, hlegal.1]
      · exact absurd hstep (by simp)
    · exact loot_guardSlain_honest hstep 1
    · exact loot_guardSlain_honest hstep 2
    · exact loot_guardSlain_honest hstep 3
    · exact loot_guardSlain_honest hstep 4
    · exact loot_hoardFrame_honest hInv hstep (by decide) (by decide)
    · exact loot_hoardFrame_honest hInv hstep (by decide) (by decide)
    · exact loot_hoardFrame_honest hInv hstep (by decide) (by decide)
    · exact loot_hoardFrame_honest hInv hstep (by decide) (by decide)
  · obtain ⟨reg, hreg, rfl⟩ := List.mem_map.mp hfrozen
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · rename_i hlegal
        have hdepthLt : s.depth ≤ FLOORS := hInv.1.2.2.1
        have hdepthBanked : (s.depth == BANKED) = false := by
          apply beq_eq_false_iff_ne.mpr
          have hFloorBanked : FLOORS < BANKED := by decide
          omega
        have hcarriedBanked : (CARRIED == BANKED) = false := by decide
        have hbank : bank (DState.mk s.depth (s.spent + 1) s.wounds s.harm s.fate
              s.ways (s.custody.set r CARRIED)) = bank s := by
          simp only [bank]
          exact countP_set_same_local _ hlegal.2.2.2.1
            (by rw [hdepthBanked, hcarriedBanked])
        cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, hbank]
      · exact absurd hstep (by simp)
    all_goals
      simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)

open Dregg2.Exec in
theorem modelProgram_loot_admitted {s s' : DState} {r : Nat}
    (hInv : ModelProgramInv s) (hstep : step s (.loot r) = some s') :
    RecordProgram.admits dungeonExec (moveIdx (.loot r))
      (encode s) (encode s') = true := by
  have hLoot := lootCase_honest hInv hstep
  have hSpent : (spentRider.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true :=
    case_all_of_constraints (spentRider_honest hInv hstep)
  simp only [step] at hstep
  split at hstep
  · rename_i hlegal
    have hdepthLt : s.depth ≤ FLOORS := hInv.1.2.2.1
    have hdepthBanked : (s.depth == BANKED) = false := by
      apply beq_eq_false_iff_ne.mpr
      have hFloorBanked : FLOORS < BANKED := by decide
      omega
    have hcarriedBanked : (CARRIED == BANKED) = false := by decide
    have hbankSame : (s.custody.set r CARRIED).countP (· == BANKED) =
        s.custody.countP (· == BANKED) :=
      countP_set_same_local _ hlegal.2.2.2.1
        (by rw [hdepthBanked, hcarriedBanked])
    cases hstep
    simp only [dungeonExec, dungeonProgram, CellProgram.toExec]
    apply cases_admit_of
    · refine ⟨lootCase.toExec, by simp [programCases], ?_⟩
      simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches, moveIdx]
    · intro tc htc hmatch
      simp only [programCases, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at htc
      rcases htc with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exact hLoot
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx, hlegal.1] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, bank, moveIdx, hbankSame] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exact hSpent
  · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem flee_hoard_immutable_honest {s s' : DState}
    (hstep : step s .flee = some s') (d : Nat)
    (hdLo : 1 ≤ d) (hdHi : d ≤ FLOORS) :
    evalConstraint (Constraint.immutable (hoardName d)).toExec
      (encode s) (encode s') = true := by
  simp only [step] at hstep
  split at hstep
  · have hdC : d ≠ CARRIED := by
      have hFC : FLOORS < CARRIED := by decide
      omega
    have hdB : d ≠ BANKED := by
      have hFB : FLOORS < BANKED := by decide
      omega
    have hsame := countP_flee_floor_local s.custody d hdC hdB
    cases hstep
    simp only [Constraint.toExec, evalConstraint]
    unfold evalSimple
    rw [encode_scalar_hoard s d hdLo hdHi,
      encode_scalar_hoard _ d hdLo hdHi]
    rw [show hoardAt
        { depth := s.depth, spent := s.spent + 1, wounds := s.wounds, harm := s.harm,
          fate := 1, ways := s.ways,
          custody := s.custody.map
            (fun c => if c = CARRIED then BANKED else c) } d = hoardAt s d by
      simpa [hoardAt, Function.comp_def] using hsame]
    simp
  · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem fleeCase_honest {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .flee = some s') :
    (fleeCase.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++
    [.fieldDelta "spent" 1, .fieldEquals "fate" 1, .fieldEquals "pack" 0] ++
    frozen ["depth", "wounds", wayName 2, wayName 3, wayName 4,
      hoardName 1, hoardName 2, hoardName 3, hoardName 4, "harm"] at hc
  simp only [List.mem_append] at hc
  rcases hc with (hcore | hverb) | hfrozen
  · exact coreTeeth_honest hInv hstep c hcore
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hverb
    rcases hverb with rfl | rfl | rfl
    · simp only [Constraint.toExec, evalConstraint]
      unfold evalSimple
      rw [encode_scalar_spent, encode_scalar_spent, legal_step_spent_eq hstep]
      simp [price]
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · have hpack : pack
            { depth := s.depth, spent := s.spent + 1, wounds := s.wounds, harm := s.harm,
              fate := 1, ways := s.ways,
              custody := s.custody.map
                (fun c => if c = CARRIED then BANKED else c) } = 0 := by
          simpa [pack] using countP_flee_carried_local s.custody
        cases hstep
        simp [Constraint.toExec, evalConstraint, evalSimple, hpack]
      · exact absurd hstep (by simp)
  · obtain ⟨reg, hreg, rfl⟩ := List.mem_map.mp hfrozen
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)
    · exact flee_hoard_immutable_honest hstep 1 (by decide) (by decide)
    · exact flee_hoard_immutable_honest hstep 2 (by decide) (by decide)
    · exact flee_hoard_immutable_honest hstep 3 (by decide) (by decide)
    · exact flee_hoard_immutable_honest hstep 4 (by decide) (by decide)
    · simp only [step] at hstep
      split at hstep
      · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
      · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem fateRider_flee_honest {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .flee = some s') :
    (fateRider.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++
    [.allowedTransitions "fate" [(0, 1)], .fieldEquals "pack" 0] at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hcore | rfl | rfl
  · exact coreTeeth_honest hInv hstep c hcore
  · simp only [step] at hstep
    split at hstep
    · rename_i hlegal
      cases hstep
      simp [Constraint.toExec, evalConstraint, hlegal.1]
    · exact absurd hstep (by simp)
  · simp only [step] at hstep
    split at hstep
    · have hpack : pack
          { depth := s.depth, spent := s.spent + 1, wounds := s.wounds, harm := s.harm,
            fate := 1, ways := s.ways,
            custody := s.custody.map
              (fun c => if c = CARRIED then BANKED else c) } = 0 := by
        simpa [pack] using countP_flee_carried_local s.custody
      cases hstep
      simp [Constraint.toExec, evalConstraint, evalSimple, hpack]
    · exact absurd hstep (by simp)

open Dregg2.Exec in
private theorem bankRider_flee_honest {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .flee = some s') :
    (bankRider.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true := by
  apply case_all_of_constraints
  intro c hc
  change c ∈ coreTeeth ++ [.fieldEquals "fate" 1, .fieldEquals "pack" 0] at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hcore | rfl | rfl
  · exact coreTeeth_honest hInv hstep c hcore
  · simp only [step] at hstep
    split at hstep
    · cases hstep; simp [Constraint.toExec, evalConstraint, evalSimple]
    · exact absurd hstep (by simp)
  · simp only [step] at hstep
    split at hstep
    · have hpack : pack
          { depth := s.depth, spent := s.spent + 1, wounds := s.wounds, harm := s.harm,
            fate := 1, ways := s.ways,
            custody := s.custody.map
              (fun c => if c = CARRIED then BANKED else c) } = 0 := by
        simpa [pack] using countP_flee_carried_local s.custody
      cases hstep
      simp [Constraint.toExec, evalConstraint, evalSimple, hpack]
    · exact absurd hstep (by simp)

open Dregg2.Exec in
theorem modelProgram_flee_admitted {s s' : DState}
    (hInv : ModelProgramInv s) (hstep : step s .flee = some s') :
    RecordProgram.admits dungeonExec (moveIdx .flee)
      (encode s) (encode s') = true := by
  have hFlee := fleeCase_honest hInv hstep
  have hFate := fateRider_flee_honest hInv hstep
  have hBank := bankRider_flee_honest hInv hstep
  have hSpent : (spentRider.toExec).constraints.all
      (fun c => evalConstraint c (encode s) (encode s')) = true :=
    case_all_of_constraints (spentRider_honest hInv hstep)
  simp only [step] at hstep
  split at hstep
  · cases hstep
    simp only [dungeonExec, dungeonProgram, CellProgram.toExec]
    apply cases_admit_of
    · refine ⟨fleeCase.toExec, by simp [programCases], ?_⟩
      simp [Case.toExec, Guard.toExec, methodIdx, TransitionGuard.matches, moveIdx]
    · intro tc htc hmatch
      simp only [programCases, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at htc
      rcases htc with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exact hFlee
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exact hFate
      · exact hBank
      · exfalso; simp [Case.toExec, Guard.toExec, methodIdx,
          TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
          verbs, moveIdx] at hmatch
      · exact hSpent
  · exact absurd hstep (by simp)

open Dregg2.Exec in
/-- Repaired model-to-program completeness: the native rulebook's every legal
verb step is admitted by the full authored record program once the model state
carries the minted-home provenance relation preserved by actual play. -/
theorem modelProgram_step_admitted {s s' : DState} {m : Move}
    (hInv : ModelProgramInv s) (hstep : step s m = some s') :
    RecordProgram.admits dungeonExec (moveIdx m) (encode s) (encode s') = true := by
  cases m with
  | delve => exact modelProgram_delve_admitted hInv hstep
  | unlock w => exact modelProgram_unlock_admitted hInv hstep
  | smite => exact modelProgram_smite_admitted hInv hstep
  | lunge => exact modelProgram_lunge_admitted hInv hstep
  | loot r => exact modelProgram_loot_admitted hInv hstep
  | flee => exact modelProgram_flee_admitted hInv hstep

private theorem foldl_none_modelProgram (ms : List Move) :
    ms.foldl (fun acc m => acc.bind (fun t => step t m)) none = none := by
  induction ms with
  | nil => rfl
  | cons m rest ih => exact ih

/-- Every state produced by a legal replay carries the stronger per-relic
provenance invariant needed by the authored program.  Thus the counterexample
above is an abstraction mismatch in `Inv`, not a reachable game state. -/
theorem modelProgramInv_replay {ms : List Move} {s : DState}
    (h : replay ms = some s) : ModelProgramInv s := by
  suffices H : ∀ (xs : List Move) (s0 s1 : DState), ModelProgramInv s0 →
      xs.foldl (fun acc m => acc.bind (fun t => step t m)) (some s0) = some s1 →
      ModelProgramInv s1 by
    exact H ms genesisState s modelProgramInv_genesis h
  intro xs
  induction xs with
  | nil =>
    intro s0 s1 h0 hrun
    simp at hrun
    simpa [hrun] using h0
  | cons m rest ih =>
    intro s0 s1 h0 hrun
    simp only [List.foldl_cons, Option.bind_some] at hrun
    cases hstep : step s0 m with
    | none =>
      rw [hstep, foldl_none_modelProgram] at hrun
      simp at hrun
    | some smid =>
      rw [hstep] at hrun
      exact ih smid s1 (modelProgramInv_step h0 hstep) hrun

theorem modelProgramInv_reachable {s : DState} (h : Reachable s) :
    ModelProgramInv s := by
  obtain ⟨ms, hms⟩ := h
  exact modelProgramInv_replay hms

/-- Every legal continuation from a replay-reachable game state is accepted by
the authored `Exec.RecordProgram`; no extra invariant premise is exposed to a
caller who already has the receipt-chain reachability witness. -/
theorem reachable_step_admitted {s s' : DState} {m : Move}
    (hReach : Reachable s) (hstep : step s m = some s') :
    Dregg2.Exec.RecordProgram.admits dungeonExec (moveIdx m)
      (encode s) (encode s') = true :=
  modelProgram_step_admitted (modelProgramInv_reachable hReach) hstep

/-- Formal obstruction to the formerly desired `Inv -> legal -> admitted` theorem:
there is an `Inv` state and a legal model transition which the authored program
correctly refuses because the state violates per-relic minted-home provenance. -/
theorem inv_not_sufficient_for_step_admission :
    ∃ s s' : DState,
      Inv s ∧ @step (instAt 0) s .delve = some s' ∧
        Dregg2.Exec.RecordProgram.admits (@dungeonExec (instAt 0)) (moveIdx .delve)
          (encode s) (encode s') = false := by
  refine ⟨wrongHomeState,
    { wrongHomeState with depth := 1, wounds := 0, spent := 1 },
    wrongHomeState_inv, wrongHomeState_delve_legal, wrongHomeState_delve_refused⟩

#assert_axioms way_flip_exhibits_key
#assert_axioms way_flip_key_mutation_refused
#assert_axioms modelProgramInv_genesis
#assert_axioms modelProgramInv_step
#assert_axioms modelProgram_delve_admitted
#assert_axioms modelProgram_unlock_admitted
#assert_axioms modelProgram_smite_admitted
#assert_axioms modelProgram_lunge_admitted
#assert_axioms modelProgram_loot_admitted
#assert_axioms modelProgram_flee_admitted
#assert_axioms modelProgram_step_admitted
#assert_axioms modelProgramInv_replay
#assert_axioms modelProgramInv_reachable
#assert_axioms reachable_step_admitted
#assert_axioms wrongHomeState_inv
#assert_axioms wrongHomeState_delve_legal
#assert_axioms wrongHomeState_delve_refused
#assert_axioms inv_not_sufficient_for_step_admission

end Dregg2.Games.Dungeon.Prog
