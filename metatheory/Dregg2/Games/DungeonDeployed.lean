/-
# Dregg2.Games.DungeonDeployed — the descent teeth RE-BASED onto the DEPLOYED evaluator.

`DungeonProgram.lean` proves the admission-soundness inversions over the signed-`Int`
`Exec.RecordProgram` model, and its header (written at `dc95b4d5ff`) records the descent as
TWO steps short of the tug's `program_admits_legal_play_deployed`: (1) vocabulary — the
descent's `affineLe`/`allowedTransitions`/`inRangeTwoSided`/`fieldDelta` were then outside
`Dregg2.Exec.DeployedConstraint`'s exported pure subset — and (2) signedness — the
inversions quantify over arbitrary signed `Exec.Value`s where the two evaluators genuinely
diverge. This module closes what is now closable, by PROOF:

* **The vocabulary gap is GONE.** The `CIRCUIT-LEAN-BOUNDARY` widening put `affineLe`,
  `allowedTransitions`, `inRangeTwoSided`, `fieldDelta`, `memberOf`, the flat `AnyOf`
  parity branches, and every heap atom the descent uses into the `@[export
  dregg_constraint_admits]` evaluator's decided subset. Of the descent's whole tooth
  vocabulary, exactly ONE constructor remains outside: `countFieldsEq` (the six
  object↔projection census teeth on the spent rider) — the Rust
  `StateConstraint::FieldsCountEquals`, enumerated in
  `exec-lean/src/constraint_oracle.rs` under "heap SHAPES not yet on the wire".

* **The Int→Nat bridge is a THEOREM** (`tooth_transport` + `descent_step_teeth_deployed`),
  not an assumption: the game's states are `Nat`-valued and reachable states are SMALL
  (every register ≤ 26, every custody code ≤ 9 — `regs_small`/`heap_small`, from `Inv`
  plus the new `Tight` reachability bound), so on the marshalled image the signed `Exec`
  verdict and the unsigned 256-bit deployed verdict AGREE, tooth by tooth. The audit's
  divergence on negative attacker scalars is real but out of scope BY SUBSTRATE here: the
  deployed register file cannot carry a negative value.

* **The inversions land at deployed width** (`deployed_tooth_conserves`/`_capacity`/
  `_pays`/`_alive`): stated DIRECTLY over `DeployedConstraint.admits` and quantifying over
  ARBITRARY `DInput`s — attacker-supplied unsigned 256-bit register files — with no `Exec`
  detour and hence no signedness caveat at all. Each has a refusing negative twin
  (`#guard`) showing the tooth bites.

## The flagship

`descent_step_teeth_deployed`: for every RECEIPT-REACHABLE state `s` and legal model step
`step s m = some s'`, EVERY tooth of EVERY matching case (verb arms AND `SlotChanged`
riders) that lies in the deployed subset evaluates to `.ok` under
`Dregg2.Exec.DeployedConstraint.admitsTop` on the marshalled register/heap input — i.e.
the `@[export dregg_constraint_admits]` evaluator the deployed node routes through ADMITS
the descent's legal play, tooth by tooth. This is the descent twin of the tug's
`program_admits_legal_play_deployed` (`MultiwayTugProgram §4I`), riding the completeness
∀-weld (`reachable_step_admitted`) instead of a driven single run.

## Honest scope (what is NOT claimed)

* **Guard dispatch stays executor-level.** `MethodIs`/`SlotChanged` case selection is the
  Rust executor's loop (same boundary as the tug §4I refinement); the theorems here are
  per-tooth verdicts conditional on the (Exec-mirrored) guard matching.
* **Verdicts are at the `admits`/`admitsTop` level** — the same function `admitsFFI`
  wraps; the String wire codec's faithfulness is `DeployedConstraint.lean`'s own `#guard`
  battery, not re-proven here.
* **The genesis mint is NOT re-based.** Its `deltaEquals` sentinel tooth reads the OLD
  heap key, and on a genuinely-absent pre-genesis key the deployed atom fails closed
  (`some a` required) while the Exec drive models the sentinel as present-`0`
  (`preGenesis`). That absent-vs-zero first-write seam is the same class the tug
  reconciliation documented; the verb cases proven here never touch it (`oldPresent` with
  both states materialized).
* **The census remainder is DESIGNED, not fired here** (`countFieldsEq`, six teeth):
  closing it requires the deployed evaluator's exported subset to carry the N-key
  aggregate — kernel-adjacent deployed admission logic, ember-gated, NOT this lane's to
  fire. The precise design + the falsifier that shows the gap are in §9; the `#guard`
  battery proves the teeth THIS module lowers (everything else) admit the
  two-relic/one-counter census forgery, so the census tooth is load-bearing, not
  decorative. ⚑ While this file was being authored, a CONCURRENT lane landed (as
  working-tree WIP) a `DConstraint.fieldsCountEquals` arm + `DInput.cells` run in
  `DeployedConstraint.lean` — convergent with the §9 design. This module's lowering
  deliberately does NOT ride that WIP yet (`toDTop` still maps `countFieldsEq` to
  `none`): the census transport is the named follow-up once that widening COMMITS.

Substrate said out loud: this is the Lean-authored CONSTRAINT-PROGRAM layer (law-#1
compliant — the teeth and both evaluators are Lean); no AIR/circuit object is authored or
touched here.
-/
import Dregg2.Games.DungeonCompleteness
import Dregg2.Exec.DeployedConstraint

namespace Dregg2.Games.Dungeon.Prog

open Dregg2.Exec (Value evalConstraint evalSimple sumScalars)
open Dregg2.Exec.DeployedConstraint

/-! ⚑ The deployed teeth are stated over the DAY'S WORLD (`Dungeon.WorldParam`): the map
is drawn from the committed day-seed, so `guardHp` and the minted-home teeth are
parameters. Every bridge theorem below therefore holds for the whole drawn family. -/
variable [WorldParam]

-- The world parameter is blanket-scoped over the file (every rule and law is stated over
-- the day's drawn map); a handful of pure list/count helpers legitimately do not mention
-- it, and the section-variable linter would otherwise report each one.
set_option linter.unusedSectionVars false

/-! ## 0. Name pins (`Nat.repr` is opaque to `simp`) + encode-scalar pins.

These mirror the (private, hence not importable) pins of `DungeonCompleteness.lean`. -/

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

/-- Membership transfers back through the `Nat → Int` cast map (local, cast-stable). -/
private theorem mem_map_natcast {l : List Nat} {x : Nat}
    (h : ((x : Nat) : Int) ∈ l.map (fun v => (v : Int))) : x ∈ l := by
  simpa using h

private theorem encode_scalar_relic (s : DState) (i : Nat) (hi : i < RELICS) :
    (encode s).scalar (relicName i) = some (s.custody.getD i 0 : Int) := by
  have hiCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    have : i < 8 := hi
    omega
  rcases hiCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [encode, Value.scalar, Value.field]

@[simp] private theorem encode_scalar_sentinel (s : DState) :
    (encode s).scalar sentinelField = some 1 := by
  simp [encode, Value.scalar, Value.field, sentinelField]

/-! ## 1. The register allocation and the marshalling (the descent's `tugSlots`). -/

/-- Register allocation: the descent's 13 register names → deployed slot indices
`0..12` (slots `13..15` spare, never named by a tooth). -/
def dgRegIdx : String → Nat
  | "depth" => 0 | "spent" => 1 | "wounds" => 2 | "fate" => 3
  | "pack" => 4 | "bank" => 5
  | "way_2" => 6 | "way_3" => 7 | "way_4" => 8
  | "hoard_1" => 9 | "hoard_2" => 10 | "hoard_3" => 11 | "hoard_4" => 12
  | _ => 15

/-- The 13 register names the descent's teeth may mention (heap keys are separate). -/
def registerNames : List String :=
  ["depth", "spent", "wounds", "fate", "pack", "bank",
   wayName 2, wayName 3, wayName 4,
   hoardName 1, hoardName 2, hoardName 3, hoardName 4]

/-- Marshal a model state into the deployed 16-slot register file, each projection at
its `dgRegIdx` slot. -/
def dgSlots (s : DState) : List DField :=
  [s.depth, s.spent, s.wounds, s.fate, pack s, bank s,
   s.ways.getD 0 0, s.ways.getD 1 0, s.ways.getD 2 0,
   hoardAt s 1, hoardAt s 2, hoardAt s 3, hoardAt s 4, 0, 0, 0]

/-- The heap keys the descent's teeth may mention: the spween sentinel + the eight
individually committed relic custody keys. -/
def keyList : List HeapKeyRef := .sentinel :: relicKeys

/-- Resolve a heap key to its marshalled value — BY CONSTRUCTION the very number the
Exec evaluator reads at the same record field, so the register↔heap marshalling cannot
drift from the Exec substrate. -/
def heapVal (s : DState) (k : HeapKeyRef) : DField :=
  (((encode s).scalar k.field).getD 0).toNat

/-- The absent marshalled context (the descent's teeth are pure — class (a)). -/
def noCtx : DCtx :=
  { present := false, height := 0, senderPresent := false, sender := 0,
    epochPresent := false, epoch := 0, epochCount := 0 }

/-- The register-only deployed input for one marshalled transition. -/
def baseInput (s s' : DState) : DInput :=
  { oldPresent := true, newNonce := 0,
    oldRegs := dgSlots s, newRegs := dgSlots s',
    heapOld := none, heapNew := none, heapOther := none,
    oldBalance := 0, newBalance := 0, ctx := noCtx, cells := [] }

/-- The marshalled deployed input for one descent tooth on a `(s, s')` transition:
registers via `dgSlots`; for a `heapField` tooth, the resolved key value on each side. -/
def dgInput (s s' : DState) : Constraint → DInput
  | .heapField k _ =>
      { baseInput s s' with heapOld := some (heapVal s k), heapNew := some (heapVal s' k) }
  | _ => baseInput s s'

/-! ## 2. Marshalling resolution: the Exec read and the deployed slot AGREE by name. -/

/-- THE Int→Nat pin, per register name: the slot index is in range and the Exec
evaluator's signed read of `encode s` at name `r` is exactly the (nonnegative) cast of
the deployed slot value. -/
private theorem resolve (s : DState) {r : String} (hr : r ∈ registerNames) :
    dgRegIdx r < stateSlots ∧
      (encode s).scalar r = some (((dgSlots s).getD (dgRegIdx r) 0 : Nat) : Int) := by
  simp only [registerNames, wayName_2, wayName_3, wayName_4,
    hoardName_1, hoardName_2, hoardName_3, hoardName_4,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by simp [encode, Value.scalar, Value.field, dgSlots, dgRegIdx]⟩

/-- The heap twin: for a descent heap key, the Exec read is the cast of the marshalled
heap value. -/
private theorem resolveHeap (s : DState) {k : HeapKeyRef} (hk : k ∈ keyList) :
    (encode s).scalar k.field = some ((heapVal s k : Nat) : Int) := by
  rcases List.mem_cons.mp hk with rfl | hk
  · simp [heapVal, HeapKeyRef.field]
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
    have hi8 : i < RELICS := List.mem_range.mp hi
    have hpin := encode_scalar_relic s i hi8
    simp only [HeapKeyRef.field, heapVal, hpin, Option.getD_some, Int.toNat_natCast]

/-! ## 3. Reachable states are SMALL — the bound that makes low-64-lane and
256-bit-full-field evaluation coincide with the Exec model on the marshalled image. -/

/-- The two value bounds `Inv` does not carry: wounds and the way flags. -/
private def Tight (s : DState) : Prop := s.wounds ≤ 2 ∧ ∀ w ∈ s.ways, w ≤ 1

/-- Guardians are slayable in at most two blows — on EVERY drawn map (the day's world
law, `Dungeon.wf_guardHp_le`), which is what keeps `wounds` inside its deployed range. -/
private theorem guardHp_le (d : Nat) : guardHp d ≤ 2 := wf_guardHp_le d

private theorem mem_of_mem_set' {l : List Nat} {i v c : Nat}
    (hc : c ∈ l.set i v) : c ∈ l ∨ c = v := by
  induction l generalizing i with
  | nil => simp [List.set] at hc
  | cons hd tl ih =>
    cases i with
    | zero => simp only [List.set, List.mem_cons] at hc ⊢; tauto
    | succ j =>
      simp only [List.set, List.mem_cons] at hc ⊢
      rcases hc with h | h
      · tauto
      · rcases ih h with h' | h' <;> tauto

private theorem tight_genesis : Tight genesisState := by
  refine ⟨Nat.zero_le _, ?_⟩
  intro w hw
  simp only [genesisState, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> omega

private theorem tight_step {s s' : DState} {m : Move}
    (ht : Tight s) (hstep : step s m = some s') : Tight s' := by
  obtain ⟨hw, hwys⟩ := ht
  cases m with
  | delve =>
    simp only [step] at hstep; split at hstep
    · cases hstep; exact ⟨Nat.zero_le 2, hwys⟩
    · exact absurd hstep (by simp)
  | unlock w =>
    simp only [step] at hstep; split at hstep
    · cases hstep
      refine ⟨hw, ?_⟩
      intro x hx
      rcases mem_of_mem_set' hx with h | rfl
      · exact hwys x h
      · omega
    · exact absurd hstep (by simp)
  | smite =>
    simp only [step] at hstep; split at hstep
    · rename_i hcond
      cases hstep
      refine ⟨?_, hwys⟩
      have := guardHp_le s.depth
      have h2 := hcond.2.2.2
      show s.wounds + 1 ≤ 2
      omega
    · exact absurd hstep (by simp)
  | loot r =>
    simp only [step] at hstep; split at hstep
    · cases hstep; exact ⟨hw, hwys⟩
    · exact absurd hstep (by simp)
  | flee =>
    simp only [step] at hstep; split at hstep
    · cases hstep; exact ⟨hw, hwys⟩
    · exact absurd hstep (by simp)

private theorem foldl_none' (ms : List Move) :
    ms.foldl (fun acc m => acc.bind (fun t => step t m)) none = none := by
  induction ms with
  | nil => rfl
  | cons m rest ih => exact ih

private theorem reachable_tight {s : DState} (h : Reachable s) : Tight s := by
  obtain ⟨ms, hms⟩ := h
  suffices H : ∀ (xs : List Move) (s0 s1 : DState), Tight s0 →
      xs.foldl (fun acc m => acc.bind (fun t => step t m)) (some s0) = some s1 →
      Tight s1 by
    exact H ms genesisState s tight_genesis hms
  intro xs
  induction xs with
  | nil =>
    intro s0 s1 h0 h1
    simp at h1
    exact h1 ▸ h0
  | cons m rest ih =>
    intro s0 s1 h0 h1
    simp only [List.foldl_cons, Option.bind_some] at h1
    cases hstep : step s0 m with
    | none => rw [hstep, foldl_none'] at h1; simp at h1
    | some smid => rw [hstep] at h1; exact ih smid s1 (tight_step h0 hstep) h1

/-- A legal step out of a reachable state is reachable (append the receipt). -/
private theorem reachable_step {s s' : DState} {m : Move}
    (hreach : Reachable s) (hstep : step s m = some s') : Reachable s' := by
  obtain ⟨ms, hms⟩ := hreach
  refine ⟨ms ++ [m], ?_⟩
  rw [replay] at hms ⊢
  rw [List.foldl_append, hms]
  simp [hstep]

private theorem getD_le_of_forall {l : List Nat} {b : Nat}
    (h : ∀ x ∈ l, x ≤ b) (i : Nat) : l.getD i 0 ≤ b := by
  rw [List.getD_eq_getElem?_getD]
  cases hv : l[i]? with
  | none => simp
  | some v => simpa using h v (List.mem_of_getElem? hv)

/-- Every marshalled register of an `Inv`+`Tight` state is at most 26 (= `BREATH`,
the largest any projection can reach), hence far below both the `field_to_u64` lane
and the `FIELD_DELTA_RESULT_BITS` range. -/
private theorem regs_small {s : DState} (hInv : Inv s) (ht : Tight s) {r : String}
    (hr : r ∈ registerNames) : (dgSlots s).getD (dgRegIdx r) 0 ≤ 26 := by
  obtain ⟨⟨hlen, hcodes⟩, hspent, hdepth, hfate, hways, hcap, hrest⟩ := hInv
  obtain ⟨hw, hwys⟩ := ht
  have hpack : pack s ≤ 8 := le_trans List.countP_le_length (le_of_eq hlen)
  have hbank : bank s ≤ 8 := le_trans List.countP_le_length (le_of_eq hlen)
  have hhoard : ∀ d, hoardAt s d ≤ 8 :=
    fun d => le_trans List.countP_le_length (le_of_eq hlen)
  have hwv : ∀ i, s.ways.getD i 0 ≤ 1 := getD_le_of_forall hwys
  simp only [registerNames, wayName_2, wayName_3, wayName_4,
    hoardName_1, hoardName_2, hoardName_3, hoardName_4,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  have hFl : s.depth ≤ 4 := hdepth
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show s.depth ≤ 26; omega
  · show s.spent ≤ 26; exact hspent
  · show s.wounds ≤ 26; omega
  · show s.fate ≤ 26; omega
  · show pack s ≤ 26; omega
  · show bank s ≤ 26; omega
  · show s.ways.getD 0 0 ≤ 26; have := hwv 0; omega
  · show s.ways.getD 1 0 ≤ 26; have := hwv 1; omega
  · show s.ways.getD 2 0 ≤ 26; have := hwv 2; omega
  · show hoardAt s 1 ≤ 26; have := hhoard 1; omega
  · show hoardAt s 2 ≤ 26; have := hhoard 2; omega
  · show hoardAt s 3 ≤ 26; have := hhoard 3; omega
  · show hoardAt s 4 ≤ 26; have := hhoard 4; omega

/-- Every marshalled heap value of an `Inv` state is at most `BANKED = 9`. -/
private theorem heap_small {s : DState} (hInv : Inv s) {k : HeapKeyRef}
    (hk : k ∈ keyList) : heapVal s k ≤ 9 := by
  obtain ⟨⟨hlen, hcodes⟩, _⟩ := hInv
  rcases List.mem_cons.mp hk with rfl | hk
  · show heapVal s .sentinel ≤ 9
    simp [heapVal, HeapKeyRef.field]
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
    have hi8 : i < RELICS := List.mem_range.mp hi
    have hval : heapVal s (.named (relicName i)) = s.custody.getD i 0 := by
      have hpin := encode_scalar_relic s i hi8
      simp only [HeapKeyRef.field, heapVal, hpin, Option.getD_some, Int.toNat_natCast]
    rw [hval]
    have hcode : ∀ c ∈ s.custody, c ≤ 9 := by
      intro c hc
      rcases hcodes c hc with ⟨_, h4⟩ | rfl | rfl
      · have : (FLOORS : Nat) = 4 := rfl
        omega
      · decide
      · decide
    exact getD_le_of_forall hcode i

/-! ## 4. The lowering into the deployed subset (`toDTop`) + the decidable side
conditions the transport needs (`toothOK`), discharged once for the WHOLE program. -/

/-- Lower an `anyOf`-liftable simple tooth to a deployed `(parity, atom)` branch —
exactly the peeled-`Not` shape `eval.rs::evaluate_simple_constraint` reduces to. -/
def Simple.toBranch : Simple → Bool × DConstraint
  | .fieldEquals r v => (false, .fieldEquals (dgRegIdx r) v)
  | .fieldGte r v    => (false, .fieldGte (dgRegIdx r) v)
  | .fieldLte r v    => (false, .fieldLte (dgRegIdx r) v)
  | .immutable r     => (false, .immutable (dgRegIdx r))
  | .negate inner    => (!(inner.toBranch.1), inner.toBranch.2)

/-- The descent heap atoms embed into the deployed heap-atom vocabulary VERBATIM. -/
def HeapAtom.toDHeap : HeapAtom → DHeapAtom
  | .equals v      => .equals v
  | .immutable     => .immutable
  | .monotonic     => .monotonic
  | .memberOf set  => .memberOf set
  | .deltaEquals d => .deltaEquals d

/-- **The partition, as a function**: lower a descent tooth into the deployed
evaluator's exported subset. `none` on EXACTLY the `countFieldsEq` census teeth — the
one descent constructor outside the deployed pure subset (the §9 remainder). -/
def Constraint.toDTop : Constraint → Option DTop
  | .fieldEquals r v => some (.base (.fieldEquals (dgRegIdx r) v))
  | .fieldGte r v => some (.base (.fieldGte (dgRegIdx r) v))
  | .fieldLte r v => some (.base (.fieldLte (dgRegIdx r) v))
  | .fieldDelta r d => some (.base (.fieldDelta (dgRegIdx r) d))
  | .strictMonotonic r => some (.base (.strictMonotonic (dgRegIdx r)))
  | .immutable r => some (.base (.immutable (dgRegIdx r)))
  | .sumEquals rs v => some (.base (.sumEquals (rs.map dgRegIdx) v))
  | .affineLe ts c => some (.base (.affineLe (ts.map (fun t => (t.1, dgRegIdx t.2))) c))
  | .inRangeTwoSided r lo hi => some (.base (.inRangeTwoSided (dgRegIdx r) lo hi))
  | .allowedTransitions r al => some (.base (.allowedTransitions (dgRegIdx r) al))
  | .anyOf vs => some (.anyOf (vs.map Simple.toBranch))
  | .heapField _ atom => some (.base (.heapField atom.toDHeap))
  | .countFieldsEq _ _ _ => none

/-- Names mentioned by an `anyOf`-liftable tooth are register names. -/
def simpleOK : Simple → Bool
  | .fieldEquals r _ => decide (r ∈ registerNames)
  | .fieldGte r _ => decide (r ∈ registerNames)
  | .fieldLte r _ => decide (r ∈ registerNames)
  | .immutable r => decide (r ∈ registerNames)
  | .negate inner => simpleOK inner

/-- The decidable side conditions of the transport: every mentioned register name is
allocated, every heap key is a descent key, and the few numeric literals that meet a
LANE (not full-field) comparison are small. -/
def toothOK : Constraint → Bool
  | .fieldEquals r _ => decide (r ∈ registerNames)
  | .fieldGte r _ => decide (r ∈ registerNames)
  | .fieldLte r _ => decide (r ∈ registerNames)
  | .fieldDelta r d => decide (r ∈ registerNames) && decide (d ≤ 1000)
  | .strictMonotonic r => decide (r ∈ registerNames)
  | .immutable r => decide (r ∈ registerNames)
  | .sumEquals rs v => rs.all (fun r => decide (r ∈ registerNames)) && decide (v ≤ 1000)
  | .affineLe ts _ => ts.all (fun t => decide (t.2 ∈ registerNames))
  | .inRangeTwoSided r _ _ => decide (r ∈ registerNames)
  | .allowedTransitions r _ => decide (r ∈ registerNames)
  | .anyOf vs => vs.all simpleOK
  | .heapField k _ => decide (k ∈ keyList)
  | .countFieldsEq _ _ _ => true

/-- EVERY tooth of the deployed program satisfies the transport side conditions —
kernel-checked over the concrete authored object. -/
private theorem programOK :
    (programCases.all fun tc => tc.constraints.all toothOK) = true := by rfl

/-! ## 5. Per-shape transport: Exec truth ⇒ deployed `.ok` on the marshalled image. -/

/-- `fieldAdd` is PLAIN addition below the lane (no wrap, high limbs zero). -/
private theorem fieldAdd_small {a d : Nat} (ha : a ≤ 26) (hd : d ≤ 1000) :
    fieldAdd a d = a + d := by
  have h1 : a / 18446744073709551616 = 0 := Nat.div_eq_of_lt (by omega)
  have h2 : a % 18446744073709551616 = a := Nat.mod_eq_of_lt (by omega)
  have h3 : d % 18446744073709551616 = d := Nat.mod_eq_of_lt (by omega)
  have h4 : (a + d) % 18446744073709551616 = a + d := Nat.mod_eq_of_lt (by omega)
  simp only [fieldAdd, low64, two64]
  rw [h1, h2, h3, h4, Nat.zero_mul, Nat.zero_add]

private theorem low64_small {a : Nat} (ha : a ≤ 1026) : low64 a = a := by
  unfold low64 two64
  exact Nat.mod_eq_of_lt (by omega)

private theorem tr_fieldEquals {s s' : DState} {r : String} (hr : r ∈ registerNames)
    (v : Nat)
    (hexec : evalConstraint (Constraint.fieldEquals r v).toExec
      (encode s) (encode s') = true) :
    admits (.fieldEquals (dgRegIdx r) v) (baseInput s s') = .ok := by
  obtain ⟨hidx, hval⟩ := resolve s' hr
  simp only [Constraint.toExec, evalConstraint, evalSimple, hval] at hexec
  have hx : (dgSlots s').getD (dgRegIdx r) 0 = v := by
    have h := Option.some.inj (beq_iff_eq.mp hexec)
    exact_mod_cast h
  have hgr : getReg (dgSlots s') (dgRegIdx r)
      = some ((dgSlots s').getD (dgRegIdx r) 0) := by
    unfold getReg
    rw [if_neg (Nat.not_le.mpr hidx)]
  simp only [admits, baseInput, hgr]
  rw [if_pos hx]

private theorem tr_fieldGte {s s' : DState} {r : String} (hr : r ∈ registerNames)
    (v : Nat)
    (hexec : evalConstraint (Constraint.fieldGte r v).toExec
      (encode s) (encode s') = true) :
    admits (.fieldGte (dgRegIdx r) v) (baseInput s s') = .ok := by
  obtain ⟨hidx, hval⟩ := resolve s' hr
  simp only [Constraint.toExec, evalConstraint, evalSimple, hval] at hexec
  have hx : v ≤ (dgSlots s').getD (dgRegIdx r) 0 := by
    have h := of_decide_eq_true hexec
    exact_mod_cast h
  have hgr : getReg (dgSlots s') (dgRegIdx r)
      = some ((dgSlots s').getD (dgRegIdx r) 0) := by
    unfold getReg
    rw [if_neg (Nat.not_le.mpr hidx)]
  simp only [admits, baseInput, hgr]
  rw [if_pos hx]

private theorem tr_fieldLte {s s' : DState} {r : String} (hr : r ∈ registerNames)
    (v : Nat)
    (hexec : evalConstraint (Constraint.fieldLte r v).toExec
      (encode s) (encode s') = true) :
    admits (.fieldLte (dgRegIdx r) v) (baseInput s s') = .ok := by
  obtain ⟨hidx, hval⟩ := resolve s' hr
  simp only [Constraint.toExec, evalConstraint, evalSimple, hval] at hexec
  have hx : (dgSlots s').getD (dgRegIdx r) 0 ≤ v := by
    have h := of_decide_eq_true hexec
    exact_mod_cast h
  have hgr : getReg (dgSlots s') (dgRegIdx r)
      = some ((dgSlots s').getD (dgRegIdx r) 0) := by
    unfold getReg
    rw [if_neg (Nat.not_le.mpr hidx)]
  simp only [admits, baseInput, hgr]
  rw [if_pos hx]

private theorem tr_fieldDelta {s s' : DState} {r : String} (hr : r ∈ registerNames)
    {d : Nat} (hd : d ≤ 1000)
    (hb : (dgSlots s).getD (dgRegIdx r) 0 ≤ 26)
    (hexec : evalConstraint (Constraint.fieldDelta r d).toExec
      (encode s) (encode s') = true) :
    admits (.fieldDelta (dgRegIdx r) d) (baseInput s s') = .ok := by
  obtain ⟨hidx, hvalO⟩ := resolve s hr
  obtain ⟨_, hvalN⟩ := resolve s' hr
  simp only [Constraint.toExec, evalConstraint, evalSimple, hvalO, hvalN] at hexec
  have hx : (dgSlots s').getD (dgRegIdx r) 0 = (dgSlots s).getD (dgRegIdx r) 0 + d := by
    have h := beq_iff_eq.mp hexec
    exact_mod_cast h
  have hadd := fieldAdd_small hb hd
  have hlt : (dgSlots s).getD (dgRegIdx r) 0 + d < two30 :=
    Nat.lt_of_le_of_lt (Nat.add_le_add hb hd) (by decide)
  have hrange : resultInRange ((dgSlots s).getD (dgRegIdx r) 0 + d) = true := by
    simpa [resultInRange] using hlt
  simp only [admits, baseInput]
  rw [if_neg (Nat.not_le.mpr hidx), if_true]
  rw [if_neg (show ¬ ((dgSlots s').getD (dgRegIdx r) 0
      ≠ fieldAdd ((dgSlots s).getD (dgRegIdx r) 0) d) from by
    rw [hadd, hx]
    exact not_not_intro rfl)]
  rw [if_neg (show ¬ ¬ (resultInRange ((dgSlots s').getD (dgRegIdx r) 0) = true) from by
    rw [hx]
    exact not_not_intro hrange)]

private theorem tr_strictMonotonic {s s' : DState} {r : String}
    (hr : r ∈ registerNames)
    (hexec : evalConstraint (Constraint.strictMonotonic r).toExec
      (encode s) (encode s') = true) :
    admits (.strictMonotonic (dgRegIdx r)) (baseInput s s') = .ok := by
  obtain ⟨hidx, hvalO⟩ := resolve s hr
  obtain ⟨_, hvalN⟩ := resolve s' hr
  simp only [Constraint.toExec, evalConstraint, evalSimple, hvalO, hvalN] at hexec
  have hx : (dgSlots s).getD (dgRegIdx r) 0 < (dgSlots s').getD (dgRegIdx r) 0 := by
    have h := of_decide_eq_true hexec
    exact_mod_cast h
  simp only [admits, baseInput]
  rw [if_neg (Nat.not_le.mpr hidx), if_true, if_pos hx]

private theorem tr_immutable {s s' : DState} {r : String} (hr : r ∈ registerNames)
    (hexec : evalConstraint (Constraint.immutable r).toExec
      (encode s) (encode s') = true) :
    admits (.immutable (dgRegIdx r)) (baseInput s s') = .ok := by
  obtain ⟨hidx, hvalO⟩ := resolve s hr
  obtain ⟨_, hvalN⟩ := resolve s' hr
  simp only [Constraint.toExec, evalConstraint, evalSimple, hvalO, hvalN] at hexec
  have hx : (dgSlots s').getD (dgRegIdx r) 0 = (dgSlots s).getD (dgRegIdx r) 0 := by
    have h := Option.some.inj (beq_iff_eq.mp hexec)
    exact_mod_cast h
  simp only [admits, baseInput]
  rw [if_neg (Nat.not_le.mpr hidx), if_true, if_pos hx]

/-- The Exec sum of register reads is the cast of the deployed slot-value sum. -/
private theorem sum_corr (s' : DState) : ∀ (rs : List String),
    (∀ r ∈ rs, r ∈ registerNames) →
    sumScalars (encode s') rs
      = some (((rs.map (fun r => (dgSlots s').getD (dgRegIdx r) 0)).sum : Nat) : Int) := by
  intro rs
  induction rs with
  | nil => intro _; rfl
  | cons r rest ih =>
    intro hmem
    obtain ⟨_, hval⟩ := resolve s' (hmem r (List.mem_cons_self ..))
    have hrest := ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
    simp only [sumScalars, List.foldr_cons] at hrest ⊢
    rw [hrest, hval]
    simp only [List.map_cons, List.sum_cons, Option.some.injEq]
    push_cast
    ring

/-- The deployed `SumEquals` accumulator admits when every index is allocated, the
lane total stays below `2^64`, and it lands on `low64 v` (tug's `sumGo_ok`, local). -/
private theorem sumGo_ok (v : DField) (regs : List DField) :
    ∀ (l : List Nat) (acc : Nat),
      (∀ i ∈ l, i < stateSlots) →
      (acc + (l.map (fun i => low64 (regs.getD i 0))).sum < two64) →
      (acc + (l.map (fun i => low64 (regs.getD i 0))).sum = low64 v) →
      sumEqualsAdmit.go v regs l acc = DAdmit.ok := by
  intro l
  induction l with
  | nil =>
    intro acc _ _ hgoal
    simp only [List.map_nil, List.sum_nil, Nat.add_zero] at hgoal
    unfold sumEqualsAdmit.go
    rw [if_pos hgoal]
  | cons i rest ih =>
    intro acc hidx hbound hgoal
    have hi : i < stateSlots := hidx i (by simp)
    simp only [List.map_cons, List.sum_cons] at hbound hgoal
    unfold sumEqualsAdmit.go
    rw [if_neg (by omega : ¬ i ≥ stateSlots)]
    simp only
    rw [if_neg (by omega : ¬ acc + low64 (regs.getD i 0) ≥ two64)]
    apply ih (acc + low64 (regs.getD i 0))
    · intro j hj; exact hidx j (by simp [hj])
    · omega
    · omega

private theorem tr_sumEquals {s s' : DState} {rs : List String}
    (hrs : ∀ r ∈ rs, r ∈ registerNames) {v : Nat} (hv : v ≤ 1000)
    (hb : ∀ r ∈ rs, (dgSlots s').getD (dgRegIdx r) 0 ≤ 26)
    (hexec : evalConstraint (Constraint.sumEquals rs v).toExec
      (encode s) (encode s') = true) :
    admits (.sumEquals (rs.map dgRegIdx) v) (baseInput s s') = .ok := by
  have hcorr := sum_corr s' rs hrs
  simp only [Constraint.toExec, evalConstraint, hcorr] at hexec
  have hsum : (rs.map (fun r => (dgSlots s').getD (dgRegIdx r) 0)).sum = v := by
    have h := Option.some.inj (beq_iff_eq.mp hexec)
    exact_mod_cast h
  have hlanes : ((rs.map dgRegIdx).map
      (fun i => low64 ((dgSlots s').getD i 0))).sum = v := by
    rw [List.map_map]
    have hcong : rs.map ((fun i => low64 ((dgSlots s').getD i 0)) ∘ dgRegIdx)
        = rs.map (fun r => (dgSlots s').getD (dgRegIdx r) 0) :=
      List.map_congr_left (fun r hrm => by
        simp only [Function.comp_apply]
        exact low64_small (le_trans (hb r hrm) (by omega)))
    rw [hcong, hsum]
  have hlow : low64 v = v := low64_small (by omega)
  simp only [admits, baseInput, sumEqualsAdmit]
  apply sumGo_ok
  · intro i hi
    obtain ⟨r, hrm, rfl⟩ := List.mem_map.mp hi
    exact (resolve s' (hrs r hrm)).1
  · rw [Nat.zero_add, hlanes]
    unfold two64
    omega
  · rw [Nat.zero_add, hlanes, hlow]

/-- Exec `affineSum` and the deployed `affineSum` compute the SAME integer on the
marshalled image (low-64 lanes are the identity below the bound). -/
private theorem affine_corr (s' : DState) : ∀ (ts : List (Int × String)),
    (∀ t ∈ ts, t.2 ∈ registerNames) →
    (∀ t ∈ ts, (dgSlots s').getD (dgRegIdx t.2) 0 ≤ 26) →
    ∃ S : Int,
      Dregg2.Exec.DeployedConstraint.affineSum
        (ts.map (fun t => (t.1, dgRegIdx t.2))) (dgSlots s') = .ok S ∧
      Dregg2.Exec.affineSum (encode s') ts = some S := by
  intro ts
  induction ts with
  | nil => intro _ _; exact ⟨0, rfl, rfl⟩
  | cons t rest ih =>
    intro hmem hb
    obtain ⟨S, hdep, hex⟩ := ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
      (fun x hx => hb x (List.mem_cons_of_mem _ hx))
    obtain ⟨hidx, hval⟩ := resolve s' (hmem t (List.mem_cons_self ..))
    have hlow : low64 ((dgSlots s').getD (dgRegIdx t.2) 0)
        = (dgSlots s').getD (dgRegIdx t.2) 0 :=
      low64_small (le_trans (hb t (List.mem_cons_self ..)) (by omega))
    refine ⟨t.1 * ((dgSlots s').getD (dgRegIdx t.2) 0 : Int) + S, ?_, ?_⟩
    · simp only [List.map_cons, Dregg2.Exec.DeployedConstraint.affineSum]
      rw [if_neg (by omega : ¬ dgRegIdx t.2 ≥ stateSlots), hdep, hlow]
    · simp only [Dregg2.Exec.affineSum, List.foldr_cons] at hex ⊢
      rw [hex, hval]
      simp only [Option.some.injEq]
      ring

private theorem tr_affineLe {s s' : DState} {ts : List (Int × String)}
    (hts : ∀ t ∈ ts, t.2 ∈ registerNames) {c : Int}
    (hb : ∀ t ∈ ts, (dgSlots s').getD (dgRegIdx t.2) 0 ≤ 26)
    (hexec : evalConstraint (Constraint.affineLe ts c).toExec
      (encode s) (encode s') = true) :
    admits (.affineLe (ts.map (fun t => (t.1, dgRegIdx t.2))) c) (baseInput s s') = .ok := by
  obtain ⟨S, hdep, hex⟩ := affine_corr s' ts hts hb
  have hmap : ts.map (fun t : Int × String => (t.1, t.2)) = ts := by simp
  have hexec' : Dregg2.Exec.evalConstraint
      (.affineLe ts c) (encode s) (encode s') = true := by
    simpa only [Constraint.toExec, hmap] using hexec
  simp only [Dregg2.Exec.evalConstraint, hex] at hexec'
  have hle : S ≤ c := of_decide_eq_true hexec'
  simp only [admits, baseInput]
  rw [hdep]
  show (if S > c then DAdmit.violated else DAdmit.ok) = DAdmit.ok
  rw [if_neg (by omega : ¬ S > c)]

private theorem tr_inRangeTwoSided {s s' : DState} {r : String}
    (hr : r ∈ registerNames) (lo hi : Nat)
    (hb : (dgSlots s').getD (dgRegIdx r) 0 ≤ 26)
    (hexec : evalConstraint (Constraint.inRangeTwoSided r lo hi).toExec
      (encode s) (encode s') = true) :
    admits (.inRangeTwoSided (dgRegIdx r) lo hi) (baseInput s s') = .ok := by
  obtain ⟨hidx, hval⟩ := resolve s' hr
  simp only [Constraint.toExec, evalConstraint, evalSimple, hval,
    Bool.and_eq_true] at hexec
  obtain ⟨hlo, hhi⟩ := hexec
  have hlo' : lo ≤ (dgSlots s').getD (dgRegIdx r) 0 := by
    have h := of_decide_eq_true hlo
    exact_mod_cast h
  have hhi' : (dgSlots s').getD (dgRegIdx r) 0 ≤ hi := by
    have h := of_decide_eq_true hhi
    exact_mod_cast h
  have hlow := low64_small (le_trans hb (by omega))
  simp only [admits, baseInput]
  rw [if_neg (Nat.not_le.mpr hidx)]
  simp only [hlow]
  rw [if_pos ⟨hlo', hhi'⟩]

private theorem tr_allowedTransitions {s s' : DState} {r : String}
    (hr : r ∈ registerNames) (al : List (Nat × Nat))
    (hexec : evalConstraint (Constraint.allowedTransitions r al).toExec
      (encode s) (encode s') = true) :
    admits (.allowedTransitions (dgRegIdx r) al) (baseInput s s') = .ok := by
  obtain ⟨hidx, hvalO⟩ := resolve s hr
  obtain ⟨_, hvalN⟩ := resolve s' hr
  simp only [Constraint.toExec, evalConstraint, hvalO, hvalN] at hexec
  obtain ⟨p, hpmem, hp⟩ := List.any_eq_true.mp hexec
  obtain ⟨q, hqmem, rfl⟩ := List.mem_map.mp hpmem
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  have hq1 : q.1 = (dgSlots s).getD (dgRegIdx r) 0 := by exact_mod_cast hp.1
  have hq2 : q.2 = (dgSlots s').getD (dgRegIdx r) 0 := by exact_mod_cast hp.2
  simp only [admits, baseInput]
  rw [if_neg (Nat.not_le.mpr hidx), if_true]
  rw [if_pos (List.any_eq_true.mpr ⟨q, hqmem, by simp [hq1, hq2]⟩)]

/-! ### The `anyOf` branch agreement — verdict-level, both directions. -/

private def flipV : DAdmit → DAdmit
  | .ok => .violated
  | .violated => .ok
  | e => e

private theorem branchAdmits_neg (p : Bool) (c : DConstraint) (i : DInput) :
    branchAdmits (!p, c) i = flipV (branchAdmits (p, c) i) := by
  cases p <;> cases h : admits c i <;>
    simp [branchAdmits, flipV, h]

/-- On the marshalled image, a deployed `(parity, atom)` branch verdict IS the Exec
`Simple` verdict (`.ok` ↔ `true`, `.violated` ↔ `false`) — the full iff, needed so a
`Not` chain flips faithfully. -/
private theorem branch_agree {s s' : DState} (v : Simple) (hok : simpleOK v = true) :
    branchAdmits v.toBranch (baseInput s s') =
      (if evalSimple v.toExec (encode s) (encode s') = true
       then DAdmit.ok else DAdmit.violated) := by
  induction v with
  | fieldEquals r w =>
    have hr : r ∈ registerNames := of_decide_eq_true hok
    obtain ⟨hidx, hval⟩ := resolve s' hr
    have hgr : getReg (dgSlots s') (dgRegIdx r)
        = some ((dgSlots s').getD (dgRegIdx r) 0) := by
      unfold getReg
      rw [if_neg (Nat.not_le.mpr hidx)]
    by_cases h : (dgSlots s').getD (dgRegIdx r) 0 = w
    · have hT : evalSimple (Simple.toExec (.fieldEquals r w))
          (encode s) (encode s') = true := by
        simp only [Simple.toExec, evalSimple, hval, h]
        exact beq_self_eq_true _
      rw [hT, if_pos rfl]
      show admits (.fieldEquals (dgRegIdx r) w) (baseInput s s') = .ok
      simp only [admits, baseInput, hgr]
      rw [if_pos h]
    · have hF : evalSimple (Simple.toExec (.fieldEquals r w))
          (encode s) (encode s') = false := by
        simp only [Simple.toExec, evalSimple, hval]
        simp only [beq_eq_false_iff_ne, ne_eq, Option.some.injEq]
        exact fun hcon => h (by exact_mod_cast hcon)
      rw [hF]
      simp only [Bool.false_eq_true, if_false]
      show admits (.fieldEquals (dgRegIdx r) w) (baseInput s s') = .violated
      simp only [admits, baseInput, hgr]
      rw [if_neg h]
  | fieldGte r w =>
    have hr : r ∈ registerNames := of_decide_eq_true hok
    obtain ⟨hidx, hval⟩ := resolve s' hr
    have hgr : getReg (dgSlots s') (dgRegIdx r)
        = some ((dgSlots s').getD (dgRegIdx r) 0) := by
      unfold getReg
      rw [if_neg (Nat.not_le.mpr hidx)]
    by_cases h : w ≤ (dgSlots s').getD (dgRegIdx r) 0
    · have hT : evalSimple (Simple.toExec (.fieldGte r w))
          (encode s) (encode s') = true := by
        simp only [Simple.toExec, evalSimple, hval]
        exact decide_eq_true (by exact_mod_cast h)
      rw [hT, if_pos rfl]
      show admits (.fieldGte (dgRegIdx r) w) (baseInput s s') = .ok
      simp only [admits, baseInput, hgr]
      rw [if_pos h]
    · have hF : evalSimple (Simple.toExec (.fieldGte r w))
          (encode s) (encode s') = false := by
        simp only [Simple.toExec, evalSimple, hval]
        exact decide_eq_false (fun hcon => h (by exact_mod_cast hcon))
      rw [hF]
      simp only [Bool.false_eq_true, if_false]
      show admits (.fieldGte (dgRegIdx r) w) (baseInput s s') = .violated
      simp only [admits, baseInput, hgr]
      rw [if_neg h]
  | fieldLte r w =>
    have hr : r ∈ registerNames := of_decide_eq_true hok
    obtain ⟨hidx, hval⟩ := resolve s' hr
    have hgr : getReg (dgSlots s') (dgRegIdx r)
        = some ((dgSlots s').getD (dgRegIdx r) 0) := by
      unfold getReg
      rw [if_neg (Nat.not_le.mpr hidx)]
    by_cases h : (dgSlots s').getD (dgRegIdx r) 0 ≤ w
    · have hT : evalSimple (Simple.toExec (.fieldLte r w))
          (encode s) (encode s') = true := by
        simp only [Simple.toExec, evalSimple, hval]
        exact decide_eq_true (by exact_mod_cast h)
      rw [hT, if_pos rfl]
      show admits (.fieldLte (dgRegIdx r) w) (baseInput s s') = .ok
      simp only [admits, baseInput, hgr]
      rw [if_pos h]
    · have hF : evalSimple (Simple.toExec (.fieldLte r w))
          (encode s) (encode s') = false := by
        simp only [Simple.toExec, evalSimple, hval]
        exact decide_eq_false (fun hcon => h (by exact_mod_cast hcon))
      rw [hF]
      simp only [Bool.false_eq_true, if_false]
      show admits (.fieldLte (dgRegIdx r) w) (baseInput s s') = .violated
      simp only [admits, baseInput, hgr]
      rw [if_neg h]
  | immutable r =>
    have hr : r ∈ registerNames := of_decide_eq_true hok
    obtain ⟨hidx, hvalO⟩ := resolve s hr
    obtain ⟨_, hvalN⟩ := resolve s' hr
    by_cases h : (dgSlots s').getD (dgRegIdx r) 0 = (dgSlots s).getD (dgRegIdx r) 0
    · have hT : evalSimple (Simple.toExec (.immutable r))
          (encode s) (encode s') = true := by
        simp only [Simple.toExec, evalSimple, hvalO, hvalN, h]
        exact beq_self_eq_true _
      rw [hT, if_pos rfl]
      show admits (.immutable (dgRegIdx r)) (baseInput s s') = .ok
      simp only [admits, baseInput]
      rw [if_neg (Nat.not_le.mpr hidx), if_true, if_pos h]
    · have hF : evalSimple (Simple.toExec (.immutable r))
          (encode s) (encode s') = false := by
        simp only [Simple.toExec, evalSimple, hvalO, hvalN]
        simp only [beq_eq_false_iff_ne, ne_eq, Option.some.injEq]
        exact fun hcon => h (by exact_mod_cast hcon)
      rw [hF]
      simp only [Bool.false_eq_true, if_false]
      show admits (.immutable (dgRegIdx r)) (baseInput s s') = .violated
      simp only [admits, baseInput]
      rw [if_neg (Nat.not_le.mpr hidx), if_true, if_neg h]
  | negate inner ih =>
    have hok' : simpleOK inner = true := hok
    have hih := ih hok'
    have hneg := branchAdmits_neg inner.toBranch.1 inner.toBranch.2 (baseInput s s')
    show branchAdmits (!inner.toBranch.1, inner.toBranch.2) (baseInput s s') = _
    rw [hneg]
    rw [show (inner.toBranch.1, inner.toBranch.2) = inner.toBranch from rfl]
    rw [hih]
    have hnot : evalSimple (Simple.toExec (.negate inner)) (encode s) (encode s')
        = !(evalSimple inner.toExec (encode s) (encode s')) := rfl
    rw [hnot]
    cases hE : evalSimple inner.toExec (encode s) (encode s') <;> simp [flipV]

private theorem anyOfGo_ok {i : DInput} :
    ∀ (bs : List (Bool × DConstraint)) (b : Bool × DConstraint), b ∈ bs →
      branchAdmits b i = .ok → ∀ last, anyOfGo bs i last = .ok := by
  intro bs
  induction bs with
  | nil => intro b hb; cases hb
  | cons hd tl ih =>
    intro b hb hok last
    rcases List.mem_cons.mp hb with rfl | htl
    · simp only [anyOfGo, hok]
    · cases hAdm : branchAdmits hd i <;>
        simp only [anyOfGo, hAdm] <;>
        first
          | rfl
          | exact ih b htl hok _

private theorem tr_anyOf {s s' : DState} {vs : List Simple}
    (hok : vs.all simpleOK = true)
    (hexec : evalConstraint (Constraint.anyOf vs).toExec
      (encode s) (encode s') = true) :
    admitsTop (.anyOf (vs.map Simple.toBranch)) (baseInput s s') = .ok := by
  have hex : vs.any (fun v => evalSimple v.toExec (encode s) (encode s')) = true := by
    simpa [Constraint.toExec, evalConstraint, List.any_map, Function.comp] using hexec
  obtain ⟨v, hvmem, hv⟩ := List.any_eq_true.mp hex
  have hbr := branch_agree (s := s) (s' := s') v (List.all_eq_true.mp hok v hvmem)
  rw [hv] at hbr
  simp only [ite_true] at hbr
  cases vs with
  | nil => cases hvmem
  | cons v0 rest =>
    simp only [List.map_cons, admitsTop]
    exact anyOfGo_ok _ _ (List.mem_map_of_mem (f := Simple.toBranch) hvmem) hbr _

/-! ### The heap atoms. -/

private theorem tr_heapField {s s' : DState} {k : HeapKeyRef} (hk : k ∈ keyList)
    (atom : HeapAtom)
    (hb : heapVal s k ≤ 9) (hb' : heapVal s' k ≤ 9)
    (hexec : evalConstraint (Constraint.heapField k atom).toExec
      (encode s) (encode s') = true) :
    admits (.heapField atom.toDHeap) (dgInput s s' (.heapField k atom)) = .ok := by
  have hvalO := resolveHeap s hk
  have hvalN := resolveHeap s' hk
  have hO : (dgInput s s' (.heapField k atom)).heapOld = some (heapVal s k) := rfl
  have hN : (dgInput s s' (.heapField k atom)).heapNew = some (heapVal s' k) := rfl
  have hred : admits (.heapField atom.toDHeap) (dgInput s s' (.heapField k atom))
      = heapAdmits atom.toDHeap (some (heapVal s k)) (some (heapVal s' k)) := by
    simp only [admits, hO, hN]
  rw [hred]
  cases atom with
  | equals v =>
    simp only [Constraint.toExec, HeapAtom.toExec, evalConstraint, evalSimple,
      hvalN] at hexec
    have hx : heapVal s' k = v := by
      have h := Option.some.inj (beq_iff_eq.mp hexec)
      exact_mod_cast h
    simp only [HeapAtom.toDHeap, heapAdmits]
    rw [if_pos hx]
  | immutable =>
    simp only [Constraint.toExec, HeapAtom.toExec, evalConstraint, evalSimple,
      hvalO, hvalN] at hexec
    have hx : heapVal s' k = heapVal s k := by
      have h := Option.some.inj (beq_iff_eq.mp hexec)
      exact_mod_cast h
    simp only [HeapAtom.toDHeap, heapAdmits]
    rw [if_pos (by rw [hx])]
  | monotonic =>
    simp only [Constraint.toExec, HeapAtom.toExec, evalConstraint, evalSimple,
      hvalO, hvalN] at hexec
    have hx : heapVal s k ≤ heapVal s' k := by
      have h := of_decide_eq_true hexec
      exact_mod_cast h
    simp only [HeapAtom.toDHeap, heapAdmits]
    rw [if_pos hx]
  | memberOf set =>
    have hexec' : Dregg2.Exec.evalSimple
        (.memberOf k.field (set.map (fun v => (v : Int))))
        (encode s) (encode s') = true := hexec
    obtain ⟨x, hxs, hxc⟩ :=
      (Dregg2.Exec.evalSimple_memberOf_iff _ _ _ _).mp hexec'
    rw [hvalN] at hxs
    have hxeq : x = ((heapVal s' k : Nat) : Int) := (Option.some.inj hxs).symm
    subst hxeq
    have hxmem : ((heapVal s' k : Nat) : Int) ∈ set.map (fun v => (v : Int)) :=
      List.contains_iff_mem.mp hxc
    have hmem : heapVal s' k ∈ set := mem_map_natcast hxmem
    have hlow : low64 (heapVal s' k) = heapVal s' k :=
      low64_small (le_trans hb' (by decide))
    simp only [HeapAtom.toDHeap, heapAdmits, hlow]
    rw [if_pos (List.contains_iff_mem.mpr hmem)]
  | deltaEquals d =>
    simp only [Constraint.toExec, HeapAtom.toExec, evalConstraint, evalSimple,
      hvalO, hvalN] at hexec
    have hx : ((heapVal s' k : Nat) : Int) = ((heapVal s k : Nat) : Int) + d :=
      Option.some.inj (beq_iff_eq.mp hexec)
    have hlO : low64 (heapVal s k) = heapVal s k :=
      low64_small (le_trans hb (by decide))
    have hlN : low64 (heapVal s' k) = heapVal s' k :=
      low64_small (le_trans hb' (by decide))
    simp only [HeapAtom.toDHeap, heapAdmits, hlO, hlN]
    rw [if_pos (by omega)]

/-! ## 6. The dispatcher: ONE transport theorem over the whole in-subset vocabulary. -/

/-- **The Int→Nat bridge, per tooth**: on the marshalled image of small (`Inv`+`Tight`)
states, Exec truth of any in-subset descent tooth transports to the DEPLOYED
evaluator's `.ok` verdict. -/
private theorem tooth_transport {s s' : DState}
    (hInv : Inv s) (hInv' : Inv s') (ht : Tight s) (ht' : Tight s')
    {c : Constraint} (hok : toothOK c = true) {dt : DTop}
    (hdt : Constraint.toDTop c = some dt)
    (hexec : evalConstraint c.toExec (encode s) (encode s') = true) :
    admitsTop dt (dgInput s s' c) = .ok := by
  cases c with
  | fieldEquals r v =>
    injection hdt with h; subst h
    exact tr_fieldEquals (of_decide_eq_true hok) v hexec
  | fieldGte r v =>
    injection hdt with h; subst h
    exact tr_fieldGte (of_decide_eq_true hok) v hexec
  | fieldLte r v =>
    injection hdt with h; subst h
    exact tr_fieldLte (of_decide_eq_true hok) v hexec
  | fieldDelta r d =>
    injection hdt with h; subst h
    simp only [toothOK, Bool.and_eq_true] at hok
    have hr := of_decide_eq_true hok.1
    exact tr_fieldDelta hr (of_decide_eq_true hok.2) (regs_small hInv ht hr) hexec
  | strictMonotonic r =>
    injection hdt with h; subst h
    exact tr_strictMonotonic (of_decide_eq_true hok) hexec
  | immutable r =>
    injection hdt with h; subst h
    exact tr_immutable (of_decide_eq_true hok) hexec
  | sumEquals rs v =>
    injection hdt with h; subst h
    simp only [toothOK, Bool.and_eq_true] at hok
    have hrs : ∀ r ∈ rs, r ∈ registerNames := fun r hr =>
      of_decide_eq_true (List.all_eq_true.mp hok.1 r hr)
    exact tr_sumEquals hrs (of_decide_eq_true hok.2)
      (fun r hr => regs_small hInv' ht' (hrs r hr)) hexec
  | affineLe ts cc =>
    injection hdt with h; subst h
    simp only [toothOK] at hok
    have hts : ∀ t ∈ ts, t.2 ∈ registerNames := fun t htm =>
      of_decide_eq_true (List.all_eq_true.mp hok t htm)
    exact tr_affineLe hts (fun t htm => regs_small hInv' ht' (hts t htm)) hexec
  | inRangeTwoSided r lo hi =>
    injection hdt with h; subst h
    have hr : r ∈ registerNames := of_decide_eq_true hok
    exact tr_inRangeTwoSided hr lo hi (regs_small hInv' ht' hr) hexec
  | allowedTransitions r al =>
    injection hdt with h; subst h
    exact tr_allowedTransitions (of_decide_eq_true hok) al hexec
  | anyOf vs =>
    injection hdt with h; subst h
    exact tr_anyOf hok hexec
  | heapField k atom =>
    injection hdt with h; subst h
    have hk : k ∈ keyList := of_decide_eq_true hok
    exact tr_heapField hk atom (heap_small hInv hk) (heap_small hInv' hk) hexec
  | countFieldsEq ks v r => simp [Constraint.toDTop] at hdt

/-! ## 7. THE FLAGSHIP — the descent's legal play lands on the DEPLOYED evaluator. -/

/-- **`descent_step_teeth_deployed` — the Int→Nat bridge, program-wide.** For every
receipt-reachable state and legal model step, EVERY in-subset tooth of EVERY matching
case (verb arm or `SlotChanged` rider) evaluates to `.ok` under
`Dregg2.Exec.DeployedConstraint.admitsTop` — the `@[export dregg_constraint_admits]`
evaluator the deployed node routes through — on the marshalled register/heap input.
The descent twin of tug's `program_admits_legal_play_deployed`, riding the
completeness ∀-weld (`reachable_step_admitted`) instead of a single driven run.
(`countFieldsEq` teeth have `toDTop = none` and are the §9 designed remainder;
guard dispatch remains executor-level, as in the tug refinement.) -/
theorem descent_step_teeth_deployed {s s' : DState} {m : Move}
    (hreach : Reachable s) (hstep : step s m = some s') :
    ∀ tc ∈ programCases,
      (Case.toExec tc).guard.matches (moveIdx m) (encode s) (encode s') = true →
      ∀ c ∈ tc.constraints, ∀ dt, Constraint.toDTop c = some dt →
        admitsTop dt (dgInput s s' c) = DAdmit.ok := by
  intro tc htc hmatch c hc dt hdt
  have hreach' : Reachable s' := reachable_step hreach hstep
  have hInv := inv_reachable hreach
  have hInv' := inv_reachable hreach'
  have ht := reachable_tight hreach
  have ht' := reachable_tight hreach'
  have hadm : Dregg2.Exec.RecordProgram.admits
      (.cases (programCases.map Case.toExec)) (moveIdx m)
      (encode s) (encode s') = true :=
    reachable_step_admitted hreach hstep
  have hexec : evalConstraint c.toExec (encode s) (encode s') = true :=
    admits_cases_mem hadm (List.mem_map_of_mem (f := Case.toExec) htc) hmatch
      c.toExec (List.mem_map_of_mem (f := Constraint.toExec) hc)
  have hok : toothOK c = true :=
    List.all_eq_true.mp (List.all_eq_true.mp programOK tc htc) c hc
  exact tooth_transport hInv hInv' ht ht' hok hdt hexec

/-! ### Per-law corollaries — the four core commons, each landing on the deployed
evaluator for EVERY verb (the cases each verb's method arm carries `coreTeeth`). -/

private def verbCase : Move → Case
  | .delve => delveCase | .unlock _ => unlockCase | .smite => smiteCase
  | .loot _ => lootCase | .flee => fleeCase

private theorem verbCase_mem (m : Move) : verbCase m ∈ programCases := by
  cases m <;> simp [verbCase, programCases]

private theorem verbCase_guard (m : Move) (o n : Value) :
    (Case.toExec (verbCase m)).guard.matches (moveIdx m) o n = true := by
  cases m <;> rfl

private theorem coreTeeth_mem_verbCase (m : Move) {c : Constraint}
    (hc : c ∈ coreTeeth) : c ∈ (verbCase m).constraints := by
  cases m <;>
    · simp only [verbCase, delveCase, unlockCase, smiteCase, lootCase, fleeCase,
        List.mem_append]
      tauto

/-- Conservation reaches the deployed referee: on every reachable legal step, the
deployed `SumEquals` tooth over the six zone slots admits the marshalled post-state. -/
theorem descent_conserves_deployed {s s' : DState} {m : Move}
    (hreach : Reachable s) (hstep : step s m = some s') :
    admitsTop (.base (.sumEquals [4, 5, 9, 10, 11, 12] 8))
      (dgInput s s' (.sumEquals zones RELICS)) = .ok :=
  descent_step_teeth_deployed hreach hstep (verbCase m) (verbCase_mem m)
    (verbCase_guard m _ _) _ (coreTeeth_mem_verbCase m (by simp [coreTeeth]))
    _ rfl

/-- Capacity attenuation reaches the deployed referee (`AffineLe` over pack+depth). -/
theorem descent_capacity_deployed {s s' : DState} {m : Move}
    (hreach : Reachable s) (hstep : step s m = some s') :
    admitsTop (.base (.affineLe [((1 : Int), 4), ((1 : Int), 0)] (8 : Int)))
      (dgInput s s' (.affineLe [((1 : Int), "pack"), ((1 : Int), "depth")] (CAP : Int)))
      = .ok :=
  descent_step_teeth_deployed hreach hstep (verbCase m) (verbCase_mem m)
    (verbCase_guard m _ _) _ (coreTeeth_mem_verbCase m (by simp [coreTeeth]))
    _ rfl

/-- The strictly-spending capped clock reaches the deployed referee (both teeth). -/
theorem descent_pays_deployed {s s' : DState} {m : Move}
    (hreach : Reachable s) (hstep : step s m = some s') :
    admitsTop (.base (.strictMonotonic 1))
        (dgInput s s' (.strictMonotonic "spent")) = .ok ∧
    admitsTop (.base (.fieldLte 1 26))
        (dgInput s s' (.fieldLte "spent" BREATH)) = .ok :=
  ⟨descent_step_teeth_deployed hreach hstep (verbCase m) (verbCase_mem m)
      (verbCase_guard m _ _) _ (coreTeeth_mem_verbCase m (by simp [coreTeeth])) _ rfl,
   descent_step_teeth_deployed hreach hstep (verbCase m) (verbCase_mem m)
      (verbCase_guard m _ _) _ (coreTeeth_mem_verbCase m (by simp [coreTeeth])) _ rfl⟩

/-- The aliveness/banking fate law reaches the deployed referee. -/
theorem descent_alive_deployed {s s' : DState} {m : Move}
    (hreach : Reachable s) (hstep : step s m = some s') :
    admitsTop (.base (.allowedTransitions 3 [(0, 0), (0, 1)]))
      (dgInput s s' (.allowedTransitions "fate" [(0, 0), (0, 1)])) = .ok :=
  descent_step_teeth_deployed hreach hstep (verbCase m) (verbCase_mem m)
    (verbCase_guard m _ _) _ (coreTeeth_mem_verbCase m (by simp [coreTeeth]))
    _ rfl

/-! ## 8. The INVERSIONS at deployed width — over ARBITRARY unsigned inputs.

`DungeonProgram §4`'s inversions quantify over arbitrary signed `Exec.Value`s; the
audit's honest bound was that they cannot be re-stated over `DeployedConstraint` for
arbitrary values because of the signed/unsigned divergence. These four theorems are
the RE-BASED inversions: stated DIRECTLY over `DeployedConstraint.admits`, quantifying
over arbitrary `DInput`s — attacker-supplied unsigned 256-bit register files. On the
deployed substrate the divergence is out of scope BY TYPE, so no caveat remains: if
the exported evaluator admits the tooth, the law holds on the deployed lanes. -/

private theorem sumGo_inv (v : DField) (regs : List DField) :
    ∀ (l : List Nat) (acc : Nat),
      sumEqualsAdmit.go v regs l acc = .ok →
      acc + (l.map (fun i => low64 (regs.getD i 0))).sum = low64 v := by
  intro l
  induction l with
  | nil =>
    intro acc h
    unfold sumEqualsAdmit.go at h
    simp only [List.map_nil, List.sum_nil, Nat.add_zero]
    by_cases hc : acc = low64 v
    · exact hc
    · rw [if_neg hc] at h; cases h
  | cons i rest ih =>
    intro acc h
    unfold sumEqualsAdmit.go at h
    by_cases hi : i ≥ stateSlots
    · rw [if_pos hi] at h; cases h
    · rw [if_neg hi] at h
      simp only at h
      by_cases hov : acc + low64 (regs.getD i 0) ≥ two64
      · rw [if_pos hov] at h; cases h
      · rw [if_neg hov] at h
        have := ih _ h
        simp only [List.map_cons, List.sum_cons]
        omega

/-- **Conservation inversion at deployed width**: ANY input the deployed `SumEquals`
zone tooth admits has its six zone lanes summing to exactly `RELICS` — whatever the
(unsigned 256-bit) writes were. -/
theorem deployed_tooth_conserves (i : DInput)
    (h : admits (.sumEquals [4, 5, 9, 10, 11, 12] 8) i = .ok) :
    ([4, 5, 9, 10, 11, 12].map (fun k => low64 (i.newRegs.getD k 0))).sum = RELICS := by
  simp only [admits, sumEqualsAdmit] at h
  have := sumGo_inv 8 i.newRegs [4, 5, 9, 10, 11, 12] 0 h
  simpa using this

/-- **Capacity inversion at deployed width**: ANY input the deployed `AffineLe`
capacity tooth admits satisfies `pack-lane + depth-lane ≤ CAP`. -/
theorem deployed_tooth_capacity (i : DInput)
    (h : admits (.affineLe [((1 : Int), 4), ((1 : Int), 0)] (8 : Int)) i = .ok) :
    low64 (i.newRegs.getD 4 0) + low64 (i.newRegs.getD 0 0) ≤ CAP := by
  simp only [admits, Dregg2.Exec.DeployedConstraint.affineSum] at h
  rw [if_neg (by decide : ¬ (4 : Nat) ≥ stateSlots),
      if_neg (by decide : ¬ (0 : Nat) ≥ stateSlots)] at h
  simp only at h
  by_cases hgt : (1 : Int) * (low64 (i.newRegs.getD 4 0) : Int)
      + ((1 : Int) * (low64 (i.newRegs.getD 0 0) : Int) + 0) > 8
  · rw [if_pos hgt] at h; cases h
  · have : (low64 (i.newRegs.getD 4 0) : Int) + (low64 (i.newRegs.getD 0 0) : Int) ≤ 8 := by
      omega
    show low64 (i.newRegs.getD 4 0) + low64 (i.newRegs.getD 0 0) ≤ 8
    exact_mod_cast this

/-- **Clock inversion at deployed width**: ANY input the deployed strict-monotone +
cap teeth admit strictly increases the spent register and stays at most `BREATH`
(full 256-bit compares — no lane truncation on this pair). -/
theorem deployed_tooth_pays (i : DInput) (hold : i.oldPresent = true)
    (hs : admits (.strictMonotonic 1) i = .ok)
    (hl : admits (.fieldLte 1 26) i = .ok) :
    i.oldRegs.getD 1 0 < i.newRegs.getD 1 0 ∧ i.newRegs.getD 1 0 ≤ BREATH := by
  constructor
  · simp only [admits] at hs
    rw [if_neg (by decide : ¬ (1 : Nat) ≥ stateSlots), if_pos (by simp [hold])] at hs
    by_cases hlt : i.oldRegs.getD 1 0 < i.newRegs.getD 1 0
    · exact hlt
    · rw [if_neg hlt] at hs; cases hs
  · simp only [admits, getReg] at hl
    rw [if_neg (by decide : ¬ (1 : Nat) ≥ stateSlots)] at hl
    simp only at hl
    by_cases hle : i.newRegs.getD 1 0 ≤ 26
    · exact hle
    · rw [if_neg hle] at hl; cases hl

/-- **Aliveness inversion at deployed width**: ANY input the deployed fate
state-machine tooth admits started from `fate = 0` and lands on `0` or `1`. -/
theorem deployed_tooth_alive (i : DInput) (hold : i.oldPresent = true)
    (h : admits (.allowedTransitions 3 [(0, 0), (0, 1)]) i = .ok) :
    i.oldRegs.getD 3 0 = 0 ∧
      (i.newRegs.getD 3 0 = 0 ∨ i.newRegs.getD 3 0 = 1) := by
  simp only [admits, hold] at h
  rw [if_neg (by decide : ¬ (3 : Nat) ≥ stateSlots)] at h
  rw [if_true] at h
  by_cases hany : ([((0 : DField), (0 : DField)), (0, 1)].any
      (fun p => p.1 == i.oldRegs.getD 3 0 && p.2 == i.newRegs.getD 3 0)) = true
  · obtain ⟨p, hpmem, hp⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpmem
    rcases hpmem with rfl | rfl
    · exact ⟨hp.1.symm, Or.inl hp.2.symm⟩
    · exact ⟨hp.1.symm, Or.inr hp.2.symm⟩
  · rw [if_neg (by simpa using hany)] at h; cases h

/-! ### The teeth BITE (negative twins — refusals at deployed width, kernel-checked). -/

private def regs0 : List DField := List.replicate 16 0

private def mkI (oldR newR : List DField) : DInput :=
  { oldPresent := true, newNonce := 0, oldRegs := oldR, newRegs := newR,
    heapOld := none, heapNew := none, heapOther := none,
    oldBalance := 0, newBalance := 0, ctx := noCtx, cells := [] }

-- Conservation: a dupe (zone lanes summing to 9) is REFUSED; an honest 8 admits.
#guard admits (.sumEquals [4, 5, 9, 10, 11, 12] 8)
  (mkI regs0 [1, 4, 1, 0, 2, 0, 0, 0, 0, 2, 2, 2, 1, 0, 0, 0]) = DAdmit.violated
#guard admits (.sumEquals [4, 5, 9, 10, 11, 12] 8)
  (mkI regs0 [1, 4, 1, 0, 1, 0, 0, 0, 0, 2, 2, 2, 1, 0, 0, 0]) = DAdmit.ok

-- Capacity: pack 8 at depth 1 is REFUSED; 4 at 4 admits.
#guard admits (.affineLe [((1 : Int), 4), ((1 : Int), 0)] (8 : Int))
  (mkI regs0 [1, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) = DAdmit.violated
#guard admits (.affineLe [((1 : Int), 4), ((1 : Int), 0)] (8 : Int))
  (mkI regs0 [4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) = DAdmit.ok

-- The clock: a free turn (spent unchanged) is REFUSED; an over-cap clock is REFUSED.
#guard admits (.strictMonotonic 1)
  (mkI [0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
       [0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) = DAdmit.violated
#guard admits (.fieldLte 1 26)
  (mkI regs0 [0, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) = DAdmit.violated

-- Fate: moving from the banked tomb (old fate 1) is REFUSED; a forged fate 2 is REFUSED.
#guard admits (.allowedTransitions 3 [(0, 0), (0, 1)])
  (mkI [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] regs0) = DAdmit.violated
#guard admits (.allowedTransitions 3 [(0, 0), (0, 1)])
  (mkI regs0 [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) = DAdmit.violated

-- A way rider's transition tooth: re-flipping an open way (1 → 1) is REFUSED.
#guard admits (.allowedTransitions 6 [(0, 1)])
  (mkI [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
       [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) = DAdmit.violated

-- The key-exhibit tooth: a heap key NOT carried refuses at deployed width.
#guard heapAdmits (DHeapAtom.equals 8) (some 1) (some 1) = DAdmit.violated
#guard heapAdmits (DHeapAtom.equals 8) (some 1) (some 8) = DAdmit.ok

-- The anyOf lowering bites: the delve way-tooth image refuses a keyless descent
-- (depth 2 with way_2 shut) and admits the same state with way_2 open.
private def wayTooth2Image : DTop :=
  .anyOf [(true, .fieldEquals 0 2), (false, .fieldGte 6 1)]
private theorem wayTooth2_image_pin :
    Constraint.toDTop (wayTooth 2) = some wayTooth2Image := rfl
#guard admitsTop wayTooth2Image
  (mkI regs0 [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) = DAdmit.violated
#guard admitsTop wayTooth2Image
  (mkI regs0 [2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) = DAdmit.ok

/-! ### The flagship's executable twin — an honest crowned-run step, marshalled, has
EVERY in-subset tooth of its verb case AND its spent rider admitted (kernel-checked);
the same battery under a mutated register allocation would fail (the pins above and
the negative twins hold the mapping honest). -/

section CanonStep
local instance : WorldParam := instAt 0

#guard
  (let s := st [.delve]
   let s' := st [.delve, .smite]
   (smiteCase.constraints ++ spentRider.constraints).all fun c =>
     match Constraint.toDTop c with
     | some dt => decide (admitsTop dt (dgInput s s' c) = DAdmit.ok)
     | none => true)

end CanonStep

/-! ## 9. THE DESIGNED REMAINDER — the `countFieldsEq` census teeth (NOT fired).

**The gap.** The six `projectionTeeth` (`countFieldsEq relicKeys v reg` — the exact
object↔projection census binding `pack`/`bank`/each hoard to the eight custody keys)
lower to Rust `StateConstraint::FieldsCountEquals` (`cell/src/program/eval.rs:1990`),
which `exec-lean/src/constraint_oracle.rs` enumerates in the NAMED trusted-Rust slot
("heap SHAPES not yet on the wire"). `Constraint.toDTop` is `none` on exactly this
constructor — the partition is total and kernel-checked (`census_is_the_remainder`).

**The falsifier (the gap BITES).** The two-relic/one-counter census forgery of
`DungeonProgram` attack 1b, marshalled to the deployed substrate: one hoard unit
debited, `pack += 1`, but TWO custody objects advanced to `CARRIED`. The battery below
proves EVERY in-subset tooth of the spent rider admits this forged transition at
deployed width — conservation, capacity, ranges, both per-object ratchets, the
sentinel freeze ALL pass. Only the census teeth refuse it, and they are evaluated in
trusted Rust. (The Exec-level mutation canary `dungeonExecWithoutProjection` in
`DungeonProgram.lean` already proves the census tooth is the indispensable refusal —
deleting exactly `projectionTeeth` makes the forgery admit.) So the deployed
LEAN-EVALUATED subset alone does NOT refuse the census forgery: the extension is
load-bearing.

**The extension design (ember-gated; NOT fired by this lane).**
Closing this tooth requires extending `Dregg2.Exec.DeployedConstraint`'s exported
subset — deployed admission logic:

1. `DInput` grows a MULTI-KEY heap read (a resolved cell run) — the marshaller
   resolves the N named `fields_map` keys post-state, each absence a first-class
   token (fail-closed, mirroring `get_field_ext` returning `None` ⇒
   `ConstraintViolated` at `eval.rs:1999`).
2. `DConstraint` grows `fieldsCountEquals (n : Nat) (value : DField) (countIdx : Nat)`:
   count FULL-FIELD equality of the first `n` resolved keys against `value` (any
   absent key ⇒ `.violated`), compare the count against the `field_from_u64` image
   in `newRegs.getD countIdx 0`.
3. The wire codec grows one tag, and `constraint_oracle.rs::encode_constraint` moves
   `FieldsCountEquals` from the trusted-Rust enumeration to the encoded subset,
   resolving the N keys exactly as the single-key `HeapField` marshalling does.
4. Acceptance: the differential gate (Lean == Rust across the subset) re-run with the
   census arm included, plus this file's forged battery flipping from all-`.ok` to
   census-`.violated` at deployed width.

⚑ STATUS AT AUTHORING TIME: a CONCURRENT lane's working-tree WIP on
`DeployedConstraint.lean` landed points 1–3 almost verbatim
(`DConstraint.fieldsCountEquals` + `DInput.cells` + the `FCE` tag). This module
compiles against that WIP's widened structures but deliberately does NOT lower
`countFieldsEq` onto the uncommitted arm: the census LOWERING + TRANSPORT (extend
`toDTop`, marshal the 8-key cells run in `dgInput`, prove the transport with the same
pattern as `tr_heapField` — mechanical, all values ≤ 9 and counts ≤ 8) is the named
follow-up once the widening commits and its differential gate is green.

Until then, the honest statement is: the census law is enforced by the deployed node
(Rust `eval.rs`, exercised by the executor tests and the Exec-level inversions), but
it is OUTSIDE what this bridge proves about the Lean-evaluated reality-gated subset. -/

/-- The partition is EXACT: a descent tooth lowers to the deployed subset IFF it is
not a census tooth (kernel-checked over the whole authored program). -/
private theorem census_is_the_remainder :
    (programCases.all fun tc => tc.constraints.all fun c =>
      (Constraint.toDTop c).isSome
        == !(match c with | .countFieldsEq _ _ _ => true | _ => false)) = true := by
  rfl

-- The spent rider carries exactly six out-of-subset teeth: the census — on EVERY day of
-- the drawn family (the remainder is a fact about the tooth SHAPES, not the map).
#guard (List.range dayCount).all (fun k =>
  ((@spentRider (instAt k)).constraints.filter fun c => (Constraint.toDTop c).isNone).length == 6)
#guard projectionTeeth.all fun c => (Constraint.toDTop c).isNone

/-! ### The forged census transition, marshalled (attack 1b at deployed width). -/

/-- Old registers: `st [.delve, .smite]` marshalled —
depth 1, spent 3, wounds 1, hoards (3, 2, 2, 1). -/
private def censusOldRegs : List DField :=
  [1, 3, 1, 0, 0, 0, 0, 0, 0, 3, 2, 2, 1, 0, 0, 0]

/-- Forged new registers: `pack := 1`, `hoard_1 := 2` (ONE debit), `spent := 4` —
conservation and capacity hold, but TWO custody objects advance below. -/
private def censusNewRegs : List DField :=
  [1, 4, 1, 0, 1, 0, 0, 0, 0, 2, 2, 2, 1, 0, 0, 0]

private def relicIdxOf (nm : String) : Nat :=
  (((List.range RELICS).find? fun i => relicName i == nm)).getD 0

/-- The forged OLD heap: every relic at its minted home, sentinel committed. -/
private def censusHeapOld : HeapKeyRef → DField
  | .sentinel => 1
  | .named nm => homeCode (relicIdxOf nm)

/-- The forged NEW heap: relics 1 AND 4 both advanced to `CARRIED` behind the single
`pack += 1` receipt (the census forgery). -/
private def censusHeapNew : HeapKeyRef → DField
  | .sentinel => 1
  | .named nm =>
      let i := relicIdxOf nm
      if i = 1 ∨ i = 4 then CARRIED else homeCode i

private def censusInput : Constraint → DInput
  | .heapField k _ =>
      { mkI censusOldRegs censusNewRegs with
          heapOld := some (censusHeapOld k), heapNew := some (censusHeapNew k) }
  | _ => mkI censusOldRegs censusNewRegs

-- ⚑ THE FALSIFIER: every in-subset tooth of the spent rider ADMITS the census
-- forgery at deployed width. The refusal lives ONLY in the out-of-subset census teeth
-- (trusted Rust) — the load-bearing gap the §9 extension design closes.
section CanonCensus
local instance : WorldParam := instAt 0

#guard
  spentRider.constraints.all fun c =>
    match Constraint.toDTop c with
    | some dt => decide (admitsTop dt (censusInput c) = DAdmit.ok)
    | none => true

end CanonCensus

/-! ## 10. Axiom hygiene — every bridge theorem on the standard kernel triple. -/

#assert_axioms descent_step_teeth_deployed
#assert_axioms descent_conserves_deployed
#assert_axioms descent_capacity_deployed
#assert_axioms descent_pays_deployed
#assert_axioms descent_alive_deployed
#assert_axioms deployed_tooth_conserves
#assert_axioms deployed_tooth_capacity
#assert_axioms deployed_tooth_pays
#assert_axioms deployed_tooth_alive
#assert_axioms wayTooth2_image_pin

end Dregg2.Games.Dungeon.Prog
