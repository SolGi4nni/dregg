/-
# Dregg2.Circuit.Emit.PredicatesRelationalCompoundRefine — the RUNG-1 functional-correctness
refinement for the emitted `predicates-relational-compound` descriptors
(`compoundPredicateDesc`, `relationalPredicateDesc`).

## What this file IS

`PredicatesRelationalCompoundEmit.lean` byte-pins the two descriptors and proves only PER-GATE
faithfulness lemmas (`binBody_zero_iff`, `atLeastOne_zero_iff`, `high_bit_gate_zero_iff` — each
gate poly = 0 ↔ its LOCAL relation). This file proves the missing WHOLE-DESCRIPTOR bridges: a trace
SATISFYING each emitted descriptor (via the deployed acceptance predicate `Satisfied2`) computes the
GENUINE semantic relation the circuit is meant to compute.

## The NO_LEAN case — we author the functional spec, then prove the refinement

The census names `PrivatePredicate.lean` as a SEMANTIC MODEL of relations-over-committed-values, but
it is a higher-level interface model (Pedersen-homomorphic conservation + a witnessed-range oracle),
NOT a faithful model of THESE hand-AIR descriptors (which use Poseidon2 commitments, a boolean gate
tree, and a witnessed integer difference). So — as for the sibling `PredicatesArithmeticRefine.lean` —
we AUTHOR the missing functional specs (`CompoundClassified`, `RelClassified`) and prove the emitted
descriptors REFINE them (SAT_IMPLIES_SEM, the load-bearing soundness direction).

### COMPOUND — the boolean composition (§1–§6)

`CompoundClassified (envAt t 0)`: on the boundary/active row `0` of any accepting compound trace,
every sub-predicate result, operator selector, `composed_result` and `gate_output` wire is BOOLEAN,
at least one operator is selected, and the composed result is the operator-selected boolean
combination of the operands — in particular for the NOT operator `composed_result = 1 − sub_result_0`
(the genuine boolean negation, fully in-circuit), for AND/Threshold `= and_intermediate`, for OR
`= 1 − and_intermediate`, for Custom `= gate_output` — and each sub-proof commitment binds its
PI-published `expected_commitment`. Consumes all 40 constraints of `compoundPredicateDesc`.

Honest scope: AND/OR/Threshold route the composed bit through the prover-supplied intermediate
`and_intermediate` (the compound AIR does NOT re-derive it in-circuit — it is hashed off-circuit in the
witness generator, exactly as `compound.rs` documents). So the fully-in-circuit boolean law is the NOT
gate; the AND/OR/Threshold laws are the descriptor's relation between the composed bit and the
prover's intermediate. This is the faithful reading of what the emitted gates force.

### RELATIONAL — the committed-value comparison (§7–§10)

`RelClassified hash (envAt t 0)`: on the active row `0` of any accepting relational trace, against the
NAMED Poseidon2 chip-table-soundness carrier `ChipTableSound`, the public commitments are Poseidon2
OPENINGS of the private values (`pub 0 = hash [value_a, blinding_a]`, `pub 1 = hash [value_b,
blinding_b]` — the "relation over committed values" content, via `chip_lookup_sound`), the asserted
result bit is TRUE (`= pub 2 = 1`), EXACTLY ONE of the {range, eq, neq} comparison relations is
selected (each flag boolean), and the selected relation holds on the private difference witness
(`eq ⇒ diff = 0`; `neq ⇒ diff ≠ 0`, via the witnessed inverse; `range ⇒` the top diff bit clears +
the bits recompose `diff`). The hypothesis is the WHOLE 47-constraint `Satisfied2` of
`relationalPredicateDesc`; the semantic relation is derived from its comparison / commitment-opening /
flag-selection gates (the two chip lookups, the result / flag / commitment gates, the range recompose /
high-bit and eq / neq comparison gates), with the auxiliary teeth — the 30 per-bit binariness gates, the
`AtLeastOne` selector, the `commit_verify` / `zero_pad` gates — carried in the hypothesis.

Honest scope: the hand AIR leaves `diff` a free witness (it is NOT tied to `value_a − value_b` in the
descriptor — the values enter ONLY through the two Poseidon2 commitment lookups), so we conclude the
selected relation on `diff` and the openings on the commitments, NOT a `value_a <op> value_b` claim.
This is exactly the faithful reading of the emitted constraints.

## The named carrier

The relational commitment-opening concludes only against a FAITHFUL Poseidon2 chip table. That
faithfulness enters as the explicit hypothesis `hChip : ChipTableSound hash (t.tf .poseidon2)` — the
same carrier `DescriptorIR2.chip_lookup_sound` names. The compound bridge consumes NO crypto carrier.

## Non-vacuity (the anti-scar)

Each bridge is fed a CONCRETE satisfying trace (`compoundWitness` computes NOT of `1` = `0`;
`relWitness` a committed EQ proof) that PROVABLY `Satisfied2`; a concrete FAILING trace
(`compoundBad` sets `composed = 1` under NOT of `1`; `relBad` sets `diff = 1` under EQ) PROVABLY
FAILS `Satisfied2` — the operator / relation gate is exactly what rejects it. So each `Satisfied2`
hypothesis is genuinely inhabited AND constraining.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters the relational
bridge ONLY through the named `ChipTableSound` carrier. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.PredicatesRelationalCompoundEmit
import Dregg2.Circuit.DecideSatisfied2

namespace Dregg2.Circuit.Emit.PredicatesRelationalCompoundRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmConstraint VmRowEnv holdsVm_gate_false holdsVm_piFirst_true)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.PredicatesRelationalCompoundEmit

set_option autoImplicit false
set_option maxRecDepth 8000

/-! ## §1 — The authored functional spec for the COMPOUND predicate. -/

/-- **`CompoundClassified env`** — the semantic relation the compound (AND/OR/NOT/Threshold/Custom)
predicate is meant to compute on one boundary row, over the ℤ field model. -/
structure CompoundClassified (env : VmRowEnv) : Prop where
  /-- Every sub-predicate result is a genuine boolean. -/
  subBool       : ∀ j, j < 8 → env.loc j = 0 ∨ env.loc j = 1
  opAndBool     : env.loc OP_AND = 0 ∨ env.loc OP_AND = 1
  opOrBool      : env.loc OP_OR = 0 ∨ env.loc OP_OR = 1
  opNotBool     : env.loc OP_NOT = 0 ∨ env.loc OP_NOT = 1
  opThrBool     : env.loc OP_THRESHOLD = 0 ∨ env.loc OP_THRESHOLD = 1
  opCustBool    : env.loc OP_CUSTOM = 0 ∨ env.loc OP_CUSTOM = 1
  /-- At least one composition operator is selected. -/
  atLeastOneOp  : env.loc OP_AND = 1 ∨ env.loc OP_OR = 1 ∨ env.loc OP_NOT = 1
                    ∨ env.loc OP_THRESHOLD = 1 ∨ env.loc OP_CUSTOM = 1
  composedBool  : env.loc COMPOSED = 0 ∨ env.loc COMPOSED = 1
  gateOutBool   : env.loc GATE_OUT = 0 ∨ env.loc GATE_OUT = 1
  /-- AND: the composed bit is the prover intermediate (`and_intermediate`). -/
  andLaw        : env.loc OP_AND = 1 → env.loc COMPOSED = env.loc AND_INT
  /-- OR: the composed bit is the boolean complement of the intermediate. -/
  orLaw         : env.loc OP_OR = 1 → env.loc COMPOSED = 1 - env.loc AND_INT
  /-- NOT: the composed bit is the genuine boolean negation of `sub_result_0` (fully in-circuit). -/
  notLaw        : env.loc OP_NOT = 1 → env.loc COMPOSED = 1 - env.loc 0
  /-- Threshold: the composed bit is the prover threshold intermediate. -/
  thrLaw        : env.loc OP_THRESHOLD = 1 → env.loc COMPOSED = env.loc AND_INT
  /-- Custom: the composed bit is the prover custom-gate output. -/
  custLaw       : env.loc OP_CUSTOM = 1 → env.loc COMPOSED = env.loc GATE_OUT
  /-- Each sub-proof commitment equals its expected commitment. -/
  commitBinds   : ∀ j, j < 8 → env.loc (SUBCOMMIT0 + j) = env.loc (EXPCOMMIT0 + j)
  /-- The composed result is pinned to the published `pi[0]`. -/
  composedPin   : env.loc COMPOSED = env.pub 0
  treeHashPin   : env.loc TREE_HASH = env.pub 1
  thresholdKPin : env.loc THRESHOLD_K = env.pub 2
  /-- Each expected commitment is pinned to its published `pi[3+j]`. -/
  expCommitPins : ∀ j, j < 8 → env.loc (EXPCOMMIT0 + j) = env.pub (3 + j)

/-! ## §2 — The constraints of `compoundPredicateDesc` are genuinely present (membership nav). -/

theorem cmem_sub (j : Nat) (hj : j < 8) : gate (binBody j) ∈ compoundPredicateDesc.constraints := by
  show gate (binBody j) ∈ compoundConstraints
  unfold compoundConstraints
  iterate 12 apply List.mem_append_left
  exact List.mem_map_of_mem (List.mem_range.mpr hj)

theorem cmem_opAnd : gate (binBody OP_AND) ∈ compoundPredicateDesc.constraints := by
  show gate (binBody OP_AND) ∈ compoundConstraints
  unfold compoundConstraints
  iterate 11 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem cmem_opOr : gate (binBody OP_OR) ∈ compoundPredicateDesc.constraints := by
  show gate (binBody OP_OR) ∈ compoundConstraints
  unfold compoundConstraints
  iterate 11 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem cmem_opNot : gate (binBody OP_NOT) ∈ compoundPredicateDesc.constraints := by
  show gate (binBody OP_NOT) ∈ compoundConstraints
  unfold compoundConstraints
  iterate 11 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem cmem_opThr : gate (binBody OP_THRESHOLD) ∈ compoundPredicateDesc.constraints := by
  show gate (binBody OP_THRESHOLD) ∈ compoundConstraints
  unfold compoundConstraints
  iterate 11 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem cmem_opCust : gate (binBody OP_CUSTOM) ∈ compoundPredicateDesc.constraints := by
  show gate (binBody OP_CUSTOM) ∈ compoundConstraints
  unfold compoundConstraints
  iterate 11 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem cmem_atLeast :
    gate (atLeastOne [OP_AND, OP_OR, OP_NOT, OP_THRESHOLD, OP_CUSTOM])
      ∈ compoundPredicateDesc.constraints := by
  show _ ∈ compoundConstraints
  unfold compoundConstraints
  iterate 10 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem cmem_composedBin : gate (binBody COMPOSED) ∈ compoundPredicateDesc.constraints := by
  show _ ∈ compoundConstraints
  unfold compoundConstraints
  iterate 9 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem cmem_and :
    gate (.mul (.var OP_AND) (subV (.var COMPOSED) AND_INT)) ∈ compoundPredicateDesc.constraints := by
  show _ ∈ compoundConstraints
  unfold compoundConstraints
  iterate 8 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem cmem_or :
    gate (.mul (.var OP_OR) (sumE [.var COMPOSED, .var AND_INT, .const (-1)]))
      ∈ compoundPredicateDesc.constraints := by
  show _ ∈ compoundConstraints
  unfold compoundConstraints
  iterate 7 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem cmem_not :
    gate (.mul (.var OP_NOT) (sumE [.var COMPOSED, .var 0, .const (-1)]))
      ∈ compoundPredicateDesc.constraints := by
  show _ ∈ compoundConstraints
  unfold compoundConstraints
  iterate 6 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem cmem_thr :
    gate (.mul (.var OP_THRESHOLD) (subV (.var COMPOSED) AND_INT))
      ∈ compoundPredicateDesc.constraints := by
  show _ ∈ compoundConstraints
  unfold compoundConstraints
  iterate 5 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem cmem_cust :
    gate (.mul (.var OP_CUSTOM) (subV (.var COMPOSED) GATE_OUT))
      ∈ compoundPredicateDesc.constraints := by
  show _ ∈ compoundConstraints
  unfold compoundConstraints
  iterate 4 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem cmem_gateOutBin : gate (binBody GATE_OUT) ∈ compoundPredicateDesc.constraints := by
  show _ ∈ compoundConstraints
  unfold compoundConstraints
  iterate 3 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem cmem_commit (j : Nat) (hj : j < 8) :
    gate (subV (.var (SUBCOMMIT0 + j)) (EXPCOMMIT0 + j)) ∈ compoundPredicateDesc.constraints := by
  show _ ∈ compoundConstraints
  unfold compoundConstraints
  iterate 2 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map_of_mem (List.mem_range.mpr hj)

theorem cmem_piComposed : piFirst COMPOSED 0 ∈ compoundPredicateDesc.constraints := by
  show _ ∈ compoundConstraints
  unfold compoundConstraints
  apply List.mem_append_left
  apply List.mem_append_right; simp

theorem cmem_piTree : piFirst TREE_HASH 1 ∈ compoundPredicateDesc.constraints := by
  show _ ∈ compoundConstraints
  unfold compoundConstraints
  apply List.mem_append_left
  apply List.mem_append_right; simp

theorem cmem_piThr : piFirst THRESHOLD_K 2 ∈ compoundPredicateDesc.constraints := by
  show _ ∈ compoundConstraints
  unfold compoundConstraints
  apply List.mem_append_left
  apply List.mem_append_right; simp

theorem cmem_piExp (j : Nat) (hj : j < 8) :
    piFirst (EXPCOMMIT0 + j) (3 + j) ∈ compoundPredicateDesc.constraints := by
  show _ ∈ compoundConstraints
  unfold compoundConstraints
  apply List.mem_append_right
  exact List.mem_map_of_mem (List.mem_range.mpr hj)

/-! ## §3 — empty mem/map logs (the compound descriptor is pure gates + PI pins). -/

theorem cmemOpsOf : memOpsOf compoundPredicateDesc = [] := by rfl

theorem cmapOpsOf : mapOpsOf compoundPredicateDesc = [] := by rfl

theorem cmemLog (t : VmTrace) : memLog compoundPredicateDesc t = [] := by
  simp [memLog, cmemOpsOf]

theorem cmapLog (t : VmTrace) : mapLog compoundPredicateDesc t = [] := by
  simp [mapLog, cmapOpsOf]

/-! ## §4 — THE COMPOUND WHOLE-DESCRIPTOR BRIDGE (SAT_IMPLIES_SEM). -/

/-- **`compound_sat_imp_sem` — the Rung-1 functional-correctness refinement for the compound
predicate.** A trace satisfying the emitted `compoundPredicateDesc`, padded to height `≥ 2` (the
always-present power-of-two padding, so row `0` is an active transition row where the `.gate` teeth
fire and the `.piBinding first` pins fire), computes the GENUINE boolean composition on its boundary
row `0`. -/
theorem compound_sat_imp_sem {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hlen : 2 ≤ t.rows.length)
    (hsat : Satisfied2 hash compoundPredicateDesc minit mfin maddrs t) :
    CompoundClassified (envAt t 0) := by
  have h0 : 0 < t.rows.length := by omega
  have hF : ((0 : Nat) == 0) = true := rfl
  have hL : ((0 : Nat) + 1 == t.rows.length) = false := by
    have : (0 : Nat) + 1 ≠ t.rows.length := by omega
    simpa using this
  -- a gate constraint forces its body to vanish on the active row 0.
  have gforce : ∀ b : EmittedExpr, gate b ∈ compoundPredicateDesc.constraints →
      b.eval (envAt t 0).loc = 0 := by
    intro b hb
    have h := hsat.rowConstraints 0 h0 (gate b) hb
    rw [hL] at h
    simpa only [gate, VmConstraint2.holdsAt, holdsVm_gate_false] using h
  -- a first-row PI pin fires on row 0.
  have pforce : ∀ col k : Nat, piFirst col k ∈ compoundPredicateDesc.constraints →
      (envAt t 0).loc col = (envAt t 0).pub k := by
    intro col k hb
    have h := hsat.rowConstraints 0 h0 (piFirst col k) hb
    rw [hF] at h
    simpa only [piFirst, VmConstraint2.holdsAt, holdsVm_piFirst_true] using h
  refine
    { subBool := ?_, opAndBool := ?_, opOrBool := ?_, opNotBool := ?_, opThrBool := ?_,
      opCustBool := ?_, atLeastOneOp := ?_, composedBool := ?_, gateOutBool := ?_,
      andLaw := ?_, orLaw := ?_, notLaw := ?_, thrLaw := ?_, custLaw := ?_,
      commitBinds := ?_, composedPin := ?_, treeHashPin := ?_, thresholdKPin := ?_,
      expCommitPins := ?_ }
  · intro j hj; exact (binBody_zero_iff _ j).mp (gforce _ (cmem_sub j hj))
  · exact (binBody_zero_iff _ OP_AND).mp (gforce _ cmem_opAnd)
  · exact (binBody_zero_iff _ OP_OR).mp (gforce _ cmem_opOr)
  · exact (binBody_zero_iff _ OP_NOT).mp (gforce _ cmem_opNot)
  · exact (binBody_zero_iff _ OP_THRESHOLD).mp (gforce _ cmem_opThr)
  · exact (binBody_zero_iff _ OP_CUSTOM).mp (gforce _ cmem_opCust)
  · -- at-least-one: the degree-5 product vanishes, so some (1 − op_i) = 0.
    have h := gforce _ cmem_atLeast
    simp only [atLeastOne, prodE, oneMinus, List.map, EmittedExpr.eval] at h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (by omega)
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inr (Or.inl (by omega))
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by omega))))
  · exact (binBody_zero_iff _ COMPOSED).mp (gforce _ cmem_composedBin)
  · exact (binBody_zero_iff _ GATE_OUT).mp (gforce _ cmem_gateOutBin)
  · intro hop; have h := gforce _ cmem_and
    simp only [subV, EmittedExpr.eval] at h; rw [hop, one_mul] at h; omega
  · intro hop; have h := gforce _ cmem_or
    simp only [sumE, EmittedExpr.eval, List.map] at h; rw [hop, one_mul] at h; omega
  · intro hop; have h := gforce _ cmem_not
    simp only [sumE, EmittedExpr.eval, List.map] at h; rw [hop, one_mul] at h; omega
  · intro hop; have h := gforce _ cmem_thr
    simp only [subV, EmittedExpr.eval] at h; rw [hop, one_mul] at h; omega
  · intro hop; have h := gforce _ cmem_cust
    simp only [subV, EmittedExpr.eval] at h; rw [hop, one_mul] at h; omega
  · intro j hj; have h := gforce _ (cmem_commit j hj)
    simp only [subV, EmittedExpr.eval] at h; omega
  · exact pforce _ _ cmem_piComposed
  · exact pforce _ _ cmem_piTree
  · exact pforce _ _ cmem_piThr
  · intro j hj; exact pforce _ _ (cmem_piExp j hj)

/-- The fully-in-circuit corollary: an accepting compound trace configured as NOT computes the
GENUINE boolean negation of its sub-result. -/
theorem compound_not_computes_negation {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hlen : 2 ≤ t.rows.length)
    (hsat : Satisfied2 hash compoundPredicateDesc minit mfin maddrs t)
    (hnot : (envAt t 0).loc OP_NOT = 1) :
    (envAt t 0).loc COMPOSED = 1 - (envAt t 0).loc 0 :=
  (compound_sat_imp_sem hlen hsat).notLaw hnot

/-! ## §5–§6 — COMPOUND non-vacuity: a NOT-of-`1` witness, and a bad `composed = 1` run. -/

/-- A row from an explicit column-prefix list (off-the-end = 0). -/
def rowOf (cols : List ℤ) : Assignment := fun i => cols.getD i 0

/-- The abstract hash never enters the compound denotation (no hash sites / map ops). -/
def hash0 : List ℤ → ℤ := fun _ => 0

/-- The honest compound witness: NOT is selected (`op_not = 1`), `sub_result_0 = 1`, and the
composed result is the genuine negation `1 − 1 = 0`. Every other wire is `0`. -/
def compoundRow : Assignment := fun c => if c = 0 then 1 else if c = OP_NOT then 1 else 0

/-- All public inputs `0` (the composed / tree-hash / threshold / expected-commitment pins all read
`0` in this witness). -/
def compoundPub : Assignment := fun _ => 0

/-- The concrete 2-row satisfying run (row 0 active, row 1 the wrap row); both rows carry
`compoundRow`. -/
def compoundWitness : VmTrace := { rows := [compoundRow, compoundRow], pub := compoundPub, tf := fun _ => [] }

/-- **The witness PROVABLY satisfies the compound descriptor.** On the active row 0 every gate body
vanishes and every PI pin reads `0`; on the wrap row 1 every constraint is vacuous; the memory legs
are the empty-log balance. -/
theorem compoundWitness_satisfies :
    Satisfied2 hash0 compoundPredicateDesc (fun _ => 0) (fun _ => (0, 0)) [] compoundWitness where
  rowConstraints := by
    intro i hi c hc
    have g0 : ((0 : Nat) + 1 == compoundWitness.rows.length) = false := rfl
    have g1 : ((1 : Nat) + 1 == compoundWitness.rows.length) = true := rfl
    have hi2 : i < 2 := hi
    clear hi
    simp only [compoundPredicateDesc, compoundConstraints] at hc
    interval_cases i <;>
      fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, gate, piFirst, g0, g1] <;>
      decide
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp only [compoundPredicateDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [cmemLog] at hop; simp at hop
  memDisciplined := by rw [cmemLog]; trivial
  memBalanced := by rw [cmemLog]; exact memCheck_nil _ _
  memTableFaithful := by rw [cmemLog]; rfl
  mapTableFaithful := by rw [cmapLog]; rfl

/-- **The bridge FIRES on the witness (the true half of non-vacuity):** the recovered composed
result is the concrete `0 = 1 − 1`, the genuine boolean NOT of `sub_result_0 = 1`. -/
theorem compoundWitness_sem_concrete :
    (envAt compoundWitness 0).loc OP_NOT = 1
      ∧ (envAt compoundWitness 0).loc 0 = 1
      ∧ (envAt compoundWitness 0).loc COMPOSED = 0
      ∧ (envAt compoundWitness 0).loc COMPOSED = 1 - (envAt compoundWitness 0).loc 0 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  exact compound_not_computes_negation (t := compoundWitness) (by decide) compoundWitness_satisfies
    (by decide)

/-- The dishonest attempt: NOT is selected on `sub_result_0 = 1`, but the prover claims
`composed = 1` (should be `0`). Row-0's NOT gate `op_not·(composed + sub_0 − 1) = 1·1 = 1 ≠ 0`. -/
def compoundBadRow : Assignment := fun c => if c = 0 then 1 else if c = OP_NOT then 1 else if c = COMPOSED then 1 else 0

def compoundBad : VmTrace := { rows := [compoundBadRow, compoundBadRow], pub := compoundPub, tf := fun _ => [] }

/-- **The dishonest run PROVABLY FAILS the hypothesis (the false half of non-vacuity):** the NOT gate
forces `composed = 1 − sub_0 = 0`, so a `composed = 1` claim has no `Satisfied2` witness. -/
theorem compoundBad_not_satisfies :
    ¬ Satisfied2 hash0 compoundPredicateDesc (fun _ => 0) (fun _ => (0, 0)) [] compoundBad := by
  intro h
  have h0 : (0 : Nat) < compoundBad.rows.length := by decide
  have hL : ((0 : Nat) + 1 == compoundBad.rows.length) = false := by decide
  have hrc := h.rowConstraints 0 h0
    (gate (.mul (.var OP_NOT) (sumE [.var COMPOSED, .var 0, .const (-1)]))) cmem_not
  rw [hL] at hrc
  simp only [gate, VmConstraint2.holdsAt, holdsVm_gate_false, sumE, EmittedExpr.eval] at hrc
  revert hrc; decide

/-! ## §7 — The authored functional spec for the RELATIONAL predicate. -/

/-- **`RelClassified hash env`** — the semantic relation the relational (`value_a <op> value_b`
over Poseidon2-committed values) predicate is meant to compute on one active row, over the ℤ field
model, against a FAITHFUL Poseidon2 chip table (the `hash` opening carrier). -/
structure RelClassified (hash : List ℤ → ℤ) (env : VmRowEnv) : Prop where
  /-- The public commitment `pi[0]` is a Poseidon2 opening of the private `(value_a, blinding_a)`. -/
  commitAOpen : env.loc COMMIT_A = hash [env.loc VALUE_A, env.loc BLINDING_A]
  /-- The public commitment `pi[1]` is a Poseidon2 opening of the private `(value_b, blinding_b)`. -/
  commitBOpen : env.loc COMMIT_B = hash [env.loc VALUE_B, env.loc BLINDING_B]
  commitAPin  : env.loc COMMIT_A = env.pub 0
  commitBPin  : env.loc COMMIT_B = env.pub 1
  /-- The asserted comparison result bit is TRUE (and published as `pi[2]`). -/
  resultTrue  : env.loc RESULT_BIT = 1
  resultPin   : env.loc RESULT_BIT = env.pub 2
  rangeBool   : env.loc RANGE_FLAG = 0 ∨ env.loc RANGE_FLAG = 1
  eqBool      : env.loc EQ_FLAG = 0 ∨ env.loc EQ_FLAG = 1
  neqBool     : env.loc NEQ_FLAG = 0 ∨ env.loc NEQ_FLAG = 1
  /-- Exactly one of the {range, eq, neq} comparison relations is selected. -/
  exactlyOne  : env.loc RANGE_FLAG + env.loc EQ_FLAG + env.loc NEQ_FLAG = 1
  /-- ⚑ THE VERDICT WELD (C2b): the free difference witness IS the committed-value difference
  `value_a − value_b`. WITHOUT this the eq/neq/range comparisons below operate on a prover-chosen
  free `diff` decoupled from the committed values (the forgery item 1 names); WITH it, every selected
  comparison is genuinely a comparison of `VALUE_A` against `VALUE_B`. -/
  diffWeld    : env.loc DIFF = env.loc VALUE_A - env.loc VALUE_B
  /-- The selected relation holds on the private difference witness: EQ ⇒ `diff = 0`. -/
  eqRel       : env.loc EQ_FLAG = 1 → env.loc DIFF = 0
  /-- RANGE ⇒ every diff bit is boolean (the recomposition is a sum of nonnegative terms). -/
  rangeBits   : env.loc RANGE_FLAG = 1 →
                  ∀ i, i < NUM_DIFF_BITS → env.loc (DIFF_BITS_START + i) = 0
                    ∨ env.loc (DIFF_BITS_START + i) = 1
  /-- NEQ ⇒ `diff ≠ 0` (witnessed by the supplied inverse). -/
  neqRel      : env.loc NEQ_FLAG = 1 → env.loc DIFF ≠ 0
  /-- RANGE ⇒ the top diff bit clears (`diff < 2^29`). -/
  rangeHigh   : env.loc RANGE_FLAG = 1 → env.loc (DIFF_BITS_START + NUM_DIFF_BITS - 1) = 0
  /-- RANGE ⇒ the diff bits recompose `diff`. -/
  rangeRecomp : env.loc RANGE_FLAG = 1 → recomposeExpr.eval env.loc = env.loc DIFF

/-! ## §8 — the constraints of `relationalPredicateDesc` are genuinely present (membership nav). -/

theorem rmem_resultPin : piFirst RESULT_BIT 2 ∈ relationalPredicateDesc.constraints := by
  show _ ∈ relationalConstraints
  unfold relationalConstraints
  iterate 14 apply List.mem_append_left
  simp

theorem rmem_c2 : gate (subC (.var RESULT_BIT) 1) ∈ relationalPredicateDesc.constraints := by
  show _ ∈ relationalConstraints
  unfold relationalConstraints
  iterate 13 apply List.mem_append_left
  apply List.mem_append_right; simp

/-- ⚑ THE VERDICT-WELD constraint `diff == value_a − value_b` (C2b) is genuinely present. -/
theorem rmem_c2b :
    gate (.add (subV (.var DIFF) VALUE_A) (.var VALUE_B)) ∈ relationalPredicateDesc.constraints := by
  show _ ∈ relationalConstraints
  unfold relationalConstraints
  iterate 12 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem rmem_c3range : gate (binBody RANGE_FLAG) ∈ relationalPredicateDesc.constraints := by
  show _ ∈ relationalConstraints
  unfold relationalConstraints
  iterate 11 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem rmem_c3eq : gate (binBody EQ_FLAG) ∈ relationalPredicateDesc.constraints := by
  show _ ∈ relationalConstraints
  unfold relationalConstraints
  iterate 11 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem rmem_c3neq : gate (binBody NEQ_FLAG) ∈ relationalPredicateDesc.constraints := by
  show _ ∈ relationalConstraints
  unfold relationalConstraints
  iterate 11 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem rmem_c4 :
    gate (sumE [.var RANGE_FLAG, .var EQ_FLAG, .var NEQ_FLAG, .const (-1)])
      ∈ relationalPredicateDesc.constraints := by
  show _ ∈ relationalConstraints
  unfold relationalConstraints
  iterate 10 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem rmem_c6 (i : Nat) (hi : i < NUM_DIFF_BITS) :
    gate (.mul (.var RANGE_FLAG) (binBody (DIFF_BITS_START + i)))
      ∈ relationalPredicateDesc.constraints := by
  show _ ∈ relationalConstraints
  unfold relationalConstraints
  iterate 8 apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map_of_mem (List.mem_range.mpr hi)

theorem rmem_c7 :
    gate (.mul (.var RANGE_FLAG) (subV recomposeExpr DIFF)) ∈ relationalPredicateDesc.constraints := by
  show _ ∈ relationalConstraints
  unfold relationalConstraints
  iterate 7 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem rmem_c8 :
    gate (.mul (.var RANGE_FLAG) (.var (DIFF_BITS_START + NUM_DIFF_BITS - 1)))
      ∈ relationalPredicateDesc.constraints := by
  show _ ∈ relationalConstraints
  unfold relationalConstraints
  iterate 6 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem rmem_c9 :
    gate (.mul (.var EQ_FLAG) (.var DIFF)) ∈ relationalPredicateDesc.constraints := by
  show _ ∈ relationalConstraints
  unfold relationalConstraints
  iterate 5 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem rmem_c10 :
    gate (.mul (.var NEQ_FLAG) (subC (.mul (.var DIFF) (.var NEQ_INV)) 1))
      ∈ relationalPredicateDesc.constraints := by
  show _ ∈ relationalConstraints
  unfold relationalConstraints
  iterate 4 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem rmem_commitAPin : piFirst COMMIT_A 0 ∈ relationalPredicateDesc.constraints := by
  show _ ∈ relationalConstraints
  unfold relationalConstraints
  iterate 2 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem rmem_commitBPin : piFirst COMMIT_B 1 ∈ relationalPredicateDesc.constraints := by
  show _ ∈ relationalConstraints
  unfold relationalConstraints
  iterate 2 apply List.mem_append_left
  apply List.mem_append_right; simp

theorem rmem_lookupA :
    commitLookup VALUE_A BLINDING_A COMMIT_A LANES_A ∈ relationalPredicateDesc.constraints := by
  show _ ∈ relationalConstraints
  unfold relationalConstraints
  apply List.mem_append_left
  apply List.mem_append_right; simp

theorem rmem_lookupB :
    commitLookup VALUE_B BLINDING_B COMMIT_B LANES_B ∈ relationalPredicateDesc.constraints := by
  show _ ∈ relationalConstraints
  unfold relationalConstraints
  apply List.mem_append_left
  apply List.mem_append_right; simp

/-! ## §9 — THE RELATIONAL WHOLE-DESCRIPTOR BRIDGE (SAT_IMPLIES_SEM, against the named carrier). -/

/-- **`relational_sat_imp_sem` — the Rung-1 functional-correctness refinement for the relational
predicate.** A trace satisfying the emitted `relationalPredicateDesc`, padded to height `≥ 2` (row `0`
is an active transition row), against a FAITHFUL Poseidon2 chip table (`hChip`, the named carrier),
computes the GENUINE committed-value comparison on its boundary row `0`: the public commitments open
the private values, the result bit is asserted, EXACTLY ONE comparison mode is selected, and the
selected relation holds on the private difference witness. -/
theorem relational_sat_imp_sem {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hlen : 2 ≤ t.rows.length)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hsat : Satisfied2 hash relationalPredicateDesc minit mfin maddrs t) :
    RelClassified hash (envAt t 0) := by
  have h0 : 0 < t.rows.length := by omega
  have hF : ((0 : Nat) == 0) = true := rfl
  have hL : ((0 : Nat) + 1 == t.rows.length) = false := by
    have : (0 : Nat) + 1 ≠ t.rows.length := by omega
    simpa using this
  -- a gate constraint forces its body to vanish on the active row 0.
  have gforce : ∀ b : EmittedExpr, gate b ∈ relationalPredicateDesc.constraints →
      b.eval (envAt t 0).loc = 0 := by
    intro b hb
    have h := hsat.rowConstraints 0 h0 (gate b) hb
    rw [hL] at h
    simpa only [gate, VmConstraint2.holdsAt, holdsVm_gate_false] using h
  -- a first-row PI pin fires on row 0.
  have pforce : ∀ col k : Nat, piFirst col k ∈ relationalPredicateDesc.constraints →
      (envAt t 0).loc col = (envAt t 0).pub k := by
    intro col k hb
    have h := hsat.rowConstraints 0 h0 (piFirst col k) hb
    rw [hF] at h
    simpa only [piFirst, VmConstraint2.holdsAt, holdsVm_piFirst_true] using h
  refine
    { commitAOpen := ?_, commitBOpen := ?_, commitAPin := ?_, commitBPin := ?_,
      resultTrue := ?_, resultPin := ?_, rangeBool := ?_, eqBool := ?_, neqBool := ?_,
      exactlyOne := ?_, diffWeld := ?_, eqRel := ?_, rangeBits := ?_, neqRel := ?_,
      rangeHigh := ?_, rangeRecomp := ?_ }
  · -- commitment A opens (via the named chip-lookup soundness carrier).
    have h := hsat.rowConstraints 0 h0 (commitLookup VALUE_A BLINDING_A COMMIT_A LANES_A) rmem_lookupA
    simp only [commitLookup, VmConstraint2.holdsAt, Lookup.holdsAt] at h
    have hs := chip_lookup_sound hash (t.tf .poseidon2) hChip (envAt t 0).loc
      [.var VALUE_A, .var BLINDING_A] COMMIT_A LANES_A (by decide) h
    simpa only [List.map_cons, List.map_nil, EmittedExpr.eval] using hs
  · have h := hsat.rowConstraints 0 h0 (commitLookup VALUE_B BLINDING_B COMMIT_B LANES_B) rmem_lookupB
    simp only [commitLookup, VmConstraint2.holdsAt, Lookup.holdsAt] at h
    have hs := chip_lookup_sound hash (t.tf .poseidon2) hChip (envAt t 0).loc
      [.var VALUE_B, .var BLINDING_B] COMMIT_B LANES_B (by decide) h
    simpa only [List.map_cons, List.map_nil, EmittedExpr.eval] using hs
  · exact pforce _ _ rmem_commitAPin
  · exact pforce _ _ rmem_commitBPin
  · have h := gforce _ rmem_c2; simp only [subC, EmittedExpr.eval] at h; omega
  · exact pforce _ _ rmem_resultPin
  · exact (binBody_zero_iff _ RANGE_FLAG).mp (gforce _ rmem_c3range)
  · exact (binBody_zero_iff _ EQ_FLAG).mp (gforce _ rmem_c3eq)
  · exact (binBody_zero_iff _ NEQ_FLAG).mp (gforce _ rmem_c3neq)
  · have h := gforce _ rmem_c4; simp only [sumE, EmittedExpr.eval] at h; omega
  · -- ⚑ diffWeld: the C2b gate forces `diff = value_a − value_b`.
    have h := gforce _ rmem_c2b; simp only [subV, EmittedExpr.eval] at h; omega
  · intro heq; have h := gforce _ rmem_c9
    simp only [EmittedExpr.eval] at h; rw [heq, one_mul] at h; exact h
  · -- rangeBits: each diff bit is boolean when range mode is selected.
    intro hr i hi
    have h2 : (envAt t 0).loc RANGE_FLAG * (binBody (DIFF_BITS_START + i)).eval (envAt t 0).loc = 0 :=
      gforce _ (rmem_c6 i hi)
    rw [hr, one_mul] at h2
    exact (binBody_zero_iff _ (DIFF_BITS_START + i)).mp h2
  · intro hneq; have h := gforce _ rmem_c10
    simp only [subC, EmittedExpr.eval] at h; rw [hneq, one_mul] at h
    intro hz; rw [hz, zero_mul] at h; omega
  · intro hr; have h := gforce _ rmem_c8
    simp only [EmittedExpr.eval] at h; rw [hr, one_mul] at h; exact h
  · intro hr; have h := gforce _ rmem_c7
    simp only [subV, EmittedExpr.eval] at h; rw [hr, one_mul] at h; omega

/-- The EQ-mode corollary: an accepting relational trace configured as an EQ comparison forces the
private difference witness to `0` (the committed values are asserted equal via `diff = 0`). -/
theorem relational_eq_forces_diff_zero {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hlen : 2 ≤ t.rows.length)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hsat : Satisfied2 hash relationalPredicateDesc minit mfin maddrs t)
    (heq : (envAt t 0).loc EQ_FLAG = 1) :
    (envAt t 0).loc DIFF = 0 :=
  (relational_sat_imp_sem hlen hChip hsat).eqRel heq

/-! ### §9b — THE RELATION OVER THE COMMITTED VALUES (the verdict-weld payoff).

With `diffWeld` tying `diff` to `value_a − value_b`, each selected comparison is now a genuine
comparison of the two committed values, not of a prover-chosen free `diff`. -/

/-- A sum of nonnegative sub-expressions evaluates nonnegatively. -/
theorem sumE_eval_nonneg (a : Assignment) (l : List EmittedExpr)
    (h : ∀ e ∈ l, 0 ≤ e.eval a) : 0 ≤ (sumE l).eval a := by
  induction l with
  | nil => simp [sumE, EmittedExpr.eval]
  | cons x xs ih =>
    cases xs with
    | nil => simpa [sumE] using h x (by simp)
    | cons y ys =>
      simp only [sumE, EmittedExpr.eval]
      have hx : 0 ≤ x.eval a := h x (by simp)
      have hrest : 0 ≤ (sumE (y :: ys)).eval a := ih (fun e he => h e (List.mem_cons_of_mem _ he))
      omega

/-- **`recompose_nonneg`** — the bit recomposition `Σ 2^i·bit_i` is a sum of nonnegative terms when
every bit is boolean, so it is `≥ 0`. This is the tooth that turns the range mode into `value_a ≥
value_b` (over ℤ): the difference, being a nonnegative bit-sum, is nonnegative. -/
theorem recompose_nonneg {a : Assignment}
    (hb : ∀ i, i < NUM_DIFF_BITS → a (DIFF_BITS_START + i) = 0 ∨ a (DIFF_BITS_START + i) = 1) :
    0 ≤ recomposeExpr.eval a := by
  unfold recomposeExpr
  apply sumE_eval_nonneg
  intro e he
  simp only [List.mem_map, List.mem_range] at he
  obtain ⟨i, hi, rfl⟩ := he
  simp only [EmittedExpr.eval]
  have hbit : 0 ≤ a (DIFF_BITS_START + i) := by rcases hb i hi with h | h <;> omega
  have hpow : 0 ≤ ((2 ^ i : Nat) : Int) := by positivity
  exact mul_nonneg hpow hbit

/-- **EQ ⇒ the committed values are EQUAL.** An accepting EQ-mode relational trace forces
`value_a = value_b` — the genuine "equality over committed values", via `diffWeld` + `eqRel`. -/
theorem relational_eq_forces_values_equal {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hlen : 2 ≤ t.rows.length)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hsat : Satisfied2 hash relationalPredicateDesc minit mfin maddrs t)
    (heq : (envAt t 0).loc EQ_FLAG = 1) :
    (envAt t 0).loc VALUE_A = (envAt t 0).loc VALUE_B := by
  have sem := relational_sat_imp_sem hlen hChip hsat
  have hd := sem.eqRel heq
  have hw := sem.diffWeld
  omega

/-- **NEQ ⇒ the committed values are DISTINCT.** An accepting NEQ-mode trace forces
`value_a ≠ value_b`, via `diffWeld` + `neqRel` (the witnessed inverse). -/
theorem relational_neq_forces_values_distinct {hash : List ℤ → ℤ} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hlen : 2 ≤ t.rows.length)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hsat : Satisfied2 hash relationalPredicateDesc minit mfin maddrs t)
    (hneq : (envAt t 0).loc NEQ_FLAG = 1) :
    (envAt t 0).loc VALUE_A ≠ (envAt t 0).loc VALUE_B := by
  have sem := relational_sat_imp_sem hlen hChip hsat
  have hd := sem.neqRel hneq
  have hw := sem.diffWeld
  omega

/-- **RANGE ⇒ the committed values satisfy `value_a ≥ value_b`** (over ℤ). The range mode's diff
bits recompose `diff` as a nonnegative bit-sum (`recompose_nonneg`), `rangeRecomp` ties that sum to
`diff`, and `diffWeld` ties `diff` to `value_a − value_b` — so `value_b ≤ value_a`. -/
theorem relational_range_forces_ge {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hlen : 2 ≤ t.rows.length)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hsat : Satisfied2 hash relationalPredicateDesc minit mfin maddrs t)
    (hr : (envAt t 0).loc RANGE_FLAG = 1) :
    (envAt t 0).loc VALUE_B ≤ (envAt t 0).loc VALUE_A := by
  have sem := relational_sat_imp_sem hlen hChip hsat
  have hnn := recompose_nonneg (sem.rangeBits hr)
  have hrec := sem.rangeRecomp hr
  have hw := sem.diffWeld
  rw [hrec] at hnn
  omega

/-! ## §10 — RELATIONAL non-vacuity: a committed EQ witness, and a bad `diff = 1` run. -/

/-- The honest relational witness: EQ is selected (`eq_flag = 1`), the difference witness `diff = 0`
(so the committed values are asserted equal), the result bit `= 1`. All committed values / commitments
/ lanes are `0`; the commitments open `hash0 [0,0] = 0`. -/
def relRow : Assignment := fun c => if c = RESULT_BIT then 1 else if c = EQ_FLAG then 1 else 0

/-- Public inputs: `pi[0] = commitment_a = 0`, `pi[1] = commitment_b = 0`, `pi[2] = result_bit = 1`. -/
def relPub : Assignment := fun k => if k = 2 then 1 else 0

/-- The Poseidon2 chip rows the two commitment lookups target: the arity-2 openings of the private
`(value, blinding)` pairs, evaluated on `relRow` (both `[2, 0, …, 0]` under the zero witness). -/
def relPoseidonRowA : List ℤ :=
  (chipLookupTuple [.var VALUE_A, .var BLINDING_A] COMMIT_A LANES_A).map (·.eval relRow)

def relPoseidonRowB : List ℤ :=
  (chipLookupTuple [.var VALUE_B, .var BLINDING_B] COMMIT_B LANES_B).map (·.eval relRow)

/-- The witness trace family carries the two commitment chip rows; every other table is empty. -/
def relTf : TraceFamily
  | TableId.poseidon2 => [relPoseidonRowA, relPoseidonRowB]
  | _ => []

/-- The concrete 2-row satisfying run (row 0 active, row 1 the wrap row); both rows carry `relRow`. -/
def relWitness : VmTrace := { rows := [relRow, relRow], pub := relPub, tf := relTf }

theorem rmemLog (t : VmTrace) : memLog relationalPredicateDesc t = [] := by
  simp [memLog, show memOpsOf relationalPredicateDesc = [] from rfl]

theorem rmapLog (t : VmTrace) : mapLog relationalPredicateDesc t = [] := by
  simp [mapLog, show mapOpsOf relationalPredicateDesc = [] from rfl]

/-- **The witness PROVABLY satisfies the relational descriptor.** On the active row 0 every gate body
vanishes (EQ mode: `range_flag = neq_flag = 0`, `eq_flag·diff = 1·0 = 0`), the two commitment lookups
hit the chip rows, and every PI pin reads its value; on the wrap row 1 the gates are vacuous and the
lookups still hit; the memory legs are the empty-log balance. -/
theorem relWitness_satisfies :
    Satisfied2 hash0 relationalPredicateDesc (fun _ => 0) (fun _ => (0, 0)) [] relWitness where
  rowConstraints := by
    intro i hi c hc
    have g0 : ((0 : Nat) + 1 == relWitness.rows.length) = false := rfl
    have g1 : ((1 : Nat) + 1 == relWitness.rows.length) = true := rfl
    have hi2 : i < 2 := hi
    clear hi
    simp only [relationalPredicateDesc, relationalConstraints] at hc
    interval_cases i <;>
      fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt, gate, piFirst,
        commitLookup, g0, g1] <;>
      decide
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp only [relationalPredicateDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [rmemLog] at hop; simp at hop
  memDisciplined := by rw [rmemLog]; trivial
  memBalanced := by rw [rmemLog]; exact memCheck_nil _ _
  memTableFaithful := by rw [rmemLog]; rfl
  mapTableFaithful := by rw [rmapLog]; rfl

/-- The witness chip table IS Poseidon2-sound for the zero hash: each row is the genuine arity-2 chip
row `chipRow hash0 [0,0] [0,…,0]` (digest `hash0 [0,0] = 0`). The carrier the bridge consumes. -/
theorem relTf_chip_sound : ChipTableSound hash0 (relTf .poseidon2) := by
  intro r hr
  simp only [relTf, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;>
    exact ⟨[0, 0], [0, 0, 0, 0, 0, 0, 0], by decide, by decide, by decide⟩

/-- **The bridge FIRES on the witness (the true half of non-vacuity):** feeding the concrete satisfying
trace + the sound chip table to `relational_sat_imp_sem` recovers the genuine relation, whose EQ leg
forces the concrete `diff = 0` (`value_a`, `value_b` asserted equal, privately). -/
theorem relWitness_sem_concrete :
    (envAt relWitness 0).loc EQ_FLAG = 1
      ∧ (envAt relWitness 0).loc RESULT_BIT = 1
      ∧ (envAt relWitness 0).loc DIFF = 0
      ∧ (envAt relWitness 0).loc COMMIT_A = hash0 [(envAt relWitness 0).loc VALUE_A,
            (envAt relWitness 0).loc BLINDING_A] := by
  have hsem := relational_sat_imp_sem (t := relWitness) (by decide) relTf_chip_sound
    relWitness_satisfies
  exact ⟨by decide, hsem.resultTrue, hsem.eqRel (by decide), hsem.commitAOpen⟩

/-- The dishonest attempt: EQ is selected but the prover claims `diff = 1` (should be `0`). Row-0's
EQ gate `eq_flag·diff = 1·1 = 1 ≠ 0`. -/
def relBadRow : Assignment :=
  fun c => if c = RESULT_BIT then 1 else if c = EQ_FLAG then 1 else if c = DIFF then 1 else 0

def relBad : VmTrace := { rows := [relBadRow, relBadRow], pub := relPub, tf := relTf }

/-- **The dishonest run PROVABLY FAILS the hypothesis (the false half of non-vacuity):** the EQ gate
forces `eq_flag·diff = 0`, so a `diff = 1` claim under EQ has no `Satisfied2` witness — the descriptor's
EQ comparison tooth is exactly what rejects it. -/
theorem relBad_not_satisfies :
    ¬ Satisfied2 hash0 relationalPredicateDesc (fun _ => 0) (fun _ => (0, 0)) [] relBad := by
  intro h
  have h0 : (0 : Nat) < relBad.rows.length := by decide
  have hL : ((0 : Nat) + 1 == relBad.rows.length) = false := by decide
  have hrc := h.rowConstraints 0 h0 (gate (.mul (.var EQ_FLAG) (.var DIFF))) rmem_c9
  rw [hL] at hrc
  simp only [gate, VmConstraint2.holdsAt, holdsVm_gate_false, EmittedExpr.eval] at hrc
  revert hrc; decide

/-- **The EQ-over-committed corollary FIRES on the witness (non-vacuity):** the honest EQ trace
(`value_a = value_b = 0`) discharges `relational_eq_forces_values_equal` to the concrete `0 = 0` —
a genuine committed-value equality recovered from an accepting proof. -/
theorem relWitness_values_equal :
    (envAt relWitness 0).loc VALUE_A = (envAt relWitness 0).loc VALUE_B :=
  relational_eq_forces_values_equal (t := relWitness) (by decide) relTf_chip_sound
    relWitness_satisfies (by decide)

/-! ## §11 — axiom hygiene: every keystone is `#assert_axioms`-clean (carriers named). -/

#assert_axioms compound_sat_imp_sem
#assert_axioms compound_not_computes_negation
#assert_axioms compoundWitness_satisfies
#assert_axioms compoundWitness_sem_concrete
#assert_axioms compoundBad_not_satisfies
#assert_axioms relational_sat_imp_sem
#assert_axioms relational_eq_forces_diff_zero
#assert_axioms sumE_eval_nonneg
#assert_axioms recompose_nonneg
#assert_axioms relational_eq_forces_values_equal
#assert_axioms relational_neq_forces_values_distinct
#assert_axioms relational_range_forces_ge
#assert_axioms relWitness_satisfies
#assert_axioms relTf_chip_sound
#assert_axioms relWitness_sem_concrete
#assert_axioms relWitness_values_equal
#assert_axioms relBad_not_satisfies

end Dregg2.Circuit.Emit.PredicatesRelationalCompoundRefine
