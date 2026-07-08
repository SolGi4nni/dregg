/-
# Dregg2.Circuit.Emit.DerivationRefine — the RUNG-1 functional-correctness refinement for the emitted
Datalog DERIVATION descriptor (`derivationDesc`).

## What this file IS

`DerivationEmit.lean` byte-pins the 377-constraint descriptor and proves ONE per-gate semantic lemma
(`gteHighBit_zero_iff`, the range high-bit tooth). This file proves the missing WHOLE-DESCRIPTOR bridge:
a trace SATISFYING the whole emitted `derivationDesc` (via the deployed acceptance predicate
`Satisfied2`) witnesses the GENUINE semantic relation a Datalog derivation step is meant to compute.

## The NO_LEAN case — we author the functional spec, then prove the refinement

No prior Lean model states what this circuit computes, so §1 authors the semantic RELATION
`DerivationStepValid`, the derivation-step IO contract (over the ℤ field model). It is a composite of
the load-bearing teeth, spanning FOURTEEN of the descriptor's twenty-eight constraint families plus the
two boundary PI pins and the C4 chip carrier — NOT a restatement of a single gate:

| field                        | forced by                | meaning                                              |
|------------------------------|--------------------------|------------------------------------------------------|
| `publishedConclusionIsHeadFact` | C4 (chip) ∘ C6 (pin)  | the published fact `pi[1]` IS `hash_fact(head)`      |
| `derivedHashPublished`       | C6                       | the derived hash column is the published `pi[1]`     |
| `bodyFactHashPublished`      | C6b ∘ boundary           | body atom 0's fact hash IS the exported leaf PI `pi[5]` |
| `stateRootCommitted`         | boundary                 | the body-root column is the committed pre-state `pi[0]` |
| `bodyFlagsBoolean`           | C1                       | each body-membership flag is a boolean selector      |
| `activeBodyRootsCommitted`   | C5 ∘ boundary            | every ACTIVE body atom is keyed to the committed root|
| `headIsVarBoolean`           | C7                       | each head `is_var` flag is boolean                   |
| `headSelectorsBoolean`       | C8                       | each head substitution selector is boolean           |
| `eqSideConditions`           | C12                      | an active `eq` check forces its two terms equal      |
| `memberofSideConditions`     | C14                      | an active `memberof` check forces its terms equal    |
| `gteHonestDiff`              | C16                      | an active `gte` carries the honest diff `a − b`      |
| `gteSignBitZero`             | C19                      | an active `gte`'s 30-bit diff has a zeroed sign bit  |
| `ltHonestDiff`               | C21                      | an active `lt` carries the honest strict diff        |
| `ltSignBitZero`              | C24                      | an active `lt`'s 30-bit diff has a zeroed sign bit   |

§4's `derivation_sat_imp_valid` (SAT_IMPLIES_SEM, the load-bearing soundness direction) composes these
teeth on the boundary/active row `0` of any accepting trace: the row is FIRST (`isFirst`, so the C6 /
boundary PI pins fire) and a TRANSITION row (`isLast = false`, guaranteed by `hlen : 2 ≤ height`, the
power-of-two padding the deployed AIR always lays), so the gate teeth are still active.

## The named carrier

The crown `publishedConclusionIsHeadFact` binds the C4 chip lookup to `hash` only against a SOUND chip
table; that soundness enters as the explicit hypothesis `ChipTableSound hash (t.tf .poseidon2)` — the
same Poseidon2 chip-AIR faithfulness `chip_lookup_sound` names, discharged concretely by the witness
below (its `tf .poseidon2` carries the genuine `chipRow`). No crypto axiom is consumed.

## Non-vacuity (the anti-scar)

* `witTrace` (§5): a concrete 2-row derivation run (one body atom active, keyed to the committed root;
  all side-conditions inactive; the head published as its genuine hash-fact) that PROVABLY
  `Satisfied2 derivationDesc` (`witTrace_satisfies`) against a genuine chip table (`witTf_chipSound`).
  Feeding it the bridge recovers the genuine relation (`witTrace_valid`), so the `Satisfied2` hypothesis
  is genuinely INHABITED — end to end, with the gate teeth actually binding on the active row 0.
* `witTraceBad` (§5): the SAME rows but an EMPTY chip table, so the C4 lookup has no matching row —
  it PROVABLY FAILS `Satisfied2` (`witTrace_not_satisfies`). So the descriptor is not constantly true;
  the hypothesis is genuinely CONSTRAINING.
* `DerivationStepValid` genuinely discriminates: it HOLDS on an all-zero env (`sem_holds`) and FAILS on
  `badEnv`, an env with an active `eq` side-condition whose terms are `5 ≠ 7` (`sem_fails`) — so the
  bridge's conclusion is a genuine, non-constant predicate.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The Poseidon2 CR carrier enters ONLY as the
NAMED hypothesis `ChipTableSound hash (t.tf .poseidon2)`, never as an axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.DerivationEmit
import Dregg2.Circuit.DecideSatisfied2

namespace Dregg2.Circuit.Emit.DerivationRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmConstraint VmRowEnv holdsVm_piFirst_true holdsVm_gate_false)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.DecideSatisfied2
  (decideConstraint2 decideRowConstraints2 decideLookup_iff decideWindow_iff)
open Dregg2.Circuit.Argus.InterpCore (decideConstraint decideConstraint_iff)
open Dregg2.Circuit.Emit.DerivationEmit

set_option autoImplicit false
set_option maxRecDepth 8000

/-! ## §1 — The authored functional spec: the GENUINE Datalog derivation-step relation. -/

/-- **`DerivationStepValid hash env`** — the semantic relation the Datalog derivation circuit is meant
to compute, over the ℤ field model (`hash` is the abstract Poseidon2 permutation). A row environment
`env` witnesses it iff the fourteen load-bearing teeth of the descriptor hold; see the file header for
the field↔constraint map. The crown is `publishedConclusionIsHeadFact`: the published conclusion IS the
genuine hash-fact of the head predicate applied to the head terms. -/
structure DerivationStepValid (hash : List ℤ → ℤ) (env : VmRowEnv) : Prop where
  /-- C4 (chip) ∘ C6 (pin): the published conclusion `pi[1]` IS the genuine hash-fact of the derived
  head — `hash [head_pred, head_term0..3, 0xFACF, 1]`, the DECO fact-site shape. -/
  publishedConclusionIsHeadFact :
    env.pub 1 = hash [env.loc HEAD_PRED, env.loc (headTerm 0), env.loc (headTerm 1),
                      env.loc (headTerm 2), env.loc (headTerm 3), 64207, 1]
  /-- C6: the derived-hash column is the published conclusion `pi[1]`. -/
  derivedHashPublished : env.loc DERIVED_HASH = env.pub 1
  /-- C6b: the body atom 0's fact hash is the exported membership-leaf binding `pi[5]` — the
  consumed body fact is pinned to a PUBLIC INPUT so the full-turn verifier can bind it to the c-list
  membership proof's authenticated leaf (closes the body↔membership-leaf gap, held forgery #3). -/
  bodyFactHashPublished : env.loc (bodyHash 0) = env.pub 5
  /-- boundary: the body-root column is the committed pre-state root `pi[0]`. -/
  stateRootCommitted : env.loc BODY_ROOT_START = env.pub 0
  /-- C1: each body-membership flag is a boolean selector. -/
  bodyFlagsBoolean : ∀ i, i < MAX_BODY_ATOMS →
    env.loc (bodyFlag i) = 0 ∨ env.loc (bodyFlag i) = 1
  /-- C5 ∘ boundary: every ACTIVE body atom is authenticated against the committed state root `pi[0]`. -/
  activeBodyRootsCommitted : ∀ i, i < MAX_BODY_ATOMS →
    env.loc (bodyFlag i) = 1 → env.loc (bodyRoot i) = env.pub 0
  /-- C7: each head `is_var` flag is boolean. -/
  headIsVarBoolean : ∀ t, t < MAX_HEAD_TERMS →
    env.loc (headIsVar t) = 0 ∨ env.loc (headIsVar t) = 1
  /-- C8: each head substitution selector is boolean. -/
  headSelectorsBoolean : ∀ t v, t < MAX_HEAD_TERMS → v < MAX_SUB_VARS →
    env.loc (headSelVar t v) = 0 ∨ env.loc (headSelVar t v) = 1
  /-- C12: an active equality side-condition forces its two terms equal. -/
  eqSideConditions : ∀ i, i < MAX_EQUAL_CHECKS →
    env.loc (eqCheckActive i) = 1 → env.loc (eqCheckTermA i) = env.loc (eqCheckTermB i)
  /-- C14: an active memberof side-condition forces its resolved terms equal. -/
  memberofSideConditions : ∀ i, i < MAX_MEMBEROF_CHECKS →
    env.loc (memberofCheckActive i) = 1 →
      env.loc (memberofCheckTermA i) = env.loc (memberofCheckTermB i)
  /-- C16: an active GTE comparator carries the honest difference `term_a − term_b`. -/
  gteHonestDiff : env.loc GTE_CHECK_ACTIVE = 1 →
    env.loc GTE_CHECK_DIFF = env.loc GTE_CHECK_TERM_A - env.loc GTE_CHECK_TERM_B
  /-- C19: an active GTE comparator's 30-bit difference has a zeroed sign bit (the in-range top bit). -/
  gteSignBitZero : env.loc GTE_CHECK_ACTIVE = 1 →
    env.loc (gteDiffBit (GTE_DIFF_BITS - 1)) = 0
  /-- C21: an active LT comparator carries the honest strict difference `term_b − term_a − 1`. -/
  ltHonestDiff : env.loc LT_CHECK_ACTIVE = 1 →
    env.loc LT_CHECK_DIFF = env.loc LT_CHECK_TERM_B - env.loc LT_CHECK_TERM_A - 1
  /-- C24: an active LT comparator's 30-bit difference has a zeroed sign bit. -/
  ltSignBitZero : env.loc LT_CHECK_ACTIVE = 1 →
    env.loc (ltDiffBit (GTE_DIFF_BITS - 1)) = 0

/-! ## §2 — The C4 chip-lookup input list; the tuple IS a `chipLookupTuple`. -/

/-- The seven absorbed inputs of the C4 `hash_fact` site: `[head_pred, head_term0..3, 0xFACF, 1]`. -/
def c4Ins : List EmittedExpr :=
  [.var HEAD_PRED, .var HEAD_TERM_START, .var (HEAD_TERM_START + 1),
   .var (HEAD_TERM_START + 2), .var (HEAD_TERM_START + 3), .const 64207, .const 1]

/-- The emitted C4 fact-site tuple IS the generic `chipLookupTuple` of `c4Ins` at digest column
`DERIVED_HASH` with the seven exposed lane columns — so the chip carrier applies verbatim. -/
theorem c4tuple_eq : c4FactSiteTuple = chipLookupTuple c4Ins DERIVED_HASH c4LaneCols := rfl

/-! ## §3 — Extraction helpers: reading per-row facts out of a `Satisfied2` witness on row 0. -/

section Extract
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **Any base-gate constraint forces its body to vanish on the active row 0** (`isLast = false`, from
`hlen`). -/
theorem der_gate0 (hlen : 2 ≤ t.rows.length)
    (hsat : Satisfied2 hash derivationDesc minit mfin maddrs t)
    {g : EmittedExpr} (hg : VmConstraint2.base (.gate g) ∈ derivationDesc.constraints) :
    g.eval (envAt t 0).loc = 0 := by
  have hpos : 0 < t.rows.length := by omega
  have hrc := hsat.rowConstraints 0 hpos _ hg
  have hlf : ((0 : Nat) + 1 == t.rows.length) = false := by
    have : (0 : Nat) + 1 ≠ t.rows.length := by omega
    simpa using this
  simpa only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc

/-- **A first-row PI pin fires on row 0.** -/
theorem der_pi0 (hlen : 2 ≤ t.rows.length)
    (hsat : Satisfied2 hash derivationDesc minit mfin maddrs t)
    {col k : Nat} (hb : VmConstraint2.base (.piBinding .first col k) ∈ derivationDesc.constraints) :
    (envAt t 0).loc col = t.pub k := by
  have hpos : 0 < t.rows.length := by omega
  have hrc := hsat.rowConstraints 0 hpos _ hb
  have := (holdsVm_piFirst_true (envAt t 0) (0 + 1 == t.rows.length) col k).mp
  simpa using this hrc

end Extract

/-! ### Membership lifts: each family is a sublist of the descriptor's constraint list. -/

theorem lift_c1 {x} (hx : x ∈ c1) : x ∈ derivationDesc.constraints := by
  show x ∈ derivationConstraints
  simp only [derivationConstraints, List.append_assoc, List.mem_append]; tauto
theorem lift_c4 {x} (hx : x ∈ c4) : x ∈ derivationDesc.constraints := by
  show x ∈ derivationConstraints
  simp only [derivationConstraints, List.append_assoc, List.mem_append]; tauto
theorem lift_c5 {x} (hx : x ∈ c5) : x ∈ derivationDesc.constraints := by
  show x ∈ derivationConstraints
  simp only [derivationConstraints, List.append_assoc, List.mem_append]; tauto
theorem lift_c6 {x} (hx : x ∈ c6) : x ∈ derivationDesc.constraints := by
  show x ∈ derivationConstraints
  simp only [derivationConstraints, List.append_assoc, List.mem_append]; tauto
theorem lift_c6b {x} (hx : x ∈ c6b) : x ∈ derivationDesc.constraints := by
  show x ∈ derivationConstraints
  simp only [derivationConstraints, List.append_assoc, List.mem_append]; tauto
theorem lift_c7 {x} (hx : x ∈ c7) : x ∈ derivationDesc.constraints := by
  show x ∈ derivationConstraints
  simp only [derivationConstraints, List.append_assoc, List.mem_append]; tauto
theorem lift_c8 {x} (hx : x ∈ c8) : x ∈ derivationDesc.constraints := by
  show x ∈ derivationConstraints
  simp only [derivationConstraints, List.append_assoc, List.mem_append]; tauto
theorem lift_c12 {x} (hx : x ∈ c12) : x ∈ derivationDesc.constraints := by
  show x ∈ derivationConstraints
  simp only [derivationConstraints, List.append_assoc, List.mem_append]; tauto
theorem lift_c14 {x} (hx : x ∈ c14) : x ∈ derivationDesc.constraints := by
  show x ∈ derivationConstraints
  simp only [derivationConstraints, List.append_assoc, List.mem_append]; tauto
theorem lift_c16 {x} (hx : x ∈ c16) : x ∈ derivationDesc.constraints := by
  show x ∈ derivationConstraints
  simp only [derivationConstraints, List.append_assoc, List.mem_append]; tauto
theorem lift_c19 {x} (hx : x ∈ c19) : x ∈ derivationDesc.constraints := by
  show x ∈ derivationConstraints
  simp only [derivationConstraints, List.append_assoc, List.mem_append]; tauto
theorem lift_c21 {x} (hx : x ∈ c21) : x ∈ derivationDesc.constraints := by
  show x ∈ derivationConstraints
  simp only [derivationConstraints, List.append_assoc, List.mem_append]; tauto
theorem lift_c24 {x} (hx : x ∈ c24) : x ∈ derivationDesc.constraints := by
  show x ∈ derivationConstraints
  simp only [derivationConstraints, List.append_assoc, List.mem_append]; tauto
theorem lift_bd {x} (hx : x ∈ boundaries) : x ∈ derivationDesc.constraints := by
  show x ∈ derivationConstraints
  simp only [derivationConstraints, List.append_assoc, List.mem_append]; tauto

/-- Boolean extraction from a `binBody` gate: `col·(col−1) = 0 → col ∈ {0,1}`. -/
theorem bin_of_gate {a : Assignment} {col : Nat} (h : (binBody col).eval a = 0) :
    a col = 0 ∨ a col = 1 := by
  simp only [binBody, EmittedExpr.eval] at h
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linarith)

/-! ## §4 — THE WHOLE-DESCRIPTOR BRIDGE (SAT_IMPLIES_SEM). -/

/-- **`derivation_sat_imp_valid` — the Rung-1 functional-correctness refinement.**

A trace `t` that SATISFIES the emitted `derivationDesc` (via the deployed acceptance predicate
`Satisfied2`), against a SOUND Poseidon2 chip table (the NAMED carrier
`ChipTableSound hash (t.tf .poseidon2)`), and padded to height `≥ 2` (so row `0` is an active transition
row), witnesses the GENUINE Datalog derivation-step relation `DerivationStepValid` on its boundary row
`0`. Composed from the fourteen per-gate teeth + the chip carrier (`chip_lookup_sound`); no crypto axiom
is consumed. -/
theorem derivation_sat_imp_valid {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hSound : ChipTableSound hash (t.tf .poseidon2))
    (hlen : 2 ≤ t.rows.length)
    (hsat : Satisfied2 hash derivationDesc minit mfin maddrs t) :
    DerivationStepValid hash (envAt t 0) := by
  have hpos : 0 < t.rows.length := by omega
  set e := envAt t 0 with he
  -- C6 : derived-hash column is published pi[1].
  have hpin1 : e.loc DERIVED_HASH = t.pub 1 :=
    der_pi0 hlen hsat (lift_c6 (by simp [c6, pin]))
  -- C6b : body atom 0's fact hash column is the exported membership-leaf PI pi[5].
  have hpin5 : e.loc (bodyHash 0) = t.pub 5 :=
    der_pi0 hlen hsat (lift_c6b (by simp [c6b, pin]))
  -- boundary : body-root column is committed pi[0].
  have hpin0 : e.loc BODY_ROOT_START = t.pub 0 :=
    der_pi0 hlen hsat (lift_bd (by simp [boundaries, pin]))
  -- C4 : the chip lookup on row 0 forces derived-hash = hash of the seven absorbed inputs.
  have hlk := hsat.rowConstraints 0 hpos c4Lookup (lift_c4 (by simp [c4]))
  have hmem : (chipLookupTuple c4Ins DERIVED_HASH c4LaneCols).map (·.eval e.loc)
      ∈ t.tf .poseidon2 := by
    have : c4FactSiteTuple.map (·.eval e.loc) ∈ t.tf .poseidon2 := by
      simpa only [VmConstraint2.holdsAt, c4Lookup, Lookup.holdsAt] using hlk
    rwa [c4tuple_eq] at this
  have hdig : e.loc DERIVED_HASH = hash (c4Ins.map (·.eval e.loc)) :=
    chip_lookup_sound hash (t.tf .poseidon2) hSound e.loc c4Ins DERIVED_HASH c4LaneCols (by decide) hmem
  have hmapins : c4Ins.map (·.eval e.loc)
      = [e.loc HEAD_PRED, e.loc (headTerm 0), e.loc (headTerm 1), e.loc (headTerm 2),
         e.loc (headTerm 3), 64207, 1] := by
    simp only [c4Ins, List.map_cons, List.map_nil, EmittedExpr.eval, headTerm, HEAD_TERM_START]
  refine
    { publishedConclusionIsHeadFact := ?_
      derivedHashPublished := ?_
      bodyFactHashPublished := ?_
      stateRootCommitted := ?_
      bodyFlagsBoolean := ?_
      activeBodyRootsCommitted := ?_
      headIsVarBoolean := ?_
      headSelectorsBoolean := ?_
      eqSideConditions := ?_
      memberofSideConditions := ?_
      gteHonestDiff := ?_
      gteSignBitZero := ?_
      ltHonestDiff := ?_
      ltSignBitZero := ?_ }
  · -- crown : pi[1] = derived-hash = hash [head_pred, terms, 0xFACF, 1]
    show e.pub 1 = hash [e.loc HEAD_PRED, e.loc (headTerm 0), e.loc (headTerm 1),
                          e.loc (headTerm 2), e.loc (headTerm 3), 64207, 1]
    have : e.pub 1 = t.pub 1 := rfl
    rw [this, ← hpin1, hdig, hmapins]
  · exact hpin1
  · exact hpin5
  · exact hpin0
  · -- C1 : flags boolean
    intro i hi
    exact bin_of_gate (der_gate0 hlen hsat (lift_c1 (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))
  · -- C5 ∘ boundary : active body root = committed pi[0]
    intro i hi hact
    have hg := der_gate0 hlen hsat
      (lift_c5 (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
    simp only [EmittedExpr.eval, subE] at hg
    -- hg : e.loc (bodyFlag i) * (e.loc (bodyRoot i) + (-1) * e.loc BODY_ROOT_START) = 0
    rw [hact, one_mul] at hg
    have : e.loc (bodyRoot i) = e.loc BODY_ROOT_START := by linarith
    rw [this]; exact hpin0
  · -- C7 : head is_var boolean
    intro t' ht'
    exact bin_of_gate (der_gate0 hlen hsat (lift_c7 (List.mem_map.mpr ⟨t', List.mem_range.mpr ht', rfl⟩)))
  · -- C8 : head selectors boolean
    intro t' v ht' hv
    refine bin_of_gate (der_gate0 hlen hsat (lift_c8 ?_))
    exact List.mem_flatMap.mpr ⟨t', List.mem_range.mpr ht',
      List.mem_map.mpr ⟨v, List.mem_range.mpr hv, rfl⟩⟩
  · -- C12 : active eq → a = b
    intro i hi hact
    have hg := der_gate0 hlen hsat (lift_c12 (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
    simp only [EmittedExpr.eval, subE] at hg
    rw [hact, one_mul] at hg
    linarith
  · -- C14 : active memberof → a = b
    intro i hi hact
    have hg := der_gate0 hlen hsat (lift_c14 (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
    simp only [EmittedExpr.eval, subE] at hg
    rw [hact, one_mul] at hg
    linarith
  · -- C16 : active gte → diff = a − b.  The gate body reduces (definitionally) to the honest form.
    intro hact
    have hg := der_gate0 hlen hsat (lift_c16 (List.Mem.head _))
    have hg' : e.loc GTE_CHECK_ACTIVE *
        (e.loc GTE_CHECK_DIFF + (-1) * e.loc GTE_CHECK_TERM_A + e.loc GTE_CHECK_TERM_B) = 0 := hg
    rw [hact, one_mul] at hg'
    linarith
  · -- C19 : active gte → sign bit 0
    intro hact
    have hg := der_gate0 hlen hsat (lift_c19 (List.Mem.head _))
    have hg' : e.loc GTE_CHECK_ACTIVE * e.loc (gteDiffBit (GTE_DIFF_BITS - 1)) = 0 := hg
    rw [hact, one_mul] at hg'
    exact hg'
  · -- C21 : active lt → diff = b − a − 1.  Same definitional reduction.
    intro hact
    have hg := der_gate0 hlen hsat (lift_c21 (List.Mem.head _))
    have hg' : e.loc LT_CHECK_ACTIVE *
        (e.loc LT_CHECK_DIFF + (-1) * e.loc LT_CHECK_TERM_B + e.loc LT_CHECK_TERM_A + 1) = 0 := hg
    rw [hact, one_mul] at hg'
    linarith
  · -- C24 : active lt → sign bit 0
    intro hact
    have hg := der_gate0 hlen hsat (lift_c24 (List.Mem.head _))
    have hg' : e.loc LT_CHECK_ACTIVE * e.loc (ltDiffBit (GTE_DIFF_BITS - 1)) = 0 := hg
    rw [hact, one_mul] at hg'
    exact hg'

/-! ## §5 — Non-vacuity (the anti-scar).

`derivation_sat_imp_valid` is worthless if its `Satisfied2` hypothesis is UNSATISFIABLE (a vacuous
`P → P`) or its `DerivationStepValid` conclusion is a constant. §5 refutes both: a CONCRETE 2-row
trace that `Satisfied2` ACCEPTS (`witTrace_satisfies`) — with row 0 an active transition row, so the
gate teeth actually bind — and a CONCRETE trace it REJECTS (`witTrace_not_satisfies`, the C4 lookup
bites), plus a concrete env where the semantic relation FAILS (`sem_fails`, an active `eq` with
`5 ≠ 7`) against one where it HOLDS (`sem_holds`). -/

/-- Deciding one constraint against the trivially-false map-oracle SOUNDLY implies it holds — the
`.mapOp` arm is unreachable (the oracle rejects, contradicting `= true`), and `derivationDesc` has no
map ops anyway; every other arm rides the verified per-arm decider. -/
theorem holdsAt_of_dc2 {hash : List ℤ → ℤ} {tf : TraceFamily} {env : VmRowEnv} {f l : Bool}
    {c : VmConstraint2} (h : decideConstraint2 (fun _ _ => false) hash tf env f l c = true) :
    c.holdsAt hash tf env f l := by
  cases c with
  | base c'      => exact (decideConstraint_iff env f l c').mp h
  | lookup ll    => exact (decideLookup_iff tf env ll).mp h
  | memOp _      => exact True.intro
  | mapOp m      => exact absurd h Bool.false_ne_true
  | umemOp _     => exact True.intro
  | proofBind _  => exact True.intro
  | windowGate w => exact (decideWindow_iff env l w).mp h

/-- The whole `rowConstraints` leg, from a single Boolean decision (no `hmapDec` needed — the ONLY
undecidable arm, `.mapOp`, is absent from `derivationDesc`). -/
theorem witRowConstraints {hash : List ℤ → ℤ} {t : VmTrace}
    (hd : decideRowConstraints2 (fun _ _ => false) hash derivationDesc t = true) :
    ∀ i < t.rows.length, ∀ c ∈ derivationDesc.constraints,
      c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  rw [decideRowConstraints2, List.all_eq_true] at hd
  intro i hi c hc
  have h2 := hd i (List.mem_range.mpr hi)
  rw [List.all_eq_true] at h2
  exact holdsAt_of_dc2 (h2 c hc)

/-- The witness ROW assignment: exactly one body atom active (slot 0), whose fact-hash is a nonzero
value with an inverse (`hash·inv = 1`), everything else zeroed. Makes EVERY gate vanish on a
transition row (the flag-0 slot satisfies C1/C2/C5; every other family is gated OFF by a zeroed
flag/active, and C3's product vanishes on the active flag). -/
def wa : Assignment := fun v =>
  if v = bodyFlag 0 then 1 else if v = bodyHash 0 then 1 else if v = bodyInv 0 then 1 else 0

/-- The witness trace family: the ONE Poseidon2 chip row is the genuine evaluated C4 fact-site tuple
(so the lookup holds by construction); every other table is empty. -/
def witTf : TraceFamily := fun tid =>
  if tid = TableId.poseidon2 then [c4FactSiteTuple.map (·.eval wa)] else []

/-- The witness: a 2-row trace (so row 0 is an ACTIVE transition row — the gate teeth bind) whose
both rows carry `wa`. `pub 5 = 1` matches the active body atom 0's fact hash (`wa (bodyHash 0) = 1`),
so the C6b membership-leaf pin holds; every other pin reads `pub _ = 0`. -/
def witTrace : VmTrace :=
  { rows := [wa, wa], pub := fun i => if i = 5 then 1 else 0, tf := witTf }

theorem witMemOps : memOpsOf derivationDesc = [] := by rfl
theorem witMapOps : mapOpsOf derivationDesc = [] := by rfl

theorem witMemLog : memLog derivationDesc witTrace = [] := by
  simp [memLog, witMemOps]

theorem witMapLog : mapLog derivationDesc witTrace = [] := by
  simp [mapLog, witMapOps]

/-- **`witTrace_satisfies` — the SATISFYING witness (hypothesis INHABITED).** The concrete 2-row
`witTrace` is in the deployed accept-set `Satisfied2 derivationDesc`: every one of the 377 gate/pin
constraints holds on both rows (decided), the lone C4 lookup finds its genuine chip row, and the
(empty) memory legs balance. So `derivation_sat_imp_valid`'s hypothesis is genuinely inhabited — with
the gate teeth actually binding on the active row 0. -/
theorem witTrace_satisfies :
    Satisfied2 (fun _ => (0 : ℤ)) derivationDesc (fun _ => 0) (fun _ => (0, 0)) [] witTrace := by
  refine
    { rowConstraints := ?_
      rowHashes := ?_
      rowRanges := ?_
      memAddrsNodup := ?_
      memClosed := ?_
      memDisciplined := ?_
      memBalanced := ?_
      memTableFaithful := ?_
      mapTableFaithful := ?_ }
  · exact witRowConstraints (by decide)
  · intro i _; exact True.intro
  · intro i _ r hr; exact absurd hr List.not_mem_nil
  · exact List.nodup_nil
  · intro op hop; rw [witMemLog] at hop; exact absurd hop List.not_mem_nil
  · rw [witMemLog]; decide
  · rw [witMemLog]; decide
  · rw [witMemLog]; rfl
  · rw [witMapLog]; rfl

/-- **`witTf_chipSound`** — the witness chip table is SOUND: its one row is the genuine `chipRow` of
the seven C4 inputs, whose digest column is `wa DERIVED_HASH = 0 = (fun _ => 0) inputs` (the degenerate
hash). So the bridge's `ChipTableSound` premise is dischargeable on the concrete witness. -/
theorem witTf_chipSound : ChipTableSound (fun _ => (0 : ℤ)) (witTrace.tf TableId.poseidon2) := by
  intro r hr
  have hrow : r = c4FactSiteTuple.map (·.eval wa) := by simpa [witTrace, witTf] using hr
  refine ⟨c4Ins.map (·.eval wa), c4LaneCols.map wa, ?_, ?_, ?_⟩
  · rw [List.length_map]; decide
  · rw [List.length_map]; decide
  · rw [hrow, c4tuple_eq]
    have hwd : wa DERIVED_HASH = 0 := by decide
    simp [chipLookupTuple, chipRow, map_eval_padToE, EmittedExpr.eval, List.map_map,
      Function.comp_def, List.length_map, hwd]

/-- **`witTrace_valid` — the bridge FIRES on the concrete witness (end-to-end non-vacuity).** Feeding
`witTrace` (satisfying, chip-sound, height 2) through `derivation_sat_imp_valid` recovers the FULL
genuine relation `DerivationStepValid` on row 0 — a real accepting trace maps to the real semantic
conclusion, the crown `publishedConclusionIsHeadFact` included. -/
theorem witTrace_valid : DerivationStepValid (fun _ => (0 : ℤ)) (envAt witTrace 0) :=
  derivation_sat_imp_valid witTf_chipSound (by decide) witTrace_satisfies

/-- The rejecting trace: the SAME rows but an EMPTY chip table, so the C4 lookup has no matching row. -/
def witTraceBad : VmTrace := { rows := [wa, wa], pub := fun _ => 0, tf := fun _ => [] }

/-- **`witTrace_not_satisfies` — a REJECTING witness (hypothesis CONSTRAINING).** With no chip row,
the C4 lookup fails on row 0, so `Satisfied2` does NOT hold — the descriptor is not a constantly-true
predicate. -/
theorem witTrace_not_satisfies :
    ¬ Satisfied2 (fun _ => (0 : ℤ)) derivationDesc (fun _ => 0) (fun _ => (0, 0)) [] witTraceBad := by
  intro h
  have hlk := h.rowConstraints 0 (by decide) c4Lookup (lift_c4 (by simp [c4]))
  simp only [VmConstraint2.holdsAt, c4Lookup, Lookup.holdsAt, witTraceBad] at hlk
  exact absurd hlk List.not_mem_nil

/-! ### The semantic relation genuinely DISCRIMINATES (the conclusion is not a constant). -/

/-- **`sem_holds`** — `DerivationStepValid` is SATISFIABLE: the all-zero env (published conclusion the
degenerate `hash [..] = 0`, every comparator/check inactive) witnesses it. -/
theorem sem_holds :
    DerivationStepValid (fun _ => (0 : ℤ)) ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩ := by
  refine
    { publishedConclusionIsHeadFact := ?_, derivedHashPublished := ?_, bodyFactHashPublished := ?_,
      stateRootCommitted := ?_,
      bodyFlagsBoolean := ?_, activeBodyRootsCommitted := ?_, headIsVarBoolean := ?_,
      headSelectorsBoolean := ?_, eqSideConditions := ?_, memberofSideConditions := ?_,
      gteHonestDiff := ?_, gteSignBitZero := ?_, ltHonestDiff := ?_, ltSignBitZero := ?_ }
  · rfl
  · rfl
  · rfl
  · rfl
  · intro i _; exact Or.inl rfl
  · intro i _ hact; simp at hact
  · intro t _; exact Or.inl rfl
  · intro t v _ _; exact Or.inl rfl
  · intro i _ hact; simp at hact
  · intro i _ hact; simp at hact
  · intro hact; exact absurd hact (by decide)
  · intro hact; exact absurd hact (by decide)
  · intro hact; exact absurd hact (by decide)
  · intro hact; exact absurd hact (by decide)

/-- An env with an ACTIVE `eq` side-condition whose two terms are `5 ≠ 7`. -/
def badEnv : VmRowEnv :=
  { loc := fun v => if v = eqCheckActive 0 then 1
                    else if v = eqCheckTermA 0 then 5
                    else if v = eqCheckTermB 0 then 7 else 0
    nxt := fun _ => 0
    pub := fun _ => 0 }

/-- **`sem_fails`** — `DerivationStepValid` is FALSIFIABLE: `badEnv` violates the active `eq`
side-condition (`5 ≠ 7`), so the relation is not constantly true. Together with `sem_holds` this
shows `DerivationStepValid` is a genuine (non-constant) predicate — the bridge's conclusion has
teeth. -/
theorem sem_fails : ¬ DerivationStepValid (fun _ => (0 : ℤ)) badEnv := by
  intro h
  have hbite := h.eqSideConditions 0 (by decide) (by decide)
  exact absurd hbite (by decide)

#assert_axioms derivation_sat_imp_valid
#assert_axioms witTrace_satisfies
#assert_axioms witTf_chipSound
#assert_axioms witTrace_valid
#assert_axioms witTrace_not_satisfies
#assert_axioms sem_holds
#assert_axioms sem_fails

end Dregg2.Circuit.Emit.DerivationRefine
