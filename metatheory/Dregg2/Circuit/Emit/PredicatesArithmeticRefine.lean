/-
# Dregg2.Circuit.Emit.PredicatesArithmeticRefine — the RUNG-1 functional-correctness refinement for
the emitted arithmetic-predicate descriptor (`predicateGeDesc`).

## What this file IS

`PredicatesArithmeticEmit.lean` proves only PER-GATE faithfulness lemmas (`c3_body_zero_iff`,
`c5_body_zero_iff` — each gate poly = 0 ↔ its local slot/diff identity). This file proves the missing
WHOLE-DESCRIPTOR bridge: a trace SATISFYING the emitted `predicateGeDesc` (via the deployed acceptance
predicate `Satisfied2`) computes the GENUINE `GreaterThanOrEqual(value, threshold)` relation.

## The NO_LEAN case — we author the functional spec, then prove the refinement

No prior Lean model states what this circuit computes, so §1 authors the semantic RELATION `ArithGeSem`
(over the ℤ field model): a row witnesses the relation iff its private input value (column `INPUT`) is
`≥` the PUBLIC threshold (`pub PI_THRESHOLD`), with a difference inside the honest chip domain
`[0, 2^29)` (the range-tooth width — a `value` more than `2^29` above `threshold` is outside the
declared domain), AND the published fact-commitment column binds its public input.

§5's `predicateGe_sat_imp_sem` (SAT_IMPLIES_SEM, the load-bearing soundness direction) composes the five
teeth of `predicateGeDesc` on the boundary/active row `0` of any accepting trace:

| tooth                         | fact forced on row 0                                   |
|-------------------------------|--------------------------------------------------------|
| C1 `.piBinding first`         | `loc THRESHOLD = pub PI_THRESHOLD`                      |
| C2 `.piBinding first`         | `loc FACT_COMMITMENT = pub PI_FACT_COMMITMENT`          |
| C3 `.gate c3Body`             | `loc SLOT_A = loc INPUT`                                |
| C5 `.gate c5Body`             | `loc DIFF = loc SLOT_A − loc THRESHOLD`                 |
| C6 `.lookup ⟨range,[DIFF]⟩`   | `0 ≤ loc DIFF ∧ loc DIFF < 2^29`  (under `hrange`)      |

Chaining: `loc DIFF = loc INPUT − pub PI_THRESHOLD ∈ [0, 2^29)`, i.e. `pub PI_THRESHOLD ≤ loc INPUT`
with a bounded difference — the `≥` predicate. The row-0 boundary is where the `.piBinding first` PI
pins fire (`isFirst`) and the `.gate` teeth are still active (`isLast = false`, guaranteed by the
`2 ≤ height` power-of-two padding the deployed AIR always lays); this is the deployment's own single
logical row (`PredicatesArithmeticEmit` §1).

## The named carrier

The range tooth C6 concludes `loc DIFF ∈ [0, 2^29)` only against the FAITHFUL range table. That table
faithfulness enters as the explicit hypothesis `hrange : t.tf .range = rangeRows DIFF_BITS` — the same
`tf .range = rangeRows bits` carrier `DescriptorIR2.lookup_replaces_range` names, discharged concretely
by the witnesses below (their `tf .range` IS `rangeRows 29`). No crypto carrier is consumed (the family
carries no Poseidon2 site).

## Non-vacuity (the anti-scar)

`geWitnessTrace` (§6): a concrete 2-row run `value=100 ≥ threshold=40` (diff `60`) that PROVABLY
`Satisfied2 predicateGeDesc` against the honest `rangeRows 29` table; feeding it the bridge recovers the
genuine `pub PI_THRESHOLD = 40 ≤ 100 = loc INPUT` (`geWitness_sem` / `geWitness_sem_concrete`).
`geBadTrace`: the HONEST `value=30 < threshold=40` attempt (diff `−10`, C1–C5 all consistent) that
PROVABLY FAILS `Satisfied2` (`geBad_not_satisfies`) — the C6 range tooth rejects a below-threshold diff.
So the `Satisfied2` hypothesis is genuinely inhabited AND constraining.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.PredicatesArithmeticEmit

namespace Dregg2.Circuit.Emit.PredicatesArithmeticRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmConstraint VmRowEnv VmRange holdsVm_gate_false holdsVm_piFirst_true)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.PredicatesArithmeticEmit

set_option autoImplicit false
set_option maxRecDepth 8000

/-! ## §1 — The authored functional spec: the GENUINE `GreaterThanOrEqual(value, threshold)` relation. -/

/-- **`ArithGeSem env`** — the semantic relation the arithmetic `GreaterThanOrEqual(value, threshold)`
predicate is meant to compute, over the ℤ field model. A row environment `env` witnesses it iff:

  * `ge`        — the private input value (`loc INPUT`) is `≥` the PUBLIC threshold (`pub PI_THRESHOLD`);
  * `domain`    — the difference lies inside the honest chip domain `[0, 2^29)` (the range-tooth width);
  * `factBinds` — the published fact-commitment column (`loc FACT_COMMITMENT`) binds its public input
    (`pub PI_FACT_COMMITMENT`).

This is the missing Rung-1 functional spec (NO prior Lean model): `predicateGe_sat_imp_sem` proves the
emitted descriptor REFINES it. -/
structure ArithGeSem (env : VmRowEnv) : Prop where
  ge        : env.pub PI_THRESHOLD ≤ env.loc INPUT
  domain    : env.loc INPUT - env.pub PI_THRESHOLD < (2 : ℤ) ^ DIFF_BITS
  factBinds : env.loc FACT_COMMITMENT = env.pub PI_FACT_COMMITMENT

/-! ## §2 — The five constraints of `predicateGeDesc` are genuinely present. -/

theorem mem_c1 : c1ThresholdPin ∈ predicateGeDesc.constraints :=
  List.mem_cons.mpr (Or.inl rfl)

theorem mem_c2 : c2FactPin ∈ predicateGeDesc.constraints :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

theorem mem_c3 : c3SlotGate ∈ predicateGeDesc.constraints :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

theorem mem_c5 : c5DiffGate ∈ predicateGeDesc.constraints :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
    (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

theorem mem_c6 : c6RangeLookup ∈ predicateGeDesc.constraints :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
    (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

theorem mem_factHash : factHashLookup ∈ predicateGeDesc.constraints := by
  simp only [predicateGeDesc]
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; exact List.mem_cons_self

theorem mem_factCommit : factCommitLookup ∈ predicateGeDesc.constraints := by
  simp only [predicateGeDesc]
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
  exact List.mem_cons_self

/-! ## §3 — empty mem/map logs (the descriptor is pure gates + one range lookup). -/

theorem memOpsOf_pred : memOpsOf predicateGeDesc = [] := rfl
theorem mapOpsOf_pred : mapOpsOf predicateGeDesc = [] := rfl
theorem memLog_pred (t : VmTrace) : memLog predicateGeDesc t = [] := by
  simp [memLog, memOpsOf_pred]
theorem mapLog_pred (t : VmTrace) : mapLog predicateGeDesc t = [] := by
  simp [mapLog, mapOpsOf_pred]

/-! ## §5 — THE WHOLE-DESCRIPTOR BRIDGE (SAT_IMPLIES_SEM). -/

/-- **The deployed range-check canonicality envelope for the Ge row (row 0).** Under the field-faithful
mod-`p` denotation every pin/gate binds only a congruence; this envelope reads the ℤ semantics back off
it. The compared cells (`INPUT`/`SLOT_A`/`THRESHOLD`) sit in the LOW HALF of the field (`2·x < p`), so
the field subtraction `value − threshold` is WRAP-FREE over ℤ (together with `DIFF < 2^29 < p/2` from
the range tooth); the commitment cell and the two public inputs are canonical (`0 ≤ · < p`). Inhabited
concretely by `geWitness_canon`, so the envelope is non-vacuous. -/
def GeCanon (t : VmTrace) : Prop :=
  (0 ≤ (envAt t 0).loc INPUT ∧ 2 * (envAt t 0).loc INPUT < 2013265921)
  ∧ (0 ≤ (envAt t 0).loc SLOT_A ∧ 2 * (envAt t 0).loc SLOT_A < 2013265921)
  ∧ (0 ≤ (envAt t 0).loc THRESHOLD ∧ 2 * (envAt t 0).loc THRESHOLD < 2013265921)
  ∧ (0 ≤ (envAt t 0).loc FACT_COMMITMENT ∧ (envAt t 0).loc FACT_COMMITMENT < 2013265921)
  ∧ (0 ≤ (envAt t 0).pub PI_THRESHOLD ∧ (envAt t 0).pub PI_THRESHOLD < 2013265921)
  ∧ (0 ≤ (envAt t 0).pub PI_FACT_COMMITMENT ∧ (envAt t 0).pub PI_FACT_COMMITMENT < 2013265921)

theorem predicateGe_sat_imp_sem {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hrange : t.tf .range = rangeRows DIFF_BITS)
    (hlen : 2 ≤ t.rows.length)
    (hsat : Satisfied2 hash predicateGeDesc minit mfin maddrs t)
    (hcanon : GeCanon t) :
    ArithGeSem (envAt t 0) := by
  obtain ⟨hcINPUT, hcSLOT, hcTH, hcFC, hcPITH, hcPIFC⟩ := hcanon
  have h0 : 0 < t.rows.length := by omega
  have hfirst : ((0 : Nat) == 0) = true := rfl
  have hlast : ((0 : Nat) + 1 == t.rows.length) = false := by
    have : (0 : Nat) + 1 ≠ t.rows.length := by omega
    simpa using this
  have hpow : (2 : ℤ) ^ DIFF_BITS = 536870912 := by norm_num [DIFF_BITS]
  -- C6 : diff range proof against the faithful range table (genuine ℤ, unaffected by the denotation).
  have hc6 : 0 ≤ (envAt t 0).loc DIFF ∧ (envAt t 0).loc DIFF < (2 : ℤ) ^ DIFF_BITS := by
    have h := hsat.rowConstraints 0 h0 c6RangeLookup mem_c6
    simp only [c6RangeLookup, VmConstraint2.holdsAt] at h
    have hv := lookup_replaces_range DIFF_BITS t.tf hrange (envAt t 0) DIFF h
    simpa only [VmRange.holds] using hv
  obtain ⟨hlo, hhi⟩ := hc6
  have hhi_num : (envAt t 0).loc DIFF < 536870912 := by rw [hpow] at hhi; exact hhi
  -- C1 : threshold PI pin (mod-p) lifted to ℤ by canonicality of both sides.
  have hc1 : (envAt t 0).loc THRESHOLD = (envAt t 0).pub PI_THRESHOLD := by
    have h := hsat.rowConstraints 0 h0 c1ThresholdPin mem_c1
    rw [hfirst] at h
    simp only [c1ThresholdPin, VmConstraint2.holdsAt, holdsVm_piFirst_true] at h
    obtain ⟨k, hk⟩ := h.dvd
    omega
  -- C2 : fact-commitment PI pin (mod-p) lifted to ℤ by canonicality.
  have hc2 : (envAt t 0).loc FACT_COMMITMENT = (envAt t 0).pub PI_FACT_COMMITMENT := by
    have h := hsat.rowConstraints 0 h0 c2FactPin mem_c2
    rw [hfirst] at h
    simp only [c2FactPin, VmConstraint2.holdsAt, holdsVm_piFirst_true] at h
    obtain ⟨k, hk⟩ := h.dvd
    omega
  -- C3 : slot identity gate (mod-p) lifted to ℤ by canonicality.
  have hc3 : (envAt t 0).loc SLOT_A = (envAt t 0).loc INPUT := by
    have h := hsat.rowConstraints 0 h0 c3SlotGate mem_c3
    rw [hlast] at h
    simp only [c3SlotGate, VmConstraint2.holdsAt, holdsVm_gate_false] at h
    have hkey : c3Body.eval (envAt t 0).loc
        = (envAt t 0).loc SLOT_A - (envAt t 0).loc INPUT := by
      simp only [c3Body, EmittedExpr.eval]; ring
    rw [hkey, Int.modEq_zero_iff_dvd] at h
    obtain ⟨k, hk⟩ := h
    omega
  -- C5 : diff gate (mod-p) lifted to ℤ by the low-half window (wrap-free subtraction).
  have hc5 : (envAt t 0).loc DIFF = (envAt t 0).loc SLOT_A - (envAt t 0).loc THRESHOLD := by
    have h := hsat.rowConstraints 0 h0 c5DiffGate mem_c5
    rw [hlast] at h
    simp only [c5DiffGate, VmConstraint2.holdsAt, holdsVm_gate_false] at h
    have hkey : c5Body.eval (envAt t 0).loc
        = (envAt t 0).loc DIFF - (envAt t 0).loc SLOT_A + (envAt t 0).loc THRESHOLD := by
      simp only [c5Body, EmittedExpr.eval]; ring
    rw [hkey, Int.modEq_zero_iff_dvd] at h
    obtain ⟨k, hk⟩ := h
    omega
  exact ⟨by omega, by omega, hc2⟩

/-! ## §5b — THE VALUE↔FACT WELD (held forgery #2): the committed fact carries the proven value. -/

/-- **`predicateGe_fact_opens_to_input`** — from the two in-circuit Poseidon2 chip lookups (against a
SOUND chip table, the NAMED carrier), the public fact commitment `pub PI_FACT_COMMITMENT` — the value a
verifier binds to a trusted credential — equals, in the genuine Poseidon2 `hash`, the DOUBLE hash of a
fact whose value slot is the SAME `INPUT` column the `≥` relation is proved about. So a satisfying
proof cannot name a fact commitment whose value differs from the value it proves about — exactly the
decoupling held forgery #2 exploited. -/
theorem predicateGe_fact_opens_to_input {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hlen : 2 ≤ t.rows.length)
    (hsat : Satisfied2 hash predicateGeDesc minit mfin maddrs t)
    (hcanon : GeCanon t) :
    (envAt t 0).pub PI_FACT_COMMITMENT
      = hash [hash [(envAt t 0).loc PREDICATE_SYM, (envAt t 0).loc INPUT,
                    (envAt t 0).loc TERM1, (envAt t 0).loc TERM2, 0, FACT_MARK, 1],
              (envAt t 0).loc STATE_ROOT, (envAt t 0).loc BLINDING, 0] := by
  obtain ⟨_, _, _, hcFC, _, hcPIFC⟩ := hcanon
  have h0 : 0 < t.rows.length := by omega
  have hc2 : (envAt t 0).loc FACT_COMMITMENT = (envAt t 0).pub PI_FACT_COMMITMENT := by
    have h := hsat.rowConstraints 0 h0 c2FactPin mem_c2
    rw [show ((0 : Nat) == 0) = true from rfl] at h
    simp only [c2FactPin, VmConstraint2.holdsAt, holdsVm_piFirst_true] at h
    obtain ⟨k, hk⟩ := h.dvd
    omega
  have hlF := hsat.rowConstraints 0 h0 factHashLookup mem_factHash
  simp only [VmConstraint2.holdsAt, factHashLookup, Lookup.holdsAt] at hlF
  have hfh := chip_lookup_sound hash (t.tf .poseidon2) hChip (envAt t 0).loc
    [.var PREDICATE_SYM, .var INPUT, .var TERM1, .var TERM2, .const 0, .const FACT_MARK, .const 1]
    FACT_HASH FACTHASH_LANES (by decide) hlF
  simp only [List.map_cons, List.map_nil, EmittedExpr.eval] at hfh
  have hlC := hsat.rowConstraints 0 h0 factCommitLookup mem_factCommit
  simp only [VmConstraint2.holdsAt, factCommitLookup, Lookup.holdsAt] at hlC
  have hfc := chip_lookup_sound hash (t.tf .poseidon2) hChip (envAt t 0).loc
    [.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0] FACT_COMMITMENT FACTCOMMIT_LANES
    (by decide) hlC
  simp only [List.map_cons, List.map_nil, EmittedExpr.eval] at hfc
  rw [← hc2, hfc, hfh]

/-- **THE WELD BITES (value ≠ committed value ⟹ REJECT).** Under Poseidon2 collision resistance —
here injectivity of the fact double-hash in its value slot — a proof whose fact witnesses match a
trusted credential of value `v0` but whose proved `INPUT ≠ v0` CANNOT satisfy the descriptor. The
honest Lean face of the emit-gate forge probe `forge_committed_value_neq_fact_rejects`. -/
theorem predicateGe_value_forge_rejected {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hlen : 2 ≤ t.rows.length) (hcanon : GeCanon t) (v0 : ℤ)
    (hcred : (envAt t 0).pub PI_FACT_COMMITMENT
      = hash [hash [(envAt t 0).loc PREDICATE_SYM, v0, (envAt t 0).loc TERM1,
                    (envAt t 0).loc TERM2, 0, FACT_MARK, 1],
              (envAt t 0).loc STATE_ROOT, (envAt t 0).loc BLINDING, 0])
    (hinj : ∀ a b : ℤ,
      hash [hash [(envAt t 0).loc PREDICATE_SYM, a, (envAt t 0).loc TERM1,
                  (envAt t 0).loc TERM2, 0, FACT_MARK, 1],
            (envAt t 0).loc STATE_ROOT, (envAt t 0).loc BLINDING, 0]
        = hash [hash [(envAt t 0).loc PREDICATE_SYM, b, (envAt t 0).loc TERM1,
                  (envAt t 0).loc TERM2, 0, FACT_MARK, 1],
                (envAt t 0).loc STATE_ROOT, (envAt t 0).loc BLINDING, 0] → a = b)
    (hforge : (envAt t 0).loc INPUT ≠ v0) :
    ¬ Satisfied2 hash predicateGeDesc minit mfin maddrs t := by
  intro hsat
  have hopen := predicateGe_fact_opens_to_input hChip hlen hsat hcanon
  exact hforge (hinj _ _ (hopen.symm.trans hcred))

/-! ## §6 — Non-vacuity: a concrete satisfying witness, an honest below-threshold run that fails. -/

/-- A row from an explicit column-prefix list (off-the-end = 0). -/
def rowOf (cols : List ℤ) : Assignment := fun i => cols.getD i 0

/-- The abstract hash never enters the range/gate denotation; the value↔fact weld's two chip lookups
land in the zero-hash chip table below, so under `hash0 = fun _ => 0` the fact-hash / fact-commitment
columns are `0`. -/
def hash0 : List ℤ → ℤ := fun _ => 0

/-- The honest satisfying assignment: `value = 100 ≥ threshold = 40`, slot-A copies the input, and the
range-proved `diff = value − threshold = 60 ∈ [0, 2^29)`. The value↔fact weld columns are `0` (their
chip digests are `hash0 _ = 0`), with `INPUT` feeding the arity-7 fact-hash absorb. Columns
`[INPUT, SLOT_A, THRESHOLD, DIFF, FACT_COMMITMENT, PREDICATE_SYM, TERM1, TERM2, STATE_ROOT, FACT_HASH]`
then the two chip lane groups (all `0`). -/
def geAsg : Assignment := rowOf [100, 100, 40, 60, 0]

/-- The public inputs: `PI_THRESHOLD = 40`, `PI_FACT_COMMITMENT = 0` (the zero-hash fact commitment). -/
def gePub : Assignment := rowOf [40, 0]

/-- The witness trace family carries the FAITHFUL range table `rangeRows 29` AND the Poseidon2 chip
table with the two genuine `chipRow`s the weld lookups absorb (arity-7 fact-hash over `INPUT = 100`,
arity-2 fact-commitment); every other table is empty. Reused by the below-threshold failing witness. -/
def geTf : TraceFamily
  | TableId.range => rangeRows DIFF_BITS
  | TableId.poseidon2 =>
      [chipRow hash0 [0, 100, 0, 0, 0, FACT_MARK, 1] (List.replicate 7 0),
       chipRow hash0 [0, 0, 0, 0] (List.replicate 7 0)]
  | _ => []

/-- The concrete 2-row satisfying run (row 0 active, row 1 the wrap row); both rows carry `geAsg`. -/
def geWitnessTrace : VmTrace := { rows := [geAsg, geAsg], pub := gePub, tf := geTf }

/-- The witness range table IS the faithful `rangeRows DIFF_BITS` — the carrier `hrange` this witness
discharges. PROVEN with `rangeRows` kept OPAQUE (`simp`, never `rfl`/`whnf`), so the 2^29-row table is
never enumerated; and stated at the EXACT `geWitnessTrace.tf .range` head so no `whnf` coercion fires
at the use sites. -/
theorem geWitnessTf_range : geWitnessTrace.tf .range = rangeRows DIFF_BITS := by
  simp only [geWitnessTrace, geTf]

/-- **The witness PROVABLY satisfies the emitted descriptor.** On both rows the range lookup holds by
`60 ∈ rangeRows 29` (via `range_row_mem_iff`, NOT enumeration); the two value↔fact weld chip lookups
land in the concrete Poseidon2 chip table (`gph*`/`gpc*`); on the active row 0 the two PI pins / two
gates hold, on the wrap row 1 they are vacuous; the memory legs are the empty-log balance. -/
theorem geWitness_satisfies :
    Satisfied2 hash0 predicateGeDesc (fun _ => 0) (fun _ => (0, 0)) [] geWitnessTrace where
  rowConstraints := by
    intro i hi c hc
    have h60 : ([(60 : ℤ)] : List ℤ) ∈ rangeRows DIFF_BITS :=
      (range_row_mem_iff 60 DIFF_BITS).mpr (by norm_num [DIFF_BITS])
    -- the two active/wrap-row guards, as literal Bools (so the `.gate` match collapses under `simp`).
    have g0 : ((0 : Nat) + 1 == geWitnessTrace.rows.length) = false := rfl
    have g1 : ((1 : Nat) + 1 == geWitnessTrace.rows.length) = true := rfl
    have hd0 : (envAt geWitnessTrace 0).loc DIFF = 60 := by decide
    have hd1 : (envAt geWitnessTrace 1).loc DIFF = 60 := by decide
    -- the range lookup holds on each row (via `range_row_mem_iff`, NOT table enumeration).
    have gl0 : Lookup.holdsAt geWitnessTrace.tf (envAt geWitnessTrace 0)
        ⟨TableId.range, [.var DIFF]⟩ := by
      simp only [Lookup.holdsAt, List.map_cons, List.map_nil, EmittedExpr.eval, geWitnessTf_range, hd0]
      exact h60
    have gl1 : Lookup.holdsAt geWitnessTrace.tf (envAt geWitnessTrace 1)
        ⟨TableId.range, [.var DIFF]⟩ := by
      simp only [Lookup.holdsAt, List.map_cons, List.map_nil, EmittedExpr.eval, geWitnessTf_range, hd1]
      exact h60
    -- the two weld chip lookups land in the concrete Poseidon2 chip table (decidable membership).
    have gph0 : Lookup.holdsAt geWitnessTrace.tf (envAt geWitnessTrace 0)
        ⟨TableId.poseidon2, chipLookupTuple [.var PREDICATE_SYM, .var INPUT, .var TERM1, .var TERM2,
          .const 0, .const FACT_MARK, .const 1] FACT_HASH FACTHASH_LANES⟩ := by
      simp only [Lookup.holdsAt, geWitnessTrace, geTf]; decide
    have gph1 : Lookup.holdsAt geWitnessTrace.tf (envAt geWitnessTrace 1)
        ⟨TableId.poseidon2, chipLookupTuple [.var PREDICATE_SYM, .var INPUT, .var TERM1, .var TERM2,
          .const 0, .const FACT_MARK, .const 1] FACT_HASH FACTHASH_LANES⟩ := by
      simp only [Lookup.holdsAt, geWitnessTrace, geTf]; decide
    have gpc0 : Lookup.holdsAt geWitnessTrace.tf (envAt geWitnessTrace 0)
        ⟨TableId.poseidon2, chipLookupTuple [.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0]
          FACT_COMMITMENT FACTCOMMIT_LANES⟩ := by
      simp only [Lookup.holdsAt, geWitnessTrace, geTf]; decide
    have gpc1 : Lookup.holdsAt geWitnessTrace.tf (envAt geWitnessTrace 1)
        ⟨TableId.poseidon2, chipLookupTuple [.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0]
          FACT_COMMITMENT FACTCOMMIT_LANES⟩ := by
      simp only [Lookup.holdsAt, geWitnessTrace, geTf]; decide
    have hi2 : i < 2 := hi
    clear hi
    simp only [predicateGeDesc] at hc
    -- gate / PI-pin teeth by `decide`; range lookups by `gl*`; the weld chip lookups by `gph*`/`gpc*`.
    interval_cases i <;>
      fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm,
        c1ThresholdPin, c2FactPin, c3SlotGate, c5DiffGate, c6RangeLookup,
        factHashLookup, factCommitLookup, g0, g1] <;>
      first
        | exact gl0
        | exact gl1
        | exact gph0
        | exact gph1
        | exact gpc0
        | exact gpc1
        | decide
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp only [predicateGeDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [memLog_pred] at hop; simp at hop
  memDisciplined := by rw [memLog_pred]; trivial
  memBalanced := by rw [memLog_pred]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_pred]; rfl
  mapTableFaithful := by rw [mapLog_pred]; rfl

/-- **The canonicality envelope is genuinely INHABITED** for the witness — value `100`, slot `100`,
threshold `40`, commitment `0` and the two PIs `40`/`0` are all small canonical field values (deep in
the low half). So the bridge does NOT rest on a vacuous range-check hypothesis. -/
theorem geWitness_canon : GeCanon geWitnessTrace := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- **The bridge FIRES on the witness (the true half of non-vacuity).** Feeding the concrete satisfying
trace + the faithful range table to `predicateGe_sat_imp_sem` recovers the genuine relation. -/
theorem geWitness_sem : ArithGeSem (envAt geWitnessTrace 0) :=
  predicateGe_sat_imp_sem (t := geWitnessTrace) geWitnessTf_range (by decide) geWitness_satisfies
    geWitness_canon

/-- The recovered semantic content is the concrete, non-trivial `40 ≤ 100` (threshold `≤` value) — not a
`True`/constant conclusion. -/
theorem geWitness_sem_concrete :
    (envAt geWitnessTrace 0).pub PI_THRESHOLD = 40
      ∧ (envAt geWitnessTrace 0).loc INPUT = 100
      ∧ (envAt geWitnessTrace 0).pub PI_THRESHOLD ≤ (envAt geWitnessTrace 0).loc INPUT := by
  refine ⟨by decide, by decide, geWitness_sem.ge⟩

/-- The concrete Poseidon2 chip table is genuinely SOUND for `hash0` (each row is a real `chipRow`) —
so the weld's named carrier `ChipTableSound` is realizable, not merely assumed. -/
theorem geChipSound : ChipTableSound hash0 (geWitnessTrace.tf .poseidon2) := by
  intro r hr
  simp only [geWitnessTrace, geTf, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h
  · exact ⟨[0, 100, 0, 0, 0, FACT_MARK, 1], List.replicate 7 0, by decide, by decide, h⟩
  · exact ⟨[0, 0, 0, 0], List.replicate 7 0, by decide, by decide, h⟩

/-- **The value↔fact WELD leg FIRES on the witness (non-vacuously).** Against the sound chip table, the
public fact commitment opens, in the genuine `hash0`, to the double hash of a fact whose value slot is
exactly the proved `INPUT = 100` — the held-forgery-#2 binding, derived not assumed. -/
theorem geWitness_fact_opens :
    (envAt geWitnessTrace 0).pub PI_FACT_COMMITMENT
      = hash0 [hash0 [(envAt geWitnessTrace 0).loc PREDICATE_SYM, (envAt geWitnessTrace 0).loc INPUT,
                (envAt geWitnessTrace 0).loc TERM1, (envAt geWitnessTrace 0).loc TERM2,
                0, FACT_MARK, 1], (envAt geWitnessTrace 0).loc STATE_ROOT,
                (envAt geWitnessTrace 0).loc BLINDING, 0] :=
  predicateGe_fact_opens_to_input (t := geWitnessTrace) geChipSound (by decide) geWitness_satisfies
    geWitness_canon

/-- The HONEST below-threshold attempt: `value = 30 < threshold = 40`, slot-A copies the input, and the
diff is the genuine `value − threshold = −10` (so C3 and C5 both HOLD — this is not a malformed trace,
it is an honest prover with a below-threshold value). Only the C6 range tooth can reject it. -/
def geBadAsg : Assignment := rowOf [30, 30, 40, -10, 7]

/-- The below-threshold trace, against the SAME faithful range table `rangeRows 29`. -/
def geBadTrace : VmTrace := { rows := [geBadAsg, geBadAsg], pub := gePub, tf := geTf }

/-- The below-threshold trace's range table is the faithful `rangeRows DIFF_BITS` (opaque `rangeRows`). -/
theorem geBadTf_range : geBadTrace.tf .range = rangeRows DIFF_BITS := by
  simp only [geBadTrace, geTf]

/-- **The honest below-threshold run PROVABLY FAILS the hypothesis (the false half of non-vacuity).**
The C6 range tooth forces `diff ∈ [0, 2^29)`, but the honest diff of a `value < threshold` is `−10 < 0`,
so no `Satisfied2` witness exists — the descriptor's range tooth is exactly what rejects a
below-threshold value. -/
theorem geBad_not_satisfies :
    ¬ Satisfied2 hash0 predicateGeDesc (fun _ => 0) (fun _ => (0, 0)) [] geBadTrace := by
  intro h
  have h0 : (0 : Nat) < geBadTrace.rows.length := by decide
  have hrc := h.rowConstraints 0 h0 c6RangeLookup mem_c6
  simp only [c6RangeLookup, VmConstraint2.holdsAt] at hrc
  have hv := lookup_replaces_range DIFF_BITS geBadTrace.tf geBadTf_range (envAt geBadTrace 0) DIFF hrc
  simp only [VmRange.holds] at hv
  have hx : (envAt geBadTrace 0).loc DIFF = -10 := by decide
  rw [hx] at hv
  exact absurd hv.1 (by decide)

/-! ## §7 — Axiom tripwires. -/

#assert_axioms predicateGe_sat_imp_sem
#assert_axioms predicateGe_fact_opens_to_input
#assert_axioms predicateGe_value_forge_rejected
#assert_axioms geWitness_satisfies
#assert_axioms geWitness_canon
#assert_axioms geChipSound
#assert_axioms geWitness_fact_opens
#assert_axioms geWitness_sem
#assert_axioms geWitness_sem_concrete
#assert_axioms geBad_not_satisfies

end Dregg2.Circuit.Emit.PredicatesArithmeticRefine
