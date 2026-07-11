/-
# Dregg2.Circuit.Emit.FoldRefine — the WHOLE-DESCRIPTOR functional-correctness bridge for the
attenuation FOLD-step descriptor (`FoldEmit.foldDesc`, "dregg-fold-step-v2").

## What Rung 0 already gave, and what THIS file adds

`FoldEmit.lean` byte-pins `foldDesc` and proves the per-GATE teeth (`mrm_body_zero_iff`,
`root_trans_body_zero_iff`, `binary_body_zero_iff`, `removal_incr_body_zero_iff`) — each constraint
polynomial vanishes EXACTLY when its LOCAL relation holds. That is not yet a statement about what the
WHOLE descriptor computes.

The fold census carries `spec_status = NO_LEAN` for this family: no proven Lean semantic model of the
attenuation fold step exists. So this file is the **NO_LEAN** case — it FIRST authors the functional
RELATION (`FoldStepValid` : what a valid attenuation-fold trace means) and THEN proves the deployed
acceptance predicate `Satisfied2` refines it:

  `foldDesc_satisfied2_refines_foldStepValid`
    : `ChipTableSound hash (t.tf .poseidon2) → 0 < t.rows.length
       → Satisfied2 hash foldDesc minit mfin maddrs t → FoldStepValid hash t`

i.e. accept ⟹ genuine (SAT_IMPLIES_SEM, the soundness direction). The whole descriptor is composed:
the per-row binary/gate/window teeth of `FoldEmit` are combined with the first/last-row PI bindings and
the arity-7 Poseidon2 fact-hash chip-lookup soundness (`chip_lookup_sound`) to conclude, for an
accepting trace, that

  * every REMOVAL row certifies a genuine fact removal against the committed OLD root — membership root
    = old root, a valid hash flag, the FACT_HASH column IS the genuine Poseidon2 fact commitment, and
    the removal counter advances by one (`RemovalCertified`);
  * the first row pins the OLD / NEW accumulator roots to the public inputs;
  * the last (SUMMARY) row publishes `ROW_TYPE = 1`, the removal / check counts, and the root-transition
    hash to the public inputs.

## The NAMED carrier

The only crypto floor is the Poseidon2 chip-table soundness `ChipTableSound hash (t.tf .poseidon2)` — a
NAMED, realizable hypothesis (the deployed Poseidon2 chip AIR's own faithfulness), exactly the carrier
`EffectVmEmitBundleFold.fold_compress_is_hashed` and `AccumulatorOpenEmit` ride. It enters ONLY through
`DescriptorIR2.chip_lookup_sound`.

## Non-vacuity (the anti-scar proof, IN THIS FILE)

* `satTrace_satisfied2` — a CONCRETE one-row summary trace GENUINELY satisfies `Satisfied2 hash foldDesc
  …`, so the bridge hypothesis is inhabited (not `P → P`, not an unsatisfiable premise).
* `satTrace_chipSound` — the SAME trace's Poseidon2 table is `ChipTableSound` (its row is a genuine
  `chipRow`), so the FULL hypothesis conjunction is jointly satisfiable.
* `satTrace_foldStepValid` — the bridge applied to that trace yields `FoldStepValid`, whose fields are
  real equations there (`ROW_TYPE = 1`, the PI publications), so the conclusion is reached from
  genuinely-satisfiable hypotheses.
* `badTrace_not_satisfied2` — a CONCRETE trace whose last row carries `ROW_TYPE = 2` is REJECTED by
  `Satisfied2` (the summary-boundary constraint bites), so the accept-set genuinely separates.

## The field-faithful denotation (mod-p) and the canonicality envelope

`VmConstraint.holdsVm` / `WindowConstraint.holdsAt` pin gate bodies only `≡ 0 [ZMOD p]`
(`p = 2013265921`, BabyBear) — the DEPLOYED field constraint, not an ℤ equality. Reading the ℤ
conclusions of `FoldStepValid` back off the congruences needs the deployed range-check invariant
carried as the EXPLICIT hypothesis `FoldTraceCanon` (§1.5): the eight semantic fold columns
canonical in `[0, p)` on every row, and the five bound public inputs canonical. Non-vacuous:
`satTrace_canon` / `goodTrace_canon` inhabit the envelope concretely. The hash-site lookup
(`factCommitmentGenuine`) is UNAFFECTED — `Lookup.holdsAt` is table membership, an ℤ equality.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY through the named
`ChipTableSound` carrier (as a hypothesis, via `chip_lookup_sound`). NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.FoldEmit
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.DecideSatisfied2

namespace Dregg2.Circuit.Emit.FoldRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmConstraint VmRowEnv holdsVm_boundaryLast_true holdsVm_piFirst_true holdsVm_piLast_true
   holdsVm_gate_of_notLast)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup WindowConstraint TableId TraceFamily VmTrace
   Satisfied2 envAt ChipTableSound chip_lookup_sound chipLookupTuple chipRow siteLaneCols
   CHIP_RATE CHIP_OUT_LANES)
open Dregg2.Circuit.Emit.FoldEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (pPrimeInt gate_modEq_iff)
open Dregg2.Crypto

set_option autoImplicit false

/-! ## §1 — The functional-correctness RELATION (the missing NO_LEAN semantic model).

`RemovalCertified` / `FoldStepValid` are the clean Lean statement of WHAT the attenuation fold circuit
is meant to compute — the functional spec the descriptor is proven to refine. They are stated over the
trace's row windows (`envAt`) so they weld directly to the deployed `Satisfied2` denotation. -/

/-- **`RemovalCertified hash env`** — the genuine semantic content of ONE removal row (`ROW_TYPE = 0`)
of an attenuation fold, read off its row window `env` (current row `loc`, next row `nxt`):

  * the fact was checked against the committed OLD accumulator root (`MEMBERSHIP_ROOT = OLD_ROOT`);
  * the row carries a valid hash flag (`HASH_VALID = 1`);
  * the FACT_HASH column IS the genuine Poseidon2 fact commitment of the fact columns
    `hash [pred, t0, t1, t2, 0, 0xFACF, 1]` (`0xFACF = 64207`, the `FACT_MARK` domain tag);
  * the removal counter advances by exactly one across the step
    (`nxt REMOVAL_COUNT = loc REMOVAL_COUNT_PLUS_ONE`). -/
structure RemovalCertified (hash : List ℤ → ℤ) (env : VmRowEnv) : Prop where
  membershipAgainstOldRoot : env.loc MEMBERSHIP_ROOT = env.loc OLD_ROOT
  hashValid : env.loc HASH_VALID = 1
  factCommitmentGenuine :
    env.loc FACT_HASH
      = hash [env.loc FACT_PRED, env.loc FACT_TERM0, env.loc FACT_TERM1, env.loc FACT_TERM2,
              0, 64207, 1]
  removalCountAdvances : env.nxt REMOVAL_COUNT = env.loc REMOVAL_COUNT_PLUS_ONE

/-- **`FoldStepValid hash t`** — the functional spec of the attenuation FOLD step: `t` is a valid fold
from a committed OLD root to a committed NEW root, removing a set of facts and publishing the removal /
check counts and the root-transition hash to the public inputs. Every row is a removal row or the
summary row; every removal row certifies a genuine removal; the roots are pinned to the PIs on the
first row; the summary (last) row publishes the outputs. -/
structure FoldStepValid (hash : List ℤ → ℤ) (t : VmTrace) : Prop where
  rowTypeBinary : ∀ i, i < t.rows.length →
    (envAt t i).loc ROW_TYPE = 0 ∨ (envAt t i).loc ROW_TYPE = 1
  removalsCertified : ∀ i, i < t.rows.length → (envAt t i).loc ROW_TYPE = 0 →
    RemovalCertified hash (envAt t i)
  oldRootIsPublicInput : (envAt t 0).loc OLD_ROOT = t.pub PI_OLD_ROOT
  newRootIsPublicInput : (envAt t 0).loc NEW_ROOT = t.pub PI_NEW_ROOT
  summaryRowIsSummary : (envAt t (t.rows.length - 1)).loc ROW_TYPE = 1
  removalCountPublished :
    (envAt t (t.rows.length - 1)).loc REMOVAL_COUNT = t.pub PI_REMOVAL_COUNT
  checkCountPublished :
    (envAt t (t.rows.length - 1)).loc CHECK_COUNT = t.pub PI_CHECK_COUNT
  transitionHashPublished :
    (envAt t (t.rows.length - 1)).loc MEMBERSHIP_ROOT = t.pub PI_TRANSITION_HASH

/-! ## §1.5 — the canonicality envelope: reading the ℤ spec back off the mod-`p` congruences.

The deployed AIR constrains cells only as BabyBear field elements; the range-check invariant (every
semantic cell and bound public input a canonical representative in `[0, p)`) is what makes the ℤ
reading honest. Carried as the EXPLICIT hypothesis `FoldTraceCanon` — inhabited concretely by
`satTrace_canon` / `goodTrace_canon` (§3/§4), so the envelope is not vacuous. -/

/-- Canonical-representative predicate: the deployed range-check invariant `0 ≤ x < p`. -/
def CanonCell (x : ℤ) : Prop := 0 ≤ x ∧ x < 2013265921

/-- Two canonical representatives congruent mod `p` are EQUAL (`p ∣ residual` with
`residual ∈ (−p, p)` collapses to `0`). -/
theorem eq_of_modEq_of_canon {a b : ℤ} (h : a ≡ b [ZMOD 2013265921])
    (ha : CanonCell a) (hb : CanonCell b) : a = b := by
  obtain ⟨ha0, ha1⟩ := ha; obtain ⟨hb0, hb1⟩ := hb
  obtain ⟨k, hk⟩ := h.dvd
  omega

/-- A canonical cell whose booleanity gate vanishes mod `p` IS `0` or `1` over ℤ: primality splits
`p ∣ x·(x−1)`, and canonicality collapses each factor. -/
theorem binary_modEq_cases {x : ℤ} (h : x * (x + -1) ≡ 0 [ZMOD 2013265921])
    (hc : CanonCell x) : x = 0 ∨ x = 1 := by
  obtain ⟨h0, h1⟩ := hc
  have hd : (2013265921 : ℤ) ∣ x * (x + -1) := Int.modEq_zero_iff_dvd.mp h
  rcases pPrimeInt.dvd_mul.mp hd with hx | hx
  · obtain ⟨k, hk⟩ := hx; left; omega
  · obtain ⟨k, hk⟩ := hx; right; omega

/-- **The fold canonicality envelope.** The eight semantic fold columns are canonical on every row,
and the five bound public inputs are canonical — the deployed range-check invariant, threaded
through the whole-descriptor bridge. (`FACT_HASH` and the fact/lane columns are NOT here: the
fact-hash clause rides the lookup, an exact table-membership equality.) -/
structure FoldTraceCanon (t : VmTrace) : Prop where
  rowType : ∀ i, i < t.rows.length → CanonCell ((envAt t i).loc ROW_TYPE)
  membershipRoot : ∀ i, i < t.rows.length → CanonCell ((envAt t i).loc MEMBERSHIP_ROOT)
  oldRoot : ∀ i, i < t.rows.length → CanonCell ((envAt t i).loc OLD_ROOT)
  newRoot : ∀ i, i < t.rows.length → CanonCell ((envAt t i).loc NEW_ROOT)
  hashValid : ∀ i, i < t.rows.length → CanonCell ((envAt t i).loc HASH_VALID)
  removalCount : ∀ i, i < t.rows.length → CanonCell ((envAt t i).loc REMOVAL_COUNT)
  removalCountPlusOne : ∀ i, i < t.rows.length → CanonCell ((envAt t i).loc REMOVAL_COUNT_PLUS_ONE)
  checkCount : ∀ i, i < t.rows.length → CanonCell ((envAt t i).loc CHECK_COUNT)
  pubOldRoot : CanonCell (t.pub PI_OLD_ROOT)
  pubNewRoot : CanonCell (t.pub PI_NEW_ROOT)
  pubRemovalCount : CanonCell (t.pub PI_REMOVAL_COUNT)
  pubCheckCount : CanonCell (t.pub PI_CHECK_COUNT)
  pubTransitionHash : CanonCell (t.pub PI_TRANSITION_HASH)

/-! ## §2 — THE BRIDGE: the whole-descriptor `Satisfied2` refines `FoldStepValid` (SAT_IMPLIES_SEM). -/

/-- **`foldDesc_satisfied2_refines_foldStepValid` — THE WHOLE-DESCRIPTOR FUNCTIONAL-REFINEMENT BRIDGE.**
Against the named Poseidon2 chip-soundness carrier, any trace ACCEPTED by the deployed fold descriptor
(`Satisfied2 hash foldDesc …`) satisfies the authored functional spec `FoldStepValid hash t`. Composes
`FoldEmit`'s per-gate teeth, the first/last-row PI bindings + boundary, and the arity-7 fact-hash
chip-lookup soundness over the WHOLE constraint list. -/
theorem foldDesc_satisfied2_refines_foldStepValid
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hlen : 0 < t.rows.length)
    (hcanon : FoldTraceCanon t)
    (h : Satisfied2 hash foldDesc minit mfin maddrs t) :
    FoldStepValid hash t := by
  have hrow := h.rowConstraints
  have hLlast : t.rows.length - 1 + 1 = t.rows.length := Nat.sub_add_cancel hlen
  have hLlt : t.rows.length - 1 < t.rows.length := by omega
  have hLb : (t.rows.length - 1 + 1 == t.rows.length) = true := by rw [hLlast]; simp
  refine
    { rowTypeBinary := ?_, removalsCertified := ?_, oldRootIsPublicInput := ?_,
      newRootIsPublicInput := ?_, summaryRowIsSummary := ?_, removalCountPublished := ?_,
      checkCountPublished := ?_, transitionHashPublished := ?_ }
  · -- rowTypeBinary: last row via the boundary (≡ 1 mod p, collapsed by canonicality), non-last
    -- via the binary gate (mod-p booleanity + primality + canonicality ⇒ ∈ {0,1} over ℤ).
    intro i hi
    by_cases hlast : i + 1 = t.rows.length
    · have hb := hrow i hi (VmConstraint2.base (.boundary .last lastSummaryBody))
        (by simp [foldDesc, foldConstraints])
      simp only [VmConstraint2.holdsAt] at hb
      rw [show (i + 1 == t.rows.length) = true from by rw [hlast]; simp,
          holdsVm_boundaryLast_true] at hb
      have hb' := (gate_modEq_iff (a := (envAt t i).loc ROW_TYPE) (b := 1)
        (by simp only [lastSummaryBody, EmittedExpr.eval]; ring)).mp hb
      exact Or.inr (eq_of_modEq_of_canon hb' (hcanon.rowType i hi) ⟨by norm_num, by norm_num⟩)
    · have hlf : (i + 1 == t.rows.length) = false := by
        simp only [beq_eq_false_iff_ne]; exact hlast
      have hg := hrow i hi (VmConstraint2.base (.gate (binaryBody ROW_TYPE)))
        (by simp [foldDesc, foldConstraints])
      simp only [VmConstraint2.holdsAt] at hg
      rw [holdsVm_gate_of_notLast _ _ _ _ hlf] at hg
      simp only [binaryBody, EmittedExpr.eval] at hg
      exact binary_modEq_cases hg (hcanon.rowType i hi)
  · -- removalsCertified.
    intro i hi hrt0
    -- A removal row is not the last row (the last row is the summary row, ROW_TYPE = 1).
    have hnotlast : i + 1 ≠ t.rows.length := by
      intro heq
      have hb := hrow i hi (VmConstraint2.base (.boundary .last lastSummaryBody))
        (by simp [foldDesc, foldConstraints])
      simp only [VmConstraint2.holdsAt] at hb
      rw [show (i + 1 == t.rows.length) = true from by rw [heq]; simp,
          holdsVm_boundaryLast_true] at hb
      simp only [lastSummaryBody, EmittedExpr.eval, hrt0] at hb
      obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp hb
      omega
    have hlf : (i + 1 == t.rows.length) = false := by
      simp only [beq_eq_false_iff_ne]; exact hnotlast
    refine
      { membershipAgainstOldRoot := ?_, hashValid := ?_, factCommitmentGenuine := ?_,
        removalCountAdvances := ?_ }
    · -- membership_root_matches gate ⇒ MEMBERSHIP_ROOT ≡ OLD_ROOT mod p on a removal row
      -- (`ROW_TYPE = 0` kills the summary factor), collapsed to ℤ by canonicality.
      have hg := hrow i hi (VmConstraint2.base (.gate mrmBody))
        (by simp [foldDesc, foldConstraints])
      simp only [VmConstraint2.holdsAt] at hg
      rw [holdsVm_gate_of_notLast _ _ _ _ hlf] at hg
      have hg' := (gate_modEq_iff (a := (envAt t i).loc MEMBERSHIP_ROOT)
        (b := (envAt t i).loc OLD_ROOT)
        (by simp only [mrmBody, EmittedExpr.eval, hrt0]; ring)).mp hg
      exact eq_of_modEq_of_canon hg' (hcanon.membershipRoot i hi) (hcanon.oldRoot i hi)
    · -- removal_hash_required gate ⇒ HASH_VALID ≡ 1 mod p on a removal row, collapsed by
      -- canonicality.
      have hg := hrow i hi (VmConstraint2.base (.gate removalHashBody))
        (by simp [foldDesc, foldConstraints])
      simp only [VmConstraint2.holdsAt] at hg
      rw [holdsVm_gate_of_notLast _ _ _ _ hlf] at hg
      have hg' := (gate_modEq_iff (a := (1 : ℤ)) (b := (envAt t i).loc HASH_VALID)
        (by simp only [removalHashBody, EmittedExpr.eval, hrt0]; ring)).mp hg
      exact (eq_of_modEq_of_canon hg' ⟨by norm_num, by norm_num⟩ (hcanon.hashValid i hi)).symm
    · -- the arity-7 fact-hash chip lookup ⇒ FACT_HASH is the genuine Poseidon2 fact commitment.
      have hlk := hrow i hi factHashLookup (by simp [foldDesc, foldConstraints])
      simp only [factHashLookup, VmConstraint2.holdsAt, Lookup.holdsAt] at hlk
      have hkey := chip_lookup_sound hash (t.tf .poseidon2) hChip (envAt t i).loc
        [.var FACT_PRED, .var FACT_TERM0, .var FACT_TERM1, .var FACT_TERM2,
         .const 0, .const 64207, .const 1] FACT_HASH (siteLaneCols FACT_LANE_BASE)
        (by decide) hlk
      simpa [EmittedExpr.eval] using hkey
    · -- removal_count_increment window ⇒ the counter advances by one on a removal row
      -- (mod p from the window, collapsed by canonicality of both counter cells; the `nxt`
      -- cell is row `i+1`'s REMOVAL_COUNT, in range because a removal row is non-last).
      have hw := hrow i hi (VmConstraint2.windowGate ⟨removalIncrBody, true⟩)
        (by simp [foldDesc, foldConstraints])
      simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt] at hw
      have hz := hw hlf
      have hg' := (gate_modEq_iff (a := (envAt t i).nxt REMOVAL_COUNT)
        (b := (envAt t i).loc REMOVAL_COUNT_PLUS_ONE)
        (by simp only [removalIncrBody, Dregg2.Circuit.DescriptorIR2.WindowExpr.eval, hrt0]
            ring)).mp hz
      have hi1 : i + 1 < t.rows.length := by omega
      exact eq_of_modEq_of_canon hg' (hcanon.removalCount (i + 1) hi1)
        (hcanon.removalCountPlusOne i hi)
  · -- oldRootIsPublicInput: first-row PI pin (mod p, collapsed by canonicality of both sides).
    have hp := hrow 0 hlen (VmConstraint2.base (.piBinding .first OLD_ROOT PI_OLD_ROOT))
      (by simp [foldDesc, foldConstraints])
    simp only [VmConstraint2.holdsAt] at hp
    rw [show ((0 : Nat) == 0) = true from rfl, holdsVm_piFirst_true] at hp
    exact eq_of_modEq_of_canon hp (hcanon.oldRoot 0 hlen) hcanon.pubOldRoot
  · -- newRootIsPublicInput: first-row PI pin (mod p, collapsed by canonicality of both sides).
    have hp := hrow 0 hlen (VmConstraint2.base (.piBinding .first NEW_ROOT PI_NEW_ROOT))
      (by simp [foldDesc, foldConstraints])
    simp only [VmConstraint2.holdsAt] at hp
    rw [show ((0 : Nat) == 0) = true from rfl, holdsVm_piFirst_true] at hp
    exact eq_of_modEq_of_canon hp (hcanon.newRoot 0 hlen) hcanon.pubNewRoot
  · -- summaryRowIsSummary: last-row boundary ⇒ ROW_TYPE ≡ 1 mod p, collapsed by canonicality.
    have hb := hrow (t.rows.length - 1) hLlt
      (VmConstraint2.base (.boundary .last lastSummaryBody))
      (by simp [foldDesc, foldConstraints])
    simp only [VmConstraint2.holdsAt] at hb
    rw [hLb, holdsVm_boundaryLast_true] at hb
    have hb' := (gate_modEq_iff (a := (envAt t (t.rows.length - 1)).loc ROW_TYPE) (b := 1)
      (by simp only [lastSummaryBody, EmittedExpr.eval]; ring)).mp hb
    exact eq_of_modEq_of_canon hb' (hcanon.rowType _ hLlt) ⟨by norm_num, by norm_num⟩
  · -- removalCountPublished: last-row PI binding (mod p, collapsed by canonicality).
    have hp := hrow (t.rows.length - 1) hLlt
      (VmConstraint2.base (.piBinding .last REMOVAL_COUNT PI_REMOVAL_COUNT))
      (by simp [foldDesc, foldConstraints])
    simp only [VmConstraint2.holdsAt] at hp
    rw [hLb, holdsVm_piLast_true] at hp
    exact eq_of_modEq_of_canon hp (hcanon.removalCount _ hLlt) hcanon.pubRemovalCount
  · -- checkCountPublished: last-row PI binding (mod p, collapsed by canonicality).
    have hp := hrow (t.rows.length - 1) hLlt
      (VmConstraint2.base (.piBinding .last CHECK_COUNT PI_CHECK_COUNT))
      (by simp [foldDesc, foldConstraints])
    simp only [VmConstraint2.holdsAt] at hp
    rw [hLb, holdsVm_piLast_true] at hp
    exact eq_of_modEq_of_canon hp (hcanon.checkCount _ hLlt) hcanon.pubCheckCount
  · -- transitionHashPublished: last-row PI binding (mod p, collapsed by canonicality).
    have hp := hrow (t.rows.length - 1) hLlt
      (VmConstraint2.base (.piBinding .last MEMBERSHIP_ROOT PI_TRANSITION_HASH))
      (by simp [foldDesc, foldConstraints])
    simp only [VmConstraint2.holdsAt] at hp
    rw [hLb, holdsVm_piLast_true] at hp
    exact eq_of_modEq_of_canon hp (hcanon.membershipRoot _ hLlt) hcanon.pubTransitionHash

/-! ## §3 — Non-vacuity: a CONCRETE satisfying witness (`Satisfied2` inhabited) and a CONCRETE failing
one (`Satisfied2` bites). -/

/-- The genuine Poseidon2 fact-hash inputs of the all-zero fact `(pred, t0, t1, t2) = (0,0,0,0)`:
`[0, 0, 0, 0, 0, 0xFACF, 1]` (the terms + the `0 / 0xFACF / 1` domain tags). -/
def satInputs : List ℤ := [0, 0, 0, 0, 0, 64207, 1]

/-- The satisfying SUMMARY row: `ROW_TYPE = 1`, `FACT_HASH = hash satInputs` (so the fact-hash lookup
matches a GENUINE chip row), every other column `0` (so every PI binding — all pinned to the all-zero
public inputs — holds). -/
def satRow (hash : List ℤ → ℤ) : Assignment :=
  fun i => if i = FACT_HASH then hash satInputs
           else if i = ROW_TYPE then 1 else 0

/-- The evaluated fact-hash lookup tuple (identical to `foldDesc`'s `factHashLookup` tuple). -/
def factTupleE : List EmittedExpr :=
  chipLookupTuple
    [.var FACT_PRED, .var FACT_TERM0, .var FACT_TERM1, .var FACT_TERM2,
     .const 0, .const 64207, .const 1]
    FACT_HASH (siteLaneCols FACT_LANE_BASE)

/-- The one-row satisfying witness: a single summary row, all-zero public inputs, and a Poseidon2 table
carrying exactly the (genuine) fact-hash chip row. -/
def satTrace (hash : List ℤ → ℤ) : VmTrace :=
  { rows := [satRow hash]
  , pub  := fun _ => 0
  , tf   := fun tbl =>
      match tbl with
      | .poseidon2 => [factTupleE.map (·.eval (satRow hash))]
      | _ => [] }

/-- The single Poseidon2 table row IS a genuine `chipRow` — the fact commitment column carries the real
`hash satInputs`. This is what makes `satTrace`'s table `ChipTableSound`. -/
theorem satTable_row_is_chipRow (hash : List ℤ → ℤ) :
    factTupleE.map (·.eval (satRow hash))
      = chipRow hash satInputs ((siteLaneCols FACT_LANE_BASE).map (satRow hash)) := by
  have hins :
      ([.var FACT_PRED, .var FACT_TERM0, .var FACT_TERM1, .var FACT_TERM2,
        .const 0, .const 64207, .const 1] : List EmittedExpr).map (·.eval (satRow hash))
        = satInputs := by
    simp [satInputs, EmittedExpr.eval, satRow, FACT_PRED, FACT_TERM0, FACT_TERM1, FACT_TERM2,
      FACT_HASH, ROW_TYPE]
  have hfh : satRow hash FACT_HASH = hash satInputs := by simp [satRow]
  unfold factTupleE chipLookupTuple chipRow
  simp only [List.map_cons, List.map_append, Dregg2.Circuit.DescriptorIR2.map_eval_padToE,
    List.map_map, Function.comp_def, EmittedExpr.eval, hins, hfh]
  simp [satInputs]

theorem satTrace_chipSound (hash : List ℤ → ℤ) :
    ChipTableSound hash ((satTrace hash).tf .poseidon2) := by
  intro r hr
  have hrX : r = factTupleE.map (·.eval (satRow hash)) := by
    have hpo : (satTrace hash).tf .poseidon2 = [factTupleE.map (·.eval (satRow hash))] := rfl
    rw [hpo, List.mem_singleton] at hr; exact hr
  refine ⟨satInputs, (siteLaneCols FACT_LANE_BASE).map (satRow hash), ?_, ?_, ?_⟩
  · decide
  · simp [siteLaneCols]
  · rw [hrX]; exact satTable_row_is_chipRow hash

/-- **Non-vacuity (accept).** The concrete one-row summary trace GENUINELY satisfies the deployed
`Satisfied2 hash foldDesc …` — the bridge's hypothesis is inhabited. -/
theorem satTrace_satisfied2 (hash : List ℤ → ℤ) :
    Satisfied2 hash foldDesc (fun _ => 0) (fun _ => (0, 0)) [] (satTrace hash) := by
  have hloc : (envAt (satTrace hash) 0).loc = satRow hash := rfl
  have hpub : (envAt (satTrace hash) 0).pub = (fun _ : Nat => (0 : ℤ)) := rfl
  refine
    { rowConstraints := ?_, rowHashes := ?_, rowRanges := ?_, memAddrsNodup := ?_,
      memClosed := ?_, memDisciplined := ?_, memBalanced := ?_, memTableFaithful := ?_,
      mapTableFaithful := ?_ }
  · intro i hi c hc
    have hi0 : i = 0 := by
      have h1 : (satTrace hash).rows.length = 1 := rfl
      omega
    subst hi0
    rw [show ((0 : Nat) == 0) = true from rfl,
        show ((0 : Nat) + 1 == (satTrace hash).rows.length) = true from rfl]
    rw [show foldDesc.constraints = foldConstraints from rfl] at hc
    fin_cases hc
    · exact True.intro
    · exact True.intro
    · exact True.intro
    · exact True.intro
    · exact List.mem_singleton.mpr rfl
    · intro _; rw [hloc, hpub]; simp [satRow, OLD_ROOT, FACT_HASH, ROW_TYPE]
    · intro hcon; exact Bool.noConfusion hcon
    · intro _; rw [hloc, hpub]; simp [satRow, NEW_ROOT, FACT_HASH, ROW_TYPE]
    · intro hcon; exact Bool.noConfusion hcon
    · intro hcon; exact Bool.noConfusion hcon
    -- (A) removal_count_plus_one gate: vacuous on the single (= last) row.
    · exact True.intro
    -- (C) removal_count_carry window (onTransition): vacuous on the last row.
    · intro hcon; exact Bool.noConfusion hcon
    -- (B) first-row REMOVAL_COUNT = 0 anchor: satRow's REMOVAL_COUNT is 0.
    · intro _; rw [hloc]; simp [firstRcBody, EmittedExpr.eval, satRow, REMOVAL_COUNT, FACT_HASH, ROW_TYPE]
    · intro _; rw [hloc, hpub]; simp [satRow, PI4_CARRIER, FACT_HASH, ROW_TYPE]
    · intro hcon; exact Bool.noConfusion hcon
    · exact True.intro
    · intro _; rw [hloc]; norm_num [lastSummaryBody, EmittedExpr.eval, satRow, ROW_TYPE, FACT_HASH]
    · intro _; rw [hloc, hpub]; simp [satRow, REMOVAL_COUNT, FACT_HASH, ROW_TYPE]
    · intro _; rw [hloc, hpub]; simp [satRow, CHECK_COUNT, FACT_HASH, ROW_TYPE]
    · intro _; rw [hloc, hpub]; simp [satRow, MEMBERSHIP_ROOT, FACT_HASH, ROW_TYPE]
  · intro i hi; exact trivial
  · intro i hi; simp [foldDesc]
  · exact List.nodup_nil
  · intro op hop
    rw [show Dregg2.Circuit.DescriptorIR2.memLog foldDesc (satTrace hash) = [] from rfl] at hop
    simp at hop
  · exact trivial
  · have hml : Dregg2.Circuit.DescriptorIR2.memLog foldDesc (satTrace hash) = [] := rfl
    rw [hml]
    simp [MemoryChecking.MemCheck, MemoryChecking.initSet, MemoryChecking.finalSet]
  · rfl
  · rfl

/-- Every non-`FACT_HASH` cell of the satisfying summary row is `0` or `1` — canonical. -/
theorem satRow_canon (hash : List ℤ → ℤ) {c : Nat} (hc : c ≠ FACT_HASH) :
    CanonCell (satRow hash c) := by
  unfold CanonCell satRow
  rw [if_neg hc]
  split <;> norm_num

/-- **The satisfying witness inhabits the canonicality envelope** — every enveloped cell is `0` or
`1` and every bound public input is `0`, all canonical representatives. The bridge's range-check
hypothesis is concretely satisfiable, not a vacuous guard. -/
theorem satTrace_canon (hash : List ℤ → ℤ) : FoldTraceCanon (satTrace hash) := by
  have hcell : ∀ (c : Nat), c ≠ FACT_HASH → ∀ i, i < (satTrace hash).rows.length →
      CanonCell ((envAt (satTrace hash) i).loc c) := by
    intro c hc i hi
    have hi0 : i = 0 := by
      have h1 : (satTrace hash).rows.length = 1 := rfl
      omega
    subst hi0
    exact satRow_canon hash hc
  have hpub : ∀ k : Nat, CanonCell ((satTrace hash).pub k) := fun k =>
    ⟨by norm_num [satTrace], by norm_num [satTrace]⟩
  exact ⟨hcell ROW_TYPE (by decide), hcell MEMBERSHIP_ROOT (by decide),
    hcell OLD_ROOT (by decide), hcell NEW_ROOT (by decide), hcell HASH_VALID (by decide),
    hcell REMOVAL_COUNT (by decide), hcell REMOVAL_COUNT_PLUS_ONE (by decide),
    hcell CHECK_COUNT (by decide), hpub _, hpub _, hpub _, hpub _, hpub _⟩

/-- **Non-vacuity (bridge capstone).** The bridge applied to the concrete satisfying witness yields the
functional spec — the conclusion is reached from genuinely-satisfiable hypotheses. -/
theorem satTrace_foldStepValid (hash : List ℤ → ℤ) :
    FoldStepValid hash (satTrace hash) :=
  foldDesc_satisfied2_refines_foldStepValid hash (fun _ => 0) (fun _ => (0, 0)) []
    (satTrace hash) (satTrace_chipSound hash) (by simp [satTrace]) (satTrace_canon hash)
    (satTrace_satisfied2 hash)

/-- The failing witness: a single row whose `ROW_TYPE = 2` (neither removal nor summary). -/
def badRow : Assignment := fun i => if i = ROW_TYPE then 2 else 0

def badTrace : VmTrace :=
  { rows := [badRow], pub := fun _ => 0, tf := fun _ => [] }

/-- **Non-vacuity (reject).** A last row carrying `ROW_TYPE = 2` is REJECTED by `Satisfied2` — the
summary-row boundary constraint (`ROW_TYPE = 1` on the last row) bites, so the accept-set genuinely
separates satisfying from violating witnesses. -/
theorem badTrace_not_satisfied2 (hash : List ℤ → ℤ) :
    ¬ Satisfied2 hash foldDesc (fun _ => 0) (fun _ => (0, 0)) [] badTrace := by
  intro h
  have hb := h.rowConstraints 0 (by decide)
    (VmConstraint2.base (.boundary .last lastSummaryBody))
    (by simp [foldDesc, foldConstraints])
  simp only [VmConstraint2.holdsAt] at hb
  rw [show ((0 : Nat) + 1 == badTrace.rows.length) = true from rfl, holdsVm_boundaryLast_true] at hb
  have hrt : (envAt badTrace 0).loc ROW_TYPE = 2 := by simp [envAt, badTrace, badRow, ROW_TYPE]
  simp only [lastSummaryBody, EmittedExpr.eval] at hb
  rw [hrt] at hb
  norm_num at hb

/-! ## §4 — Strengthened non-vacuity: the LOAD-BEARING removal-authentication clause genuinely BITES.

The satisfying witness above is a summary-only trace, so its `removalsCertified` clause is vacuously
quantified. This section exhibits an accepting trace with a REAL removal row (so `removalsCertified`
fires with real content through the bridge) AND a rejecting trace whose REMOVAL row trips
`membership_root_matches` (so the field `RemovalCertified.membershipAgainstOldRoot` names a gate that
genuinely bites — not merely the summary boundary). -/

/-- A 2-row trace whose removal row (`ROW_TYPE = 0`, row 0, active) has `MEMBERSHIP_ROOT = 5 ≠ 0 =
OLD_ROOT` — violating `membership_root_matches` — closed by a well-formed summary row (`ROW_TYPE = 1`),
so the SOLE violation is the removal-authentication gate. -/
def badRemovalRow0 : Assignment := fun c =>
  ([0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD c 0

def badRemovalRow1 : Assignment := fun c =>
  ([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD c 0

def badRemovalTrace : VmTrace :=
  { rows := [badRemovalRow0, badRemovalRow1], pub := fun _ => 0, tf := fun _ => [] }

/-- **Non-vacuity (reject at the removal gate).** The trace whose removal row violates
`membership_root_matches` is REJECTED by `Satisfied2` — the exact gate `RemovalCertified`'s
`membershipAgainstOldRoot` field names genuinely BITES on a removal (non-last) row, not merely the
summary boundary. This is the direct witness that the load-bearing removal-authentication content is
real (the gate fires and separates). -/
theorem badRemoval_not_satisfied2 (hash : List ℤ → ℤ) :
    ¬ Satisfied2 hash foldDesc (fun _ => 0) (fun _ => (0, 0)) [] badRemovalTrace := by
  intro h
  have hc := h.rowConstraints 0 (by decide) (VmConstraint2.base (.gate mrmBody))
    (by simp [foldDesc, foldConstraints])
  simp only [VmConstraint2.holdsAt] at hc
  rw [holdsVm_gate_of_notLast _ _ _ _
        (show ((0 : Nat) + 1 == badRemovalTrace.rows.length) = false from rfl)] at hc
  -- The removal row's gate residual is `(1−0)·(5−0) = 5`, and `p ∤ 5` — the field gate bites.
  have he : mrmBody.eval (envAt badRemovalTrace 0).loc = 5 := by decide
  rw [he] at hc
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp hc
  omega

/-- The concrete Poseidon2 permutation the ACCEPTING 2-row witness pins its digests to (the bridge
itself is proven for an ABSTRACT `hash`; here a concrete `hash = 0` makes the digest columns numeric). -/
def concreteFoldHash : List ℤ → ℤ := fun _ => 0

/-- The accepting REMOVAL row: `ROW_TYPE = 0`, valid hash, `MEMBERSHIP_ROOT = OLD_ROOT = 100`, new root
`200`, the removed fact `(pred=7, terms=8,9,10)`, `REMOVAL_COUNT = 0`, `REMOVAL_COUNT_PLUS_ONE = 1`,
pi4-carrier `300`; `FACT_HASH = 0 = concreteFoldHash …`. -/
def goodRow0 : Assignment := fun c =>
  ([0, 0, 100, 100, 200, 0, 0, 7, 8, 9, 10, 1, 1, 300, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD c 0

/-- The accepting SUMMARY row: `ROW_TYPE = 1`, `REMOVAL_COUNT = 1`, `MEMBERSHIP_ROOT = pi4 = 300`. -/
def goodRow1 : Assignment := fun c =>
  ([1, 0, 300, 100, 200, 1, 0, 0, 0, 0, 0, 0, 0, 300, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD c 0

/-- Public inputs: old root 100, new root 200, removal count 1, check count 0, transition hash 300. -/
def goodPub : Assignment := fun c => ([100, 200, 1, 0, 300, 0] : List ℤ).getD c 0

/-- The Poseidon2 chip table: the two genuine arity-7 fact-hash rows (removal fact `[7,8,9,10]`; summary
row's all-zero fact), each a `chipRow concreteFoldHash …` so `ChipTableSound` holds structurally. -/
def goodPoseidonTable : List (List ℤ) :=
  [ chipRow concreteFoldHash [7, 8, 9, 10, 0, 64207, 1] (List.replicate 7 0)
  , chipRow concreteFoldHash [0, 0, 0, 0, 0, 64207, 1] (List.replicate 7 0) ]

/-- The accepting 2-row witness (a genuine removal row + the summary row). -/
def goodTrace : VmTrace :=
  { rows := [goodRow0, goodRow1]
  , pub  := goodPub
  , tf   := fun tbl => match tbl with | .poseidon2 => goodPoseidonTable | _ => [] }

/-- The accepting witness's chip table IS sound (each row is a genuine `chipRow concreteFoldHash …`). -/
theorem goodTrace_chipSound : ChipTableSound concreteFoldHash (goodTrace.tf .poseidon2) := by
  intro r hr
  have hpo : goodTrace.tf .poseidon2 = goodPoseidonTable := rfl
  rw [hpo, goodPoseidonTable, List.mem_cons, List.mem_singleton] at hr
  rcases hr with rfl | rfl
  · exact ⟨[7, 8, 9, 10, 0, 64207, 1], List.replicate 7 0, by decide, by decide, rfl⟩
  · exact ⟨[0, 0, 0, 0, 0, 64207, 1], List.replicate 7 0, by decide, by decide, rfl⟩

/-- The good trace declares no mem/map ops, so both global logs are empty. -/
theorem goodTrace_memLog : Dregg2.Circuit.DescriptorIR2.memLog foldDesc goodTrace = [] := rfl
theorem goodTrace_mapLog : Dregg2.Circuit.DescriptorIR2.mapLog foldDesc goodTrace = [] := rfl

-- Reduce one row-`i` constraint to its concrete decidable content (booleans pinned, `holdsAt`
-- unfolded), so the accepting witness's per-row obligations discharge by `decide`. The `first`
-- combinator dispatches each constraint shape (a vacuous wrong-row guard via `Bool.noConfusion`, a
-- fired equality via `decide`, the fact-hash lookup via unfolding); some alternatives are redundant on
-- one row but exercised on the other, so the two per-branch linters are scoped off here.
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem goodTrace_rowConstraints :
    ∀ i < goodTrace.rows.length, ∀ c ∈ foldDesc.constraints,
      c.holdsAt concreteFoldHash goodTrace.tf (envAt goodTrace i) (i == 0)
        (i + 1 == goodTrace.rows.length) := by
  intro i hi c hc
  have hlen2 : goodTrace.rows.length = 2 := rfl
  rw [hlen2] at hi ⊢
  rw [show foldDesc.constraints = foldConstraints from rfl] at hc
  interval_cases i
  · -- removal row (first, active): pin isFirst = true, isLast = false.
    rw [show ((0 : Nat) == 0) = true from rfl, show ((0 : Nat) + 1 == 2) = false from rfl]
    fin_cases hc <;>
      first
        | exact True.intro
        | (intro hcon; exact Bool.noConfusion hcon)
        | (intro _; decide)
        | (simp only [VmConstraint2.holdsAt,
            Dregg2.Circuit.Emit.EffectVmEmit.holdsVm_gate_false]; decide)
        | (simp only [factHashLookup, VmConstraint2.holdsAt, Lookup.holdsAt]; decide)
  · -- summary row (last): pin isFirst = false, isLast = true.
    rw [show ((1 : Nat) == 0) = false from rfl, show ((1 : Nat) + 1 == 2) = true from rfl]
    fin_cases hc <;>
      first
        | exact True.intro
        | (intro hcon; exact Bool.noConfusion hcon)
        | (intro _; decide)
        | (simp only [VmConstraint2.holdsAt,
            Dregg2.Circuit.Emit.EffectVmEmit.holdsVm_gate_false]; decide)
        | (simp only [factHashLookup, VmConstraint2.holdsAt, Lookup.holdsAt]; decide)

/-- **Non-vacuity (accept, with a REAL removal row).** The 2-row removal+summary witness satisfies the
deployed `Satisfied2` — so an accepting trace CONTAINING a removal row exists. -/
theorem goodTrace_satisfied :
    Satisfied2 concreteFoldHash foldDesc (fun _ => 0) (fun _ => (0, 0)) [] goodTrace where
  rowConstraints := goodTrace_rowConstraints
  rowHashes := fun i hi => trivial
  rowRanges := fun i hi => by simp [foldDesc]
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [goodTrace_memLog] at hop; simp at hop
  memDisciplined := by rw [goodTrace_memLog]; trivial
  memBalanced := by
    rw [goodTrace_memLog]
    simp [MemoryChecking.MemCheck, MemoryChecking.initSet, MemoryChecking.finalSet]
  memTableFaithful := by rw [goodTrace_memLog]; rfl
  mapTableFaithful := by rw [goodTrace_mapLog]; rfl

/-- **The removal+summary witness inhabits the canonicality envelope** — every enveloped cell of
both rows and all five bound public inputs are small canonical field values (`≤ 300`). -/
theorem goodTrace_canon : FoldTraceCanon goodTrace := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩ <;>
  · intro i hi
    have h2 : goodTrace.rows.length = 2 := rfl
    rw [h2] at hi
    interval_cases i <;> exact ⟨by decide, by decide⟩

/-- **The bridge applied to the real removal witness.** `goodTrace_foldStepValid` is a concrete
`FoldStepValid` reached from the genuinely-satisfiable accepting witness. -/
theorem goodTrace_foldStepValid : FoldStepValid concreteFoldHash goodTrace :=
  foldDesc_satisfied2_refines_foldStepValid concreteFoldHash (fun _ => 0) (fun _ => (0, 0)) []
    goodTrace goodTrace_chipSound (by decide) goodTrace_canon goodTrace_satisfied

/-- The load-bearing `removalsCertified` clause FIRES on the real removal row 0 of the accepting
witness — the `RemovalCertified` structure is genuinely inhabited THROUGH the bridge, not vacuously. -/
theorem goodTrace_removal_certified :
    RemovalCertified concreteFoldHash (envAt goodTrace 0) :=
  goodTrace_foldStepValid.removalsCertified 0 (by decide) (by decide)

/-- …and its content is real: the removal row's membership root equals the committed OLD root
(`100 = 100`) and its hash flag is valid — the removal was genuinely authenticated. -/
example :
    (envAt goodTrace 0).loc MEMBERSHIP_ROOT = (envAt goodTrace 0).loc OLD_ROOT
      ∧ (envAt goodTrace 0).loc HASH_VALID = 1 :=
  ⟨goodTrace_removal_certified.membershipAgainstOldRoot, goodTrace_removal_certified.hashValid⟩

#assert_axioms foldDesc_satisfied2_refines_foldStepValid
#assert_axioms satTrace_satisfied2
#assert_axioms satTrace_chipSound
#assert_axioms satTrace_foldStepValid
#assert_axioms badTrace_not_satisfied2
#assert_axioms badRemoval_not_satisfied2
#assert_axioms goodTrace_satisfied
#assert_axioms goodTrace_chipSound
#assert_axioms goodTrace_foldStepValid
#assert_axioms goodTrace_removal_certified

end Dregg2.Circuit.Emit.FoldRefine
