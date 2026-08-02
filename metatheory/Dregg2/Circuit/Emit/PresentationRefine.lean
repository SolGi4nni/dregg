/-
# Dregg2.Circuit.Emit.PresentationRefine — the WHOLE-DESCRIPTOR functional-correctness bridge for
the `presentation` family (Rung 1, additive over `PresentationEmit.lean`).

`PresentationEmit.lean` byte-pins `presentationFreshnessDesc` and proves per-GATE lemmas
(`diffBind_body_zero_iff`, `bound_body_zero_iff`, `freshness_bound_sound`). What was MISSING — and
what this file supplies — is the whole-descriptor bridge: a trace SATISFYING the descriptor
(`Satisfied2`, the deployed acceptance predicate) corresponds to the GENUINE semantic relation the
circuit is meant to compute.

## The NO_LEAN case — this file AUTHORS the functional spec, then proves the refinement

No proven Lean model of "the presentation summary AIR + freshness binding" existed. So §1 authors the
semantic RELATION `PresentationFresh` — the functional spec of what an accepted presentation trace
MEANS — and §2 proves the descriptor's `Satisfied2` REFINES it (`presentation_satisfied2_fresh`,
SAT_IMPLIES_SEM: the deployed accept-set is contained in the genuine relation's truth-set).

`PresentationFresh env` says, on the (first) summary row:
  1. **summary faithfulness** — the 19 summary columns ARE the published public summary
     (`env.loc i = env.pub i` for every `i < SUMMARY_WIDTH`): the presented summary is exactly the
     verifier's public inputs, not a substituted one;
  2. **verifier anchoring** — the freshness column IS the published verifier block height
     (`env.loc VERIFIER = env.pub PI_VERIFIER`);
  3. **token freshness** — `not_after_height ≥ verifier_block_height`, read in BabyBear as a small
     non-negative field difference `not_after − verifier ∈ [0, p/2]` — EXACTLY the acceptance region
     of the deployed `verify_freshness_binding` (`presentation.rs:316–345`).

This matches PRECISELY the arithmetic the descriptor internalizes; the named STARK-leaf checks
(fold-chain continuity, issuer-federation membership, temporal STARKs, the presentation-tag Poseidon2
hash) ride the recursion argument OFF this descriptor by design (documented in `PresentationEmit`), so
they are correctly OUTSIDE this descriptor's functional spec.

## The bridge composes EVERY constraint (not one gate)

`presentation_satisfied2_fresh` extracts, from the ONE hypothesis `Satisfied2`, the full constraint
set on the first summary row: the 19 summary `.piBinding`s (→ summary faithfulness), the verifier
`.piBinding` (→ anchoring), the diff-binding gate (`diff = not_after − verifier`), the bound gate
(`diff + hi = p/2`), and BOTH range lookups (`diff, hi ∈ [0, 2^30)`); it then folds the two range
teeth + the bound gate through the byte-pinned `freshness_bound_sound` to conclude `diff ∈ [0, p/2]`,
i.e. token freshness over the genuine data. This is what makes the emitted descriptor a proven
functional refinement rather than a byte-pinned blob.

## Non-vacuity (the anti-scar)

§3 exhibits a CONCRETE satisfying witness — `honestTrace` (a fresh token: verifier 1000, not_after
1500, so diff 500, hi p/2−500) — and proves `honest_satisfies : Satisfied2 … honestTrace` in full
(every leg discharged), so the bridge's hypothesis is genuinely INHABITED; `bridge_fires_on_honest`
runs the bridge end-to-end on it. §4 exhibits a CONCRETE failing witness — `expiredTrace` (an expired
token: not_after 999 < verifier 1000, honest diff = −1) — and proves `expired_not_satisfied` (the diff
range tooth BITES: `Satisfied2` is unsatisfiable) AND `expired_not_fresh` (the relation is genuinely
falsifiable). Hypothesis inhabited-and-constraining; conclusion true-and-false.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} (pure `omega`/`norm_num`/`simp`; this
family internalizes NO Poseidon2 hashing, so NO CR carrier enters). NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.PresentationEmit
import Dregg2.Circuit.Emit.EffectVmEmitTransfer

namespace Dregg2.Circuit.Emit.PresentationRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmRowEnv VmConstraint VmRow holdsVm_gate_false holdsVm_gate_true holdsVm_piFirst_true
   holdsVm_boundaryLast_true)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId TraceFamily VmTrace Satisfied2 envAt
   rangeRows range_row_mem_iff lookup_replaces_range lookup_range_complete memOpsOf mapOpsOf
   memLog mapLog)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff eqToModEq)
open Dregg2.Circuit.Emit.PresentationEmit
-- ⚑ `presentationFreshnessDesc` is COMPILER-AUTHORED (`EffectLower.lowerAir`), so no list literal
-- survives to `simp` on: every membership below goes through `presentationFreshnessDesc_constraints`
-- (the compiler's output, by `rfl`) and every gate residual through the generic `gateBody_eval`.
open Dregg2.Circuit.Emit.AirNormalForm (gateBody gateBody_eval lowerConstraint_gateBody)
open Dregg2.Crypto

set_option autoImplicit false

/-! ## §0 — field-denotation glue. The DEPLOYED `VmConstraint.holdsVm` pins each gate/PI only
`≡ 0 [ZMOD p]` / `≡ pub [ZMOD p]` (`p` the BabyBear prime), NOT `= 0`. The genuine ℤ summary/anchor
equalities are recovered off the DEPLOYED range-check canonicality envelope `PresCanon`; the two
freshness range LOOKUPS already deliver honest ℤ bounds on `DIFF`/`HI`, so the wrap-free windows make
the diff/bound gate congruences genuine ℤ identities. -/

/-- Two canonical field cells congruent mod `p` are EQUAL over ℤ. -/
theorem eq_of_modEq_canon {a b : ℤ} (h : a ≡ b [ZMOD 2013265921])
    (ha0 : 0 ≤ a) (ha1 : a < 2013265921) (hb0 : 0 ≤ b) (hb1 : b < 2013265921) : a = b := by
  rw [Int.modEq_iff_dvd] at h; obtain ⟨k, hk⟩ := h; omega

/-- **The deployed range-check canonicality envelope for the summary row.** The 19 summary cells and
their public inputs are canonical field cells (`0 ≤ · < p`); the `VERIFIER` / `NOT_AFTER` block-height
cells sit in the LOW HALF (`2·x < p`), so — with `DIFF ∈ [0, p/2]` (the two range teeth + bound gate)
— the field subtraction `not_after − verifier` is wrap-free over ℤ. Inhabited by `honest_canon`. -/
def PresCanon (env : VmRowEnv) : Prop :=
  (∀ i, i < SUMMARY_WIDTH →
      (0 ≤ env.loc i ∧ env.loc i < 2013265921) ∧ (0 ≤ env.pub i ∧ env.pub i < 2013265921))
  ∧ (0 ≤ env.loc VERIFIER ∧ 2 * env.loc VERIFIER < 2013265921)
  ∧ (0 ≤ env.pub PI_VERIFIER ∧ env.pub PI_VERIFIER < 2013265921)
  ∧ (0 ≤ env.loc NOT_AFTER ∧ 2 * env.loc NOT_AFTER < 2013265921)

/-! ## §1 — THE FUNCTIONAL SPEC (authored here — no prior Lean model existed). -/

/-- **`PresentationFresh env` — the genuine semantic relation the presentation circuit computes.**
On the summary row `env`:
* `summaryFaithful` — every summary column equals the published public summary input;
* `verifierAnchored` — the verifier-height column equals the published verifier-block-height input;
* `tokenFresh` — the token is not expired: `not_after − verifier ∈ [0, p/2]` (the deployed
  `verify_freshness_binding` acceptance region, `p/2 = HALF_P`).
The freshness is stated over the UNDERLYING data (`not_after`, `verifier`), NOT the gadget witness
columns `DIFF`/`HI` — those are the circuit's private witnesses, proved to realize this relation. -/
structure PresentationFresh (env : VmRowEnv) : Prop where
  summaryFaithful  : ∀ i, i < SUMMARY_WIDTH → env.loc i = env.pub i
  verifierAnchored : env.loc VERIFIER = env.pub PI_VERIFIER
  tokenFresh       : 0 ≤ env.loc NOT_AFTER - env.loc VERIFIER
                       ∧ env.loc NOT_AFTER - env.loc VERIFIER ≤ HALF_P

/-! ## §2 — THE WHOLE-DESCRIPTOR BRIDGE (SAT_IMPLIES_SEM). -/

/-- **`presentation_satisfied2_fresh` — THE BRIDGE.** On any multi-table witness whose `.range` table
is the faithful 30-bit range table and whose main trace has height ≥ 2 (so the first summary row is
first-and-not-last, matching the deployed padded AIR), a `Satisfied2` of `presentationFreshnessDesc`
FORCES the genuine relation `PresentationFresh` on the first summary row. Composes ALL constraints:
the 19 summary + verifier `.piBinding`s, the diff-binding and bound gates, and the two 30-bit range
lookups (folded via `freshness_bound_sound` into `diff ≤ p/2`). -/
theorem presentation_satisfied2_fresh
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hrange : t.tf .range = rangeRows FRESH_BITS)
    (hlen : 1 < t.rows.length)
    (hsat : Satisfied2 hash presentationFreshnessDesc minit mfin maddrs t)
    (hcanon : PresCanon (envAt t 0)) :
    PresentationFresh (envAt t 0) := by
  have hi0 : 0 < t.rows.length := by omega
  have hrow := hsat.rowConstraints 0 hi0
  have hf : (0 == 0) = true := rfl
  have hl : (0 + 1 == t.rows.length) = false := by
    rw [beq_eq_false_iff_ne]; omega
  obtain ⟨hcSum, hcVer, hcPubVer, hcNa⟩ := hcanon
  -- diff range lookup: DIFF ∈ [0, 2^30) (an honest ℤ bound — the lookup is not a field congruence).
  have hdr : 0 ≤ (envAt t 0).loc DIFF ∧ (envAt t 0).loc DIFF < 2 ^ FRESH_BITS := by
    have hmem : diffRangeLookup ∈ presentationFreshnessDesc.constraints := by
      rw [presentationFreshnessDesc_constraints]
      exact List.mem_append_right _ (by simp)
    have h : Lookup.holdsAt t.tf (envAt t 0) ⟨.range, [.var DIFF]⟩ := hrow _ hmem
    exact lookup_replaces_range FRESH_BITS t.tf hrange (envAt t 0) DIFF h
  -- hi range lookup: HI ∈ [0, 2^30).
  have hhr : 0 ≤ (envAt t 0).loc HI ∧ (envAt t 0).loc HI < 2 ^ FRESH_BITS := by
    have hmem : hiRangeLookup ∈ presentationFreshnessDesc.constraints := by
      rw [presentationFreshnessDesc_constraints]
      exact List.mem_append_right _ (by simp)
    have h : Lookup.holdsAt t.tf (envAt t 0) ⟨.range, [.var HI]⟩ := hrow _ hmem
    exact lookup_replaces_range FRESH_BITS t.tf hrange (envAt t 0) HI h
  have hdr' : 0 ≤ (envAt t 0).loc DIFF ∧ (envAt t 0).loc DIFF < 2 ^ 30 := by
    simpa [FRESH_BITS] using hdr
  have hhr' : 0 ≤ (envAt t 0).loc HI ∧ (envAt t 0).loc HI < 2 ^ 30 := by
    simpa [FRESH_BITS] using hhr
  have h30 : ((2 : ℤ) ^ 30) = 1073741824 := by norm_num
  -- bound gate (mod `p`): DIFF + HI ≡ p/2. With both in `[0, 2^30)` (sum `< 2^31 < p/2 + p`), the
  -- congruence is the genuine ℤ identity `DIFF + HI = p/2`.
  have hbe : (envAt t 0).loc DIFF + (envAt t 0).loc HI = HALF_P := by
    have hmem : boundGate ∈ presentationFreshnessDesc.constraints := by
      rw [presentationFreshnessDesc_constraints]
      exact List.mem_append_right _ (by simp)
    have h : VmConstraint.holdsVm (envAt t 0) (0 == 0) (0 + 1 == t.rows.length)
        (.gate boundBody) := hrow _ hmem
    rw [hl, holdsVm_gate_false] at h
    have hmod : (envAt t 0).loc DIFF + (envAt t 0).loc HI ≡ HALF_P [ZMOD 2013265921] :=
      -- ⚑ the residual read off the COMPILED body (`boundBody = gateBody boundSrc`) by the generic
      -- `gateBody_eval` tooth; `boundSrc.rhs` IS the `HALF_P` literal.
      (gate_modEq_iff (gateBody_eval boundSrc (envAt t 0).loc)).mp h
    rw [Int.modEq_iff_dvd] at hmod
    obtain ⟨k, hk⟩ := hmod
    simp only [HALF_P] at hk ⊢
    rw [h30] at hdr' hhr'
    omega
  -- fold the two range teeth + the bound gate through the byte-pinned soundness lemma.
  have hbound : (envAt t 0).loc DIFF ≤ HALF_P := freshness_bound_sound _ _ hdr' hhr' hbe
  -- diff-binding gate (mod `p`): DIFF ≡ NOT_AFTER − VERIFIER. With `DIFF ∈ [0, p/2]` and the low-half
  -- windows on the two block heights, the field subtraction is wrap-free, so this is the ℤ identity.
  have hdc : (envAt t 0).loc DIFF = (envAt t 0).loc NOT_AFTER - (envAt t 0).loc VERIFIER := by
    have hmem : diffBindGate ∈ presentationFreshnessDesc.constraints := by
      rw [presentationFreshnessDesc_constraints]
      exact List.mem_append_right _ (by simp)
    have h : VmConstraint.holdsVm (envAt t 0) (0 == 0) (0 + 1 == t.rows.length)
        (.gate diffBindBody) := hrow _ hmem
    rw [hl, holdsVm_gate_false] at h
    have hmod : (envAt t 0).loc DIFF
        ≡ (envAt t 0).loc NOT_AFTER - (envAt t 0).loc VERIFIER [ZMOD 2013265921] :=
      (gate_modEq_iff (by
        rw [show diffBindBody = gateBody diffBindSrc from rfl, gateBody_eval]
        show (envAt t 0).loc DIFF
            - ((envAt t 0).loc NOT_AFTER + (-1) * (envAt t 0).loc VERIFIER) = _
        ring)).mp h
    rw [Int.modEq_iff_dvd] at hmod
    obtain ⟨k, hk⟩ := hmod
    simp only [HALF_P] at hbound
    omega
  refine
    { summaryFaithful := ?_
      verifierAnchored := ?_
      tokenFresh := ?_ }
  · -- 19 summary piBindings (mod `p`) → summary faithfulness (lifted off canonicality of both sides).
    intro j hj
    have hmem : (VmConstraint2.base (.piBinding VmRow.first j j))
        ∈ presentationFreshnessDesc.constraints := by
      rw [presentationFreshnessDesc_constraints]
      simp only [summaryPins]
      exact List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
    have h : VmConstraint.holdsVm (envAt t 0) (0 == 0) (0 + 1 == t.rows.length)
        (.piBinding VmRow.first j j) := hrow _ hmem
    rw [hf, holdsVm_piFirst_true] at h
    obtain ⟨⟨hl0, hl1⟩, hp0, hp1⟩ := hcSum j hj
    exact eq_of_modEq_canon h hl0 hl1 hp0 hp1
  · -- verifier piBinding (mod `p`) → verifier anchoring (lifted off canonicality of both sides).
    have hmem : verifierPin ∈ presentationFreshnessDesc.constraints := by
      rw [presentationFreshnessDesc_constraints]
      exact List.mem_append_right _ (by simp)
    have h : VmConstraint.holdsVm (envAt t 0) (0 == 0) (0 + 1 == t.rows.length)
        (.piBinding VmRow.first VERIFIER PI_VERIFIER) := hrow _ hmem
    rw [hf, holdsVm_piFirst_true] at h
    exact eq_of_modEq_canon h hcVer.1 (by omega) hcPubVer.1 hcPubVer.2
  · -- freshness: 0 ≤ not_after − verifier ≤ p/2 (via DIFF = not_after − verifier).
    rw [← hdc]
    exact ⟨hdr.1, hbound⟩

/-! ## §3 — NON-VACUITY (accept): a CONCRETE satisfying witness — an honest fresh token. -/

/-- The honest summary row: an all-zero summary, `verifier = 1000`, `not_after = 1500`, so the gadget
witnesses `diff = 500` and `hi = p/2 − 500 = 1006632460` (both in `[0, 2^30)`). -/
def honestRow : Assignment := fun c =>
  if c = VERIFIER then 1000
  else if c = NOT_AFTER then 1500
  else if c = DIFF then 500
  else if c = HI then 1006632460
  else 0

/-- The honest public inputs: the 19 summary slots are 0, the verifier anchor (slot 19) is 1000. -/
def honestPub : Assignment := fun k => if k = PI_VERIFIER then 1000 else 0

/-- The honest trace family: the faithful 30-bit range table; every other table empty (the descriptor
declares no mem/map ops, so `.memory`/`.mapOps` must read empty). `if`-based (not a matcher) so the
`.range` faithfulness is a controlled rewrite that never enumerates the `2^30`-row table. -/
def honestTF (tid : TableId) : Dregg2.Circuit.DescriptorIR2.Table :=
  if tid = TableId.range then rangeRows FRESH_BITS else []

/-- The honest multi-table witness: two identical summary rows (height 2 = the minimal padded power of
two, so row 0 is first-and-not-last). -/
def honestTrace : VmTrace :=
  { rows := [honestRow, honestRow], pub := honestPub, tf := honestTF }

/-- The honest `.range` slot IS the faithful 30-bit range table — proved by a projection rewrite then
a single `if_pos`, keeping `rangeRows FRESH_BITS` an un-reduced subterm so the elaborator NEVER
enumerates the `2^30`-row table (any `whnf` of a bare `rangeRows FRESH_BITS` would). -/
theorem honestTrace_range : honestTrace.tf TableId.range = rangeRows FRESH_BITS := by
  rw [show honestTrace.tf = honestTF from rfl]
  unfold honestTF
  rw [if_pos rfl]

-- Concrete evaluations of the honest row (each `rfl`: the column defs compute).
theorem honestRow_verifier : honestRow VERIFIER = 1000 := rfl
theorem honestRow_notafter : honestRow NOT_AFTER = 1500 := rfl
theorem honestRow_diff : honestRow DIFF = 500 := rfl
theorem honestRow_hi : honestRow HI = 1006632460 := rfl

theorem honestRow_summary (j : Nat) (hj : j < 19) : honestRow j = 0 := by
  have h1 : ¬ j = VERIFIER := by simp only [VERIFIER]; omega
  have h2 : ¬ j = NOT_AFTER := by simp only [NOT_AFTER]; omega
  have h3 : ¬ j = DIFF := by simp only [DIFF]; omega
  have h4 : ¬ j = HI := by simp only [HI]; omega
  simp only [honestRow, if_neg h1, if_neg h2, if_neg h3, if_neg h4]

theorem honestPub_verifier : honestPub PI_VERIFIER = 1000 := rfl

theorem honestPub_summary (j : Nat) (hj : j < 19) : honestPub j = 0 := by
  have h1 : ¬ j = PI_VERIFIER := by simp only [PI_VERIFIER]; omega
  simp only [honestPub, if_neg h1]

/-- **The range-lookup completeness tooth, at the honest trace.** For any row `i` and any column `w`
whose honest value `v` lies in `[0, 2^30)`, the `.range` lookup on `⟨w⟩` holds — routed through the
proven `lookup_range_complete` + `honestTF_range`, so the `2^30`-row table is NEVER enumerated. -/
theorem honest_range_lookup (i w : Nat) (v : ℤ) (hv : (envAt honestTrace i).loc w = v)
    (h0 : 0 ≤ v) (h1 : v < 2 ^ FRESH_BITS) :
    Lookup.holdsAt honestTrace.tf (envAt honestTrace i) ⟨.range, [.var w]⟩ := by
  refine lookup_range_complete FRESH_BITS honestTrace.tf honestTrace_range (envAt honestTrace i) w ?_
  show (0 : ℤ) ≤ (envAt honestTrace i).loc w ∧ (envAt honestTrace i).loc w < 2 ^ FRESH_BITS
  rw [hv]; exact ⟨h0, h1⟩

/-- **`honest_satisfies` — the bridge's hypothesis is GENUINELY INHABITED.** The honest fresh-token
witness satisfies `Satisfied2` of `presentationFreshnessDesc` in full: every constraint holds on both
rows (the piBindings/gates fire on row 0, are vacuous on the last row; the range lookups fire on both),
the hash-site/range legs are empty, and — the descriptor declaring no mem/map ops — every memory /
table-faithfulness leg reads the empty log. -/
theorem honest_satisfies :
    Satisfied2 (fun _ => 0) presentationFreshnessDesc (fun _ => 0) (fun _ => (0, 0)) []
      honestTrace := by
  have hmemops : memOpsOf presentationFreshnessDesc = [] := rfl
  have hmapops : mapOpsOf presentationFreshnessDesc = [] := rfl
  have hml : memLog presentationFreshnessDesc honestTrace = [] := by
    simp [memLog, hmemops, honestTrace]
  have hmpl : mapLog presentationFreshnessDesc honestTrace = [] := by
    simp [mapLog, hmapops, honestTrace]
  refine
    { rowConstraints := ?_
      rowHashes := ?_
      rowRanges := ?_
      memAddrsNodup := List.nodup_nil
      memClosed := ?_
      memDisciplined := ?_
      memBalanced := ?_
      memTableFaithful := ?_
      mapTableFaithful := ?_ }
  · -- rowConstraints: on both rows, every declared constraint holds.
    intro i hi c hc
    have hlen2 : honestTrace.rows.length = 2 := rfl
    rw [hlen2] at hi ⊢
    rw [presentationFreshnessDesc_constraints] at hc
    have hi2 : i = 0 ∨ i = 1 := by omega
    rcases hi2 with rfl | rfl
    · -- row 0 (first, not last): piBindings + gates + lookups all fire.
      rcases List.mem_append.mp hc with hsum | htail
      · rw [summaryPins, List.mem_map] at hsum
        obtain ⟨j, hjr, rfl⟩ := hsum
        rw [List.mem_range] at hjr
        simp only [SUMMARY_WIDTH] at hjr
        show VmConstraint.holdsVm (envAt honestTrace 0) (0 == 0) (0 + 1 == 2)
          (.piBinding VmRow.first j j)
        rw [show (0 == 0) = true from rfl, holdsVm_piFirst_true]
        exact eqToModEq (by show honestRow j = honestPub j
                            rw [honestRow_summary j hjr, honestPub_summary j hjr])
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at htail
        rcases htail with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · show VmConstraint.holdsVm (envAt honestTrace 0) (0 == 0) (0 + 1 == 2)
            (.piBinding VmRow.first VERIFIER PI_VERIFIER)
          rw [show (0 == 0) = true from rfl, holdsVm_piFirst_true]
          exact eqToModEq (by show honestRow VERIFIER = honestPub PI_VERIFIER
                              rw [honestRow_verifier, honestPub_verifier])
        · show VmConstraint.holdsVm (envAt honestTrace 0) (0 == 0) (0 + 1 == 2) (.gate diffBindBody)
          rw [show (0 + 1 == 2) = false from rfl, holdsVm_gate_false]
          exact eqToModEq (by show diffBindBody.eval honestRow = 0
                              simp only [diffBindBody, gateBody_eval, diffBindSrc,
                                Dregg2.Circuit.Expr.eval, honestRow_diff,
                                honestRow_notafter, honestRow_verifier]
                              norm_num)
        · show VmConstraint.holdsVm (envAt honestTrace 0) (0 == 0) (0 + 1 == 2) (.gate boundBody)
          rw [show (0 + 1 == 2) = false from rfl, holdsVm_gate_false]
          exact eqToModEq (by show boundBody.eval honestRow = 0
                              simp only [boundBody, gateBody_eval, boundSrc,
                                Dregg2.Circuit.Expr.eval, honestRow_diff, honestRow_hi]
                              norm_num)
        · exact honest_range_lookup 0 DIFF 500 rfl (by norm_num) (by norm_num [FRESH_BITS])
        · exact honest_range_lookup 0 HI 1006632460 rfl (by norm_num) (by norm_num [FRESH_BITS])
        · -- diffBindLast (boundary .last) on row 0 (not last) — vacuous.
          simp [diffBindLast, VmConstraint2.holdsAt, VmConstraint.holdsVm]
        · -- boundLast (boundary .last) on row 0 (not last) — vacuous.
          simp [boundLast, VmConstraint2.holdsAt, VmConstraint.holdsVm]
    · -- row 1 (last): piBindings/gates vacuous; range lookups + last-row boundaries fire.
      rcases List.mem_append.mp hc with hsum | htail
      · rw [summaryPins, List.mem_map] at hsum
        obtain ⟨j, _, rfl⟩ := hsum
        simp [VmConstraint2.holdsAt, VmConstraint.holdsVm]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at htail
        rcases htail with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · simp [verifierPin, VmConstraint2.holdsAt, VmConstraint.holdsVm]
        · simp [diffBindGate, lowerConstraint_gateBody, VmConstraint2.holdsAt,
            VmConstraint.holdsVm]
        · simp [boundGate, lowerConstraint_gateBody, VmConstraint2.holdsAt, VmConstraint.holdsVm]
        · exact honest_range_lookup 1 DIFF 500 rfl (by norm_num) (by norm_num [FRESH_BITS])
        · exact honest_range_lookup 1 HI 1006632460 rfl (by norm_num) (by norm_num [FRESH_BITS])
        · -- diffBindLast (boundary .last) on row 1 (last) — FIRES; holds by construction.
          show VmConstraint.holdsVm (envAt honestTrace 1) (1 == 0) (1 + 1 == 2)
            (.boundary VmRow.last diffBindBody)
          rw [show (1 + 1 == 2) = true from rfl, holdsVm_boundaryLast_true]
          exact eqToModEq (by show diffBindBody.eval honestRow = 0
                              simp only [diffBindBody, gateBody_eval, diffBindSrc,
                                Dregg2.Circuit.Expr.eval, honestRow_diff,
                                honestRow_notafter, honestRow_verifier]
                              norm_num)
        · -- boundLast (boundary .last) on row 1 (last) — FIRES; holds by construction.
          show VmConstraint.holdsVm (envAt honestTrace 1) (1 == 0) (1 + 1 == 2)
            (.boundary VmRow.last boundBody)
          rw [show (1 + 1 == 2) = true from rfl, holdsVm_boundaryLast_true]
          exact eqToModEq (by show boundBody.eval honestRow = 0
                              simp only [boundBody, gateBody_eval, boundSrc,
                                Dregg2.Circuit.Expr.eval, honestRow_diff, honestRow_hi]
                              norm_num)
  · intro i _
    simp only [presentationFreshnessDesc]
    exact True.intro
  · intro i _ r hr
    rw [show presentationFreshnessDesc.ranges = [] from rfl] at hr
    simp at hr
  · intro op hop
    simp [hml] at hop
  · rw [hml]; exact True.intro
  · rw [hml]
    simp [MemoryChecking.MemCheck, MemoryChecking.initSet, MemoryChecking.finalSet]
  · rw [hml]; rfl
  · rw [hmpl]; rfl

/-- **The canonicality envelope is genuinely INHABITED** — the honest witness's summary cells and
public inputs are `0` (canonical) and the block heights `verifier = 1000` / `not_after = 1500` sit deep
in the low half. So the bridge does NOT rest on a vacuous range-check hypothesis. -/
theorem honest_canon : PresCanon (envAt honestTrace 0) := by
  refine ⟨fun i hi => ?_, ?_, ?_, ?_⟩
  · have hl : (envAt honestTrace 0).loc i = 0 := by
      rw [show (envAt honestTrace 0).loc i = honestRow i from rfl]; exact honestRow_summary i hi
    have hp : (envAt honestTrace 0).pub i = 0 := by
      rw [show (envAt honestTrace 0).pub i = honestPub i from rfl]; exact honestPub_summary i hi
    rw [hl, hp]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> decide
  · rw [show (envAt honestTrace 0).loc VERIFIER = honestRow VERIFIER from rfl, honestRow_verifier]
    exact ⟨by decide, by decide⟩
  · rw [show (envAt honestTrace 0).pub PI_VERIFIER = honestPub PI_VERIFIER from rfl, honestPub_verifier]
    exact ⟨by decide, by decide⟩
  · rw [show (envAt honestTrace 0).loc NOT_AFTER = honestRow NOT_AFTER from rfl, honestRow_notafter]
    exact ⟨by decide, by decide⟩

/-- **`bridge_fires_on_honest`** — the whole-descriptor bridge run end-to-end on the concrete honest
witness: the genuine relation holds on its summary row. -/
theorem bridge_fires_on_honest : PresentationFresh (envAt honestTrace 0) :=
  presentation_satisfied2_fresh (fun _ => 0) (fun _ => 0) (fun _ => (0, 0)) [] honestTrace
    honestTrace_range (by decide) honest_satisfies honest_canon

/-! ## §4 — NON-VACUITY (reject): a CONCRETE failing witness — an expired token. -/

/-- The expired summary row: `verifier = 1000`, `not_after = 999` (expired: not_after < verifier), so
the HONEST `diff = not_after − verifier = −1` is NEGATIVE — out of `[0, 2^30)`. -/
def expiredRow : Assignment := fun c =>
  if c = VERIFIER then 1000
  else if c = NOT_AFTER then 999
  else if c = DIFF then -1
  else if c = HI then 1006632961
  else 0

/-- The expired witness (same shape as honest; only the token is stale). -/
def expiredTrace : VmTrace :=
  { rows := [expiredRow, expiredRow], pub := honestPub, tf := honestTF }

/-- The expired witness's `.range` slot is the faithful 30-bit range table (as for honest). -/
theorem expiredTrace_range : expiredTrace.tf TableId.range = rangeRows FRESH_BITS := by
  rw [show expiredTrace.tf = honestTF from rfl]
  unfold honestTF
  rw [if_pos rfl]

/-- **`expired_not_satisfied` — the descriptor is genuinely CONSTRAINING (the freshness tooth bites).**
No `hash`/boundary makes the expired token satisfy `presentationFreshnessDesc`: its honest `diff = −1`
fails the 30-bit range lookup, so `Satisfied2` is UNSATISFIABLE for this witness. -/
theorem expired_not_satisfied (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) :
    ¬ Satisfied2 hash presentationFreshnessDesc minit mfin maddrs expiredTrace := by
  intro h
  have hi0 : 0 < expiredTrace.rows.length := by
    rw [show expiredTrace.rows.length = 2 from rfl]; omega
  have hmem : diffRangeLookup ∈ presentationFreshnessDesc.constraints := by
    rw [presentationFreshnessDesc_constraints]
    exact List.mem_append_right _ (by simp)
  have hc : Lookup.holdsAt expiredTrace.tf (envAt expiredTrace 0) ⟨.range, [.var DIFF]⟩ :=
    h.rowConstraints 0 hi0 diffRangeLookup hmem
  have hrng := lookup_replaces_range FRESH_BITS expiredTrace.tf expiredTrace_range
    (envAt expiredTrace 0) DIFF hc
  have h0 : (0 : ℤ) ≤ (envAt expiredTrace 0).loc DIFF := hrng.1
  rw [show (envAt expiredTrace 0).loc DIFF = (-1 : ℤ) from rfl] at h0
  norm_num at h0

/-- **`expired_not_fresh` — the RELATION is genuinely FALSIFIABLE** (its `tokenFresh` fails on the
expired witness: `not_after − verifier = −1 < 0`). Together with `bridge_fires_on_honest`,
`PresentationFresh` is true on some witness and false on another — not a `True` in disguise. -/
theorem expired_not_fresh : ¬ PresentationFresh (envAt expiredTrace 0) := by
  intro h
  have hnf := h.tokenFresh.1
  rw [show (envAt expiredTrace 0).loc NOT_AFTER = 999 from rfl,
      show (envAt expiredTrace 0).loc VERIFIER = 1000 from rfl] at hnf
  norm_num at hnf

#assert_axioms presentation_satisfied2_fresh
#assert_axioms honest_satisfies
#assert_axioms honest_canon
#assert_axioms bridge_fires_on_honest
#assert_axioms expired_not_satisfied
#assert_axioms expired_not_fresh

end Dregg2.Circuit.Emit.PresentationRefine
