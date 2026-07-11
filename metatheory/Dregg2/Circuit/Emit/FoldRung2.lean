/-
# Dregg2.Circuit.Emit.FoldRung2 — the RUNG-2 no-forgery discharge for the FOLD-step removal count.

## What Rung 0/1 gave, and what THIS file closes

`FoldEmit.lean` byte-pins `foldDesc` and proves the per-gate teeth; `FoldRefine.lean` bridges
`Satisfied2 ⟹ FoldStepValid`. But BOTH inherited the deployed DSL descriptor's REMOVAL-COUNT FORGERY
HOLE: the increment window `(1-ROW_TYPE)*(next[RC] - loc[RC_PLUS_ONE])` read a FREE witness column
`REMOVAL_COUNT_PLUS_ONE` (col 12) that NO constraint tied to `REMOVAL_COUNT + 1` (`fold.rs:580` declares
it a bare `ColumnKind::Value`, and the deployed boundaries DROPPED the hand-AIR's `first_removal_count`
pin). An adversary set `REMOVAL_COUNT_PLUS_ONE` (and the counter's free start) arbitrarily and published
ANY `pi[2]` for a fold with a completely different number of removal rows — a k-forgery of the removed
count that a verifier accepts (`fold_accepts_forged_removal_count`, §3 here).

`FoldEmit` now emits the three constraints that close it (matching / exceeding the deployed AIR):

  * **(A)** `.base (.gate rcPlusOneBody)` — `(1-ROW_TYPE)*(REMOVAL_COUNT_PLUS_ONE - REMOVAL_COUNT - 1) = 0`
    binds the aux increment column to `REMOVAL_COUNT + 1` on every removal row (it is consumed ONLY by
    the transition-only increment window, so a `.gate` covering rows `0..n-2` is exactly its read set);
  * **(C)** `.windowGate rcCarryBody` — `ROW_TYPE*(next[RC] - loc[RC]) = 0` carries the count constant
    across the summary/pad tail to the last row (the increment window is gated OFF there);
  * **(B)** `.base (.boundary .first firstRcBody)` — `REMOVAL_COUNT = 0` on row 0 anchors the start (the
    count strictly before row 0 is zero).

Under the count-BEFORE-this-row convention (`REMOVAL_COUNT i = #removals in rows 0..i-1`) these make the
published `pi[2]` EXACTLY the number of `ROW_TYPE = 0` rows — proven here as
`removal_count_faithful` (a genuine induction, no carrier needed: pure in-circuit arithmetic).

## The no-forgery statement (argus-grade)

`removal_count_faithful` : `Satisfied2 hash foldDesc … t → 0 < t.rows.length →
  FoldTraceCanon t → t.rows.length ≤ p →
  t.pub PI_REMOVAL_COUNT = removalRowCount t` — the published removal count equals the count of removal
rows in the trace. Its NON-VACUITY poles: `honest_faithful_goodTrace` (the accepted honest witness
publishes the TRUE count 1) and the FORGE `forgeTrace` (was `Satisfied2` under the PRE-FIX descriptor
`foldDescPreFix` publishing `pi[2] = 9` for a ONE-removal fold, and is now REJECTED by `foldDesc`, THE
regression `forge_not_satisfied2_fixed`).

## The field-faithful denotation (mod-p)

The deployed gates pin residuals only `≡ 0 [ZMOD p]` (`p = 2013265921`, BabyBear). The per-step
counter lemmas are HONESTLY congruences — over the field a counter genuinely wraps after `p`
removal rows, so the per-step ℤ equality is FALSE in general. The headline collapses the chained
congruence ONCE, under `FoldRefine.FoldTraceCanon` (the deployed range-check invariant) plus the
trace-length bound `t.rows.length ≤ p` (which keeps `removalRowCount < p`); both are concretely
inhabited by the honest witness (`goodTrace_canon`, length 2), so the envelope is non-vacuous.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; NO crypto carrier is consumed — the count
faithfulness is pure in-circuit arithmetic (the fact-hash chip carrier is orthogonal, unused here). NEW
file; imports read-only.
-/
import Dregg2.Circuit.Emit.FoldRefine

namespace Dregg2.Circuit.Emit.FoldRung2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmConstraint VmRow VmRowEnv holdsVm_gate_of_notLast holdsVm_boundaryFirst_true
   holdsVm_boundaryLast_true holdsVm_piLast_true holdsVm_gate_false)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup WindowConstraint TableId TraceFamily VmTrace
   Satisfied2 envAt ChipTableSound)
open Dregg2.Circuit.Emit.FoldEmit
open Dregg2.Circuit.Emit.FoldRefine
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff)
open Dregg2.Crypto

set_option autoImplicit false

/-! ## §1 — The general LOCAL no-forgery lemmas (each extracts ONE fixed constraint). -/

/-- **(B) first-row anchor.** Any accepting trace pins `REMOVAL_COUNT ≡ 0 [ZMOD p]` on row 0 — the
field-faithful boundary pin. -/
theorem first_removal_count_zero {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash foldDesc minit mfin maddrs t) (hlen : 0 < t.rows.length) :
    (envAt t 0).loc REMOVAL_COUNT ≡ 0 [ZMOD 2013265921] := by
  have hB := h.rowConstraints 0 hlen (VmConstraint2.base (.boundary VmRow.first firstRcBody))
    (by simp [foldDesc, foldConstraints])
  simp only [VmConstraint2.holdsAt] at hB
  rw [show ((0 : Nat) == 0) = true from rfl, holdsVm_boundaryFirst_true] at hB
  simpa [firstRcBody, EmittedExpr.eval] using hB

/-- **(A + increment window) increment faithfulness — THE core no-forgery.** On a REMOVAL row `i` that
is not the last row, the counter advances by EXACTLY one mod `p`: `RC (i+1) ≡ RC i + 1 [ZMOD p]`. The
prover cannot make the count jump — the free aux column that admitted the k-forgery is now bound to
`RC + 1` by (A), and the increment window copies it into the next row's counter. (Honestly a
congruence: over the field a counter wraps after `p` removal rows; the headline collapses the chain
once, under canonicality + the length bound.) -/
theorem removal_count_increment_faithful {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash foldDesc minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : i + 1 ≠ t.rows.length)
    (hrt : (envAt t i).loc ROW_TYPE = 0) :
    (envAt t (i + 1)).loc REMOVAL_COUNT
      ≡ (envAt t i).loc REMOVAL_COUNT + 1 [ZMOD 2013265921] := by
  have hlf : (i + 1 == t.rows.length) = false := by simp only [beq_eq_false_iff_ne]; exact hnl
  -- (A): rcPlusOneBody ≡ 0 on a removal row ⇒ RC_PLUS_ONE ≡ RC + 1
  have hA := h.rowConstraints i hi (VmConstraint2.base (.gate rcPlusOneBody))
    (by simp [foldDesc, foldConstraints])
  simp only [VmConstraint2.holdsAt] at hA
  rw [holdsVm_gate_of_notLast _ _ _ _ hlf] at hA
  have hA' := (gate_modEq_iff (a := (envAt t i).loc REMOVAL_COUNT_PLUS_ONE)
    (b := (envAt t i).loc REMOVAL_COUNT + 1)
    (by simp only [rcPlusOneBody, EmittedExpr.eval, hrt]; ring)).mp hA
  -- increment window: nxt RC ≡ loc RC_PLUS_ONE on a removal row
  have hW := h.rowConstraints i hi (VmConstraint2.windowGate ⟨removalIncrBody, true⟩)
    (by simp [foldDesc, foldConstraints])
  simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt] at hW
  have hW' := (gate_modEq_iff (a := (envAt t i).nxt REMOVAL_COUNT)
    (b := (envAt t i).loc REMOVAL_COUNT_PLUS_ONE)
    (by simp only [removalIncrBody, Dregg2.Circuit.DescriptorIR2.WindowExpr.eval, hrt]
        ring)).mp (hW hlf)
  have hnext : (envAt t (i + 1)).loc REMOVAL_COUNT = (envAt t i).nxt REMOVAL_COUNT := rfl
  rw [hnext]
  exact hW'.trans hA'

/-- **(C) summary-carry faithfulness.** On a SUMMARY/pad row `i` (`ROW_TYPE = 1`) that is not the last
row, the count is CONSTANT into the next row mod `p`: `RC (i+1) ≡ RC i [ZMOD p]`. This carries the
total across the summary+pad tail to the last row, which the transition-only increment window leaves
untouched. -/
theorem summary_count_constant {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash foldDesc minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : i + 1 ≠ t.rows.length)
    (hrt : (envAt t i).loc ROW_TYPE = 1) :
    (envAt t (i + 1)).loc REMOVAL_COUNT ≡ (envAt t i).loc REMOVAL_COUNT [ZMOD 2013265921] := by
  have hlf : (i + 1 == t.rows.length) = false := by simp only [beq_eq_false_iff_ne]; exact hnl
  have hC := h.rowConstraints i hi (VmConstraint2.windowGate ⟨rcCarryBody, true⟩)
    (by simp [foldDesc, foldConstraints])
  simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt] at hC
  have hC' := (gate_modEq_iff (a := (envAt t i).nxt REMOVAL_COUNT)
    (b := (envAt t i).loc REMOVAL_COUNT)
    (by simp only [rcCarryBody, Dregg2.Circuit.DescriptorIR2.WindowExpr.eval, hrt]
        ring)).mp (hC hlf)
  have hnext : (envAt t (i + 1)).loc REMOVAL_COUNT = (envAt t i).nxt REMOVAL_COUNT := rfl
  rw [hnext]
  exact hC'

/-- Row-type binary on an ACTIVE (non-last) row (no carrier — the `row_type_binary` gate mod `p`,
collapsed to an EXACT `{0,1}` by `p`'s primality + the canonicality envelope). -/
theorem row_type_binary_active {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash foldDesc minit mfin maddrs t) (hcanon : FoldTraceCanon t)
    (i : Nat) (hi : i < t.rows.length) (hnl : i + 1 ≠ t.rows.length) :
    (envAt t i).loc ROW_TYPE = 0 ∨ (envAt t i).loc ROW_TYPE = 1 := by
  have hlf : (i + 1 == t.rows.length) = false := by simp only [beq_eq_false_iff_ne]; exact hnl
  have hg := h.rowConstraints i hi (VmConstraint2.base (.gate (binaryBody ROW_TYPE)))
    (by simp [foldDesc, foldConstraints])
  simp only [VmConstraint2.holdsAt] at hg
  rw [holdsVm_gate_of_notLast _ _ _ _ hlf] at hg
  simp only [binaryBody, EmittedExpr.eval] at hg
  exact binary_modEq_cases hg (hcanon.rowType i hi)

/-- Last-row summary (no carrier — the `last_row_is_summary` boundary mod `p`, collapsed by the
canonicality envelope). -/
theorem last_row_is_summary {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash foldDesc minit mfin maddrs t) (hlen : 0 < t.rows.length)
    (hcanon : FoldTraceCanon t) :
    (envAt t (t.rows.length - 1)).loc ROW_TYPE = 1 := by
  have hLlt : t.rows.length - 1 < t.rows.length := by omega
  have hLb : (t.rows.length - 1 + 1 == t.rows.length) = true := by
    rw [Nat.sub_add_cancel hlen]; simp
  have hb := h.rowConstraints (t.rows.length - 1) hLlt
    (VmConstraint2.base (.boundary VmRow.last lastSummaryBody)) (by simp [foldDesc, foldConstraints])
  simp only [VmConstraint2.holdsAt] at hb
  rw [hLb, holdsVm_boundaryLast_true] at hb
  have hb' := (gate_modEq_iff (a := (envAt t (t.rows.length - 1)).loc ROW_TYPE) (b := 1)
    (by simp only [lastSummaryBody, EmittedExpr.eval]; ring)).mp hb
  exact eq_of_modEq_of_canon hb' (hcanon.rowType _ hLlt) ⟨by norm_num, by norm_num⟩

/-! ## §2 — The FULL count faithfulness (the induction: `pi[2] = #removal rows`). -/

/-- `removalsBefore t i` — the number of removal rows (`ROW_TYPE = 0`) strictly before row `i`. -/
def removalsBefore (t : VmTrace) (i : Nat) : Nat :=
  (List.range i).countP (fun j => decide ((envAt t j).loc ROW_TYPE = 0))

/-- `removalRowCount t` — the total number of removal rows in the whole trace. -/
def removalRowCount (t : VmTrace) : Nat := removalsBefore t t.rows.length

theorem removalsBefore_succ (t : VmTrace) (i : Nat) :
    removalsBefore t (i + 1)
      = removalsBefore t i + (if (envAt t i).loc ROW_TYPE = 0 then 1 else 0) := by
  unfold removalsBefore
  rw [List.range_succ, List.countP_append]
  congr 1
  by_cases h : (envAt t i).loc ROW_TYPE = 0 <;> simp [h]

/-- **The per-row invariant** — for every row `i`, the counter is CONGRUENT mod `p` to the
removal-row count strictly before `i`. Pure induction on the (A)/(C)/(B)/binary constraints; no
carrier (the binary split consumes the canonicality envelope). The chained congruence is collapsed
once, in `removal_count_faithful`. -/
theorem count_invariant {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash foldDesc minit mfin maddrs t) (hlen : 0 < t.rows.length)
    (hcanon : FoldTraceCanon t) :
    ∀ i, i < t.rows.length →
      (envAt t i).loc REMOVAL_COUNT ≡ (removalsBefore t i : ℤ) [ZMOD 2013265921] := by
  intro i
  induction i with
  | zero =>
    intro _
    simpa [removalsBefore] using first_removal_count_zero h hlen
  | succ k ih =>
    intro hk1
    have hk : k < t.rows.length := by omega
    have hnl : k + 1 ≠ t.rows.length := by omega
    have ihk := ih hk
    rw [removalsBefore_succ]
    rcases row_type_binary_active h hcanon k hk hnl with h0 | h1
    · rw [if_pos h0]
      push_cast
      exact (removal_count_increment_faithful h k hk hnl h0).trans (ihk.add_right 1)
    · have hne : ¬ ((envAt t k).loc ROW_TYPE = 0) := by rw [h1]; decide
      rw [if_neg hne, Nat.add_zero]
      exact (summary_count_constant h k hk hnl h1).trans ihk

/-- **`removal_count_faithful` — THE RUNG-2 NO-FORGERY.** An accepting trace publishes `pi[2]` EXACTLY
equal to the number of removal rows in the trace. The k-forgery (publish any count for a fold with a
different number of removals) is impossible. The mod-`p` congruence chain is collapsed ONCE here:
the published input is canonical (`FoldTraceCanon`), and `removalRowCount t < p` because the count
is bounded by the trace length (`hbound`), so the congruence IS the ℤ equality. -/
theorem removal_count_faithful {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash foldDesc minit mfin maddrs t) (hlen : 0 < t.rows.length)
    (hcanon : FoldTraceCanon t) (hbound : t.rows.length ≤ 2013265921) :
    t.pub PI_REMOVAL_COUNT = (removalRowCount t : ℤ) := by
  have hLlt : t.rows.length - 1 < t.rows.length := by omega
  have hLb : (t.rows.length - 1 + 1 == t.rows.length) = true := by
    rw [Nat.sub_add_cancel hlen]; simp
  -- last-row PI binding: RC (len-1) ≡ pub[2]
  have hp := h.rowConstraints (t.rows.length - 1) hLlt
    (VmConstraint2.base (.piBinding VmRow.last REMOVAL_COUNT PI_REMOVAL_COUNT))
    (by simp [foldDesc, foldConstraints])
  simp only [VmConstraint2.holdsAt] at hp
  rw [hLb, holdsVm_piLast_true] at hp
  have hpub : (envAt t (t.rows.length - 1)).pub PI_REMOVAL_COUNT = t.pub PI_REMOVAL_COUNT := rfl
  rw [hpub] at hp
  -- invariant at row len-1
  have hinv := count_invariant h hlen hcanon (t.rows.length - 1) hLlt
  -- removalRowCount = removalsBefore (len-1), since the last row is a summary
  have hsum := last_row_is_summary h hlen hcanon
  have hne : ¬ ((envAt t (t.rows.length - 1)).loc ROW_TYPE = 0) := by rw [hsum]; decide
  have hlenEq : t.rows.length = (t.rows.length - 1) + 1 := (Nat.sub_add_cancel hlen).symm
  have hrrc : removalRowCount t = removalsBefore t (t.rows.length - 1) := by
    unfold removalRowCount
    conv_lhs => rw [hlenEq]
    rw [removalsBefore_succ, if_neg hne, Nat.add_zero]
  -- the count is bounded by the trace length, hence < p
  have hcount : removalsBefore t (t.rows.length - 1) ≤ t.rows.length - 1 := by
    unfold removalsBefore
    simpa using List.countP_le_length
      (p := fun j => decide ((envAt t j).loc ROW_TYPE = 0)) (l := List.range (t.rows.length - 1))
  have hlt : removalRowCount t < 2013265921 := by omega
  -- chain the congruences: pub[2] ≡ RC (len-1) ≡ removalsBefore (len-1) = removalRowCount
  have hchain : t.pub PI_REMOVAL_COUNT ≡ (removalRowCount t : ℤ) [ZMOD 2013265921] := by
    rw [hrrc]
    exact hp.symm.trans hinv
  -- collapse ONCE: both sides canonical
  exact eq_of_modEq_of_canon hchain hcanon.pubRemovalCount
    ⟨Int.natCast_nonneg _, by exact_mod_cast hlt⟩

/-! ## §3 — THE FORGE: the exact k-forgery the audit found, now a REGRESSION (was-accepted → rejected). -/

/-- The PRE-FIX 17-constraint list — `foldConstraints` WITHOUT (A)/(C)/(B). This is the deployed-DSL
descriptor the forge exploited; kept here ONLY to witness that the forge WAS accepted before the fix. -/
def foldConstraintsPreFix : List VmConstraint2 :=
  [ .base (.gate (binaryBody ROW_TYPE))
  , .base (.gate (binaryBody HASH_VALID))
  , .base (.gate mrmBody)
  , .base (.gate removalHashBody)
  , factHashLookup
  , .base (.piBinding VmRow.first OLD_ROOT PI_OLD_ROOT)
  , .windowGate ⟨constancyBody OLD_ROOT, true⟩
  , .base (.piBinding VmRow.first NEW_ROOT PI_NEW_ROOT)
  , .windowGate ⟨constancyBody NEW_ROOT, true⟩
  , .windowGate ⟨removalIncrBody, true⟩
  , .base (.piBinding VmRow.last PI4_CARRIER PI_TRANSITION_HASH)
  , .windowGate ⟨constancyBody PI4_CARRIER, true⟩
  , .base (.gate rootTransBody)
  , .base (.boundary VmRow.last lastSummaryBody)
  , .base (.piBinding VmRow.last REMOVAL_COUNT PI_REMOVAL_COUNT)
  , .base (.piBinding VmRow.last CHECK_COUNT PI_CHECK_COUNT)
  , .base (.piBinding VmRow.last MEMBERSHIP_ROOT PI_TRANSITION_HASH) ]

def foldDescPreFix : EffectVmDescriptor2 :=
  { name := "dregg-fold-step-v2-prefix", traceWidth := FOLD_WIDTH, piCount := FOLD_PI_COUNT
  , tables := [], constraints := foldConstraintsPreFix, hashSites := [], ranges := [] }

/-- The forging REMOVAL row: identical to `FoldRefine.goodRow0` (a genuine removal of fact `(7,8,9,10)`
against `OLD_ROOT = 100`) EXCEPT `REMOVAL_COUNT_PLUS_ONE` (col 12) is the FREE forged value `9` instead
of the honest `REMOVAL_COUNT + 1 = 1`. -/
def forgeRow0 : Assignment := fun c =>
  ([0, 0, 100, 100, 200, 0, 0, 7, 8, 9, 10, 1, 9, 300, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD c 0

/-- The forging SUMMARY row: identical to `FoldRefine.goodRow1` EXCEPT `REMOVAL_COUNT` (col 5) is the
forged `9` the free increment carried in (the increment window then binds `pub[2] = 9`). -/
def forgeRow1 : Assignment := fun c =>
  ([1, 0, 300, 100, 200, 9, 0, 0, 0, 0, 0, 0, 0, 300, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD c 0

/-- Forged public inputs: `pi[2] = 9` (removal count) — a fold with ONE removal row claiming NINE. -/
def forgePub : Assignment := fun c => ([100, 200, 9, 0, 300, 0] : List ℤ).getD c 0

/-- The 2-row forge trace (one genuine removal + a summary), reusing the honest witness's SOUND
Poseidon2 fact-hash table (the forge does not lie about the fact commitments — it lies about the COUNT
via the free aux column). -/
def forgeTrace : VmTrace :=
  { rows := [forgeRow0, forgeRow1]
  , pub := forgePub
  , tf := fun tbl => match tbl with | .poseidon2 => goodPoseidonTable | _ => [] }

theorem forgeTrace_chipSound : ChipTableSound concreteFoldHash (forgeTrace.tf .poseidon2) := by
  intro r hr
  have hpo : forgeTrace.tf .poseidon2 = goodPoseidonTable := rfl
  rw [hpo, goodPoseidonTable, List.mem_cons, List.mem_singleton] at hr
  rcases hr with rfl | rfl
  · exact ⟨[7, 8, 9, 10, 0, 64207, 1], List.replicate 7 0, by decide, by decide, rfl⟩
  · exact ⟨[0, 0, 0, 0, 0, 64207, 1], List.replicate 7 0, by decide, by decide, rfl⟩

theorem forgeTrace_memLog : Dregg2.Circuit.DescriptorIR2.memLog foldDescPreFix forgeTrace = [] := rfl
theorem forgeTrace_mapLog : Dregg2.Circuit.DescriptorIR2.mapLog foldDescPreFix forgeTrace = [] := rfl

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem forgeTrace_rowConstraints_prefix :
    ∀ i < forgeTrace.rows.length, ∀ c ∈ foldDescPreFix.constraints,
      c.holdsAt concreteFoldHash forgeTrace.tf (envAt forgeTrace i) (i == 0)
        (i + 1 == forgeTrace.rows.length) := by
  intro i hi c hc
  have hlen2 : forgeTrace.rows.length = 2 := rfl
  rw [hlen2] at hi ⊢
  rw [show foldDescPreFix.constraints = foldConstraintsPreFix from rfl] at hc
  interval_cases i
  · rw [show ((0 : Nat) == 0) = true from rfl, show ((0 : Nat) + 1 == 2) = false from rfl]
    fin_cases hc <;>
      first
        | exact True.intro
        | (intro hcon; exact Bool.noConfusion hcon)
        | (intro _; decide)
        | (simp only [VmConstraint2.holdsAt, holdsVm_gate_false]; decide)
        | (simp only [factHashLookup, VmConstraint2.holdsAt, Lookup.holdsAt]; decide)
  · rw [show ((1 : Nat) == 0) = false from rfl, show ((1 : Nat) + 1 == 2) = true from rfl]
    fin_cases hc <;>
      first
        | exact True.intro
        | (intro hcon; exact Bool.noConfusion hcon)
        | (intro _; decide)
        | (simp only [VmConstraint2.holdsAt, holdsVm_gate_false]; decide)
        | (simp only [factHashLookup, VmConstraint2.holdsAt, Lookup.holdsAt]; decide)

/-- **The forge WAS accepted (the non-vacuity pole).** The 2-row forge `Satisfied2`s the PRE-FIX
descriptor — the deployed DSL fold AIR admitted it. -/
theorem forge_satisfied2_prefix :
    Satisfied2 concreteFoldHash foldDescPreFix (fun _ => 0) (fun _ => (0, 0)) [] forgeTrace where
  rowConstraints := forgeTrace_rowConstraints_prefix
  rowHashes := fun i _ => trivial
  rowRanges := fun i _ => by simp [foldDescPreFix]
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [forgeTrace_memLog] at hop; simp at hop
  memDisciplined := by rw [forgeTrace_memLog]; trivial
  memBalanced := by
    rw [forgeTrace_memLog]
    simp [MemoryChecking.MemCheck, MemoryChecking.initSet, MemoryChecking.finalSet]
  memTableFaithful := by rw [forgeTrace_memLog]; rfl
  mapTableFaithful := by rw [forgeTrace_mapLog]; rfl

/-- **THE GATE — the forge is now REJECTED.** The exact accepted-but-non-satisfying witness above is
UNSAT under the fixed `foldDesc`: the (A) `removal_count_plus_one` gate BITES on the removal row (its
forged `REMOVAL_COUNT_PLUS_ONE = 9 ≠ REMOVAL_COUNT + 1 = 1`). A regression: the trace that WAS
`Satisfied2` is now NOT. -/
theorem forge_not_satisfied2_fixed :
    ¬ Satisfied2 concreteFoldHash foldDesc (fun _ => 0) (fun _ => (0, 0)) [] forgeTrace := by
  intro h
  have hA := h.rowConstraints 0 (by decide) (VmConstraint2.base (.gate rcPlusOneBody))
    (by simp [foldDesc, foldConstraints])
  simp only [VmConstraint2.holdsAt] at hA
  rw [holdsVm_gate_of_notLast _ _ _ _
        (show ((0 : Nat) + 1 == forgeTrace.rows.length) = false from rfl)] at hA
  -- The forged removal row's (A) residual is `(1−0)·(9−0−1) = 8`, and `p ∤ 8` — the field gate bites.
  have he : rcPlusOneBody.eval (envAt forgeTrace 0).loc = 8 := by decide
  rw [he] at hA
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp hA
  omega

/-- **The forgery quantified.** The forge published removal count `9` while the trace has EXACTLY ONE
removal row — the k-forgery. It was accepted by the pre-fix descriptor (`forge_satisfied2_prefix`) and
is rejected by the fixed one (`forge_not_satisfied2_fixed`). -/
theorem forge_publishes_wrong_count :
    forgeTrace.pub PI_REMOVAL_COUNT = 9
      ∧ removalRowCount forgeTrace = 1
      ∧ (9 : ℤ) ≠ (removalRowCount forgeTrace : ℤ) := by
  refine ⟨rfl, ?_, ?_⟩
  · decide
  · decide

/-! ## §4 — Non-vacuity, TRUE half: an ACCEPTED honest trace publishes the RIGHT count. -/

/-- **The fix does not break honest proofs, and yields the TRUE count.** `FoldRefine.goodTrace` (a
genuine one-removal fold, `Satisfied2` under the fixed `foldDesc`) publishes `pi[2] = 1 =
removalRowCount goodTrace` — the no-forgery theorem FIRES on a real accepted witness. -/
theorem honest_faithful_goodTrace :
    goodTrace.pub PI_REMOVAL_COUNT = (removalRowCount goodTrace : ℤ)
      ∧ removalRowCount goodTrace = 1 := by
  refine ⟨removal_count_faithful goodTrace_satisfied (by decide) goodTrace_canon (by decide), ?_⟩
  decide

#assert_axioms first_removal_count_zero
#assert_axioms removal_count_increment_faithful
#assert_axioms summary_count_constant
#assert_axioms count_invariant
#assert_axioms removal_count_faithful
#assert_axioms forge_satisfied2_prefix
#assert_axioms forge_not_satisfied2_fixed
#assert_axioms forge_publishes_wrong_count
#assert_axioms honest_faithful_goodTrace

end Dregg2.Circuit.Emit.FoldRung2
