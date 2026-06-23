/-
# Dregg2.Circuit.WitnessExtractV1 — the adversarial-witness EXTRACTOR for the v1 (`EffectCommit`) effects.

`WitnessExtract` discharges the hostile-witness obligation for the v2 (`EffectCommit2`) effect class:
an ARBITRARY satisfying assignment, pinned by the verifier's public-input check to the committed digest
wires, forces the effect's `apex` — no dead whole-trace `hEnc`. This module is the EXACT v1 analog.

The v1 full-state circuit is `E.guardGates ++ [cERest, cEFrame, cETouched, cELog]` (`effectCircuit`). The
four EQ gates read ONLY the eight digest wires `66 .. 73` (`cERest` reads `66/67`, `cEFrame` `68/69`,
`cETouched` `70/71`, `cELog` `72/73`, by their definitions), and the guard gates are local on
`< guardWidth` (`E.guardLocal`). So an adversary's free choice on the OTHER wires — including the two
root wires `64/65`, which `effectCircuit` never gates, and every `w ≥ 74` — is irrelevant; what the
verifier pins is just those gate-relevant wires, via its public-input check against the committed digests.

We name that obligation `PIBindsDigestsV1`: `a` agrees with the honest encoding on the guard region and
the eight digest wires. It is STRICTLY WEAKER than the dead whole-trace `hEnc` (which pinned all wires).
From it + satisfaction we EXTRACT the full apex via the generic `effect_circuit_full_sound` (whose
post-cell map is RECONSTRUCTED by `funext`, grounded on the realizable Poseidon-CR injective digests).

The `AccountsWF` side-conditions on pre/post are the well-formed-accounts hypotheses the executor already
maintains; they pass through unchanged (the extractor does not weaken them).

NON-VACUITY: `effect_extract_rejects_*` — a PI-bound trace whose claimed state VIOLATES the apex (tampered
non-`cell` field / live-bystander cell / wrong touched cell / forged log) is UNSAT. The extractor CONSTRAINS.

ADDITIVE: imports `EffectCommit` only; edits nothing.
-/
import Dregg2.Circuit.EffectCommit

namespace Dregg2.Circuit.WitnessExtractV1

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit
open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective cellLeafInjective
  RestHashIffFrame AccountsWF)
open Dregg2.Exec (RecordKernelState CellId)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the public-input binding the verifier enforces on the gate-relevant wires.

The eight digest wires the four EQ gates compare, plus the guard region. (NO claim on the root wires
`64/65` nor on any `w ≥ 74` — the adversary keeps those.) -/

/-- **`PIBindsDigestsV1 S E pre args post a`** — the verifier's public-input obligation for the v1
circuit: `a` agrees with `encodeE S E pre args post` on (i) the guard region `w < guardWidth` and (ii)
the eight rest/frame/touched/log digest wires `66 .. 73`. STRICTLY WEAKER than `a = encodeE …`. -/
def PIBindsDigestsV1 {St Args : Type} (S : CommitSurface) (E : EffectSpec St Args)
    (pre : St) (args : Args) (post : St) (a : Assignment) : Prop :=
  (∀ w, w < E.guardWidth → a w = E.guardEncode pre args post w)
  ∧ a vERestPre     = encodeE S E pre args post vERestPre
  ∧ a vERestPost    = encodeE S E pre args post vERestPost
  ∧ a vEFramePre    = encodeE S E pre args post vEFramePre
  ∧ a vEFramePost   = encodeE S E pre args post vEFramePost
  ∧ a vETouchedPost = encodeE S E pre args post vETouchedPost
  ∧ a vETouchedExp  = encodeE S E pre args post vETouchedExp
  ∧ a vELogPost     = encodeE S E pre args post vELogPost
  ∧ a vELogExp      = encodeE S E pre args post vELogExp

/-- The honest encoding satisfies the PI obligation (the binding is realizable). -/
theorem encodeE_PIBindsDigestsV1 {St Args : Type} (S : CommitSurface) (E : EffectSpec St Args)
    (pre : St) (args : Args) (post : St) :
    PIBindsDigestsV1 S E pre args post (encodeE S E pre args post) :=
  ⟨fun w hw => encodeE_agrees_guardEncode S E pre args post w hw,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §2 — locality: a PI-bound `a` satisfies `effectCircuit` IFF the honest encoding does. -/

/-- **`satisfiedE_of_PIBindsDigestsV1`** — an ARBITRARY `a` that is PI-bound to the honest encoding's
gate-relevant wires satisfies `effectCircuit E` IFF the honest encoding does. Each EQ gate's holding
under `a` rewrites (via the eight PI equalities) to its holding under `encodeE`; the guard region
transports by `E.guardLocal`. This lets us run `effect_circuit_full_sound` on a trace we did NOT assume
equals the encoder over all wires. -/
theorem satisfiedE_of_PIBindsDigestsV1 {St Args : Type} (S : CommitSurface) (E : EffectSpec St Args)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigestsV1 S E pre args post a) :
    satisfiedE S E a ↔ satisfiedE S E (encodeE S E pre args post) := by
  obtain ⟨hguard, hRPre, hRPost, hFPre, hFPost, hTPost, hTExp, hLPost, hLExp⟩ := hPI
  unfold satisfiedE effectCircuit
  constructor
  · intro hsat c hc
    rcases List.mem_append.mp hc with hcg | hc4
    · -- guard gate: transport via guardLocal.
      have hag : satisfied E.guardGates a := fun c' hc' => hsat c' (List.mem_append_left _ hc')
      have hge : satisfied E.guardGates (E.guardEncode pre args post) :=
        (E.guardLocal a _ hguard).mp hag
      exact (E.guardLocal _ _ (fun w hw => encodeE_agrees_guardEncode S E pre args post w hw)).mpr hge
        c hcg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc4
      have hra := hsat cERest    (by simp [List.mem_append, List.mem_cons])
      have hfa := hsat cEFrame   (by simp [List.mem_append, List.mem_cons])
      have hta := hsat cETouched (by simp [List.mem_append, List.mem_cons])
      have hla := hsat cELog     (by simp [List.mem_append, List.mem_cons])
      rcases hc4 with rfl | rfl | rfl | rfl
      · unfold Constraint.holds cERest at hra ⊢
        simp only [Expr.eval] at hra ⊢; rw [hRPre, hRPost] at hra; exact hra
      · unfold Constraint.holds cEFrame at hfa ⊢
        simp only [Expr.eval] at hfa ⊢; rw [hFPre, hFPost] at hfa; exact hfa
      · unfold Constraint.holds cETouched at hta ⊢
        simp only [Expr.eval] at hta ⊢; rw [hTPost, hTExp] at hta; exact hta
      · unfold Constraint.holds cELog at hla ⊢
        simp only [Expr.eval] at hla ⊢; rw [hLPost, hLExp] at hla; exact hla
  · intro hsat c hc
    rcases List.mem_append.mp hc with hcg | hc4
    · have hge : satisfied E.guardGates (E.guardEncode pre args post) :=
        (E.guardLocal _ _ (fun w hw => encodeE_agrees_guardEncode S E pre args post w hw)).mp
          (fun c' hc' => hsat c' (List.mem_append_left _ hc'))
      exact (E.guardLocal a _ hguard).mpr hge c hcg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc4
      have hre := hsat cERest    (by simp [List.mem_append, List.mem_cons])
      have hfe := hsat cEFrame   (by simp [List.mem_append, List.mem_cons])
      have hte := hsat cETouched (by simp [List.mem_append, List.mem_cons])
      have hle := hsat cELog     (by simp [List.mem_append, List.mem_cons])
      rcases hc4 with rfl | rfl | rfl | rfl
      · unfold Constraint.holds cERest at hre ⊢
        simp only [Expr.eval] at hre ⊢; rw [hRPre, hRPost]; exact hre
      · unfold Constraint.holds cEFrame at hfe ⊢
        simp only [Expr.eval] at hfe ⊢; rw [hFPre, hFPost]; exact hfe
      · unfold Constraint.holds cETouched at hte ⊢
        simp only [Expr.eval] at hte ⊢; rw [hTPost, hTExp]; exact hte
      · unfold Constraint.holds cELog at hle ⊢
        simp only [Expr.eval] at hle ⊢; rw [hLPost, hLExp]; exact hle

/-! ## §3 — the EXTRACTOR: arbitrary satisfying + PI-bound trace ⇒ full apex. -/

/-- **`effect_extract`** — THE v1 adversarial-witness extractor. An ARBITRARY assignment `a` that
(1) satisfies the v1 effect circuit and (2) is `PIBindsDigestsV1`-pinned determines the WHOLE post-state:
`E.apex pre args post`. The adversary keeps the root wires `64/65` and every `w ≥ 74`; the verifier pins
only the eight digest wires + guard region — the genuine ZK soundness obligation, grounded injective by
Poseidon2 CR (`compressNInjective`/`cellLeafInjective`). The `AccountsWF` pre/post conditions are the
executor's standing well-formedness, passed through. -/
theorem effect_extract {St Args : Type} (S : CommitSurface) (E : EffectSpec St Args)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (hGuard : GuardDecodes E)
    (pre : St) (args : Args) (post : St)
    (hwf : AccountsWF (E.view.toKernel pre)) (hwf' : AccountsWF (E.view.toKernel post))
    (a : Assignment)
    (hsat : satisfiedE S E a)
    (hPI : PIBindsDigestsV1 S E pre args post a) :
    E.apex pre args post :=
  effect_circuit_full_sound S E hN hL hRest hLog hGuard pre args post hwf hwf'
    ((satisfiedE_of_PIBindsDigestsV1 S E pre args post a hPI).mp hsat)

/-! ## §4 — NON-VACUITY: anti-ghost teeth. A PI-bound trace whose claimed state VIOLATES the apex is
UNSAT. The extractor CONSTRAINS — a forged/tampered state cannot have a satisfying PI-bound witness. -/

/-- **`effect_extract_rejects_field_tamper`** — a claimed post whose `nullifiers` (any non-`cell`
component) differ from `pre`'s has NO satisfying PI-bound witness. (`cERest` + `RestHashIffFrame`.) -/
theorem effect_extract_rejects_field_tamper {St Args : Type} (S : CommitSurface) (E : EffectSpec St Args)
    (hRest : RestHashIffFrame S.RH)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigestsV1 S E pre args post a)
    (htamper : (E.view.toKernel post).nullifiers ≠ (E.view.toKernel pre).nullifiers) :
    ¬ satisfiedE S E a := by
  intro hsat
  exact effectCircuit_rejects_field_tamper S E hRest pre args post htamper
    ((satisfiedE_of_PIBindsDigestsV1 S E pre args post a hPI).mp hsat)

/-- **`effect_extract_rejects_third_cell`** — a live bystander cell (`c₀ ∈ accounts`, `c₀ ∉ T`) whose
post value differs from pre has NO satisfying PI-bound witness. (`cEFrame` + `FrameDigestBindsCells`.) -/
theorem effect_extract_rejects_third_cell {St Args : Type} (S : CommitSurface) (E : EffectSpec St Args)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (pre : St) (args : Args) (post : St) (a : Assignment) {c₀ : CellId}
    (hPI : PIBindsDigestsV1 S E pre args post a)
    (hc₀ : c₀ ∈ (E.view.toKernel pre).accounts) (hc₀T : c₀ ∉ E.touched pre args)
    (htamper : (E.view.toKernel pre).cell c₀ ≠ (E.view.toKernel post).cell c₀) :
    ¬ satisfiedE S E a := by
  intro hsat
  exact effectCircuit_rejects_third_cell S E hN hL pre args post hc₀ hc₀T htamper
    ((satisfiedE_of_PIBindsDigestsV1 S E pre args post a hPI).mp hsat)

/-- **`effect_extract_rejects_wrong_touched`** — a touched cell whose post value differs from the spec's
`expectedLeaf` has NO satisfying PI-bound witness. (`cETouched` + `FrameDigestBindsCells`.) -/
theorem effect_extract_rejects_wrong_touched {St Args : Type} (S : CommitSurface) (E : EffectSpec St Args)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (pre : St) (args : Args) (post : St) (a : Assignment) {c₀ : CellId}
    (hPI : PIBindsDigestsV1 S E pre args post a)
    (hc₀ : c₀ ∈ E.touched pre args)
    (htamper : (E.view.toKernel post).cell c₀ ≠ E.expectedLeaf pre args c₀) :
    ¬ satisfiedE S E a := by
  intro hsat
  exact effectCircuit_rejects_wrong_touched S E hN hL pre args post hc₀ htamper
    ((satisfiedE_of_PIBindsDigestsV1 S E pre args post a hPI).mp hsat)

/-- **`effect_extract_rejects_log_forge`** — a claimed post-log differing from the spec-predicted
post-log has NO satisfying PI-bound witness. (`cELog` + `logHashInjective`.) -/
theorem effect_extract_rejects_log_forge {St Args : Type} (S : CommitSurface) (E : EffectSpec St Args)
    (hLog : logHashInjective S.LH)
    (pre : St) (args : Args) (post : St) (a : Assignment)
    (hPI : PIBindsDigestsV1 S E pre args post a)
    (htamper : E.view.getLog post ≠ E.postLog pre args) :
    ¬ satisfiedE S E a := by
  intro hsat
  exact effectCircuit_rejects_log_forge S E hLog pre args post htamper
    ((satisfiedE_of_PIBindsDigestsV1 S E pre args post a hPI).mp hsat)

/-! ## §4b — CONCRETE non-vacuity: the four v1 EQ gates REJECT a tampered wire (decidable `#guard`s).
A tampered rest (`66 ≠ 67`), frame-reuse (`68 ≠ 69`), touched (`70 ≠ 71`) or log (`72 ≠ 73`) digest FAILS
its gate — so the extractor's teeth really CONSTRAIN, not vacuously hold. -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

#guard decide (¬ cERest.holds    (fun w => if w = vERestPre then 7 else 0))
#guard decide (¬ cEFrame.holds   (fun w => if w = vEFramePre then 3 else 0))
#guard decide (¬ cETouched.holds (fun w => if w = vETouchedPost then 1 else 0))
#guard decide (¬ cELog.holds     (fun w => if w = vELogPost then 5 else 0))
/- and the all-equal (honest-shaped) assignment is ACCEPTED by all four (not vacuously false). -/
#guard decide (cERest.holds (fun _ => 0) ∧ cEFrame.holds (fun _ => 0)
  ∧ cETouched.holds (fun _ => 0) ∧ cELog.holds (fun _ => 0))

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms encodeE_PIBindsDigestsV1
#assert_axioms satisfiedE_of_PIBindsDigestsV1
#assert_axioms effect_extract
#assert_axioms effect_extract_rejects_field_tamper
#assert_axioms effect_extract_rejects_third_cell
#assert_axioms effect_extract_rejects_wrong_touched
#assert_axioms effect_extract_rejects_log_forge

end Dregg2.Circuit.WitnessExtractV1
