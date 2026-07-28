/-
# `Dregg2.Circuit.OodExtChallengeLayout` — the OOD/column-layout layer and `DecodedLdtLink` at the
QUARTIC-EXTENSION challenge typing, and the EXACT relation to the base-typed forms.

## The defect this repairs (confirmed in the files, not hearsay)

`DecodedLdtLink` (`FriDecodedTraceWitness.lean:450-475`) binds
`∃ (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)` and evaluates
`OodColumnLayout.oodBatchResidual d tr ζ qp : Polynomial BabyBear` at `Λ`, with
`OodQuotientConsistency.exceptionalSet _ : Finset BabyBear` (`OodColumnLayout.lean:109`,
`OodQuotientConsistency.lean:85`). In the DEPLOYED verifier both challenges are `Challenge`, the
quartic extension — the tree's own record says so: "the constraint-RLC `α`, the out-of-domain `ζ`,
and every commit-phase fold `β` are QUARTIC-EXTENSION-FIELD elements"
(`ExtFieldChallenge.lean:8-15`), `singleAirOkExt` takes `alpha zeta : ExtElem F` at `extDeg = 4`
(`ExtFieldChallenge.lean:720-721`), and the opened values are `Challenge` at
`vendor/plonky3-fri-82cfad73/src/verifier.rs:623-640`.

This file authors the extension-typed counterpart ADDITIVELY (no landed definition is edited) and —
this is the part that had to be investigated rather than assumed — proves what actually holds
between the two typings.

## ⚑ THE TRUE RELATION (§3), stated plainly

* **Base solutions LIFT, completely.** Along `algebraMap BabyBear E` the residual family, the
  batching polynomial, the layout equation, and BOTH non-exceptionality side-conditions transport
  (`oodRfamExt_lift`, `oodBatchResidualExt_lift`, `notMem_exceptionalSet_lift`), so
  `decodedLdtLinkExt_of_decodedLdtLink` : `DecodedLdtLink ⟹ DecodedLdtLinkExt`.
* **Extension solutions do NOT descend, and the base equation cannot even EXPRESS the deployed
  one.** Every base-typed layout value is, under the embedding, an element of
  `Set.range (algebraMap BabyBear E)` (`base_layout_value_mem_range`);
  `extLayout_value_beyond_base` produces an extension-typed layout value that is NOT in that range,
  and `fire_extLayout_value_beyond_base` / `fire_extLayout_separation` fire it at the REAL deployed
  descriptor `transferV3`. So the base-typed layout equation is a DIFFERENT equation over a strictly
  smaller value space, not a specialization of the deployed one. (This is a separation of the
  WITNESS families, proved; it is NOT a claim that `DecodedLdtLinkExt ⇏ DecodedLdtLink` as `Prop`s —
  separating those would need an accepting instance of the deployed verifier, which nobody has.)
* **And the lane-0 squeeze cannot rescue it**: `coordFunctional_not_multiplicative` proves that for
  ANY `F`-basis of ANY extension with `1 < finrank`, NO basis-coordinate functional `E → F` is
  multiplicative (were it, it would be an injective `F`-linear map `E → F`, forcing
  `finrank F E ≤ 1`). Fired at the deployed quartic basis (`bb4_lane_not_multiplicative`). This is
  the precise reason "project to lane 0" is not a homomorphic restriction.
* **Nothing downstream is lost.** `mainAirAcceptF_of_oodLayoutExt` proves the EXTENSION-typed layout
  equation still forces the BASE-field per-row AIR conclusion `MainAirAcceptF d t`: the ζ-Schwartz–
  Zippel step runs over `E`, gives the polynomial identity `C.map φ = (Z.map φ) · qp`, and
  evaluating at the EMBEDDED row points plus injectivity of `φ` lands the base-field row vanishing.
  So the repair replaces an unachievable hypothesis with an achievable one at the SAME conclusion.
  ⚠ The Fiat–Shamir PRICING is not re-derived here: what IS proved is that the exceptional-set
  cardinality bound is the same small Nat (`oodBatchResidualExt_exceptionalSet_card_lt`) inside a
  field of size `|E|` rather than `|BabyBear|`, so the ε denominator moves in the favourable
  direction; the extension analogue of the landed `rlc_debatch_error_babybear` probability statement
  is NOT proved in this file.

## The `ζ ↦ ζ^64` decode coordinate (§4)

`FriDecodedDomainRebase` proved the decode and the modeler agree exactly on the `2^21` rows but NOT
as polynomials, the difference being `Z`-divisible and provably nonzero once `2^15 ≤ natDegree p`
(`rebase64_ne_colPoly`) — and the OOD point is BY DEFINITION off the domain. So the OOD point is
taken here in the DECODE coordinate: `liftPoly_rebase64_eval` proves
`(p.map φ).eval (ζ^64) = ((rebase64 p).map φ).eval ζ` for EVERY `ζ : E` (exact, hypothesis-free),
`liftPoly_rebase64_eval_rowPt` composes it with `rebase64_eval_rowPt` at the embedded row points,
and `decodedTr_colPoly_rebase_ext` composes it with `decodedTr_colPoly_rebase` at the very object
`DecodedLdtLink` names.

## What this does NOT close (the honest remainder)

* **The opened VALUES are still single felts.** `TableOpening.constraintEval` /
  `quotientAtZeta` / `vanishingAtZeta : ℤ` — the deployed 4-lane `Challenge` openings squeezed to
  one lane. `DecodedLdtLinkExt` deliberately keeps the deployed opening/Merkle conjuncts BYTE-FOR-
  BYTE as the base link has them and retypes only the CHALLENGES; widening the openings to four
  lanes (and the Merkle recompute to the four committed lanes) is the felt-width wound, named and
  NOT repaired here.
* The DEEP-quotient model (`FriDeepQuotientRlc`) is still not wired to the residual: that needs
  `RlcDistributes` / BCIKS correlated agreement at the deployed parameters, which nobody has proved
  (`FriDeployedExtCode` §5 records the completeness direction and that its union-bound radius leaves
  the unique-decoding regime for `numCols ≥ 2`).
* The verifier-side link (`AcceptsFull` ⟹ the transcript's OOD point IS `ζ^64` and the opened values
  ARE the decode interpolants at it) is `DeployedTraceExtract`'s named residual, untouched.
* The FRI soundness floor is unchanged; retyping the challenges changes no soundness bound (the FS
  denominators are not re-derived here, see the ⚠ above).
* ⚠ **THE SAME DEFECT IS TREE-WIDE — this file repairs ONE consumer, not the class.** The identical
  base-field challenge typing `(ζ Λ : BabyBear)` + `(qp : VmConstraint2 → Polynomial BabyBear)`
  occurs at `AlgoStarkSoundGeneral.lean:143` (`FriLdtExtract`),
  `AlgoStarkSoundTransferV3.lean:114/139/181/228` (`Rfam`, `FriLdtExtractV3`, `hood_of_reductions`,
  `mainAirAcceptF_of_floor`), `OodColumnLayout.lean:96-283` (the whole base-typed modeler),
  `FieldIntegerLift.lean:72/140` (`OodInterpF.ζ`), `FriLdtExtractDeployed.lean:106`,
  `FriVerifierFS.lean:108`, `StarkSoundReduce.lean:91/135/167`, `RlcRomBound.lean:299`, and
  `KprimeCompose.lean:63`. Two RELATED sites of the same class: `LogUpColumnLayout.logupChallenge`
  reads the LogUp bus challenge `α` as a SINGLE base scalar out of a public trace column
  (`challengeCol d`), where the deployed LogUp challenges are likewise `Challenge`; and
  `OodSoundnessGame`'s ε theorems (`oodNonExc_soundness_error_babybear`,
  `rlc_debatch_error_babybear`) price at `|BabyBear| = 2013265921` rather than `|Challenge|`
  (conservative, but not faithful). Nothing above is fixed here.

Sorry-free; no `axiom`; no carrier; all imports read-only.

⚑ **UPDATED 2026-07-25 (cutover).** §1's `liftPoly` (and `notMem_exceptionalSet_lift`, and the toy
`colPoly_tHonest_zero`/`constraintPoly_dArith_tHonest_zero` — which were proved in THREE places) now
live in `Dregg2.Circuit.OodInterpFieldExt`, upstream of `DeployedTraceExtract`, and are `export`ed
back here.  Reason: this module sits BELOW `DeployedTraceExtract` in the import DAG, so a `liftPoly`
defined here could never be named by the deployed extraction chain it is about.  One definition, one
source; every `OodExtChallengeLayout.liftPoly` reference resolves unchanged.
-/
import Dregg2.Circuit.OodInterpFieldExt
import Dregg2.Circuit.FriDeployedExtCode
import Dregg2.Circuit.FriDecodedDomainRebase
import Dregg2.Tactics

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Dregg2.Circuit.OodExtChallengeLayout

open Polynomial
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.DescriptorIR2 (VmTrace EffectVmDescriptor2 VmConstraint2 envAt TraceFamily)
open Dregg2.Circuit.AirChecksSatisfied (MainAirAcceptF isArith arithResidual)
open Dregg2.Circuit.TraceColumnInterp
  (constraintPoly domainSize rowPt constraintPoly_eval_eq_arithResidual)
open Dregg2.Circuit.FieldIntegerLift
  (vanishingPoly vanishingPoly_eval_rowPt babyBear_cast_eq_zero_iff)
open Dregg2.Circuit.OodQuotientConsistency (exceptionalSet ood_consistency)
open Dregg2.Circuit.OodSoundnessGame
  (batchResidual batchResidual_coeff batchResidual_eval rlc_debatch
   batchResidual_natDegree_lt batchResidual_exceptionalSet_card_lt)
open Dregg2.Circuit.OodColumnLayout
  (oodArithList oodRfam oodBatchResidual mem_oodArithList_iff
   oodArithList_transferV3_length oodArithList_transferV3_pos)
open Dregg2.Circuit.RotatedKernelRefinement (transferV3)

/-! ## §1 — The BASE→EXTENSION coefficient lift of the trace-derived polynomials.

The committed trace is BASE-field data, so `constraintPoly` and `vanishingPoly` are genuinely
`Polynomial BabyBear`; what the deployed verifier moves into the extension is the POINT they are
read at and the quotient/challenge algebra around them. So the honest retyping embeds their
COEFFICIENTS and keeps the objects themselves. -/

/-! **⚑ RELOCATED, NOT DUPLICATED.** `liftPoly` and its five lemmas now live in
`Dregg2.Circuit.OodInterpFieldExt`, which sits ABOVE `DeployedTraceExtract` in the import DAG.  This
module is BELOW it (via `FriDecodedDomainRebase → FriDecodedTraceWitness → DeployedTraceExtract`), so
the deployed extraction chain could never have named a `liftPoly` defined here — the ordering problem
the cutover discipline calls out.  Re-exported, so every downstream
`OodExtChallengeLayout.liftPoly` reference resolves unchanged to the SAME constant; there is exactly
one `liftPoly` in the tree. -/
export Dregg2.Circuit.OodInterpFieldExt
  (liftPoly liftPoly_eval_base liftPoly_zero liftPoly_eq_zero_iff liftPoly_sub liftPoly_mul
   notMem_exceptionalSet_lift colPoly_tHonest_zero constraintPoly_dArith_tHonest_zero)

/-! ## §2 — THE EXTENSION-TYPED OOD/COLUMN-LAYOUT LAYER.

Every object of `OodColumnLayout` restated with `ζ Λ : E`, `qp : VmConstraint2 → Polynomial E`,
`exceptionalSet _ : Finset E`. The layout LAWS come through unchanged because `batchResidual` and
its Schwartz–Zippel machinery were already field-generic; what has to be re-proved is the CONSUMER
(§2.3): that the extension-typed equation still forces the BASE-field AIR conclusion. -/

section ExtLayer

variable {E : Type*} [Field E] [Algebra BabyBear E] [DecidableEq E]

/-- **The per-constraint residual family at the EXTENSION challenge typing**:
`R_j = C_j(ζ) − Z(ζ)·q_j(ζ)` with `ζ` an extension element, the committed `C_j`/`Z` lifted
coefficientwise, and `q_j` a genuinely extension-coefficiented quotient (the deployed quotient
chunks carry `Challenge` values, committed as four base lanes). -/
noncomputable def oodRfamExt (E : Type*) [Field E] [Algebra BabyBear E]
    (d : EffectVmDescriptor2) (t : VmTrace) (ζ : E)
    (qp : VmConstraint2 → Polynomial E) : Fin (oodArithList d).length → E :=
  fun j => (liftPoly E (constraintPoly d t ((oodArithList d).get j))).eval ζ
             - (liftPoly E (vanishingPoly t)).eval ζ * (qp ((oodArithList d).get j)).eval ζ

/-- **The RLC batching polynomial at the EXTENSION challenge typing** — `Σ_j Λ^j·R_j` as a
`Polynomial E`, evaluated at an extension `Λ`. This is the object the deployed verifier's batched
constraint opening actually is. -/
noncomputable def oodBatchResidualExt (E : Type*) [Field E] [Algebra BabyBear E]
    (d : EffectVmDescriptor2) (t : VmTrace) (ζ : E)
    (qp : VmConstraint2 → Polynomial E) : Polynomial E :=
  batchResidual (oodRfamExt E d t ζ qp)

/-! ### §2.1 — The layout laws, at the extension typing. -/

/-- Its value at an extension challenge Λ is the batched sum `Σ_j R_j·Λ^j`. -/
theorem oodBatchResidualExt_eval_eq (d : EffectVmDescriptor2) (t : VmTrace) (ζ : E)
    (qp : VmConstraint2 → Polynomial E) (Λ : E) :
    (oodBatchResidualExt E d t ζ qp).eval Λ
      = ∑ j : Fin (oodArithList d).length, oodRfamExt E d t ζ qp j * Λ ^ (j : ℕ) :=
  batchResidual_eval (oodRfamExt E d t ζ qp) Λ

/-- **THE COLUMN-LAYOUT LAW AT THE EXTENSION TYPING**: coefficient `j` of the extension-valued
batched residual is exactly the `j`-th arith constraint's extension-valued residual. -/
theorem oodColumnLayoutExt_law (d : EffectVmDescriptor2) (t : VmTrace) (ζ : E)
    (qp : VmConstraint2 → Polynomial E) (j : Fin (oodArithList d).length) :
    (oodBatchResidualExt E d t ζ qp).coeff (j : ℕ)
      = (liftPoly E (constraintPoly d t ((oodArithList d).get j))).eval ζ
          - (liftPoly E (vanishingPoly t)).eval ζ * (qp ((oodArithList d).get j)).eval ζ :=
  batchResidual_coeff (oodRfamExt E d t ζ qp) j

/-- The degree bound is the same small Nat as at the base typing. -/
theorem oodBatchResidualExt_natDegree_lt (d : EffectVmDescriptor2)
    (hn : 0 < (oodArithList d).length) (t : VmTrace) (ζ : E)
    (qp : VmConstraint2 → Polynomial E) :
    (oodBatchResidualExt E d t ζ qp).natDegree < (oodArithList d).length :=
  batchResidual_natDegree_lt hn (oodRfamExt E d t ζ qp)

/-- The RLC bad-Λ set is the SAME size bound, now inside a field of size `|E|` rather than
`|BabyBear|` — this is exactly where the FS pricing improves under the repair. -/
theorem oodBatchResidualExt_exceptionalSet_card_lt (d : EffectVmDescriptor2)
    (hn : 0 < (oodArithList d).length) (t : VmTrace) (ζ : E)
    (qp : VmConstraint2 → Polynomial E) :
    (exceptionalSet (oodBatchResidualExt E d t ζ qp)).card < (oodArithList d).length :=
  batchResidual_exceptionalSet_card_lt hn (oodRfamExt E d t ζ qp)

/-! ### §2.2 — De-batching at the extension typing. -/

/-- **De-batch over `E`.** If the extension-valued batched residual vanishes at a NON-exceptional
extension challenge `Λ`, every declared arithmetic constraint satisfies its per-constraint OOD
identity — at the extension point `ζ`. -/
theorem oodLayoutExt_debatch (d : EffectVmDescriptor2) (t : VmTrace) (ζ : E)
    (qp : VmConstraint2 → Polynomial E) (Λ : E)
    (heval : (oodBatchResidualExt E d t ζ qp).eval Λ = 0)
    (hLam : Λ ∉ exceptionalSet (oodBatchResidualExt E d t ζ qp)) :
    ∀ c ∈ d.constraints, isArith c →
      (liftPoly E (constraintPoly d t c)).eval ζ
        = (liftPoly E (vanishingPoly t)).eval ζ * (qp c).eval ζ := by
  have hRzero : ∀ j, oodRfamExt E d t ζ qp j = 0 :=
    rlc_debatch (oodRfamExt E d t ζ qp) Λ heval hLam
  intro c hc harith
  have hcf : c ∈ oodArithList d := (mem_oodArithList_iff d c).mpr ⟨hc, harith⟩
  obtain ⟨i, hlt, hget⟩ := List.mem_iff_getElem.mp hcf
  have hj0 : oodRfamExt E d t ζ qp ⟨i, hlt⟩ = 0 := hRzero ⟨i, hlt⟩
  simp only [oodRfamExt, List.get_eq_getElem, hget] at hj0
  exact sub_eq_zero.mp hj0

/-! ### §2.3 — ⚑ THE CONSUMER SURVIVES THE RETYPING: the extension-typed layout equation still
forces the BASE-field per-row AIR conclusion.

This is the load-bearing check. The Schwartz–Zippel step now runs over `E`, producing the
polynomial identity `C.map φ = (Z.map φ)·q` in `Polynomial E`. Evaluating THAT at the EMBEDDED row
points — where `Z` vanishes over the base field — and using injectivity of `φ` recovers exactly the
base-field row vanishing the AIR predicate is stated with. No divisibility descent is needed. -/

/-- The extension-typed per-constraint OOD identity at a non-exceptional extension `ζ` forces the
BASE-field row vanishing of the committed constraint polynomial. -/
theorem constraintPoly_eval_rowPt_eq_zero_of_ext (d : EffectVmDescriptor2)
    (t : VmTrace) (ζ : E) (qp : VmConstraint2 → Polynomial E) (c : VmConstraint2)
    (hood : (liftPoly E (constraintPoly d t c)).eval ζ
        = (liftPoly E (vanishingPoly t)).eval ζ * (qp c).eval ζ)
    (hnonexc : ζ ∉ exceptionalSet
        (liftPoly E (constraintPoly d t c) - liftPoly E (vanishingPoly t) * qp c))
    (i : ℕ) (hi : i < t.rows.length) :
    (constraintPoly d t c).eval (rowPt i) = 0 := by
  have hid : liftPoly E (constraintPoly d t c) = liftPoly E (vanishingPoly t) * qp c :=
    ood_consistency _ _ _ ζ hood hnonexc
  have hev := congrArg (Polynomial.eval (algebraMap BabyBear E (rowPt i))) hid
  rw [liftPoly_eval_base, eval_mul, liftPoly_eval_base, vanishingPoly_eval_rowPt t i hi,
    map_zero, zero_mul] at hev
  exact (algebraMap BabyBear E).injective (by rw [hev, map_zero])

/-- **⚑ THE EXTENSION-TYPED OOD LAYER FORCES `MainAirAcceptF`.** With the challenges drawn from the
extension — as the deployed verifier draws them — the batched layout equation at a non-exceptional
`Λ` plus per-constraint non-exceptionality of `ζ` yields exactly the same base-field per-row AIR
acceptance the base-typed layer yielded. The retyping costs the consumer NOTHING. -/
theorem mainAirAcceptF_of_oodLayoutExt (d : EffectVmDescriptor2) (t : VmTrace)
    (hcap : t.rows.length ≤ domainSize) (ζ Λ : E) (qp : VmConstraint2 → Polynomial E)
    (heval : (oodBatchResidualExt E d t ζ qp).eval Λ = 0)
    (hLam : Λ ∉ exceptionalSet (oodBatchResidualExt E d t ζ qp))
    (hnonexc : ∀ c ∈ d.constraints, isArith c →
        ζ ∉ exceptionalSet
          (liftPoly E (constraintPoly d t c) - liftPoly E (vanishingPoly t) * qp c)) :
    MainAirAcceptF d t := by
  have hood := oodLayoutExt_debatch d t ζ qp Λ heval hLam
  intro i hi c hc
  rw [← babyBear_cast_eq_zero_iff]
  by_cases ha : isArith c
  · rw [← constraintPoly_eval_eq_arithResidual d t hcap i hi c ha]
    exact constraintPoly_eval_rowPt_eq_zero_of_ext d t ζ qp c (hood c hc ha)
      (hnonexc c hc ha) i hi
  · cases c <;> simp_all [isArith, arithResidual]

end ExtLayer

/-! ## §3 — ⚑ THE RELATION BETWEEN THE TWO TYPINGS.

Investigated, not assumed. The answer has two halves and they point in OPPOSITE directions:

* **§3.1 — base solutions LIFT** (everything transports along `algebraMap`, including both
  non-exceptionality side-conditions), so the base-typed statement IMPLIES the extension-typed one;
* **§3.2 — extension solutions DO NOT descend**, and more sharply the base-typed layout equation
  cannot even EXPRESS the deployed value: a concrete extension-typed layout value at the real
  deployed descriptor lies outside `Set.range (algebraMap BabyBear BB4)`, which every base-typed
  layout value is confined to. Together with §3.3 (no basis-coordinate functional is multiplicative)
  this is the precise content of "the base-typed equation is a DIFFERENT equation, not a
  specialization". -/

section Relation

variable {E : Type*} [Field E] [Algebra BabyBear E]

/-! ### §3.1 — THE LIFT. -/

/-- Batching commutes with the coefficient lift. -/
theorem batchResidual_lift {n : ℕ} (R : Fin n → BabyBear) :
    batchResidual (fun j => algebraMap BabyBear E (R j)) = liftPoly E (batchResidual R) := by
  simp only [batchResidual, liftPoly, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]

/-- **The residual family lifts.** At embedded base data the extension-typed residual is the
embedding of the base-typed one — the base layer is exactly the `algebraMap`-image slice. -/
theorem oodRfamExt_lift (d : EffectVmDescriptor2) (t : VmTrace) (ζ : BabyBear)
    (qp : VmConstraint2 → Polynomial BabyBear) (j : Fin (oodArithList d).length) :
    oodRfamExt E d t (algebraMap BabyBear E ζ) (fun c => liftPoly E (qp c)) j
      = algebraMap BabyBear E (oodRfam d t ζ qp j) := by
  simp only [oodRfamExt, oodRfam, liftPoly_eval_base, map_sub, map_mul]

/-- **The batching polynomial lifts.** -/
theorem oodBatchResidualExt_lift (d : EffectVmDescriptor2) (t : VmTrace) (ζ : BabyBear)
    (qp : VmConstraint2 → Polynomial BabyBear) :
    oodBatchResidualExt E d t (algebraMap BabyBear E ζ) (fun c => liftPoly E (qp c))
      = liftPoly E (oodBatchResidual d t ζ qp) := by
  rw [oodBatchResidualExt, oodBatchResidual]
  rw [show oodRfamExt E d t (algebraMap BabyBear E ζ) (fun c => liftPoly E (qp c))
      = fun j => algebraMap BabyBear E (oodRfam d t ζ qp j) from
    funext (fun j => oodRfamExt_lift d t ζ qp j)]
  exact batchResidual_lift (oodRfam d t ζ qp)

/-- **The layout equation lifts.** -/
theorem oodBatchResidualExt_eval_lift (d : EffectVmDescriptor2) (t : VmTrace) (ζ Λ : BabyBear)
    (qp : VmConstraint2 → Polynomial BabyBear) :
    (oodBatchResidualExt E d t (algebraMap BabyBear E ζ)
        (fun c => liftPoly E (qp c))).eval (algebraMap BabyBear E Λ)
      = algebraMap BabyBear E ((oodBatchResidual d t ζ qp).eval Λ) := by
  rw [oodBatchResidualExt_lift, liftPoly_eval_base]

/-- The per-constraint ζ side-condition lifts too (its residual is built with `sub`/`mul`, both of
which commute with the coefficient lift). -/
theorem notMem_exceptionalSet_constraint_lift [DecidableEq E] (d : EffectVmDescriptor2)
    (t : VmTrace) (ζ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear) (c : VmConstraint2)
    (h : ζ ∉ exceptionalSet (constraintPoly d t c - vanishingPoly t * qp c)) :
    algebraMap BabyBear E ζ ∉ exceptionalSet
      (liftPoly E (constraintPoly d t c) - liftPoly E (vanishingPoly t) * liftPoly E (qp c)) := by
  have hrw : liftPoly E (constraintPoly d t c) - liftPoly E (vanishingPoly t) * liftPoly E (qp c)
      = liftPoly E (constraintPoly d t c - vanishingPoly t * qp c) := by
    rw [liftPoly_sub, liftPoly_mul]
  rw [hrw]
  exact notMem_exceptionalSet_lift h

end Relation

/-! ### §3.2 — ⚑ NO DESCENT: the base-typed equation cannot EXPRESS the deployed value.

The lift of §3.1 says the base layer sits inside the extension layer as the `algebraMap`-image
slice. This section shows the inclusion is PROPER in the only way that matters for faithfulness:
every base-typed layout value is confined to `Set.range (algebraMap BabyBear E)`, and a concrete
extension-typed layout value at the real deployed descriptor is NOT in that range. So the two are
not the same equation, and the base-typed one is not a specialization of the deployed one. -/

section NoDescent

variable {E : Type*} [Field E] [Algebra BabyBear E] [DecidableEq E]

/-- Every BASE-typed layout value is, under the embedding, confined to the base field's image. -/
theorem base_layout_value_mem_range (d : EffectVmDescriptor2) (t : VmTrace) (ζ Λ : BabyBear)
    (qp : VmConstraint2 → Polynomial BabyBear) :
    (oodBatchResidualExt E d t (algebraMap BabyBear E ζ)
        (fun c => liftPoly E (qp c))).eval (algebraMap BabyBear E Λ)
      ∈ Set.range (algebraMap BabyBear E) := by
  rw [oodBatchResidualExt_eval_lift]
  exact ⟨_, rfl⟩

/-- **⚑ A DEPLOYED-SHAPE EXTENSION LAYOUT VALUE OUTSIDE THE BASE FIELD.** With a genuinely
extension-valued quotient constant `ξ` (which is exactly what the deployed `quotient : Challenge`
opening is) and a nonvanishing domain vanisher at the OOD point, the extension-typed batched layout
value at `Λ = 0` is `φ(C₀(ζ₀)) − φ(Z(ζ₀))·ξ`, which lies in `range φ` only if `ξ` does. So the
extension-typed layout equation takes values NO base-typed layout equation can take. -/
theorem extLayout_value_beyond_base {ζ₀ : BabyBear} {ξ : E}
    (hξ : ξ ∉ Set.range (algebraMap BabyBear E))
    (d : EffectVmDescriptor2) (hn : 0 < (oodArithList d).length) (t : VmTrace)
    (hZ : (vanishingPoly t).eval ζ₀ ≠ 0) :
    (oodBatchResidualExt E d t (algebraMap BabyBear E ζ₀)
        (fun _ => Polynomial.C ξ)).eval 0 ∉ Set.range (algebraMap BabyBear E) := by
  set c₀ : VmConstraint2 := (oodArithList d).get ⟨0, hn⟩ with hc₀
  set a : BabyBear := (constraintPoly d t c₀).eval ζ₀ with ha
  set b : BabyBear := (vanishingPoly t).eval ζ₀ with hb
  have hval : (oodBatchResidualExt E d t (algebraMap BabyBear E ζ₀)
      (fun _ => Polynomial.C ξ)).eval 0
      = algebraMap BabyBear E a - algebraMap BabyBear E b * ξ := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    have hcoeff : (oodBatchResidualExt E d t (algebraMap BabyBear E ζ₀)
        (fun _ => Polynomial.C ξ)).coeff 0
        = oodRfamExt E d t (algebraMap BabyBear E ζ₀) (fun _ => Polynomial.C ξ) ⟨0, hn⟩ :=
      batchResidual_coeff _ ⟨0, hn⟩
    rw [hcoeff]
    simp only [oodRfamExt, liftPoly_eval_base, Polynomial.eval_C, ← hc₀, ← ha, ← hb]
  rw [hval]
  rintro ⟨s, hs⟩
  have hbne : algebraMap BabyBear E b ≠ 0 :=
    fun h0 => hZ ((algebraMap BabyBear E).injective (by rw [h0, map_zero]))
  refine hξ ⟨(a - s) / b, ?_⟩
  rw [map_div₀, map_sub, div_eq_iff hbne, hs]
  ring

/-- **The same fact as a SEPARATION of witnesses**: the exhibited extension-typed layout value is
attained by NO lifted base-typed witness, for any base `ζ'`, `Λ'`, `qp'`. -/
theorem extLayout_witness_not_lifted {ζ₀ : BabyBear} {ξ : E}
    (hξ : ξ ∉ Set.range (algebraMap BabyBear E))
    (d : EffectVmDescriptor2) (hn : 0 < (oodArithList d).length) (t : VmTrace)
    (hZ : (vanishingPoly t).eval ζ₀ ≠ 0)
    (ζ' Λ' : BabyBear) (qp' : VmConstraint2 → Polynomial BabyBear) :
    (oodBatchResidualExt E d t (algebraMap BabyBear E ζ₀)
        (fun _ => Polynomial.C ξ)).eval 0
      ≠ (oodBatchResidualExt E d t (algebraMap BabyBear E ζ')
          (fun c => liftPoly E (qp' c))).eval (algebraMap BabyBear E Λ') := by
  intro heq
  exact extLayout_value_beyond_base hξ d hn t hZ
    (heq ▸ base_layout_value_mem_range d t ζ' Λ' qp')

end NoDescent

/-! ### §3.3 — ⚑ WHY THE LANE-0 SQUEEZE CANNOT RESCUE THE BASE TYPING.

The tempting move — "read lane 0 of the extension quantities and you are back at the base equation"
— is unavailable, and not for a technical reason: NO basis-coordinate functional of a nontrivial
extension is multiplicative. If one were, it would be an injective `F`-linear map `E → F` (it would
send `1` to `1` and units to units), forcing `finrank F E ≤ finrank F F = 1`. So the base-typed
layout equation is not the lane-0 image of the deployed one; it is a different equation. -/

section LaneProjection

variable {F E r : Type*} [Field F] [Field E] [Algebra F E]

/-- A basis-coordinate functional of `E` over `F`, as an `F`-linear map — the "read lane `i₀`"
operation `FriChallengerUnified.projBeta` performs, in its algebraic form. -/
noncomputable def coordLin (b : Module.Basis r F E) (i₀ : r) : E →ₗ[F] F where
  toFun x := b.repr x i₀
  map_add' := by intro x y; simp
  map_smul' := by intro c x; simp

@[simp] theorem coordLin_apply (b : Module.Basis r F E) (i₀ : r) (x : E) :
    coordLin b i₀ x = b.repr x i₀ := rfl

/-- **⚑ NO BASIS-COORDINATE FUNCTIONAL IS MULTIPLICATIVE** on a nontrivial extension. This is the
precise statement behind "lane-0 projection is not a homomorphism", proved for EVERY basis and
EVERY coordinate. -/
theorem coordFunctional_not_multiplicative (b : Module.Basis r F E) (i₀ : r)
    (h : 1 < Module.finrank F E) :
    ∃ x y : E, b.repr (x * y) i₀ ≠ b.repr x i₀ * b.repr y i₀ := by
  by_contra hcon
  have hmul : ∀ x y : E, coordLin b i₀ (x * y) = coordLin b i₀ x * coordLin b i₀ y := by
    intro x y
    by_contra hne
    exact hcon ⟨x, y, hne⟩
  have hb : coordLin b i₀ (b i₀) = 1 := by
    show b.repr (b i₀) i₀ = 1
    simp
  have hone : coordLin b i₀ 1 = 1 := by
    have hx := hmul (b i₀) 1
    rw [mul_one, hb, one_mul] at hx
    exact hx.symm
  have hinj : Function.Injective (coordLin b i₀) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have hxx := hmul x x⁻¹
    rw [mul_inv_cancel₀ hx0, hone, hx, zero_mul] at hxx
    exact one_ne_zero hxx
  have hle : Module.finrank F E ≤ Module.finrank F F :=
    LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_self] at hle
  omega

end LaneProjection

/-! ## §4 — ⚑ THE OOD POINT IN THE DECODE COORDINATE (`ζ ↦ ζ^64`), AT THE EXTENSION TYPING.

`FriDecodedDomainRebase` §5 established a REAL constraint on how the sub-pieces compose: with the
current `TraceColumnInterp.rowPt`, the decode interpolant `p` and the modeler's `colPoly` agree
exactly on the `2^21` trace rows and are DIFFERENT polynomials once `2^15 ≤ natDegree p`
(`rebase64_ne_colPoly`), the difference being a multiple of the row-vanishing polynomial. The OOD
point is by definition OFF the trace domain, so the correction term does not vanish there.

The resolution taken here is the one that costs nothing now that `ζ` is being retyped anyway: read
the decode side at the DECODE COORDINATE `ζ^64`. The change of variable is exact and
hypothesis-free at the extension typing (`liftPoly_rebase64_eval`), it composes with the base-field
row bridge (`liftPoly_rebase64_eval_rowPt` ∘ `rebase64_eval_rowPt`), and it composes with the
deployed extraction object (`decodedTr_colPoly_rebase_ext` ∘ `decodedTr_colPoly_rebase`). -/

section DecodeCoordinate

open Dregg2.Circuit.FriDecodedDomainRebase
  (rebase rebase64 interpPt rebase64_eval_rowPt decodedTr_colPoly_rebase)
open Dregg2.Circuit.FriBatchedOracle (MatrixOracle)
open Dregg2.Circuit.FriDeployedRateInstance (friSetupDeployed)
open Dregg2.Circuit.CircuitSoundness (BatchPublicInputs BatchProof)
open Dregg2.Circuit.FriDecodedTraceWitness (decodedTr decodedMatrix)

variable {E : Type*} [Field E] [Algebra BabyBear E]

/-- **⚑ THE DECODE COORDINATE, AT THE EXTENSION TYPING.** Reading the lifted decode interpolant at
`ζ^64` IS reading the lifted RE-BASED interpolant at `ζ`, for EVERY extension point `ζ` — exact, no
hypotheses. This is `FriDecodedDomainRebase`'s change of variable transported to the field the
deployed OOD point actually lives in. -/
theorem liftPoly_rebase64_eval (p : Polynomial BabyBear) (ζ : E) :
    (liftPoly E (rebase64 p)).eval ζ = (liftPoly E p).eval (ζ ^ 64) := by
  simp only [rebase64, rebase, liftPoly, Polynomial.map_comp, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]

/-- **The composition with the base-field row bridge.** At an EMBEDDED modeler row point, the
decode-coordinate reading of the lifted interpolant is the embedding of the decode's own row value
— `rebase64_eval_rowPt` transported through the lift. So the decode coordinate agrees with the
modeler exactly on the rows, in the extension, with no correction term. -/
theorem liftPoly_rebase64_eval_rowPt (p : Polynomial BabyBear) (i : Fin (2 ^ 21)) :
    (liftPoly E p).eval ((algebraMap BabyBear E (rowPt (i : ℕ))) ^ 64)
      = algebraMap BabyBear E (p.eval (FriDecodedTraceReadout.rowPt i)) := by
  rw [← liftPoly_rebase64_eval, liftPoly_eval_base, rebase64_eval_rowPt]

/-- **⚑ SUB-PIECE 3 COMPOSED WITH THE RETYPING, AT THE OBJECT `DecodedLdtLink` NAMES.**
`decodedTr_colPoly_rebase` with two extension-typed conjuncts appended: the decode-coordinate
change of variable at every extension point, and the row-level agreement at the embedded modeler
rows. So an extension-typed OOD claim about the decode interpolant at `ζ^64` is exactly a claim
about the re-based polynomial at `ζ`, whose modeler-side interpolant is `colPoly (decodedTr …)`. -/
theorem decodedTr_colPoly_rebase_ext {numCols : ℕ}
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hcols : MatrixOracle.ColsClose friSetupDeployed.C 7340032 (oracle pi π))
    (j : Fin numCols) :
    ∃ p : Polynomial BabyBear,
      p.natDegree < 2 ^ 18 * 8 ∧
      (∀ i : Fin (2 ^ 21),
        decodedMatrix (oracle pi π) hcols i j = p.eval (FriDecodedTraceReadout.rowPt i)) ∧
      Dregg2.Circuit.TraceColumnInterp.colPoly (decodedTr oracle pubA tfam pi π) (j : ℕ)
        = Lagrange.interpolate (Finset.range (2 ^ 21)) interpPt
            (fun i => (rebase64 p).eval (interpPt i)) ∧
      (∀ ζ : E, (liftPoly E p).eval (ζ ^ 64) = (liftPoly E (rebase64 p)).eval ζ) ∧
      (∀ i : Fin (2 ^ 21),
        (liftPoly E p).eval ((algebraMap BabyBear E (rowPt (i : ℕ))) ^ 64)
          = algebraMap BabyBear E (decodedMatrix (oracle pi π) hcols i j)) := by
  obtain ⟨p, hpd, hval, hcol⟩ := decodedTr_colPoly_rebase oracle pubA tfam pi π hcols j
  refine ⟨p, hpd, hval, hcol, fun ζ => (liftPoly_rebase64_eval p ζ).symm, fun i => ?_⟩
  rw [liftPoly_rebase64_eval_rowPt, ← hval i]

end DecodeCoordinate

/-! ## §5 — ⚑ `DecodedLdtLinkExt`: the honest extension-typed residual, and the lift.

Scope discipline: the CHALLENGES (`ζ`, `Λ`) and the quotient family are retyped to the extension —
that is this file's job. The deployed opening/Merkle conjuncts are carried BYTE-FOR-BYTE from the
base link, INCLUDING the single-felt `TableOpening.constraintEval`/`vanishingAtZeta`/
`quotientAtZeta`; widening those to four lanes is the SEPARATE felt-width wound, named in the header
and deliberately not conflated here. -/

section Link

open Dregg2.Circuit.FriBatchedOracle (MatrixOracle)
open Dregg2.Circuit.FriDeployedRateInstance (friSetupDeployed)
open Dregg2.Circuit.CircuitSoundness (BatchPublicInputs BatchProof tracePublishedCommit)
open Dregg2.Circuit.FriDecodedTraceWitness (decodedTr DecodedLdtLink decodedTr_rows_le)
open Dregg2.Circuit.FriVerifierBridge (ProofView)
open Dregg2.Circuit.FriVerifier
  (verifyAlgo BatchProofData WrapPublics FriParams RecursionVk FriCore FieldArith TableOpening
   fullChecks)
open Dregg2.Circuit.OodCommitmentBinding
  (merkleRecomputeZ OpeningColl commitmentOpening_binds_of_noColl openingColl_refutes_poseidon2CR)
open Dregg2.Circuit.OodQuotientConsistency (verifyAlgo_accept_forces_table_identity)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.AlgoStarkSoundGeneral (AcceptsFull)

/-- **⚑ `DecodedLdtLinkExt` — `DecodedLdtLink` WITH THE DEPLOYED CHALLENGE TYPING.** Identical to
`DecodedLdtLink` (`FriDecodedTraceWitness.lean:450`) except that `ζ`, `Λ` are drawn from the
challenge extension `E`, the per-constraint quotients are `Polynomial E`, the batched residual is
`oodBatchResidualExt` (a `Polynomial E`), and both exceptional sets are `Finset E`. The layout
equation's right-hand side is the EMBEDDING of the base link's right-hand side — the deployed
single-felt opening, unchanged. -/
def DecodedLdtLinkExt (E : Type*) [Field E] [Algebra BabyBear E] [DecidableEq E] {numCols : ℕ}
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (d : EffectVmDescriptor2) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    AcceptsFull perm RATE toNat params vk core A initState logN view pi π →
    MatrixOracle.ColsClose friSetupDeployed.C 7340032 (oracle pi π) →
    ∃ (ζ Λ : E) (qp : VmConstraint2 → Polynomial E)
      (topen : TableOpening ℤ) (ood vCommitted root : ℤ) (idx : Nat) (siblings : List ℤ),
      (view pi π).1.oodPoint = [ood] ∧
      topen ∈ (view pi π).1.tableOpenings ∧
      merkleRecomputeZ sponge idx vCommitted siblings = root ∧
      merkleRecomputeZ sponge idx topen.constraintEval siblings = root ∧
      (oodBatchResidualExt E d (decodedTr oracle pubA tfam pi π) ζ qp).eval Λ
        = algebraMap BabyBear E (((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear)) ∧
      Λ ∉ exceptionalSet (oodBatchResidualExt E d (decodedTr oracle pubA tfam pi π) ζ qp) ∧
      (∀ c ∈ d.constraints, isArith c →
          ζ ∉ exceptionalSet
            (liftPoly E (constraintPoly d (decodedTr oracle pubA tfam pi π) c)
              - liftPoly E (vanishingPoly (decodedTr oracle pubA tfam pi π)) * qp c)) ∧
      tracePublishedCommit (decodedTr oracle pubA tfam pi π) = pi.toPublished

/-- **⚑ THE LIFT — `DecodedLdtLink ⟹ DecodedLdtLinkExt`.** Every base-typed witness embeds: the
layout equation, the RLC non-exceptionality of `Λ`, and the per-constraint non-exceptionality of `ζ`
all transport along `algebraMap BabyBear E`. So the extension-typed link is a WEAKER demand than the
base-typed one — which is the point: the deployed verifier supplies extension witnesses, so the
base-typed link demands something the deployed verifier does not provide, while the extension-typed
link demands exactly what it does. -/
theorem decodedLdtLinkExt_of_decodedLdtLink (E : Type*) [Field E] [Algebra BabyBear E]
    [DecidableEq E] {numCols : ℕ}
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (d : EffectVmDescriptor2)
    (h : DecodedLdtLink sponge perm RATE toNat params vk core A initState logN view
      oracle pubA tfam d) :
    DecodedLdtLinkExt E sponge perm RATE toNat params vk core A initState logN view
      oracle pubA tfam d := by
  intro pi π hacc hcols
  obtain ⟨ζ, Λ, qp, topen, ood, vCommitted, root, idx, siblings,
    hoodPt, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc, hPub⟩ := h pi π hacc hcols
  refine ⟨algebraMap BabyBear E ζ, algebraMap BabyBear E Λ, fun c => liftPoly E (qp c),
    topen, ood, vCommitted, root, idx, siblings,
    hoodPt, hmem, hCommitted, hOpened, ?_, ?_, ?_, hPub⟩
  · rw [oodBatchResidualExt_eval_lift, hlayout]
  · rw [oodBatchResidualExt_lift]
    exact notMem_exceptionalSet_lift hLam
  · intro c hc ha
    exact notMem_exceptionalSet_constraint_lift d _ ζ qp c (hnonexc c hc ha)

/-! ### §5.1 — ⚑ THE CONSUMER, AT THE EXTENSION TYPING: `DecodedLdtLinkExt` still delivers
`MainAirAcceptF` on the decoded trace. Same crypto composition as the landed base-typed chain
(`hood_of_reductions`): acceptance forces the batched table identity, the Poseidon2-CR binding
identifies the committed and opened values, so the layout right-hand side is `0`; the RLC de-batch
and the ζ-Schwartz–Zippel step then run over the EXTENSION, and §2.3 lands the base-field per-row
conclusion. -/

/-- **`hood` at the extension typing, ∀ d.** Acceptance + the Poseidon2 collision-resistance binding
+ the extension-typed layout equation + non-exceptional extension `Λ` force every declared
arithmetic constraint's OOD identity — as an equation over the CHALLENGE EXTENSION. -/
theorem hood_of_oodColumnLayoutExt (E : Type*) [Field E] [Algebra BabyBear E] [DecidableEq E]
    (d : EffectVmDescriptor2)
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat)
    (proof : BatchProofData ℤ) (pub : WrapPublics ℤ)
    (hacc : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN proof pub = true)
    (t : VmTrace) (ζ Λ : E) (qp : VmConstraint2 → Polynomial E)
    (topen : TableOpening ℤ) (ood vCommitted root : ℤ) (idx : Nat) (siblings : List ℤ)
    (hoodPt : proof.oodPoint = [ood])
    (hmem : topen ∈ proof.tableOpenings)
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened : merkleRecomputeZ sponge idx topen.constraintEval siblings = root)
    (hno : ¬ OpeningColl sponge idx topen.constraintEval vCommitted siblings)
    (hlayout : (oodBatchResidualExt E d t ζ qp).eval Λ
        = algebraMap BabyBear E (((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear)))
    (hLam : Λ ∉ exceptionalSet (oodBatchResidualExt E d t ζ qp)) :
    ∀ c ∈ d.constraints, isArith c →
      (liftPoly E (constraintPoly d t c)).eval ζ
        = (liftPoly E (vanishingPoly t)).eval ζ * (qp c).eval ζ := by
  have htable : topen.constraintEval = A.mul topen.vanishingAtZeta topen.quotientAtZeta :=
    verifyAlgo_accept_forces_table_identity perm RATE toNat params vk core A initState logN
      proof pub ood hoodPt topen hmem hacc
  have hbind : topen.constraintEval = vCommitted :=
    commitmentOpening_binds_of_noColl sponge hno hCommitted hOpened
  have hvc : vCommitted = A.mul topen.vanishingAtZeta topen.quotientAtZeta := hbind.symm.trans htable
  have heval : (oodBatchResidualExt E d t ζ qp).eval Λ = 0 := by
    rw [hlayout, hvc, sub_self, map_zero]
  exact oodLayoutExt_debatch d t ζ qp Λ heval hLam

/-- **⚑ THE PAYOFF — the retyping costs the consumer NOTHING.** `DecodedLdtLinkExt` at an accepting,
`ColsClose`-close run, plus the Poseidon2 binding, forces exactly the AIR conjunct the base-typed
link forced: `MainAirAcceptF d (decodedTr …)`. So the repair is strictly better — the hypothesis is
achievable (the deployed challenges ARE extension elements) and the conclusion is identical. (The
soundness-ERROR statement is not re-derived at the extension; see the header's ⚠.) -/
theorem mainAirAcceptF_of_decodedLdtLinkExt (E : Type*) [Field E] [Algebra BabyBear E]
    [DecidableEq E] {numCols : ℕ}
    (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (d : EffectVmDescriptor2)
    (hlink : DecodedLdtLinkExt E sponge perm RATE toNat params vk core A initState logN view
      oracle pubA tfam d)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : AcceptsFull perm RATE toNat params vk core A initState logN view pi π)
    (hcols : MatrixOracle.ColsClose friSetupDeployed.C 7340032 (oracle pi π)) :
    MainAirAcceptF d (decodedTr oracle pubA tfam pi π) := by
  obtain ⟨ζ, Λ, qp, topen, ood, vCommitted, root, idx, siblings,
    hoodPt, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc, -⟩ := hlink pi π hacc hcols
  have htable : topen.constraintEval = A.mul topen.vanishingAtZeta topen.quotientAtZeta :=
    verifyAlgo_accept_forces_table_identity perm RATE toNat params vk core A initState logN
      (view pi π).1 (view pi π).2 ood hoodPt topen hmem hacc
  -- ⚠ NOT PORTED IN THIS PASS: the opening data arrives from the `DecodedLdtLinkExt` BUNDLE, which
  -- does not carry the per-run residual, so this site still buys its binding with the REFUTED global
  -- floor. Grandfathered, not new; the port is a conjunct on that bundle, a separate pass.
  have hbind : topen.constraintEval = vCommitted :=
    commitmentOpening_binds_of_noColl sponge
      (fun hc => openingColl_refutes_poseidon2CR sponge idx topen.constraintEval vCommitted
        siblings hc hCR) hCommitted hOpened
  have hvc : vCommitted = A.mul topen.vanishingAtZeta topen.quotientAtZeta := hbind.symm.trans htable
  have heval : (oodBatchResidualExt E d (decodedTr oracle pubA tfam pi π) ζ qp).eval Λ = 0 := by
    rw [hlayout, hvc, sub_self, map_zero]
  exact mainAirAcceptF_of_oodLayoutExt d _ (decodedTr_rows_le oracle pubA tfam pi π)
    ζ Λ qp heval hLam hnonexc

end Link

/-! ## §6 — FIRING: the extension typing is inhabited, and the relation bites, on CONCRETE data.

Three separate obligations, discharged separately:

* §6.1 the extension typing's hypothesis bundle is INHABITED at genuinely NON-BASE challenges on a
  real 2-row trace, and produces a real `MainAirAcceptF` (nothing here is true by emptiness);
* §6.2 the LIFT fires concretely;
* §6.3 the NO-DESCENT separation fires at the REAL deployed descriptor `transferV3`, and the
  lane-projection obstruction fires at the DEPLOYED quartic basis. -/

section Fire

open Dregg2.Circuit.FriDeployedExtCode
  (BB4 bb4Basis bb4_finrank exists_not_mem_range_algebraMap deployed_colsClose_ext_iff extMatrix
   friCodeDeployedExt)
open Dregg2.Circuit.AirChecksSatisfied (dArith tHonest zRow)
open Dregg2.Circuit.DescriptorIR2 (zeroAsg)
open Dregg2.Circuit.FriDecodedTraceWitness (defaultTrace)

/-! ### §6.1 — INHABITED at non-base challenges, on the honest 2-row trace. -/

/-- The extension-typed residual family VANISHES on the honest instance with the zero quotient. -/
theorem oodRfamExt_dArith_tHonest (ζ : BB4) :
    oodRfamExt BB4 dArith tHonest ζ (fun _ => 0) = fun _ => 0 := by
  funext j
  have hc' : (oodArithList dArith).get j = VmConstraint2.base (.gate (.var 0)) := by
    have hmem : (oodArithList dArith).get j ∈ dArith.constraints :=
      ((mem_oodArithList_iff dArith _).mp (List.get_mem _ _)).1
    simpa [dArith] using hmem
  simp only [oodRfamExt, hc', constraintPoly_dArith_tHonest_zero, liftPoly_zero,
    Polynomial.eval_zero, mul_zero, sub_zero]

theorem oodBatchResidualExt_dArith_tHonest (ζ : BB4) :
    oodBatchResidualExt BB4 dArith tHonest ζ (fun _ => 0) = 0 := by
  rw [oodBatchResidualExt, oodRfamExt_dArith_tHonest ζ]
  simp [batchResidual]

/-- **⚑ FIRE — the extension-typed OOD layer is INHABITED AT GENUINELY NON-BASE CHALLENGES, and
DELIVERS.** On the honest 2-row toy instance, with the OOD point AND the RLC challenge both drawn
from `BB4 ∖ image(BabyBear)` (so the witness is NOT a lifted base witness — §3.2's regime), every
hypothesis of `mainAirAcceptF_of_oodLayoutExt` holds and it produces the real per-row AIR acceptance
`MainAirAcceptF dArith tHonest`. Nothing here is vacuous: the trace has rows, the descriptor has a
declared arithmetic constraint, and the challenges are outside the base field. -/
theorem fire_ext_hypotheses_inhabited :
    ∃ ζ Λ : BB4,
      ζ ∉ Set.range (algebraMap BabyBear BB4) ∧
      Λ ∉ Set.range (algebraMap BabyBear BB4) ∧
      MainAirAcceptF dArith tHonest := by
  obtain ⟨ξ, hξ⟩ := exists_not_mem_range_algebraMap (F := BabyBear) (E := BB4)
    (by rw [bb4_finrank]; norm_num)
  refine ⟨ξ, ξ, hξ, hξ, ?_⟩
  refine mainAirAcceptF_of_oodLayoutExt (E := BB4) dArith tHonest ?_ ξ ξ (fun _ => 0) ?_ ?_ ?_
  · simp [tHonest, domainSize]
  · rw [oodBatchResidualExt_dArith_tHonest]; simp
  · rw [oodBatchResidualExt_dArith_tHonest]; simp [exceptionalSet]
  · intro c hc _
    simp only [dArith, List.mem_singleton] at hc
    subst hc
    rw [constraintPoly_dArith_tHonest_zero]
    simp [liftPoly, exceptionalSet]

/-! ### §6.2 — the LIFT fires. -/

/-- **FIRE — the lift transports a concrete base witness.** The base-typed residual family of the
honest instance embeds into the extension-typed one, at the embedded challenge. -/
theorem fire_lift_transports (ζ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
    (j : Fin (oodArithList dArith).length) :
    oodRfamExt BB4 dArith tHonest (algebraMap BabyBear BB4 ζ) (fun c => liftPoly BB4 (qp c)) j
      = algebraMap BabyBear BB4 (oodRfam dArith tHonest ζ qp j) :=
  oodRfamExt_lift dArith tHonest ζ qp j

/-! ### §6.3 — the NO-DESCENT separation, at the REAL deployed descriptor and basis. -/

/-- **⚑ FIRE — a deployed-shape extension layout value at `transferV3` that NO base-typed layout
equation can express.** `transferV3` is the real deployed descriptor (147 arithmetic columns,
`oodArithList_transferV3_length`); the quotient constant is a genuine `Challenge` element outside
the base field, exactly as the deployed `quotient : Challenge` opening is. -/
theorem fire_extLayout_value_beyond_base :
    ∃ ξ : BB4, ξ ∉ Set.range (algebraMap BabyBear BB4) ∧
      (oodBatchResidualExt BB4 transferV3 defaultTrace (algebraMap BabyBear BB4 0)
        (fun _ => Polynomial.C ξ)).eval 0 ∉ Set.range (algebraMap BabyBear BB4) := by
  obtain ⟨ξ, hξ⟩ := exists_not_mem_range_algebraMap (F := BabyBear) (E := BB4)
    (by rw [bb4_finrank]; norm_num)
  refine ⟨ξ, hξ, extLayout_value_beyond_base hξ transferV3 ?_ defaultTrace ?_⟩
  · rw [oodArithList_transferV3_length]; norm_num
  · simp [vanishingPoly, defaultTrace]

/-- **⚑ FIRE — the SEPARATION**: that value is attained by no lifted base-typed witness whatsoever. -/
theorem fire_extLayout_separation :
    ∃ ξ : BB4, ∀ (ζ' Λ' : BabyBear) (qp' : VmConstraint2 → Polynomial BabyBear),
      (oodBatchResidualExt BB4 transferV3 defaultTrace (algebraMap BabyBear BB4 0)
          (fun _ => Polynomial.C ξ)).eval 0
        ≠ (oodBatchResidualExt BB4 transferV3 defaultTrace (algebraMap BabyBear BB4 ζ')
            (fun c => liftPoly BB4 (qp' c))).eval (algebraMap BabyBear BB4 Λ') := by
  obtain ⟨ξ, hξ⟩ := exists_not_mem_range_algebraMap (F := BabyBear) (E := BB4)
    (by rw [bb4_finrank]; norm_num)
  refine ⟨ξ, fun ζ' Λ' qp' => extLayout_witness_not_lifted hξ transferV3 ?_ defaultTrace ?_ ζ' Λ' qp'⟩
  · rw [oodArithList_transferV3_length]; norm_num
  · simp [vanishingPoly, defaultTrace]

/-- **⚑ FIRE — the lane-0 squeeze is not a homomorphism AT THE DEPLOYED QUARTIC BASIS.** Two
`Challenge` values whose lane-0 product differs from the lane-0 of their product. So "project the
extension quantities to lane 0 and you recover the base-typed equation" is FALSE at the deployed
parameters, and the base-typed layout equation is not a restriction of the deployed one. -/
theorem bb4_lane_not_multiplicative :
    ∃ x y : BB4, bb4Basis.repr (x * y) 0 ≠ bb4Basis.repr x 0 * bb4Basis.repr y 0 :=
  coordFunctional_not_multiplicative bb4Basis 0 (by rw [bb4_finrank]; norm_num)

/-- Every lane is equally hopeless — the obstruction is not an artifact of choosing lane `0`. -/
theorem bb4_no_lane_multiplicative (i : Fin 4) :
    ∃ x y : BB4, bb4Basis.repr (x * y) i ≠ bb4Basis.repr x i * bb4Basis.repr y i :=
  coordFunctional_not_multiplicative bb4Basis i (by rw [bb4_finrank]; norm_num)

end Fire

/-! ## §6.4 — the antecedent, stated ENTIRELY at the extension.

`FriDeployedExtCode.deployed_colsClose_ext_iff` proved the literal `DecodedLdtLink` proximity
antecedent is EQUIVALENT to its extension-typed form on the retyped matrix. With that, the whole
consumer chain can be stated with no base-field object in the hypotheses except the committed matrix
itself (which IS base-field data — the deployed commitment is over `Val`). -/

section ExtAntecedent

open Dregg2.Circuit.FriBatchedOracle (MatrixOracle)
open Dregg2.Circuit.FriDeployedRateInstance (friSetupDeployed)
open Dregg2.Circuit.CircuitSoundness (BatchPublicInputs BatchProof)
open Dregg2.Circuit.FriDecodedTraceWitness (decodedTr)
open Dregg2.Circuit.FriVerifierBridge (ProofView)
open Dregg2.Circuit.FriVerifier (FriParams RecursionVk FriCore FieldArith)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.AlgoStarkSoundGeneral (AcceptsFull)
open Dregg2.Circuit.FriDeployedExtCode (BB4 friCodeDeployedExt extMatrix deployed_colsClose_ext_iff)

/-- **⚑ THE CONSUMER WITH A FULLY EXTENSION-TYPED PROXIMITY ANTECEDENT.** The committed matrix's
proximity is stated against the EXTENSION-typed deployed FRI code on the retyped matrix; the
challenges are extension elements; and the conclusion is still the base-field per-row AIR
acceptance. -/
theorem mainAirAcceptF_of_decodedLdtLinkExt_extAntecedent {numCols : ℕ}
    (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (d : EffectVmDescriptor2)
    (hlink : DecodedLdtLinkExt BB4 sponge perm RATE toNat params vk core A initState logN view
      oracle pubA tfam d)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : AcceptsFull perm RATE toNat params vk core A initState logN view pi π)
    (hcols : MatrixOracle.ColsClose friCodeDeployedExt 7340032 (extMatrix BB4 (oracle pi π))) :
    MainAirAcceptF d (decodedTr oracle pubA tfam pi π) :=
  mainAirAcceptF_of_decodedLdtLinkExt BB4 sponge hCR perm RATE toNat params vk core A initState
    logN view oracle pubA tfam d hlink pi π hacc (deployed_colsClose_ext_iff _ |>.mp hcols)

end ExtAntecedent

/-! ## §7 — Axiom hygiene. Every keystone kernel-clean (Lean's own three axioms only). -/

#assert_all_clean [
  oodBatchResidualExt_eval_eq,
  oodColumnLayoutExt_law,
  oodBatchResidualExt_natDegree_lt,
  oodBatchResidualExt_exceptionalSet_card_lt,
  oodLayoutExt_debatch,
  constraintPoly_eval_rowPt_eq_zero_of_ext,
  mainAirAcceptF_of_oodLayoutExt
]

#assert_all_clean [
  batchResidual_lift,
  oodRfamExt_lift,
  oodBatchResidualExt_lift,
  oodBatchResidualExt_eval_lift,
  notMem_exceptionalSet_constraint_lift,
  base_layout_value_mem_range,
  extLayout_value_beyond_base,
  extLayout_witness_not_lifted,
  coordFunctional_not_multiplicative
]

#assert_all_clean [
  liftPoly_rebase64_eval,
  liftPoly_rebase64_eval_rowPt,
  decodedTr_colPoly_rebase_ext,
  decodedLdtLinkExt_of_decodedLdtLink,
  hood_of_oodColumnLayoutExt,
  mainAirAcceptF_of_decodedLdtLinkExt,
  mainAirAcceptF_of_decodedLdtLinkExt_extAntecedent
]

#assert_all_clean [
  oodRfamExt_dArith_tHonest,
  oodBatchResidualExt_dArith_tHonest,
  fire_ext_hypotheses_inhabited,
  fire_lift_transports,
  fire_extLayout_value_beyond_base,
  fire_extLayout_separation,
  bb4_lane_not_multiplicative,
  bb4_no_lane_multiplicative
]

end Dregg2.Circuit.OodExtChallengeLayout
