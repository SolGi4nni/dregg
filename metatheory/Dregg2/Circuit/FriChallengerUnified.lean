import Dregg2.Circuit.FriVerifier
import Dregg2.Circuit.FriTranscriptBind
import Dregg2.Tactics

/-!
# Full deployed one-thread challenger — transcript-bound FRI and grinding

## The bug this file closes (executably confirmed)

`concreteFriChecks.foldConsistent` (`FriVerifier.lean:508`) binds its betas argument as
`_betas` and DISCARDS it: every FRI layer is folded with the PROVER-SUPPLIED
`LayerOpening.beta`. The fold betas — which FRI soundness requires to be Fiat-Shamir-random —
are a FREE prover choice in the plain `verifyAlgo`. A forgery that swaps a layer beta and
refolds `finalPoly` is ACCEPTED by `verifyAlgo` (the `#guard`s at the bottom demonstrate it).

## The fix (additive; supersedes `FriTranscriptBind.verifyAlgoTB`)

`deriveTranscript` runs ONE CONTINUED `Challenger` in the exact deployed p3 order:
the three scalar instance preamble absorbs; trace/preprocessed commitments; publics;
constraint-RLC `α`; quotient commitment; OOD `ζ`; all opened evaluations; the PCS
batch-combination challenge; every FRI commitment/`β`; final polynomial; variable-arity
schedule; query-PoW witness absorb and masked squeeze; then the query-index draws.
Every squeeze result and every post-squeeze challenger state is retained in
`DerivedChallenges` instead of being silently discarded.

This SUPERSEDES `verifyAlgoTB` rather than conjoining with it: `verifyAlgoTB`'s
`deriveOod` squeezes ζ as a 1-lane preamble-less thread, which conflicts with the
one-thread `params.extDeg`-lane ζ here — ANDing both would leave no accepting proofs.

## Residual (named honestly)

* **qidx is still bound only to the init-seeded thread.** `verifyAlgo` internally derives
  its query indices from a challenger seeded at `Challenger.init initState` and binds each
  query's `index` to THAT thread. ANDing an additional post-ζ-thread qidx check here is
  unsatisfiable additively (it would force two distinct challenger threads to agree ⇒ zero
  accepting proofs). One-threading the query indices needs editing `verifyAlgo`'s seed —
  not an additive change. So `deriveTranscript.qidx` is COMPUTED (the faithful one-thread
  indices) but NOT yet enforced by `verifyAlgoUnified`.
* **Base-vs-extension representation.** Deployed algebra challenges are quartic extension
  elements; this model represents one as its ordered `params.extDeg = 4` base-lane list.
  `projBeta` is used only by the older scalar `LayerOpening` shell. Replacing that shell
  with an extension-valued fold is the explicitly named `ExtensionFoldWidthResidual`;
  no squeeze or absorb is omitted.
-/

namespace Dregg2.Circuit.FriChallengerUnified

open Dregg2.Circuit.FriVerifier

/-- A name for the one representation mismatch that remains after the full sequencing
cutover: p3 challenges are extension elements, while the old FRI-opening shell stores a
single base element. This proposition is documentary and is never assumed by a theorem. -/
def ExtensionFoldWidthResidual (params : FriParams) : Prop := params.extDeg ≠ 1

/-- Every challenge and checkpoint produced by the ONE continued deployed transcript.
The checkpoints make later refinements state-to-state, rather than merely comparing the
last query indices. -/
structure DerivedChallenges (F : Type) where
  constraintAlpha : List F
  ζ : List F
  openingAlpha : List F
  betas : List (List F)
  powSample : Option Nat
  qidx : List Nat
  postPreamble : Challenger F
  postConstraintAlpha : Challenger F
  postZeta : Challenger F
  postOpeningAlpha : Challenger F
  postFri : Challenger F
  postPow : Challenger F

/-- The three deployed scalar preamble fields have exactly one base-field encoding each. -/
def preambleShape {F : Type} (proof : BatchProofData F) : Bool :=
  decide (proof.degreeBitsPreamble.length = 1)
    && decide (proof.baseDegreeBitsPreamble.length = 1)
    && decide (proof.preprocessedWidthPreamble.length = 1)

/-- Current p3 derives one `log_arity` from each FRI commit-phase opening, requires it in
`1..=maxLogArity`, and observes the schedule after `finalPoly`. The decoder carries the
canonical base-field encodings; this check pins their count and bounds. -/
def logAritiesWellFormed {F : Type} (toNat : F → Nat) (params : FriParams)
    (proof : BatchProofData F) : Bool :=
  decide (proof.friLogArities.length = proof.friCommitments.length)
    && proof.friLogArities.all fun a => decide (0 < toNat a && toNat a ≤ params.maxLogArity)

/-- The deployed `GrindingChallenger::check_witness`: for zero bits it is a literal
no-op; otherwise absorb the singleton witness and mask a FRESH base squeeze. Malformed
witness shape returns `none` and leaves the state available only for deterministic
diagnostics; the verifier rejects it. -/
def deriveQueryPow {F : Type} [Inhabited F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (powBits : Nat)
    (witness : List F) (c : Challenger F) : Option Nat × Challenger F :=
  match witness with
  | [w] =>
      if powBits = 0 then (some 0, c)
      else
        let c := Challenger.observe perm RATE c w
        let (masked, c) := Challenger.sampleBits perm RATE toNat powBits c
        (some masked, c)
  | _ => (none, c)

/-- **The one-thread transcript** — ONE continued `Challenger`, in the deployed p3 order:
`init` → three preamble scalars → trace → optional preprocessed commitment → publics →
constraint `α` → quotient commitment → `ζ` → opened evaluations → PCS opening `α` →
FRI commits/`β`s → final polynomial → log-arities → query witness/fresh masked squeeze →
query indices. This includes every deployed observe/sample site on the non-ZK EffectVm
path. Commit-phase PoW is configured to zero in the deployed Rust, and p3's zero-bit
`check_witness` performs neither an absorb nor a squeeze. -/
def deriveTranscript {F : Type} [Inhabited F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (initState : List F) (logN : Nat)
    (proof : BatchProofData F) (pub : WrapPublics F) : DerivedChallenges F :=
  let c := Challenger.init initState
  let c := Challenger.observeList perm RATE c proof.degreeBitsPreamble
  let c := Challenger.observeList perm RATE c proof.baseDegreeBitsPreamble
  let c := Challenger.observeList perm RATE c proof.preprocessedWidthPreamble
  let postPreamble := c
  let c := Challenger.observeList perm RATE c proof.traceCommit
  let c := Challenger.observeList perm RATE c proof.preprocessedCommit
  let c := Challenger.observeList perm RATE c pub.segment
  let (constraintAlpha, c) := Challenger.sampleExt perm RATE params.extDeg c
  let postConstraintAlpha := c
  let c := Challenger.observeList perm RATE c proof.quotientCommit
  let (zeta, c) := Challenger.sampleExt perm RATE params.extDeg c
  let postZeta := c
  let c := Challenger.observeList perm RATE c proof.openedEvaluations
  let (openingAlpha, c) := Challenger.sampleExt perm RATE params.extDeg c
  let postOpeningAlpha := c
  let (betas, c) := deriveFri perm RATE params proof c
  let c := Challenger.observeList perm RATE c proof.friLogArities
  let postFri := c
  let (powSample, c) := deriveQueryPow perm RATE toNat params.powBits proof.powWitness c
  let postPow := c
  let (qidx, _) := deriveQueryIndices perm RATE toNat params logN c
  { constraintAlpha, ζ := zeta, openingAlpha, betas, powSample, qidx,
    postPreamble, postConstraintAlpha, postZeta, postOpeningAlpha, postFri, postPow }

/-- Project the base-field beta out of a derived `extDeg`-lane extension squeeze: the first
basis coefficient (at `extDeg = 1` the ext element IS its single base lane). The
base-vs-extension residual is named in the module docstring. -/
def projBeta {F : Type} [Inhabited F] (d : List F) : F := d.headD default

/-- **The beta-binding check.** For EVERY query, the prover's per-layer betas
(`q.layers.map (·.beta)`) must equal the transcript-derived betas positionally:
`betas[i] ↔ q.layers[i].beta` (`deriveFri` squeezes one beta per fold-layer commitment, in
fold order; `|betas| = |friCommitments| = |q.layers| − 1`, so the zip covers every derived
beta). This is the check whose ABSENCE is the `_betas` bug. -/
def betasBound {F : Type} [Inhabited F] [DecidableEq F]
    (proof : BatchProofData F) (betas : List (List F)) : Bool :=
  decide (betas.length = proof.friCommitments.length)
    && proof.queries.all fun q =>
      decide (q.layers.length = betas.length + 1)
        && (betas.zip (q.layers.map (·.beta))).all fun (d, b) => decide (b = projBeta d)

/-- Transcript-bound query grinding. This is the deployed check: acceptance is about
the fresh masked squeeze AFTER absorbing the witness, never about the witness's own low
bits. -/
def queryPowCheckUnified {F : Type} [Inhabited F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F) : Bool :=
  match (deriveTranscript perm RATE toNat params initState logN proof pub).powSample with
  | some masked => decide (masked = 0)
  | none => false

/-- All checks that specifically bind the old verifier shell to the deployed continued
challenger. Factored out so the strengthening theorem has a single transparent conjunct. -/
def unifiedTranscriptChecks {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F) : Bool :=
  let d := deriveTranscript perm RATE toNat params initState logN proof pub
  decide (proof.oodPoint = d.ζ)
    && preambleShape proof
    && logAritiesWellFormed toNat params proof
    && queryPowCheckUnified perm RATE toNat params initState logN proof pub
    && betasBound proof d.betas

/-- **The unified verifier**: `verifyAlgo` with the fully-concrete `fullChecks`, AND the
OOD point bound to the one-thread ζ, AND the prover layer betas bound to the one-thread
FRI betas. Acceptance closes the free-beta gap (and the free-ζ gap, on the one thread). -/
def verifyAlgoUnified {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (initState : List F) (logN : Nat)
    (proof : BatchProofData F) (pub : WrapPublics F) : Bool :=
  verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
      initState logN proof pub
    && unifiedTranscriptChecks perm RATE toNat params initState logN proof pub

/-- **Strengthening**: whatever `verifyAlgoUnified` accepts, plain `verifyAlgo` (with the
same concrete `fullChecks`) accepts — so EVERY existing `verifyAlgo`-soundness theorem
transports to the unified verifier unchanged. -/
theorem verifyAlgoUnified_imp_verifyAlgo {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (hacc : verifyAlgoUnified perm RATE toNat params vk core A initState logN proof pub
      = true) :
    verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
      initState logN proof pub = true := by
  unfold verifyAlgoUnified at hacc
  simp only [Bool.and_eq_true] at hacc
  exact hacc.1

#assert_axioms verifyAlgoUnified_imp_verifyAlgo

/-- **The free-beta bug CLOSED.** Unified acceptance FORCES `betasBound`: every
prover-supplied layer beta the derived list covers equals the transcript-derived beta —
the fold betas are no longer a free prover choice. -/
theorem verifyAlgoUnified_forces_betas_bound {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (hacc : verifyAlgoUnified perm RATE toNat params vk core A initState logN proof pub
      = true) :
    betasBound proof
      (deriveTranscript perm RATE toNat params initState logN proof pub).betas = true := by
  unfold verifyAlgoUnified at hacc
  simp only [Bool.and_eq_true] at hacc
  have ht := hacc.2
  unfold unifiedTranscriptChecks at ht
  simp only [Bool.and_eq_true] at ht
  exact ht.2

#assert_axioms verifyAlgoUnified_forces_betas_bound

/-- **The ζ bound, on the one thread.** Unified acceptance forces the prover's OOD point to
equal the one-thread transcript-derived ζ. -/
theorem verifyAlgoUnified_forces_ood_bound {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (hacc : verifyAlgoUnified perm RATE toNat params vk core A initState logN proof pub
      = true) :
    proof.oodPoint
      = (deriveTranscript perm RATE toNat params initState logN proof pub).ζ := by
  unfold verifyAlgoUnified at hacc
  simp only [Bool.and_eq_true] at hacc
  have ht := hacc.2
  unfold unifiedTranscriptChecks at ht
  simp only [Bool.and_eq_true] at ht
  exact of_decide_eq_true ht.1.1.1.1

#assert_axioms verifyAlgoUnified_forces_ood_bound

/-- Unified acceptance forces the deployed transcript-bound grinding check. -/
theorem verifyAlgoUnified_forces_query_pow {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (hacc : verifyAlgoUnified perm RATE toNat params vk core A initState logN proof pub
      = true) :
    queryPowCheckUnified perm RATE toNat params initState logN proof pub = true := by
  unfold verifyAlgoUnified at hacc
  simp only [Bool.and_eq_true] at hacc
  have ht := hacc.2
  unfold unifiedTranscriptChecks at ht
  simp only [Bool.and_eq_true] at ht
  exact ht.1.2

#assert_axioms verifyAlgoUnified_forces_query_pow

/-- A present witness whose transcript-bound masked squeeze is nonzero is rejected. -/
theorem queryPowCheckUnified_rejects_nonzero {F : Type} [Inhabited F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (masked : Nat)
    (hs : (deriveTranscript perm RATE toNat params initState logN proof pub).powSample
      = some masked) (hne : masked ≠ 0) :
    queryPowCheckUnified perm RATE toNat params initState logN proof pub = false := by
  unfold queryPowCheckUnified
  rw [hs]
  exact decide_eq_false hne

#assert_axioms queryPowCheckUnified_rejects_nonzero

/-! ## Non-vacuity + THE TOOTH BITES (executable, mandatory).

A spelled-out concrete ACCEPTING proof (`acceptProof`) over `Nat` with a mixing toy
permutation: `verifyAlgoUnified` returns `true` on it, and its `queries[0].layers[0].beta`
IS the transcript-derived `betas[0]` (guarded literally below). Then the FORGERY
(`forgeProof`): swap that layer beta (`+1`) and refold `finalPoly` consistently — plain
`verifyAlgo` is FOOLED (accepts: the `_betas` bug), `verifyAlgoUnified` REJECTS. -/
section NonVacuity

/-- A mixing toy permutation (affine map then reverse) — enough diffusion that the derived
challenges are nontrivial. The Challenger LOGIC is what's exercised (the real Poseidon2-w16
is KAT-pinned in `Dregg2.Circuit.Poseidon2BabyBearW16`). -/
private def uPerm : List Nat → List Nat := fun s => (s.map (fun v => 5 * v + 1)).reverse

private def uRATE : Nat := 8
private def uInit : List Nat := List.replicate 16 0
private def uToNat : Nat → Nat := id
private def uLogN : Nat := 3

/-- Toy params: ONE query, `powBits = 0` (any witness grinds), `extDeg = 1` (ζ and each
beta are single base lanes — the named residual), `logFinalPolyLen = 0` (constant final
poly, as deployed). -/
private def uParams : FriParams :=
  { logBlowup := 1, numQueries := 1, powBits := 0, maxLogArity := 1,
    logFinalPolyLen := 0, extDeg := 1 }

/-- The toy FRI core (the same shape as `FriVerifier`'s §5 toy): a content-mixing
compression and the linear fold `e0 + beta·e1`. -/
private def uCore : FriCore Nat :=
  { compress := fun a b => [a.headD 0 * 7 + b.headD 0 * 13 + 1],
    foldCombine := fun beta _x e0 e1 => e0 + beta * e1 }

private def uArith : FieldArith Nat :=
  { add := (· + ·), mul := (· * ·), pow := fun b n => b ^ n, zero := 0, one := 1 }

private def uVk : RecursionVk Nat := ⟨fun _ => true⟩
private def uPub : WrapPublics Nat := ⟨[7, 8, 9]⟩

/-- The commitment skeleton: everything the transcript observes BEFORE the fold data.
`ζ` and the derived betas depend only on these fields (plus `pub`), never on
`finalPoly`/`queries`/`oodPoint` — so the honest prover can derive them first and then
build the fold openings around them, exactly as below. -/
private def stubProof : BatchProofData Nat :=
  { degreeBitsPreamble := [3], baseDegreeBitsPreamble := [3],
    preprocessedWidthPreamble := [0], traceCommit := [1, 2, 3],
    friCommitments := [[4, 5]], finalPoly := [0], queries := [],
    exposedSegment := [7, 8, 9], oodPoint := [], quotientCommit := [6],
    openedEvaluations := [11, 12], friLogArities := [1], powWitness := [] }

/-- The one-thread ζ (a singleton at `extDeg = 1`). -/
private def uZeta : List Nat :=
  (deriveTranscript uPerm uRATE uToNat uParams uInit uLogN stubProof uPub).ζ

/-- THE transcript-derived layer-0 beta — `acceptProof.queries[0].layers[0].beta` is
literally this value (guarded below). -/
private def uBeta0 : Nat :=
  projBeta ((deriveTranscript uPerm uRATE uToNat uParams uInit uLogN stubProof uPub).betas.headD [])

/-- Layer 0: opens the trace commitment (empty sibling path ⇒ the leaf IS the root), and
folds with the TRANSCRIPT-DERIVED beta `uBeta0`. -/
private def uL0 : LayerOpening Nat :=
  { beta := uBeta0, x := 5, e0 := 10, e1 := 4, leaf := [1, 2, 3], siblings := [] }

/-- The layer-0 fold value: `e0 + beta·e1`. -/
private def uNext0 : Nat := 10 + uBeta0 * 4

/-- Layer 1: opens the fold-layer commitment `[4,5]`, its `e0` is the layer-0 fold value
(the chain check), and it folds once more to the final constant. (Its own beta is beyond
the derived-beta zip: `|betas| = |layers| − 1`.) -/
private def uL1 : LayerOpening Nat :=
  { beta := 2, x := 3, e0 := uNext0, e1 := 6, leaf := [4, 5], siblings := [] }

/-- The honest final constant: layer 1's fold value. -/
private def uFinal : Nat := uNext0 + 2 * 6

/-- The honest proof, sans queries — `finalPoly` is the genuine refold, `oodPoint` the
one-thread ζ, PoW witness present (`powBits = 0`). -/
private def preProof : BatchProofData Nat :=
  { stubProof with finalPoly := [uFinal], oodPoint := uZeta, powWitness := [0] }

/-- The init-seeded query index `verifyAlgo` binds `queries[i].index` to (the residual
thread — see the module docstring). Depends on `finalPoly`, hence derived AFTER the refold. -/
private def uQidx : List Nat :=
  (deriveQueryIndices uPerm uRATE uToNat uParams uLogN
    (deriveFri uPerm uRATE uParams preProof (Challenger.init uInit)).2).1

/-- **The concrete ACCEPTING witness**: honest openings, transcript-derived beta, ζ, and
query index. -/
private def acceptProof : BatchProofData Nat :=
  { preProof with queries := [{ index := uQidx.headD 0, layers := [uL0, uL1] }] }

-- The witness's layer-0 beta IS (literally) `deriveTranscript`'s `betas[0]`, and its
-- oodPoint IS the one-thread ζ — computed against the FINAL proof, not the stub.
#guard (acceptProof.queries.map fun q => q.layers.map (·.beta)) = [[uBeta0, 2]]
#guard (deriveTranscript uPerm uRATE uToNat uParams uInit uLogN acceptProof uPub).betas.map projBeta
  = [uBeta0]
#guard acceptProof.oodPoint
  = (deriveTranscript uPerm uRATE uToNat uParams uInit uLogN acceptProof uPub).ζ
#guard (deriveTranscript uPerm uRATE uToNat uParams uInit uLogN acceptProof uPub).constraintAlpha.length
  = uParams.extDeg
#guard (deriveTranscript uPerm uRATE uToNat uParams uInit uLogN acceptProof uPub).openingAlpha.length
  = uParams.extDeg
#guard (deriveTranscript uPerm uRATE uToNat uParams uInit uLogN acceptProof uPub).qidx.length
  = uParams.numQueries
#guard preambleShape acceptProof = true
#guard logAritiesWellFormed uToNat uParams acceptProof = true

private def noPreambleProof : BatchProofData Nat :=
  { acceptProof with
    degreeBitsPreamble := ([] : List Nat)
    baseDegreeBitsPreamble := ([] : List Nat)
    preprocessedWidthPreamble := ([] : List Nat) }

-- The omitted preamble is not cosmetic: it shifts the first extension squeeze, and
-- the verifier rejects the malformed three-scalar shape.
#guard (deriveTranscript uPerm uRATE uToNat uParams uInit uLogN noPreambleProof uPub).constraintAlpha
  != (deriveTranscript uPerm uRATE uToNat uParams uInit uLogN acceptProof uPub).constraintAlpha
#guard preambleShape noPreambleProof = false
#guard logAritiesWellFormed uToNat uParams { acceptProof with friLogArities := [] } = false

-- NON-VACUITY: the unified verifier ACCEPTS the honest witness (so does plain verifyAlgo).
#guard verifyAlgoUnified uPerm uRATE uToNat uParams uVk uCore uArith uInit uLogN
  acceptProof uPub = true
#guard verifyAlgo uPerm uRATE uToNat uParams uVk (fullChecks uCore uArith uToNat uParams.powBits)
  uInit uLogN acceptProof uPub = true

/-! ### The forgery: swap the layer-0 beta and refold. -/

/-- The forged beta: the transcript-derived one, shifted. -/
private def fBeta : Nat := uBeta0 + 1

/-- The forger refolds layer 0 with the forged beta… -/
private def fNext0 : Nat := 10 + fBeta * 4

/-- …and the final constant, consistently. -/
private def fFinal : Nat := fNext0 + 2 * 6

private def fPreProof : BatchProofData Nat :=
  { stubProof with finalPoly := [fFinal], oodPoint := uZeta, powWitness := [0] }

/-- The forger recomputes the (init-thread) query index against the forged `finalPoly` —
everything needed is public. -/
private def fQidx : List Nat :=
  (deriveQueryIndices uPerm uRATE uToNat uParams uLogN
    (deriveFri uPerm uRATE uParams fPreProof (Challenger.init uInit)).2).1

/-- **The forgery**: layer-0 beta swapped `uBeta0 → uBeta0 + 1`, fold chain and `finalPoly`
refolded consistently. Internally self-consistent — only the BETA is not the transcript's. -/
private def forgeProof : BatchProofData Nat :=
  { fPreProof with
    queries := [{ index := fQidx.headD 0,
                  layers := [{ uL0 with beta := fBeta }, { uL1 with e0 := fNext0 }] }] }

-- THE TOOTH BITES: plain `verifyAlgo` is FOOLED by the free-beta forgery (the `_betas`
-- bug, live)…
#guard verifyAlgo uPerm uRATE uToNat uParams uVk (fullChecks uCore uArith uToNat uParams.powBits)
  uInit uLogN forgeProof uPub = true
-- …and `verifyAlgoUnified` REJECTS it (only the beta binding differs: ζ still matches).
#guard verifyAlgoUnified uPerm uRATE uToNat uParams uVk uCore uArith uInit uLogN
  forgeProof uPub = false
#guard betasBound forgeProof
  (deriveTranscript uPerm uRATE uToNat uParams uInit uLogN forgeProof uPub).betas = false

/-! ### Transcript-bound grinding bites.

The witness `0` passes the retired self-test for every positive bit count. With the
continued challenger it is absorbed, the next squeeze is nonzero in this fixture, and
the real check rejects it. This directly distinguishes transcript grinding from the
wrong witness-self-test. -/
private def powParams : FriParams := { uParams with powBits := 2 }
private def badTranscriptPow : BatchProofData Nat := { stubProof with powWitness := [0] }

#guard legacyQueryPowSelfCheck uToNat powParams.powBits badTranscriptPow = true
#guard queryPowCheckUnified uPerm uRATE uToNat powParams uInit uLogN badTranscriptPow uPub = false
#guard (deriveTranscript uPerm uRATE uToNat powParams uInit uLogN badTranscriptPow uPub).powSample
  ≠ some 0

end NonVacuity

#assert_axioms deriveTranscript
#assert_axioms deriveQueryPow
#assert_axioms betasBound
#assert_axioms queryPowCheckUnified
#assert_axioms verifyAlgoUnified

end Dregg2.Circuit.FriChallengerUnified
