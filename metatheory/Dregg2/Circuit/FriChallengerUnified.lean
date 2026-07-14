import Dregg2.Circuit.FriVerifier
import Dregg2.Circuit.FriTranscriptBind
import Dregg2.Tactics

/-!
# One-thread challenger unification — closing the FREE-FRI-BETA soundness gap

## The bug this file closes (executably confirmed)

`concreteFriChecks.foldConsistent` (`FriVerifier.lean:508`) binds its betas argument as
`_betas` and DISCARDS it: every FRI layer is folded with the PROVER-SUPPLIED
`LayerOpening.beta`. The fold betas — which FRI soundness requires to be Fiat-Shamir-random —
are a FREE prover choice in the plain `verifyAlgo`. A forgery that swaps a layer beta and
refolds `finalPoly` is ACCEPTED by `verifyAlgo` (the `#guard`s at the bottom demonstrate it).

## The fix (additive; supersedes `FriTranscriptBind.verifyAlgoTB`)

`deriveTranscript` runs ONE CONTINUED `Challenger` in the deployed p3 order
(`uni-stark/src/verifier.rs`): observe the trace commitment, observe the public values,
sample α (advance, value discarded), observe the quotient-chunks commitment, sample ζ —
and then CONTINUES the SAME challenger through `FriVerifier.deriveFri` (the FRI betas)
and `FriVerifier.deriveQueryIndices`. `verifyAlgoUnified` is `verifyAlgo` (with the
fully-concrete `fullChecks`) AND the ζ-binding AND the beta-binding (`betasBound`):
acceptance forces every prover-supplied layer beta to equal the transcript-derived one.

This SUPERSEDES `verifyAlgoTB` rather than conjoining with it: `verifyAlgoTB`'s
`deriveOod` squeezes ζ as a 1-lane preamble-less thread, which conflicts with the
one-thread `params.extDeg`-lane ζ here — ANDing both would leave no accepting proofs.

## Residuals (named honestly)

* **qidx is still bound only to the init-seeded thread.** `verifyAlgo` internally derives
  its query indices from a challenger seeded at `Challenger.init initState` and binds each
  query's `index` to THAT thread. ANDing an additional post-ζ-thread qidx check here is
  unsatisfiable additively (it would force two distinct challenger threads to agree ⇒ zero
  accepting proofs). One-threading the query indices needs editing `verifyAlgo`'s seed —
  not an additive change. So `deriveTranscript.qidx` is COMPUTED (the faithful one-thread
  indices) but NOT yet enforced by `verifyAlgoUnified`.
* **ζ width = `params.extDeg`.** The toy fixture uses `extDeg = 1`; the deployment squeezes
  ζ as a degree-4 extension element (`extDeg = 4`) — the standing base-vs-extension-field
  abstraction residual.
* **The degree-bits preamble constants are omitted.** The deployed transcript first observes
  `degree_bits`/`base_degree_bits`/`preprocessed_width`; those absorbs shift every later
  duplexing. As with `deriveFri`/`deriveOod`, the SEQUENCE STRUCTURE is modeled from `init`;
  bit-exact deployed-state fidelity is the standing `TranscriptRefines` obligation.
-/

namespace Dregg2.Circuit.FriChallengerUnified

open Dregg2.Circuit.FriVerifier

/-- The challenges one continued transcript thread derives: the OOD point `ζ`, the FRI fold
betas (one `extDeg`-lane list per fold-layer commitment, in fold order), and the query
indices. -/
structure DerivedChallenges (F : Type) where
  ζ : List F
  betas : List (List F)
  qidx : List Nat

/-- **The one-thread transcript** — ONE continued `Challenger`, in the deployed p3 order:
`init` → observe the trace commitment → observe the public values → sample α at
`params.extDeg` lanes (the constraint-RLC challenge; the sponge advances, the value is
discarded here) → observe the quotient-chunks commitment → sample ζ at `params.extDeg`
lanes → and then the SAME challenger, verbatim, seeds `deriveFri` (the FRI betas) and
`deriveQueryIndices`. This is the unification `FriTranscriptBind` named as the faithful
fix: no per-phase re-`init`, every later challenge downstream of every earlier
observation. -/
def deriveTranscript {F : Type} [Inhabited F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (initState : List F) (logN : Nat)
    (proof : BatchProofData F) (pub : WrapPublics F) : DerivedChallenges F :=
  let c := Challenger.init initState
  let c := Challenger.observeList perm RATE c proof.traceCommit
  let c := Challenger.observeList perm RATE c pub.segment
  let c := (Challenger.sampleExt perm RATE params.extDeg c).2       -- sample α (advance only)
  let c := Challenger.observeList perm RATE c proof.quotientCommit
  let (zeta, c) := Challenger.sampleExt perm RATE params.extDeg c   -- squeeze ζ
  let (betas, c) := deriveFri perm RATE params proof c              -- CONTINUED thread → betas
  let (qidx, _) := deriveQueryIndices perm RATE toNat params logN c -- CONTINUED thread → qidx
  ⟨zeta, betas, qidx⟩

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
  proof.queries.all fun q =>
    (betas.zip (q.layers.map (·.beta))).all fun (d, b) => decide (b = projBeta d)

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
    && decide (proof.oodPoint
        = (deriveTranscript perm RATE toNat params initState logN proof pub).ζ)
    && betasBound proof (deriveTranscript perm RATE toNat params initState logN proof pub).betas

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
  exact hacc.1.1

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
  exact hacc.2

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
  exact of_decide_eq_true hacc.1.2

#assert_axioms verifyAlgoUnified_forces_ood_bound

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
  { traceCommit := [1, 2, 3], friCommitments := [[4, 5]], finalPoly := [0], queries := [],
    exposedSegment := [7, 8, 9], oodPoint := [], quotientCommit := [6], powWitness := [] }

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

end NonVacuity

#assert_axioms deriveTranscript
#assert_axioms betasBound
#assert_axioms verifyAlgoUnified

end Dregg2.Circuit.FriChallengerUnified
