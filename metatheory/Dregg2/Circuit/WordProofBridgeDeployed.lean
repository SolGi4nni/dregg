/-
# `Dregg2.Circuit.WordProofBridgeDeployed` — CLOSING the word↔proof type-shape gap between
`FriVerifierCompose`'s abstract `WordProofBridge` predicate and the deployed
`DeployedFriEmbedding` / `ColumnDecodeBridge` carriers.

## What this module does (the one-line honest claim)

`FriVerifierCompose` §3 names its blocker (a) — the WORD↔PROOF BRIDGE — as an abstract predicate
`WordProofBridge committed accepts bundleFails isFar` and states, in prose, that "supplying it is
supplying `DeployedTraceExtract.DeployedFriEmbedding`". That sentence was never a Lean term: the two
subtrees (`FriVerifierCompose`, over abstract `Proof`/`Word`; `DeployedTraceExtract`/`FriColumnDecode`,
over the deployed `verifyAlgo`/`BatchProof`/`Int`-columns) never touched. This file WRITES the
implication as a theorem:

    `DeployedFriEmbedding … → WordProofBridge (committed := oracle) (accepts := verifyAlgo)`
        `(bundleFails := ¬ TraceWitnessed) (isFar := (· ∉ friSetupK8.C))`

and pushes it down to the REAL DEPLOYED WORD ENCODING: the committed word is
`decodeColumn (column pi π)` — the mod-`p` reduction of the actual committed `Int` FRI column
(`FriColumnDecode.decodeColumn`), so the bridge is stated over the object the deployed proof carries,
not an abstract stand-in.

The proof is one line of logic — the bridge IS `decode_trace`, contrapositively: on `verifyAlgo`-accept,
if the extraction bundle (`TraceWitnessed`) FAILS then the committed oracle cannot be a genuine
low-degree codeword (`∉ friSetupK8.C`), because a codeword-committed accepting run yields
`TraceWitnessed` by `decode_trace`. Feeding this into `FriVerifierCompose.bundleFail_imp_far_of_bridge`
gives the containment `accepts ∧ bundleFails ⊆ accepts ∧ isFar` the compose step consumes.

## What this DOES and DOES NOT do (the honest scope, at current resolution)

DOES: connect the compose-file's `WordProofBridge` predicate to the in-tree `DeployedFriEmbedding`
carrier — the type-shape gap `FriVerifierCompose` blocker (a) flags ("supplying WordProofBridge is
supplying DeployedFriEmbedding") is now a proven implication, over the deployed `Int`-column encoding.

DOES NOT: discharge `DeployedFriEmbedding` / `ColumnDecodeBridge` itself. Those remain the assumed
carriers — `ColumnDecodeBridge.accept_chains` still carries the four verifier-side sub-seams
(`FriColumnDecode` docstring: (a) Merkle commitment→total-column extraction, (b) the PROBABILISTIC
spot-check→full-domain FRI query-soundness step, (c) the `foldCombine`-mod-`p` pin, (d) transcript
rewind). And two things `FriVerifierCompose` §3 names remain open and are NOT touched here:
  * the `isFar := (· ∉ friSetupK8.C)` used here is 0-farness ("not a codeword"). At the deployed
    arity-8 unique-decoding radius the embedding's `accept_folds` + `friProximityK8_discharge0` make
    that event deterministically empty on accepting runs, so `εQuery` here is discharged by the
    DETERMINISTIC embedding hypothesis, NOT paid probabilistically. Reconciling 0-farness with
    `epsQuery`'s δ-far quantitative radius (`FriVerifierQuery`) is the residual the compose file's
    `epsQuery` addend still rests on.
  * blocker (b), the `sampleBits` uniformity defect (`babybear_sampleBits_not_balanced`), is
    untouched.

So the deliverable is precisely: the decode lemma the compose step needs, over the real deployed word
encoding, reducing `WordProofBridge` to the already-named `DeployedFriEmbedding` carrier — no more, and
stated as no more.

## Discipline

Sorry-free; no `axiom`; no `def …Sound`/`…Hard` carrier — the bridge is a theorem from the explicit
`DeployedFriEmbedding` hypothesis. `#assert_axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
ADDITIVE new file; all imports read-only; the shared apex modules are untouched.
-/
import Dregg2.Circuit.FriVerifierCompose
import Dregg2.Circuit.FriColumnDecode

namespace Dregg2.Circuit.WordProofBridgeDeployed

open Dregg2.Circuit.FriVerifierBridge (ProofView DeployedRefines)
open Dregg2.Circuit.FriVerifier (verifyAlgo FriParams RecursionVk FriChecks)
open Dregg2.Circuit.CircuitSoundness (Registry BatchPublicInputs BatchProof)
open Dregg2.Circuit.FriFoldArity (friSetupK8 f0 fHon8 f0_not_mem fHon8_mem)
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.DeployedTraceExtract
  (DeployedFriEmbedding TraceWitnessed DeployedTraceDecode deployedFriEmbedding_of_traceDecode)
open Dregg2.Circuit.FriColumnDecode (decodeColumn)
open Dregg2.Circuit.FriVerifierCompose (WordProofBridge bundleFail_imp_far_of_bridge)

set_option autoImplicit false

/-! ## §1 — THE DECODE BRIDGE: `DeployedFriEmbedding → WordProofBridge`, `isFar := (· ∉ C)`. -/

/-- **⚑ THE WORD↔PROOF BRIDGE, WRITTEN.** From a `DeployedFriEmbedding`, the compose file's abstract
`WordProofBridge` holds at:
  * `committed := fun (pi, π) => emb.oracle pi π` — the committed BabyBear column oracle;
  * `accepts   := fun (pi, π) => verifyAlgo … (view pi π).1 (view pi π).2` — the deployed verifier;
  * `bundleFails := fun (pi, π) => ¬ TraceWitnessed hash (R pi.effect) pi` — the extraction bundle fails;
  * `isFar := fun w => w ∉ friSetupK8.C` — the committed word is not a genuine low-degree codeword.

⚑ THE ARGUMENT — the bridge IS `decode_trace`, contrapositively. On accept, suppose the committed word
were a codeword (`∈ friSetupK8.C`); then `emb.decode_trace` produces `TraceWitnessed`, i.e. the bundle
does NOT fail. Contrapositive: on accept, if the bundle fails, the committed word is far. Nothing here
discharges `DeployedFriEmbedding` — it CONNECTS it to the compose-file predicate. -/
theorem wordProofBridge_of_embedding
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (emb : DeployedFriEmbedding hash R perm RATE toNat params vk checks initState logN view) :
    WordProofBridge
      (fun p : BatchPublicInputs × BatchProof => emb.oracle p.1 p.2)
      (fun p => verifyAlgo perm RATE toNat params vk checks initState logN
        (view p.1 p.2).1 (view p.1 p.2).2)
      (fun p => ¬ TraceWitnessed hash (R p.1.effect) p.1)
      (fun w => w ∉ friSetupK8.C) := by
  intro p hacc hfail hmem
  exact hfail (emb.decode_trace p.1 p.2 hacc hmem)

/-! ## §2 — the same, over the DEPLOYED `DeployedTraceDecode` (the shrunk residual). -/

/-- **THE BRIDGE from the shrunk residual.** `DeployedTraceDecode` (accept_folds = the FRI
column-identification residual; ood_decode = the OOD/leg codeword decode) yields the full embedding
by `deployedFriEmbedding_of_traceDecode`, whose `oracle` is `dec.oracle` — so the bridge holds at the
`DeployedTraceDecode`'s own committed oracle. -/
theorem wordProofBridge_of_traceDecode
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (dec : DeployedTraceDecode hash R perm RATE toNat params vk checks initState logN view) :
    WordProofBridge
      (fun p : BatchPublicInputs × BatchProof => dec.oracle p.1 p.2)
      (fun p => verifyAlgo perm RATE toNat params vk checks initState logN
        (view p.1 p.2).1 (view p.1 p.2).2)
      (fun p => ¬ TraceWitnessed hash (R p.1.effect) p.1)
      (fun w => w ∉ friSetupK8.C) :=
  wordProofBridge_of_embedding hash R perm RATE toNat params vk checks initState logN view
    (deployedFriEmbedding_of_traceDecode hash R perm RATE toNat params vk checks initState logN
      view dec)

/-- **⚑ THE BRIDGE OVER THE REAL DEPLOYED WORD ENCODING.** When the residual's committed oracle IS the
mod-`p` decode of a deployed `Int` FRI column (`dec.oracle pi π = decodeColumn (column pi π)` — exactly
what `FriColumnDecode.deployedTraceDecode_of_columnDecode B hood` produces, with `hcol := fun _ _ => rfl`
and `column := B.column`), the `WordProofBridge` is stated over `decodeColumn (column pi π)` — the
object the deployed proof actually carries, not an abstract stand-in. -/
theorem wordProofBridge_decodedColumn
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (dec : DeployedTraceDecode hash R perm RATE toNat params vk checks initState logN view)
    (column : BatchPublicInputs → BatchProof → List Int)
    (hcol : ∀ pi π, dec.oracle pi π = decodeColumn (column pi π)) :
    WordProofBridge
      (fun p : BatchPublicInputs × BatchProof => decodeColumn (column p.1 p.2))
      (fun p => verifyAlgo perm RATE toNat params vk checks initState logN
        (view p.1 p.2).1 (view p.1 p.2).2)
      (fun p => ¬ TraceWitnessed hash (R p.1.effect) p.1)
      (fun w => w ∉ friSetupK8.C) := by
  intro p hacc hfail
  have h : dec.oracle p.1 p.2 ∉ friSetupK8.C :=
    wordProofBridge_of_traceDecode hash R perm RATE toNat params vk checks initState logN
      view dec p hacc hfail
  show decodeColumn (column p.1 p.2) ∉ friSetupK8.C
  rw [← hcol p.1 p.2]
  exact h

/-! ## §3 — plugging into the compose machinery: the containment the compose step consumes. -/

/-- **⚑ THE BRIDGE FEEDS `friLdtExtractV3_rom_of_legs`.** Composing with the compose file's own
`bundleFail_imp_far_of_bridge`: on accept with a failing bundle, the committed word is BOTH accepted
and far — exactly the event `epsQuery` bounds. This is the wiring that lets the deployed embedding
supply the compose step's `wQuery` leg (the `far word passes` event). -/
theorem bridge_feeds_compose
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (emb : DeployedFriEmbedding hash R perm RATE toNat params vk checks initState logN view)
    (p : BatchPublicInputs × BatchProof)
    (hacc : verifyAlgo perm RATE toNat params vk checks initState logN
      (view p.1 p.2).1 (view p.1 p.2).2 = true)
    (hfail : ¬ TraceWitnessed hash (R p.1.effect) p.1) :
    verifyAlgo perm RATE toNat params vk checks initState logN
        (view p.1 p.2).1 (view p.1 p.2).2 = true
      ∧ emb.oracle p.1 p.2 ∉ friSetupK8.C :=
  bundleFail_imp_far_of_bridge
    (wordProofBridge_of_embedding hash R perm RATE toNat params vk checks initState logN view emb)
    p hacc hfail

/-! ## §4 — TEETH: the bridge is NON-VACUOUS and its `isFar` genuinely two-valued.

The conclusion `isFar := (· ∉ friSetupK8.C)` is not a tautology and not always-false: the far word `f0`
satisfies it, the honest codeword `fHon8` refutes it. So the bridge asserts a REAL constraint on the
committed word — and the one thing that would make `wordProofBridge_of_embedding` FALSE (an accepting,
codeword-committed run whose bundle nonetheless fails) is exactly what `decode_trace` forbids. -/

/-- **`isFar` FIRES** — the frequency-8 far word `f0` is far (not a codeword). So the bridge's
conclusion is inhabited: there is a word for which `isFar` genuinely holds. -/
theorem isFar_f0 : f0 ∉ friSetupK8.C := f0_not_mem

/-- **`isFar` is REFUTABLE** — the honest degree-`< 8` codeword `fHon8` is NOT far. So `isFar` is not
the constant-`True` predicate: the bridge's conclusion is a real, falsifiable statement about the
committed word, not a tautology. -/
theorem not_isFar_fHon8 : ¬ (fHon8 ∉ friSetupK8.C) := fun h => h fHon8_mem

/-- **⚑ WHAT WOULD MAKE THE BRIDGE FALSE, AND WHY IT CANNOT.** The bridge fails at `(pi, π)` exactly
when an accepting run has a committed word that is NOT far (`∈ friSetupK8.C`) yet the bundle fails
(`¬ TraceWitnessed`). That configuration directly refutes `emb.decode_trace`, which turns a
codeword-committed accepting run INTO `TraceWitnessed`. So the bridge's truth is precisely
`decode_trace`, contrapositively — non-vacuous, and pinned to a real obligation. -/
theorem bridge_violation_refutes_decode_trace
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (emb : DeployedFriEmbedding hash R perm RATE toNat params vk checks initState logN view)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : verifyAlgo perm RATE toNat params vk checks initState logN
      (view pi π).1 (view pi π).2 = true)
    (hnotfar : ¬ (emb.oracle pi π ∉ friSetupK8.C))
    (hfail : ¬ TraceWitnessed hash (R pi.effect) pi) :
    False :=
  hfail (emb.decode_trace pi π hacc (not_not.mp hnotfar))

#assert_axioms wordProofBridge_of_embedding
#assert_axioms wordProofBridge_of_traceDecode
#assert_axioms wordProofBridge_decodedColumn
#assert_axioms bridge_feeds_compose
#assert_axioms isFar_f0
#assert_axioms not_isFar_fHon8
#assert_axioms bridge_violation_refutes_decode_trace

end Dregg2.Circuit.WordProofBridgeDeployed
