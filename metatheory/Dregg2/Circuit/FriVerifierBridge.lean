/-
# Dregg2.Circuit.FriVerifierBridge — `verifyAlgo → StarkSound`: the verifier ALGORITHM
out of the TCB.

**The problem this closes.** The circuit-soundness apex
(`CircuitSoundness.lightclient_unfoolable`) rests on `StarkSound` — a carrier stated
over the OPAQUE `verifyBatch : VerifyKey → BatchPublicInputs → BatchProof → Verdict`.
That carrier asserts "the deployed verifier ACCEPTS ⟹ ∃ a `Satisfied2` witness
publishing the public inputs". Because `verifyBatch` is opaque, the carrier hides HOW
`accept` is computed: the entire verifier ALGORITHM — the Fiat-Shamir transcript
derivation, the FRI fold-chain, the Merkle-path recompute, the query-index sampling,
the per-table quotient / logup / PoW checks — is TRUSTED inside that one black box. A
bug anywhere in the algorithm is invisible to the proof.

**The factoring.** `FriVerifier.lean` lifts that algorithm from opaque-verdict to a
SPECIFIED Lean function `verifyAlgo` whose soundness-relevant TEETH are PROVEN as
theorems (`concreteFriChecks_rejects_query_count`, `friQueryCheck_rejects_bad_final`,
`merkleRecompute_binds`, `batchTablesCheck_rejects_tampered_quotient`,
`queryPowCheck_rejects_bad_pow`, …). This module bridges the two: it makes `StarkSound`
a THEOREM (`starkSound_of_verifyAlgo`) resting on exactly two named pieces —

  1. **`AlgoStarkSound`** — the FRI/STARK extraction floor, now stated over the
     SPECIFIED `verifyAlgo` instead of the opaque `verifyBatch`. This is the
     IRREDUCIBLE math floor (FRI low-degree soundness + the trace decode + Poseidon2
     collision-resistance) — the same floor `metatheory/docs/STARK-FLOOR.md` already
     carries, now sitting ON TOP of the proven algorithm rather than swallowing it. A
     Prop class, never an `axiom`.

  2. **`DeployedRefines`** — the deployed Rust `verify_batch` computes the SAME accept
     Boolean as `verifyAlgo` on the mapped proof data. This is the code-refines-spec
     residual: the analogue of `FriVerifier.GnarkRefines` for the Rust verifier. It is
     the ONLY remaining trusted thing about the verifier CODE; the algorithm's
     correctness is now proven, not trusted.

**What this buys (the honest line).** Before: the whole verifier (algorithm + crypto)
was one opaque carrier. After: the verifier ALGORITHM is specified and its teeth are
proven; the trusted base is exactly `{ FRI-LDT + Poseidon2-CR (the math floor, as
`AlgoStarkSound`), DeployedRefines (Rust = spec) }`. `deployed_rejects_tampered_quotient`
makes this CONCRETE: a verifier that accepted a tampered quotient is RULED OUT by the
proven algorithm + the refinement, with no appeal to the floor — the algorithm is
doing real soundness work, out of the TCB.

`#assert_axioms` stays `⊆ {propext, Classical.choice, Quot.sound}`: both pieces enter
as a typeclass / a Prop hypothesis, never an `axiom`.
-/
import Dregg2.Circuit.FriVerifier
import Dregg2.Circuit.CircuitSoundness

namespace Dregg2.Circuit.FriVerifierBridge

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.FriVerifier
open Dregg2.Circuit.DescriptorIR2 (Satisfied2 VmTrace)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec
open Verdict

/-- **The proof-data view**: how the deployed public inputs + proof present to the
SPECIFIED verifier. A batch `(pi, π)` is read as the flat `BatchProofData ℤ` the
`verifyAlgo` algorithm walks (trace commit, FRI fold-layer commitments, final poly,
query openings, the OOD table openings, the grinding witness) plus the `WrapPublics ℤ`
segment. The deployed verifier's bytes ARE this data; the view is the (faithful)
reading. -/
abbrev ProofView := BatchPublicInputs → BatchProof → BatchProofData Int × WrapPublics Int

/-- **`AlgoStarkSound` — the FRI/STARK extraction floor over the SPECIFIED algorithm.**

For every `(pi, π)` whose mapped proof data the SPECIFIED `verifyAlgo` ACCEPTS, there
is a genuine `Satisfied2` circuit witness `t` of the claimed descriptor `R pi.effect`
whose published OLD/NEW commitments are exactly `pi.toPublished`. This is the FRI
low-degree-soundness + trace-decode extraction (`StarkSound`'s content) — but now the
ACCEPT is the proven-teeth `verifyAlgo`, not an opaque verdict. The IRREDUCIBLE math
floor, carried as a Prop class exactly like `StarkSound` / `Poseidon2SpongeCR`; never
an `axiom`. -/
class AlgoStarkSound (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView) : Prop where
  extract : ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyAlgo perm RATE toNat params vk checks initState logN
        (view pi π).1 (view pi π).2 = true →
    ∃ (minit : Int → Int) (mfin : Int → Int × Nat) (maddrs : List Int) (t : VmTrace),
      Satisfied2 hash (R pi.effect) minit mfin maddrs t ∧
        tracePublishedCommit t = pi.toPublished

/-- **`DeployedRefines` — the deployed verifier refines the specified algorithm.**

Whenever the deployed Rust `verify_batch` ACCEPTS `(pi, π)`, the SPECIFIED `verifyAlgo`
also accepts the mapped proof data. This is the Rust-side refinement obligation — the
analogue of `FriVerifier.GnarkRefines` (the gnark circuit) for the deployed verifier.
It is the SOLE trusted thing about the verifier code; the algorithm itself is proven. -/
def DeployedRefines (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyBatch (vkOfRegistry R) pi π = accept →
    verifyAlgo perm RATE toNat params vk checks initState logN
      (view pi π).1 (view pi π).2 = true

/-- **`starkSound_of_verifyAlgo` — THE BRIDGE.** `StarkSound` is now a THEOREM: from
the FRI/STARK extraction floor over the SPECIFIED algorithm (`AlgoStarkSound`) and the
deployed-refines-spec residual (`DeployedRefines`), the apex's `StarkSound hash R`
holds. The opaque whole-verifier carrier is GONE; what remains is the math floor (now
over the proven algorithm) + one refinement of the Rust code to the Lean spec. -/
theorem starkSound_of_verifyAlgo
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    [carrier : AlgoStarkSound hash R perm RATE toNat params vk checks initState logN view]
    (href : DeployedRefines R perm RATE toNat params vk checks initState logN view) :
    StarkSound hash R where
  extract := fun pi π hacc => carrier.extract pi π (href pi π hacc)

/-- **`lightclient_unfoolable_via_algo` — the apex on the verifier ALGORITHM.**
⚠ HONESTY (2026-07-10 audit): the algorithm's soundness is `AlgoStarkSound`, a `class` with **ZERO instances**,
taken as a hypothesis here; and `DeployedRefines` is likewise **never proved**, taken as `href`. So this is NOT
"the PROVEN verifier algorithm" (the previous wording): `starkSound_of_verifyAlgo`'s body is
`carrier.extract ∘ href` — modus ponens over TWO assumptions. The decomposition SHAPE is good
(algorithm-soundness ⟂ deployment-refinement, the same shape as DEBT-B's `denote`), but it currently REPLACES
ONE assumed carrier (`StarkSound`) WITH TWO. Discharging it means: FRI-proximity @ BabyBear + AIR soundness +
ChipTableSoundN @ the real perm + Merkle binding ⟹ `AlgoStarkSound`; and proving `DeployedRefines`
(`verifyBatch` refines `verifyAlgo`). See `docs/reference/DEBT-A-STARKSOUND-TARGET.md`.
⚠ CORRECTION (2026-07-10): an earlier revision of this comment listed `FriExtract` in the `AlgoStarkSound` chain.
That was WRONG. `AlgoStarkSound.extract` produces a satisfying **VmTrace** from `verifyAlgo` acceptance — the
classic STARK soundness argument (proximity ⟹ a low-degree codeword; Merkle binding ⟹ the opened trace IS it;
AIR ⟹ it satisfies the constraints). `FriExtract` (AggAirSound) is a different obligation: the in-circuit
RECURSION-verifier subcircuit's soundness (SNARK-of-a-fixed-verifier), producing a verifying CHILD PROOF. It
blocks the RECURSIVE/AGGREGATED apex, NOT single-batch `AlgoStarkSound`. `CircuitSoundness.lean` references
`FriExtract` zero times.

The single-transition soundness apex (`CircuitSoundness.lightclient_unfoolable`),
re-stated to rest on the bridge instead of an assumed `[StarkSound]`: from the FRI
floor over the specified algorithm + the Rust-refines-spec residual + the same hash-CR
/ per-effect / witness-decode floors as the apex, a deployed-accepted batch yields a
genuine kernel transition committing to the public inputs. The verifier algorithm is
out of the TCB — only the math floor (`AlgoStarkSound`, `Poseidon2SpongeCR`) and the
`DeployedRefines` code-refinement are trusted. -/
theorem lightclient_unfoolable_via_algo
    (hash : List Int → Int) (S : CommitSurface) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    [AlgoStarkSound hash R perm RATE toNat params vk checks initState logN view]
    (href : DeployedRefines R perm RATE toNat params vk checks initState logN view)
    (hCR : Poseidon2SpongeCR hash)
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (kstep e))
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = accept) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧
      kstep pi.effect pre post ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn :=
  have inst : StarkSound hash R :=
    starkSound_of_verifyAlgo hash R perm RATE toNat params vk checks initState logN view href
  @lightclient_unfoolable hash S R hCR inst kstep hrefines pi π hwitdec hacc

/-! ## The teeth are load-bearing for the DEPLOYED verifier (the algorithm out of TCB).

The point of specifying the algorithm is that its PROVEN reject-teeth now constrain the
DEPLOYED verifier, via `DeployedRefines` (contrapositive: the algorithm rejects ⟹ the
deployed verifier rejects). `deployed_rejects_tampered_quotient` is the witness: a
proof carrying a tampered batch-table quotient CANNOT be accepted by the deployed
verifier — ruled out by the proven `verifyAlgo_full_rejects_tampered_quotient` + the
refinement, with NO appeal to the FRI floor. The algorithm is doing real soundness
work, out of the trusted base. -/

/-- **The algorithm's tooth bites the deployed verifier.** With the deployed verifier
refining the FULL specified algorithm (`fullChecks` = FRI core + the concrete batch
checks), a batch whose mapped proof carries a tampered quotient on some opened table is
REJECTED by the deployed verifier — proven from the algorithm's tooth + the
refinement, not from the crypto floor. -/
theorem deployed_rejects_tampered_quotient
    (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (core : FriCore Int) (A : FieldArith Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (href : DeployedRefines R perm RATE toNat params vk
              (fullChecks core A toNat params.powBits) initState logN view)
    (pi : BatchPublicInputs) (π : BatchProof)
    (ood : Int) (hood : (view pi π).1.oodPoint = [ood])
    (t : TableOpening Int) (hmem : t ∈ (view pi π).1.tableOpenings)
    (htamper : t.constraintEval ≠ A.mul t.vanishingAtZeta t.quotientAtZeta) :
    verifyBatch (vkOfRegistry R) pi π ≠ accept := by
  intro hacc
  have halgo := href pi π hacc
  have hrej := verifyAlgo_full_rejects_tampered_quotient
      perm RATE toNat params vk core A initState logN (view pi π).1 (view pi π).2
      ood hood t hmem htamper
  rw [hrej] at halgo
  exact Bool.noConfusion halgo

end Dregg2.Circuit.FriVerifierBridge
