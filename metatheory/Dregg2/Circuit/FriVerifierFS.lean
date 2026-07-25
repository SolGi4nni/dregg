/-
# `Dregg2.Circuit.FriVerifierFS` — STAGE 2: the FS terms become theorems (the first crypto payoff).

`docs/reference/FRI-EXTRACTION-FLOOR-DESIGN.md` §5 Stage 2. Stage 1 (`FriVerifierO`) gave the
faithfulness bridge + the per-path query budget `permCallCount`. This file turns the TWO Fiat–Shamir
non-exceptionality conjuncts of `FriLdtExtractV3` — `Λ ∉ exceptionalSet …` and the per-arith-constraint
`ζ ∉ exceptionalSet …` — from ASSUMED into PROVEN-except-with-ε, over the `RomCounting` counting model.

## The two deliverables

  **1. `ExtractBundleSansFS`** — `FriLdtExtractV3`'s existential body with EXACTLY the two FS conjuncts
  removed (the ten remaining conjuncts copied token-for-token). ⚑ 2026-07-25: the audit gate proving it
  is genuinely the sub-conjunction — `friLdtExtractV3_imp_sansFS` — is DELETED here and RELOCATED to
  `FriFsDecodedOodRepair.friLdtExtractV3Cons_imp_sansFSCons`, the same destructure/reassemble audit at
  the CORRECTED OOD shape. Both the landed gate's premise and its conclusion are PROVED EMPTY at the
  deployed configuration (`deleted_sansFS_gate_premise_was_empty` below,
  `FriFsDecodedOodRepair.extractBundleSansFS_makes_verifyBatch_reject_everything`); the singleton
  `oodPoint = [ood]` at `:112` is the cause. The DEFINITION is retained as the subject of those receipts.

  **2. The FS ε-theorem `fs_epsilon_bound`.** For a Q-attempt oracle adversary (each attempt a FRESH
  squeeze point `∉ S` — the honest carrier, see below), the probability that ANY attempt's derived
  challenge is exceptional OR any grinding attempt hits the PoW mask is

      Pr[ some derived challenge exceptional  ∨  some PoW freebie ]
        ≤ (Q+1) · deg / |F|  +  Q / 2^pow.

  The CRUX is `RomCounting.condProb_fresh_eq` ("a fresh point hits a fixed target with probability
  exactly `1/|R|` — what the adversary has not queried, it does not know"). The workhorse built here,
  `condProb_fresh_mem_le`, unions that over the exceptional set: a fresh challenge lands in a `Finset E`
  with probability `≤ |E|/|R|` — a REAL bound, not a restated `≤ 1`. `condProb_fresh_family_le` unions
  over the `Q+1` transcript attempts (the `(Q+1)` factor) and the `Q` grinding attempts (`Q/2^pow`, the
  grinding accounting as a theorem for the first time). The product oracle range `F × Fin (2^pow)` carries
  the field challenge AND the PoW mask so the whole bad event is ONE `condProb` of a disjunction.

## Honest scope — what is proven vs. what is NAMED

PROVEN, over the `RomCounting` finite-oracle model, sorry-free and axiom-clean:
  - `condProb_fresh_mem_le`  (fresh challenge exceptional ≤ |E|/|R|)      — the crux, applied cleanly.
  - `condProb_fresh_family_le`  (union over Q+1 / Q attempts)              — the `(Q+1)` / `Q` factors.
  - `fs_epsilon_bound`  (the ε(Q, deg, pow) headline)                      — REAL: `(Q+1)·deg/|F| + Q/2^pow`.
  - `fs_epsilon_bound_babybear`  (grounded at the deployed field, ε via `exceptionalSet_card_le`).

NAMED carriers (the honest gap, exactly as `FRI-EXTRACTION-FLOOR-DESIGN.md` §4.5 anticipates —
`RomOracle` lacks the `QueryLog` erasure interface, so these are supplied as hypotheses, not yet derived
from `verifyAlgoO`):
  - **FRESHNESS** (`fsPt i ∉ S`, `powPt j ∉ S`): the derived-challenge/PoW squeeze points are outside the
    set `S` the oracle is already conditioned on. This is Stage 2's falsifier (§6): if the deployed FS
    transcript order let the adversary see a challenge before committing to what it must be non-exceptional
    for, freshness would fail — and that would be a real transcript bug, a WIN not a failure.
  - **The finite-oracle instantiation**: `condProb` is over a uniform `H : D → R` with `D`, `R` finite;
    tying `D`/`R` to the deployed `perm : List F → List F` needs the width-pinning + the query-log-to-fresh
    bridge (§4.5, a "modest addition" to `RomOracle`), and the counting of attempts to `permCallCount`.

Two of `FriLdtExtractV3`'s twelve conjuncts move from assumed toward proven here; the residual is the
freshness bridge, named — not the exceptional-set arithmetic (proven) nor the grinding term (proven).

## Discipline

Additive: modifies NO deployed spec/proof (`verifyAlgo`, `FriLdtExtractV3`, `deriveTranscript`,
`RomCounting`, `OodSoundnessGame` all untouched). `#assert_all_clean` over the keystones; no `sorry`,
no fresh `axiom`, no `native_decide`. Builds targeted (`lake build Dregg2.Circuit.FriVerifierFS`).
-/
import Dregg2.Crypto.RomCounting
import Dregg2.Circuit.OodSoundnessGame
import Dregg2.Circuit.AlgoStarkSoundTransferV3
import Dregg2.Circuit.FriLdtExtractDeployed
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Circuit.FriVerifierFS

open Dregg2.Crypto.RomCounting
open Dregg2.Circuit.OodQuotientConsistency (exceptionalSet exceptionalSet_card_le)

set_option autoImplicit false

/-! ## §1 — `ExtractBundleSansFS`: `FriLdtExtractV3`'s body MINUS the two FS conjuncts.

The ten conjuncts below are copied token-for-token from `FriLdtExtractV3`
(`AlgoStarkSoundTransferV3.lean:136–163`); the two removed are the FS non-exceptionality of Λ
(`Λ ∉ exceptionalSet (batchResidual (Rfam transferV3 t ζ qp))`) and of ζ per arith constraint
(`∀ c ∈ transferV3.constraints, isArith c → ζ ∉ exceptionalSet (…)`). Same binders, same order. -/

open Polynomial
open Dregg2.Circuit.FriVerifierBridge (ProofView)
open Dregg2.Circuit.FriVerifier
  (verifyAlgo BatchProofData WrapPublics FriParams RecursionVk FriChecks FriCore FieldArith
   TableOpening fullChecks)
open Dregg2.Circuit.CircuitSoundness
  (BatchPublicInputs BatchProof tracePublishedCommit)
open Dregg2.Circuit.DescriptorIR2 (VmTrace EffectVmDescriptor2 envAt VmConstraint2)
open Dregg2.Circuit.AirChecksSatisfied (isArith)
open Dregg2.Circuit.RotatedKernelRefinement (transferV3)
open Dregg2.Circuit.TraceColumnInterp (domainSize)
open Dregg2.Circuit.OodSoundnessGame (batchResidual)
open Dregg2.Circuit.OodCommitmentBinding (merkleRecomputeZ)
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.AlgoStarkSoundTransferV3 (Rfam FriLdtExtractV3)

/-- **`ExtractBundleSansFS`** — the TEN non-FS conjuncts of `FriLdtExtractV3`'s existential body,
verbatim. Identical signature to `FriLdtExtractV3`; the existential binders and the ten conjuncts are
token-for-token the same, with EXACTLY the two Fiat–Shamir non-exceptionality conjuncts deleted. This is
the bundle a later assembly (§5) will ASSUME, discharging the two removed conjuncts except-with-ε via
`fs_epsilon_bound`. -/
def ExtractBundleSansFS
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN (view pi π).1 (view pi π).2 = true →
    ∃ (t : VmTrace) (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
      (topen : TableOpening ℤ) (ood vCommitted root : ℤ) (idx : Nat) (siblings : List ℤ),
      -- FRI geometry / opening structure:
      t.rows.length ≤ domainSize ∧
      (view pi π).1.oodPoint = [ood] ∧
      topen ∈ (view pi π).1.tableOpenings ∧
      -- commitment recompute data (proof structure; feeds the `Poseidon2SpongeCR` binding):
      merkleRecomputeZ sponge idx vCommitted siblings = root ∧
      merkleRecomputeZ sponge idx topen.constraintEval siblings = root ∧
      -- THE transferV3 COLUMN-LAYOUT law (+ BabyBear→ℤ bridge):
      (batchResidual (Rfam transferV3 t ζ qp)).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear) ∧
      -- aux legs (verbatim the `algoStarkSound_of_bricks_transferV3` non-`MainAirAccept` premises):
      (∀ i < t.rows.length, ∀ c ∈ transferV3.constraints, ¬ isArith c →
          c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) ∧
      t.tf .memory = [] ∧ t.tf .mapOps = [] ∧
      tracePublishedCommit t = pi.toPublished

/-! **⚑ DELETED 2026-07-25 — `friLdtExtractV3_imp_sansFS`.** The adversarial-audit gate
`FriLdtExtractV3 → ExtractBundleSansFS`, and the LAST consumer in this module of a proved-empty
premise: at the deployed `cfg*` arguments `FriLdtExtractV3` forces `CircuitSoundness.verifyBatch` to
return `Verdict.reject` on EVERY key/public-input/proof triple
(`deleted_sansFS_gate_premise_was_empty` below), because it concludes `oodPoint = [ood]` — one base
felt — while acceptance forces four extension lanes. Its CONCLUSION was empty for the same reason
(`FriFsDecodedOodRepair.extractBundleSansFS_makes_verifyBatch_reject_everything`): the gate was an
empty ⟹ empty implication.

RELOCATED, not restated in place. The gate's value is the mechanical token-for-token check that
`ExtractBundleSansFS` IS `FriLdtExtractV3`'s body minus exactly the two FS conjuncts; performing that
check at the CORRECTED shape needs `FriLdtExtractDeployed.FriLdtExtractV3Cons` on the left and a
cons-shaped `ExtractBundleSansFS` on the right, and the latter
(`FriFsDecodedOodRepair.ExtractBundleSansFSCons`) lives in a module that IMPORTS this one. So the
corrected gate is `FriFsDecodedOodRepair.friLdtExtractV3Cons_imp_sansFSCons` — the SAME destructure /
reassemble / drop-exactly-`hLam`-and-`hnonexc` audit, at the shape the verifier actually forces.
Redefining `ExtractBundleSansFS` here instead would have destroyed the downstream vacuity receipts
that take it as their subject.

`ExtractBundleSansFS` the DEFINITION (above) is deliberately RETAINED, as the SUBJECT of those
receipts and of `PremiseInhabitability`'s E3 row, so the broken shape cannot reappear silently. It
has no consumers left outside the vacuity instruments and
`FriFsDecodedOodRepair.extractBundleSansFS_imp_cons`. -/

/-- **THE RECEIPT for the deleted gate.** Its premise — `AlgoStarkSoundTransferV3.FriLdtExtractV3` at
the deployed `cfg*` arguments — forces `CircuitSoundness.verifyBatch` to return `Verdict.reject` on
EVERY key/public-input/proof triple. The gate therefore said nothing about any run the deployed
verifier accepts, for the simple reason that there are none under that hypothesis. -/
theorem deleted_sansFS_gate_premise_was_empty
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (h : FriLdtExtractV3 sponge hash
      Dregg2.Circuit.CircuitSoundness.cfgPerm Dregg2.Circuit.CircuitSoundness.cfgRATE
      Dregg2.Circuit.CircuitSoundness.cfgToNat Dregg2.Circuit.CircuitSoundness.cfgParams
      Dregg2.Circuit.CircuitSoundness.cfgVk Dregg2.Circuit.CircuitSoundness.cfgCore
      Dregg2.Circuit.CircuitSoundness.cfgA Dregg2.Circuit.CircuitSoundness.cfgInitState
      Dregg2.Circuit.CircuitSoundness.cfgLogN Dregg2.Circuit.CircuitSoundness.cfgView)
    (vkey : Dregg2.Circuit.CircuitSoundness.VerifyKey)
    (pi : BatchPublicInputs) (π : BatchProof) :
    Dregg2.Circuit.CircuitSoundness.verifyBatch vkey pi π
      = Dregg2.Circuit.CircuitSoundness.Verdict.reject :=
  Dregg2.Circuit.FriLdtExtractDeployed.friLdtExtractV3_makes_verifyBatch_reject_everything
    sponge hash h vkey pi π

/-! ## §2 — The `condProb` union-bound layer (additive over `RomCounting`).

`RomCounting` proves `condProb_fresh_eq` (a fresh point hits a fixed target with probability exactly
`1/|R|`). Everything Stage 2 needs is that lemma unioned over (a) the exceptional set, (b) the attempts.
The two combinators — Boolean subadditivity and the finite `∃`-bound — are proved here. -/

section RomLayer

variable {D R : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

/-- **Boolean subadditivity of `condProb`.** `Pr[f ∨ g] ≤ Pr[f] + Pr[g]` — the winning oracles of
`f || g` inject into the union of the two winning sets, and `card_union_le` closes it. The union-bound
atom. -/
theorem condProb_or_le (C : Finset (D → R)) (f g : (D → R) → Bool) :
    condProb C (fun H => f H || g H) ≤ condProb C f + condProb C g := by
  have hcard : (C.filter (fun H => (f H || g H) = true)).card
      ≤ (C.filter (fun H => f H = true)).card + (C.filter (fun H => g H = true)).card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro H hH
    simp only [Finset.mem_filter, Finset.mem_union, Bool.or_eq_true] at hH ⊢
    rcases hH.2 with h | h
    · exact Or.inl ⟨hH.1, h⟩
    · exact Or.inr ⟨hH.1, h⟩
  unfold condProb
  rw [← add_div, div_eq_mul_inv, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast hcard

/-- **The finite `∃`-union bound.** `Pr[∃ i ∈ s, q i] ≤ ∑ i ∈ s, Pr[q i]` — union bound over a `Finset`
of events, by induction on `s` through `condProb_or_le`. -/
theorem condProb_exists_le (C : Finset (D → R)) {ι : Type} [DecidableEq ι] (s : Finset ι)
    (q : ι → (D → R) → Bool) :
    condProb C (fun H => decide (∃ i ∈ s, q i H = true)) ≤ ∑ i ∈ s, condProb C (q i) := by
  induction s using Finset.induction with
  | empty =>
      refine le_of_eq ?_
      rw [Finset.sum_empty]
      exact condProb_eq_zero (fun H _ => by simp)
  | insert a s ha ih =>
      have hcongr : ∀ H : D → R, decide (∃ i ∈ insert a s, q i H = true)
          = (q a H || decide (∃ i ∈ s, q i H = true)) := by
        intro H
        by_cases hex : ∃ i ∈ s, q i H = true
        · have hyes : ∃ i ∈ insert a s, q i H = true := by
            obtain ⟨i, hi, hq⟩ := hex; exact ⟨i, Finset.mem_insert_of_mem hi, hq⟩
          simp [hex]
        · by_cases hqa : q a H = true
          · have hyes : ∃ i ∈ insert a s, q i H = true := ⟨a, Finset.mem_insert_self a s, hqa⟩
            simp [hqa]
          · have hqaf : q a H = false := by simpa using hqa
            have hno : ¬ ∃ i ∈ insert a s, q i H = true := by
              rintro ⟨i, hi, hq⟩
              rcases Finset.mem_insert.1 hi with rfl | hmem
              · exact hqa hq
              · exact hex ⟨i, hmem, hq⟩
            simp [hex, hqaf]
      calc condProb C (fun H => decide (∃ i ∈ insert a s, q i H = true))
          = condProb C (fun H => q a H || decide (∃ i ∈ s, q i H = true)) :=
            condProb_congr (fun H _ => hcongr H)
        _ ≤ condProb C (q a) + condProb C (fun H => decide (∃ i ∈ s, q i H = true)) :=
            condProb_or_le _ _ _
        _ ≤ condProb C (q a) + ∑ i ∈ s, condProb C (q i) := by linarith [ih]
        _ = ∑ i ∈ insert a s, condProb C (q i) := by rw [Finset.sum_insert ha]

/-- **⚑ THE WORKHORSE — a fresh challenge lands in a `Finset E` with probability `≤ |E|/|R|`.** For a
fresh point `a ∉ S`, the union of `condProb_fresh_eq` (`= 1/|R|` per element) over the `|E|` elements of
`E` bounds the exceptional-hit probability by `|E|/|R|`. This is the ROM form of
`OodSoundnessGame.oodNonExc_winProb_le` — but over a CONDITIONED (fresh) coordinate, which is the point of
the random-oracle re-basing. A REAL bound: at `E = {z}` it is `condProb_fresh_eq`, tight at `1/|R|`. -/
theorem condProb_fresh_mem_le (S : Finset D) (σ : D → R) (a : D) (ha : a ∉ S) (E : Finset R) :
    condProb (cyl S σ) (fun H => decide (H a ∈ E)) ≤ (E.card : ℝ) / (Fintype.card R : ℝ) := by
  induction E using Finset.induction with
  | empty =>
      rw [Finset.card_empty, Nat.cast_zero, zero_div]
      exact le_of_eq (condProb_eq_zero (fun H _ => by simp))
  | insert z E hz ih =>
      have hcongr : ∀ H : D → R, decide (H a ∈ insert z E)
          = (decide (H a = z) || decide (H a ∈ E)) := by
        intro H
        by_cases h1 : H a = z
        · simp [Finset.mem_insert, h1]
        · by_cases h2 : H a ∈ E <;> simp [Finset.mem_insert, h1, h2]
      calc condProb (cyl S σ) (fun H => decide (H a ∈ insert z E))
          = condProb (cyl S σ) (fun H => decide (H a = z) || decide (H a ∈ E)) :=
            condProb_congr (fun H _ => hcongr H)
        _ ≤ condProb (cyl S σ) (fun H => decide (H a = z))
              + condProb (cyl S σ) (fun H => decide (H a ∈ E)) := condProb_or_le _ _ _
        _ = 1 / (Fintype.card R : ℝ) + condProb (cyl S σ) (fun H => decide (H a ∈ E)) := by
            rw [condProb_fresh_eq S σ a ha z]
        _ ≤ 1 / (Fintype.card R : ℝ) + (E.card : ℝ) / (Fintype.card R : ℝ) := by linarith [ih]
        _ = ((insert z E).card : ℝ) / (Fintype.card R : ℝ) := by
            rw [Finset.card_insert_of_notMem hz, ← add_div]; push_cast; ring

/-- **The exact family sum-bound.** For `m` FRESH attempt points `a i ∉ S`, each aiming at a `Finset E i`,
the probability that ANY attempt hits its target is `≤ (∑ i, |E i|)/|R|`. `condProb_exists_le` over
`Finset.univ : Finset (Fin m)`, each term by `condProb_fresh_mem_le`. -/
theorem condProb_fresh_family_sum_le (S : Finset D) (σ : D → R) {m : ℕ}
    (a : Fin m → D) (ha : ∀ i, a i ∉ S) (E : Fin m → Finset R) :
    condProb (cyl S σ) (fun H => decide (∃ i : Fin m, H (a i) ∈ E i))
      ≤ (∑ i : Fin m, ((E i).card : ℝ)) / (Fintype.card R : ℝ) := by
  have key := condProb_exists_le (cyl S σ) (Finset.univ : Finset (Fin m))
    (fun i H => decide (H (a i) ∈ E i))
  refine le_trans (le_trans (le_of_eq ?_) key) ?_
  · refine condProb_congr (fun H _ => ?_)
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨i, hi⟩; exact ⟨i, Finset.mem_univ i, by simpa using hi⟩
    · rintro ⟨i, _, hi⟩; exact ⟨i, by simpa using hi⟩
  · rw [Finset.sum_div]
    exact Finset.sum_le_sum (fun i _ => condProb_fresh_mem_le S σ (a i) (ha i) (E i))

/-- **⚑ THE `(Q+1)` / `Q` UNION — the family bound with a uniform degree cap.** For `m` fresh attempts,
each targeting a `Finset` of size `≤ b`, the any-hit probability is `≤ m·b/|R|`. This is where the
multiplicity of transcript attempts (`Q+1`) and grinding attempts (`Q`) enters the ε. -/
theorem condProb_fresh_family_le (S : Finset D) (σ : D → R) {m : ℕ}
    (a : Fin m → D) (ha : ∀ i, a i ∉ S) (E : Fin m → Finset R) (b : ℕ)
    (hb : ∀ i, (E i).card ≤ b) :
    condProb (cyl S σ) (fun H => decide (∃ i : Fin m, H (a i) ∈ E i))
      ≤ ((m * b : ℕ) : ℝ) / (Fintype.card R : ℝ) := by
  refine le_trans (condProb_fresh_family_sum_le S σ a ha E) ?_
  have hsum : (∑ i : Fin m, ((E i).card : ℝ)) ≤ ((m * b : ℕ) : ℝ) := by
    calc (∑ i : Fin m, ((E i).card : ℝ))
        ≤ ∑ _i : Fin m, (b : ℝ) := Finset.sum_le_sum (fun i _ => by exact_mod_cast hb i)
      _ = ((m * b : ℕ) : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hsum (by positivity)

end RomLayer

/-! ## §3 — The FS ε-theorem: `(Q+1)·deg/|F| + Q/2^pow`.

The product oracle range `F × Fin (2^pow)` carries the field challenge (`.1`) and the PoW mask (`.2`).
The bad event is: SOME transcript attempt's field challenge is exceptional, OR some grinding attempt's
mask is `0`. `condProb_or_le` splits the two families; `condProb_fresh_family_le` bounds each. -/

/-- **⚑ THE FS ε-THEOREM.** For a `Q`-attempt oracle adversary over the product oracle
`H : D → F × Fin (2^pow)`: each of the `Q+1` transcript attempts derives its field challenge at a FRESH
point `fsPt i ∉ S` and must avoid the exceptional set `Efs i` (size `≤ degBound`); each of the `Q`
grinding attempts squeezes its PoW mask at a FRESH point `powPt j ∉ S`. The probability that ANY
challenge is exceptional OR any grind hits `0` is

    ≤ (Q+1) · degBound / |F|  +  Q / 2^pow.

A REAL probability bound, `condProb_fresh_eq` at its heart, NOT a restated `≤ 1`. The freshness
hypotheses (`hfs`, `hpow`) are the honest NAMED carrier — the query-log-to-fresh bridge `RomOracle`
does not yet provide (see module header / `FRI-EXTRACTION-FLOOR-DESIGN.md` §4.5). -/
theorem fs_epsilon_bound
    {F : Type} [Fintype F] [DecidableEq F] [CommRing F] [IsDomain F]
    {D : Type} [Fintype D] [DecidableEq D]
    (pow : ℕ) (S : Finset D) (σ : D → F × Fin (2 ^ pow))
    (Q degBound : ℕ)
    (fsPt : Fin (Q + 1) → D) (hfs : ∀ i, fsPt i ∉ S)
    (Efs : Fin (Q + 1) → Finset F) (hEfs : ∀ i, (Efs i).card ≤ degBound)
    (powPt : Fin Q → D) (hpow : ∀ j, powPt j ∉ S) :
    condProb (cyl S σ)
        (fun H =>
          decide (∃ i : Fin (Q + 1), (H (fsPt i)).1 ∈ Efs i)
            || decide (∃ j : Fin Q, (H (powPt j)).2 = (0 : Fin (2 ^ pow))))
      ≤ ((Q + 1 : ℕ) * degBound : ℝ) / (Fintype.card F : ℝ) + (Q : ℝ) / ((2 : ℝ) ^ pow) := by
  haveI : Nonempty F := ⟨1⟩
  have hcF : 0 < Fintype.card F := Fintype.card_pos
  have hcFR : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast hcF.ne'
  have hpow2 : (0 : ℝ) < (2 : ℝ) ^ pow := by positivity
  have hcardR : (Fintype.card (F × Fin (2 ^ pow)) : ℝ)
      = (Fintype.card F : ℝ) * (2 : ℝ) ^ pow := by
    rw [Fintype.card_prod, Fintype.card_fin]; push_cast; ring
  have hcFpos : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hcF
  have hprodpos : (0 : ℝ) < (Fintype.card F : ℝ) * (2 : ℝ) ^ pow := mul_pos hcFpos hpow2
  refine le_trans (condProb_or_le _ _ _) (add_le_add ?_ ?_)
  · -- FS family: (H a).1 ∈ Efs i  ⟺  H a ∈ (Efs i) ×ˢ univ.
    have hcong : ∀ H : D → F × Fin (2 ^ pow),
        decide (∃ i : Fin (Q + 1), (H (fsPt i)).1 ∈ Efs i)
          = decide (∃ i : Fin (Q + 1),
              H (fsPt i) ∈ (Efs i) ×ˢ (Finset.univ : Finset (Fin (2 ^ pow)))) := by
      intro H
      apply decide_eq_decide.mpr
      constructor
      · rintro ⟨i, hi⟩; exact ⟨i, Finset.mem_product.2 ⟨hi, Finset.mem_univ _⟩⟩
      · rintro ⟨i, hi⟩; exact ⟨i, (Finset.mem_product.1 hi).1⟩
    rw [condProb_congr (fun H _ => hcong H)]
    have hfam := condProb_fresh_family_le S σ fsPt hfs
      (fun i => (Efs i) ×ˢ (Finset.univ : Finset (Fin (2 ^ pow)))) (degBound * 2 ^ pow)
      (fun i => by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
        exact Nat.mul_le_mul_right _ (hEfs i))
    refine le_trans hfam (le_of_eq ?_)
    rw [hcardR]
    push_cast
    rw [div_eq_div_iff hprodpos.ne' hcFpos.ne']
    ring
  · -- PoW family: (H a).2 = 0  ⟺  H a ∈ univ ×ˢ {0}.
    have hcong : ∀ H : D → F × Fin (2 ^ pow),
        decide (∃ j : Fin Q, (H (powPt j)).2 = (0 : Fin (2 ^ pow)))
          = decide (∃ j : Fin Q,
              H (powPt j) ∈ (Finset.univ : Finset F) ×ˢ ({0} : Finset (Fin (2 ^ pow)))) := by
      intro H
      apply decide_eq_decide.mpr
      constructor
      · rintro ⟨j, hj⟩
        exact ⟨j, Finset.mem_product.2 ⟨Finset.mem_univ _, by simp [hj]⟩⟩
      · rintro ⟨j, hj⟩
        exact ⟨j, by simpa using (Finset.mem_product.1 hj).2⟩
    rw [condProb_congr (fun H _ => hcong H)]
    have hfam := condProb_fresh_family_le S σ powPt hpow
      (fun _ => (Finset.univ : Finset F) ×ˢ ({0} : Finset (Fin (2 ^ pow)))) (Fintype.card F)
      (fun _ => by
        rw [Finset.card_product, Finset.card_univ, Finset.card_singleton]; simp)
    refine le_trans hfam (le_of_eq ?_)
    rw [hcardR]
    push_cast
    rw [div_eq_div_iff hprodpos.ne' hpow2.ne']
    ring

/-! ## §4 — Grounding at the deployed field (BabyBear) with the real `exceptionalSet`.

The abstract `Efs` become the deployed `exceptionalSet (Rp i)`, and `hEfs` becomes the Schwartz–Zippel
`exceptionalSet_card_le` — so `degBound` is a genuine polynomial-degree cap and `|F| = 2013265921`. -/

open Dregg2.Circuit.BabyBearFriField (babyBearP)

/-- **⚑ THE FS ε-THEOREM AT BABYBEAR** — grounded in the deployed exceptional sets. Each transcript
attempt's residual polynomial `Rp i` (degree `≤ degBound`) supplies its exceptional set via
`exceptionalSet_card_le`, so the FS-bad probability at the deployed field is

    ≤ (Q+1) · degBound / 2013265921  +  Q / 2^pow.

The `Λ` conjunct instantiates at `Rp i := batchResidual (Rfam transferV3 t ζ qp)` (degree `< #arithList`,
`batchResidual_exceptionalSet_card_lt`); the `ζ` conjunct at the per-arith-constraint residual
(`ood_hnonexc_escape_prob_le`'s polynomial). Both live under this one bound. -/
theorem fs_epsilon_bound_babybear
    {D : Type} [Fintype D] [DecidableEq D]
    (pow : ℕ) (S : Finset D) (σ : D → BabyBear × Fin (2 ^ pow))
    (Q degBound : ℕ)
    (fsPt : Fin (Q + 1) → D) (hfs : ∀ i, fsPt i ∉ S)
    (Rp : Fin (Q + 1) → Polynomial BabyBear) (hdeg : ∀ i, (Rp i).natDegree ≤ degBound)
    (powPt : Fin Q → D) (hpow : ∀ j, powPt j ∉ S) :
    condProb (cyl S σ)
        (fun H =>
          decide (∃ i : Fin (Q + 1), (H (fsPt i)).1 ∈ exceptionalSet (Rp i))
            || decide (∃ j : Fin Q, (H (powPt j)).2 = (0 : Fin (2 ^ pow))))
      ≤ ((Q + 1 : ℕ) * degBound : ℝ) / 2013265921 + (Q : ℝ) / ((2 : ℝ) ^ pow) := by
  haveI : NeZero babyBearP := ⟨(Nat.Prime.pos (Fact.out (p := Nat.Prime babyBearP))).ne'⟩
  have hcard : (Fintype.card BabyBear : ℝ) = 2013265921 := by
    exact_mod_cast Dregg2.Circuit.OodSoundnessGame.babybear_card
  have h := fs_epsilon_bound (F := BabyBear) pow S σ Q degBound fsPt hfs
    (fun i => exceptionalSet (Rp i))
    (fun i => le_trans (exceptionalSet_card_le (Rp i)) (hdeg i)) powPt hpow
  rwa [hcard] at h

/-! ## §5 — Teeth: the ε is a genuine probability, not a vacuous `≤ 1`. -/

/-- **(TOOTH — the workhorse bound is TIGHT.)** At a singleton target `E = {z}`,
`condProb_fresh_mem_le` yields exactly `1/|R|` (it IS `condProb_fresh_eq`): the FS bound genuinely bounds
a POSITIVE-probability event — a fresh challenge CAN be exceptional. Non-vacuity of the workhorse. -/
theorem condProb_fresh_mem_singleton_tight
    {D R : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]
    (S : Finset D) (σ : D → R) (a : D) (ha : a ∉ S) (z : R) :
    condProb (cyl S σ) (fun H => decide (H a ∈ ({z} : Finset R))) = 1 / (Fintype.card R : ℝ) := by
  have hcongr : ∀ H : D → R, decide (H a ∈ ({z} : Finset R)) = decide (H a = z) := by
    intro H; simp
  rw [condProb_congr (fun H _ => hcongr H), condProb_fresh_eq S σ a ha z]

/-- **(TOOTH — the ε is `< 1` at concrete params.)** At `Q = 1`, `degBound = 1`, `|F| = 7`, `pow = 3` the
bound is `2/7 + 1/8 < 1` — a real, meaningful probability, not the trivial `≤ 1`. Both terms are live and
positive. -/
theorem fs_epsilon_lt_one_example :
    ((1 + 1 : ℕ) * 1 : ℝ) / 7 + (1 : ℝ) / ((2 : ℝ) ^ 3) < 1 := by norm_num

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  deleted_sansFS_gate_premise_was_empty,
  condProb_or_le,
  condProb_exists_le,
  condProb_fresh_mem_le,
  condProb_fresh_family_sum_le,
  condProb_fresh_family_le,
  fs_epsilon_bound,
  fs_epsilon_bound_babybear,
  condProb_fresh_mem_singleton_tight,
  fs_epsilon_lt_one_example
]

end Dregg2.Circuit.FriVerifierFS
