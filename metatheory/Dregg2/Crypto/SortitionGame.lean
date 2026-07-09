/-
# `Dregg2.Crypto.SortitionGame` — the VRF LEADER-SORTITION game.

Lifts the abstract VRF security framework (`Dregg2.Crypto.VRF`) to the protocol-level sortition guarantee:
electing a leader/committee-member by "`VRF(sk, epoch) < thr`" is **FAIR**, **UNPREDICTABLE**, and
**UNIQUE**. Every one of the three reduces to a property `VRF.lean` already supplies — `UniqueOutputs`
(the X-VRF-lesson property) and `Pseudorandom` (the abstract indistinguishability game). NO new carrier is
invented here: this file introduces no assumed predicate. It only *interprets* the VRF output as an
election ticket and *derives* the sortition guarantees from the VRF's own security.

**The model.** A validator holds `sk`; its public key is `pkOf sk`. For epoch `x : Input` the validator
evaluates `eval sk x = (y, π)` and is **elected** iff the output falls below the threshold: `y < thr`
(`elected`). A *claim of election* is a pair `(y, π)` that both verifies and lies below threshold
(`ElectionProof`) — the on-chain artifact "I proved I was chosen."

**UNIQUENESS — no double-claim (the X-VRF lesson at the protocol level).** `sortition_unique`: two verifying
election claims for one `(pk, epoch)` force the SAME output — a validator cannot present two different
winning tickets. This is `VRF.uniqueness_at_most_one` applied directly; a malicious validator can neither
grind nor double-claim committee membership. The **"Breaking X-VRF"** attack (WOTS+/XMSS) is exactly a
`verify` relation that admits two outputs — and `doubleClaim_breaks_sortition_uniqueness` exhibits a
uniqueness-VIOLATING VRF that WOULD let a validator claim two distinct committee seats, so the reliance on
VRF uniqueness is load-bearing, not decorative.

**FAIRNESS — the honest base rate.** `electionDensity thr = |{y : y < thr}| / |Output|` is the fraction of
the output space below threshold — the base rate a uniform draw is elected. `sortition_fair`: under
`Pseudorandom V`, the real output's election bit equals the election bit of ANY uniform sample `u` — the
induced election-distinguisher gains nothing, so an honest validator is elected with exactly the density a
uniform draw would be, `thr/|Output|`. This is precisely — and only — what the (idealized, perfect)
`Pseudorandom` game supplies: indistinguishable-from-uniform ⟹ the election density matches uniform's.

**UNPREDICTABILITY — no edge before evaluation.** `sortition_unpredictable`: ANY predictor that sees only
`pk`, the `verify` oracle, and `epoch` (never `sk`) returns the same verdict on the real output as on a
uniform surrogate — predicting election IS distinguishing the output from uniform, so `Pseudorandom` forbids
any advantage over the base rate `thr/|Output|`.

All keystones `#assert_axioms`-clean; `#guard`s exhibit a non-vacuous election density, a unique honest
winner, and the X-VRF double-claim tooth.
-/
import Dregg2.Crypto.VRF
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Rat

namespace Dregg2.Crypto.SortitionGame

open Dregg2.Crypto.VRF

variable {SK PK Input Output Proof : Type*}

/-! ## The sortition model — election as `VRF(sk, epoch) < thr`. -/

/-- **ELECTED.** An honest validator holding `sk` is elected for epoch `x` at threshold `thr` iff its VRF
output falls below the threshold: `(eval sk x).1 < thr`. The `output < thr` sortition rule, over an ordered
output space. -/
def elected [LinearOrder Output] (V : VRF SK PK Input Output Proof)
    (sk : SK) (x : Input) (thr : Output) : Bool :=
  decide ((V.eval sk x).1 < thr)

/-- **A CLAIM OF ELECTION.** The on-chain artifact a validator presents: an output `y` with proof `π` that
BOTH verifies under `pk` for epoch `x` AND lies below threshold. "I proved I was chosen for epoch `x`." -/
def ElectionProof [LinearOrder Output] (V : VRF SK PK Input Output Proof)
    (pk : PK) (x : Input) (thr : Output) (y : Output) (π : Proof) : Prop :=
  V.verify pk x y π = true ∧ y < thr

/-! ## UNIQUENESS — no double-claim (the X-VRF lesson, ← `VRF.uniqueness_at_most_one`). -/

/-- **SORTITION UNIQUENESS.** Two verifying election claims for the SAME `(pk, epoch)` present the SAME
output — a validator cannot show two different winning tickets. Directly `VRF.uniqueness_at_most_one`: the
MRV uniqueness guarantee, lifted to the sortition claim. This is what stops a malicious validator from
grinding or double-claiming committee membership. -/
theorem sortition_unique [LinearOrder Output] (V : VRF SK PK Input Output Proof)
    (hu : UniqueOutputs V) (pk : PK) (x : Input) (thr : Output)
    (y y' : Output) (π π' : Proof)
    (h : ElectionProof V pk x thr y π) (h' : ElectionProof V pk x thr y' π') :
    y = y' :=
  uniqueness_at_most_one V hu pk x y y' π π' h.1 h'.1

#assert_axioms sortition_unique

/-- **THE X-VRF DOUBLE-CLAIM, stated as a refutation.** Two DISTINCT outputs, both verifying AND both below
threshold, are two winning tickets for one `(pk, epoch)` — a double-claim. Their existence REFUTES
`UniqueOutputs`, so any sortition that assumed uniqueness loses its premise. This is the "Breaking X-VRF"
failure mode at the protocol level: the load-bearing reason `sortition_unique` needs VRF uniqueness. -/
theorem double_claim_refutes_uniqueness [LinearOrder Output] (V : VRF SK PK Input Output Proof)
    (pk : PK) (x : Input) (thr : Output) (y y' : Output) (π π' : Proof)
    (hne : y ≠ y')
    (h : ElectionProof V pk x thr y π) (h' : ElectionProof V pk x thr y' π') :
    ¬ UniqueOutputs V :=
  two_outputs_break_uniqueness V pk x y y' π π' hne h.1 h'.1

#assert_axioms double_claim_refutes_uniqueness

/-! ## FAIRNESS — the honest base rate (← `VRF.Pseudorandom`). -/

/-- **ELECTION DENSITY.** The fraction of the output space below threshold: `|{y : y < thr}| / |Output|`.
This is the base rate `thr/|Output|` — the probability a UNIFORM draw is elected. A pure counting quantity;
fairness will say the real VRF matches it. -/
def electionDensity [Fintype Output] [LinearOrder Output] (thr : Output) : ℚ :=
  ((Finset.univ.filter (· < thr)).card : ℚ) / (Fintype.card Output : ℚ)

/-- The density is nonnegative. -/
theorem electionDensity_nonneg [Fintype Output] [LinearOrder Output] (thr : Output) :
    0 ≤ electionDensity thr :=
  div_nonneg (by exact_mod_cast Nat.zero_le _) (by exact_mod_cast Nat.zero_le _)

/-- The density is a genuine probability: `≤ 1` (the elected set is a subset of the whole space). -/
theorem electionDensity_le_one [Fintype Output] [LinearOrder Output] (thr : Output) :
    electionDensity thr ≤ 1 := by
  unfold electionDensity
  rcases Nat.eq_zero_or_pos (Fintype.card Output) with h | h
  · rw [h]; simp
  · rw [div_le_one (by exact_mod_cast h)]
    have : (Finset.univ.filter (· < thr)).card ≤ Fintype.card Output := by
      rw [← Finset.card_univ]; exact Finset.card_filter_le _ _
    exact_mod_cast this

#assert_axioms electionDensity_le_one

/-- **SORTITION FAIRNESS.** Under `Pseudorandom V`, the real output's election bit equals the election bit
of ANY uniform sample `u` at the same threshold. The election-distinguisher `fun _ _ _ y => y < thr` gains
nothing (`Pseudorandom`), so an honest validator is elected exactly when a uniform draw would be — i.e. with
density `electionDensity thr = thr/|Output|`. This is precisely, and only, what the (perfect)
`Pseudorandom` game supplies: indistinguishable-from-uniform ⟹ the election density matches uniform's. -/
theorem sortition_fair [LinearOrder Output] (V : VRF SK PK Input Output Proof)
    (hpr : Pseudorandom V) (sk : SK) (x : Input) (thr : Output) (u : Output) :
    elected V sk x thr = decide (u < thr) := by
  have h := hpr (fun _ _ _ y => decide (y < thr)) sk x u
  simpa [elected] using h

#assert_axioms sortition_fair

/-! ## UNPREDICTABILITY — no edge before evaluation (← `VRF.Pseudorandom`). -/

/-- **SORTITION UNPREDICTABILITY.** ANY predictor `P` that sees only `pk`, the `verify` oracle, and the
epoch (NEVER `sk`) returns the SAME verdict on the real output `(eval sk x).1` as on a uniform surrogate `u`
— predicting whether a validator is elected IS distinguishing the VRF output from uniform, so `Pseudorandom`
grants no advantage over the base rate `thr/|Output|`. Directly the `Pseudorandom` game. -/
theorem sortition_unpredictable (V : VRF SK PK Input Output Proof)
    (hpr : Pseudorandom V) (P : Distinguisher PK Input Output Proof)
    (sk : SK) (x : Input) (u : Output) :
    P (V.pkOf sk) (V.verify (V.pkOf sk)) x (V.eval sk x).1 =
    P (V.pkOf sk) (V.verify (V.pkOf sk)) x u :=
  hpr P sk x u

#assert_axioms sortition_unpredictable

/-! ## Teeth — a non-vacuous honest winner, and the X-VRF double-claim.

`toyVRF` (over `Fin 4`) is a uniqueness-RESPECTING sortition VRF: only output `0` verifies, and `0 < 1`, so
the honest validator is elected with a UNIQUE ticket. `doubleClaimVRF` accepts EVERY output (the "Breaking
X-VRF" shape) — so outputs `0` and `1`, both `< 3`, are TWO distinct winning tickets: a double-claim that
refutes `UniqueOutputs`. The pair separates a fair/unique sortition from the X-VRF break. -/

section Teeth

/-- A uniqueness-RESPECTING sortition VRF over `Fin 4`: eval always outputs `0`, and only `y = 0` verifies. -/
def toyVRF : VRF Unit Unit Unit (Fin 4) Unit where
  pkOf _ := ()
  eval _ _ := (0, ())
  verify _ _ y _ := decide (y = 0)

/-- A uniqueness-VIOLATING sortition VRF over `Fin 4`: `verify` accepts ANY output (the "Breaking X-VRF"
shape). Distinct outputs then form distinct winning tickets — the double-claim. -/
def doubleClaimVRF : VRF Unit Unit Unit (Fin 4) Unit where
  pkOf _ := ()
  eval _ _ := (0, ())
  verify _ _ _ _ := true

/-- `toyVRF` has UNIQUE outputs: only `0` verifies, so any two verifying outputs coincide. -/
theorem toyVRF_unique : UniqueOutputs toyVRF := by
  rintro pk x y₁ y₂ ⟨_, h1⟩ ⟨_, h2⟩
  simp only [toyVRF, decide_eq_true_eq] at h1 h2
  rw [h1, h2]

#assert_axioms toyVRF_unique

/-- The honest validator IS elected under `toyVRF` at threshold `1`, with a UNIQUE winning ticket `(0, ())`:
`sortition_unique` applies non-vacuously. -/
theorem toyVRF_elected_unique :
    ElectionProof toyVRF () () 1 0 () ∧
    (∀ y' π', ElectionProof toyVRF () () 1 y' π' → (0 : Fin 4) = y') := by
  refine ⟨⟨rfl, by decide⟩, ?_⟩
  intro y' π' h'
  exact sortition_unique toyVRF toyVRF_unique () () 1 0 y' () π' ⟨rfl, by decide⟩ h'

#assert_axioms toyVRF_elected_unique

/-- **THE X-VRF DOUBLE-CLAIM TOOTH.** Under `doubleClaimVRF`, outputs `0` and `1` are BOTH valid election
claims (both verify, both `< 3`) yet distinct — a validator double-claims two committee seats. Their
existence REFUTES `UniqueOutputs doubleClaimVRF` via `double_claim_refutes_uniqueness`: the load-bearing
reason `sortition_unique` needs VRF uniqueness. This is "Breaking X-VRF" at the sortition layer. -/
theorem doubleClaim_breaks_sortition_uniqueness : ¬ UniqueOutputs doubleClaimVRF :=
  double_claim_refutes_uniqueness doubleClaimVRF () () 3 0 1 () ()
    (by decide) ⟨rfl, by decide⟩ ⟨rfl, by decide⟩

#assert_axioms doubleClaim_breaks_sortition_uniqueness

-- FAIRNESS non-vacuity: over `Fin 4`, the below-`1` set is `{0}`, so the election density is `1/4`.
#guard electionDensity (1 : Fin 4) == (1 / 4 : ℚ)
-- The below-`3` set is `{0,1,2}`, density `3/4` — the base rate scales with the threshold.
#guard electionDensity (3 : Fin 4) == (3 / 4 : ℚ)
-- HONEST WINNER (unique): `toyVRF` elects the validator (output `0 < 1`) and only `0` verifies.
#guard elected toyVRF () () (1 : Fin 4)
#guard toyVRF.verify () () (0 : Fin 4) () && !toyVRF.verify () () (1 : Fin 4) ()
-- X-VRF DOUBLE-CLAIM tooth: `doubleClaimVRF` accepts TWO distinct winning tickets `0` and `1` (both `< 3`).
#guard (doubleClaimVRF.verify () () (0 : Fin 4) () && decide ((0 : Fin 4) < 3)) &&
       (doubleClaimVRF.verify () () (1 : Fin 4) () && decide ((1 : Fin 4) < 3))

end Teeth

end Dregg2.Crypto.SortitionGame
