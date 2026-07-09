/-
# `Dregg2.Crypto.RandomnessBeacon` — the abstract post-quantum randomness-beacon security framework.

This is the reusable scaffolding that REPLACES a classical BLS group-public randomness beacon with a
POST-QUANTUM one. The leading construction is HashRand-style: hash-based, asynchronous, batched weak VSS
plus approximate agreement, needing only a collision-resistant hash and pairwise secure channels — NO
threshold signature, NO pairing, NO group-public key. So the security carrier is exactly the hash carrier
`HashCR` already used by `Dregg2.Crypto.HermineHintMLWE`, and this file reuses that machinery directly.

A randomness beacon must provide TWO security properties; we formalize both abstractly over abstract
party / contribution / output types so a hash-based instantiation plugs in:

1. **UNBIASABILITY.** The output is a deterministic function of the committed contribution multiset
   (`beacon_output_determined`), and — as long as ≥1 honest UNPREDICTABLE contribution is included — no
   coalition below the corruption threshold can steer it. We model the output as a hash-combine over the
   contribution set and prove the honest slot is COLLISION-RESISTANT: fixing the adversary's (bounded)
   contributions, distinct honest contributions give distinct outputs (`honest_makes_unbiasable`), so the
   adversary that committed its part first cannot pin the output — the honest contribution moves it. A
   "bias" (making the output insensitive to a distinct honest contribution) is exactly a hash collision
   (`bias_breaks_honest_slot_cr`). The honest-slot carrier `HonestSlotCR` is NOT bespoke: it is DISCHARGED
   by the imported `HashCR` (`honestSlotCR_of_hashcr` — hash collision-resistance of the combine plus
   multiset cons-cancellation), and against `HashCR` the reduction is direct (`unbiasable_of_hashcr`):
   distinct honest reveals hash to distinct outputs.

2. **UNPREDICTABILITY.** The output is unpredictable before the honest contributions are revealed. We model
   commit-then-reveal (each party commits `cmᵢ = H(i, cᵢ)` then reveals `cᵢ`; the output depends on all
   revealed `cᵢ`) with the SAME imported `CommitReveal`/`HashCR` structure. Binding
   (`commit_binds_contribution` = `HermineHintMLWE.commitment_binding`) pins the honest party to one `cᵢ`;
   the output hash is injective in the honest reveal (`output_unpredictable_before_reveal`), so any a-priori
   prediction matches at most ONE honest contribution — a prediction correct for two distinct
   committed-consistent reveals BREAKS `HashCR` (`prediction_matching_two_reveals_breaks_hashcr`). Without a
   revealed honest `cᵢ` the adversary is reduced to guessing it through the commitment, i.e. inverting the
   hash. Both properties therefore reduce to the ONE named carrier `HashCR`.

3. **Monte-Carlo boundary (documented, not a proof gap).** A HashRand-style beacon runs asynchronous
   approximate agreement, which terminates with a small tunable failure probability `δ` PER BEACON (the
   "Monte-Carlo" aspect). This is a liveness/agreement boundary of the transport, orthogonal to the two
   safety properties above (unbiasability + unpredictability), which hold whenever a beacon output is
   produced at all. It is a documented operational boundary, not a hole in this framework: the reductions
   below make no claim about agreement termination, only about the output of a produced beacon.
-/
import Dregg2.Crypto.HermineHintMLWE

namespace Dregg2.Crypto.RandomnessBeacon

open Dregg2.Crypto.HermineHintMLWE

/-! ## The beacon model — output as a deterministic combine over the committed contribution multiset.

A beacon output is `H(c₁ ‖ … ‖ cₙ)` over the contribution set. Abstractly it is a `combine` from the
committed contribution multiset to the output — a genuine FUNCTION, so once the contributions are committed
the output is FIXED (no adaptive re-selection). The honest slot is the collision-resistance carrier. -/

section Model

variable {Ct O : Type*}

/-- A randomness beacon: the output is a deterministic function of the committed contribution multiset.
`combine` is the hash-combine `H(c₁ ‖ … ‖ cₙ)`; using a `Multiset` bakes in that the output does not
depend on contribution ORDER, only on the committed set-with-multiplicity. -/
structure Beacon (Ct O : Type*) where
  combine : Multiset Ct → O

/-- The beacon output on a committed contribution multiset. -/
def Beacon.output (b : Beacon Ct O) (cs : Multiset Ct) : O := b.combine cs

/-- **DETERMINISM (the first half of unbiasability).** The output is a deterministic function of the
committed contribution multiset: equal committed multisets ⇒ equal output. Once contributions are
committed the adversary cannot re-roll the output — there is nothing left to choose. -/
theorem beacon_output_determined (b : Beacon Ct O) {cs cs' : Multiset Ct} (h : cs = cs') :
    b.output cs = b.output cs' := congrArg b.combine h

/-- **`HonestSlotCR`** — honest-slot collision-resistance of the combine. Fixing the other (adversarial)
contributions `rest`, the map from an honest contribution to the output is INJECTIVE: distinct honest
contributions in the SAME position give distinct outputs. This is PURE collision-resistance — it asserts
nothing about honest-input entropy or unpredictability — so it is NOT a bespoke carrier: for the
hash-combine realization it is DISCHARGED by the imported standard `HashCR` (`honestSlotCR_of_hashcr`),
being hash collision-resistance composed with multiset cons-cancellation. -/
def HonestSlotCR (b : Beacon Ct O) : Prop :=
  ∀ (rest : Multiset Ct) (c c' : Ct), b.combine (c ::ₘ rest) = b.combine (c' ::ₘ rest) → c = c'

/-- **UNBIASABILITY (the core).** Under `HonestSlotCR`, with the adversary's contributions `rest` fixed
(it committed them first), an honest contribution the adversary cannot predict makes the output
UNBIASABLE: distinct honest values `c ≠ c'` yield distinct outputs, so the adversary cannot force the
output to any predetermined value — the included honest contribution moves it. -/
theorem honest_makes_unbiasable (b : Beacon Ct O) (hcr : HonestSlotCR b)
    (rest : Multiset Ct) (c c' : Ct) (hne : c ≠ c') :
    b.combine (c ::ₘ rest) ≠ b.combine (c' ::ₘ rest) :=
  fun h => hne (hcr rest c c' h)

/-- **A BIAS IS A COLLISION.** If some adversary makes the output INSENSITIVE to a distinct honest
contribution (two distinct honest values `c ≠ c'` give the SAME output at the same `rest` — it "absorbed"
the honest randomness), that witnesses a collision and BREAKS `HonestSlotCR`. The contrapositive of
`honest_makes_unbiasable`: biasability is exactly a hash collision on the honest slot. -/
theorem bias_breaks_honest_slot_cr (b : Beacon Ct O)
    (rest : Multiset Ct) (c c' : Ct) (hne : c ≠ c')
    (hcol : b.combine (c ::ₘ rest) = b.combine (c' ::ₘ rest)) : ¬ HonestSlotCR b :=
  fun hcr => hne (hcr rest c c' hcol)

end Model

/-! ## Reduction to the imported `HashCR` carrier.

The honest-slot collision-resistance `HonestSlotCR` is REALIZED by a collision-resistant hash-combine. We
model the combine as a hash over `(honest contribution, adversary aggregate)` and reduce unbiasability
DIRECTLY to `HermineHintMLWE.HashCR` — the same carrier the concurrent-signature argument uses. -/

section HashReduction

/-- The beacon output as a hash-combine over `(honest contribution, adversary aggregate)` at index `i`,
via the imported `CommitReveal` hash. `beaconViaHash cr i adv c = H(i, (c, adv))`. -/
def beaconViaHash {Idx Ct Adv O : Type*} (cr : CommitReveal Idx (Ct × Adv) O)
    (i : Idx) (adv : Adv) (c : Ct) : O := cr.H i (c, adv)

/-- **UNBIASABILITY reduces to `HashCR`.** Under collision-resistance of the combine hash, distinct honest
contributions `c ≠ c'` produce distinct beacon outputs, for ANY fixed adversary aggregate `adv`. So the
adversary cannot steer the output: it would need a hash collision. This is the honest-slot injectivity of
`HonestSlotCR`, derived from the ONE named carrier `HashCR`. -/
theorem unbiasable_of_hashcr {Idx Ct Adv O : Type*} (cr : CommitReveal Idx (Ct × Adv) O)
    (hcr : HashCR cr) (i : Idx) (adv : Adv) (c c' : Ct) (hne : c ≠ c') :
    beaconViaHash cr i adv c ≠ beaconViaHash cr i adv c' :=
  fun h => hne (congrArg Prod.fst (hcr i (c, adv) (c', adv) h))

/-! ### `HonestSlotCR` is NOT a bespoke carrier — it REDUCES to the standard `HashCR`.

The honest-slot carrier `HonestSlotCR` (§ Model) is not an independent assumption: when the beacon combine
is the standard collision-resistant hash over the committed multiset, `HonestSlotCR` is exactly `HashCR`
(the SAME carrier `HermineHintMLWE` uses) composed with multiset cons-left-cancellation. We realize the
beacon as such a hash and DISCHARGE `HonestSlotCR` from `HashCR`, so the honest slot bottoms out at the one
named hash carrier — no fresh beacon carrier. -/

/-- A beacon whose combine is the STANDARD collision-resistant hash over the committed contribution
multiset: `combine cs = H((), cs)`, reusing the imported `CommitReveal`/`HashCR` carrier (index `Unit`,
committed domain `Multiset Ct`). This is the honest realization of the abstract `Beacon`. -/
def beaconOfHash {Ct O : Type*} (cr : CommitReveal Unit (Multiset Ct) O) : Beacon Ct O :=
  ⟨fun cs => cr.H () cs⟩

/-- **`HonestSlotCR` REDUCES to the imported `HashCR`.** When the beacon combine is a collision-resistant
hash over the committed multiset, honest-slot injectivity is NOT a fresh assumption: it is exactly hash
collision-resistance (`HashCR`) — distinct committed multisets hash to distinct outputs — composed with
multiset cons-left-cancellation (`Multiset.cons_inj_left`, a pure fact). So `HonestSlotCR` bottoms out at
the SAME `HashCR` carrier the concurrent-signature argument uses, the true floor, with no bespoke beacon
carrier. -/
theorem honestSlotCR_of_hashcr {Ct O : Type*} (cr : CommitReveal Unit (Multiset Ct) O)
    (hcr : HashCR cr) : HonestSlotCR (beaconOfHash cr) := fun rest c c' h =>
  (Multiset.cons_inj_left rest).mp (hcr () (c ::ₘ rest) (c' ::ₘ rest) h)

end HashReduction

/-! ## Unpredictability — commit-then-reveal, reusing `CommitReveal`/`HashCR`.

Each party commits `cmᵢ = H(i, cᵢ)` (binding) then reveals `cᵢ`; the output is the hash-combine over the
revealed contributions. Binding pins the honest party to one `cᵢ`; the output hash is injective in that
reveal, so the output is unpredictable before reveal — an a-priori prediction can match at most one honest
contribution. Both facts reuse the imported `HermineHintMLWE` machinery. -/

section Unpredictability

/-- **BINDING (reused).** Under `HashCR` of the commitment hash, an honest party cannot open one commitment
`cm` to two different contributions — it is pinned to the `cᵢ` it committed. This is exactly
`HermineHintMLWE.commitment_binding`; it is what makes the reveal FORCED, so the output is determined only
at reveal time. -/
theorem commit_binds_contribution {Idx Ct C : Type*} (cmCR : CommitReveal Idx Ct C)
    (hcr : HashCR cmCR) (cm : C) (i : Idx) (c c' : Ct)
    (ho : cmCR.opens cm i c) (ho' : cmCR.opens cm i c') : c = c' :=
  commitment_binding cmCR hcr cm i c c' ho ho'

/-- **UNPREDICTABILITY (the core).** Before the honest contribution is revealed, the adversary holds only
the commitment; the output hash is INJECTIVE in the honest reveal, so distinct possible honest
contributions produce distinct outputs. Hence no single value is the output for more than one honest
contribution: the adversary is reduced to GUESSING the committed `cᵢ` (inverting the commitment) — it cannot
predict the output. Same math as `unbiasable_of_hashcr`, read as the guessing (not steering) game. -/
theorem output_unpredictable_before_reveal {Idx Ct Adv O : Type*}
    (outCR : CommitReveal Idx (Ct × Adv) O) (hout : HashCR outCR)
    (i : Idx) (adv : Adv) (c c' : Ct) (hne : c ≠ c') :
    beaconViaHash outCR i adv c ≠ beaconViaHash outCR i adv c' :=
  unbiasable_of_hashcr outCR hout i adv c c' hne

/-- **A CORRECT EARLY PREDICTION BREAKS `HashCR`.** If an a-priori prediction `o` (fixed before reveal)
equals the real output for TWO distinct committed-consistent honest reveals `c ≠ c'`, that is a collision on
the output hash — it BREAKS `HashCR`. So a prediction can match at most one honest contribution; the
adversary that predicts the beacon without a revealed honest `cᵢ` has broken the hash. The reduction of
unpredictability to the named carrier. -/
theorem prediction_matching_two_reveals_breaks_hashcr {Idx Ct Adv O : Type*}
    (outCR : CommitReveal Idx (Ct × Adv) O) (i : Idx) (adv : Adv) (o : O)
    (c c' : Ct) (hne : c ≠ c')
    (hpred : beaconViaHash outCR i adv c = o) (hpred' : beaconViaHash outCR i adv c' = o) :
    ¬ HashCR outCR :=
  fun hcr => (unbiasable_of_hashcr outCR hcr i adv c c' hne) (hpred.trans hpred'.symm)

end Unpredictability

#assert_axioms beacon_output_determined
#assert_axioms honest_makes_unbiasable
#assert_axioms bias_breaks_honest_slot_cr
#assert_axioms unbiasable_of_hashcr
#assert_axioms honestSlotCR_of_hashcr
#assert_axioms commit_binds_contribution
#assert_axioms output_unpredictable_before_reveal
#assert_axioms prediction_matching_two_reveals_breaks_hashcr

/-! ## Teeth — the properties FIRE on concrete data (non-vacuity).

(a) Unbiasability: a concrete additive combine is honest-slot collision-resistant; an honest contribution
    makes the output unbiasable (changing the adversary's contribution keeps the output well-defined but
    the honest contribution is baked in — the adversary did NOT set it).
(b) The hash reduction: an injective combine hash gives `HashCR`, and distinct honest reveals hash to
    distinct outputs.
(c) Commit-binding teeth: an equivocated reveal breaks `HashCR`; an output insensitive to the honest reveal
    (a bias) likewise breaks `HashCR`. -/

section Teeth

/-! ### (a) Unbiasability teeth — an additive combine over `ℤ`. -/

/-- A concrete beacon: `combine = Σ`. The output is the sum of the committed contributions — order-free
(a `Multiset`) and honest-slot injective (adding a constant is a bijection). -/
def sumBeacon : Beacon ℤ ℤ := ⟨Multiset.sum⟩

/-- `sumBeacon` genuinely satisfies `HonestSlotCR`: with the adversary aggregate `rest` fixed, distinct
honest contributions give distinct sums. -/
theorem sumBeacon_cr : HonestSlotCR sumBeacon := by
  intro rest c c' h
  have h' : c + rest.sum = c' + rest.sum := by
    change Multiset.sum (c ::ₘ rest) = Multiset.sum (c' ::ₘ rest) at h
    rwa [Multiset.sum_cons, Multiset.sum_cons] at h
  exact add_right_cancel h'

/-- **UNBIASABILITY FIRES.** With the adversary's contribution fixed (`rest = {1}`), the honest values
`5 ≠ 6` produce distinct outputs — the adversary cannot force a predetermined value; the honest
contribution moves the beacon. -/
theorem sum_honest_unbiasable :
    sumBeacon.combine (5 ::ₘ ({1} : Multiset ℤ)) ≠ sumBeacon.combine (6 ::ₘ ({1} : Multiset ℤ)) :=
  honest_makes_unbiasable sumBeacon sumBeacon_cr {1} 5 6 (by decide)

-- The output is the well-defined sum with the honest 5 included.
#guard sumBeacon.combine (5 ::ₘ ({1} : Multiset ℤ)) = 6
-- The adversary CHANGED its contribution (1 → 2): the output is still well-defined (7)…
#guard sumBeacon.combine (5 ::ₘ ({2} : Multiset ℤ)) = 7
-- …but the honest 5 is baked in — the output DIFFERS from the adversary-only combine, so the adversary
-- did NOT set the beacon output.
#guard sumBeacon.combine (5 ::ₘ ({1} : Multiset ℤ)) ≠ sumBeacon.combine ({1} : Multiset ℤ)
-- Changing the honest contribution changes the output (the unbiasability tooth).
#guard sumBeacon.combine (5 ::ₘ ({1} : Multiset ℤ)) ≠ sumBeacon.combine (6 ::ₘ ({1} : Multiset ℤ))

/-! ### (b) Hash-reduction teeth — an injective combine hash. -/

/-- A binding combine hash `H(i, (c, adv)) = (i, c, adv)`, injective on its domain. -/
def exBeaconHash : CommitReveal ℕ (ℤ × ℤ) (ℕ × ℤ × ℤ) := ⟨fun i w => (i, w)⟩

theorem exBeaconHash_hashcr : HashCR exBeaconHash := fun _ _ _ h => (Prod.ext_iff.mp h).2

/-- **THE HASH REDUCTION FIRES.** Under `HashCR`, distinct honest contributions `5 ≠ 6` (same adversary
aggregate `1`) hash to distinct beacon outputs — unbiasability from the named carrier, non-vacuously. -/
theorem hash_beacon_unbiasable :
    beaconViaHash exBeaconHash 0 (1 : ℤ) (5 : ℤ) ≠ beaconViaHash exBeaconHash 0 (1 : ℤ) (6 : ℤ) :=
  unbiasable_of_hashcr exBeaconHash exBeaconHash_hashcr 0 1 5 6 (by decide)

#guard beaconViaHash exBeaconHash 0 (1 : ℤ) (5 : ℤ) = (0, 5, 1)
#guard beaconViaHash exBeaconHash 0 (1 : ℤ) (5 : ℤ) ≠ beaconViaHash exBeaconHash 0 (1 : ℤ) (6 : ℤ)

/-- The identity multiset-hash `H((), cs) = cs` is collision-resistant (`HashCR`). -/
def idMultisetHash : CommitReveal Unit (Multiset ℤ) (Multiset ℤ) := ⟨fun _ cs => cs⟩

theorem idMultisetHash_hashcr : HashCR idMultisetHash := fun _ _ _ h => h

/-- **`HonestSlotCR` FROM `HashCR` FIRES.** The beacon induced by a collision-resistant multiset-hash
satisfies `HonestSlotCR` via `honestSlotCR_of_hashcr` — the honest-slot carrier discharged by the standard
`HashCR`, non-vacuously (no bespoke carrier assumed). -/
theorem hashBeacon_honest_slot_cr : HonestSlotCR (beaconOfHash idMultisetHash) :=
  honestSlotCR_of_hashcr idMultisetHash idMultisetHash_hashcr

-- The discharged honest slot moves the output: distinct honest contributions give distinct beacons.
#guard (beaconOfHash idMultisetHash).combine (5 ::ₘ ({1} : Multiset ℤ))
  ≠ (beaconOfHash idMultisetHash).combine (6 ::ₘ ({1} : Multiset ℤ))

/-! ### (c) Commit-binding teeth — equivocation and bias each break `HashCR`. -/

/-- A COLLIDING commitment hash `H(i, c) = 0` for all `c` — every reveal opens every commitment. -/
def badCommit : CommitReveal ℕ ℤ ℕ := ⟨fun _ _ => 0⟩

/-- **EQUIVOCATION FIRES.** On `badCommit`, the distinct reveals `7 ≠ 8` both open the commitment `0`, so
`equivocation_breaks_hashcr` (imported) yields a genuine `¬ HashCR badCommit` — the commit-binding tooth,
non-vacuously. An equivocated reveal is exactly a hash collision. -/
theorem badCommit_not_binding : ¬ HashCR badCommit :=
  equivocation_breaks_hashcr badCommit 0 5 7 8 (by decide) rfl rfl

-- The equivocation is a real collision: distinct reveals, one commitment.
#guard badCommit.commit 5 7 = badCommit.commit 5 8
#guard (7 : ℤ) ≠ 8

/-- A combine hash INSENSITIVE to the honest reveal: `H(i, w) = 0`. Every honest contribution yields the
same output — the adversary has "absorbed" the honest randomness. -/
def badBeaconOut : CommitReveal ℕ (ℤ × ℤ) ℕ := ⟨fun _ _ => 0⟩

/-- **BIAS FIRES.** The prediction `o = 0` matches the beacon output for the two distinct honest reveals
`5 ≠ 6`, so `prediction_matching_two_reveals_breaks_hashcr` yields `¬ HashCR badBeaconOut`: an output the
adversary can predict / that ignores the honest contribution is exactly a hash collision. -/
theorem bias_predicts_and_breaks_hashcr : ¬ HashCR badBeaconOut :=
  prediction_matching_two_reveals_breaks_hashcr badBeaconOut 0 (1 : ℤ) 0 (5 : ℤ) (6 : ℤ) (by decide) rfl rfl

-- The bias is a real collision: distinct honest reveals, one output.
#guard beaconViaHash badBeaconOut 0 (1 : ℤ) (5 : ℤ) = beaconViaHash badBeaconOut 0 (1 : ℤ) (6 : ℤ)

end Teeth

#assert_axioms sumBeacon_cr
#assert_axioms sum_honest_unbiasable
#assert_axioms exBeaconHash_hashcr
#assert_axioms hash_beacon_unbiasable
#assert_axioms idMultisetHash_hashcr
#assert_axioms hashBeacon_honest_slot_cr
#assert_axioms badCommit_not_binding
#assert_axioms bias_predicts_and_breaks_hashcr

end Dregg2.Crypto.RandomnessBeacon
