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
   (`bias_breaks_honest_slot_cr`). ⚑ The old `HashCR`-conditioned exports (`honestSlotCR_of_hashcr`,
   `unbiasable_of_hashcr`) are DELETED (2026-07-24) — `HashCR` is refuted at every compressing combine
   (`hashCR_false_of_compressing`); the discharged successors are
   `RandomnessBeaconRegrounded.beacon_binding_rom` / `hashrand_output_binding_rom` (keyed-ROM floor,
   PROVED), and the deterministic residue is `prediction_matching_two_reveals_breaks_hashcr`.

2. **UNPREDICTABILITY.** The output is unpredictable before the honest contributions are revealed. We model
   commit-then-reveal (each party commits `cmᵢ = H(i, cᵢ)` then reveals `cᵢ`; the output depends on all
   revealed `cᵢ`) with the SAME imported `CommitReveal` structure. ⚑ The old `HashCR`-conditioned
   binding exports (`commit_binds_contribution`, `output_unpredictable_before_reveal`) are DELETED
   (2026-07-24, refuted floor); the discharged successors are
   `RandomnessBeaconRegrounded.hashrand_commit_binding_rom` and `beacon_binding_rom` (keyed-ROM floor,
   PROVED). A prediction correct for two distinct committed-consistent reveals still BREAKS `HashCR`
   (`prediction_matching_two_reveals_breaks_hashcr` — the retained extractor witness). Both properties
   now price on the PROVED keyed-ROM floor instead of the refuted injectivity carrier.

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
being hash collision-resistance composed with multiset cons-cancellation.

⚠ **BROKEN AS NAMED — FALSE for a compressing combine, so `honest_makes_unbiasable` below is VACUOUSLY
TRUE at deployed parameters** (`Crypto.BeaconSlotRegrounded.honestSlotCR_false_of_compressing`;
`docs/deos/VACUITY-SWEEP.md` FINDING 2). ⚑ Its falsity has a DIFFERENT SHAPE from its siblings and the
replacement file proves and explains why: with `rest` fixed the slot is `Ct → O`, a map between two
FIXED-WIDTH types, so there is no infinite domain for the counting core — the honest refutation is
pigeonhole on cardinalities under `|O| < |Ct|`, which IS the definition of a hash-combine.

⚠ **AND THE "NOT BESPOKE — IT BOTTOMS OUT AT THE STANDARD `HashCR`" DEFENCE ABOVE DOES NOT RESCUE IT.**
`honestSlotCR_of_hashcr` is true and is not a defence: `HashCR` is ONE OF THE FOUR FLOORS
`HashFloorHonesty` ALREADY PROVED FALSE (its TOOTH 3), and
`BeaconSlotRegrounded.honestSlotCR_discharge_hypothesis_is_false_of_finite_out` proves it at the exact
`cr` this beacon is built from. So the discharge transports NOTHING at deployed parameters — false
hypothesis, false conclusion, both vacuous. Bottoming out at a standard floor is grounding only if the
standard floor is SATISFIABLE.

**The honest replacement is `Crypto.BeaconSlotRegrounded`** — `honest_makes_unbiasable`'s
advantage-bounded sibling, from a REAL bias game via a data-dependent extractor running through
`Multiset.cons_inj_left` (the same pure cancellation `honestSlotCR_of_hashcr` uses, now CARRYING the
reduction instead of a false hypothesis), with an explicit undischarged `Eff`. This def is KEPT so the
record and the teeth — including `bias_breaks_honest_slot_cr`, which the replacement fires THROUGH —
keep compiling. -/
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

/-! ⚑ **The old export `unbiasable_of_hashcr` (`HashCR → distinct outputs`) is DELETED** — its
`hcr : HashCR` hypothesis is pure INJECTIVITY of the combine hash, PROVED FALSE for every compressing
combine by `HashFloorHonesty.hashCR_false_of_compressing` (the deployed combine maps long framed
pre-images to a fixed-width digest — compressing). It steered nothing at deployed parameters. Its
content survives as `prediction_matching_two_reveals_breaks_hashcr` below (the `¬ HashCR`-conclusion
extractor witness); the DISCHARGED successor is `RandomnessBeaconRegrounded.beacon_binding_rom` — the
beacon-steering OPENING game at the SAMPLED keyed oracle, every query-bounded steering adversary's
advantage NEGLIGIBLE on the PROVED floor `KeyedRomFloor.keyedRom_hard` (the birthday bound). -/

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

/-! ⚑ **The old export `honestSlotCR_of_hashcr` (`HashCR → HonestSlotCR`) is DELETED** — a
FALSE→FALSE bridge: BOTH ends are refuted floors at deployed parameters
(`hashCR_false_of_compressing` for the hypothesis;
`BeaconSlotRegrounded.honestSlotCR_false_of_compressing` for the conclusion), so it transported
nothing. `BeaconSlotRegrounded.honestSlotCR_of_injective` keeps the same bridge content restated over
the deployment for its vacuity-dissection; the mathematical content (`Multiset.cons_inj_left`
composed with the hash) survives, DISCHARGED, in
`RandomnessBeaconRegrounded.hashrand_output_binding_rom` — the honest-slot binding at the sampled
oracle, floor PROVED. -/

end HashReduction

/-! ## Unpredictability — commit-then-reveal, reusing `CommitReveal`/`HashCR`.

Each party commits `cmᵢ = H(i, cᵢ)` (binding) then reveals `cᵢ`; the output is the hash-combine over the
revealed contributions. Binding pins the honest party to one `cᵢ`; the output hash is injective in that
reveal, so the output is unpredictable before reveal — an a-priori prediction can match at most one honest
contribution. Both facts reuse the imported `HermineHintMLWE` machinery. -/

section Unpredictability

/-! ⚑ **The old exports `commit_binds_contribution` (`HashCR → c = c'`) and
`output_unpredictable_before_reveal` (`HashCR → distinct outputs`) are DELETED** — the same refuted
injectivity floor. The commitment-pinning content survives, DISCHARGED, as
`RandomnessBeaconRegrounded.hashrand_commit_binding_rom` (the commit-opening game at the sampled
oracle — an honest party is pinned to ONE contribution except with negligible probability, floor
PROVED) and `HermineRomBinding.commitReveal_binds_rom` (the generic commit-reveal form); the
unpredictability content as `beacon_binding_rom` (a published prediction opened by two distinct
reveals IS a beacon-steering win). The deterministic residue is
`prediction_matching_two_reveals_breaks_hashcr` below — the extractor witness. -/

/-- **A CORRECT EARLY PREDICTION BREAKS `HashCR`.** If an a-priori prediction `o` (fixed before reveal)
equals the real output for TWO distinct committed-consistent honest reveals `c ≠ c'`, that is a collision on
the output hash — it BREAKS `HashCR`. So a prediction can match at most one honest contribution; the
adversary that predicts the beacon without a revealed honest `cᵢ` has broken the hash. Retained ONLY
as the reduction's deterministic extractor witness (a `¬ HashCR` CONCLUSION), never re-exported. -/
theorem prediction_matching_two_reveals_breaks_hashcr {Idx Ct Adv O : Type*}
    (outCR : CommitReveal Idx (Ct × Adv) O) (i : Idx) (adv : Adv) (o : O)
    (c c' : Ct) (hne : c ≠ c')
    (hpred : beaconViaHash outCR i adv c = o) (hpred' : beaconViaHash outCR i adv c' = o) :
    ¬ HashCR outCR :=
  fun hcr => hne (congrArg Prod.fst (hcr i (c, adv) (c', adv) (hpred.trans hpred'.symm)))

end Unpredictability

#assert_axioms beacon_output_determined
#assert_axioms honest_makes_unbiasable
#assert_axioms bias_breaks_honest_slot_cr
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

/-- **THE HASH REDUCTION FIRES.** Distinct honest contributions `5 ≠ 6` (same adversary aggregate `1`)
hash to distinct beacon outputs on the injective instance. (Formerly routed through the deleted
`unbiasable_of_hashcr`; on the concrete instance the distinctness is decidable.) -/
theorem hash_beacon_unbiasable :
    beaconViaHash exBeaconHash 0 (1 : ℤ) (5 : ℤ) ≠ beaconViaHash exBeaconHash 0 (1 : ℤ) (6 : ℤ) := by
  decide

#guard beaconViaHash exBeaconHash 0 (1 : ℤ) (5 : ℤ) = (0, 5, 1)
#guard beaconViaHash exBeaconHash 0 (1 : ℤ) (5 : ℤ) ≠ beaconViaHash exBeaconHash 0 (1 : ℤ) (6 : ℤ)

/-- The identity multiset-hash `H((), cs) = cs` is collision-resistant (`HashCR`). -/
def idMultisetHash : CommitReveal Unit (Multiset ℤ) (Multiset ℤ) := ⟨fun _ cs => cs⟩

theorem idMultisetHash_hashcr : HashCR idMultisetHash := fun _ _ _ h => h

/-- **`HonestSlotCR` FIRES on the identity multiset-hash.** The beacon induced by the injective
multiset-hash satisfies `HonestSlotCR` directly (`Multiset.cons_inj_left` on the identity hash) —
non-vacuously, no bespoke carrier assumed. (Formerly routed through the deleted
`honestSlotCR_of_hashcr`.) -/
theorem hashBeacon_honest_slot_cr : HonestSlotCR (beaconOfHash idMultisetHash) :=
  fun rest c c' h => (Multiset.cons_inj_left rest).mp h

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
