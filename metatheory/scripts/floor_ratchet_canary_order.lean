/-
# floor_ratchet_canary_order.lean — THE B4 EVASION CLASS: binder ORDER.

`#floor_ratchet` exempts ANTI-FLOOR content, and it must: the campaign wants refutations written,
so writing one can never be a build error. The question is what "a refutation" means to a machine.

Until 2026-07-25 the answer keyed on POSITION. A declaration concluding `False` was exempt when its
refuted floor was the INNERMOST binder, on the reasoning that `Γ → F → False` IS `Γ → ¬ F` by
definition. That reasoning is correct and the rule was still a hole, because **binder order is a
spelling the author controls**. The identical contrapositive soundness claim — "assume the floor,
assume the system is broken, derive absurdity" — was GATED with its floor hypothesis written first
and EXEMPT with it written last. Nothing else changed. The gate's own error message coached the
swap in so many words: *"move the floor binder LAST … it costs no proof work."*

Two theorems were sitting on it, and they are not toys:

    Dregg2.Crypto.HermineMSIS.no_forgery_under_msis
    Dregg2.Crypto.HermineSelfTargetMSIS.no_forgery_under_msis_selftarget

Both read as "the deployed threshold signature cannot be forged". Both rest entirely on
`Lattice.MSISHard`, which this tree REFUTES (`CryptoFloorTeeth.not_msisHard_of_short_ball`: at a
compressing `A` the ball of short vectors outnumbers the codomain, so a short nonzero kernel vector
exists by pigeonhole). Under the old rule they were not grandfathered — they were EXEMPT, filed by
the instrument alongside `poseidon2SpongeCR_false_babyBear` as anti-floor content. A theorem that
reads as assurance and says nothing is worse than no theorem, and this one was invisible.

The rule now consults NO binder position: a refuted floor in ANY hypothesis disqualifies, and
exemption means *concludes* `¬ Floor …` while *assuming* no floor. This file is the four evasions
that closes, declared for real and pointed at the gate.

    cd metatheory && lake env lean scripts/floor_ratchet_canary_order.lean

**EXPECTED: EXIT=1**, with `⚑ FLOOR-RATCHET: … NEW declaration(s) …` naming every theorem below.
A ZERO exit means the gate has gone back to keying on spelling, and every "cannot be forged" /
"no fork" / "rejects" theorem in the tree can be laundered out of the census by moving one binder.

⚑ The cost of the tightening is pinned in the OTHER direction by `FloorRatchetSpecimens`
(`specRefutation`, `specRefutationManyHyp` must stay EXEMPT) and by the tree itself: the three
genuine refutations that had been written uncurried were restated as `¬ Floor …` in the same
commit — same proof term, no proof work — rather than grandfathered.
-/
import Dregg2

open Dregg2.Circuit.Poseidon2Binding
open Dregg2.Circuit.StateCommit (compressNInjective)

/-- **B4 — THE PROBE.** The exact declaration that walked through the old rule. Read the name: it
claims the deployed consensus is safe. Read the type: it assumes a hash is injective — which this
tree proves FALSE for every BabyBear-bounded sponge — and derives absurdity from a collision. It is
`no_forgery_under_msis` with the crypto removed. Under the old rule: EXEMPT, because `hCR` is last.
Swap the two hypotheses and the old rule gated it. -/
theorem adv_reorder_consensus_safe_under_floor {sponge : List ℤ → ℤ}
    (hLive : sponge [1] = sponge [2]) (hCR : Poseidon2SpongeCR sponge) : False :=
  absurd (hCR [1] [2] hLive) (by simp)

/-- **B4 × B1** — the same evasion aimed at the NEGATION branch: floor innermost, conclusion a
`¬ …` of a DIFFERENT refuted floor. Both routes reordered at once. Assuming one refuted floor to
refute another is not anti-floor content; it is vacuity with a negation stapled on. -/
theorem adv_reorder_neg_other_floor {sponge : List ℤ → ℤ} (h : List ℤ → ℤ)
    (hLive : sponge [1] = sponge [2]) (hCR : Poseidon2SpongeCR sponge) :
    ¬ compressNInjective h :=
  absurd (hCR [1] [2] hLive) (by simp)

/-- A `Prop`-valued ALIAS for a refuted floor. Not a violation itself — it is here so the theorem
below reaches the floor through a name the gate has never heard of, which is the cheapest way to
imagine escaping a constant-keyed scan. It does not escape: the joint `prop-body` fixpoint sees an
alias for a floor as floor-carrying content, so `content` holds it before `antiFloor` is ever
called. (The gate will name this `abbrev` too, in class `prop-body`.) -/
abbrev spongeFloorAlias (f : List ℤ → ℤ) : Prop := Poseidon2SpongeCR f

/-- **B4 through an ALIAS.** Floor innermost AND indirected through `spongeFloorAlias`, so no
`Poseidon2SpongeCR` constant appears in this type at all. -/
theorem adv_reorder_via_alias {sponge : List ℤ → ℤ}
    (hLive : sponge [1] = sponge [2]) (hCR : spongeFloorAlias sponge) : False :=
  absurd (hCR [1] [2] hLive) (by simp)

/-- **B4 through a `let` IN THE TYPE.** Floor innermost and bound by a `let` rather than named
directly — the last spelling trick available on the hypothesis side. `foldConsts` walks the whole
binder domain, `let` bodies included. -/
theorem adv_reorder_via_let {sponge : List ℤ → ℤ}
    (hLive : sponge [1] = sponge [2])
    (hCR : let P := Poseidon2SpongeCR sponge; P) : False :=
  absurd (hCR [1] [2] hLive) (by simp)

/-- ⚑ THE CONTROL, and it is load-bearing: a GENUINE refutation, with several non-floor
hypotheses, in the shape of `collisionResistant_false_of_compressing` and every
`*_false_of_finite_range` in the tree. It must NOT appear in the gate's violation list. A rule that
gated this would make the campaign's own anti-floor work a build error, and a noisy gate gets
switched off — which is the same outcome as a blind one, reached more slowly. -/
theorem control_genuine_refutation_stays_exempt (f : List ℤ → ℤ)
    (hb : ∀ xs, 0 ≤ f xs ∧ f xs < (2013265921 : ℤ)) : ¬ Poseidon2SpongeCR f :=
  Dregg2.Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear f hb

#floor_ratchet
