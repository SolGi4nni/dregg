/-
# Dregg2.Circuit.Emit.PastaSpongeWeld — the TWO sponge copies, welded.

## The finding this file closes

The cross-implementation differential (`scripts/pickles-crossimpl-differential.sh`,
`metatheory/EmitConformanceVectors.lean`) diffs ONE of this tree's two Poseidon sponge spellings
against `mina_poseidon::ArithmeticSponge`: the incremental state machine
`PastaPoseidonFq.SpongeSt` / `absorb1` / `squeeze1` / `challenge`, over the pairs `sponge_fp`,
`sponge_fq` and `challenge`. The OTHER spelling — `PastaPoseidon.Ref.absorbAll` / `Ref.hash`, a
whole-list fold with `pN`/`mdsN`/`rcsN` baked in — was diffed by NOTHING, and it is the one the
Fr-sponge sits on: `KimchiVerify.frSpongeDigest` and `KimchiVerify.frSqueezePair` are both defined
through `Ref.absorbAll`.

⚑ So the differential's green covered the sponge that DOES NOT feed the weld. That is the gap.

## What the two copies actually are — read, not assumed

They are the SAME algorithm in two shapes, and the tree already proved half of it:

  * `PastaPoseidonFq.Core` is the parameter-generic rendering of `PastaPoseidon.Ref` (identical
    `sbox`/`round`/`perm`/`absorbAt`/`absorbFrom` bodies, a `Params` record in place of the baked
    constants), and `PastaPoseidonFq.core_is_Ref_at_Fp` proves `Core.hash fpParams = Ref.hash` BY
    INDUCTION over every input.
  * `SpongeSt`'s `absorb1` / `squeeze1` are written against `Core.absorbAt` / `Core.perm` — they do
    not re-transcribe the permutation at all.

What was NEVER established is that the state machine's schedule agrees with the whole-list fold.
`Ref.absorbFrom`'s `[]` clause supplies a closing permutation; `absorbMany` supplies none and leaves
the sponge in `Absorbed n`, the closing permutation coming from `squeeze1`'s `.absorbed` branch.
Two different places, and nothing said they line up. `absorbMany_squeeze1` below says they do — for
every parameter set, every input and every lane-counter state, by induction, so a divergence at any
length is a red rather than an unpinned case.

## What the weld buys

`frSqueezePair_is_two_challenges` states that `KimchiVerify.frSqueezePair` — the v′/u′ derivation
the C3 challenge check runs on — is EXACTLY two successive `challenge fpParams` calls of the sponge
the `challenge` differential pair drives, and `frSpongeDigest_is_squeeze` states the Fr-sponge digest
is that same sponge's squeeze. The cross-impl green on `sponge_fp` / `challenge` therefore transfers
to the weld-feeding side by theorem rather than by hope.

The differential covers the other direction: `EmitConformanceVectors`'s `frdigest` / `frpair` /
`frphase2` pairs drive `Ref.hash`, `frSqueezePair` and `frSpongeDigest` against o1-labs'
`DefaultFrSponge` (`absorb` / `challenge` / `digest` / `absorb_evaluations`) — a Rust these theorems
cannot see. A theorem that the two Lean copies agree, plus a differential that one of them matches
the Rust, is what makes the pair of them mean something; neither alone does.

## Substrate

⚑ No AIR, no gate, no constraint. This file states equalities between existing value-returning
definitions and pins three of them at concrete inputs. `#assert_axioms`-clean; no `sorry`, no
`native_decide`.
-/
import Dregg2.Circuit.Emit.KimchiVerify
import Dregg2.Circuit.Emit.PastaPoseidonFq

set_option autoImplicit false

namespace Dregg2.Circuit.Emit.PastaSpongeWeld

open Dregg2.Circuit.Emit.PastaPoseidon
open Dregg2.Circuit.Emit.PastaPoseidonFq
open Dregg2.Circuit.Emit.KimchiVerify (low128 frSqueezePair frSpongeDigest frPhase2Inputs)

/-! ## §1 — the schedule weld: the state machine's absorb-then-squeeze IS the whole-list fold. -/

/-- **`absorbMany_squeeze1`** — absorbing `xs` through the `SpongeSt` state machine from
`Absorbed n` and then squeezing yields EXACTLY the state `Core.absorbFrom` computes from the same
`(st, n)`, together with its lane-0 projection and the `Squeezed 1` mode.

The closing permutation lives in `squeeze1`'s `.absorbed` branch on the left and in `absorbFrom`'s
`[]` clause on the right; this is the statement that those are the same one permutation, applied
once. Generic in `Params` (so it holds at `fpParams`, the Fr-sponge, and at `fqParams`, phase 1),
and by induction on `xs`. -/
theorem absorbMany_squeeze1 (P : Params) :
    ∀ (xs st : List Nat) (n : Nat),
      squeeze1 P (absorbMany P ⟨st, .absorbed n⟩ xs)
        = (⟨Core.absorbFrom P st n xs, .squeezed 1⟩,
           (Core.absorbFrom P st n xs).getD 0 0) := by
  intro xs
  induction xs with
  | nil => intro st n; rfl
  | cons x rest ih =>
      intro st n
      simp only [absorbMany, List.foldl_cons, absorb1, Core.absorbFrom]
      by_cases h : n = rate
      · simp only [h]
        exact ih _ 1
      · simp only [if_neg h]
        exact ih _ (n + 1)

/-- **`sponge_absorb_squeeze_is_hash`** — the state machine's squeeze after absorbing `xs` from a
fresh sponge is the whole-list `Core.hash P xs`. -/
theorem sponge_absorb_squeeze_is_hash (P : Params) (xs : List Nat) :
    (squeeze1 P (absorbMany P newSponge xs)).2 = Core.hash P xs := by
  simp only [newSponge, absorbMany_squeeze1 P xs [0, 0, 0] 0, Core.hash, Core.absorbAll]

/-- ⚑ **`two_sponge_copies_agree`** — THE STATEMENT OF FINDING 2. The sponge the cross-impl
differential drives (`SpongeSt` absorb-then-squeeze at `fpParams`) and the sponge the Fr-sponge weld
is built on (`PastaPoseidon.Ref.hash`) compute the SAME function of the SAME input, for every input.
Not "should be equivalent": equal, by induction, at every length. -/
theorem two_sponge_copies_agree (xs : List Nat) :
    (squeeze1 fpParams (absorbMany fpParams newSponge xs)).2 = Ref.hash xs := by
  rw [sponge_absorb_squeeze_is_hash, core_is_Ref_at_Fp]

/-- The state-level version: the sponge state the differential's `sponge_fp` pair leaves behind is
`Ref.absorbAll`'s output, so BOTH lanes (not only lane 0) are the same object. This is what
`frSqueezePair` needs, since it reads lane 1. -/
theorem two_sponge_copies_agree_state (xs : List Nat) :
    (squeeze1 fpParams (absorbMany fpParams newSponge xs)).1.st = Ref.absorbAll [0, 0, 0] xs := by
  simp only [newSponge, absorbMany_squeeze1 fpParams xs [0, 0, 0] 0, Ref.absorbAll,
    absorbFrom_at_fp]

/-! ## §2 — the Fr-sponge, expressed in the DIFFED sponge. -/

/-- The rate-boundary step, isolated: a squeeze from `Squeezed 1` finds `1 ≠ rate = 2`, so it reads
lane 1 of the SAME state and performs NO permutation (`poseidon.rs:128-146`). This is why the second
`challenge()` is free, and it is the step `frSqueezePair`'s second component encodes. -/
theorem squeeze1_squeezed_one (P : Params) (t : List Nat) :
    squeeze1 P ⟨t, .squeezed 1⟩ = (⟨t, .squeezed 2⟩, t.getD 1 0) := rfl

/-- ⚑ **`frSqueezePair_is_two_challenges`** — `KimchiVerify.frSqueezePair`, the v′/u′ derivation
`challengesOk` runs on, IS two successive `challenge fpParams` calls of the `SpongeSt` sponge: the
first squeezes lane 0 of the permuted state, the second finds `Squeezed 1 ≠ rate` and reads lane 1
of the SAME state with no second permutation. That rate-boundary behaviour is exactly what the
`challenge` differential pair sweeps against `DefaultFqSponge::challenge`. -/
theorem frSqueezePair_is_two_challenges (stream : List Nat) :
    frSqueezePair stream
      = ((challenge fpParams (absorbMany fpParams newSponge stream)).2,
         (challenge fpParams (challenge fpParams (absorbMany fpParams newSponge stream)).1).2) := by
  simp only [frSqueezePair, challenge, newSponge, absorbMany_squeeze1 fpParams stream [0, 0, 0] 0,
    squeeze1_squeezed_one, Ref.absorbAll, absorbFrom_at_fp, low128]

/-- ⚑ **`frSpongeDigest_is_squeeze`** — the Fr-sponge's phase-2 digest is the diffed sponge's
squeeze over the phase-2 absorb stream. `fr_sponge.digest()` is one `sponge.squeeze()`
(`plonk_sponge.rs:51-53`), and this says dregg's rendering of it is the sponge the differential
covers, at the actual stream `frPhase2Inputs` assembles. -/
theorem frSpongeDigest_is_squeeze (digest ftEval1 pZeta pZetaOmega : Nat)
    (evZeta evZetaOmega : List Nat) :
    frSpongeDigest digest ftEval1 pZeta pZetaOmega evZeta evZetaOmega
      = (squeeze1 fpParams (absorbMany fpParams newSponge
          (frPhase2Inputs digest ftEval1 pZeta pZetaOmega evZeta evZetaOmega))).2 := by
  simp only [frSpongeDigest, two_sponge_copies_agree]

/-! ## §3 — the agreement PINNED at concrete inputs.

The theorems above are the real content; these are the drift alarm. Two shapes that agree today are
two shapes that will disagree later, and a `#guard` is what makes the disagreement loud at
elaboration time instead of at the next differential run. The empty list, a partial block, an exact
rate block, a rate+1 block and a two-block input are all here because the rate boundary is where the
two schedules could differ. -/

#guard (squeeze1 fpParams (absorbMany fpParams newSponge [])).2 == Ref.hash []
#guard (squeeze1 fpParams (absorbMany fpParams newSponge [1])).2 == Ref.hash [1]
#guard (squeeze1 fpParams (absorbMany fpParams newSponge [1, 2])).2 == Ref.hash [1, 2]
#guard (squeeze1 fpParams (absorbMany fpParams newSponge [1, 2, 3])).2 == Ref.hash [1, 2, 3]
#guard (squeeze1 fpParams (absorbMany fpParams newSponge [1, 2, 3, 4])).2 == Ref.hash [1, 2, 3, 4]
#guard (squeeze1 fpParams (absorbMany fpParams newSponge [0, 0, 0, 0, 0])).2
        == Ref.hash [0, 0, 0, 0, 0]

-- Non-vacuity: the guards above are not "everything equals everything". A one-element shift of the
-- stream moves the value, and lane 1 is NOT lane 0.
#guard Ref.hash [1, 2] != Ref.hash [2, 1]
#guard (frSqueezePair [1, 2, 3]).1 != (frSqueezePair [1, 2, 3]).2

-- And the two lanes of the pair really are lanes 0 and 1 of ONE permuted state, which is what makes
-- the second `challenge()` cost no permutation.
#guard (frSqueezePair [1, 2, 3]).1
        == low128 ((squeeze1 fpParams (absorbMany fpParams newSponge [1, 2, 3])).1.st.getD 0 0)
#guard (frSqueezePair [1, 2, 3]).2
        == low128 ((squeeze1 fpParams (absorbMany fpParams newSponge [1, 2, 3])).1.st.getD 1 0)

#assert_axioms absorbMany_squeeze1
#assert_axioms squeeze1_squeezed_one
#assert_axioms sponge_absorb_squeeze_is_hash
#assert_axioms two_sponge_copies_agree
#assert_axioms two_sponge_copies_agree_state
#assert_axioms frSqueezePair_is_two_challenges
#assert_axioms frSpongeDigest_is_squeeze

end Dregg2.Circuit.Emit.PastaSpongeWeld
