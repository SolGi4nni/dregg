/-
# Dregg2.Verify.FloorPole — declaring a floor HONEST, so writing its refutability pole is free.

`feedback-prove-the-floor-false` requires three things of a floor: it must be **SATISFIABLE**
(else every consumer is vacuously true), **REFUTABLE** (else it asserts nothing), and **NOT
PROVABLE** (else it is a tautology wearing an assumption's clothes). Two of those are witnesses
you write down. The third falls out of the first two.

⚑ **AND UNTIL THIS MODULE EXISTED, WRITING THE SECOND ONE REDDED THE ROOT.**

`#floor_ratchet` derives its refuted-floor set from `¬ F …`-concluding theorems, and it derives
it for a reason — a hand-maintained list is how the Python ruler went blind to 7 of 10 refuted
floors. But the derivation cannot tell these two apart, because they have the same TYPE SHAPE:

  * `poseidon2SpongeCR_false_babyBear : ¬ Poseidon2SpongeCR deployedSponge` — the floor is FALSE
    where the system stands. Every consumer is vacuous. **The gate must red them.**
  * `canonical_fails_on_dup : ¬ Lace.Canonical dupLace` — the floor FAILS at a deliberately
    degenerate instance, exhibited to show the hypothesis has content. This is the doctrine's own
    required check on an honest structural invariant, and its consumers are not vacuous at all.
    **The gate must not touch them.**

So completing the doctrine's check on an honest floor reclassified it as refuted and turned every
one of its consumers into a build error. The author's reward for doing the required work was a red
root and a pile of baseline entries. `docs/UNREFUTED-FLOORS-AUDIT.md` finding 4 records this as the
plausible mechanical reason **5 of the 8 unrefuted floors have no refutability witness at all**,
and `ae37dd523` records an author routing around it in the live tree: `CrossSchemeSameOpening`'s
refutability pole was deliberately NOT spelled `¬ CrossSchemeSameOpening …`, so the instrument
would not see it, so the gate would not fire. An instrument people route around measures a tree
shaped by the routing.

## THE DECLARATION

`HonestHypothesis P` is `True`. It is not a proof obligation and it is not evidence — it is a
NAME the gate can find in the elaborated environment, exactly the way it finds everything else.
All of the content is in what `#floor_ratchet` CHECKS before it honours one:

  1. **Not a named sentinel.** The 17 floors in `FloorCensus.sentinelFloors` — `Poseidon2SpongeCR`,
     `MSISHard`, `CollisionResistant`, the `StateCommit` family, … — can NEVER be declared honest.
     Those are the deployed-parameter crypto floors this campaign exists to delete, and the
     fail-closed sentinel check would refuse the run anyway. Named first so nobody has to discover
     it by trying.
  2. **A refutability pole exists**, in-tree, at a CLOSED instance: some theorem proves
     `¬ F c₁ … cₙ` with no telescope fvars in the arguments. Declaring a floor honest when nothing
     refutes it declares nothing — the honest state for such a floor is `UNREFUTED`, which the
     census already reports and the gate already ignores.
  3. **A satisfiability witness exists**, in-tree: some theorem CLAIMS `F …` (at a closed instance
     or under an `∃`) while ASSUMING no floor content. A floor with a refutation and no model is
     indistinguishable from a vacuity bomb, which is the exact finding `ae37dd523` landed against
     `CrossSchemeSameOpening`. Both poles or nothing.
  4. **The refutation is NOT PARAMETRIC.** `∀ f, ¬ F f` says the floor fails at EVERY instance —
     that is not "refutable", that is FALSE, and its consumers are vacuous however the author
     labels it. A parametric refutation beats the declaration, always.

Fail any of those and the gate hard-errors naming the floor and the missing pole. It does not
quietly ignore the declaration: a declaration the gate silently drops is worse than none, because
the author believes the floor is classified and it is not.

## WHY THIS IS NOT A LOOPHOLE, STATED PLAINLY

It removes NOTHING that is gated today: no floor in this tree is declared honest as this lands, so
the derived refuted set, the carrier surface and the baseline are byte-identical. It changes what
happens NEXT TIME someone completes the doctrine's check on an honest floor — three lines (model,
counterexample, declaration) instead of a red root and N grandfathered names.

And every use is visible three ways: as source next to the floor, as a `HONEST` record in
`#floor_census`, and as a line in `#floor_ratchet`'s own log on every root build.

The check it cannot run is the semantic one — whether the closed instance the pole refutes is the
DEPLOYED instance or a demo. That is why (1) exists: for the floors where "deployed" is the whole
question, the answer is hard-wired to NO.

## THE DECLARATIONS LIVE HERE, AND THAT FIXES THE IMPORT DIRECTION

The docstring above was written expecting the FLOOR's module to `import Dregg2.Verify.FloorPole`
and declare next to its own definition. It is the other way round: this module imports the floors,
because `Dregg2.lean` already imports THIS file (line 1413) and nothing else needs to change for a
declaration to reach the gate. The cost is stated so the next author does not discover it as a
cycle: a module reached from the `import`s below can never itself import `Verify/FloorPole`.
-/

import Dregg2.Circuit.Emit.Sha256MerkleFold
import Dregg2.Circuit.Emit.LightClientMidHashFold

set_option autoImplicit false

namespace Dregg2.Verify.FloorPole

/-- `HonestHypothesis (F a₁ … aₙ)` — a DECLARATION that `F` is an honest hypothesis: satisfiable,
refutable, and therefore not provable. Discharged by `trivial`; all of the content is in the four
conditions `#floor_ratchet` checks before honouring it (see the module docstring), each of which
FAILS THE BUILD rather than being quietly ignored.

Spell it applied to the floor at ARBITRARY arguments, so the declaration is about the floor and not
about one instance of it:

```lean
theorem strandForkFree_is_honest (l : Lace) (n : ℕ) :
    HonestHypothesis (StrandForkFree l n) := trivial
```

⚑ It is NOT a licence to assume the floor. Consumers still take it as a hypothesis and still owe
the discharge; what changes is that the gate stops treating the floor's own COUNTEREXAMPLE as
proof that they are vacuous. -/
def HonestHypothesis (_P : Prop) : Prop := True

/-- The one inhabitant. `HonestHypothesis` is `True`, so this is definitional — the declaration is
a NAME for the gate to find, not evidence. -/
theorem honest (P : Prop) : HonestHypothesis P := trivial

/-! ## §1 — THE DECLARED FLOORS, AND THE MEASUREMENT THAT PUT THEM HERE

Both are the same shape and it is the shape this file was built for: a floor PARAMETERIZED by the
class it is asserted on, whose restriction to a class is load-bearing because the UNRESTRICTED
instance is exactly the refuted idealized floor. `¬ F ⊤` is therefore a required part of the
statement, not a defect in it — and the derivation, which sees only `¬ F …`, promoted `F` wholesale
and gated every consumer at every class.

⚑ MEASURED BOTH WAYS on the real tree, 2026-07-28, lane `floor-honest` on hbox, `lake build Dregg2`
with the four red/WIP `Games.Dungeon*` root imports commented LANE-LOCALLY so the gate could
adjudicate at all:

  * declarations ABSENT — **22** violations: 17 keyed to `pairSepOn`, 4 to `compressSepOn`, 1 to
    `Hash4NoCollision`. Every one of the 21 in the first two groups binds the floor at a
    UNIVERSALLY QUANTIFIED class `P` and pairs it with a coverage obligation (`FoldCovered` /
    `AbsorbCovered`), i.e. the consumer must EXHIBIT its transcript — the exact port shape the gate
    exists to reward.
  * declarations PRESENT — **2**. Both survive on their own merits and neither is in the
    parameterized-class family:
      - `AutomataflRevealRefine.not_revealColl_of_hash4NoCollision`, below;
      - `Sha256MerkleFold.pairSepOn_top_iff`, which is a carrier of `pairHashInjective` — the
        IDEALIZED twin, still refuted, still model-free — and NOT of the floor declared honest
        here. The gate reports one floor per carrier, so `pairSepOn` was the name printed against
        it in the 22; `pairHashInjective` was always the reason.

That second survivor is the control this run needed, and it is a sharper one than a synthetic probe:
declaring `pairSepOn` honest did NOT launder the refuted floor sitting FOUR LINES ABOVE IT IN ITS
OWN FILE. It is also a spelling artefact worth naming, because the same content one file over is
exempt: `LightClientMidHashFold` states its upper pole as `¬ compressSepOn ⊤` and carries nothing,
while `Sha256MerkleFold` states it as `pairSepOn ⊤ ↔ pairHashInjective`, and an `↔` puts BOTH sides
in assumption position. Only the `.mp` direction is ever used (by `pairSepOn_top_false`). That is
the fold arc's one-line call, not this file's.

⚑ WHAT THE GATE ACCEPTED AS A MODEL, AND WHY THAT IS THINNER THAN IT READS. The honest-floor report
names the model it found, and on both floors it found the ⊥ one — `pairSepOn_bot` /
`compressSepOn_bot`, the class `fun _ _ => False`. Check (3) is satisfied by a floor that holds
VACUOUSLY at the empty class, which is the shape the check was written to exclude. The real models
are `pairSepOn_modelSep` and `compressSepOn_midAbsorbSep` (kernel evaluation of the deployed SHA-256
and BLAKE2b), and what makes THEM models is `modelSep_class_inhabited` / `midAbsorbSep_class_inhabited`
— companions the gate does not read and, being a type-shape check, cannot. So (3) is a check that
SOMETHING claims the floor, not that anything inhabits it non-trivially. Stated here rather than
worked around: the declarations below are sound on the real models, and the gate would have
honoured them on the empty one.

⚑ `Circuit.Emit.AutomataflRevealRefine.Hash4NoCollision` is NOT declared here and MUST NOT BE. It
fails checks (3) and (4) on its own merits: `hash4NoCollision_false_babyBear` refutes it for an
ARBITRARY `hash` bounded by the BabyBear modulus, which is a refutation at every instance the tree
deploys rather than at one degenerate class, and no theorem in the tree claims `Hash4NoCollision …`
at any instance at all. Its one remaining consumer,
`not_revealColl_of_hash4NoCollision`, IS vacuous at deployed parameters — it records that the old
floor implied the new per-instance residual — and the gate is right to say so. -/

/-- `Sha256MerkleFold.pairSepOn P` — `pairHash` separates on the pairs satisfying `P`.

  1. NOT A SENTINEL — the sentinel list is the deployed-parameter crypto floors; this one is
     one night old and is the campaign's own replacement shape.
  2. REFUTED AT A CLOSED INSTANCE — `pairSepOn_truncSep_false` at the two-element class
     `truncSep`, riding an EXECUTABLE collision (`pairHash_ignores_word_64`: message word 64 of
     `a ‖ b` is never read), and `pairSepOn_top_false` at `⊤`, where the floor IS the refuted
     `pairHashInjective`.
  3. NOT REFUTED PARAMETRICALLY — the only two `¬ pairSepOn …` theorems in the tree are the two
     above, both at a constant class. There is no `∀ P, ¬ pairSepOn P`, and there cannot be:
     `pairSepOn_bot` proves the ⊥ instance.
  4. MODEL PRESENT — `pairSepOn_modelSep`, by kernel evaluation of the REAL SHA-256 on all nine
     ordered pairs of a three-element class, with `modelSep_class_inhabited` pinning that the
     class holds genuinely distinct members. `pairSepOn_tmChainSep` is a second one at the
     Tendermint chain's own pairs. -/
theorem pairSepOn_is_honest (P : List Nat → List Nat → Prop) :
    HonestHypothesis (Dregg2.Circuit.Emit.Sha256MerkleFold.pairSepOn P) := trivial

/-- `LightClientMidHashFold.compressSepOn P` — `Ref.compress` separates on the `(state, block)`
pairs satisfying `P` at a given `(counter, flag)`.

  1. NOT A SENTINEL. ⚑ `Circuit.StateCommit.compressInjective` IS one; this floor's own idealized
     twin `Emit.LightClientMidHashFold.compressInjective` is a DIFFERENT constant in a different
     namespace, refuted here by `compressInjective_false` and correctly left in the refuted set.
  2. REFUTED AT A CLOSED INSTANCE — `compressSepOn_top_false` at `⊤`, where the floor collapses to
     that idealized twin, which the weight-inflation collision refutes by kernel evaluation
     (`authSetRootRef_weight_collision`: weight `0` and weight `2^64` share a root, because a
     BLAKE2b message word is read only modulo `2^64`).
  3. NOT REFUTED PARAMETRICALLY — `compressSepOn_top_false` is the tree's only `¬ compressSepOn …`,
     at a constant class; `compressSepOn_bot` proves the ⊥ instance.
  4. MODEL PRESENT — `compressSepOn_midAbsorbSep`, kernel-evaluated on the real BLAKE2b, with
     `midAbsorbSep_class_inhabited` for the class.

⚑ (2) here rests on ONE closed instance where `pairSepOn` has two, and the difference is real: the
`⊤` refutation is the weakest possible pole, since it says only "the floor is not the unrestricted
one". `weight_collision_block_out_of_range` records why there is no second one — the block the
collision needs carries a word `≥ 2^64`, which the width gate refuses, so the refuting class sits
OUTSIDE the class a gated absorb can walk. That is the honest reading and it is also the reason
this floor is plausible rather than refuted on the classes its consumers name. -/
theorem compressSepOn_is_honest (P : List Nat → List Nat → Nat → Nat → Prop) :
    HonestHypothesis (Dregg2.Circuit.Emit.LightClientMidHashFold.compressSepOn P) := trivial

#assert_axioms pairSepOn_is_honest
#assert_axioms compressSepOn_is_honest

end Dregg2.Verify.FloorPole
