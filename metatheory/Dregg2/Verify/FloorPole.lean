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
-/

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

end Dregg2.Verify.FloorPole
