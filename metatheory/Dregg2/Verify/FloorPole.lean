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
  3. **A satisfiability witness exists AT AN INHABITED CLASS**, in-tree: some theorem CLAIMS
     `F C₁ … Cₙ` while ASSUMING no floor content, every `Prop`-valued argument `Cᵢ` is a NAMED
     predicate of ours, and each one is PROVED to have two distinct members by an unconditional
     in-tree theorem. A floor with a refutation and no model is indistinguishable from a vacuity
     bomb (the exact finding `ae37dd523` landed against `CrossSchemeSameOpening`) — and a
     class-parameterized floor asserted at the EMPTY class is that same bomb wearing a model's
     clothes. ⚑ The second half of this check was MISSING for a day and both floors below rode
     the ⊥ model through it; see §1.
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
import Dregg2.Circuit.Emit.PicklesTranscriptBinding

set_option autoImplicit false

namespace Dregg2.Verify.FloorPole

/-- `HonestHypothesis (F a₁ … aₙ)` — a DECLARATION that `F` is an honest hypothesis: satisfiable,
refutable, and therefore not provable. Discharged by `trivial`; all of the content is in the four
conditions `#floor_ratchet` checks before honouring it (see the module docstring), each of which
FAILS THE BUILD rather than being quietly ignored.

Spell it applied to the floor at ARBITRARY arguments, so the declaration is about the floor and not
about one instance of it:

```lean
theorem pairSepOn_is_honest (P : List Nat → List Nat → Prop) :
    HonestHypothesis (pairSepOn P) := trivial
```

⚑ The floor must be parameterized by the CLASS it is asserted on, as this one is. Check (3) is
answered by exhibiting a NAMED class with two distinct members; a floor with no `Prop`-valued
argument gives that question nowhere to be asked, so its degenerate instantiation would be
invisible, and the gate REFUSES the declaration rather than honouring one it cannot adjudicate.

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

⚑ RE-MEASURED HOURS LATER ON A THIRD FLOOR NOBODY HAD DECLARED, AND IT CAME IN AT 5. `hashSepOn`
landed the same night in `5ecafe486` (P4's transcript binding), built DELIBERATELY in this shape,
and the tree-wide verdict went 1 → **5**. All four additions were `hashSepOn` consumers and not one
of them was a defect: the floor arrived with a `⊤` pole, a SECOND pole at a reachable two-element
class, a kernel-evaluated model over the deployed Poseidon, and its `_class_inhabited` companion
already written. Doing the whole doctrine correctly, in one commit, cost four build errors — the same
perverse incentive this module exists to remove, arriving through a new FLOOR instead of a new pole.
MEASURED BOTH WAYS 2026-07-29, lane `floor-honest` on hbox, same control as above plus one more line
(`Dregg2.Circuit.Emit.MinaWrapSgChunk0` commented LANE-LOCALLY — a co-tenant module landed the same
night whose ~75G peak `earlyoom` SIGTERMs on a box running five other lanes; its three siblings ARE
in the environment and contribute ZERO carriers, so the delta below is exact and the absolute is not
in doubt):

  * declaration ABSENT — **5** violations: 4 keyed to `hashSepOn` (`hashSepOn_mono`,
    `hashSepOn_top_imp`, `digest_binds_transcript_on`, `assertEqDigest_binds_transcript_on`), 1 to
    `Hash4NoCollision`.
  * declaration PRESENT — **1**, and it is the SAME survivor as the earlier run:
    `AutomataflRevealRefine.not_revealColl_of_hash4NoCollision`, still red, still correctly so. The
    gate named `hashSepOn`'s legs back: pole `hashSepOn_truncHashSep_false` — the SHARPER of the two,
    at the reachable class, not `⊤` — model `hashSepOn_modelHashSep`, class inhabited by
    `modelHashSep_class_inhabited`.

⚑ WHAT THE GATE ACCEPTED AS A MODEL — THE FAIL-OPEN, MEASURED 2026-07-28 AND CLOSED THE SAME DAY.
The honest-floor report names the model it found, and on both floors it found the ⊥ one:

    model Dregg2.Circuit.Emit.Sha256MerkleFold.pairSepOn_bot
    model Dregg2.Circuit.Emit.LightClientMidHashFold.compressSepOn_bot

— the class `fun _ _ => False`, whose proof is `fun _ _ _ _ h => h.elim` and holds no hash, no class
and no deployed object. The model check was satisfied by the floor holding VACUOUSLY at the empty
class, which is precisely the shape it was written to exclude, so ANY refuted floor could have been
declared honest — and had its consumers stop being billed — for the price of four characters of
`False`. The real models were `pairSepOn_modelSep` and `compressSepOn_midAbsorbSep` (kernel
evaluation of the deployed SHA-256 and BLAKE2b) all along, and the declarations were sound on them;
the gate simply was not reading the thing that made them models.

**THE REPAIR, and what it now demands.** `#floor_ratchet` no longer accepts a claim of the floor as
a model. Every `Prop`-valued argument of the floor in the model's statement must be a NAMED
predicate of ours, and each must be PROVED to have TWO DISTINCT MEMBERS by one unconditional in-tree
theorem — `C ā`, `C b̄` at closed arguments differing at a position, together with the disequality
there. That is `modelSep_class_inhabited` and `midAbsorbSep_class_inhabited`, which is why the
declarations below now cite them as the load-bearing half of leg (4).

⚑ **It is a PROOF OBLIGATION, not a name convention.** The checker keys on nothing but the
STATEMENT — no `_class_inhabited` suffix, no attribute, no list. `pairSepOn_bot`'s class is an
ANONYMOUS term, so there is no predicate to exhibit members of; and even named, `⊥ a b` is
unprovable at every `a`, `b`. No spelling buys it a pass. The two members must be DISTINCT for a
second reason worth writing down: a SINGLETON class satisfies a separation floor for free, because
any two of its members are the same member, so "inhabited" alone would have admitted a model with
exactly as much content as the ⊥ one.

⚑ **WHAT THE REPAIR STILL DOES NOT REACH.** The argument comparison is SYNTACTIC, so the two
members and their disequality have to be spelled the same way — they are, in one theorem, which is
why the obligation is stated as one theorem. And the test is keyed to a `Prop`-VALUED ARGUMENT: a
floor with NO class parameter has nowhere for the question to be asked, its degenerate instantiation
would be undetectable, and such a declaration is now REFUSED rather than waved through. That is the
fail-closed direction and it costs nothing today, both declared floors being class-parameterized;
the docstring example above is written in that shape for the same reason.

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
  4. MODEL PRESENT, AT AN INHABITED CLASS — `pairSepOn_modelSep`, by kernel evaluation of the
     REAL SHA-256 on all nine ordered pairs of a three-element class, **and**
     `modelSep_class_inhabited`, which is what the gate now reads: it proves `modelSep` holds of
     two closed pairs differing in their right component and that those components are DISTINCT.
     ⚑ `pairSepOn_bot` is REFUSED here and that is the point — its class is an anonymous
     `fun _ _ => False`, so there is no predicate to exhibit members of. `pairSepOn_tmChainSep`
     is a second model at the Tendermint chain's own pairs, with `tmChainSep_class_inhabited`. -/
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
  4. MODEL PRESENT, AT AN INHABITED CLASS — `compressSepOn_midAbsorbSep`, kernel-evaluated on the
     real BLAKE2b, **and** `midAbsorbSep_class_inhabited`, which the gate reads: two closed
     `(state, block, counter, flag)` members differing in the BLOCK, and those two blocks proved
     distinct. ⚑ `compressSepOn_bot` is REFUSED, same reason as `pairSepOn_bot`.

⚑ (2) here rests on ONE closed instance where `pairSepOn` has two, and the difference is real: the
`⊤` refutation is the weakest possible pole, since it says only "the floor is not the unrestricted
one". `weight_collision_block_out_of_range` records why there is no second one — the block the
collision needs carries a word `≥ 2^64`, which the width gate refuses, so the refuting class sits
OUTSIDE the class a gated absorb can walk. That is the honest reading and it is also the reason
this floor is plausible rather than refuted on the classes its consumers name. -/
theorem compressSepOn_is_honest (P : List Nat → List Nat → Nat → Nat → Prop) :
    HonestHypothesis (Dregg2.Circuit.Emit.LightClientMidHashFold.compressSepOn P) := trivial

/-- `PicklesTranscriptBinding.hashSepOn P` — the REAL Kimchi Poseidon-over-Pasta reference
`PastaPoseidon.Ref.hash` separates on the transcripts satisfying `P`. The THIRD floor of this shape,
and the first that arrived with all four legs ALREADY WRITTEN: `5ecafe486` (P4's transcript binding)
built it deliberately to mirror `pairSepOn`, so this declaration adds no content to that module — it
tells the gate what the module already proved.

  1. NOT A SENTINEL — `sentinelFloors` names the deployed-parameter crypto floors the campaign exists
     to delete; this is the campaign's own replacement shape, over a hash the kernel evaluates.
  2. REFUTED AT A CLOSED INSTANCE — twice, at two DIFFERENT constant classes. `hashSepOn_top_false`
     at `⊤`, where the floor collapses to the idealized `RefHashInjective`, killed by
     `hash_singleton_ignores_mod_pN`: `absorbAt` reduces its input mod `pN`, so
     `Ref.hash [x] = Ref.hash [x + pN]` for EVERY `x` — generic, no numeric coincidence, the
     analogue of `pairHash_ignores_word_64`. And `hashSepOn_truncHashSep_false` at the two-element
     class `truncHashSep`, riding `hash_empty_eq_hash_zero`: absorbing NOTHING and absorbing a bare
     `0` coincide, a ZERO-QUERY structural collision of the add-to-absorb sponge with no modular
     arithmetic in it at all. The second pole is what makes the class restriction load-bearing rather
     than decorative — unlike the `⊤` pole, the class it refutes at is a pair of transcripts a real
     prover could feed the sponge, so a consumer that declines to exhibit its class is not merely
     unproved. `compressSepOn` above has only the `⊤` pole and says so; this floor does not need
     that caveat.
  3. NOT REFUTED PARAMETRICALLY — those two are the tree's only `¬ hashSepOn …` theorems and both sit
     at a CONSTANT class. There is no `∀ P, ¬ hashSepOn P` and there cannot be: `hashSepOn_bot`
     proves the ⊥ instance and `hashSepOn_modelHashSep` proves a non-trivial one.
  4. MODEL PRESENT, AT AN INHABITED CLASS — `hashSepOn_modelHashSep`, by kernel evaluation of the
     REAL deployed Kimchi Poseidon (the reference `PastaPoseidon.lean` §5 anchors to o1js gold
     vectors) on all nine ordered pairs of the three-element class `modelHashSep`, **and**
     `modelHashSep_class_inhabited`, which is the half the gate actually reads: ONE unconditional
     theorem stating `modelHashSep [0]`, `modelHashSep [1]` and `([0] : List Nat) ≠ [1]` — two
     members at closed arguments differing at position 0, together with the disequality THERE. ⚑
     `hashSepOn_bot` is REFUSED, same reason as `pairSepOn_bot`: its class is an anonymous
     `fun _ => False`, so there is no predicate to exhibit members of.

⚑ WHAT THIS CLEARS, AND THE ONE THING IT CLEARS THAT IS WORTH NAMING. Three of the four carriers it
removes bind the floor at a UNIVERSALLY QUANTIFIED class and are the port shape the gate exists to
reward: `hashSepOn_mono` (`hashSepOn Q → hashSepOn P` under `P ≤ Q`), and P4's two payoff theorems
`digest_binds_transcript_on` / `assertEqDigest_binds_transcript_on`, which turn an `assertEqDigest`
between two REAL digests into TRANSCRIPT equality given separation on the class the two verification
instances themselves hash. The fourth, `hashSepOn_top_imp : hashSepOn ⊤ → RefHashInjective`, binds
the floor at the REFUTED `⊤` instance and is vacuous read as a standalone implication. It is cleared
because its one remaining floor mention — `RefHashInjective`, still derived as refuted, still gated
for everyone else — sits in CLAIM position, which the position rule exempts. Say plainly why that is
right rather than leaving it to be discovered: the declaration is per-FLOOR, not per-INSTANCE, so the
gate cannot bill a consumer for standing at the one class the floor is known to fail at.
`hashSepOn_top_imp` is not a guarantee about the deployed system — it is the upper pole's own
plumbing, its ONLY consumer in the tree is `hashSepOn_top_false`, and deleting it would move the same
term inline. `Sha256MerkleFold.pairSepOn_top_iff` sits on that same residual from the other side,
where an `↔` put the idealized twin in ASSUMPTION position and kept it correctly red. -/
theorem hashSepOn_is_honest (P : List Nat → Prop) :
    HonestHypothesis (Dregg2.Circuit.Emit.PicklesTranscriptBinding.hashSepOn P) := trivial

#assert_axioms pairSepOn_is_honest
#assert_axioms compressSepOn_is_honest
#assert_axioms hashSepOn_is_honest

end Dregg2.Verify.FloorPole
