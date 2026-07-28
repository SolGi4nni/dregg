/-
# Dregg2.Verify.FloorRatchet — THE ACCRUAL GATE (`#floor_ratchet`)

The vacuity campaign was measured over its own window (`74f2623c51^` → HEAD) and it was
LOSING: 52 carriers removed, **63 added**, net **+11**. Forty-six of the additions were
BRAND-NEW theorems in BRAND-NEW modules landed by other lanes while the campaign ran, every
one of them taking `Poseidon2SpongeCR` — a hypothesis this tree PROVES FALSE at deployed
BabyBear parameters — as a hypothesis. Accrual was outrunning removal ~1.2 : 1. Porting
faster cannot win that race. Only a gate can.

This is the gate. It fails the build when a NEW declaration takes a REFUTED floor as a
hypothesis.

## Where it runs, and why there
`#floor_ratchet` is invoked at the END of `Dregg2.lean` — the root module every lane already
builds (`lake build Dregg2`, the standing green bar). At that point the environment holds the
whole tree, so the check reads the ELABORATED environment, not source text.

⚑ **Everything it reads arrives through IMPORTS.** That is the point, and it is the direct
repair of the campaign's previous tooth. `Tools/ConeCutoverListCommit` asserted its post-state
by reading files through `IO.FS`; lake's dependency graph is built from IMPORTS and cannot see
an `IO.FS.readFile`, so the module was replayed from a cached olean forever — `lake build`
returned EXIT=0 while a forced `lake env lean` on the same file returned EXIT=1 on a REAL
violation. A check outside the dependency graph is theatre in both directions.

Here, the two inputs are:
  * the environment — reached by `import`, so adding a theorem ANYWHERE under `Dregg2/`
    invalidates that module's olean, transitively invalidates `Dregg2.olean`, and forces
    `Dregg2.lean` (and this check) to re-elaborate; and
  * the baseline — `Dregg2.Verify.FloorRatchetBaseline`, a Lean SOURCE module holding a
    `def`, so editing it is an import change too.
There is no third input and no file read. The check cannot go stale without lake knowing.

## What counts as a violation
A declaration in our modules whose ELABORATED TYPE mentions a refuted floor, in any position,
directly or through a `Prop`-def whose BODY carries one, or through a STRUCTURE one of whose
FIELDS carries one — or a floor spelled INLINE rather than by name. Six surfaces, all gated:

  * **binder** — `theorem foo (hCR : Poseidon2SpongeCR hash) : …`. The visible class.
  * **prop-body** — `def descriptorRefines … : Prop := Poseidon2SpongeCR hash → …`. The floor
    is in the def's VALUE, so its users have NO floor binder and are invisible to every
    binder-keyed ruler. The census found ~250 carriers hiding behind three such defs
    (`descriptorRefines`, `descriptorComplete`, `ClosedLogExtract`).
  * **propdef-user** — a declaration whose type mentions such a def.
  * **bundle** — a STRUCTURE with a floor-typed FIELD. `CommitSurface` carries four
    (`cmbInj`/`compInj : compressInjective`, `compNInj`, `leafInj`), so no inhabitant of it
    exists at deployed BabyBear parameters.
  * **bundle-user** — ⚑ THE B3 HOLE, closed 2026-07-25. A declaration that takes such a
    structure as a HYPOTHESIS is exactly as vacuous as one taking a floor binder, and until this
    landed it added ZERO carriers. The adversarial probe was one line:
    `b3_via_grandfathered_bundle (R : Poseidon2RealizedSponge s) … : xs = ys := R.spongeCR xs ys h`
    — the gate's prop-body fixpoint covered `Prop`-valued DEFS only and never propagated through
    structure fields, so 32 grandfathered bundles (`CommitSurface` alone reached by 409
    declarations) were a standing bypass anyone could take today.
  * **inj-spelled** — ⚑ THE SPELLING HOLE, closed 2026-07-25. Every class above keys on a floor
    NAME; `Poseidon2SpongeCR f` is DEFINITIONALLY `Function.Injective f` at `f : List ℤ → ℤ`, so
    the identical hypothesis cost a build error under one spelling and nothing under the other.
    The gate's own log printed the size of the bypass on every run ("N `Function.Injective`-spelled
    sites ungated (known residual)"). It is a SPLIT, not a blanket gate — a compressing function
    cannot be injective, a widening or structural one may genuinely be — and the split is DERIVED
    from in-tree refutations, never from a list. See `Dregg2/Verify/InjSpelling.lean`. The refuted
    half turned out to be worse than the named floors: ~600 sites bind `Function.Injective D` for a
    whole-function digest `(CellId → AssetId → ℤ) → ℤ`, whose domain is UNCOUNTABLE, so no such
    injection exists at ANY parameters (`Dregg2/Verify/InjSpelledFloors.lean`) — a cardinality
    impossibility rather than an optimistic assumption about Poseidon2.

The prop-body and bundle sets are computed to a JOINT fixpoint: a `Prop` def whose body mentions
a floor bundle carries a floor, a structure with a floor-carrying-`Prop`-def field carries one,
and a structure with a floor-carrying-STRUCTURE field carries one. So a def-of-a-def, a
bundle-of-a-bundle, and every mixture is caught.

`mk` and projections stay in the scan (the other compiler companions — `casesOn`, `recOn`,
`injEq`, `eq_def`, … — are dropped as noise; their parent is always caught).

EXEMPT, because it is ANTI-floor content and the campaign wants MORE of it, not less: a
declaration that REFUTES floor content and ASSUMES none — see `antiFloor`. Writing a new
refutation never trips the gate; assuming a refuted floor on the way to a negation does.

  * **THE POSITION RULE, 2026-07-27.** That exemption was implemented as "the conclusion is `¬ F …`
    or `False`, AND no binder carries floor content", and only the second half was ever the rule.
    The first half taxed every declaration that says something POSITIVE about a floor: its MODEL
    (`theorem sat : F goodInstance`, or `∃ f, F f`), and its COUNTEREXAMPLE written one conjunct
    off the blessed spelling (`forked_strand_not_forkFree : forkedLace = … ∧ ¬ StrandForkFree …`).
    None of those assumes anything — if the floor is false they become UNPROVABLE, not vacuous —
    and all of them were `binder`-class carriers. `34854bf62` is the tree paying for it in the
    other direction: a satisfiability witness DELETED partly because naming a floor in a conclusion
    "is a gate carrier for no benefit". The test is now `assumesFloorContent`: a declaration is a
    carrier exactly when its claim is CONTINGENT on floor content — every `∀`/`→` domain anywhere,
    including ones buried inside an `∃` or a conjunct, and both sides of an `↔`, and any occurrence
    at all of a `prop-body` def or a BUNDLE (those UNFOLD to an implication / have no inhabitant,
    so a positive claim about one IS the vacuity). `specSatisfiabilityWitness`, `specPoleInConjunct`,
    `specClaimBuriedArrow` and `specIffLaundry` pin all four edges on every run.

## HONEST FLOORS — the gate stopped taxing the refutability pole (`Verify/FloorPole`)

The refuted set is derived from `¬ F …` theorems, and two very different things have that shape:
`¬ Poseidon2SpongeCR deployedSponge` (the floor is FALSE where the system stands — gate its
consumers) and `¬ Lace.Canonical dupLace` (the floor FAILS at a degenerate instance, which is the
doctrine's REQUIRED refutability check on an honest structural invariant — leave its consumers
alone). The derivation promoted both, so completing `feedback-prove-the-floor-false` on an honest
floor reddened the root and cost a pile of baseline entries.
`docs/UNREFUTED-FLOORS-AUDIT.md` finding 4 records that as the plausible reason 5 of the 8
unrefuted floors have NO refutability witness, and `ae37dd523` records an author deliberately
mis-spelling the one pole they did write so the instrument would not see it. An instrument people
route around measures a tree shaped by the routing.

A floor now leaves the refuted set only via an explicit in-tree `FloorPole.HonestHypothesis`
declaration, and only when FOUR checks pass — never a sentinel, refuted at a CLOSED instance,
NOT refuted parametrically, and with a satisfiability witness in the environment. Every failure is
a hard error naming the missing pole; every success is printed on every root build with both poles.
It removes nothing gated today (no floor is declared honest as this lands) and it makes the correct
next move three lines instead of a red root.

  * **B4 — the BINDER-ORDER hole, closed 2026-07-25.** The exemption used to accept a `False`
    conclusion whenever the floor was the INNERMOST binder, since `Γ → F → False` IS `Γ → ¬ F`.
    True, and still a hole: ORDER IS A SPELLING THE AUTHOR CONTROLS, so the same soundness claim
    was gated or exempt depending on where its floor hypothesis sat, and the gate's own error text
    coached the swap. It now consults NO position — a floor in ANY hypothesis disqualifies. What
    was sitting on the hole was `HermineMSIS.no_forgery_under_msis` and
    `HermineSelfTargetMSIS.no_forgery_under_msis_selftarget`: "the deployed threshold signature
    cannot be forged", resting on `Lattice.MSISHard`, which `CryptoFloorTeeth` REFUTES.

## The floor list is DERIVED, never hand-maintained
A hand list is how the Python ruler went blind to 7 of 10 refuted floors and how the campaign
was measured at 1273 when the true surface was ~1650. `refutedFloors` is computed from the
environment on every run:

  `F` is a refuted floor ⟺ `F` is a `Prop`-valued `def` in our modules, AND some theorem in
  our modules concludes `¬ F …`, AND (`F` is injectivity-SHAPED — the `injShape`/`injShapeAnd`
  δ-test shared with `#floor_census` — OR `F` is a named sentinel, for the floors whose shape
  is not injectivity, e.g. `MSISHard`'s `¬∃`).

Prove a new floor false and the gate starts defending it the same build, with no edit here.

## FAIL-CLOSED
A gate that under-measures passes vacuously and looks exactly like success. `#floor_ratchet`
hard-errors — never passes quietly — unless (a) the environment holds ≥ 500 000 constants
(whole-tree scale), (b) every sentinel floor resolves, (c) every sentinel the tree refutes is
REDISCOVERED as refuted by the derivation above, (d) the `prop-body` keystone gates are
rediscovered, (e) every sentinel BUNDLE is rediscovered as a floor-carrying structure, and
(f) all twelve `antiFloor` `FloorRatchetSpecimens` classify exactly as documented, and (g) the
DERIVED refuted inline-injectivity signature set is non-empty and its five specimens split exactly
as documented. It shares (b)-(d) with `#floor_census` so the two instruments cannot drift apart.

(e) and (f) are the B1/B2/B3/B4 teeth's own self-check. A fixpoint that stops propagating through
fields, or an exemption predicate that degenerates in either direction, is INVISIBLE from a green
build — the surface just reads lower, which is indistinguishable from progress. Both now fail the
root build instead.

## The RATCHET
The ~1650 existing carriers cannot be ported today, so the gate compares against a checked-in
baseline of grandfathered declaration NAMES (`FloorRatchetBaseline.grandfathered`).
  * a carrier NOT in the baseline → **build error**. This is the accrual stop.
  * a baseline name that is no longer a carrier → reported as SLACK, never an error.
LOWERING is easy and mechanical, and runs against a GREEN tree:
`#floor_ratchet_emit "…/FloorRatchetBaseline.lean"` rewrites the baseline as
`baseline ∩ current`, so it can only ever REMOVE names. Run it after a port to bank the win.

RAISING is deliberate and manual: paste the names the failing gate prints into the baseline's
`manual` array. That asymmetry is not decoration — it falls out of a fact about lake. A gate
failure IS an elaboration error in `Dregg2.lean`, and `lean` writes NO olean for a module that
errors, so at exactly the moment you would want to re-emit, `import Dregg2` either cannot
resolve or silently resolves to the LAST GREEN olean and reports a surface that predates your
change. Pasting needs no environment, no build, and shows up as added lines in review.
(`#floor_ratchet_emit!` still exists, but only to re-bootstrap the WHOLE baseline on a green
tree — it is not the way to launder one violation, and it cannot be run while the gate is red.)

This tool only GATES. It proves nothing: a clean run means "no new declaration took a
provably-false hypothesis", not that the surviving ~1650 are sound.
-/
import Lean
import Dregg2.Verify.FloorCensus
import Dregg2.Verify.FloorRatchetBaseline
import Dregg2.Verify.FloorRatchetBaselineInline
import Dregg2.Verify.InjSpelling

set_option autoImplicit false
-- `surface` is one long `do` block and the do-elaborator recurses once per statement; the
-- honest-floor derivation put it near the default 512. Same budget note as `Verify/FloorCensus`.
set_option maxRecDepth 8000

namespace Dregg2.Verify.FloorRatchet

open Lean Meta Elab Command
open Dregg2.Verify.FloorCensus
  (ourModule moduleOf isInternalName headConst? notArg? injShape injShapeAnd
   sentinelFloors sentinelPropBody negWitnesses posWitnesses)

/-- The marker constant `Dregg2.Verify.FloorPole.HonestHypothesis`, named by raw `Name` rather
than imported: `Verify/FloorPole` is imported by the TREE (next to the floors it describes) and
this module is imported by the root, so a real import here would be a cycle. Everything else in
this file resolves its subjects out of the environment the same way. -/
def honestMarker : Name := `Dregg2.Verify.FloorPole.HonestHypothesis

/-- FAIL-CLOSED scale gate: whole-tree is ~915k constants. Below this the environment is
partial and every count reads low — which is indistinguishable from progress. -/
def minConstants : Nat := 500000

/-- Compiler-generated companions with no source token of their own. Dropped from the scan:
their parent declaration always carries the same floor and is always caught, so keeping them
would only inflate the baseline and churn it on every unrelated structure edit.

⚑ `mk` and projections are deliberately NOT here. A structure FIELD typed at a floor is the
BUNDLE class — `Poseidon2Tree.spongeCR`, `Compress2.compress1CR`, `PortalBundle.cellLeafInj` —
and it is the one shape where the floor has no argument position to be per-instance at. It
must stay gated. -/
def isGeneratedCompanion (n : Name) : Bool :=
  match n with
  | .str _ s =>
    s == "casesOn" || s == "recOn" || s == "rec" || s == "below" || s == "brecOn"
      || s == "ibelow" || s == "binductionOn" || s == "noConfusion" || s == "noConfusionType"
      || s == "ctorIdx" || s == "toCtorIdx" || s == "sizeOf_spec" || s == "injEq"
      || s == "eq_def" || s == "induct" || s == "fun_cases" || s.startsWith "match_"
      || s.startsWith "proof_" || (s.startsWith "eq_" && (s.drop 3).all Char.isDigit)
  | _ => false

/-- SENTINEL BUNDLES: structures the joint fixpoint must rediscover as floor-carrying. A fixpoint
that stops propagating through structure FIELDS reports a smaller surface and passes — which is
exactly what B3 exploited — so these fail the build closed instead.

`CommitSurface` is the worst of them (four refuted floors as fields, reached by 409 declarations);
`Poseidon2RealizedSponge` is the one the original probe rode in on; `ClosureReadouts`,
`ClosureReadoutsLive` and `StateDecodeLog` are TRANSITIVE (their floor arrives through fields of
other bundles / floor-carrying `Prop` defs), so they pin the fixpoint's CLOSURE and not just its
first step.

⚑ A name here can fail closed for the GOOD reason: the bundle got PORTED, its floor field deleted,
and it is correctly no longer floor-carrying. That is the ratchet noticing a win, and the fix is to
delete the line in the same commit as the port. `DeployedCapTree.CapHashScheme` was on this list
for exactly one afternoon before a co-tenant lane shed its `chipCR : Compress1CR` field
(`Circuit/CapHashBundleCutoverCheck.lean`) and re-inhabited it with `deployedCapHashScheme`, whose
own chip REFUTES the deleted field — so keep the list to bundles too big to fall by accident. -/
def sentinelBundles : List Name :=
  [ `Dregg2.Circuit.CircuitSoundness.CommitSurface
  , `Dregg2.Circuit.Poseidon2Binding.Poseidon2RealizedSponge
  , `Dregg2.Circuit.ClosureLog.StateDecodeLog
  , `Dregg2.Circuit.ClosureFanoutGenuine.ClosureReadouts
  , `Dregg2.Circuit.ClosureReadoutsRealizable.ClosureReadoutsLive ]

/-- The `antiFloor` SELF-TEST specimens and their required verdicts (`true` = must be exempt).
Each name is a `Prop`-valued def in `Dregg2.Verify.FloorRatchetSpecimens` whose VALUE is a
declaration TYPE; `surface` classifies the value and hard-errors if the verdict moved.

The first eight are the B1/B2/B3/B4 record: they were all EXEMPT under some earlier spelling of the
rule and each one is a laundering route that shipped. The last four pin the POSITION rule — that a
floor MENTIONED in a claim is not a floor ASSUMED — at both of its edges. -/
def specimenVerdicts : List (Name × Bool) :=
  [ (`Dregg2.Verify.FloorRatchetSpecimens.specRefutation, true)
  , (`Dregg2.Verify.FloorRatchetSpecimens.specRefutationManyHyp, true)
  , (`Dregg2.Verify.FloorRatchetSpecimens.specB1NegationLaundry, false)
  , (`Dregg2.Verify.FloorRatchetSpecimens.specB2FalseLaundry, false)
  , (`Dregg2.Verify.FloorRatchetSpecimens.specB3BundleLaundry, false)
  , (`Dregg2.Verify.FloorRatchetSpecimens.specB4UncurriedShape, false)
  , (`Dregg2.Verify.FloorRatchetSpecimens.specB4BinderOrderLaundry, false)
  , (`Dregg2.Verify.FloorRatchetSpecimens.specB4NegOtherFloorReordered, false)
  -- the POSITION rule (2026-07-27): a floor MENTIONED in a claim is not a floor ASSUMED
  , (`Dregg2.Verify.FloorRatchetSpecimens.specSatisfiabilityWitness, true)
  , (`Dregg2.Verify.FloorRatchetSpecimens.specPoleInConjunct, true)
  , (`Dregg2.Verify.FloorRatchetSpecimens.specClaimBuriedArrow, false)
  , (`Dregg2.Verify.FloorRatchetSpecimens.specIffLaundry, false) ]

/-- The INLINE-INJECTIVITY SELF-TEST specimens and their required verdicts (`true` = must be
GATED). The split this pins is the one thing about the inline tooth that can go wrong invisibly:

  * degenerate toward GATED and every `Function.Injective` assumption in the tree becomes a build
    error, including the genuinely true ones (a widening encoding, a coordinate embedding, a
    parametric `β → ℤ` with `β` a type variable). A gate that noisy gets turned off, and then
    there is no gate.
  * degenerate toward EXEMPT and the residual comes back: a refuted floor spelled
    `Function.Injective f` instead of `Poseidon2SpongeCR f`, for free.

Both read as a green build with a different number, so both are asserted on every run. -/
def injSpecimenVerdicts : List (Name × Bool) :=
  [ (`Dregg2.Verify.FloorRatchetSpecimens.specInjSpelledDeployedFloor, true)
  , (`Dregg2.Verify.FloorRatchetSpecimens.specInjSpelledWholeFunctionDigest, true)
  , (`Dregg2.Verify.FloorRatchetSpecimens.specInjWideningEncoding, false)
  , (`Dregg2.Verify.FloorRatchetSpecimens.specInjParametricComponent, false)
  , (`Dregg2.Verify.FloorRatchetSpecimens.specInjRefutationOfInline, false) ]

/-- The specimens are the instrument's own fixtures, not tree content: excluded from the carrier
surface so they never occupy lines in a baseline whose only healthy direction is shorter. -/
def specimens : NameSet :=
  injSpecimenVerdicts.foldl (fun a (n, _) => a.insert n)
    (specimenVerdicts.foldl (fun a (n, _) => a.insert n) {})

/-- A CLAIM position, scanned deeply. Floor content in a positive claim (`theorem sat : F good`)
assumes nothing — the theorem does not become vacuous if `F` is false, it becomes UNPROVABLE. But
an implication buried inside a claim (`∃ p, F h → p = q`, `Nonempty (F h → C)`) is an assumption
wearing a claim's clothes, so every `∀`/`→` DOMAIN anywhere under here still counts.

`hidden` — floor-carrying `Prop` defs and floor BUNDLES — counts wherever it appears, claim
position included. That asymmetry is the whole point of the split: `descriptorRefines d` UNFOLDS to
`Poseidon2SpongeCR hash → …`, so CONCLUDING one is concluding an implication whose antecedent is
refuted, and that is the vacuity itself rather than a claim about it. A floor NAME has no such
antecedent hiding in it. -/
partial def claimAssumes (floorC hidden : Name → Bool) (e : Expr) : Bool :=
  match e with
  | .forallE _ d b _ =>
    d.foldConsts false (fun c a => a || floorC c || hidden c)
      || claimAssumes floorC hidden b
  | .lam _ d b _ => claimAssumes floorC hidden d || claimAssumes floorC hidden b
  | .app f a => claimAssumes floorC hidden f || claimAssumes floorC hidden a
  | .letE _ t v b _ =>
    claimAssumes floorC hidden t || claimAssumes floorC hidden v || claimAssumes floorC hidden b
  | .mdata _ b => claimAssumes floorC hidden b
  | .proj _ _ b => claimAssumes floorC hidden b
  | .const c _ => hidden c
  | _ => false

/-- **Is this declaration's claim CONTINGENT on floor content?** The carrier test, and the
complement of the anti-floor exemption below.

Reading the type as `∀ x₁:A₁ … xₙ:Aₙ, C`: any `Aᵢ` carrying floor content is an assumption, whatever
its position in the telescope (that is B4 — binder ORDER is a spelling the author controls and is
never consulted). Then `C` is decomposed by the connectives that actually carry a hypothesis
inward:

  * `¬ p` — NOT contingent. Proving a negation is refuting `p`, not assuming it. This is what makes
    a refutability pole free, in EVERY spelling: `¬ F c`, `A ∧ ¬ F c`, `∃ x, ¬ F x`.
  * `∧` / `∨` / `∃` — recurse; a floor's model or counterexample is routinely stated inside one,
    and `crossScheme_fails_on_weak_schemes` had to be written around this to keep the root green.
  * `↔` — BOTH sides are antecedents of each other, so both are assumption positions. `F f ↔ secure
    f` has a vacuous forward direction and must not be exempt.
  * anything else — `claimAssumes`, which still catches an implication buried in a claim.

⚑ The only declarations this exempts that the old rule gated are ones whose floor mentions are ALL
in claim position: satisfiability witnesses, poles stated in a conjunct or an `∃`, bridge claims.
None of them is vacuous under any reading, and none of them can be used to launder a guarantee —
a guarantee CONTINGENT on a floor has that floor in an antecedent by definition, and every
antecedent position above is checked. -/
partial def assumesFloorContent (floorC hidden : Name → Bool) (e : Expr) : Bool :=
  match e with
  | .forallE _ d b _ =>
    d.foldConsts false (fun c a => a || floorC c || hidden c)
      || assumesFloorContent floorC hidden b
  | .mdata _ b => assumesFloorContent floorC hidden b
  | .app (.const ``Not _) _ => false
  | .app (.app (.const ``And _) l) r =>
    assumesFloorContent floorC hidden l || assumesFloorContent floorC hidden r
  | .app (.app (.const ``Or _) l) r =>
    assumesFloorContent floorC hidden l || assumesFloorContent floorC hidden r
  | e =>
    if e.isAppOfArity ``Exists 2 then
      match e.getAppArgs[1]! with
      | .lam _ _ b _ => assumesFloorContent floorC hidden b
      | _ => claimAssumes floorC hidden e
    else if e.isAppOfArity ``Iff 2 then
      let args := e.getAppArgs
      args[0]!.foldConsts false (fun c a => a || floorC c || hidden c)
        || args[1]!.foldConsts false (fun c a => a || floorC c || hidden c)
    else claimAssumes floorC hidden e

/-- ANTI-floor content, exempt from the gate: a declaration that REFUTES floor content and
ASSUMES none. Precisely — and read the ⚑ block at the bottom before this line, which records how
the second condition was dropped in 2026-07-27 — the rule USED to be, over `∀ x₁:A₁ … xₙ:Aₙ, C`:

  **NO `Aᵢ` carries floor content, AND `C` is `¬ F …` for floor content `F` (or `C = False`).**

Two conditions, and the FIRST is the one that does the work — so much so that the second turned
out to be doing only harm, and is gone. "Concludes a negation" is a
conclusion SHAPE, not a refutation test; what makes a declaration a refutation is that it reaches
that conclusion WITHOUT ASSUMING the thing it refutes. A declaration that assumes `Floor` and
concludes `False` is not a refutation — "if this false thing were true, anything follows" is the
DEFINITION of vacuity — and it says exactly as little as one that assumes `Floor` and concludes an
equation.

⚑ **BINDER ORDER IS NOW IRRELEVANT, WHICH IS THE WHOLE POINT.** The rule this replaced exempted
`C = False` when the floor was the INNERMOST binder, on the reasoning that `Γ → F → False` IS
`Γ → ¬ F` by definition. That is true, and it was still a hole, because ORDER IS A SPELLING THE
AUTHOR CONTROLS. The same theorem, hypotheses swapped, changed verdict:

    theorem consensus_safe_under_floor (hCR : Poseidon2SpongeCR s) (hFork : …) : False   -- GATED
    theorem consensus_safe_under_floor (hFork : …) (hCR : Poseidon2SpongeCR s) : False   -- exempt

The gate's own error text used to coach the swap ("move the floor binder LAST … it costs no proof
work"). An adversarial probe took it and the gate said OK. **B4** is that hole, and what was
sitting on it when it closed was not hypothetical — it was two theorems that read as the deployed
system's post-quantum security:

  * `Dregg2.Crypto.HermineMSIS.no_forgery_under_msis` — nine hypotheses describing two forked
    Hermine forgeries, then `(hard : MSISHard A …) : False`. It reads "the deployed threshold
    signature cannot be forged". `Lattice.MSISHard` is a floor THIS TREE REFUTES
    (`CryptoFloorTeeth.not_msisHard_of_short_ball`: at a compressing `A` the short ball outnumbers
    the codomain, so a short nonzero kernel vector EXISTS by pigeonhole).
  * `Dregg2.Crypto.HermineSelfTargetMSIS.no_forgery_under_msis_selftarget` — the same claim on the
    SelfTargetMSIS route, the one `AdvCalculus.pq_euf_cma_grounded_in_msis` and
    `HermineHybrid.hermine_hybrid_survives_classical_break` build the hybrid keystone on.

Both are grandfathered by NAME in the baseline now, which is the point: a reader of the baseline
can see them. Under the old rule they were invisible — not grandfathered, EXEMPT, indistinguishable
from `poseidon2SpongeCR_false_babyBear`.

⚑ WHAT IT COSTS, stated plainly. Exactly ONE spelling of a genuine refutation is no longer free:
the UNCURRIED `Γ → F → False`. Three declarations in the tree used it and all three were restated
as `¬ F …` in the same commit, definitionally equal and zero proof work
(`compress1CR_field_uninhabitable_babyBear`, `deployedCapHashScheme_field_would_be_uninhabitable`,
`residueBlind_refutes_spongeCR`). The 128 refutations already spelled `¬ F …` were untouched.

That residual is the FAIL-CLOSED direction, and it is why this is a decision procedure and not a
discipline. The old rule's spelling-dependence let a VACUOUS claim out; this one's can only make a
GENUINE refutation trip the gate, where the author sees the error, restates in one line, and moves
on. A gate may cost its user a restatement; it may not launder a security claim.

The `C = False` branch is kept for completeness and is now SUBSUMED: the type is
`∀ x₁:A₁ … xₙ:Aₙ, False`, so every subterm is a binder domain, and if none carries floor content
the declaration is not a carrier by any route. Nothing reaches it that the carrier scan would
otherwise have flagged. It stays because it makes the rule statable in one sentence and because
removing it would be a silent behaviour change the day a conclusion grows a non-binder position.

Read off the TYPE syntactically — no naming convention, no proof term, no telescope
instantiation. Keeping it type-only matters: a gate that read proof terms would classify the same
statement differently depending on how it was proved.

⚑ **THE CONCLUSION SHAPE STOPPED BEING A WHITELIST (2026-07-27).** The rule above is stated as two
conditions, and it was IMPLEMENTED as "the conclusion is one of two blessed shapes, AND no binder
carries floor content". The first condition was doing work it should never have done. A declaration
whose only floor mention is in a POSITIVE claim — `theorem sat : Poseidon2SpongeCR refSponge`, the
SATISFIABLE pole; `theorem t : ∃ f, F f`, the same thing existentially; `forked_strand_not_forkFree
: forkedLace = … ∧ ¬ StrandForkFree forkedLace 9`, a refutability pole one conjunct off the blessed
spelling — assumes NOTHING and is not vacuous under any reading, and all three were CARRIERS. The
tree paid for it: `34854bf62` deleted a satisfiability witness partly because naming a floor in a
conclusion "is a gate carrier for no benefit", which is the gate teaching authors to delete their
anti-vacuity content.

So the test is now the SECOND condition alone, applied to every position, by
`assumesFloorContent`: **a declaration is a carrier exactly when its claim is CONTINGENT on floor
content.** Positive claims about a floor are not; implications buried anywhere in the conclusion
still are. `antiFloor` survives as its complement so the eight specimen verdicts — the record of
what B1/B2/B3/B4 cost — keep testing the LIVE predicate rather than a retired one. -/
def antiFloor (floorC hidden : Name → Bool) (ty : Expr) : Bool :=
  !assumesFloorContent floorC hidden ty

/-- A declaration that violates (or is grandfathered under) the ratchet. -/
structure Carrier where
  name  : Name
  floor : Name          -- the refuted floor, `prop-body` def, or floor BUNDLE it carries
  cls   : String        -- binder | prop-body | propdef-user | bundle | bundle-user | inj-spelled
  deriving Inhabited

structure Surface where
  floors    : Array Name           -- refuted floors, DERIVED from the environment
  honest    : Array (Name × Name × Name × Name)
    -- floors DECLARED honest and CHECKED as such: (floor, declaration, ¬-pole, model)
  propBody  : Array Name           -- Prop defs carrying a floor in their BODY (joint fixpoint)
  bundles   : Array Name           -- structures with a floor-carrying FIELD (joint fixpoint)
  carriers  : Array Carrier        -- sorted by name
  injSigs   : Array String         -- REFUTED inline `Function.Injective` signatures (derived)
  shapeLeak : Nat                  -- inline-injectivity sites at UNREFUTED signatures (exempt)
  injResid  : Array (String × Nat) -- those signatures, with site counts — the EXEMPT half, named
  total     : Nat                  -- constants in the environment

/-- Names in our own trees, non-internal, plus the total constant count for the scale gate.

Ours-ness is decided by MODULE INDEX against a mask computed once over `moduleNames`, not by
`moduleOf` per name: the per-name form costs a `Name.toString` on each of ~915k constants and
this runs on every root build.

⚑ A constant with NO module index belongs to the module being elaborated RIGHT NOW, and is
counted as OURS. `#floor_census`'s `moduleOf` maps that case to `` `«current» ``, which
`ourModule` rejects — so a violation introduced in the same file as the check would be
invisible to it. The gate must see the file it is standing in. -/
def ourNames (env : Environment) : Array Name × Nat := Id.run do
  let mut allNames : Array Name := env.constants.foldStage2 (fun acc n _ => acc.push n) #[]
  allNames := env.constants.map₁.fold (fun acc n _ => acc.push n) allNames
  let mask : Array Bool := env.header.moduleNames.map ourModule
  let mut ours : Array Name := #[]
  for nm in allNames do
    let mine :=
      match env.getModuleIdxFor? nm with
      | some idx => mask.getD idx.toNat false
      | none     => true
    unless mine do continue
    if isInternalName nm then continue
    ours := ours.push nm
  return (ours, allNames.size)

/-- Syntactic `Prop`-valued test on a TYPE (`∀ …, Prop`). No metavariables, no telescope. -/
def isPropValued (ty : Expr) : Bool := ty.getForallBody == .sort .zero

/-- Compute the whole gated surface from the imported environment. FAILS CLOSED. -/
def surface : MetaM Surface := do
  let env ← getEnv
  let (ours, total) := ourNames env
  -- (a) whole-tree scale
  if total < minConstants then
    throwError "FLOOR-RATCHET FAIL-CLOSED: only {total} constants in the environment \
      (whole-tree is ~915k). Partial import — a ratchet run here would under-count carriers \
      and PASS a build that accrues. Refusing to report."
  -- (b) sentinel floors resolve
  for (f, _) in sentinelFloors do
    unless env.contains f do
      throwError "FLOOR-RATCHET FAIL-CLOSED: sentinel floor {f} is not in the environment. \
        Partial import or a renamed floor — refusing to gate against a smaller floor set."

  -- ===== refutation witnesses: theorems concluding `¬ H …` (syntactic, no telescope) =====
  let mut witnessOf : Std.HashMap Name Name := {}
  for nm in ours do
    let some ci := env.find? nm | continue
    let .thmInfo _ := ci | continue
    if let some arg := notArg? ci.type.getForallBody then
      if let some h := headConst? arg then
        if !witnessOf.contains h then witnessOf := witnessOf.insert h nm

  -- ===== a refuted FLOOR is a refuted, injectivity-shaped (or sentinel-named) Prop def ====
  let namedSet : NameSet := sentinelFloors.foldl (fun a (f, _) => a.insert f) {}
  let mut floors : NameSet := {}
  let mut floorArr : Array Name := #[]
  for (h, _) in witnessOf.toList do
    let some ci := env.find? h | continue
    -- ⚑ LOAD-BEARING: the refuted head must be OUR def. `Function.Injective` is itself
    -- injectivity-SHAPED, so a single in-tree `theorem … : ¬ Function.Injective f` would
    -- otherwise promote Mathlib's `Function.Injective` to a refuted floor and make every
    -- injectivity hypothesis anywhere a violation.
    unless ourModule (moduleOf env h) do continue
    unless isPropValued ci.type do continue
    let shaped ←
      if namedSet.contains h then pure true
      else match ci with
        | .defnInfo di =>
          try
            forallTelescope di.type fun xs _ => do
              let b := di.value.beta xs
              if ← injShape b then return true else injShapeAnd b
          catch _ => pure false
        | _ => pure false
    if shaped then
      floors := floors.insert h
      floorArr := floorArr.push h
  -- (c) every sentinel the tree refutes must be REDISCOVERED as refuted
  for (f, needRefut) in sentinelFloors do
    if needRefut && !floors.contains f then
      throwError "FLOOR-RATCHET FAIL-CLOSED: sentinel floor {f} has no visible in-tree \
        ¬-conclusion refutation. Partial import (the refutation module is missing) or a \
        genuine regression — either way the gate would defend a smaller floor set than the \
        tree actually refutes. Refusing to run."

  -- ===== HONEST floors: the refutability pole stops costing a red root (`Verify/FloorPole`) ====
  -- A `¬ F c` at a DEGENERATE instance and a `¬ F deployed` have the same type shape, so the
  -- derivation above promotes both and gates every consumer of both. For a floor that is
  -- satisfiable AND refutable that is backwards: completing the doctrine's own check turns the
  -- floor's honest consumers into build errors, which is the measured reason 5 of 8 unrefuted
  -- floors have no pole and one author deliberately mis-spelled the one they wrote (`ae37dd523`).
  -- A floor leaves the set ONLY by an explicit in-tree declaration that passes all four checks
  -- below; every failure is a hard error naming the missing pole, never a silent drop.
  let mut honestDecl : Std.HashMap Name Name := {}
  for nm in ours do
    let some ci := env.find? nm | continue
    let b := ci.type.getForallBody
    if b.isAppOfArity honestMarker 1 then
      if let some h := headConst? b.appArg! then
        if !honestDecl.contains h then honestDecl := honestDecl.insert h nm
  let mut honest : NameSet := {}
  let mut honestRec : Array (Name × Name × Name × Name) := #[]
  unless honestDecl.isEmpty do
    let honestSet : NameSet := honestDecl.fold (fun a f _ => a.insert f) {}
    let mut negClosed : Std.HashMap Name Name := {}
    let mut negParam : Std.HashMap Name Name := {}
    let mut satWit : Std.HashMap Name Name := {}
    for nm in ours do
      let some ci := env.find? nm | continue
      let .thmInfo _ := ci | continue
      unless ci.type.getUsedConstants.any honestSet.contains do continue
      let (negs, pos) ← forallTelescope ci.type fun xs body => do
        let negs := negWitnesses honestSet body #[]
        -- A MODEL must be proved from data alone: any propositional binder makes it a CONDITIONAL
        -- discharge, and a conditional model is not evidence that the obligation is inhabitable.
        let mut condHyp := false
        for x in xs do
          if ← Meta.isProp (← inferType x) then condHyp := true
        return (negs, if condHyp then #[] else posWitnesses honestSet false body #[])
      for (f, closed) in negs do
        if closed && !negClosed.contains f then negClosed := negClosed.insert f nm
        if !closed && !negParam.contains f then negParam := negParam.insert f nm
      for (f, parametric) in pos do
        if !parametric && !satWit.contains f then satWit := satWit.insert f nm
    for (f, decl) in honestDecl.toList do
      -- (1) NEVER a named sentinel. These are the deployed-parameter crypto floors the campaign
      -- exists to delete, and "is the refuted instance the deployed one" is exactly the semantic
      -- question no type-shape check can answer — so for them the answer is hard-wired to NO.
      if sentinelFloors.any (·.1 == f) then
        throwError "FLOOR-RATCHET FAIL-CLOSED: {decl} declares the SENTINEL floor {f} honest. \
          A named sentinel can never be declared honest — it is a deployed-parameter crypto floor \
          this tree proves false, and the fail-closed sentinel check would refuse the run anyway. \
          Port its consumers or refute it; do not relabel it."
      unless floors.contains f do
        throwError "FLOOR-RATCHET FAIL-CLOSED: {decl} declares {f} honest, but {f} is not a \
          refuted floor in this environment — nothing promotes it and the declaration gates \
          nothing. Either it is not injectivity-shaped/sentinel-named (so it was never a \
          candidate), or its refutability pole is missing or was deleted. The honest state for \
          such a floor is UNREFUTED, which the census already reports. Delete the declaration, or \
          write the pole it is claiming exists."
      -- (4) a PARAMETRIC refutation says the floor fails at EVERY instance. That is not
      -- "refutable", that is FALSE, and its consumers are vacuous however they are labelled.
      if let some pw := negParam.get? f then
        throwError "FLOOR-RATCHET FAIL-CLOSED: {decl} declares {f} honest, but {pw} refutes it \
          PARAMETRICALLY — for arbitrary arguments, not at one degenerate instance. A floor false \
          everywhere is not an honest hypothesis with a counterexample; it is a false hypothesis, \
          and every consumer of it is vacuous. Port them."
      -- (2) the refutability pole it is claiming
      let some nw := negClosed.get? f
        | throwError "FLOOR-RATCHET FAIL-CLOSED: {decl} declares {f} honest with no REFUTABILITY \
            pole in the environment: no theorem proves `¬ {f} …` at a closed instance. Declaring \
            a floor honest is declaring that both poles exist; write the counterexample."
      -- (3) the model. A refutation with no inhabitant is a vacuity bomb, not an honest
      -- obligation — the finding `ae37dd523` landed against `CrossSchemeSameOpening`.
      let some sw := satWit.get? f
        | throwError "FLOOR-RATCHET FAIL-CLOSED: {decl} declares {f} honest with no SATISFIABILITY \
            witness in the environment: nothing CLAIMS `{f} …` at an exhibited instance while \
            assuming no floor content. An obligation with consumers and no inhabitant is \
            indistinguishable from a vacuity bomb — every consumer is true for free. Exhibit a \
            model, at deployed shape and not at an escape hatch."
      honest := honest.insert f
      honestRec := honestRec.push (f, decl, nw, sw)
  unless honest.isEmpty do
    floorArr := floorArr.filter (fun f => !honest.contains f)
    floors := floorArr.foldl (·.insert ·) {}

  -- ===== the JOINT `prop-body` × `bundle` fixpoint =====
  -- `prop-body`: `def … : Prop := Floor … → …` — the floor is in the def's VALUE, so its users
  -- carry no floor binder.
  -- `bundle`:    `structure S where … (fld : Floor …)` — the floor is a FIELD, so no inhabitant
  -- of `S` exists at deployed parameters and a hypothesis `(s : S)` is exactly as vacuous as a
  -- floor binder. Read off the CONSTRUCTOR's type, which spans the structure's parameters and
  -- every field; the `c != nm` guard keeps a recursive structure from triggering on itself.
  -- The two are closed TOGETHER: a `Prop` def can mention a bundle and a field can be typed at a
  -- `Prop` def or at another bundle, so separate fixpoints would each miss the other's step.
  let mut propDefs : Array (Name × Array Name) := #[]
  for nm in ours do
    let some ci := env.find? nm | continue
    let .defnInfo di := ci | continue
    if floors.contains nm then continue
    -- The `antiFloor` specimens are Prop-valued defs whose BODIES are floor-carrying by design.
    -- They are the instrument's fixtures; letting them into the fixpoint would put eight entries
    -- in the gate's own report of what the TREE carries.
    if specimens.contains nm then continue
    unless isPropValued di.type do continue
    propDefs := propDefs.push (nm, di.value.getUsedConstants)
  let mut structDefs : Array (Name × Array Name) := #[]
  for nm in ours do
    let some ci := env.find? nm | continue
    let .inductInfo ii := ci | continue
    unless isStructure env nm do continue
    let mut used : Array Name := #[]
    for c in ii.ctors do
      if let some cci := env.find? c then used := used ++ cci.type.getUsedConstants
    structDefs := structDefs.push (nm, used)
  let mut pb : NameSet := {}
  let mut pbArr : Array Name := #[]
  let mut bn : NameSet := {}
  let mut bnArr : Array Name := #[]
  let mut iters := 0
  let mut changed := true
  while changed && iters < 100 do
    changed := false
    iters := iters + 1
    for (nm, used) in propDefs do
      if pb.contains nm then continue
      if used.any (fun c => floors.contains c || pb.contains c || bn.contains c) then
        pb := pb.insert nm
        pbArr := pbArr.push nm
        changed := true
    for (nm, used) in structDefs do
      if bn.contains nm then continue
      if used.any (fun c =>
           c != nm && (floors.contains c || pb.contains c || bn.contains c)) then
        bn := bn.insert nm
        bnArr := bnArr.push nm
        changed := true
  if iters >= 100 then
    throwError "FLOOR-RATCHET FAIL-CLOSED: the prop-body × bundle fixpoint did not converge."
  -- (d) the load-bearing prop-body keystone gates must be rediscovered
  for f in sentinelPropBody do
    unless pb.contains f do
      throwError "FLOOR-RATCHET FAIL-CLOSED: prop-body sentinel {f} was not discovered as a \
        floor-carrying Prop def. The ~250 carriers that hang off it invisibly would all pass \
        the gate. Refusing to run."
  -- (e) every sentinel BUNDLE must be rediscovered — the B3 tooth's own self-check
  for s in sentinelBundles do
    unless env.contains s do
      throwError "FLOOR-RATCHET FAIL-CLOSED: bundle sentinel {s} is not in the environment. \
        Partial import or a renamed structure — refusing to gate against a smaller bundle set."
    unless bn.contains s do
      throwError "FLOOR-RATCHET FAIL-CLOSED: bundle sentinel {s} was not discovered as a \
        floor-carrying STRUCTURE. Two ways this happens, and they need opposite responses.\n\
        (a) THE FIXPOINT BROKE — it has stopped propagating through structure FIELDS, which is \
        exactly the B3 bypass: every declaration taking {s} as a hypothesis would pass the gate \
        while being as vacuous as a floor binder. Fix the fixpoint.\n\
        (b) THE BUNDLE WAS PORTED — its floor field is deleted and it is correctly no longer \
        floor-carrying. That is a WIN; delete this name from `sentinelBundles` in the same \
        commit as the port, and re-emit the baseline to bank the carriers that fell with it.\n\
        Check which by reading the structure's fields. Refusing to run until then."
  -- The SPLIT the position rule needs: a floor NAME assumes nothing in a claim position, a
  -- floor-carrying `Prop` def or BUNDLE assumes something wherever it appears (it UNFOLDS to an
  -- implication / has no inhabitant). See `assumesFloorContent`.
  let floorNames : Name → Bool := fun c => floors.contains c
  let hiddenContent : Name → Bool := fun c => pb.contains c || bn.contains c
  -- (f) the exemption predicate must still classify its eight specimens as documented. A rule
  -- that degenerates to "everything is a refutation" exempts the tree and passes forever; one
  -- that degenerates the other way makes writing a refutation a build error. Neither is visible
  -- from a green build, so both are asserted here on every run.
  for (spec, wantExempt) in specimenVerdicts do
    let some sci := env.find? spec
      | throwError "FLOOR-RATCHET FAIL-CLOSED: antiFloor specimen {spec} is not in the \
          environment. `Dregg2/Verify/FloorRatchetSpecimens.lean` is unimported or renamed, so \
          the exemption predicate is running unchecked. Refusing to run."
    let .defnInfo sdi := sci
      | throwError "FLOOR-RATCHET FAIL-CLOSED: antiFloor specimen {spec} is not a def."
    let got := antiFloor floorNames hiddenContent sdi.value
    unless got == wantExempt do
      throwError "FLOOR-RATCHET FAIL-CLOSED: antiFloor specimen {spec} classified \
        {(if got then "EXEMPT" else "GATED")}, expected \
        {(if wantExempt then "EXEMPT" else "GATED")}. \
        The anti-floor exemption has moved. If it now exempts too much, the gate is a laundry \
        (that is B1/B2: `False` and `¬ …` are conclusion SHAPES, not refutation tests). If too \
        little, writing a refutation has become a build error. Fix the predicate, or change the \
        specimen's expected verdict IN THE DIFF and say why."

  -- ===== the INLINE-SPELLED refuted injectivity signatures (derived; see `Verify/InjSpelling`) =====
  -- `Poseidon2SpongeCR f` IS `Function.Injective f` at `f : List ℤ → ℤ`, so until this landed the
  -- SAME hypothesis cost a build error under one spelling and nothing under the other.
  let injSigs ← InjSpelling.signatures ours floorArr
  let injMemo ← IO.mkRef ({} : Std.HashMap String (Option Name))
  -- (g) the inline tooth's own fail-closed check. A signature set that silently empties reports a
  -- smaller surface and PASSES, which is indistinguishable from a port — the same failure mode
  -- (e) exists for. `List ℤ → ℤ` must be there (Source A: it is `Poseidon2SpongeCR`'s own
  -- signature, and the tree refutes that floor) and so must at least one Source-B signature (a
  -- concrete type admitting NO injection at all).
  if injSigs.isEmpty then
    throwError "FLOOR-RATCHET FAIL-CLOSED: the refuted INLINE-injectivity signature set is EMPTY. \
      Either `Verify/InjSpelling.signatures` broke, or every `¬ Function.Injective` refutation \
      left the tree — either way every floor spelled `Function.Injective f` is ungated again, \
      which is the bypass this tooth closed. Refusing to run."
  for (spec, wantGated) in injSpecimenVerdicts do
    let some sci := env.find? spec
      | throwError "FLOOR-RATCHET FAIL-CLOSED: inline-injectivity specimen {spec} is not in the \
          environment. `Dregg2/Verify/FloorRatchetSpecimens.lean` is unimported or renamed, so \
          the inline classifier is running unchecked. Refusing to run."
    let .defnInfo sdi := sci
      | throwError "FLOOR-RATCHET FAIL-CLOSED: inline-injectivity specimen {spec} is not a def."
    let got := (← InjSpelling.classify injSigs injMemo sdi.value).isSome
    unless got == wantGated do
      throwError "FLOOR-RATCHET FAIL-CLOSED: inline-injectivity specimen {spec} classified \
        {(if got then "GATED" else "EXEMPT")}, expected \
        {(if wantGated then "GATED" else "EXEMPT")}. \
        The inline split has moved. Too GATED and a legitimate injectivity assumption \
        (a widening encoding, a coordinate embedding, a parametric `β → ℤ`) is now a build error \
        — a noisy gate gets disabled, which is how a gate is lost entirely. Too EXEMPT and a \
        refuted floor spelled `Function.Injective f` walks through again. Fix the classifier, or \
        change the specimen's expected verdict IN THE DIFF and say why."
  -- ===== the carrier surface =====
  let mut carriers : Array Carrier := #[]
  let mut shapeLeak := 0
  let mut injResid : Std.HashMap String Nat := {}
  for nm in ours do
    if isGeneratedCompanion nm then continue
    if floors.contains nm then continue
    if specimens.contains nm then continue
    let some ci := env.find? nm | continue
    -- IDENTITY classes first: a floor-carrying `Prop` def / STRUCTURE is a carrier by what it IS,
    -- and its own type (`∀ …, Prop`, `Sort _`) mentions nothing.
    if pb.contains nm then
      carriers := carriers.push ⟨nm, nm, "prop-body"⟩
      continue
    if bn.contains nm then
      carriers := carriers.push ⟨nm, nm, "bundle"⟩
      continue
    -- ONE `foldConsts` pass, not three scans of a `getUsedConstants` array. This loop runs
    -- over every one of our declarations on EVERY root build, and `getUsedConstants` allocates
    -- and dedups a fresh `Array Name` per type before we ask it three questions; folding the
    -- constants answers all three with no intermediate array, which is strictly less work.
    --
    -- ⚑ NO SPEEDUP IS CLAIMED. Both forms were measured the same way (paired `import Dregg2`
    -- probes with and without the invocation, three runs each) and the difference is BURIED IN
    -- NOISE on a co-tenanted machine: 4-17s added for the array form, 14-35s for this one, with
    -- the spread inside each form larger than the gap between them. Loading ~920k constants
    -- dominates, and the OS page-cache state swamps everything else. What IS measured is the
    -- gate's total added cost, of order 10s on a root elaboration that already costs ~30s, and
    -- the fact that both forms return an identical surface (1586 carriers / 27 floors / 563
    -- shape-leaks) — which is a useful cross-check on this rewrite, and all it is.
    let (floorHit, pbHit, bnHit, injSeen) :=
      ci.type.foldConsts (none, none, none, false) fun c (fh, ph, bh, inj) =>
        ( if fh.isNone && floors.contains c then some c else fh
        , if ph.isNone && pb.contains c then some c else ph
        , if bh.isNone && bn.contains c then some c else bh
        , inj || c == ``Function.Injective )
    -- Cheap exit for the ~99% of declarations that mention no content at all, so the structural
    -- position walk below runs on the few thousand that do rather than on every declaration.
    if floorHit.isNone && pbHit.isNone && bnHit.isNone && !injSeen then continue
    -- ⚑ MENTIONING IS NOT ASSUMING. The named classes fire only when the claim is CONTINGENT on
    -- the content — see `assumesFloorContent`. A satisfiability witness, or a refutability pole in
    -- a conjunct or an `∃`, mentions a floor and assumes nothing, and was a carrier under the old
    -- whole-type test purely because the exemption keyed on TWO blessed conclusion shapes.
    let named? : Option (Name × String) :=
      if !assumesFloorContent floorNames hiddenContent ci.type then none
      else if let some f := floorHit then some (f, "binder")
      else if let some f := pbHit then some (f, "propdef-user")
      else if let some f := bnHit then some (f, "bundle-user")
      else none
    match named? with
    | some (f, cls) => carriers := carriers.push ⟨nm, f, cls⟩
    | none =>
      if injSeen then
        -- ⚑ THE INLINE SPELLING. A `Function.Injective f` HYPOTHESIS at a signature this tree
        -- refutes is the same vacuity as a named floor binder; at any other signature it may be
        -- perfectly true (a widening encoding, a constructor, a parametric `β → ℤ`) and gating it
        -- would be noise. The split is decided by `Verify/InjSpelling`, from in-tree refutations.
        -- It runs even for declarations the named classes exempt: `antiFloor` reads content BY
        -- NAME and `Function.Injective` is not one, so an inline-spelled refuted floor bound by a
        -- declaration that concludes `False` is the B1/B2 laundry one spelling over.
        match ← InjSpelling.classify injSigs injMemo ci.type with
        | some fl => carriers := carriers.push ⟨nm, fl, "inj-spelled"⟩
        | none =>
          shapeLeak := shapeLeak + 1
          for k in ← InjSpelling.residualKeys injSigs ci.type do
            injResid := injResid.insert k ((injResid.getD k 0) + 1)
  let sorted := carriers.qsort (fun a b => a.name.toString < b.name.toString)
  let residArr := injResid.toList.toArray.qsort (fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1))
  let sigKeys ← injSigs.mapM (fun s => do pure s!"{← InjSpelling.sigKey s.dom s.cod}  [{s.floor}]")
  return { floors := floorArr.qsort (fun a b => a.toString < b.toString)
           honest := honestRec
           propBody := pbArr, bundles := bnArr, carriers := sorted
           injSigs := sigKeys.qsort (fun a b => a < b), shapeLeak, injResid := residArr, total }

/-! ## The gate -/

/-- Compare the live surface against the checked-in baseline. New carriers are a hard error. -/
def check (baseline : Array String) : MetaM Unit := do
  let s ← surface
  let base : Std.HashSet String := baseline.foldl (fun a b => a.insert b) {}
  let cur : Std.HashSet String := s.carriers.foldl (fun a c => a.insert c.name.toString) {}
  let fresh := s.carriers.filter (fun c => !base.contains c.name.toString)
  let slack := baseline.filter (fun b => !cur.contains b)
  unless fresh.isEmpty do
    let env ← getEnv
    let shown := fresh.toList.take 40
    let body := String.intercalate "\n" (shown.map fun c =>
      s!"    {c.name}\n      floor: {c.floor}   class: {c.cls}   module: {moduleOf env c.name}")
    let more := if fresh.size > shown.length then
        s!"\n    … and {fresh.size - shown.length} more." else ""
    let paste := String.intercalate ",\n" (fresh.toList.map fun c => s!"  \"{c.name}\"")
    throwError "\n\
      ⚑ FLOOR-RATCHET: {fresh.size} NEW declaration(s) take a REFUTED floor as a hypothesis.\n\
      \n\
      A floor listed below is PROVED FALSE in this tree at deployed BabyBear parameters, so \
      every theorem assuming it is VACUOUS — it says nothing about the deployed system. The \
      campaign measured accrual outrunning removal ~1.2:1; this gate is the stop.\n\
      \n{body}{more}\n\
      \n\
      Three ways forward, in order of preference:\n\
      \n\
      1. PORT IT (what the campaign wants). Replace the floor hypothesis with a per-instance, \
         REFUTABLE side condition at the exact pair your proof feeds the floor — see \
         `Circuit/MapOpsColumnLayout.lean` (`pathCollFind` / `noPathColl_of_CR`) or \
         `Circuit/StateCommitLeafCutoverCheck.lean` for the worked shape. The old hypothesis \
         implies the new one, so the ported theorem is strictly STRONGER.\n\
      \n\
      2. STATE IT AS ANTI-FLOOR CONTENT — but SPELL IT AS A REFUTATION. Exempt means \"refutes \
         floor content and ASSUMES NONE\": conclusion `¬ Floor …`, and NO hypothesis carrying \
         floor content, in ANY position. ⚑ REORDERING WILL NOT HELP AND IS NOT WHAT TO DO. \
         Binder ORDER is not consulted — it is a spelling you control, and keying on it is \
         exactly the B4 hole this rule closed (`no_forgery_under_msis`, which reads as \"the \
         deployed signature cannot be forged\", was EXEMPT purely because its refuted `MSISHard` \
         binder happened to come last). A `False` conclusion is not enough either (B2), and \
         neither is a `¬ …` conclusion reached while assuming a floor (B1).\n\
         \n\
         If your declaration genuinely IS a refutation and you wrote it uncurried as \
         `… → Floor … → False`, restate it as `… : ¬ Floor …` and DELETE that last binder. The \
         two are definitionally equal, so the proof term is unchanged and it costs no proof \
         work — `residueBlind_refutes_spongeCR` and \
         `compress1CR_field_uninhabitable_babyBear` are the worked examples. If instead the \
         floor is a genuine PREMISE your conclusion needs, you are at case 1 or case 3, not \
         here.\n\
      \n\
      ⚑ IF THE FLOOR WAS SPELLED INLINE (class `inj-spelled`), the binder reads \
         `Function.Injective f` rather than a floor NAME, and it is the same hypothesis: the floor \
         named above is DEFINITIONALLY `Function.Injective` at your `f`'s type, or the tree holds \
         a theorem that NO function of that type is injective. Re-spelling it (either direction) \
         changes nothing and is not a fix. If `f`'s domain is a FUNCTION SPACE \
         (`CellId → AssetId → ℤ`, `Caps`, `BornEmptySideTables`, …) the assumption is not merely \
         false at BabyBear — it is a CARDINALITY impossibility (`Verify/InjSpelledFloors`), and \
         the repair is STRUCTURAL: digest the FINITE support actually touched (the \
         `accounts : Finset CellId` rows), never the whole function.\n\
      \n\
      ⚑ IF THE FLOOR ARRIVED THROUGH A STRUCTURE (class `bundle-user`), there is no binder to \
         move: a field is fixed for the life of the value with no argument position. Do NOT swap \
         in a `noColl` field — quantifying over a set chosen in advance is either empty or \
         uninhabitable again, which removes the NAME the ruler counts while rebuilding the \
         vacuity. DELETE the floor field and re-inhabit the structure with a CONSTRUCTED \
         deployed inhabitant (precedent: `deployedPoseidon2Tree`, `deployedCompress2`, \
         `deployedCap8Scheme`).\n\
      \n\
      3. GRANDFATHER IT, VISIBLY. If it genuinely cannot be ported now, paste the lines below \
         into `manual` in `Dregg2/Verify/FloorRatchetBaseline.lean` and say in the commit \
         message WHY the port is not possible yet. Each one is a claim, on the record, that a \
         new theorem is knowingly VACUOUS at deployed parameters.\n\
      \n\
      ⚑ Paste, do NOT reach for `#floor_ratchet_emit!` here: this build just FAILED, `lean` \
         writes no olean for a module that errors, so `import Dregg2` either cannot resolve or \
         silently resolves to the LAST GREEN olean and reports a surface that predates your \
         change. The emitters are for a GREEN tree — plain after a port (shrink-only, banks \
         the win), `!` only to re-bootstrap the whole baseline.\n\
      \n{paste}\n"
  let byCls := fun k => (s.carriers.filter (fun c => c.cls == k)).size
  -- ⚑ EVERY honest-floor demotion is printed on EVERY root build, with both of the poles it rode
  -- in on. A gate that quietly stopped defending a floor would read as a smaller number, which is
  -- indistinguishable from a port — so it is never quiet.
  unless s.honest.isEmpty do
    let hlines := String.intercalate "\n" (s.honest.toList.map fun (f, d, n, m) =>
      s!"  {f}\n    declared by {d}\n    refutability pole {n}\n    model {m}")
    logInfo s!"floor-ratchet: {s.honest.size} floor(s) DECLARED HONEST and checked \
      (satisfiable + refutable at a closed instance + not a sentinel + not parametrically \
      refuted), so their consumers are NOT gated:\n{hlines}"
  logInfo s!"floor-ratchet OK — {s.carriers.size} grandfathered carriers over \
    {s.floors.size} refuted floors ({s.propBody.size} prop-body defs, {s.bundles.size} floor \
    bundles); binder {byCls "binder"} + prop-body {byCls "prop-body"} + propdef-user \
    {byCls "propdef-user"} + bundle {byCls "bundle"} + bundle-user {byCls "bundle-user"} \
    + inj-spelled {byCls "inj-spelled"}; baseline {baseline.size}, slack {slack.size}; \
    inline injectivity: {s.injSigs.size} REFUTED signatures gated, {s.shapeLeak} sites left at \
    {s.injResid.size} UNREFUTED signatures (exempt — `#floor_ratchet_floors` lists them); \
    {s.total} constants."

/-! ## Auditing what the gate DERIVED

The floor list is computed, not written down, which is the feature — and therefore the thing
that can go wrong without anyone noticing. Two directions:

  * UNDER-derivation (a floor the tree refutes is not rediscovered) is caught FAIL-CLOSED by
    the sentinel checks in `surface`.
  * OVER-derivation has no automatic catch and would be far more disruptive: promoting some
    innocent `Prop` def to a "refuted floor" would flag its every user, including the
    campaign's own ported theorems. The derivation is deliberately narrow against this — the
    refuted head must be OUR `Prop`-valued def AND injectivity-SHAPED or a named sentinel — so
    the per-instance side conditions the campaign PORTS TO (`SpongeColl`, `LogColl`,
    `PathColl`, `CNColl`: `xs ≠ ys ∧ hash xs = hash ys`) do not qualify. Their bodies are
    `And (Ne …) (Eq …)`, which is neither `injShape` (body is not an fvar equation) nor
    `injShapeAnd` (`Ne` is not an fvar equality), so writing `¬ SpongeColl …` — the campaign's
    most common new theorem — cannot promote `SpongeColl` to a floor.

`#floor_ratchet_floors` is how that stays honest: it prints the derived floor set with a
per-floor carrier count. Read it whenever the gate's behaviour surprises you. -/

def report : MetaM Unit := do
  let s ← surface
  let mut lines : Array String := #[]
  for f in s.floors do
    let n := (s.carriers.filter (fun c => c.floor == f)).size
    lines := lines.push s!"  {n}\t{f}"
  let mut blines : Array String := #[]
  for b in s.bundles do
    let n := (s.carriers.filter (fun c => c.floor == b)).size
    blines := blines.push s!"  {n}\t{b}"
  let byCls := fun k => (s.carriers.filter (fun c => c.cls == k)).size
  let hlines := String.intercalate "\n" (s.honest.toList.map fun (f, d, n, m) =>
    s!"  {f}\tby {d}\tpole {n}\tmodel {m}")
  logInfo s!"floor-ratchet DERIVED SURFACE\n\
    refuted floors ({s.floors.size}), with carrier counts:\n\
    {String.intercalate "\n" lines.toList}\n\
    floors DECLARED HONEST ({s.honest.size}) — refutable at a degenerate instance AND satisfiable, \
    so their consumers are not vacuous and are not gated (`Verify/FloorPole`):\n{hlines}\n\
    floor BUNDLES ({s.bundles.size}) — structures with a floor-carrying FIELD, with the number \
    of declarations reached through each:\n\
    {String.intercalate "\n" blines.toList}\n\
    prop-body Prop defs ({s.propBody.size}): \
    {String.intercalate ", " (s.propBody.toList.map (·.toString))}\n\
    carriers {s.carriers.size} = binder {byCls "binder"} + prop-body {byCls "prop-body"} \
    + propdef-user {byCls "propdef-user"} + bundle {byCls "bundle"} \
    + bundle-user {byCls "bundle-user"} + inj-spelled {byCls "inj-spelled"}\n\
    REFUTED inline-injectivity signatures ({s.injSigs.size}) — GATED, with the refutation each \
    one rides on:\n\
    {String.intercalate "\n" (s.injSigs.toList.map (fun k => s!"  {k}"))}\n\
    UNREFUTED inline-injectivity signatures ({s.injResid.size}) — NOT gated, {s.shapeLeak} sites. \
    Each is a `Function.Injective` hypothesis the tree does NOT prove false: a widening encoding, \
    a coordinate embedding, a permutation, or a parametric domain. Gating them would be noise, \
    and a noisy gate gets disabled. To gate one, REFUTE it (`Verify/InjSpelledFloors`) — the \
    signature set is derived, so the same build picks it up:\n\
    {String.intercalate "\n" (s.injResid.toList.map (fun (k, n) => s!"  {n}\t{k}"))}\n\
    constants in environment: {s.total}"

/-! ## Emitting a new baseline (a dev tool; the OUTPUT side may touch the filesystem) -/

private def chunkSize : Nat := 150

def renderBaseline (names : Array String) : String := Id.run do
  let mut out :=
    "/-\n\
     # Dregg2.Verify.FloorRatchetBaseline — the grandfathered refuted-floor carriers.\n\
     \n\
     GENERATED by `#floor_ratchet_emit` (see `Dregg2/Verify/FloorRatchet.lean`). Do not edit\n\
     by hand except to DELETE lines. Every name here is a declaration whose type takes a\n\
     hypothesis this tree PROVES FALSE at deployed BabyBear parameters, so the declaration\n\
     is VACUOUS. They are grandfathered because they cannot all be ported at once — this\n\
     file is the RATCHET, and its only healthy direction is SHORTER.\n\
     \n\
     * REMOVING lines: mechanical. After a port, re-run the plain\n\
       `#floor_ratchet_emit \"…\"` — it emits `baseline ∩ current`, so it can only shrink.\n\
     * ADDING lines: requires `#floor_ratchet_emit!` and shows up as added lines in review.\n\
       An added line is a claim that a new theorem HAD to be built on a refuted floor.\n\
     -/\n\
     set_option autoImplicit false\n\
     \n\
     namespace Dregg2.Verify.FloorRatchetBaseline\n\n"
  let chunks := (names.size + chunkSize - 1) / chunkSize
  for i in [0:chunks] do
    let part := names.extract (i * chunkSize) (min ((i + 1) * chunkSize) names.size)
    out := out ++ s!"private def c{i} : Array String := #[\n"
    out := out ++ String.intercalate ",\n" (part.toList.map (fun n => s!"  \"{n}\""))
    out := out ++ "]\n\n"
  out := out ++
    "/-- ⚑ THE HAND-PASTE TARGET for a DELIBERATE RAISE. When `#floor_ratchet` fails it prints\n\
     its violating names already formatted as lines for this array; pasting them here is how you\n\
     grandfather a declaration that genuinely cannot be ported yet.\n\
     \n\
     It exists because the obvious recipe does not work. A failing gate means `Dregg2.lean` has\n\
     an elaboration error, and `lean` writes NO olean for a module that errors — so\n\
     `FloorRatchetEmit` (which does `import Dregg2`) cannot run at all, or, worse, runs against\n\
     a STALE `Dregg2.olean` left by the last green build and silently reports a surface that\n\
     predates your change. Pasting needs no environment and no build.\n\
     \n\
     Every line added here is a claim, on the record and in the diff, that a new declaration had\n\
     to be built on a hypothesis this tree PROVES FALSE at deployed BabyBear parameters — i.e.\n\
     that it is knowingly VACUOUS. Say why in the commit message. The next shrink-emit folds\n\
     surviving entries into the chunks above and drops the ones that got ported. -/\n\
     def manual : Array String := #[]\n\n"
  out := out ++ "/-- The grandfathered carriers. Only ever gets SHORTER. -/\ndef grandfathered : Array String :=\n"
  if chunks == 0 then
    out := out ++ "  manual\n"
  else
    out := out ++ "  " ++ String.intercalate " ++ " ((List.range chunks).map (fun i => s!"c{i}"))
                ++ " ++ manual\n"
  out := out ++ "\nend Dregg2.Verify.FloorRatchetBaseline\n"
  return out

/-- `grow = false`: emit `baseline ∩ current` (shrink only). `grow = true`: emit `current`. -/
def emit (baseline : Array String) (path : String) (grow : Bool) : MetaM Unit := do
  let s ← surface
  let base : Std.HashSet String := baseline.foldl (fun a b => a.insert b) {}
  let curNames := s.carriers.map (·.name.toString)
  let out :=
    if grow then curNames
    else curNames.filter (fun n => base.contains n)
  let added := if grow then (curNames.filter (fun n => !base.contains n)).size else 0
  IO.FS.writeFile path (renderBaseline out)
  logInfo s!"floor-ratchet baseline → {path}: {out.size} names \
    (was {baseline.size}; {baseline.size - (baseline.filter (fun b => out.contains b)).size} \
    removed, {added} ADDED{if grow then " — deliberate raise, justify it in the commit" else ""})."

/-! ## Commands -/

/-- `#floor_ratchet` — THE GATE. Fails the build when a declaration not in
`Dregg2.Verify.FloorRatchetBaseline.grandfathered` takes a refuted floor as a hypothesis.
Invoked at the end of `Dregg2.lean`, so `lake build Dregg2` carries it. Both of its inputs
(the environment, the baseline) arrive through IMPORTS, so lake re-runs it exactly when a
declaration anywhere in the tree changes — it cannot be replayed stale from cache. -/
elab "#floor_ratchet" : command =>
  liftTermElabM (Dregg2.Verify.FloorRatchet.check
    (Dregg2.Verify.FloorRatchetBaseline.grandfathered
      ++ Dregg2.Verify.FloorRatchetBaselineInline.inlineSpelled))

/-- `#floor_ratchet_floors` — print the DERIVED refuted-floor set, the prop-body defs, and
per-floor carrier counts. A diagnostic, not a gate: run it from a module that imports `Dregg2`
when you want to see what the ratchet is defending. Never invoked from the build. -/
elab "#floor_ratchet_floors" : command =>
  liftTermElabM Dregg2.Verify.FloorRatchet.report

/-- `#floor_ratchet_emit "…/FloorRatchetBaseline.lean"` — rewrite the baseline as
`baseline ∩ current`. SHRINK ONLY: a carrier that is not already grandfathered is dropped on
the floor, so this can never launder a fresh violation into the baseline. Run it after a port
to bank the win. -/
elab "#floor_ratchet_emit" path:str : command =>
  liftTermElabM (Dregg2.Verify.FloorRatchet.emit
    (Dregg2.Verify.FloorRatchetBaseline.grandfathered
      ++ Dregg2.Verify.FloorRatchetBaselineInline.inlineSpelled) path.getString false)

/-- `#floor_ratchet_emit! "…"` — RAISE the ratchet: grandfather every current carrier,
including new ones. A different token on purpose, and the result is ADDED LINES in a
reviewable diff. Use only when a new declaration genuinely cannot be built without a refuted
floor, and say why in the commit message. -/
elab "#floor_ratchet_emit!" path:str : command =>
  liftTermElabM (Dregg2.Verify.FloorRatchet.emit
    (Dregg2.Verify.FloorRatchetBaseline.grandfathered
      ++ Dregg2.Verify.FloorRatchetBaselineInline.inlineSpelled) path.getString true)

end Dregg2.Verify.FloorRatchet
