/-
# Dregg2.Verify.FreeConclusionRatchet — THE FREE-CONCLUSION GATE (`#free_conclusion_ratchet`)

## The hole this closes, stated at the resolution it was found at

`#floor_ratchet` catches **CARRIERS**: a declaration that ASSUMES a hypothesis this tree proves
false. `#keystone_audit` (`Verify/KeystoneLint`) catches a keystone with no SATISFIABILITY witness
and no TEETH. Between them there is a class neither can see, and it shipped THREE TIMES in one
session with every gate green:

> a keystone whose **CONCLUSION** is satisfied unconditionally.

`HistoryAggregation.verified_history_conserves_orBreak` and `root_tooth_pins_kernel_orBreak` were
registered keystones (`Verify/KeystoneAuditUnfoolability` (7) and (9)), one of them documented as
"the headline CRITICAL-3 closure". Their conclusion is `OrBreak (StateBreakP …) (the real claim)`,
i.e. `the real claim ∨ ∃ two colliding lists`. `SpongeCollisionShirk.spongeCollision_of_fieldBounded`
PROVES the right disjunct at any field-bounded sponge — which is every deployed sponge, by the same
pigeonhole that refutes the injectivity floor these statements were ported OFF of. So the
disjunction is literally `True`, and `orBreak_stateBreakP_iff_True` says exactly that, in the tree,
already, over an ARBITRARY good branch.

**Both keystones passed `#keystone_audit`, and they passed HONESTLY.** The satisfiability companion
really does exhibit an instance where the hypotheses hold and the conclusion fires. The teeth
companion really does refute a hostile instance. Neither check is about the conclusion's
*information content*, and a free disjunct is invisible to both:

  * the SATISFIABLE check asks "are the hypotheses jointly satisfiable" — they are, and a free
    conclusion does not make them otherwise;
  * the TEETH check asks "is the conclusion refutable somewhere" — the tooth is stated over a
    DIFFERENT predicate (`tooth_rejects_broken_order` concludes `¬ ChainBound`), which is genuinely
    two-valued. The keystone's own disjunction is never the thing the tooth refutes.

`#assert_axioms` cannot see it either: it audits the PROOF (kernel-clean) and never the STATEMENT.
And `#floor_ratchet` cannot see it BY CONSTRUCTION — the whole point of the `_orBreak` twin is that
it has NO floor hypothesis. The port from `vacuous-by-false-hypothesis` to
`vacuous-by-free-disjunct` moves a declaration OFF the floor ratchet's surface entirely, so the
carrier count goes DOWN and the instrument reports progress. That is the worst property of this
class: **the existing gate registers the defect as a win.**

## What this gate does

For every `@[load_bearing_keystone]`-tagged declaration, it asks whether the CONCLUSION contains,
in positive position, a subterm that this tree ALREADY PROVES is free. It never guesses what "free"
means — the freeness witnesses are DERIVED from the environment on every run, the way
`FloorRatchet.refutedFloors` is derived from the tree's own refutation theorems:

  `W` is a FREENESS WITNESS ⟺ `W` is a theorem in our modules, and either
    * **(iff_True)** its conclusion is `Q ↔ True` — the tree has proved `Q` carries no
      information (`orBreak_spongeCollision_iff_True`, `orBreak_stateBreakP_iff_True`,
      `CommitSurface.orBreak_stateBreak_iff_True`); or
    * **(arbitrary-branch)** its conclusion is `Q`, and `Q` mentions a `Prop`-typed binder of `W`'s
      own telescope that NO OTHER binder constrains — i.e. `Q` is proved for an ARBITRARY good
      branch (`orBreak_spongeCollision_trivial`, `orBreak_stateBreakP_trivial`). This is the
      `_trivial` spelling and it is the same fact.
  AND the resulting pattern **DISCRIMINATES** (see `isGeneric`).

Each witness's pattern `?P ∨ B` ALSO yields the BARE pattern `B` (§2b): instantiate the arbitrary
good branch at `False` and the same witness proves the break event outright, so a conclusion that IS
the break event — with no disjunction anywhere — is reached by the same derivation. That rule
carries an exemption and the exemption is the whole of it; see "THE BARE CONCLUSION" below.

Prove a new break event free and the gate starts defending against it the same build, with no edit
here — exactly `FloorRatchet`'s derivation discipline, for the same reason (a hand list is how the
Python ruler went blind to 7 of 10 refuted floors).

## ⚑ THE DISCRIMINATION GATE, and why the derivation is not obviously right

The derivation above, taken literally, admits `CollisionReduce.OrBreak.broke`:

    theorem OrBreak.broke (h : Break) : OrBreak Break P     -- {Break P : Prop} implicit

`P` is a `Prop` binder no other binder constrains, and it occurs in the conclusion. So `broke` is an
"arbitrary-branch witness" whose pattern is `?P ∨ ?Break` — which matches **every disjunction in the
tree**. A gate armed with it flags everything, gets turned off within a week, and then there is no
gate. `OrBreak.ok` is the same hazard from the other side.

So a derived pattern must PROVE IT DISCRIMINATES before it is allowed to arm the gate: it is
matched against opaque probes (`a`, `a ∨ b`, `a ∧ b`, `¬ a`, at fresh Prop locals), and a pattern
that matches one of them is DISCARDED as generic. `?P ∨ SpongeCollision ?hash` cannot match
`a ∨ b` — `SpongeCollision ?hash` against an opaque `b` fails — while `?P ∨ ?Break` matches it
immediately. The two are pinned as specimens (`witnessSpecimenVerdicts`) and re-checked on every
run, because a discrimination test that degenerates is invisible from a green build in both
directions.

## The one distinction the whole gate turns on

The SOUND port is *also* a disjunction. These two lines have the same symbols and opposite content:

    xs = ys ∨ SpongeCollision hash        -- FREE: pigeonhole supplies the right disjunct
    xs = ys ∨ SpongeColl hash xs ys       -- SOUND: a collision AT THE NAMED PAIR

The second is what `AggregationAirSound`, `MapPathCutoverCheck` and `StateCommitLeafRegrounded`
land on, and `SpongeCollisionShirk.noSpongeColl_satisfiable` proves it FAILS at a real pair of a
real field-bounded sponge — so no `_iff_True` witness for it exists, and none can. The gate
separates them because it is keyed on IN-TREE FREENESS PROOFS, not on the `∨` connective.
`FreeConclusionSpecimens.specPerInstanceResidual` is that control, asserted CLEAN on every run: if
this gate ever flags the repair, porting becomes a build error and the campaign loses.

## POSITION

Only POSITIVE positions of the CONCLUSION are scanned. `forallTelescope` strips the whole binder
telescope first, so every hypothesis — including an implication buried inside the conclusion — is
out of scope: whether a hypothesis is legitimate is `#floor_ratchet`'s question and this gate does
not double-bill it. Within the conclusion, `¬` and `↔` are NOT descended:

  * under `¬`, a free disjunct makes the statement UNPROVABLE, not vacuous — that is a tombstone
    and the campaign wants more of them;
  * `A ↔ B` with `B` free ASSERTS `A`, which is content.

⚠ THE BARE RULE READS THE HYPOTHESES, and the sentence above needs that qualification rather than
being left to read as a blanket. It does not judge whether a hypothesis is LEGITIMATE — that is
`#floor_ratchet`'s question and it is still not double-billed here. It asks only whether a
hypothesis is IDLE at a conclusion the tree already proves free, which is a property of the
conclusion, priced against the freeness proof. A hypothesis in a declaration whose conclusion is not
free is never looked at at all.

## ⚑ THE BARE CONCLUSION — SETTLED 2026-08-02. It was written up as possibly terminal. It is not.

This gate shipped (`0f802d73d`) with a hole it had MEASURED on itself, and a hedge attached to it.
The hole:

    #free_conclusion_probe Dregg2.Circuit.CommitFaithfulRegrounded.stateBreak_faithful_reduces
      → "no free disjunct found"

though that theorem's conclusion is `FaithfulBreakGlobal …`, which
`faithfulBreakGlobal_free_of_fieldBounded` proves OUTRIGHT ten lines above it in its own file. Same
for `Distributed.HistoryAggregation.ChainLogColl.toSponge`, whose conclusion is a bare
`SpongeCollision compressN`. CAUSE: every derived pattern had the shape `?P ∨ Break`, so a
conclusion that IS the free event, undisjoined, matched nothing.

The hedge, in that commit's message: *"a bare-`Break` rule would also flag
`spongeCollision_of_fieldBounded`, which the spec deliberately pins CLEAN"* — and then, attached to
it, the guess that the limit might be a permanent one. **That argument is right about the pair and
wrong about the verdict, and the guess is REFUTED below rather than inherited.** The phrase itself
is deliberately not reproduced here: a docstring asserting a limit nobody proved is the exact move
this campaign exists to stop, and the record of it belongs in `0f802d73d`, not in the instrument. The two declarations really
are indistinguishable by any predicate on the SHAPE OF THE CONCLUSION — the conclusion is the same
proposition:

    FieldBounded hash      → SpongeCollision hash      -- the REFUTATION.  must stay CLEAN
    SpongeColl hash xs ys  → SpongeCollision hash      -- the `_toGlobal` BRIDGE.  must FLAG

They are separated, exactly and mechanically, by a predicate on the HYPOTHESIS:

> **A declaration concluding a bare free break event is FLAGGED iff it carries a `Prop` hypothesis
> that the freeness proof itself does not need.**

The refutation assumes precisely what the freeness witness assumes, so nothing it carries is idle
and it is clean. A consumer that returns the break event as its GUARANTEE assumes things about the
object it claims to secure (`hW : Poseidon2Width8 permW`, `StateBreakP …`, `ChainLogColl …`) and
every one of them is DEAD WEIGHT — the witness reaches that same conclusion without them. That is
what makes such a statement vacuous, and the report now NAMES the idle hypothesis (`Hit.detail`).
`bareTestHere` is the implementation and carries the argument again at the point of use.

Three things about the predicate, because a rule is a claim:

  * it needs no notion of authorial intent, no naming convention and no registration — it compares
    two telescopes at the parameters the CONCLUSION MATCH already determined;
  * it does not exempt "the refutation" BY NAME. Every restatement of it is clean
    (`specBareFreenessWithData`), and a "refutation" that acquires an idle `Prop` hypothesis is
    flagged — which is the fail-closed direction, since that is no longer a refutation but a weaker
    theorem wearing one;
  * it is an EXEMPTION, not a matter of scope. The other candidate refinement was to lean on the
    fact that only KEYSTONES are scanned, so `spongeCollision_of_fieldBounded` is simply out of
    scope. That is strictly weaker — it holds exactly until someone tags the pigeonhole fact — so
    `scripts/free_conclusion_canary.lean` REGISTERS the refutation as a keystone (§2b,
    `control_free_conclusion_canary_refutation_KS`) and requires the gate to leave it alone anyway.

MEASURED 2026-08-02, and each of these is a number that would have hidden a mistake:

  * the two blind declarations above now FLAG, each naming its idle hypothesis;
  * `spongeCollision_of_fieldBounded`, `faithfulBreakGlobal_free_of_fieldBounded` and the
    `specBreakClaimed` specimen read CLEAN;
  * the tagged corpus is UNCHANGED — 0 free conclusions over 84 keystones — so the baseline stays
    EMPTY and this rule reds nothing that was not already red;
  * the three historical statements still flag through the DISJUNCTIVE rule and their three
    `_of_noColl` ports still read clean: the new rule moved no old verdict;
  * the canary bites both ways — §2b names a bare-violation keystone and not the refutation control,
    §2c proves the rule cannot be switched off quietly (a witness set with the bare patterns
    stripped is REFUSED by `bareSentinelWitnesses`).

## ⚠ WHAT THIS GATE DOES NOT DO — read before quoting it

It is a **necessary-condition** check on one known-and-proved class, not a decision procedure for
vacuity. Precisely:

  1. **It only reaches break events the tree has ALREADY PROVED free.** A brand-new global
     existential with no `_iff_True` companion is invisible here until someone writes the
     refutation. That is the same shape as `#floor_ratchet` (which sees only floors the tree
     refutes) and it is why both instruments are derivations rather than lists — the refutation is
     the arming step, and writing it is cheap.
  2. **The freeness witnesses carry their own hypotheses** (`FieldBounded compressN`). A keystone
     stated at an ABSTRACT, unbounded sponge is flagged even though the disjunct is not free THERE.
     That is deliberate and it is the fail-closed direction: every deployed sponge is field-bounded,
     and the cost of a false positive is one baseline row with a stated reason, while the cost of a
     false negative is what §1 of this docstring describes. The report NAMES the witness so its
     residual hypothesis is one click away.
  3. **It says nothing about the good branch.** A keystone that is not flagged may still be vacuous
     for a reason nobody has proved yet. A clean run means "no registered keystone concludes
     something this tree proves free", not "the keystones are sound".
  4. **The BARE rule reads the hypotheses, so it is silent on a declaration with none.** A keystone
     concluding a bare break event and assuming nothing (`theorem k : SpongeCollision headHash`) is
     CLEAN here, and rightly: at a CONCRETE sponge that IS the pigeonhole fact and carries content,
     and at an abstract one it is not provable at all. The tree contains no third case today; if one
     appears, this rule does not see it.
-/
import Lean
import Dregg2.Verify.FloorCensus
import Dregg2.Verify.KeystoneLint

set_option autoImplicit false
set_option maxRecDepth 4000

namespace Dregg2.Verify.FreeConclusionRatchet

open Lean Meta Elab Command
open Dregg2.Verify.FloorCensus (ourModule moduleOf isInternalName headConst?)
open Dregg2.Verify.KeystoneLint (keystoneExt)

/-! ## §1 — the syntactic PREFILTER (no `MetaM`, runs over every constant) -/

/-- Peel the `∀` telescope off a type, returning the binder DOMAINS (each with loose bvars
referring to the binders before it) and the body. -/
partial def peelForall (e : Expr) (doms : Array Expr) : Array Expr × Expr :=
  match e with
  | .forallE _ d b _ => peelForall b (doms.push d)
  | e => (doms, e)

/-- `Q` from `Q ↔ True` (either orientation). The **iff_True** witness shape: the tree has PROVED
that `Q` carries no information. -/
def iffTrueSide? (e : Expr) : Option Expr :=
  match e with
  | .app (.app (.const ``Iff _) l) r =>
    if r == .const ``True [] then some l
    else if l == .const ``True [] then some r
    else none
  | _ => none

/-- Does loose bvar `k` occur ONLY in strictly positive positions of `e`? Over-approximated in the
SAFE direction: an occurrence in a `∀`/`λ` domain, under `¬`, or on either side of an `↔` is
refused outright, and everything else counts as positive.

⚑ MEASURED, and it is the difference between a freeness witness and an ordinary parametric theorem.
The first derivation admitted `Dregg2.Liveness.haltGraph_reachable (P : Prop) : reachable (haltGraph
P) 1 ↔ P` — a halting-reduction gadget, proved for an arbitrary `P`, with no binder constraining
`P`. It is not free: `P` occurs on BOTH sides of the `↔`, so the statement is not monotone in `P`
and proving it for every `P` proves something real. What makes `orBreak_spongeCollision_trivial` a
freeness witness is that its `P` is strictly POSITIVE — the statement is monotone in the good
branch, so proving it for arbitrary `P` proves it at `P := False`, i.e. with no good branch at all
(`orBreak_spongeCollision_False` is that instance, in the tree, spelled out). -/
partial def onlyPositive (k : Nat) (e : Expr) : Bool :=
  if !e.hasLooseBVar k then true else
  match e with
  | .forallE _ d b _ => !d.hasLooseBVar k && onlyPositive (k + 1) b
  | .lam _ d b _ => !d.hasLooseBVar k && onlyPositive (k + 1) b
  | .letE _ t v b _ => !t.hasLooseBVar k && !v.hasLooseBVar k && onlyPositive (k + 1) b
  | .mdata _ b => onlyPositive k b
  | .proj _ _ b => onlyPositive k b
  | .app (.const ``Not _) a => !a.hasLooseBVar k
  | .app f a =>
    if e.isAppOfArity ``Iff 2 then
      let args := e.getAppArgs
      !args[0]!.hasLooseBVar k && !args[1]!.hasLooseBVar k
    else onlyPositive k f && onlyPositive k a
  | _ => true

/-- The **arbitrary-branch** witness shape (`_trivial`): the index of a `Prop`-typed binder that the
body MENTIONS, that NO LATER binder constrains, and that occurs only POSITIVELY — so the body is
proved for an arbitrary `P` with no assumption about `P` and monotonically in it, which is exactly
"the good branch is unreachable from the statement".

Three guards, and each one has already discarded something the tree really contains:
  * the body must not BE the variable (`∀ P : Prop, P` is `False`, not a freeness witness);
  * no LATER binder domain may mention it — `∀ (P : Prop), P → P` has `h : P` constraining `P` and
    is an ordinary implication (binders BEFORE it cannot mention it at all);
  * it must occur only positively — see `onlyPositive`, which is what `haltGraph_reachable` failed.

de Bruijn: inside the body, binder `i` of `n` is `bvar (n-1-i)`; inside domain `j`, it is
`bvar (j-1-i)`. -/
def arbitraryBranch? (doms : Array Expr) (body : Expr) : Option Nat := Id.run do
  let n := doms.size
  for i in [0 : n] do
    if doms[i]! != .sort .zero then continue
    let k := n - 1 - i
    if !body.hasLooseBVar k then continue
    if body == .bvar k then continue
    if !onlyPositive k body then continue
    let mut clean := true
    for j in [i + 1 : n] do
      if doms[j]!.hasLooseBVar (j - 1 - i) then clean := false
    if clean then return some i
  return none

/-- Compiler-generated companions with no source token of their own, dropped from the witness
scan. Copied from `FloorRatchet.isGeneratedCompanion` (not imported: that module pulls in the
~1900-row floor baseline, and this gate must stay cheap to build on its own).

⚑ MEASURED, not precautionary. The first run of `#free_conclusion_witnesses` derived
`Circuit.FriVerifier.GenuineWitness.mk.injEq` and `.mk.sizeOf_spec` as freeness witnesses: that
structure has a `Prop`-typed field, so `mk.injEq`'s statement quantifies over a `Prop` no other
binder constrains and the arbitrary-branch test fires on an `Eq`-headed pattern nobody wrote. It is
noise rather than a hole — the pattern only matches an equation between two `mk` applications — but
a DERIVED instrument that reports junk is one people stop reading, which is how it goes blind. -/
def isGeneratedCompanion (n : Name) : Bool :=
  match n with
  | .str _ s =>
    s == "casesOn" || s == "recOn" || s == "rec" || s == "below" || s == "brecOn"
      || s == "ibelow" || s == "binductionOn" || s == "noConfusion" || s == "noConfusionType"
      || s == "ctorIdx" || s == "toCtorIdx" || s == "sizeOf_spec" || s == "injEq"
      || s == "eq_def" || s == "induct" || s == "fun_cases" || s.startsWith "match_"
      || s.startsWith "proof_" || (s.startsWith "eq_" && (s.drop 3).all Char.isDigit)
  | _ => false

/-! ## §2 — building the pattern, and proving it DISCRIMINATES

A pattern is built by instantiating the witness's whole telescope with METAVARIABLES, so matching
assigns the witness's own parameters (the sponge, the good branch) and never the keystone's.
Everything below creates those metavariables INSIDE the local context it will match in — a pattern
built outside a `withLocalDecl` scope cannot be assigned a term mentioning that scope's locals, so
the probes would trivially "fail" and the discrimination gate would accept every pattern. -/

/-- The free pattern of a witness type. `iffForm` selects the `Q ↔ True` side; otherwise the whole
(instantiated) conclusion is the pattern. -/
def patternOf (ty : Expr) (iffForm : Bool) : MetaM (Option Expr) := do
  let (_, _, body) ← forallMetaTelescope ty
  if iffForm then return iffTrueSide? body else return some body

/-- **THE DISCRIMINATION GATE.** A pattern that matches an OPAQUE probe of its own shape matches
every term of that shape in the tree, so arming the gate with it would flag everything. `?P ∨ ?Break`
(from `OrBreak.broke` / `OrBreak.ok`, real theorems in this tree) matches `a ∨ b` and is discarded;
`?P ∨ SpongeCollision ?hash` cannot, and arms the gate.

The probes are built at FRESH Prop locals so nothing about them can be inferred, and the pattern is
rebuilt inside their scope so its metavariables are assignable to them. -/
def isGeneric (ty : Expr) (iffForm : Bool) : MetaM Bool :=
  withLocalDeclD `a (.sort .zero) fun a =>
  withLocalDeclD `b (.sort .zero) fun b => do
    let probes : Array Expr :=
      #[ a
       , mkApp2 (.const ``Or []) a b
       , mkApp2 (.const ``And []) a b
       , mkApp (.const ``Not []) a
       , mkApp2 (.const ``Iff []) a b ]
    for p in probes do
      let hit ← withoutModifyingState do
        match ← patternOf ty iffForm with
        | none => pure false
        | some pat => try isDefEq pat p catch _ => pure false
      if hit then return true
    return false

/-- Does the witness's pattern match `target`? `target` lives in the caller's local context (the
keystone's own telescope), the pattern's metavariables are created there, and every assignment is
rolled back — so one witness cannot poison the next. -/
def matchesWitness (ty : Expr) (iffForm : Bool) (target : Expr) : MetaM Bool :=
  withoutModifyingState do
    match ← patternOf ty iffForm with
    | none => pure false
    | some pat => try isDefEq pat target catch _ => pure false

/-! ## §3 — the derived witness set -/

/-! ### §2b — THE BARE PATTERN, DERIVED FROM THE DISJUNCTIVE ONE

A witness's pattern is `?P ∨ B` with `?P` the witness's OWN arbitrary good branch. Instantiate that
metavariable at `False` and the witness proves `False ∨ B`, i.e. **`B` itself**, under exactly the
hypotheses it already carries. So the tree's proof that `?P ∨ B` is free IS a proof that the BARE
break event `B` is free, and the bare pattern is DERIVED — never a second hand list, and it arms and
disarms with the disjunctive one.

That instance is not hypothetical: `SpongeCollisionShirk.orBreak_spongeCollision_False` is literally
`OrBreak (SpongeCollision hash) False` in the tree, and `spongeCollision_of_fieldBounded` is the
same fact with the `False` peeled off.

⚑ THE BARE PATTERN GETS ITS OWN DISCRIMINATION GATE, for a sharper failure than the disjunctive
one: if `B` came back an unassigned metavariable the pattern would be `?B`, which matches EVERY
proposition in the tree rather than merely every disjunction. `isGenericBare` runs the same opaque
probes.

⚠ AND IT IS REDUNDANT TODAY — said plainly rather than left to read as a defence. On the shape
`?P ∨ B` a bare-metavariable `B` already makes `isGeneric` match the `a ∨ b` probe, so the witness
never survives to reach here. It is kept because the two patterns are computed by DIFFERENT code
paths (`patternOf` takes the `↔ True` side unreduced; `barePatternOf` reduces), and the day those
diverge — a loosened left-disjunct guard, a deeper `whnf` — this is the check that stops a pattern
matching the whole tree. It is defence in depth for a specific future edit, not a check that can
fire today. -/

/-- The BARE free pattern of a witness, plus the witness's own telescope metavariables (the caller
needs them AFTER matching, to read off which hypotheses the freeness proof actually requires).

`none` unless the pattern reduces to `?P ∨ B` with `?P` an unassigned metavariable OF THIS
WITNESS'S telescope. A concrete left disjunct is not an arbitrary good branch, so nothing is derived
from it. -/
def barePatternOf (ty : Expr) (iffForm : Bool) : MetaM (Option (Expr × Array Expr)) := do
  let (mvars, _, body) ← forallMetaTelescope ty
  let some concl := (if iffForm then iffTrueSide? body else some body) | return none
  let c ← try whnfR concl catch _ => pure concl
  unless c.isAppOfArity ``Or 2 do return none
  let args := c.getAppArgs
  let lhs ← instantiateMVars args[0]!
  unless lhs.isMVar do return none
  unless mvars.any (fun m => m == lhs) do return none
  return some (args[1]!, mvars)

/-- The DISCRIMINATION gate for the bare pattern. Same probes, same reason, one extra bite: a bare
pattern that is itself a metavariable matches every `Prop` in the tree. -/
def isGenericBare (ty : Expr) (iffForm : Bool) : MetaM Bool :=
  withLocalDeclD `a (.sort .zero) fun a =>
  withLocalDeclD `b (.sort .zero) fun b => do
    let probes : Array Expr :=
      #[ a
       , mkApp2 (.const ``Or []) a b
       , mkApp2 (.const ``And []) a b
       , mkApp (.const ``Not []) a
       , mkApp2 (.const ``Iff []) a b ]
    for p in probes do
      let hit ← withoutModifyingState do
        match ← barePatternOf ty iffForm with
        | none => pure false
        | some (pat, _) => try isDefEq pat p catch _ => pure false
      if hit then return true
    return false

/-- A FREENESS WITNESS, derived from the environment. `heads` is the PREFILTER key: the pattern's
head constant BOTH as written and after reducible unfolding, because `OrBreak B P` is an `abbrev`
for `P ∨ B` and a keystone may spell the same statement either way (that spelling split is the
residual `FloorRatchet` had to close for `Function.Injective` vs `Poseidon2SpongeCR`;
`FreeConclusionSpecimens.specFreeSpelledViaOr` pins it here before it can open).

`bareHeads` is the same prefilter for the BARE pattern (§2b), EMPTY when the witness arms no bare
pattern — which is how a witness whose conclusion is not a disjunction over its own good branch
(`CatalogInstances.AuthorizationGuard.admits_unchecked`, an `Eq`) contributes nothing to the bare
rule. -/
structure FreeWitness where
  thm       : Name
  iffForm   : Bool
  shape     : String
  heads     : Array Name
  bareHeads : Array Name
  deriving Inhabited

/-- Every freeness witness in our modules, sorted by name so the gate's verdicts and its baseline
keys do not depend on environment traversal order. THEOREMS only: a `def` is not a proof of
anything, and every witness this class has produced is a theorem. -/
def deriveWitnesses : MetaM (Array FreeWitness) := do
  let env ← getEnv
  let mask : Array Bool := env.header.moduleNames.map ourModule
  let mut names : Array Name := env.constants.foldStage2 (fun acc n _ => acc.push n) #[]
  names := env.constants.map₁.fold (fun acc n _ => acc.push n) names
  let mut out : Array FreeWitness := #[]
  for nm in names do
    -- A constant with NO module index belongs to the module being elaborated RIGHT NOW and is
    -- OURS — the gate must see the file it is standing in (`FloorRatchet.ourNames`, same rule).
    let mine :=
      match env.getModuleIdxFor? nm with
      | some idx => mask.getD idx.toNat false
      | none     => true
    unless mine do continue
    if isInternalName nm then continue
    if isGeneratedCompanion nm then continue
    let some ci := env.find? nm | continue
    unless ci matches .thmInfo _ do continue
    let (doms, body) := peelForall ci.type #[]
    let iffForm := (iffTrueSide? body).isSome
    let arb := (arbitraryBranch? doms body).isSome
    unless iffForm || arb do continue
    if ← isGeneric ci.type iffForm then continue
    let heads? ← withoutModifyingState do
      match ← patternOf ci.type iffForm with
      | none => pure none
      | some pat => do
        let asWritten := headConst? pat
        let reduced ← try pure (headConst? (← whnfR pat)) catch _ => pure none
        pure (some ((#[] ++ asWritten.toArray) ++ reduced.toArray))
    let some heads := heads? | continue
    if heads.isEmpty then continue
    let bareHeads ← withoutModifyingState do
      match ← barePatternOf ci.type iffForm with
      | none => pure (#[] : Array Name)
      | some (pat, _) =>
        if ← isGenericBare ci.type iffForm then pure #[] else do
          let asWritten := headConst? pat
          let reduced ← try pure (headConst? (← whnfR pat)) catch _ => pure none
          pure ((#[] ++ asWritten.toArray) ++ reduced.toArray)
    out := out.push
      { thm := nm, iffForm, shape := if iffForm then "iff_True" else "arbitrary-branch", heads,
        bareHeads }
  return out.qsort (fun x y => x.thm.toString < y.thm.toString)

/-! ## §4 — scanning a conclusion -/

/-- A flagged declaration: WHICH witness proves WHICH subterm of its conclusion free. `detail` is
the bare rule's evidence — the hypothesis that the freeness proof does NOT need, i.e. the one the
declaration is carrying for nothing — and is empty for a disjunctive hit. -/
structure Hit where
  subject : Name
  witness : Name
  shape   : String
  subterm : String
  detail  : String := ""
  deriving Inhabited

/-- Baseline row separator. Chosen because no Lean identifier contains it. The key is the PAIR
`(subject, witness)`, never the name alone — a grandfathered NAME would be a blanket exemption over
every break event for the life of that name, which is exactly the hole `FloorRatchet` closed on
2026-08-01 (161 declarations were sitting on it). -/
def keySep : String := " ⊣ "

def hitKey (h : Hit) : String := h.subject.toString ++ keySep ++ h.witness.toString

/-- **THE BARE RULE, and the ONE predicate that separates its two poles.**

A conclusion that IS the free break event, undisjoined, is `True` for exactly the same reason a
disjunction over it is — so it must be flagged. But the tree's own PROOF that the event is free has
that shape too (`SpongeCollisionShirk.spongeCollision_of_fieldBounded :  FieldBounded hash →
SpongeCollision hash`), and flagging it would gate the refutation that ARMS this gate. Those two are
the counterexample pair, and this is the predicate that separates them:

> **A declaration concluding a bare free break event is flagged iff it carries a `Prop` hypothesis
> that the freeness proof itself does not need.**

The refutation assumes exactly `FieldBounded hash` — the freeness witness's own hypothesis, and
nothing else — so it is CLEAN, and so is every restatement of it. A consumer that returns the break
event as its GUARANTEE carries hypotheses ABOUT THE THING IT CLAIMS TO SECURE (`hW :
Poseidon2Width8 permW`, `StateBreakP …`, `ChainLogColl …`), and every one of them is dead weight:
the conclusion follows from the witness alone. That is exactly what makes it vacuous, and it is
what the flag says.

The comparison is against the witness's own telescope INSTANTIATED BY THE MATCH, so it is the
hypotheses the freeness proof needs AT THESE PARAMETERS, not a name test. A witness hypothesis still
carrying a metavariable after the match is UNDETERMINED and covers nothing — otherwise it would
unify with any subject hypothesis at all and the rule would fail open.

⚠ FAIL-CLOSED, on the same terms as the disjunctive rule (docstring §2): a subject that does not
supply `FieldBounded` is flagged anyway. Its conclusion is free at every sponge this tree deploys,
the cost of a false positive is one baseline row with a stated reason, and the shipped gate already
takes exactly this direction — `HistoryAggregation.logChained_of_verified_orBreak` has no
`FieldBounded` hypothesis and is flagged (measured 2026-08-02). -/
def bareTestHere (ws : Array FreeWitness) (subject : Name) (hyps : Array Expr) (e : Expr) :
    MetaM (Option Hit) := do
  let env ← getEnv
  let some hs := headConst? e | return none
  for w in ws do
    unless w.bareHeads.contains hs do continue
    let some wci := env.find? w.thm | continue
    let res ← withoutModifyingState do
      let some (pat, mvars) ← barePatternOf wci.type w.iffForm | pure none
      let matched ← try isDefEq pat e catch _ => pure false
      if !matched then pure none else do
        let mut needed : Array Expr := #[]
        for m in mvars do
          let mty ← instantiateMVars (← inferType m)
          if mty.hasExprMVar then continue
          if ← isProp mty then needed := needed.push mty
        for h in hyps do
          let hty ← instantiateMVars h
          let mut covered := false
          for wh in needed do
            let same ← withoutModifyingState <|
              (do try isDefEq hty wh catch _ => pure false)
            if same then
              covered := true
              break
          unless covered do
            return some
              { subject, witness := w.thm, shape := s!"bare({w.shape})",
                subterm := toString (← ppExpr e),
                detail := toString (← ppExpr hty) }
        pure none
    if let some h := res then return some h
  return none

/-- Test ONE subterm, IN ITS OWN SCOPE, against every derived witness. The head prefilter is
syntactic and consults BOTH spellings the witness recorded, so `OrBreak B P` and its `abbrev`
expansion `P ∨ B` land on the same witness. The DISJUNCTIVE rule is tried first, so a keystone whose
conclusion is `P ∨ Break` is reported against the disjunction it actually wrote rather than against
the break event nested inside it. -/
def testHere (ws : Array FreeWitness) (subject : Name) (hyps : Array Expr) (e : Expr) :
    MetaM (Option Hit) := do
  let env ← getEnv
  let some hs := headConst? e | return none
  for w in ws do
    unless w.heads.contains hs do continue
    let some wci := env.find? w.thm | continue
    if ← matchesWitness wci.type w.iffForm e then
      return some { subject, witness := w.thm, shape := w.shape,
                    subterm := toString (← ppExpr e) }
  bareTestHere ws subject hyps e

/-- Walk the POSITIVE positions of a conclusion, testing each in place.

`¬` and `↔` are not descended (see the POSITION section of the module docstring). Binders are
entered through `forallTelescope` / `lambdaTelescope`, which both DISCARD the domains (negative
position) and replace loose bvars by locals.

⚑ **THE MATCH HAPPENS INSIDE THE BINDER'S SCOPE, and the first draft of this file got that wrong.**
Collecting subterms into an array and matching them afterwards lets a subterm ESCAPE the
`lambdaTelescope` that introduced its locals: by match time those free variables are no longer in
the local context, `isDefEq` cannot assign against them, and the term silently reads as clean. The
symptom is a gate that passes on anything nested under an `∃` or a `λ` — which is where a free
disjunct hides in a real "there is an extraction such that …" statement.
`FreeConclusionSpecimens.specFreeUnderExists` is exactly that shape, and it is why the classifier
self-test exists: the bug was found by the specimen, on the first run, not by review.

`hyps` carries the subject's `Prop` hypotheses down for the BARE rule, and it GROWS at every `∀` the
scan enters: an implication nested inside the conclusion (`… → SpongeCollision hash`) is dead weight
in exactly the same way as one in the outer telescope, and reading only the outer telescope would
let one hop of nesting hide it. -/
partial def scanPositive (ws : Array FreeWitness) (subject : Name) (hyps : Array Expr) (e : Expr) :
    MetaM (Option Hit) := do
  match e with
  | .app (.const ``Not _) _ => return none
  | .mdata _ b => scanPositive ws subject hyps b
  | .forallE .. => forallTelescope e fun xs b => do
      scanPositive ws subject (← propHyps hyps xs) b
  | .lam .. => lambdaTelescope e fun _ b => scanPositive ws subject hyps b
  | .letE _ _ _ b _ => scanPositive ws subject hyps b
  | .app f a =>
    if e.isAppOfArity ``Iff 2 then return none
    if let some h ← testHere ws subject hyps e then return some h
    if let some h ← scanPositive ws subject hyps f then return some h
    scanPositive ws subject hyps a
  | _ => testHere ws subject hyps e
where
  /-- Extend `acc` with the types of the `Prop`-typed locals among `xs`. -/
  propHyps (acc : Array Expr) (xs : Array Expr) : MetaM (Array Expr) := do
    let mut out := acc
    for x in xs do
      let t ← inferType x
      if ← isProp t then out := out.push t
    return out

/-- Classify ONE type: the first (witness, positive subterm) pair that matches, or `none`.
Deterministic — witnesses are sorted, positions are visited outside-in. -/
def scanType (ws : Array FreeWitness) (subject : Name) (ty : Expr) : MetaM (Option Hit) :=
  forallTelescope ty fun xs concl => do
    let mut hyps : Array Expr := #[]
    for x in xs do
      let t ← inferType x
      if ← isProp t then hyps := hyps.push t
    scanPositive ws subject hyps concl

/-! ## §5 — FAIL-CLOSED self-checks

A gate that under-measures passes vacuously and looks exactly like success. Every one of these
hard-errors rather than reporting a smaller number. -/

/-- Whole-corpus scale gate: the tagged corpus is 90 keystones across 12 audit modules as this
lands, of which 83 were reachable when it was measured (see §6). Below this bar the
environment is partial (the invoking module is missing `KeystoneAudit*` imports) and every count
reads low — indistinguishable from progress. -/
def minKeystones : Nat := 60

/-- SENTINEL FREENESS WITNESSES: the three the tree already holds, which the derivation MUST
rediscover. A derivation that stops recognising one of these reports a smaller free set and PASSES,
which is exactly the shape of failure this whole module exists to stop, so it fails the build
instead.

⚑ A name here can fail closed for the GOOD reason: the break event got ported away and its freeness
theorem deleted. That is a win, and the fix is to delete the line in the same commit — but NEVER to
delete the freeness theorem while leaving the break event in the tree, which would silently disarm
the gate for that whole family. -/
def sentinelWitnesses : List Name :=
  [ `Dregg2.Circuit.SpongeCollisionShirk.orBreak_spongeCollision_iff_True
  , `Dregg2.Circuit.StateCommitReduce.orBreak_stateBreakP_iff_True
  , `Dregg2.Circuit.CircuitSoundness.CommitSurface.orBreak_stateBreak_iff_True ]

/-- SENTINEL BARE PATTERNS: witnesses that MUST arm the bare rule (§2b) as well as the disjunctive
one. The bare pattern is DERIVED from the disjunctive pattern's shape, so a change to `patternOf`,
to `whnfR`'s reducibility, or to how a break event is spelled can silently stop deriving it — and a
disarmed bare rule looks exactly like a tree with no bare free conclusions in it.

Only witnesses reachable from EVERY invocation site are listed (both of these come in through
`Circuit.CircuitSoundness`). The bare `∨` spelling — `CommitFaithfulRegrounded.orFaithful-
BreakGlobal_iff_True`, which no module imports — is not pinnable here for that reason; it was
MEASURED to arm `FaithfulBreakGlobal` on 2026-08-02 and `specFreeBareStateBreak` pins the
`whnfR`-through-`OrBreak` path that the spelling difference exercises. -/
def bareSentinelWitnesses : List Name :=
  [ `Dregg2.Circuit.SpongeCollisionShirk.orBreak_spongeCollision_iff_True
  , `Dregg2.Circuit.StateCommitReduce.orBreak_stateBreakP_iff_True ]

/-- The DISCRIMINATION self-test (`true` = must be ACCEPTED as a freeness witness). Both
degenerations are invisible from a green build:

  * accept too much and `OrBreak.broke`'s `?P ∨ ?Break` arms the gate, every disjunction in the
    tree is flagged, and the gate gets deleted;
  * accept too little and the free disjuncts walk back in — `orBreak_spongeCollision_trivial` is
    the `_trivial` spelling of the sentinel `_iff_True`, and dropping the arbitrary-branch form
    would leave a family armed only if someone happened to write the `↔` version. -/
def witnessSpecimenVerdicts : List (Name × Bool) :=
  [ (`Dregg2.Circuit.SpongeCollisionShirk.orBreak_spongeCollision_trivial, true)
  , (`Dregg2.Circuit.SpongeCollisionShirk.orBreak_spongeCollision_iff_True, true)
  , (`Dregg2.Circuit.CollisionReduce.OrBreak.broke, false)
  , (`Dregg2.Circuit.CollisionReduce.OrBreak.ok, false) ]

/-- The CLASSIFIER self-test (`true` = the type must be FLAGGED). Each name is a `Prop`-valued def
in `Dregg2.Verify.FreeConclusionSpecimens` whose VALUE is a declaration TYPE.
`specPerInstanceResidual` is the one that matters most: it is the landed REPAIR, and a gate that
flags it turns porting into a build error.

⚑ THE LAST FOUR ARE THE BARE RULE'S POLES, and they are the whole reason that rule can exist. The
declaration that MUST flag (`specFreeBareBreak`, a named residual cashed out as the global event)
and the one that MUST NOT (`specBreakClaimed`, the pigeonhole refutation) have the SAME shape
`Hyp → Break`. What separates them is whether the hypothesis is one the freeness proof itself
carries. If either verdict moves, that separation has failed and the bare rule is either blind or
eating the refutation. -/
def classifierSpecimenVerdicts : List (Name × Bool) :=
  [ (`Dregg2.Verify.FreeConclusionSpecimens.specFreeOrBreak, true)
  , (`Dregg2.Verify.FreeConclusionSpecimens.specFreeSpelledViaOr, true)
  , (`Dregg2.Verify.FreeConclusionSpecimens.specFreeUnderConjunct, true)
  , (`Dregg2.Verify.FreeConclusionSpecimens.specFreeUnderExists, true)
  , (`Dregg2.Verify.FreeConclusionSpecimens.specFreeStateBreak, true)
  , (`Dregg2.Verify.FreeConclusionSpecimens.specPerInstanceResidual, false)
  , (`Dregg2.Verify.FreeConclusionSpecimens.specBreakInHypothesis, false)
  , (`Dregg2.Verify.FreeConclusionSpecimens.specOrdinaryDisjunction, false)
  , (`Dregg2.Verify.FreeConclusionSpecimens.specFreeUnderNot, false)
  , (`Dregg2.Verify.FreeConclusionSpecimens.specFreeBareBreak, true)
  , (`Dregg2.Verify.FreeConclusionSpecimens.specFreeBareStateBreak, true)
  , (`Dregg2.Verify.FreeConclusionSpecimens.specBreakClaimed, false)
  , (`Dregg2.Verify.FreeConclusionSpecimens.specBareFreenessWithData, false) ]

/-! ## §6 — THE BASELINE

⚑ **IT IS EMPTY, AND THAT IS A MEASUREMENT, NOT AN ASSUMPTION.** `#free_conclusion_report` was run
before this file was armed and found ZERO free conclusions over **83 of the 90** tagged keystones —
the two that WERE free (`KeystoneAuditUnfoolability` (7) `verified_history_conserves_KS` and (9)
`root_tooth_pins_kernel_KS`) had already been repointed onto their per-instance `_of_noColl` forms
by hand, hours earlier. So this gate reds NOTHING on the day it lands and its healthy value is 0.

⚠ **83, NOT 90, AND THE MISSING 7 ARE NOT MEASURED.** `KeystoneAuditSystemRoots` (1),
`KeystoneAuditArgusReceipt` (4) and `KeystoneAuditTerminalAdapters` (2) are unbuildable at HEAD
through `Dregg2/Circuit/CircuitCompletenessNonVacuityReal.lean`, which fails a `rfl` at :421 and
leaks `sorryAx` into four declarations. That red is unmodified in the working tree and predates this
gate. `FreeConclusionGate` imports all twelve regardless, so those 7 are scanned the moment the red
clears — and if any of them IS free, this gate reds then rather than never.

⚑ **THE MEASUREMENT IS NOT WHAT MAKES THE GATE CREDIBLE — THE THREE HISTORICAL STATEMENTS ARE.**
A gate whose first run finds nothing has proved nothing. All three declarations that fooled
`#keystone_audit` are still in the tree as tombstones, and the gate NAMES every one of them with
the exact free subterm (`#free_conclusion_probe`, run 2026-08-01):

    HistoryAggregation.verified_history_conserves_orBreak      ⟵ orBreak_stateBreakP_iff_True
    HistoryAggregation.root_tooth_pins_kernel_orBreak          ⟵ orBreak_stateBreakP_iff_True
    RecursiveAggregation.conserves_from_verification_orBreak   ⟵ orBreak_stateBreakP_iff_True

and their three `_of_noColl` ports come back CLEAN. Load-bearing and refutable, on the real objects.

⚑ **RE-MEASURED 2026-08-02, WITH THE BARE RULE ARMED: still ZERO, over 84 reachable keystones.** The
rule that closed the bare blind spot added NOTHING to this baseline, and the three statements above
still flag through the disjunctive rule with the same witness. So the baseline is empty for two
independent reasons now, and neither of them is "nobody looked": the two declarations the bare rule
was built for (`CommitFaithfulRegrounded.stateBreak_faithful_reduces`,
`HistoryAggregation.ChainLogColl.toSponge`) are real and really flag — they are simply not tagged as
keystones, which is exactly the difference between a bridge that loses the pair and a claim.

Rows are `subject{keySep}witness` — the PAIR, so a grandfathered keystone that acquires a SECOND
free disjunct is a fresh violation rather than covered forever by one row. A row is a claim, on the
record, that a registered keystone knowingly concludes something this tree proves unconditional. -/
def grandfathered : Array String := #[]

/-! ## §7 — the check -/

structure Surface where
  witnesses : Array FreeWitness
  keystones : Array Name
  hits      : Array Hit

/-- Self-checks (a)–(c): the sentinel witnesses, the DISCRIMINATION verdicts, and the CLASSIFIER
verdicts. Split out from `surface` because none of them needs the keystone corpus — they are
properties of the instrument, and they must be runnable (and demonstrable) without a whole-tree
build. `surface` runs them too; nothing is checked in only one place. -/
def selfTest (ws : Array FreeWitness) : MetaM Unit := do
  let env ← getEnv
  -- (a) the three sentinels must be REDISCOVERED by the derivation.
  for s in sentinelWitnesses do
    if (env.find? s).isNone then
      throwError "FREE-CONCLUSION FAIL-CLOSED: sentinel freeness witness {s} is not in the \
        environment. Either it was renamed/deleted (update `sentinelWitnesses` in the same commit \
        as the port that removed the break event) or this module is being elaborated without the \
        module that holds it, in which case the gate is measuring a partial tree."
    unless ws.any (fun w => w.thm == s) do
      throwError "FREE-CONCLUSION FAIL-CLOSED: sentinel freeness witness {s} EXISTS but the \
        derivation did not rediscover it. The derivation has gone blind — every break event of \
        that family is now ungated and this gate would pass on the exact statements it was built \
        to catch. Fix the derivation, do not delete the sentinel."
  -- (a') the BARE pattern must still be derived from those witnesses (§2b).
  for s in bareSentinelWitnesses do
    let some w := ws.find? (fun w => w.thm == s)
      | throwError "FREE-CONCLUSION FAIL-CLOSED: bare-pattern sentinel {s} is not among the derived \
        witnesses at all — see the `sentinelWitnesses` error above for the two ways that happens."
    if w.bareHeads.isEmpty then
      throwError "FREE-CONCLUSION FAIL-CLOSED: {s} is still a freeness witness but no longer arms a \
        BARE pattern. `barePatternOf` reads `?P ∨ B` off the witness's own conclusion and hands back \
        `B`; if that stopped working, a declaration whose conclusion IS the free break event — \
        undisjoined — reads CLEAN again, which is the blind spot this rule was written to close \
        (`CommitFaithfulRegrounded.stateBreak_faithful_reduces`, measured blind on 2026-08-01). \
        Fix the derivation, do not delete the sentinel."
  -- (b) the discrimination test must not have degenerated in either direction.
  for (spec, want) in witnessSpecimenVerdicts do
    let some ci := env.find? spec
      | throwError "FREE-CONCLUSION FAIL-CLOSED: witness specimen {spec} is not in the environment."
    let (doms, body) := peelForall ci.type #[]
    let iffForm := (iffTrueSide? body).isSome
    let arb := (arbitraryBranch? doms body).isSome
    let got := (iffForm || arb) && !(← isGeneric ci.type iffForm)
    unless got == want do
      throwError "FREE-CONCLUSION FAIL-CLOSED: witness specimen {spec} classified \
        {if got then "ACCEPTED" else "REJECTED"}, expected \
        {if want then "ACCEPTED" else "REJECTED"}. The DISCRIMINATION gate has degenerated. \
        Accepting too much arms the gate with `?P ∨ ?Break`, which flags every disjunction in the \
        tree; accepting too little disarms whole break families. Both read as a green build with a \
        different number."
  -- (c) the classifier must not have degenerated in either direction.
  for (spec, want) in classifierSpecimenVerdicts do
    let some ci := env.find? spec
      | throwError "FREE-CONCLUSION FAIL-CLOSED: classifier specimen {spec} is not in the \
        environment (it lives in `Dregg2.Verify.FreeConclusionSpecimens`; the invoking module must \
        import it)."
    let some val := ci.value?
      | throwError "FREE-CONCLUSION FAIL-CLOSED: classifier specimen {spec} is not a def."
    let got := (← scanType ws spec val).isSome
    unless got == want do
      throwError "FREE-CONCLUSION FAIL-CLOSED: classifier specimen {spec} classified \
        {if got then "FLAGGED" else "CLEAN"}, expected {if want then "FLAGGED" else "CLEAN"}. \
        ⚑ If `specPerInstanceResidual` is the one that moved, the gate is now flagging the \
        campaign's own REPAIR — the per-instance residual at a NAMED pair — and porting has just \
        become a build error. ⚑ If `specBreakClaimed` is the one that moved, the BARE rule has \
        eaten the pigeonhole REFUTATION that arms this whole gate, which is the failure that made \
        the bare class look terminal in the first place. Fix the classifier; do not weaken the \
        specimen."

/-- Derive the witness set, run every self-check, and classify the tagged corpus. Hard-errors on any
fail-closed condition BEFORE reporting, so a blind instrument can never report a clean surface. -/
def surface : MetaM Surface := do
  let env ← getEnv
  let ws ← deriveWitnesses
  selfTest ws
  -- (d) scale.
  let ks := ((keystoneExt.getState env).toList.map Prod.fst).toArray
  let ks := ks.qsort (fun x y => x.toString < y.toString)
  if ks.size < minKeystones then
    throwError "FREE-CONCLUSION FAIL-CLOSED: only {ks.size} @[load_bearing_keystone] declarations \
      are visible (expected ≥ {minKeystones}). The invoking module is missing `KeystoneAudit*` \
      imports, so the gate is measuring a fraction of the corpus and every count reads low — which \
      is indistinguishable from a clean tree."
  let mut hits : Array Hit := #[]
  for k in ks do
    let some ci := env.find? k | continue
    if let some h ← scanType ws k ci.type then
      hits := hits.push h
  return { witnesses := ws, keystones := ks, hits }

/-- Compare the live surface against `grandfathered`. A new free conclusion is a hard error. -/
def check : MetaM Unit := do
  let s ← surface
  let base : Std.HashSet String := grandfathered.foldl (fun a r => a.insert r) {}
  let fresh := s.hits.filter (fun h => !base.contains (hitKey h))
  let slack := grandfathered.filter (fun r => !s.hits.any (fun h => hitKey h == r))
  -- Printed BEFORE any `throwError`: `throwError` discards the command's message log, and the run
  -- you most need the derived witness set on is the RED one.
  let wlines := String.intercalate "\n" (s.witnesses.toList.map fun w =>
    s!"  {w.thm}  [{w.shape}]")
  logInfo s!"free-conclusion: {s.witnesses.size} DERIVED freeness witness(es) arming the gate over \
    {s.keystones.size} tagged keystone(s):\n{wlines}"
  unless fresh.isEmpty do
    let env ← getEnv
    let body := String.intercalate "\n" (fresh.toList.map fun h =>
      s!"    {h.subject}\n      module: {moduleOf env h.subject}\n      \
        free subterm: {h.subterm}\n      proved free by: {h.witness}  [{h.shape}]" ++
      (if h.detail.isEmpty then ""
       else s!"\n      ⚑ BARE: the conclusion IS the free event. This hypothesis does no work — the \
witness proves the conclusion without it:\n        {h.detail}"))
    let paste := String.intercalate ",\n" (fresh.toList.map fun h => s!"  \"{hitKey h}\"")
    throwError "\n\
      ⚑ FREE-CONCLUSION RATCHET: {fresh.size} registered keystone(s) CONCLUDE something this \
      tree PROVES is satisfied unconditionally.\n\
      \n\
      The named subterm is not a weakened claim — it is `True`. The break event is a GLOBAL \
      EXISTENTIAL, and the same pigeonhole that refutes the injectivity floor these statements \
      were ported OFF of ESTABLISHES it, at every field-bounded (= every deployed) sponge. The \
      keystone therefore constrains nothing, and it will have passed `#keystone_audit` HONESTLY: \
      the satisfiability witness fires, the teeth refute a hostile instance, and neither check \
      looks at the conclusion's information content.\n\
      \n\
      A hit marked ⚑ BARE has no disjunction at all: its CONCLUSION is the free event, and the \
      named hypothesis is dead weight. The fix is the same port — return the residual AT THE NAMED \
      PAIR (`SpongeColl hash a b`, `RecStateCommitColl …`) instead of the global existential — \
      except that here there is no good branch to keep, so the statement is a `_toGlobal` bridge \
      and the question is whether anything should be reading it as a guarantee at all.\n\
      \n{body}\n\
      \n\
      Two ways forward.\n\
      \n\
      1. PORT IT — the only real one. Replace the global break event with a PER-INSTANCE residual \
         at the exact pair the extraction visits, and state it UNCONDITIONALLY:\n\
         \n\
             …  →  concl ∨ Coll hash a b          -- `a`, `b` NAMED by the statement\n\
         \n\
         The shape is a TOTAL EXTRACTOR returning the specific colliding pair, an unconditional \
         `_or_collides` naming that pair, and a per-instance `¬ Coll … p` bound where the claim is \
         made. Worked, landed, and carrying all three teeth: `Circuit/AggregationAirSound.lean`, \
         `Circuit/MapPathCutoverCheck.lean`, `Circuit/StateCommitLeafRegrounded.lean` \
         (`RecStateCommitColl`). `SpongeCollisionShirk.noSpongeColl_of_spongeCR` is the bridge, so \
         the ported statement is strictly STRONGER than the one it replaces.\n\
         \n\
         ⚠ THREE THINGS THAT LOOK LIKE THE FIX AND ARE NOT, each proved free in this tree:\n\
           • `P ∨ Break` with `Break` a GLOBAL existential — that is this error.\n\
           • a UNIVERSALLY QUANTIFIED side condition `∀ xs ys, ¬ Coll xs ys` — that is injectivity \
             rewritten, and `#floor_ratchet` will bill you for it instead.\n\
           • a residual quantified OUTSIDE the claim: `(∀ a b, …) ∨ (∃ x y, …)` is free, while \
             `∀ a b, h a = h b → a = b ∨ Coll h a b` prices each instance. Same symbols, opposite \
             content.\n\
      \n\
      2. GRANDFATHER IT, VISIBLY. If the port genuinely cannot happen now, paste the rows below \
         into `grandfathered` in `Dregg2/Verify/FreeConclusionRatchet.lean` and say in the commit \
         WHY. Each row is a claim, on the record, that a registered load-bearing keystone \
         knowingly concludes something unconditional. The baseline is EMPTY as this gate lands and \
         its only healthy direction is to stay that way.\n\
      \n\
      ⚑ REPOINTING THE KEYSTONE ONTO A DIFFERENT THEOREM IS NOT A FIX UNLESS THE NEW ONE IS \
      PER-INSTANCE. `KeystoneAuditUnfoolability` (7) was repointed TWICE and the FIRST repoint \
      landed on another free-disjunct statement — same instrument, same PASS, same nothing.\n\
      \n{paste}\n"
  unless slack.isEmpty do
    logInfo s!"free-conclusion: {slack.size} baseline row(s) are SLACK (no longer free — the port \
      landed). Delete them:\n  {String.intercalate "\n  " slack.toList}"
  logInfo s!"free-conclusion OK — {s.keystones.size} tagged keystone(s) scanned, \
    {s.hits.size} with a free conclusion, baseline {grandfathered.size}, \
    {s.witnesses.size} derived freeness witnesses. ⚠ This gate only reaches break events the tree \
    has ALREADY PROVED free; a clean run is not a soundness result."

/-! ## §8 — the commands -/

/-- `#free_conclusion_ratchet` — THE GATE. Throws if any tagged keystone concludes a disjunction
this tree proves free and is not grandfathered. Invoke it where the WHOLE tagged corpus is in
scope. -/
elab "#free_conclusion_ratchet" : command =>
  liftTermElabM <| check.run'

/-- `#free_conclusion_report` — the same scan, never throws. For surveying the corpus (and for
producing the baseline) without failing a build. -/
elab "#free_conclusion_report" : command =>
  liftTermElabM <| (do
    let s : Surface ← surface
    let wlines := String.intercalate "\n" (s.witnesses.toList.map fun (w : FreeWitness) =>
      s!"  {w.thm}  [{w.shape}]")
    let hlines :=
      if s.hits.isEmpty then "  (none)"
      else String.intercalate "\n" (s.hits.toList.map fun (h : Hit) =>
        s!"  \"{hitKey h}\"\n     free subterm: {h.subterm}" ++
        (if h.detail.isEmpty then "" else s!"\n     ⚑ BARE; idle hypothesis: {h.detail}"))
    logInfo s!"free-conclusion REPORT\n\
      {s.witnesses.size} derived freeness witness(es):\n{wlines}\n\
      {s.keystones.size} tagged keystone(s); {s.hits.size} with a FREE conclusion:\n{hlines}").run'

/-- `#free_conclusion_probe K` — classify ONE declaration, tagged or not. Never throws.

This is the question an author should be able to ask BEFORE registering a keystone ("is the
disjunction I just wrote free?"), and it is how the gate is demonstrated against the historical
statements: `#free_conclusion_probe Dregg2.Distributed.HistoryAggregation.verified_history_conserves_orBreak`
names the exact subterm that fooled `#keystone_audit`. -/
elab "#free_conclusion_probe" k:ident : command => do
  let subject ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo k
  liftTermElabM <| (do
    let ws : Array FreeWitness ← deriveWitnesses
    let env ← getEnv
    let some ci := env.find? subject
      | throwError "#free_conclusion_probe: {subject} is not in the environment."
    match ← scanType ws subject ci.type with
    | some h =>
      let extra :=
        if h.detail.isEmpty then ""
        else s!"\n  ⚑ BARE — the conclusion IS the free event, and this hypothesis does no work \
(the witness proves the conclusion without it): {h.detail}"
      logInfo s!"⚑ FREE CONCLUSION — {subject}\n  free subterm : {h.subterm}\n  \
        proved free by: {h.witness}  [{h.shape}]{extra}\n  \
        This statement is satisfied unconditionally at the parameters that witness assumes."
    | none =>
      logInfo s!"free-conclusion: no free conclusion found in {subject} — no free disjunct, and no \
        bare break event either. ⚠ That is a NEGATIVE result against {ws.size} derived witnesses, \
        not a soundness result — a break event nobody has proved free yet is invisible here.").run'

/-- `#free_conclusion_selftest` — run the instrument's OWN checks (sentinels rediscovered,
discrimination verdicts, classifier verdicts) with no keystone corpus in scope. Throws on any
failure. This is what makes the classifier demonstrable from a module-scoped build. -/
elab "#free_conclusion_selftest" : command =>
  liftTermElabM <| (do
    let ws : Array FreeWitness ← deriveWitnesses
    selfTest ws
    logInfo s!"free-conclusion SELF-TEST PASS — {sentinelWitnesses.length} sentinel witness(es) \
      rediscovered, {bareSentinelWitnesses.length} of them still arming a BARE pattern, \
      {witnessSpecimenVerdicts.length} discrimination verdict(s) held, \
      {classifierSpecimenVerdicts.length} classifier verdict(s) held, over {ws.size} derived \
      witnesses.").run'

/-- `#free_conclusion_witnesses` — print only what the derivation armed the gate with. The
counterpart of `#floor_ratchet_floors`: a derived instrument must be able to say what it derived. -/
elab "#free_conclusion_witnesses" : command =>
  liftTermElabM <| (do
    let ws : Array FreeWitness ← deriveWitnesses
    let wlines := String.intercalate "\n" (ws.toList.map fun (w : FreeWitness) =>
      s!"  {w.thm}  [{w.shape}]  heads: {w.heads.toList}\n     bare: \
{if w.bareHeads.isEmpty then "(none — arms no bare pattern)" else toString w.bareHeads.toList}")
    logInfo s!"free-conclusion DERIVED WITNESSES ({ws.size})\n{wlines}").run'

end Dregg2.Verify.FreeConclusionRatchet
