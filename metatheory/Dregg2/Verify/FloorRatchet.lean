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
directly or through a `Prop`-def whose BODY carries one. Three surfaces, all gated:

  * **binder** — `theorem foo (hCR : Poseidon2SpongeCR hash) : …`. The visible class.
  * **prop-body** — `def descriptorRefines … : Prop := Poseidon2SpongeCR hash → …`. The floor
    is in the def's VALUE, so its users have NO floor binder and are invisible to every
    binder-keyed ruler. The census found ~250 carriers hiding behind three such defs
    (`descriptorRefines`, `descriptorComplete`, `ClosedLogExtract`); the set is closed to a
    fixpoint, so a def-of-a-def is caught too.
  * **bundle/field** — a structure FIELD typed at a floor makes the structure UNINHABITABLE
    at deployed parameters. Projections and `mk` are kept in the scan for exactly this reason
    (the other compiler companions — `casesOn`, `recOn`, `injEq`, `eq_def`, … — are dropped as
    noise; their parent is always caught).

EXEMPT, because it is ANTI-floor content and the campaign wants MORE of it, not less: a
declaration whose conclusion is `¬ Floor …` (a refutation witness) or `False` (a tooth /
reduction stated contradiction-style). Writing a new refutation never trips the gate.

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
REDISCOVERED as refuted by the derivation above, and (d) the three `prop-body` keystone gates
are rediscovered. It shares those sentinels with `#floor_census` so the two instruments cannot
drift apart.

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

set_option autoImplicit false

namespace Dregg2.Verify.FloorRatchet

open Lean Meta Elab Command
open Dregg2.Verify.FloorCensus
  (ourModule moduleOf isInternalName headConst? notArg? injShape injShapeAnd
   sentinelFloors sentinelPropBody)

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

/-- ANTI-floor content, exempt from the gate: a conclusion of `¬ Floor …` (a refutation
witness) or `False` (a tooth / a reduction stated contradiction-style). The campaign wants
these written, so the gate must never make writing one a build error. Read off the TYPE's
forall body syntactically — no naming convention is consulted. -/
def isAntiFloor (floors : NameSet) (ty : Expr) : Bool :=
  let b := ty.getForallBody
  match notArg? b with
  | some arg => match headConst? arg with
                | some h => floors.contains h
                | none   => false
  | none => b.isAppOf ``False

/-- A declaration that violates (or is grandfathered under) the ratchet. -/
structure Carrier where
  name  : Name
  floor : Name          -- the refuted floor, or the `prop-body` def, it carries
  cls   : String        -- "binder" | "prop-body" | "propdef-user"
  deriving Inhabited

structure Surface where
  floors    : Array Name           -- refuted floors, DERIVED from the environment
  propBody  : Array Name           -- Prop defs carrying a floor in their BODY (fixpoint)
  carriers  : Array Carrier        -- sorted by name
  shapeLeak : Nat                  -- `Function.Injective`-spelled sites (reported, ungated)
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

  -- ===== `prop-body` carriers: `def … : Prop := Floor … → …`, closed to a fixpoint =====
  let mut propDefs : Array (Name × Array Name) := #[]
  for nm in ours do
    let some ci := env.find? nm | continue
    let .defnInfo di := ci | continue
    if floors.contains nm then continue
    unless isPropValued di.type do continue
    propDefs := propDefs.push (nm, di.value.getUsedConstants)
  let mut pb : NameSet := {}
  let mut pbArr : Array Name := #[]
  let mut iters := 0
  let mut changed := true
  while changed && iters < 100 do
    changed := false
    iters := iters + 1
    for (nm, used) in propDefs do
      if pb.contains nm then continue
      if used.any (fun c => floors.contains c || pb.contains c) then
        pb := pb.insert nm
        pbArr := pbArr.push nm
        changed := true
  if iters >= 100 then
    throwError "FLOOR-RATCHET FAIL-CLOSED: the prop-body fixpoint did not converge."
  -- (d) the three load-bearing prop-body keystone gates must be rediscovered
  for f in sentinelPropBody do
    unless pb.contains f do
      throwError "FLOOR-RATCHET FAIL-CLOSED: prop-body sentinel {f} was not discovered as a \
        floor-carrying Prop def. The ~250 carriers that hang off it invisibly would all pass \
        the gate. Refusing to run."

  -- ===== the carrier surface =====
  let mut carriers : Array Carrier := #[]
  let mut shapeLeak := 0
  for nm in ours do
    if isGeneratedCompanion nm then continue
    if floors.contains nm then continue
    let some ci := env.find? nm | continue
    if isAntiFloor floors ci.type then continue
    if pb.contains nm then
      carriers := carriers.push ⟨nm, nm, "prop-body"⟩
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
    let (floorHit, pbHit, injSeen) :=
      ci.type.foldConsts (none, none, false) fun c (fh, ph, inj) =>
        ( if fh.isNone && floors.contains c then some c else fh
        , if ph.isNone && pb.contains c then some c else ph
        , inj || c == ``Function.Injective )
    if let some f := floorHit then
      carriers := carriers.push ⟨nm, f, "binder"⟩
    else if let some f := pbHit then
      carriers := carriers.push ⟨nm, f, "propdef-user"⟩
    else if injSeen then
      shapeLeak := shapeLeak + 1
  let sorted := carriers.qsort (fun a b => a.name.toString < b.name.toString)
  return { floors := floorArr.qsort (fun a b => a.toString < b.toString)
           propBody := pbArr, carriers := sorted, shapeLeak, total }

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
      2. STATE IT AS ANTI-FLOOR CONTENT. A declaration concluding `¬ Floor …` or `False` is \
         exempt by construction — refutations and reductions never trip this gate.\n\
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
  logInfo s!"floor-ratchet OK — {s.carriers.size} grandfathered carriers over \
    {s.floors.size} refuted floors ({s.propBody.size} prop-body defs); baseline \
    {baseline.size}, slack {slack.size}; {s.shapeLeak} `Function.Injective`-spelled sites \
    ungated (known residual); {s.total} constants."

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
  let byCls := fun k => (s.carriers.filter (fun c => c.cls == k)).size
  logInfo s!"floor-ratchet DERIVED SURFACE\n\
    refuted floors ({s.floors.size}), with carrier counts:\n\
    {String.intercalate "\n" lines.toList}\n\
    prop-body Prop defs ({s.propBody.size}): \
    {String.intercalate ", " (s.propBody.toList.map (·.toString))}\n\
    carriers {s.carriers.size} = binder {byCls "binder"} + prop-body {byCls "prop-body"} \
    + propdef-user {byCls "propdef-user"}\n\
    ungated `Function.Injective`-spelled sites: {s.shapeLeak}\n\
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
    Dregg2.Verify.FloorRatchetBaseline.grandfathered)

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
    Dregg2.Verify.FloorRatchetBaseline.grandfathered path.getString false)

/-- `#floor_ratchet_emit! "…"` — RAISE the ratchet: grandfather every current carrier,
including new ones. A different token on purpose, and the result is ADDED LINES in a
reviewable diff. Use only when a new declaration genuinely cannot be built without a refuted
floor, and say why in the commit message. -/
elab "#floor_ratchet_emit!" path:str : command =>
  liftTermElabM (Dregg2.Verify.FloorRatchet.emit
    Dregg2.Verify.FloorRatchetBaseline.grandfathered path.getString true)

end Dregg2.Verify.FloorRatchet
