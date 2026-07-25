/-
# Dregg2.Tools.ConePort — the mechanical S3 threader port (elaborated-term analysis, kernel-checked
generation, fail-closed everywhere).

## What this is

The vacuity-elimination campaign replaces theorems that CARRY a refuted floor hypothesis (an
infinite-domain injectivity that is FALSE at deployed BabyBear parameters) with S3 forms: the SAME
conclusion, the floor binder swapped for a per-instance, refutable `¬ Coll` side condition
instantiated at the exact arguments the proof passes. The ENDPOINT of a cone is re-proved by hand
(`Circuit/ListCommitRegrounded` is the exemplar); this tool ports the THREADERS mechanically:

  1. **ANALYSIS on the elaborated term** — real binder positions, the real proof term, the actual
     argument expressions at every floor-passing application. Never a regex.
  2. **SURGERY on the proof `Expr`** — each application of the old endpoint is replaced by the
     ported lemma, with the floor argument dropped and the instantiated side condition threaded.
  3. **VERIFICATION before emission** — `Meta.check`, `inferType ≟ intended statement`, and a real
     `addDecl` (the KERNEL accepts the port or the site is refused). Then delaboration with a
     mandatory ROUND-TRIP (re-elaborate the printed text, `isDefEq` against the built `Expr`);
     delaboration is not injective, and a port that prints as a different theorem is exactly the
     silent-weakening failure mode.
  4. **EMISSION as source** — the artifact under review is the generated `.lean` file, which
     re-verifies everything at `lake build` and carries its own `#assert_axioms` /
     `#assert_not_depends_on` pins.

## What it REFUSES (fail closed, loudly; a refusal is a correct answer, never a warning)

  * the floor hypothesis is APPLIED to arguments (the theorem is an ENDPOINT — needs a hand S2);
  * the floor flows to a consumer with no registered port rule (an unported cone edge);
  * a floor-passing application sits under a proof-local binder (`fun`/motive), so the side
    condition would need quantification the tool cannot invent (LEAKY — needs a human);
  * the floor occurs in the CONCLUSION or in a later binder's type (re-pointing changes the
    statement shape — a real consequence, reported, never papered over);
  * partial application of the ported endpoint; residual floor dependence after surgery; kernel
    rejection; delaboration round-trip failure.

A port may only make the measurement MORE true: the driver (`Tools/ConePortListCommitRun`) pins the
expected outcome of every site in the cluster and turns any drift into a BUILD ERROR.
-/
import Lean
import Dregg2.Tactics

namespace Dregg2.Tools.ConePort

open Lean Meta Elab

set_option autoImplicit false

/-! ## §1 — configuration: port rules. -/

/-- **A port rule**: how one application of `orig` (at full `arity`, with floor-hypothesis
arguments exactly at `floorIdxs`, all of them BARE floor-binder fvars) is rewritten into an
application of `repl`. `argMap` lists, in `repl`'s argument order, which `orig` argument each slot
takes; `none` marks the side-condition slot, whose instantiated binder type (read off `repl`'s own
telescope — never rebuilt by hand) becomes a hypothesis of the ported theorem. -/
structure AppRule where
  orig : Name
  arity : Nat
  floorIdxs : Array Nat
  repl : Name
  argMap : Array (Option Nat)
  /-- human tag for the report (`noColl` / `noCNColl` / …). -/
  tag : String
  deriving Inhabited

/-- The tool's configuration: the floor constants whose binders are eliminated, the rules table,
and the suffix for generated names. -/
structure PortConfig where
  floors : List Name
  rules : List AppRule
  suffix : String := "_of_noColl"
  /-- namespace the generated theorems are declared under. -/
  genNamespace : Name
  /-- constants every generated port must NOT reach (emitted as `#assert_not_depends_on` pins and
  checked in-tool via `Dregg2.findForbiddenPath` semantics at build). -/
  forbidden : List Name

/-! ## §2 — analysis results. -/

structure SiteRecord where
  site : Expr
  rule : AppRule
  args : Array Expr
  levels : List Level
  sideCond : Expr
  deriving Inhabited

structure PortResult where
  origName : Name
  newName : Name
  tags : List String
  nSites : Nat
  nSideConds : Nat
  typeTxt : String
  proofTxt : String
  /-- proof text needed the fully-explicit fallback printer. -/
  explicitFallback : Bool
  docTxt : String
  deriving Inhabited

inductive Outcome where
  | ported (r : PortResult)
  | refused (reason : String)
  deriving Inhabited

/-! ## §3 — the walker: find every floor-relevant node of the proof term. -/

private partial def stripMData : Expr → Expr
  | .mdata _ b => stripMData b
  | .app f a => .app (stripMData f) (stripMData a)
  | .lam n t b i => .lam n (stripMData t) (stripMData b) i
  | .forallE n t b i => .forallE n (stripMData t) (stripMData b) i
  | .letE n t v b nd => .letE n (stripMData t) (stripMData v) (stripMData b) nd
  | .proj s i b => .proj s i (stripMData b)
  | e => e

private def isFloorFVar (floorFVars : Array FVarId) (e : Expr) : Bool :=
  match e with
  | .fvar fv => floorFVars.contains fv
  | _ => false

private def containsFloor (floorFVars : Array FVarId) (e : Expr) : Bool :=
  floorFVars.any e.containsFVar

/-- Walk the (mdata-stripped, telescope-instantiated) proof term. Records every full application
of a ruled constant that consumes a floor fvar; records a refusal for every OTHER contact with a
floor fvar (ALL of them — the diagnosis must not depend on traversal order). Recursion under
binders is deliberate — sites found there carry loose bvars and are refused at side-condition
construction (the LEAKY class). -/
private partial def walk (cfg : PortConfig) (floorFVars : Array FVarId)
    (sites : IO.Ref (Array (AppRule × Expr × Array Expr × List Level)))
    (bad : IO.Ref (Array String)) : Expr → MetaM Unit := fun e => do
  unless containsFloor floorFVars e do return
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const c lvls =>
      let matching := cfg.rules.filter (fun r => r.orig == c)
      if !matching.isEmpty then
        let some r0 := matching.head? | unreachable!
        if args.size < r0.arity then
          bad.modify (·.push s!"PARTIAL application of ported endpoint `{c}` ({args.size} < {r0.arity} args) touches the floor — cannot rewrite structurally")
          return
        -- find the first rule whose floor positions are exactly bare floor fvars and whose
        -- retained positions are floor-free.
        let rule? := matching.find? (fun r =>
          r.floorIdxs.all (fun i => i < args.size && isFloorFVar floorFVars args[i]!) &&
          (List.range r.arity).all (fun j =>
            r.floorIdxs.contains j || !containsFloor floorFVars args[j]!))
        match rule? with
        | some r =>
          sites.modify (·.push (r, e, args, lvls))
          -- recurse into retained args only (floor args are consumed by the rewrite).
          for j in [0:args.size] do
            unless r.floorIdxs.contains j do walk cfg floorFVars sites bad args[j]!
        | none =>
          bad.modify (·.push s!"application of `{c}` touches the floor in an unruled position — route to human")
      else
        -- not a ruled head: a BARE floor fvar argument is a pass to an unported consumer.
        if args.any (isFloorFVar floorFVars) then
          let cls := if c.isInternal || (c.toString.splitOn "._").length > 1 then
            s!"floor hypothesis flows into COMPILER-LIFTED AUX `{c}` (a structure-field/match lift) — needs transitive aux contraction; the BUNDLE is the port unit here, route to human"
          else
            s!"floor hypothesis PASSED to unported consumer `{c}` — port that consumer first (DAG order) or route to human"
          bad.modify (·.push cls)
        else
          for a in args do walk cfg floorFVars sites bad a
    | .fvar fv =>
      if floorFVars.contains fv then
        bad.modify (·.push "floor hypothesis APPLIED to arguments — this is an ENDPOINT; it needs a hand-written extractor (S2), not a mechanical port")
      else
        if args.any (isFloorFVar floorFVars) then
          bad.modify (·.push "floor hypothesis passed to a LOCAL function — route to human")
        else do
          walk cfg floorFVars sites bad f
          for a in args do walk cfg floorFVars sites bad a
    | _ =>
      walk cfg floorFVars sites bad f
      for a in args do walk cfg floorFVars sites bad a
  | .fvar fv =>
    if floorFVars.contains fv then
      bad.modify (·.push "floor hypothesis referenced outside any portable application (stored in a structure / motive / transport) — route to human")
  | .lam _ t b _ => do walk cfg floorFVars sites bad t; walk cfg floorFVars sites bad b
  | .forallE _ t b _ => do walk cfg floorFVars sites bad t; walk cfg floorFVars sites bad b
  | .letE _ t v b _ => do
      walk cfg floorFVars sites bad t; walk cfg floorFVars sites bad v
      walk cfg floorFVars sites bad b
  | .proj _ _ b => walk cfg floorFVars sites bad b
  | .mdata _ b => walk cfg floorFVars sites bad b
  | _ => return

/-! ## §4 — side-condition instantiation, read off the replacement lemma's own telescope. -/

/-- Instantiate `repl`'s telescope along `argMap` with this site's arguments; the binder type at
the `none` slot — with every preceding binder instantiated — IS the side condition. Fails if the
replacement's shape does not match (fail closed). -/
private def sideCondOf (env : Environment) (r : AppRule) (lvls : List Level)
    (args : Array Expr) : Except String Expr := do
  let some info := env.find? r.repl | throw s!"replacement `{r.repl}` not found"
  unless info.levelParams.length == lvls.length do
    throw s!"replacement `{r.repl}` universe arity mismatch"
  let mut ty := info.instantiateTypeLevelParams lvls
  let mut cond? : Option Expr := none
  for slot in r.argMap do
    let .forallE _ dom body _ := ty
      | throw s!"replacement `{r.repl}` telescope shorter than argMap"
    match slot with
    | some i =>
      unless i < args.size do throw "argMap index out of range"
      ty := body.instantiate1 args[i]!
    | none =>
      if cond?.isSome then throw "argMap has more than one side-condition slot"
      cond? := some dom
      -- the side condition is a Prop; later binders cannot depend on its proof in a way that
      -- matters for instantiation, but fail closed if they do.
      if body.hasLooseBVars then
        ty := body.instantiate1 (mkConst ``True.intro)  -- placeholder, only to keep walking
      else
        ty := body
  match cond? with
  | some c => return c
  | none => throw s!"rule for `{r.orig}` has no side-condition slot"

/-- Build the replacement application for one site, given the fvar of its side condition. -/
private def replAppOf (r : AppRule) (lvls : List Level) (args : Array Expr) (hno : Expr) : Expr :=
  let replArgs := r.argMap.map (fun | some i => args[i]! | none => hno)
  mkAppN (mkConst r.repl lvls) replArgs

/-! ## §5 — delaboration + round trip. -/

private def ppWith (opts : Options → Options) (e : Expr) : MetaM String := do
  withOptions opts do
    let fmt ← Meta.ppExpr e
    return toString (fmt.pretty (width := 100))

private def baseOpts (o : Options) : Options :=
  (o.setBool `pp.fullNames true).setBool `pp.funBinderTypes true

private def explicitOpts (o : Options) : Options :=
  ((baseOpts o).setBool `pp.explicit true).setBool `pp.universes true

/-- Re-elaborate printed text and `isDefEq` it against the intended `Expr`. Any error, leftover
metavariable, or `sorry` is a round-trip FAILURE. Monomorphic declarations only (the driver refuses
universe-polymorphic targets before reaching here). -/
private def roundTrips (txt : String) (expectedTy? : Option Expr) (intended : Expr) :
    TermElabM Bool := do
  let env ← getEnv
  match Parser.runParserCategory env `term txt with
  | .error _ => return false
  | .ok stx =>
    try
      Term.withoutErrToSorry do
        let e ← Term.elabTerm stx expectedTy?
        Term.synthesizeSyntheticMVarsNoPostponing
        let e ← instantiateMVars e
        if e.hasExprMVar || e.hasSorry then return false
        isDefEq e intended
    catch _ => return false

/-! ## §6 — the port of one declaration. -/

def portName (cfg : PortConfig) (n : Name) : Name :=
  -- keep the parent-namespace tail for collision-freedom and auditability:
  -- Dregg2.Circuit.Foo.bar ↦ <genNamespace>.Foo.bar<suffix>
  let tail := match n with
    | .str p s =>
      let parentTail := match p with
        | .str _ ps => Name.mkSimple ps
        | _ => Name.anonymous
      parentTail ++ Name.mkSimple (s ++ cfg.suffix)
    | _ => Name.mkSimple ("anon" ++ cfg.suffix)
  cfg.genNamespace ++ tail

def portDecl (cfg : PortConfig) (n : Name) : TermElabM Outcome := do
  let env ← getEnv
  let some info := env.find? n
    | return .refused "declaration not found (partial environment? FAIL CLOSED)"
  let some v := info.value? (allowOpaque := true)
    | return .refused "no proof term available (axiom/opaque) — nothing to analyze"
  forallTelescope info.type fun xs body => do
    -- locate floor binders.
    let mut floorFVars : Array FVarId := #[]
    let mut floorNames : Array Name := #[]
    for x in xs do
      let ld ← x.fvarId!.getDecl
      if let .const h _ := ld.type.getAppFn then
        if cfg.floors.contains h then
          floorFVars := floorFVars.push x.fvarId!
          floorNames := floorNames.push ld.userName
    if floorFVars.isEmpty then
      return .refused "no floor binder in the telescope — not a carrier (nothing to port)"
    -- the conclusion must not mention the floor.
    if containsFloor floorFVars body then
      return .refused "floor occurs in the CONCLUSION — the honest re-point changes the statement shape; route to human"
    -- no retained binder's type may depend on a floor binder.
    for x in xs do
      unless floorFVars.contains x.fvarId! do
        let ld ← x.fvarId!.getDecl
        if containsFloor floorFVars ld.type then
          return .refused s!"binder `{ld.userName}`'s type depends on the floor binder — route to human"
    -- align the proof term with the telescope and walk it.
    let vb := stripMData (v.beta xs)
    let sites ← IO.mkRef (#[] : Array (AppRule × Expr × Array Expr × List Level))
    let bad ← IO.mkRef (#[] : Array String)
    walk cfg floorFVars sites bad vb
    let bads ← bad.get
    unless bads.isEmpty do
      -- prefer the ENDPOINT diagnosis (an applied floor dominates any incidental threading),
      -- then the aux-sink diagnosis; report the count of distinct contacts either way.
      let hasSub : String → String → Bool := fun sub s => (s.splitOn sub).length > 1
      let pick := (bads.find? (hasSub "ENDPOINT")).getD
        ((bads.find? (hasSub "AUX")).getD bads[0]!)
      return .refused s!"{pick} [{bads.size} floor contact(s) outside portable sites]"
    let recs ← sites.get
    if recs.isEmpty then
      -- the floor binder is DEAD in the proof; deletion, not porting, is the right move — and it
      -- is a different wave with its own guard. Refuse here.
      return .refused "floor binder is DEAD in the proof term — a Wave −1 deletion, not an S3 port"
    unless info.levelParams.isEmpty do
      return .refused s!"universe-polymorphic target ({recs.size} portable site(s) found) — the emission harness is monomorphic; route to human"
    -- build side conditions; refuse on loose bvars (LEAKY) or non-telescope fvars.
    let teleSet : FVarIdSet := xs.foldl (fun s x => s.insert x.fvarId!) {}
    let mut sited : Array SiteRecord := #[]
    for (r, site, args, lvls) in recs do
      match sideCondOf env r lvls args with
      | .error e => return .refused s!"side-condition construction failed: {e}"
      | .ok cond =>
        if cond.hasLooseBVars then
          return .refused "LEAKY: floor-passing application under a proof-local binder — the side condition needs quantification the tool cannot invent; route to human"
        let st := Lean.collectFVars {} cond
        for fv in st.fvarIds do
          unless teleSet.contains fv do
            return .refused "LEAKY: side condition mentions a proof-local hypothesis — route to human"
        sited := sited.push { site, rule := r, args, levels := lvls, sideCond := cond }
    -- dedup side conditions (structural first, isDefEq to catch printer-identical twins).
    let mut conds : Array Expr := #[]
    let mut condIdx : Array Nat := #[]
    for s in sited do
      let mut found : Option Nat := none
      for i in [0:conds.size] do
        if found.isNone then
          if conds[i]! == s.sideCond || (← isDefEq conds[i]! s.sideCond) then
            found := some i
      match found with
      | some i => condIdx := condIdx.push i
      | none => conds := conds.push s.sideCond; condIdx := condIdx.push (conds.size - 1)
    -- introduce the side-condition binders and perform the surgery.
    let condDecls : Array (Name × (Array Expr → TermElabM Expr)) :=
      (Array.range conds.size).map (fun i =>
        (Name.mkSimple (if conds.size == 1 then "hno" else s!"hno{i+1}"),
         fun _ => pure conds[i]!))
    withLocalDeclsD condDecls fun hnos => do
      let mut pairs : Array (Expr × Expr) := #[]
      for i in [0:sited.size] do
        let s := sited[i]!
        let newApp := replAppOf s.rule s.levels s.args hnos[condIdx[i]!]!
        pairs := pairs.push (s.site, newApp)
      let pairsList := pairs
      let newBody := vb.replace (fun e =>
        (pairsList.find? (fun p => p.1 == e)).map (·.2))
      for fv in floorFVars do
        if newBody.containsFVar fv then
          return .refused "RESIDUAL floor dependence after surgery (a nested or aliased use survived) — route to human"
      let retained := xs.filter (fun x => !floorFVars.contains x.fvarId!)
      let newTele := retained ++ hnos
      let newType ← instantiateMVars (← mkForallFVars newTele body)
      let newProof ← instantiateMVars (← mkLambdaFVars newTele newBody)
      -- verify: Meta.check + type agreement + KERNEL.
      try Meta.check newProof
      catch ex => return .refused s!"Meta.check rejected the surgered proof: {← ex.toMessageData.toString}"
      let inferred ← inferType newProof
      unless (← isDefEq inferred newType) do
        return .refused "surgered proof does not prove the intended statement — fail closed"
      let newName := portName cfg n
      try
        addDecl (.thmDecl { name := newName, levelParams := [], type := newType, value := newProof })
      catch ex =>
        return .refused s!"KERNEL rejected the port: {← ex.toMessageData.toString}"
      -- delaborate + mandatory round trip (base printer, then fully-explicit fallback).
      let tyTxtBase ← ppWith baseOpts newType
      let prTxtBase ← ppWith baseOpts newProof
      let tyOkBase ← roundTrips tyTxtBase none newType
      let prOkBase ← if tyOkBase then roundTrips prTxtBase (some newType) newProof else pure false
      let mut typeTxt := tyTxtBase
      let mut proofTxt := prTxtBase
      let mut fallback := false
      unless tyOkBase && prOkBase do
        let tyTxtEx ← ppWith explicitOpts newType
        let prTxtEx ← ppWith explicitOpts newProof
        let tyOkEx ← roundTrips tyTxtEx none newType
        let prOkEx ← if tyOkEx then roundTrips prTxtEx (some newType) newProof else pure false
        unless tyOkEx && prOkEx do
          return .refused "delaboration ROUND-TRIP failure (both printers) — emitting nothing; route to human"
        typeTxt := tyTxtEx
        proofTxt := prTxtEx
        fallback := true
      let tags := (sited.map (·.rule.tag)).toList.eraseDups
      let floorList := String.intercalate ", " (floorNames.toList.map (s!"`{·}`"))
      let doc := s!"⚙ MACHINE-PORTED (`Tools/ConePort`) from `{n}` — S3: floor binder(s) {floorList} \
replaced by {conds.size} instantiated per-instance side condition(s) [{String.intercalate ", " tags}]; \
conclusion UNCHANGED, proof surgered at {sited.size} site(s), kernel-checked and round-tripped. \
HONEST-BUT-CONDITIONAL: the port is conditional on the deployed hash not colliding at the NAMED \
per-instance points — refutable, decidable per instance, never universal."
      return .ported {
        origName := n, newName, tags, nSites := sited.size, nSideConds := conds.size,
        typeTxt, proofTxt, explicitFallback := fallback, docTxt := doc }

/-! ## §7 — the cluster driver: expectations, report, emission. -/

inductive Expected where
  | port
  | refuse (substr : String)

structure Target where
  decl : Name
  expected : Expected

def emitModule (cfg : PortConfig) (imports : List Name) (results : Array PortResult)
    (header : String) : String := Id.run do
  let mut out := s!"/-\n{header}\n-/\n"
  for i in imports do
    out := out ++ s!"import {i}\n"
  out := out ++ s!"\nnamespace {cfg.genNamespace}\n\nset_option autoImplicit false\n"
  for r in results do
    let localName := r.newName.replacePrefix cfg.genNamespace Name.anonymous
    out := out ++ s!"\n/-- {r.docTxt} -/\ntheorem {localName} :\n    {r.typeTxt} :=\n  {r.proofTxt}\n"
    out := out ++ s!"#assert_axioms {r.newName}\n"
    let bads := String.intercalate ", " (cfg.forbidden.map toString)
    out := out ++ s!"#assert_not_depends_on {r.newName} [{bads}]\n"
  out := out ++ s!"\nend {cfg.genNamespace}\n"
  return out

structure ClusterReport where
  ported : Array PortResult := #[]
  refusals : Array (Name × String) := #[]
  mismatches : Array String := #[]

def runCluster (cfg : PortConfig) (targets : List Target) : TermElabM ClusterReport := do
  let mut rep : ClusterReport := {}
  for t in targets do
    let outcome ← portDecl cfg t.decl
    match outcome, t.expected with
    | .ported r, .port =>
      rep := { rep with ported := rep.ported.push r }
      let fb := if r.explicitFallback then ", explicit-fallback" else ""
      logInfo m!"PORTED  {t.decl} → {r.newName}  [sites={r.nSites}, sideConds={r.nSideConds}, tags={r.tags}{fb}]"
    | .refused reason, .refuse sub =>
      rep := { rep with refusals := rep.refusals.push (t.decl, reason) }
      if (reason.splitOn sub).length > 1 then
        logInfo m!"REFUSED (expected) {t.decl}: {reason}"
      else
        let msg := s!"{t.decl}: refused for an UNEXPECTED reason: {reason} (expected …{sub}…)"
        rep := { rep with mismatches := rep.mismatches.push msg }
    | .ported r, .refuse _ =>
      let msg := s!"{t.decl}: PORTED but was pinned as a refusal — the ruler moved; update the pin only after reading why (new name {r.newName})"
      rep := { rep with mismatches := rep.mismatches.push msg }
    | .refused reason, .port =>
      let msg := s!"{t.decl}: REFUSED but was pinned as portable: {reason}"
      rep := { rep with mismatches := rep.mismatches.push msg }
  return rep

end Dregg2.Tools.ConePort
