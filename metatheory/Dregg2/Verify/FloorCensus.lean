/-
# Dregg2.Verify.FloorCensus — the elaborated-term floor census (`#floor_census`).

The instrument that supersedes `scripts/binding_surface_complete.py` (a TEXT-over-source
regex ruler, historically wrong in both directions: blind to 7 of 10 refuted floors, credited
per-file discharges across unrelated objects, and originally FAILED OPEN on a bad path).
This census reads the ELABORATED environment instead: real binder positions, real constant
identity, and the actual PROOF TERM, so endpoint-vs-threader is a subterm predicate rather
than a 12-character regex context.

Passes (all READ-ONLY over the imported environment):

* **Pass 0 — floor DISCOVERY, no hand list.** Every `Prop`-valued `def` in our modules whose
  body δ-matches an injectivity shape (`… → f a = f b → a = b`, or a conjunction-of-equalities
  multi-target variant) is a candidate floor. A hand-maintained list is how the Python ruler
  went blind; the shape is the fact.
* **Pass 0b — REFUTED-ness is mechanical.** A candidate `F` is refuted iff the environment
  holds a theorem whose telescope body is `¬ F …`, or whose body is `False` with a binder of
  type `F …`. The `_false_babyBear` naming convention is never consulted — the TYPE is.
  A refutation whose refuted instance is CLOSED (no telescope fvars in `F`'s arguments) is
  flagged `instance`; an open one is `parametric`.
* **Pass 1 — CARRIER census.** For every constant in our modules: the refuted floors bound in
  HYPOTHESIS position of its elaborated type (section `variable`s are already `forallE`s here
  — no scope emulation), classified against the proof term:
    - `endpoint` — some subterm applies the floor hypothesis to arguments (the hypothesis is
      ELIMINATED; re-pointing it is a real re-proof). Includes `absurd`-elimination and floor
      hypotheses whose application happens inside a compiler-lifted auxiliary (`_proof_N`,
      `._unary`, `.match_N`) — those are chased transitively (`aux-endpoint` flag), because a
      `def` building a structure PASSES the floor at the def and APPLIES it inside the aux.
    - `threader` — the hypothesis occurs but only ever as an ARGUMENT to another constant:
      a statement rewrite once its endpoint is ported.
    - `dead` — the proof term never touches it (droppable, modulo conclusion occurrence).
    - `no-value` — axiom/opaque/ctor/recursor carriers (no proof term to classify).
    - `tooth` — telescope body is `False`: refutation teeth and reduction-to-floor
      theorems stated contradiction-style. A distinct class, never dropped (the underlying
      proof-term class is kept as a `was-*` flag).
  Structural classes, no allow-lists: a conclusion whose head is itself a floor is a
  BRIDGE (kept, flagged `bridge`).
* **Bundles.** Structure FIELDS typed at a floor are found via projections
  (`getProjectionStructureName?` + floor-headed forall-body) and reported as `BUNDLE`/`PROJ`.
* **The `Function.Injective` blind spot.** `Poseidon2SpongeCR f` is defeq to
  `Function.Injective f`, so a binder spelled `Function.Injective` can carry the same refuted
  content invisibly to every name-keyed ruler. Sites whose binder δ-matches the injectivity
  shape under the `Function.Injective` spelling (and bind no named floor) are reported as
  `SHAPE` lines — the leak surface, kept distinct from the named census.
* **Floor-flow DAG.** `T → c` iff `T`'s proof passes its floor hypothesis fvar as an argument
  to `c` (the floor's flow, not the proof's general dependency cone). Longest-path levels by
  fixpoint drive the port wave plan.

## FAIL-CLOSED, by construction
A census over a half-imported environment reports fewer carriers and looks exactly like
progress (the Python ruler's original fail-open defect, one level up). `#floor_census` hard-
errors — no output, nonzero exit — unless (a) the environment holds ≥ 500 000 constants
(whole-tree scale), (b) every SENTINEL floor name resolves, and (c) every sentinel that the
tree refutes is seen as refuted by Pass 0b. A count that reads lower must come from a landed
port, never from an instrument that quietly measured less.

## Output (machine-readable, TSV, one record per line)
  `FLOOR   name refuted witness closed? named?`
  `CARRIER name module file startLine endLine kind class conc level floors flags`
  `BUNDLE  struct` / `PROJ proj struct floor`
  `SHAPE   name module file line injective-head`
  `SUMMARY key value`
Usage: `#floor_census` (stdout) or `#floor_census "/abs/path/out.tsv"` (file + summary).

This tool only MEASURES. It proves nothing, ports nothing, and a clean report means "the
stated assumptions are not provably false in-tree" — not a verified system.
-/
import Lean

set_option autoImplicit false

namespace Dregg2.Verify.FloorCensus

open Lean Meta Elab Command

/-- The modules the census measures (the metatheory's own trees, not Lean/Mathlib). -/
def ourModule (m : Name) : Bool :=
  let s := m.toString
  s.startsWith "Dregg2" || s.startsWith "Market" || s.startsWith "Bfv"
    || s.startsWith "Metatheory" || s.startsWith "Polis"

/-- SENTINELS: floors the census must SEE for its report to mean anything.
The `Bool` is `true` iff the tree holds a refutation Pass 0b must rediscover
(BindingHashCR is refuted only at a chosen bad instance — presence-required only). -/
def sentinelFloors : List (Name × Bool) :=
  [ (`Dregg2.Circuit.StateCommit.compressNInjective, true)
  , (`Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR, true)
  , (`Dregg2.Circuit.StateCommit.compressInjective, true)
  , (`Dregg2.Circuit.StateCommit.logHashInjective, true)
  , (`Dregg2.Circuit.StateCommit.cellLeafInjective, true)
  , (`Dregg2.Crypto.Lattice.MSISHard, true)
  , (`Dregg2.Circuit.HashFloorHonesty.CollisionResistant, true)
  , (`Dregg2.Exec.Factory.HashInjective, true)
  , (`Dregg2.Crypto.CommitmentBinding.Compress1CR, true)
  , (`Dregg2.Circuit.DeployedCapTree.Compress8CR, true)
  , (`Dregg2.Crypto.HermineHintMLWE.HashCR, true)
  , (`Dregg2.Apps.PreRotation.KeySetCR, true)
  , (`Dregg2.Apps.QueueRoot.RootCR, true)
  , (`Dregg2.Apps.QueueRoot.LeafCR, true)
  , (`Dregg2.Apps.QueueRoot.PairCR, true)
  , (`Dregg2.Apps.QueueRoot.LenBindCR, true)
  , (`Dregg2.Authority.MacaroonDischarge.BindingHashCR, false)
  ]

/-- Defining module of a constant (core-API only; `getModuleFor?` is a Mathlib add-on). -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]?.getD `«?»
  | none => `«current»

def headConst? (e : Expr) : Option Name :=
  match e.getAppFn with | .const n _ => some n | _ => none

/-- `Eq _ l r` (syntactic). -/
def eqPair? (e : Expr) : Option (Expr × Expr) :=
  match e with
  | .app (.app (.app (.const ``Eq _) _) l) r => some (l, r)
  | _ => none

def notArg? (e : Expr) : Option Expr :=
  match e with
  | .app (.const ``Not _) p => some p
  | _ => none

def concShape (b : Expr) : String :=
  match headConst? b with
  | some ``Eq => "eq" | some ``Iff => "iff" | some ``False => "False"
  | some ``Or => "or" | some ``And => "and" | some ``Exists => "exists"
  | some ``Not => "not" | some ``Ne => "ne" | some _ => "opaque-pred"
  | none => if b.isForall then "forall" else "other"

/-- Compiler-lifted / internal names (`_proof_N`, `._unary`, `.match_N`, …). -/
def isInternalName (n : Name) : Bool :=
  n.isInternal || (n.toString.splitOn "._").length > 1

/-- Auto-generated companions with no source token of their own (`eq_def`, `injEq`, …) —
flagged so the source-diff can bucket them; never silently excluded. -/
def isAutoCompanion (n : Name) : Bool :=
  match n with
  | .str _ s =>
    s == "eq_def" || s == "injEq" || s == "sizeOf_spec" || s == "noConfusion"
      || s == "noConfusionType" || s.startsWith "match_" || s.startsWith "proof_"
      || (s.startsWith "eq_" && (s.drop 3).all Char.isDigit)
  | _ => false

/-- Transport/elimination sinks: a floor fvar passed here is being USED via a motive,
not threaded to a lemma. Flagged (`transport`) and routed to a human, never silently
reclassified — `simp`-generated `Eq.mpr` chains are ambiguous in both directions. -/
def transportSinks : List Name :=
  [``Eq.mpr, ``Eq.mp, ``Eq.rec, ``Eq.ndrec, ``Eq.subst, ``eq_of_heq, ``cast, ``False.elim]

/-! ## Pass 0 — injectivity-shape discovery -/

/-- `∀ …, (… f a = f b …) → a = b` — a binder equation that becomes the conclusion's
equation under `a ↦ b` substitution. -/
def injShape (t : Expr) : MetaM Bool := do
  try
    forallTelescope t fun xs body => do
      if xs.size < 3 then return false
      let some (l, r) := eqPair? body | return false
      let .fvar a := l | return false
      let .fvar b := r | return false
      for x in xs do
        let hy ← inferType x
        if let some (hl, hr) := eqPair? hy then
          if hl != hr && (hl.replaceFVarId a (.fvar b)) == hr then return true
      return false
  catch _ => return false

/-- Conjunction of fvar equalities (the `compressInjective` multi-target shape). -/
partial def eqsOnly (e : Expr) : Bool :=
  match e with
  | .app (.app (.const ``And _) l) r => eqsOnly l && eqsOnly r
  | _ => match eqPair? e with
         | some (.fvar _, .fvar _) => true
         | _ => false

def injShapeAnd (t : Expr) : MetaM Bool := do
  try
    forallTelescope t fun xs body => do
      if xs.size < 3 then return false
      unless body.isAppOf ``And do return false
      unless eqsOnly body do return false
      for x in xs do
        if (eqPair? (← inferType x)).isSome then return true
      return false
  catch _ => return false

/-! ## Proof-term visitor -/

structure VisitOut where
  applied : Bool := false
  used : Bool := false
  /-- `(c, i)`: a floor fvar passed as argument `i` of an application headed by `c`. -/
  edges : Array (Name × Nat) := #[]

def visitValue (fvs : Array FVarId) (v : Expr) : MetaM VisitOut := do
  let stA ← IO.mkRef false
  let stU ← IO.mkRef false
  let stE ← IO.mkRef (#[] : Array (Name × Nat))
  let _ ← Meta.transform v (pre := fun s => do
    match s with
    | .fvar fv =>
      if fvs.contains fv then stU.set true
      return .continue
    | .app .. =>
      let args := s.getAppArgs
      match s.getAppFn with
      | .fvar fv => if fvs.contains fv && args.size > 0 then stA.set true
      | .const c _ =>
        for i in [0:args.size] do
          if let .fvar fv := args[i]! then
            if fvs.contains fv then
              stE.modify (fun a => if a.contains (c, i) then a else a.push (c, i))
      | _ => pure ()
      return .continue
    | _ => return .continue)
  return { applied := ← stA.get, used := ← stU.get, edges := ← stE.get }

/-- Chase a floor argument INTO a compiler-lifted auxiliary: is it APPLIED in there
(transitively), and which NON-internal constants does it flow to from inside? This is what
makes `accountsComponent`-shaped defs endpoints instead of mis-read threaders, and what
keeps `listComponent → ListDigestBindsList` in the DAG when the flow is hidden inside a
lifted `_proof_N`. Fuel-bounded, memoized. -/
partial def auxResolve (memo : IO.Ref (Std.HashMap (Name × Nat) (Bool × Array Name)))
    (fuel : Nat) (c : Name) (idx : Nat) : MetaM (Bool × Array Name) := do
  if fuel == 0 then return (false, #[])
  if let some r := (← memo.get).get? (c, idx) then return r
  let env ← getEnv
  let some info := env.find? c | return (false, #[])
  let some v := info.value? (allowOpaque := true) | return (false, #[])
  let r ← forallTelescope info.type fun xs _ => do
    if idx < xs.size then
      let fv := xs[idx]!.fvarId!
      let vo ← visitValue #[fv] (v.beta xs)
      let mut applied := vo.applied
      let mut ext : Array Name := #[]
      for (c', i') in vo.edges do
        if c' == ``absurd then applied := true
        else if isInternalName c' then
          let (a', e') ← auxResolve memo (fuel - 1) c' i'
          if a' then applied := true
          for x in e' do
            if !ext.contains x then ext := ext.push x
        else
          if !ext.contains c' then ext := ext.push c'
      return (applied, ext)
    else
      return (false, #[])
  memo.modify (·.insert (c, idx) r)
  return r

/-! ## The census -/

structure Site where
  name : Name
  mod : Name
  kind : String
  cls : String
  conc : String
  floors : Array Name
  edges : Array Name
  flags : Array String
  startLine : Nat
  endLine : Nat
  deriving Inhabited

def declKind : ConstantInfo → String
  | .thmInfo _ => "thm" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque" | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .quotInfo _ => "quot"

def modFile (m : Name) : String :=
  (m.toString.replace "." "/") ++ ".lean"

def fmtNames (ns : Array Name) : String :=
  if ns.isEmpty then "-" else ",".intercalate (ns.toList.map (·.toString))

def fmtFlags (fs : Array String) : String :=
  if fs.isEmpty then "-" else ",".intercalate fs.toList

def run (outPath : Option String) : MetaM Unit := do
  let env ← getEnv
  let consts := env.constants
  let mut allNames : Array Name := consts.foldStage2 (fun acc n _ => acc.push n) #[]
  allNames := consts.map₁.fold (fun acc n _ => acc.push n) allNames
  let total := allNames.size
  -- ⚑ FAIL-CLOSED gate (a): whole-tree scale. A partial import measures less and looks
  -- like progress; refuse to report at all.
  if total < 500000 then
    throwError "FLOOR-CENSUS FAIL-CLOSED: only {total} constants in the environment \
      (whole-tree is ~915k). Partial import — refusing to emit a census that would \
      under-count carriers."
  -- ⚑ FAIL-CLOSED gate (b): every sentinel floor resolves.
  for (f, _) in sentinelFloors do
    unless env.contains f do
      throwError "FLOOR-CENSUS FAIL-CLOSED: sentinel floor {f} is not in the \
        environment. Partial import or renamed floor — refusing to report."

  let mut ours : Array Name := #[]
  for nm in allNames do
    if isInternalName nm then continue
    if ourModule (moduleOf env nm) then ours := ours.push nm

  -- ===== Pass 0: discover injectivity-shaped Prop defs =====
  let mut cand : Array Name := #[]
  for nm in ours do
    let some ci := env.find? nm | continue
    let .defnInfo di := ci | continue
    let hit ← forallTelescope di.type fun xs body => do
      unless body == .sort .zero do return false
      let b := di.value.beta xs
      if ← injShape b then return true
      injShapeAnd b
    if hit then cand := cand.push nm
  -- named sentinels join the candidate set whatever their shape (MSISHard is `¬∃`-shaped)
  let mut candSet : NameSet := cand.foldl (·.insert ·) {}
  for (f, _) in sentinelFloors do
    if !candSet.contains f then
      candSet := candSet.insert f
      cand := cand.push f

  -- ===== Pass 0b: refutation witnesses =====
  -- ⚑ Only a `¬ F …`-CONCLUSION theorem is a refutation WITNESS of `F`. A theorem
  -- `(h : F …) → X → False` proves ¬(F ∧ X), not ¬F — it is a TOOTH (cure machinery,
  -- excluded from the carrier surface below) but never the recorded refutation, and it
  -- never satisfies the sentinel gate.
  let mut refutedBy : Std.HashMap Name (Name × Bool) := {}  -- floor ↦ (¬-witness, closed?)
  let mut falseForm : Std.HashMap Name Name := {}           -- floor ↦ a False-under-hyps tooth
  for nm in ours do
    let some ci := env.find? nm | continue
    let .thmInfo _ := ci | continue
    let (negs, falses) ← forallTelescope ci.type fun xs body => do
      let mut negs : Array (Name × Bool) := #[]
      let mut falses : Array Name := #[]
      if let some arg := notArg? body then
        if let some h := headConst? arg then
          if candSet.contains h then negs := negs.push (h, !arg.hasFVar)
      if body.isAppOf ``False then
        for x in xs do
          let ty ← inferType x
          if let some h := headConst? ty then
            if candSet.contains h then falses := falses.push h
      return (negs, falses)
    for (h, closed) in negs do
      if !refutedBy.contains h then refutedBy := refutedBy.insert h (nm, closed)
    for h in falses do
      if !falseForm.contains h then falseForm := falseForm.insert h nm
  -- ⚑ FAIL-CLOSED gate (c): sentinels the tree refutes must be SEEN refuted (¬-form).
  for (f, needRefut) in sentinelFloors do
    if needRefut && !refutedBy.contains f then
      throwError "FLOOR-CENSUS FAIL-CLOSED: sentinel floor {f} has no visible in-tree \
        ¬-conclusion refutation. Partial import (refutation module missing) or a genuine \
        regression — either way, refusing to report a smaller floor set."

  let floors : NameSet := refutedBy.fold (fun a f _ => a.insert f) {}
  let mut lines : Array String := #[]
  for f in cand do
    let named := sentinelFloors.any (·.1 == f)
    match refutedBy.get? f with
    | some (wit, closed) =>
      lines := lines.push
        s!"FLOOR\t{f}\trefuted\t{wit}\t{if closed then "instance" else "parametric"}\t{if named then "named" else "discovered"}"
    | none =>
      match falseForm.get? f with
      | some tooth =>
        lines := lines.push
          s!"FLOOR\t{f}\tFALSE-UNDER-HYPS-ONLY\t{tooth}\t-\t{if named then "named" else "discovered"}"
      | none =>
        lines := lines.push
          s!"FLOOR\t{f}\tUNREFUTED\t-\t-\t{if named then "named" else "discovered"}"

  -- ===== Pass 1: carriers =====
  let memo ← IO.mkRef ({} : Std.HashMap (Name × Nat) (Bool × Array Name))
  let mut sites : Array Site := #[]
  let mut bundles : Array (Name × Name × Name) := #[]   -- (proj, struct, floor)
  let mut shapes : Array (Name × Name × Name) := #[]    -- (site, mod, injective-at head)
  for nm in ours do
    let some info := env.find? nm | continue
    if floors.contains nm then continue
    let mod := moduleOf env nm
    -- structure FIELD typed at a floor, seen through its projection
    if let some h := headConst? info.type.getForallBody then
      if floors.contains h then
        if let some sn := env.getProjectionStructureName? nm then
          bundles := bundles.push (nm, sn, h)
    let tyC := info.type.getUsedConstants
    let hasNamed := tyC.any (fun c => floors.contains c)
    let maybeShape := tyC.contains ``Function.Injective
    unless hasNamed || maybeShape do continue
    let res ← forallTelescope info.type fun xs body => do
      let mut fvs : Array FVarId := #[]
      let mut fls : Array Name := #[]
      let mut flags : Array String := #[]
      let mut shapeHits : Array Name := #[]
      for x in xs do
        let ld ← x.fvarId!.getDecl
        match headConst? ld.type with
        | some h =>
          if floors.contains h then
            fvs := fvs.push x.fvarId!
            if !fls.contains h then fls := fls.push h
            if ld.binderInfo == .instImplicit && !flags.contains "instImp" then
              flags := flags.push "instImp"
          else if h == ``Function.Injective then
            -- record EVERY `Function.Injective`-spelled binder (the leak surface); the
            -- injected function's head const when it has one, `«fun»`/`«fvar»` otherwise
            let fh := match ld.type.getAppArgs.back? with
              | some f => match f.getAppFn with
                | .const fn _ => fn
                | .fvar _ => `«fvar»
                | .lam .. => `«fun»
                | _ => `«other»
              | none => `«other»
            shapeHits := shapeHits.push fh
        | none => pure ()
      if fvs.isEmpty then
        return some (Sum.inl shapeHits)
      if !shapeHits.isEmpty then flags := flags.push "inj-spelled"
      -- body `False` = the TOOTH class: refutation teeth AND reduction-to-floor theorems
      -- stated contradiction-style (`Floor → forgery → False`). NOT dropped — a distinct
      -- class inside the carrier surface, so no site the text ruler counts goes invisible.
      let isTooth := body.isAppOf ``False
      let conc := concShape body
      if (headConst? body).any floors.contains then flags := flags.push "bridge"
      if fvs.any body.containsFVar then flags := flags.push "conc-floor"
      if isAutoCompanion nm then flags := flags.push "auto-name"
      let mut cls := "no-value"
      let mut edges : Array Name := #[]
      if let some v := info.value? (allowOpaque := true) then
        let v' := v.beta xs
        let uc := v'.getUsedConstants
        if uc.contains ``Eq.mpr || uc.contains ``of_eq_true then flags := flags.push "simp"
        let vo ← visitValue fvs v'
        for (c, _) in vo.edges do
          if !edges.contains c then edges := edges.push c
        cls := if vo.applied then "endpoint" else if vo.used then "threader" else "dead"
        if !vo.applied && vo.used then
          -- absurd-elimination and aux-lifted application are USES, not threads; and a
          -- floor flowing THROUGH an aux to a real carrier is an edge the DAG must keep
          for (c, i) in vo.edges do
            if c == ``absurd then
              cls := "endpoint"
              if !flags.contains "absurd-use" then flags := flags.push "absurd-use"
            else if isInternalName c then
              let (applied, ext) ← auxResolve memo 8 c i
              if applied then
                cls := "endpoint"
                if !flags.contains "aux-endpoint" then flags := flags.push "aux-endpoint"
              for x in ext do
                if !edges.contains x then edges := edges.push x
          if vo.edges.any (fun (c, _) => transportSinks.contains c) then
            flags := flags.push "transport"
      if isTooth then
        flags := flags.push s!"was-{cls}"
        cls := "tooth"
      return some (Sum.inr (Site.mk nm mod (declKind info) cls conc fls edges flags 0 0))
    match res with
    | none => pure ()
    | some (Sum.inl shapeHits) =>
      for fh in shapeHits do shapes := shapes.push (nm, mod, fh)
    | some (Sum.inr s) =>
      let (l0, l1) ← match ← findDeclarationRanges? nm with
        | some rg => pure (rg.range.pos.line, rg.range.endPos.line)
        | none => pure (0, 0)
      sites := sites.push { s with startLine := l0, endLine := l1 }

  -- ===== floor-flow DAG levels =====
  let carrierSet : NameSet := sites.foldl (fun a s => a.insert s.name) {}
  let mut level : Std.HashMap Name Nat := {}
  let mut changed := true
  let mut iters := 0
  while changed && iters < 300 do
    changed := false
    iters := iters + 1
    for s in sites do
      let mut lv := 0
      for e in s.edges do
        if carrierSet.contains e then lv := max lv ((level.getD e 0) + 1)
      if lv != level.getD s.name 0 then
        level := level.insert s.name lv
        changed := true
  if iters >= 300 then
    throwError "FLOOR-CENSUS FAIL-CLOSED: floor-flow level fixpoint did not converge \
      (cycle in the flow graph?) — refusing to emit a wave plan from a broken DAG."

  let sorted := sites.qsort (fun a b =>
    a.mod.toString < b.mod.toString
      || (a.mod.toString == b.mod.toString && a.startLine < b.startLine))
  for s in sorted do
    lines := lines.push
      (s!"CARRIER\t{s.name}\t{s.mod}\t{modFile s.mod}\t{s.startLine}\t{s.endLine}\t" ++
       s!"{s.kind}\t{s.cls}\t{s.conc}\t{level.getD s.name 0}\t{fmtNames s.floors}\t{fmtFlags s.flags}")
  let mut structSeen : Array Name := #[]
  for (p, sn, fl) in bundles do
    if !structSeen.contains sn then structSeen := structSeen.push sn
    lines := lines.push s!"PROJ\t{p}\t{sn}\t{fl}"
  for sn in structSeen do
    lines := lines.push s!"BUNDLE\t{sn}"
  for (n, m, fh) in shapes do
    let (l0, _) ← match ← findDeclarationRanges? n with
      | some rg => pure (rg.range.pos.line, rg.range.endPos.line)
      | none => pure (0, 0)
    lines := lines.push s!"SHAPE\t{n}\t{m}\t{modFile m}\t{l0}\t{fh}"
  -- every OUR module in the imported closure — the source-diff's in-env oracle
  for m in env.header.moduleNames do
    if ourModule m then lines := lines.push s!"MODULE\t{m}"

  -- ===== summary =====
  let mut summary : Array String := #[]
  summary := summary.push s!"SUMMARY\tconstants\t{total}"
  summary := summary.push s!"SUMMARY\tour-constants\t{ours.size}"
  summary := summary.push s!"SUMMARY\tcandidate-floors\t{cand.size}"
  summary := summary.push s!"SUMMARY\trefuted-floors\t{floors.size}"
  summary := summary.push s!"SUMMARY\tcarriers\t{sites.size}"
  for cl in ["endpoint", "threader", "dead", "no-value", "tooth"] do
    summary := summary.push s!"SUMMARY\tclass-{cl}\t{(sites.filter (·.cls == cl)).size}"
  summary := summary.push s!"SUMMARY\tbridges\t{(sites.filter (·.flags.contains "bridge")).size}"
  summary := summary.push s!"SUMMARY\tconc-floor\t{(sites.filter (·.flags.contains "conc-floor")).size}"
  summary := summary.push s!"SUMMARY\taux-endpoints\t{(sites.filter (·.flags.contains "aux-endpoint")).size}"
  summary := summary.push s!"SUMMARY\tbundle-structs\t{structSeen.size}"
  summary := summary.push s!"SUMMARY\tbundle-projs\t{bundles.size}"
  summary := summary.push s!"SUMMARY\tshape-only-injective-sites\t{shapes.size}"
  let mut perFloor : Std.HashMap Name Nat := {}
  for s in sites do
    for f in s.floors do perFloor := perFloor.insert f ((perFloor.getD f 0) + 1)
  for (f, c) in perFloor.toList do
    summary := summary.push s!"SUMMARY\tfloor-carriers\t{f}\t{c}"
  let mut lvHist : Std.HashMap Nat Nat := {}
  for s in sites do
    let lv := level.getD s.name 0
    lvHist := lvHist.insert lv ((lvHist.getD lv 0) + 1)
  for (lv, c) in lvHist.toList.toArray.qsort (fun a b => a.1 < b.1) do
    summary := summary.push s!"SUMMARY\tlevel-{lv}\t{c}"

  match outPath with
  | some p =>
    IO.FS.writeFile p ("\n".intercalate ((lines ++ summary).toList) ++ "\n")
    for l in summary do IO.println l
    IO.println s!"floor-census: {sites.size} carriers → {p}"
  | none =>
    for l in lines ++ summary do IO.println l

/-- `#floor_census` / `#floor_census "/abs/out.tsv"` — the elaborated-term floor census
over everything imported at the point of invocation. Fails CLOSED (hard error, no output)
on partial imports. See the module docstring for the record format. -/
elab "#floor_census" out:(str)? : command => do
  let p := out.map (·.getString)
  liftTermElabM (Dregg2.Verify.FloorCensus.run p)

end Dregg2.Verify.FloorCensus
