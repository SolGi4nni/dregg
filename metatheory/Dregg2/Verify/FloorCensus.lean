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
* **Pass 1b — floor in a Prop-def BODY (census v2).** `def … : Prop := Floor … → …` carries a
  floor with NO floor binder in its type — invisible to every binder test (the
  `descriptorRefines`/`descriptorComplete`/`ClosedLogExtract` keystone shape). Pass 1b
  δ-inspects the VALUE of every Prop-valued def and reports floor-mentioning ones as class
  `prop-body` (flag `direct`, or `via-propdef` when the mention is through another such def —
  computed to fixpoint). Sites that MENTION a `prop-body` def in their own type without any
  direct floor binder are class `propdef-user` (their statements rewrite when the def is
  regrounded); sites whose type names a floor OUTSIDE any binder head (inside a binder's own
  pi, or in the conclusion) are class `embedded` (flags `emb-binder`/`emb-conc`/`neg-conc`;
  a recorded refutation witness is flagged `refut-witness` and is anti-floor content, not
  port surface). v1 silently DROPPED all of these.
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
* **Floor-flow DAG, HIGHER-ORDER-aware (census v2).** `T → c` iff `T`'s proof passes its floor
  hypothesis fvar as an argument to `c` (the floor's flow, not the proof's general dependency
  cone). v1 recorded only `.const`-headed applications, so a proof passing its floor into
  ANOTHER HYPOTHESIS (`hrefines pi.effect hCR …` — the `lightclient_unfoolable` keystone
  shape) showed NO edge and sat at L0. v2 also records floor fvars passed to fvar-headed
  applications (flag `ho-thread`): when the receiving hypothesis's statement head is a
  carrier constant (typically a `prop-body` def) that becomes a DAG edge; otherwise the site
  is flagged `ho-opaque` (level not trustworthy as work order). Floor flow into a
  proof-LOCAL function (bvar/lambda head) is flagged `ho-local`. Statement-level coupling to
  `prop-body` defs is also an edge (the statement rewrites after the def regrounds). Both
  levelings are reported: the CARRIER column and `level-*` histogram use the v2 edges;
  `RELEVEL name old new` lines show every site the correction moved (old = v1 edge
  semantics), so DAG level can be read as work order again.
* **DEAD split (census v2).** `dead` undifferentiated oversold the deletion wave: most dead
  defs are structure projections/`ctorIdx` boilerplate (flag `struct-boiler`) that die only
  when their BUNDLE is ported. The summary splits dead by kind × blocking-flags:
  `dead-thm-clean` is the genuine day-one deletion wave.
* **Multi-floor combinations (census v2).** `COMBO floors n n-threader` lines histogram the
  exact floor COMBINATIONS carried by multi-floor sites, so an AppRule table is designed
  against real combinations rather than one floor at a time.

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
  `RELEVEL name v1-level v2-level` (sites the higher-order edge correction moved)
  `COMBO   floors carriers threaders` (multi-floor combination histogram)
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

/-- ⚑ **A GATE WAS REMOVED HERE ON 2026-07-28, KNOWINGLY, AND THIS IS THE RECORD.**

`Dregg2.Circuit.HashFloorHonesty.CollisionResistant` was a named sentinel with `needRefut = true`.
The `def` is now DELETED (it was `HashCRHardQuant F ⊤` under a name that hid the `⊤`, and that floor
is refuted for every compressing family), so the entry had to go with it: BOTH instruments — this
census and `FloorRatchet` — FAIL CLOSED with a hard error on a sentinel name that does not resolve,
so leaving the entry would red the root for every lane rather than gate anything.

**WHAT IS NO LONGER CAUGHT.** Nothing rediscovers this floor's SHAPE. Pass 0 finds injectivity-shaped
`Prop` defs; `CollisionResistant`'s body was `∀ A : CollisionFinder F, Negl (collisionAdv F A)`,
which is not injectivity-shaped, so the derived half of the census never saw it — the sentinel was
the ONLY thing gating it. So a future author can reintroduce a floor of exactly this shape, under any
name, and neither instrument will say a word. That is a real weakening and it is the cost.

**WHY NOTHING COULD STAND IN.** `Crypto.FloorGames.HashCRHardQuant` cannot take the slot: at a
restricted `Eff` it IS the honest rung 2, and this list is keyed by head constant, so a
`needRefut` entry for it would record `¬ HashCRHardQuant F ⊤` as a refutation of the floor AT EVERY
`Eff` — the instrument would then report every honest rung-2 carrier as sitting on a refuted floor,
which is false. A gate that lies is worse than an absent one.

**WHO DECIDED.** ember, asked directly on 2026-07-27, answering that the `def` goes now — a
check-weakening is on `CLAUDE.md`'s short list reserved for the operator, it was put to them as one,
and this is the authorized outcome, not an accident and not a drift.

**WHAT WOULD RESTORE IT.** A DERIVED detector for the shape `∀ A : <finder-like structure> F,
Negl (<advantage> F A)` — i.e. teaching Pass 0 to recognise "universally quantified over an
unrestricted adversary structure with a negligible advantage" the way it already recognises
injectivity. That is strictly better than a name-keyed sentinel, because it would also catch the
next author who writes the same floor with a fresh structure and a fresh name; a replacement
sentinel entry would only catch the one who reuses this one.

SENTINELS: floors the census must SEE for its report to mean anything.
The `Bool` is `true` iff the tree holds a refutation Pass 0b must rediscover
(BindingHashCR is refuted only at a chosen bad instance — presence-required only). -/
def sentinelFloors : List (Name × Bool) :=
  [ (`Dregg2.Circuit.StateCommit.compressNInjective, true)
  , (`Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR, true)
  , (`Dregg2.Circuit.StateCommit.compressInjective, true)
  , (`Dregg2.Circuit.StateCommit.logHashInjective, true)
  , (`Dregg2.Circuit.StateCommit.cellLeafInjective, true)
  , (`Dregg2.Crypto.Lattice.MSISHard, true)
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

/-- Pass 1b SENTINELS: known load-bearing `Prop`-def-BODY floor carriers the v2 census must
rediscover (each is `def … : Prop := Poseidon2SpongeCR hash → …` — no floor binder in the
type, so a binder-only census reports them as NOT CARRIERS at all). Fail closed if any is
missed: these gate the L0 keystones. -/
def sentinelPropBody : List Name :=
  [ `Dregg2.Circuit.CircuitSoundness.descriptorRefines ]

/-- Pass 1b RATCHET (the INVERSE sentinel): `Prop`-def-body floor carriers that have been PORTED —
their floor antecedent is DELETED — and must never come back. Each name must resolve to a `Prop`-
valued `def` in our modules AND must NOT be discovered as a prop-body floor carrier. Fail closed on
either: a ported def that reappears in `propBody` is the port being reverted, and a name that no
longer resolves is the ratchet quietly losing its grip.

TWO of the three keystone gates fell on 2026-07-25, both by the same finding: the antecedent was DEAD.

* `ClosureAll.ClosedLogExtract` — all 35 rungs discharging a slot bound it `_hCR` and never used it.
* `CircuitCompleteness.descriptorComplete` — every rung is built by `descriptorComplete_of_satFloor`,
  which binds it `_hCR` and never uses it. Completeness CONSTRUCTS its decode; only the soundness
  direction reads a kernel back out of a commitment, and only that direction can be fooled by a
  collision. Porting it let `lightclient_complete` — the completeness apex — shed the floor entirely.

So both ports are DELETIONS, strictly strengthening, needing no bridge lemma. The kernel-defeq shape
pins live in `Circuit/ClosedLogExtractPortCheck`; this list is the census-level half, so an instrument
that reports the class as clean cannot also be the instrument that stopped looking. -/
def portedPropBody : List Name :=
  [ `Dregg2.Circuit.ClosureAll.ClosedLogExtract
  , `Dregg2.Circuit.CircuitCompleteness.descriptorComplete ]

/-- The higher-order-flow SENTINEL: the top keystone that v1 mis-leveled to L0 because its
floor hypothesis flows into ANOTHER hypothesis (`hrefines`), not a constant. v2 must see the
`ho-thread` and level it strictly above 0, or the DAG is not a work order — fail closed. -/
def sentinelHoThread : Name := `Dregg2.Circuit.CircuitSoundness.lightclient_unfoolable

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

/-- Auto-generated STRUCTURE boilerplate: projections and the compiler's per-inductive
companions. A DEAD floor binder here is not a free deletion — it dies only when its whole
bundle is ported (flag `struct-boiler`; the day-one deletion wave must not count these). -/
def isStructBoilerplate (env : Environment) (n : Name) : Bool :=
  (env.getProjectionFnInfo? n).isSome ||
    match n with
    | .str _ s =>
      s == "ctorIdx" || s == "noConfusion" || s == "noConfusionType" || s == "casesOn"
        || s == "recOn" || s == "below" || s == "brecOn" || s == "ibelow"
        || s == "binductionOn" || s == "mk"
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
  /-- HYPOTHESIS fvars (not themselves floor binders) RECEIVING a floor fvar as an
  argument — the higher-order flow v1 was blind to (`hrefines pi.effect hCR …`). -/
  hoSinks : Array FVarId := #[]
  /-- A floor fvar flowed into a proof-LOCAL head (bvar/lambda/projection): higher-order
  flow the site-level binder map cannot resolve. -/
  hoLocal : Bool := false

def visitValue (fvs : Array FVarId) (v : Expr) : MetaM VisitOut := do
  let stA ← IO.mkRef false
  let stU ← IO.mkRef false
  let stE ← IO.mkRef (#[] : Array (Name × Nat))
  let stH ← IO.mkRef (#[] : Array FVarId)
  let stL ← IO.mkRef false
  let isFloorFvar : Expr → Bool := fun e =>
    match e with | .fvar fv => fvs.contains fv | _ => false
  let _ ← Meta.transform v (pre := fun s => do
    match s with
    | .fvar fv =>
      if fvs.contains fv then stU.set true
      return .continue
    | .app .. =>
      let args := s.getAppArgs
      match s.getAppFn with
      | .fvar fv =>
        if fvs.contains fv then
          if args.size > 0 then stA.set true else pure ()
        else if args.any isFloorFvar then
          stH.modify (fun a => if a.contains fv then a else a.push fv)
      | .const c _ =>
        for i in [0:args.size] do
          if let .fvar fv := args[i]! then
            if fvs.contains fv then
              stE.modify (fun a => if a.contains (c, i) then a else a.push (c, i))
      | _ =>
        if args.any isFloorFvar then stL.set true
      return .continue
    | _ => return .continue)
  return { applied := ← stA.get, used := ← stU.get, edges := ← stE.get,
           hoSinks := ← stH.get, hoLocal := ← stL.get }

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
  /-- v2 edges: higher-order flow targets (the receiving hypothesis's statement-head
  carrier) + statement-level coupling to `prop-body` defs. Kept separate from proof-term
  `edges` so both levelings stay computable. -/
  hoEdges : Array Name := #[]
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
  -- `(h : F …) → X → False` proves ¬(F ∧ X), not ¬F — it is a TOOTH (classified as such
  -- in the carrier surface below) but never the recorded refutation, and it never
  -- satisfies the sentinel gate.
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

  -- ===== Pass 1b: floor-in-Prop-def-BODY carriers (census v2) =====
  -- `def … : Prop := Floor … → …` has NO floor binder in its type; the floor lives in the
  -- VALUE. δ-inspect every Prop-valued def's value; close under mention-of-another-such-def.
  let refutWitness : NameSet :=
    falseForm.fold (fun a _ w => a.insert w)
      (refutedBy.fold (fun a _ (w, _) => a.insert w) {})
  let mut propDefs : Array (Name × Array Name) := #[]
  for nm in ours do
    let some ci := env.find? nm | continue
    let .defnInfo di := ci | continue
    if floors.contains nm then continue
    let isProp ← forallTelescope di.type fun _ b => pure (b == .sort .zero)
    unless isProp do continue
    propDefs := propDefs.push (nm, di.value.getUsedConstants)
  let mut propBody : Std.HashMap Name (Array Name) := {}  -- def ↦ floors carried via body
  let mut pbDirect : NameSet := {}
  let mut pbIters := 0
  let mut pbChanged := true
  while pbChanged && pbIters < 100 do
    pbChanged := false
    pbIters := pbIters + 1
    for (nm, used) in propDefs do
      let mut fl : Array Name := propBody.getD nm #[]
      let before := fl.size
      let hadDirect := pbDirect.contains nm
      let mut dir := hadDirect
      for c in used do
        if floors.contains c then
          dir := true
          if !fl.contains c then fl := fl.push c
        else if let some fs := propBody.get? c then
          if c != nm then
            for f in fs do if !fl.contains f then fl := fl.push f
      if fl.size > before || (dir && !hadDirect) then
        propBody := propBody.insert nm fl
        if dir then pbDirect := pbDirect.insert nm
        pbChanged := true
  if pbIters >= 100 then
    throwError "FLOOR-CENSUS FAIL-CLOSED: Pass 1b prop-def-body fixpoint did not converge."
  -- ⚑ FAIL-CLOSED gate (d): the known load-bearing Prop-def-body keystone gates must be seen.
  for f in sentinelPropBody do
    unless propBody.contains f do
      throwError "FLOOR-CENSUS FAIL-CLOSED: Pass 1b sentinel {f} was not discovered as a \
        prop-body floor carrier. Partial import or a regression in the δ-unfolding — a v2 \
        census that misses the keystone gates must not report."
  -- ⚑ FAIL-CLOSED gate (d′), the RATCHET: a PORTED prop-body keystone must still resolve, and must
  -- NOT be a floor carrier again. Landing a port and then letting the floor creep back into the
  -- def's body is the exact regression this campaign keeps paying for, and it is invisible to every
  -- binder-keyed ruler — so the census, which is the only instrument that can see the class, is
  -- where the ratchet has to live.
  for f in portedPropBody do
    unless env.find? f |>.isSome do
      throwError "FLOOR-CENSUS FAIL-CLOSED: ported prop-body keystone {f} is not in the \
        environment. The ratchet cannot certify a port whose subject it cannot resolve — a rename \
        or deletion must update `portedPropBody` in the same commit."
    if propBody.contains f then
      throwError "FLOOR-CENSUS FAIL-CLOSED: PORT REVERTED — {f} is a prop-body floor carrier \
        again, carrying {propBody.getD f #[]}. Its floor antecedent was DELETED by a landed port; \
        a floor back in the def's BODY makes every theorem that merely MENTIONS it a silent \
        carrier with no binder anywhere in its type. Re-do the port, or remove the name from \
        `portedPropBody` and say in the commit that the campaign gave the surface back."

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
    -- v2: statement-level mentions of prop-body defs, and prop-body defs themselves
    let tyPds := tyC.filter (fun c => propBody.contains c)
    let isPB := propBody.contains nm
    unless hasNamed || maybeShape || isPB || !tyPds.isEmpty do continue
    let boiler := isStructBoilerplate env nm
    let (shapeHits, site?) ← forallTelescope info.type fun xs body => do
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
      if boiler then flags := flags.push "struct-boiler"
      if fvs.isEmpty then
        -- ===== v2: sites with NO direct floor binder (all silently dropped by v1) =====
        if isPB then
          -- Pass 1b carrier: floor named in the Prop def's BODY (δ-level).
          let mut hoEdges : Array Name := tyPds
          if let some v := info.value? (allowOpaque := true) then
            for c in v.getUsedConstants do
              if c != nm && propBody.contains c && !hoEdges.contains c then
                hoEdges := hoEdges.push c
          flags := flags.push (if pbDirect.contains nm then "direct" else "via-propdef")
          if refutWitness.contains nm then flags := flags.push "refut-witness"
          return (shapeHits, some (Site.mk nm mod (declKind info) "prop-body"
            (concShape body) (propBody.getD nm #[]) #[] hoEdges flags 0 0))
        if hasNamed then
          -- floor named in the TYPE outside any binder head: conclusion or a binder's pi.
          let mut fls2 : Array Name := tyC.filter (fun c => floors.contains c)
          if (notArg? body).any (fun a => (headConst? a).any floors.contains) then
            flags := flags.push "neg-conc"
          else if body.getUsedConstants.any floors.contains then
            flags := flags.push "emb-conc"
          let mut embBinder := false
          for x in xs do
            let ld ← x.fvarId!.getDecl
            if ld.type.getUsedConstants.any floors.contains then embBinder := true
          if embBinder then flags := flags.push "emb-binder"
          if refutWitness.contains nm then flags := flags.push "refut-witness"
          if !tyPds.isEmpty then flags := flags.push "uses-propdef"
          return (shapeHits, some (Site.mk nm mod (declKind info) "embedded"
            (concShape body) fls2 #[] tyPds flags 0 0))
        if !tyPds.isEmpty then
          -- statement mentions a prop-body carrier: rewrites when the def is regrounded.
          let mut fls2 : Array Name := #[]
          for c in tyPds do
            for f in propBody.getD c #[] do
              if !fls2.contains f then fls2 := fls2.push f
          flags := flags.push "uses-propdef"
          return (shapeHits, some (Site.mk nm mod (declKind info) "propdef-user"
            (concShape body) fls2 #[] tyPds flags 0 0))
        return (shapeHits, none)
      if !shapeHits.isEmpty then flags := flags.push "inj-spelled"
      -- body `False` = the TOOTH class: refutation teeth AND reduction-to-floor theorems
      -- stated contradiction-style (`Floor → forgery → False`). NOT dropped — a distinct
      -- class inside the carrier surface, so no site the text ruler counts goes invisible.
      let isTooth := body.isAppOf ``False
      let conc := concShape body
      if (headConst? body).any floors.contains then flags := flags.push "bridge"
      if fvs.any body.containsFVar then flags := flags.push "conc-floor"
      if isAutoCompanion nm then flags := flags.push "auto-name"
      if isPB then
        flags := flags.push "body-floor"
      if !tyPds.isEmpty then flags := flags.push "uses-propdef"
      let mut hoEdges : Array Name := tyPds
      if isPB then
        for f in propBody.getD nm #[] do
          if !fls.contains f then fls := fls.push f
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
        -- ===== v2: HIGHER-ORDER floor flow (the `lightclient_unfoolable` blind spot) =====
        -- the floor hypothesis passed into ANOTHER hypothesis: resolve the receiving
        -- hypothesis's statement head to a carrier constant when possible (a DAG edge);
        -- an unresolvable receiver makes the site's level untrustworthy (`ho-opaque`).
        unless vo.hoSinks.isEmpty do
          flags := flags.push "ho-thread"
          for g in vo.hoSinks do
            let ty? ← try pure (some (← g.getDecl).type) catch _ => pure none
            let head? := match ty? with
              | some gt => headConst? gt.getForallBody
              | none => none
            match head? with
            | some h =>
              let carrierHead := propBody.contains h || floors.contains h
              if carrierHead && !hoEdges.contains h then
                hoEdges := hoEdges.push h
              if !carrierHead && !flags.contains "ho-opaque" then
                flags := flags.push "ho-opaque"
            | none =>
              if !flags.contains "ho-opaque" then flags := flags.push "ho-opaque"
        if vo.hoLocal && !flags.contains "ho-local" then flags := flags.push "ho-local"
      if isTooth then
        flags := flags.push s!"was-{cls}"
        cls := "tooth"
      return (shapeHits, some (Site.mk nm mod (declKind info) cls conc fls edges hoEdges
        flags 0 0))
    match site? with
    | none =>
      for fh in shapeHits do shapes := shapes.push (nm, mod, fh)
    | some s =>
      -- SHAPE lines stay confined to sites with no direct floor binder (v1 semantics kept:
      -- binder-carrying sites carry `inj-spelled` instead)
      if s.cls == "prop-body" || s.cls == "embedded" || s.cls == "propdef-user" then
        for fh in shapeHits do shapes := shapes.push (nm, mod, fh)
      let (l0, l1) ← match ← findDeclarationRanges? nm with
        | some rg => pure (rg.range.pos.line, rg.range.endPos.line)
        | none => pure (0, 0)
      sites := sites.push { s with startLine := l0, endLine := l1 }

  -- ===== floor-flow DAG levels: v1 edge semantics AND v2 (higher-order-aware) =====
  -- v1: nodes are the proof-term-classified sites only, edges are proof-term floor flow.
  -- v2: all sites (incl. `prop-body`/`propdef-user`/`embedded`), edges also carry the
  -- higher-order flow and statement-level prop-def coupling. Both are computed so every
  -- level the correction MOVED is reported (`RELEVEL`), not silently rewritten.
  let oldClasses : List String := ["endpoint", "threader", "dead", "no-value", "tooth"]
  let v1Set : NameSet := sites.foldl
    (fun a s => if oldClasses.contains s.cls then a.insert s.name else a) {}
  let carrierSet : NameSet := sites.foldl (fun a s => a.insert s.name) {}
  let mut levelV1 : Std.HashMap Name Nat := {}
  let mut changed := true
  let mut iters := 0
  while changed && iters < 300 do
    changed := false
    iters := iters + 1
    for s in sites do
      unless oldClasses.contains s.cls do continue
      let mut lv := 0
      for e in s.edges do
        if v1Set.contains e then lv := max lv ((levelV1.getD e 0) + 1)
      if lv != levelV1.getD s.name 0 then
        levelV1 := levelV1.insert s.name lv
        changed := true
  if iters >= 300 then
    throwError "FLOOR-CENSUS FAIL-CLOSED: v1 floor-flow level fixpoint did not converge \
      (cycle in the flow graph?) — refusing to emit a wave plan from a broken DAG."
  let mut level : Std.HashMap Name Nat := {}
  changed := true
  iters := 0
  while changed && iters < 300 do
    changed := false
    iters := iters + 1
    for s in sites do
      let mut lv := 0
      for e in s.edges do
        if carrierSet.contains e then lv := max lv ((level.getD e 0) + 1)
      for e in s.hoEdges do
        if carrierSet.contains e then lv := max lv ((level.getD e 0) + 1)
      if lv != level.getD s.name 0 then
        level := level.insert s.name lv
        changed := true
  if iters >= 300 then
    throwError "FLOOR-CENSUS FAIL-CLOSED: v2 floor-flow level fixpoint did not converge \
      (cycle in the flow graph?) — refusing to emit a wave plan from a broken DAG."
  -- ⚑ FAIL-CLOSED gate (e): the higher-order keystone must be SEEN threading and re-leveled.
  match sites.find? (·.name == sentinelHoThread) with
  | some s =>
    unless s.flags.contains "ho-thread" && level.getD s.name 0 ≥ 1 do
      throwError "FLOOR-CENSUS FAIL-CLOSED: {sentinelHoThread} is not seen as a \
        higher-order threader above L0 (flags {fmtFlags s.flags}, level \
        {level.getD s.name 0}). The DAG would repeat v1's keystone mis-leveling — \
        refusing to report."
  | none =>
    throwError "FLOOR-CENSUS FAIL-CLOSED: keystone {sentinelHoThread} is not in the \
      carrier surface at all. Partial import — refusing to report."

  let sorted := sites.qsort (fun a b =>
    a.mod.toString < b.mod.toString
      || (a.mod.toString == b.mod.toString && a.startLine < b.startLine))
  for s in sorted do
    lines := lines.push
      (s!"CARRIER\t{s.name}\t{s.mod}\t{modFile s.mod}\t{s.startLine}\t{s.endLine}\t" ++
       s!"{s.kind}\t{s.cls}\t{s.conc}\t{level.getD s.name 0}\t{fmtNames s.floors}\t{fmtFlags s.flags}")
  -- every proof-term-classified site the higher-order correction MOVED
  let mut relevels := 0
  for s in sorted do
    unless oldClasses.contains s.cls do continue
    let l1 := levelV1.getD s.name 0
    let l2 := level.getD s.name 0
    if l1 != l2 then
      relevels := relevels + 1
      lines := lines.push s!"RELEVEL\t{s.name}\t{l1}\t{l2}"
  -- multi-floor COMBINATION histogram (the AppRule table is designed against these)
  let mut combos : Std.HashMap String (Nat × Nat) := {}
  for s in sites do
    if s.floors.size ≥ 2 then
      let key := "+".intercalate
        (((s.floors.qsort (fun a b => a.toString < b.toString)).toList).map (·.toString))
      let (a, t) := combos.getD key (0, 0)
      combos := combos.insert key (a + 1, if s.cls == "threader" then t + 1 else t)
  let comboArr := combos.toList.toArray.qsort (fun a b =>
    a.2.1 > b.2.1 || (a.2.1 == b.2.1 && a.1 < b.1))
  for (k, a, t) in comboArr do
    lines := lines.push s!"COMBO\t{k}\t{a}\t{t}"
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
  for cl in ["endpoint", "threader", "dead", "no-value", "tooth",
             "prop-body", "propdef-user", "embedded"] do
    summary := summary.push s!"SUMMARY\tclass-{cl}\t{(sites.filter (·.cls == cl)).size}"
  -- the pre-v2 surface (proof-term-classified sites only), for continuity with old reports
  summary := summary.push
    s!"SUMMARY\tcarriers-v1-classes\t{(sites.filter (fun s => oldClasses.contains s.cls)).size}"
  -- refutation WITNESSES surfaced by the embedded class are anti-floor content, not port
  -- surface; the port surface excludes exactly those
  let witnessSites := (sites.filter (·.flags.contains "refut-witness")).size
  summary := summary.push s!"SUMMARY\tembedded-refut-witness\t{witnessSites}"
  summary := summary.push s!"SUMMARY\tsurface-port\t{sites.size - witnessSites}"
  -- ===== v2 gap 3: DEAD split by kind × flags (the honest day-one deletion wave) =====
  let blocking : List String :=
    ["bridge", "conc-floor", "auto-name", "simp", "transport", "instImp", "inj-spelled",
     "absurd-use", "struct-boiler", "body-floor", "uses-propdef"]
  let deadS := sites.filter (·.cls == "dead")
  let deadThm := deadS.filter (·.kind == "thm")
  let deadDef := deadS.filter (·.kind == "def")
  summary := summary.push
    s!"SUMMARY\tdead-thm-clean\t{(deadThm.filter (fun s => !s.flags.any (blocking.contains ·))).size}"
  summary := summary.push
    s!"SUMMARY\tdead-thm-flagged\t{(deadThm.filter (fun s => s.flags.any (blocking.contains ·))).size}"
  summary := summary.push
    s!"SUMMARY\tdead-def-boiler\t{(deadDef.filter (·.flags.contains "struct-boiler")).size}"
  summary := summary.push
    s!"SUMMARY\tdead-def-other\t{(deadDef.filter (fun s => !s.flags.contains "struct-boiler")).size}"
  let deadOtherKind := (deadS.filter (fun s => s.kind != "thm" && s.kind != "def")).size
  summary := summary.push s!"SUMMARY\tdead-other-kind\t{deadOtherKind}"
  -- ===== v2 gap 2: higher-order flow accounting =====
  summary := summary.push
    s!"SUMMARY\tho-thread-sites\t{(sites.filter (·.flags.contains "ho-thread")).size}"
  summary := summary.push
    s!"SUMMARY\tho-opaque-sites\t{(sites.filter (·.flags.contains "ho-opaque")).size}"
  summary := summary.push
    s!"SUMMARY\tho-local-sites\t{(sites.filter (·.flags.contains "ho-local")).size}"
  summary := summary.push s!"SUMMARY\trelevel-changed\t{relevels}"
  -- ===== v2 gap 1: prop-body accounting =====
  summary := summary.push
    s!"SUMMARY\tpropbody-direct\t{(sites.filter (fun s => s.cls == "prop-body" && s.flags.contains "direct")).size}"
  summary := summary.push
    s!"SUMMARY\tpropbody-via\t{(sites.filter (fun s => s.cls == "prop-body" && s.flags.contains "via-propdef")).size}"
  summary := summary.push
    s!"SUMMARY\tbody-floor-binder-sites\t{(sites.filter (·.flags.contains "body-floor")).size}"
  summary := summary.push
    s!"SUMMARY\tuses-propdef-sites\t{(sites.filter (·.flags.contains "uses-propdef")).size}"
  -- ===== v2 gap 4: multi-floor accounting =====
  summary := summary.push
    s!"SUMMARY\tmulti-floor-carriers\t{(sites.filter (·.floors.size ≥ 2)).size}"
  summary := summary.push
    s!"SUMMARY\tmulti-floor-threaders\t{(sites.filter (fun s => s.cls == "threader" && s.floors.size ≥ 2)).size}"
  summary := summary.push s!"SUMMARY\tmulti-floor-combos\t{comboArr.size}"
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
  -- the v1 (proof-term-edges-only) histogram, so the correction's movement is visible
  let mut lvHist1 : Std.HashMap Nat Nat := {}
  for s in sites do
    unless oldClasses.contains s.cls do continue
    let lv := levelV1.getD s.name 0
    lvHist1 := lvHist1.insert lv ((lvHist1.getD lv 0) + 1)
  for (lv, c) in lvHist1.toList.toArray.qsort (fun a b => a.1 < b.1) do
    summary := summary.push s!"SUMMARY\tlevel-v1edges-{lv}\t{c}"

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
