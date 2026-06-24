/-
# Dregg2.Verify.LoadBearingLint — the `@[load_bearing]` spec-integrity linter.

A `@[load_bearing]` declaration is a *specification* (a `Prop`-valued admissibility predicate or a
full-state relation, e.g. `BurnGuard`, `MintASpec`, `SetFieldSpec`, `execGraph`) whose JOB is to be an
INDEPENDENT reference for an executor arm. The danger this linter measures is the *spec↔gate gap
collapse*: a "spec" that is secretly the implementation's own dispatch gate (the `execGraph_eq_any :=
rfl` shape) attests NOTHING — proving "executor meets spec" against it is `rfl`, a tautology.

For a spec `S` (optionally paired with the implementation gate `G` it validates, and a non-vacuity
witness `W`) the command `#load_bearing_audit` runs THREE checks:

  1. **Import/dependency boundary.** Collect the TRANSITIVE `usedConstants` of `S`'s definition body
     and FAIL if any lives under a forbidden *executor STEP-GATE* namespace/name (`recKExec`,
     `recKBurnAsset`, `recCBurnAsset`, `execFullA`, `stateStep`, `stateStepGuarded`, `stateStepDev`,
     `makeSovereignStep`, `heapStepGuardedW`, `recKMintAsset`, `recCMintAsset`, …). A spec written over
     PURE kernel-field helpers (`recTransferBal`, `mintAuthorizedB`, `cellLifecycleLive`, `stateAuthB`)
     is independent and PASSES; a spec that calls the executor step IS the gate and FAILS. The forbidden
     set is the dispatch/step functions, NOT the kernel ledger/authority helpers a faithful spec is
     ENTITLED to name.

  2. **Not def-eq to the gate.** Given a `gate := G` pairing, run `Lean.Meta.isDefEq` between `S` and
     `G` (eta/beta/whnf-aware). FAIL if they are defeq — this is the `execGraph_eq_any := rfl`
     failure: the spec IS the gate, so the spec⟺executor theorem is `rfl` and validates nothing. With
     no `gate`, this check is reported `n/a` (only the boundary + non-vacuity bite).

  3. **Non-vacuity companion.** Require a sibling witness `W` (passed `nonvacuous := W`, or the naming
     convention `<S>_nonvacuous`) to EXIST and be `sorry`-free (no non-kernel axioms via
     `collectAxioms`). Ideally `W` witnesses BOTH an accepted instance and a refuted one; the linter
     checks existence + axiom-cleanliness (it cannot read intent, but a vacuous `True`-spec cannot
     carry a refuted witness, so a clean non-vacuity companion is the operational proxy).

The command prints `PASS`/`FAIL` per check with the reason, then an overall verdict. It is a pure
REJECTOR — it can only report, never close a goal or weaken a theorem.

Reusable: tag specs `@[load_bearing]` (or `@[load_bearing gate := …]`) and either run
`#load_bearing_audit` per spec or `#load_bearing_audit_tagged` to sweep every tagged decl.
-/
import Lean
import Dregg2.Tactics

open Lean Elab Command Meta

namespace Dregg2.Verify.LoadBearingLint

/-! ## §1 — the forbidden executor STEP-GATE constants.

These are the dispatch / step functions a `@[load_bearing]` spec must NOT transitively name: naming one
means the "spec" is reading the executor's own gate, so it cannot be an independent reference. This list
is the executable kernel's *step* surface (`Dregg2.Exec.*` dispatch), deliberately EXCLUDING the pure
kernel-field helpers (`recTransferBal`, `mintAuthorizedB`, `cellLifecycleLive`, `stateAuthB`,
`recStateCommit`, …) a faithful spec is entitled to name. A name is forbidden if it is, or is a
namespace-prefix-suffix of, any entry (so `Dregg2.Exec.recKBurnAsset` and any `.match_`/`._eq` of it are
caught). -/
-- single-backtick `Name` literals (NOT `` ``name``): the linter module deliberately does NOT import
-- the executor (so it stays a light, reusable leaf), so these constants are not in THIS module's
-- environment at elaboration time. They ARE in the environment of any module that imports both the
-- executor and this linter — which is where the command runs. Name literals don't require existence.
def forbiddenStepGates : List Name :=
  [ -- RecordKernel-level balance/value step
    `Dregg2.Exec.recKExec
  , `Dregg2.Exec.recCexec
    -- the per-asset supply step gates (TurnExecutorFull)
  , `Dregg2.Exec.TurnExecutorFull.recKBurnAsset
  , `Dregg2.Exec.TurnExecutorFull.recCBurnAsset
  , `Dregg2.Exec.TurnExecutorFull.recKMintAsset
  , `Dregg2.Exec.TurnExecutorFull.recCMintAsset
  , `Dregg2.Exec.TurnExecutorFull.recKBurnAssetLegacy
  , `Dregg2.Exec.TurnExecutorFull.recKMintAssetLegacy
    -- the legacy ℤ-ledger mint/burn steps (RecordKernel)
  , `Dregg2.Exec.recKBurn
  , `Dregg2.Exec.recKMint
  , `Dregg2.Exec.recCBurn
  , `Dregg2.Exec.recCMint
    -- the top-level dispatch + the sovereign step (TurnExecutorFull)
  , `Dregg2.Exec.TurnExecutorFull.execFullA
  , `Dregg2.Exec.TurnExecutorFull.makeSovereignStep
  , `Dregg2.Substrate.HeapKernel.heapStepGuardedW
    -- the cell-state field step family (EffectsState)
  , `Dregg2.Exec.EffectsState.stateStep
  , `Dregg2.Exec.EffectsState.stateStepGuarded
  , `Dregg2.Exec.EffectsState.stateStepDev
  ]

/-- Is `n` a forbidden step-gate constant (exact match OR an internal child like `n.match_1`,
`n._eq_1` of one)? We compare against each forbidden base by `==` or by checking the forbidden base is
a strict name-prefix of `n` (catching auto-generated equation/match lemmas of the gate). -/
def isForbidden (n : Name) : Bool :=
  forbiddenStepGates.any fun base => n == base || base.isPrefixOf n

/-! ## §2 — transitive used-constant collection over definition bodies.

`Expr.getUsedConstants` gives the DIRECT constants of one expression. We close transitively over the
`value?` (definition body) of each reached constant, so a spec that calls a helper that calls a gate is
still caught. We DO NOT descend into types of opaque constants (structures/inductives) — only `value?`
bodies — which is exactly the "definition body" boundary the criterion names. A visited-set bounds the
walk. -/
partial def transitiveConsts (env : Environment) (roots : Array Name) : MetaM (Std.HashSet Name) := do
  let mut visited : Std.HashSet Name := {}
  let mut stack : List Name := roots.toList
  while h : !stack.isEmpty do
    let n := stack.head (by simpa using h)
    stack := stack.tail
    if visited.contains n then continue
    visited := visited.insert n
    match env.find? n with
    | some ci =>
      -- the body (def value); plus the type, to catch a gate that leaks in via a spec's TYPE.
      let mut es : Array Expr := #[ci.type]
      if let some v := ci.value? then es := es.push v
      for e in es do
        for c in e.getUsedConstants do
          unless visited.contains c do stack := c :: stack
    | none => pure ()
  return visited

/-! ## §3 — the three checks. -/

structure CheckResult where
  pass   : Bool
  reason : String

/-- CHECK 1 — import/dependency boundary: none of the spec's transitive constants is a forbidden
step gate. Returns the offending names on FAIL. -/
def checkBoundary (spec : Name) : MetaM CheckResult := do
  let env ← getEnv
  let reached ← transitiveConsts env #[spec]
  let offenders := reached.toList.filter isForbidden
  if offenders.isEmpty then
    return { pass := true, reason := "independent — references no executor step gate" }
  else
    return { pass := false
             reason := s!"references executor STEP GATE(s): {offenders} — the spec is reading the \
               implementation's own dispatch, not an independent reference" }

/-- CHECK 2 — not def-eq to the gate. `isDefEq spec gate` at the value level. A `gate := G` pairing is
required; with none we report `n/a` (`pass := true`, but flagged so the verdict shows it was not
exercised). The known offender (`execGraph` vs the `.any` body via `execGraph_eq_any := rfl`) is the
calibration: `isDefEq` MUST return `true` there. -/
def checkNotDefEqGate (spec : Name) (gate? : Option Name) : MetaM CheckResult := do
  match gate? with
  | none => return { pass := true, reason := "n/a — no `gate :=` pairing supplied" }
  | some gate =>
    let env ← getEnv
    let some specCi := env.find? spec | throwError "load_bearing: unknown spec `{spec}`"
    let some gateCi := env.find? gate | throwError "load_bearing: unknown gate `{gate}`"
    -- compare the DEFINITIONS (values). If a value is absent (opaque), fall back to the constant
    -- expression so `isDefEq` still has something to chew (it will whnf/delta as needed).
    let specE := specCi.value?.getD (mkConst spec)
    let gateE := gateCi.value?.getD (mkConst gate)
    let eq ← isDefEq specE gateE
    if eq then
      return { pass := false
               reason := s!"DEF-EQ to gate `{gate}` — the spec IS the implementation gate (the \
                 `:= rfl` collapse); proving executor⟺spec against it attests nothing" }
    else
      return { pass := true, reason := s!"distinct from gate `{gate}` (not defeq)" }

/-- CHECK 3 — non-vacuity companion exists and is `sorry`/axiom-clean. Resolves `nonvacuous?` or the
`<spec>_nonvacuous` convention; FAILS if absent, or if `collectAxioms` shows a non-kernel axiom (a
`sorryAx` leak ⇒ the witness is fake). -/
def checkNonVacuity (spec : Name) (nonvacuous? : Option Name) : MetaM CheckResult := do
  let env ← getEnv
  let candidate : Name := nonvacuous?.getD (spec.appendAfter "_nonvacuous")
  match env.find? candidate with
  | none =>
    return { pass := false
             reason := s!"no non-vacuity companion `{candidate}` — a spec with no witnessed \
               accepted+refuted instance may be vacuous (accept-everything)" }
  | some _ =>
    let axs ← collectAxioms candidate
    let bad := axs.filter fun a => !Dregg2.cleanAxioms.contains a
    if bad.isEmpty then
      return { pass := true, reason := s!"witness `{candidate}` present + axiom-clean" }
    else
      return { pass := false
               reason := s!"non-vacuity witness `{candidate}` depends on non-kernel axioms {bad.toList} \
                 (a `sorryAx` here ⇒ the witness is fake)" }

/-! ## §4 — the audit driver + report. -/

structure AuditSpec where
  spec        : Name
  gate?       : Option Name := none
  nonvacuous? : Option Name := none

/-- Run all three checks on one spec and return (overall, lines). -/
def runAudit (a : AuditSpec) : MetaM (Bool × Array String) := do
  let c1 ← checkBoundary a.spec
  let c2 ← checkNotDefEqGate a.spec a.gate?
  let c3 ← checkNonVacuity a.spec a.nonvacuous?
  let mark (c : CheckResult) := if c.pass then "PASS" else "FAIL"
  let overall := c1.pass && c2.pass && c3.pass
  let lines := #[
    s!"  [1] import/dependency boundary : {mark c1} — {c1.reason}",
    s!"  [2] not-defeq-to-gate          : {mark c2} — {c2.reason}",
    s!"  [3] non-vacuity companion      : {mark c3} — {c3.reason}",
    s!"  OVERALL: {if overall then "PASS (independent + meaningful)" else "FAIL (gate-copy / vacuous — see above)"}"]
  return (overall, lines)

/-! ## §5 — the `@[load_bearing]` attribute (tag specs, optionally with their gate/witness).

`@[load_bearing]`, `@[load_bearing gate := G]`, `@[load_bearing nonvacuous := W]`, or both. Tagged
decls are swept by `#load_bearing_audit_tagged`. -/

structure LoadBearingEntry where
  gate?       : Option Name := none
  nonvacuous? : Option Name := none
  deriving Inhabited

initialize loadBearingExt :
    SimplePersistentEnvExtension (Name × LoadBearingEntry) (Std.HashMap Name LoadBearingEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, e) => m.insert n e
    addImportedFn := fun ess => Id.run do
      let mut m : Std.HashMap Name LoadBearingEntry := {}
      for es in ess do for (n, e) in es do m := m.insert n e
      return m }

syntax (name := loadBearingAttr)
  "load_bearing" (" gate " ":=" ident)? (" nonvacuous " ":=" ident)? : attr

initialize registerBuiltinAttribute {
  name := `loadBearingAttr
  descr := "marks a declaration as a load-bearing spec for the spec-integrity linter"
  add := fun decl stx _kind => do
    let gate? ← match stx with
      | `(attr| load_bearing gate := $g $[nonvacuous := $_]?) =>
          some <$> (liftCommandElabM <| liftCoreM <| realizeGlobalConstNoOverloadWithInfo g)
      | _ => pure none
    let nv? ← match stx with
      | `(attr| load_bearing $[gate := $_]? nonvacuous := $w) =>
          some <$> (liftCommandElabM <| liftCoreM <| realizeGlobalConstNoOverloadWithInfo w)
      | _ => pure none
    modifyEnv fun env =>
      loadBearingExt.addEntry env (decl, { gate? := gate?, nonvacuous? := nv? }) }

/-! ## §6 — the commands. -/

/-- `#load_bearing_audit S (gate := G)? (nonvacuous := W)?` — audit ONE spec. Prints the 3-check report
and FAILS (throws) if the overall verdict is FAIL, so it is a usable CI gate. -/
syntax (name := loadBearingAuditCmd)
  "#load_bearing_audit" ident (" gate " ":=" ident)? (" nonvacuous " ":=" ident)? : command

elab_rules : command
  | `(command| #load_bearing_audit $s $[gate := $g?]? $[nonvacuous := $w?]?) => do
    let spec ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
    let gate? ← g?.mapM fun g => liftCoreM <| realizeGlobalConstNoOverloadWithInfo g
    let nv?   ← w?.mapM fun w => liftCoreM <| realizeGlobalConstNoOverloadWithInfo w
    let (overall, lines) ← liftTermElabM <| (runAudit { spec, gate?, nonvacuous? := nv? }).run'
    let report := s!"load_bearing audit — {spec}\n" ++ String.intercalate "\n" lines.toList
    if overall then logInfo report
    else throwError report

/-- `#load_bearing_audit_report S …` — same checks, but ALWAYS `logInfo` (never throws). For
measuring/surveying a spec known to be a gate-copy without failing the build. -/
syntax (name := loadBearingAuditReportCmd)
  "#load_bearing_audit_report" ident (" gate " ":=" ident)? (" nonvacuous " ":=" ident)? : command

elab_rules : command
  | `(command| #load_bearing_audit_report $s $[gate := $g?]? $[nonvacuous := $w?]?) => do
    let spec ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
    let gate? ← g?.mapM fun g => liftCoreM <| realizeGlobalConstNoOverloadWithInfo g
    let nv?   ← w?.mapM fun w => liftCoreM <| realizeGlobalConstNoOverloadWithInfo w
    let (_overall, lines) ← liftTermElabM <| (runAudit { spec, gate?, nonvacuous? := nv? }).run'
    logInfo <| s!"load_bearing audit — {spec}\n" ++ String.intercalate "\n" lines.toList

/-- `#load_bearing_audit_tagged` — sweep every `@[load_bearing]`-tagged decl in the environment,
auditing each with its attached `gate?`/`nonvacuous?`. Throws if ANY fails (CI gate over the whole
tagged corpus). -/
elab "#load_bearing_audit_tagged" : command => do
  let env ← getEnv
  let m := loadBearingExt.getState env
  let entries := m.toList
  if entries.isEmpty then
    logWarning "#load_bearing_audit_tagged: no @[load_bearing] declarations found"
    return
  let mut anyFail := false
  let mut report := s!"#load_bearing_audit_tagged — {entries.length} tagged spec(s)\n"
  for (spec, e) in entries do
    let (overall, lines) ← liftTermElabM <|
      (runAudit { spec, gate? := e.gate?, nonvacuous? := e.nonvacuous? }).run'
    report := report ++ s!"\n• {spec}\n" ++ String.intercalate "\n" lines.toList ++ "\n"
    unless overall do anyFail := true
  if anyFail then throwError report else logInfo report

end Dregg2.Verify.LoadBearingLint
