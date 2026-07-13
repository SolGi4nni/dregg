/-
# Dregg2.Circuit.ClosureDesignationDischarge — `derive_designation_discharge`: the metaprogram that
AUTO-GENERATES the per-effect-family `RowEncodes`-of-designation discharge lemma from the family's
`RowEncodes` definition, so the P1 readout reduction becomes "apply the macro N times".

## What this lands

`ClosureColumnDischarge.rowEncodes_of_designation` proved, BY HAND for the transfer template, that the
`RowEncodes` column reads are `env.loc`-DETERMINED: given only the two published-commitment ties
(`env.pub OLD/NEW_COMMIT = env.loc (s?Col STATE_COMMIT)`), the canonical decoders
`decodeCellPre/decodeCellPost` satisfy `RowEncodes`, the 17 column equalities all `rfl`.

There are ~24 distinct per-effect `RowEncodes` families (`EffectVmEmitMint.RowEncodes`,
`EffectVmEmitIncrementNonce.RowEncodesIncNonce`, `EffectVmEmitCreateCellFullState.RowEncodesCreate`,
…), each in its own `EffectVmEmit<E>` namespace with a DIFFERENT signature but the SAME skeleton. Every
one of them decodes the row's `state_before` / `param` / `state_after` columns into concrete
`CellState`/value records, and every one is `env.loc`-determined the same way. Writing the discharge
lemma by hand for each is a mechanical grind.

`derive_designation_discharge` reads the family's `RowEncodes` def, CLASSIFIES its shape by
introspecting the argument telescope + the conjunction body, and EMITS the discharge lemma (plus its
`#assert_axioms` tripwire). The emitted lemma is a REAL proof: the column reads close by `rfl`, the
`∀ i` field blocks by `intro i; rfl`, and the publish ties by `assumption` from the two named
hypotheses. Nothing is `sorry`; nothing is vacuous.

## The three shape-classes it handles (all sharing the transfer `CellState` + decoders)

  * **post-only** — `RE (env) (post : CellState)` (createCell / factory / makeSovereign born-empty):
    only the `state_after` block; NO commit column, NO publish ties. Conclusion
    `RE env (decodeCellPost env)`, no hypotheses.
  * **pre-post** — `RE (env) (pre post : CellState)` (incrementNonce / cellSeal / …): full
    `state_before` + `state_after` blocks + the two publish ties. Conclusion
    `RE env (decodeCellPre env) (decodeCellPost env)`, hypotheses `hOld`/`hNew`.
  * **value-carrying** — `RE (env) (pre : CellState) (amt : ℤ) (post : CellState)` (mint / burn /
    bridgeMint / noteSpend): pre + post blocks, a `param` column tie `env.loc (prmCol …) = amt`, and
    the two publish ties. The macro FINDS the param column from the body (Mint's `VALUE_LO`, Burn's
    `param.BURN_AMOUNT_LO`, …) and plugs `amt := env.loc (that column)`. Conclusion
    `RE env (decodeCellPre env) (env.loc …) (decodeCellPost env)`, hypotheses `hOld`/`hNew`.

## Shape-classes the macro REFUSES (loudly), naming the variant needed

A family whose `RowEncodes` deviates from the skeleton is REJECTED with a diagnostic rather than
force-fit — exactly the honest boundary:

  * a leading non-`env` binder (`SetField.RowEncodesSF (slot : Fin 8) (env) …`) — the `slot`
    parameter + its extra `env.loc (prmCol VALUE) = post.fields slot` written-value tie need a variant;
  * a `CellState`-arg that is not the transfer `CellState` (`Bridge.RowEncodes` over
    `RecordKernelState`) — a different decoder set;
  * any argument that is neither `VmRowEnv`, the transfer `CellState`, nor `ℤ`.

The refusal is a hard error at the macro invocation, so a deviating family cannot be silently mis-derived.

## Axiom hygiene

Each emitted lemma is followed by an emitted `#assert_axioms`, so `⊆ {propext, Classical.choice,
Quot.sound}` is a build-time tripwire on every derivation. NEW file; imports read-only.
-/
import Dregg2.Circuit.ClosureColumnDischarge
import Dregg2.Circuit.Emit.EffectVmEmitMint
import Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce
import Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState

namespace Dregg2.Circuit.ClosureDesignationDischarge

open Lean Lean.Meta Lean.Elab Lean.Elab.Command
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.ClosureColumnDischarge (decodeCellPre decodeCellPost)

/-! ## §1 — the introspection + emission engine. -/

/-- The `CellState` every derivable family reuses (the transfer state block). -/
private def cellStateName : Name := ``Dregg2.Circuit.Emit.EffectVmEmitTransferSound.CellState

/-- Split an iterated right-nested `And` into its atomic conjuncts. -/
private partial def splitAnd (e : Lean.Expr) : Array Lean.Expr :=
  if e.isAppOfArity ``And 2 then
    let a := e.appFn!.appArg!
    let b := e.appArg!
    #[a] ++ splitAnd b
  else
    #[e]

/-- The recognized shape of a `RowEncodes` family. `value` carries the delaborated param column term
(the `env.loc`-argument the value slot reads). -/
private inductive DesigShape where
  | postOnly
  | prePost
  | value (colStr : String)

/-- Introspect a `RowEncodes` family constant: telescope its definition, classify the shape, confirm
the publish-tie presence, and (for the value shape) locate the `param` column the value slot reads.
Throws a NAMED error for any family that deviates from the transfer skeleton. Returns the shape and
whether the two publish ties are present. -/
private def classify (famName : Name) : MetaM (DesigShape × Bool) := do
  let info ← getConstInfo famName
  let some val := info.value?
    | throwError "derive_designation_discharge: `{famName}` has no unfoldable body (it is a \
        `structure`/opaque, e.g. Bridge's `RowEncodes` over `RecordKernelState`). Such a family is \
        not a `∧`-chain of column reads and needs a dedicated variant, not this generic derivation."
  Meta.lambdaTelescope val fun xs body => do
    if xs.isEmpty then
      throwError "derive_designation_discharge: `{famName}` takes no arguments"
    -- the first explicit argument MUST be the row environment `env : VmRowEnv`.
    let env := xs[0]!
    let envTy ← whnf (← inferType env)
    unless envTy.isConstOf ``Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv do
      throwError "derive_designation_discharge: the first argument of `{famName}` is not `VmRowEnv` \
        (got `{← inferType env}`). A leading non-`env` binder (e.g. SetField's `slot : Fin 8`) needs \
        a dedicated variant, not this generic derivation."
    -- classify the remaining arguments into CellState / ℤ / other.
    let mut cellArgs : Array Lean.Expr := #[]
    let mut intArgs : Array Lean.Expr := #[]
    for x in xs[1:] do
      let ty ← whnf (← inferType x)
      if ty.isConstOf cellStateName then
        cellArgs := cellArgs.push x
      else if ty.isConstOf ``Int then
        intArgs := intArgs.push x
      else
        throwError "derive_designation_discharge: argument `{x}` of `{famName}` has type `{← inferType x}`, \
          which is neither the transfer `CellState` nor `ℤ`. A family over a different record (e.g. \
          Bridge's `RecordKernelState`) needs a dedicated variant."
    -- the publish ties are present iff the body mentions `VmRowEnv.pub`.
    let conjs := splitAnd body
    let hasTies := conjs.any fun c =>
      match c.eq? with
      | some (_, lhs, _) => lhs.getAppFn.isConstOf ``Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv.pub
      | none => false
    -- dispatch on the argument profile.
    match cellArgs.size, intArgs.size with
    | 1, 0 => return (.postOnly, hasTies)
    | 2, 0 => return (.prePost, hasTies)
    | 2, 1 =>
      -- locate the conjunct `env.loc COL = amt` and read COL off it.
      let amt := intArgs[0]!
      let mut colStr? : Option String := none
      for c in conjs do
        match c.eq? with
        | some (_, lhs, rhs) =>
          if rhs.isFVar && rhs.fvarId! == amt.fvarId! then
            -- lhs = `VmRowEnv.loc env COL`; the column is the 2nd application argument.
            let args := lhs.getAppArgs
            if lhs.getAppFn.isConstOf ``Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv.loc
                && args.size == 2 then
              let col := args[1]!
              let colFmt ← withOptions (fun o => (pp.fullNames.set o true)) <| ppExpr col
              colStr? := some (toString colFmt)
        | none => pure ()
      match colStr? with
      | some s => return (.value s, hasTies)
      | none =>
        throwError "derive_designation_discharge: could not locate the `env.loc` param column the value \
          argument of `{famName}` reads; this family needs a dedicated variant."
    | nc, ni =>
      throwError "derive_designation_discharge: `{famName}` has {nc} `CellState` argument(s) and {ni} \
        `ℤ` argument(s) — an unrecognized shape. Recognized: (1 cell,0 int)=post-only, \
        (2 cell,0 int)=pre-post, (2 cell,1 int)=value-carrying."

/-- Assemble the discharge-lemma command source (and its name) for a classified family. The emitted
source is FULLY QUALIFIED (`VmRowEnv`, `sbCol`, `pi.OLD_COMMIT`, the decoders, …) so it elaborates
correctly wherever the macro is invoked — it does NOT depend on the caller's `open` context. -/
private def emitSource (famName : Name) (lemName : Name) (shape : DesigShape) (hasTies : Bool) :
    String :=
  let E := "Dregg2.Circuit.Emit.EffectVmEmit."          -- VmRowEnv, sbCol, saCol, pi.*, state.*
  let D := "Dregg2.Circuit.ClosureColumnDischarge."     -- decodeCellPre, decodeCellPost
  let reStr := famName.toString
  let hyps :=
    if hasTies then
      s!" (hOld : env.pub {E}pi.OLD_COMMIT = env.loc ({E}sbCol {E}state.STATE_COMMIT))" ++
      s!" (hNew : env.pub {E}pi.NEW_COMMIT = env.loc ({E}saCol {E}state.STATE_COMMIT))"
    else ""
  let plugs :=
    match shape with
    | .postOnly    => s!"({D}decodeCellPost env)"
    | .prePost     => s!"({D}decodeCellPre env) ({D}decodeCellPost env)"
    | .value col   => s!"({D}decodeCellPre env) (env.loc ({col})) ({D}decodeCellPost env)"
  s!"theorem {lemName.toString} (env : {E}VmRowEnv){hyps} :\n" ++
  s!"    {reStr} env {plugs} := by\n" ++
  s!"  unfold {reStr}\n" ++
  s!"  repeat' apply And.intro\n" ++
  s!"  all_goals first\n" ++
  s!"    | rfl\n" ++
  s!"    | (intro i; rfl)\n" ++
  s!"    | assumption"

/-- The default derived lemma name: `<familyNamespaceTail>_of_designation`
(e.g. `EffectVmEmitMint.RowEncodes` → `EffectVmEmitMint_of_designation`). -/
private def defaultName (famName : Name) : Name :=
  let nsTail :=
    match famName.getPrefix.components.getLast? with
    | some c => c.toString
    | none => "family"
  Name.mkSimple (nsTail ++ "_of_designation")

/-- **`derive_designation_discharge <RowEncodes> [as <name>]`** — emit the designation-discharge lemma
for the per-effect `RowEncodes` family named by the (fully-qualified) identifier, followed by its
`#assert_axioms` tripwire. See the module docstring for the shape-classes handled and refused. -/
syntax (name := deriveDesignationDischarge)
  "derive_designation_discharge " ident (" as " ident)? : command

elab_rules : command
  | `(derive_designation_discharge $fam:ident $[as $nm:ident]?) => do
    let famName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo fam
    let lemName : Name :=
      match nm with
      | some id => id.getId
      | none => defaultName famName
    let (shape, hasTies) ← liftTermElabM <| classify famName
    let src := emitSource famName lemName shape hasTies
    match Lean.Parser.runParserCategory (← getEnv) `command src with
    | .ok stx => elabCommand stx
    | .error e => throwError "derive_designation_discharge: emission failed to parse:\n{e}\n--- source ---\n{src}"
    let assertSrc := s!"#assert_axioms {lemName.toString}"
    match Lean.Parser.runParserCategory (← getEnv) `command assertSrc with
    | .ok stx => elabCommand stx
    | .error e => throwError "derive_designation_discharge: assert emission failed:\n{e}"

/-! ## §2 — the PROTOTYPE derivations across the three shape-classes.

Each line below REPLACES a hand-written ~15-line discharge lemma. The emitted lemma builds green and is
`#assert_axioms`-clean (the macro emits the tripwire too). Together they prove the skeleton generalizes:
one value-carrying family, one pre-post family, one post-only family. -/

-- value-carrying: `EffectVmEmitMint.RowEncodes (env) (pre) (amt : ℤ) (post)`.
derive_designation_discharge Dregg2.Circuit.Emit.EffectVmEmitMint.RowEncodes
  as mint_rowEncodes_of_designation

-- pre-post: `EffectVmEmitIncrementNonce.RowEncodesIncNonce (env) (pre post)`.
derive_designation_discharge Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce.RowEncodesIncNonce
  as incNonce_rowEncodes_of_designation

-- post-only: `EffectVmEmitCreateCellFullState.RowEncodesCreate (env) (post)`.
derive_designation_discharge Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState.RowEncodesCreate
  as createCell_rowEncodes_of_designation

end Dregg2.Circuit.ClosureDesignationDischarge
