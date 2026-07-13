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
import Dregg2.Circuit.Emit.EffectVmEmitBurn
import Dregg2.Circuit.Emit.EffectVmEmitBridgeMint
import Dregg2.Circuit.Emit.EffectVmEmitNoteSpend
import Dregg2.Circuit.Emit.EffectVmEmitNoteCreate
import Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation
import Dregg2.Circuit.Emit.EffectVmEmitRefreshDelegation
import Dregg2.Circuit.Emit.EffectVmEmitExercise
import Dregg2.Circuit.Emit.EffectVmEmitPipelinedSend
import Dregg2.Circuit.Emit.EffectVmEmitCellDestroy
import Dregg2.Circuit.Emit.EffectVmEmitSetVK
import Dregg2.Circuit.Emit.EffectVmEmitCellUnseal
import Dregg2.Circuit.Emit.EffectVmEmitRefusal
import Dregg2.Circuit.Emit.EffectVmEmitCellSeal
import Dregg2.Circuit.Emit.EffectVmEmitReceiptArchive
import Dregg2.Circuit.Emit.EffectVmEmitEmitEvent
import Dregg2.Circuit.Emit.EffectVmEmitSetPermissions
import Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactoryFullState
import Dregg2.Circuit.Emit.EffectVmEmitMakeSovereignFullState
import Dregg2.Circuit.Emit.EffectVmEmitSetField
import Dregg2.Circuit.Emit.EffectVmEmitBridge
import Dregg2.Circuit.Emit.EffectVmEmitSpawn
import Dregg2.Circuit.Emit.EffectVmEmitAttenuateA

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

/-! ## §2b — the FULL clean cohort: one macro line per derivable family.

The prototypes (§2) proved the skeleton generalizes; this section APPLIES it across every clean
`RowEncodes` family — the ~18 remaining derivable effects. Each line REPLACES a hand-written ~15-line
discharge lemma and emits its `#assert_axioms` tripwire. The macro's `classify` accepts each (first arg
`VmRowEnv`, remaining args the transfer `CellState`/`ℤ`, dispatched by profile); the emitted proof
closes the column reads by `rfl`, the `∀ i` blocks by `intro i; rfl`, and the publish ties (where
present) by `assumption`. The ties-FREE families (refresh/receiptArchive: no `state_commit` column, no
`env.pub` ties) emit NO hypotheses — the whole decode is `rfl`. -/

-- value-carrying (2 cell, 1 int): pre + post blocks + the `param` value column + the two publish ties.
derive_designation_discharge Dregg2.Circuit.Emit.EffectVmEmitBurn.RowEncodes
  as burn_rowEncodes_of_designation
derive_designation_discharge Dregg2.Circuit.Emit.EffectVmEmitBridgeMint.RowEncodes
  as bridgeMint_rowEncodes_of_designation
derive_designation_discharge Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.RowEncodesSpend
  as noteSpend_rowEncodes_of_designation
derive_designation_discharge Dregg2.Circuit.Emit.EffectVmEmitNoteCreate.RowEncodesNote
  as noteCreate_rowEncodes_of_designation

-- pre-post WITH the two publish ties (full `state_before`/`state_after` blocks + commit column + ties).
derive_designation_discharge Dregg2.Circuit.Emit.EffectVmEmitRevokeDelegation.RowEncodesRevoke
  as revokeDelegation_rowEncodes_of_designation
derive_designation_discharge Dregg2.Circuit.Emit.EffectVmEmitExercise.RowEncodesExercise
  as exercise_rowEncodes_of_designation
derive_designation_discharge Dregg2.Circuit.Emit.EffectVmEmitPipelinedSend.RowEncodesSend
  as pipelinedSend_rowEncodes_of_designation
derive_designation_discharge Dregg2.Circuit.Emit.EffectVmEmitCellDestroy.RowEncodesDestroy
  as cellDestroy_rowEncodes_of_designation
derive_designation_discharge Dregg2.Circuit.Emit.EffectVmEmitSetVK.RowEncodesVK
  as setVK_rowEncodes_of_designation
derive_designation_discharge Dregg2.Circuit.Emit.EffectVmEmitCellUnseal.RowEncodesUnseal
  as cellUnseal_rowEncodes_of_designation
derive_designation_discharge Dregg2.Circuit.Emit.EffectVmEmitRefusal.RowEncodesRefusal
  as refusal_rowEncodes_of_designation
derive_designation_discharge Dregg2.Circuit.Emit.EffectVmEmitCellSeal.RowEncodesSeal
  as cellSeal_rowEncodes_of_designation
derive_designation_discharge Dregg2.Circuit.Emit.EffectVmEmitEmitEvent.RowEncodes
  as emitEvent_rowEncodes_of_designation
derive_designation_discharge Dregg2.Circuit.Emit.EffectVmEmitSetPermissions.RowEncodesPerms
  as setPermissions_rowEncodes_of_designation

-- pre-post WITHOUT publish ties (no `state_commit` column, no `env.pub` — the whole decode is `rfl`).
derive_designation_discharge Dregg2.Circuit.Emit.EffectVmEmitRefreshDelegation.RefreshRowEncodes
  as refreshDelegation_rowEncodes_of_designation
derive_designation_discharge Dregg2.Circuit.Emit.EffectVmEmitReceiptArchive.ArchiveRowEncodes
  as receiptArchive_rowEncodes_of_designation

-- post-only (born-empty: only the `state_after` block; NO commit column, NO publish ties).
derive_designation_discharge Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactoryFullState.RowEncodesFactory
  as createCellFromFactory_rowEncodes_of_designation
derive_designation_discharge Dregg2.Circuit.Emit.EffectVmEmitMakeSovereignFullState.RowEncodesMakeSov
  as makeSovereign_rowEncodes_of_designation

/-! ## §3 — the HAND-AUTHORED variants the macro REFUSES (loudly), each following the same skeleton.

Four families deviate from the derivable skeleton and are authored by hand with the family's specific
ties. Each still closes the column reads by `rfl`/`intro i; rfl` and carries ONLY the genuine residual
(publish ties + the family's specific tie) as hypotheses — the honest boundary. -/

/-- **setField (5) — the leading `slot : Fin 8` binder + the written-value tie.** `RowEncodesSF slot env
pre post` is the transfer skeleton (17 column reads + 2 publish ties) PLUS a written-value tie
`env.loc (prmCol VALUE) = post.fields slot` (the runtime `new_value = param1` write). The macro refuses
the leading non-`env` binder; here `slot` leads and `hVal` (the written-value tie — a genuine per-slot
residual) joins `hOld`/`hNew`. The 17 column reads + `hVal`'s `post.fields slot` all `rfl` off the
canonical decoders. -/
theorem setField_rowEncodes_of_designation (slot : Fin 8) (env : VmRowEnv)
    (hOld : env.pub pi.OLD_COMMIT = env.loc (sbCol state.STATE_COMMIT))
    (hNew : env.pub pi.NEW_COMMIT = env.loc (saCol state.STATE_COMMIT))
    (hVal : env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitSetField.VALUE)
      = env.loc (saCol (state.FIELD_BASE + slot.val))) :
    Dregg2.Circuit.Emit.EffectVmEmitSetField.RowEncodesSF slot env
      (decodeCellPre env) (decodeCellPost env) := by
  unfold Dregg2.Circuit.Emit.EffectVmEmitSetField.RowEncodesSF
  repeat' apply And.intro
  all_goals first
    | rfl
    | (intro i; rfl)
    | assumption

#assert_axioms setField_rowEncodes_of_designation

/-- **spawn (a `(1 cell, 1 int)` profile) — post-only + a cap-digest param.** `SpawnRowEncodes env post
capDigestNew` is a born-empty post-only block PLUS a leading cap-digest param read `env.loc (prmCol
paramSP.CAP_DIGEST_NEW) = capDigestNew`. The macro's profile table has no `(1 cell, 1 int)` entry, so it
refuses; the discharge plugs `capDigestNew := env.loc (prmCol paramSP.CAP_DIGEST_NEW)` and every conjunct
(the cap-digest read + the post block) is `rfl` — NO hypotheses (born-empty carries no publish ties). -/
theorem spawn_rowEncodes_of_designation (env : VmRowEnv) :
    Dregg2.Circuit.Emit.EffectVmEmitSpawn.SpawnRowEncodes env (decodeCellPost env)
      (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitSpawn.paramSP.CAP_DIGEST_NEW)) := by
  unfold Dregg2.Circuit.Emit.EffectVmEmitSpawn.SpawnRowEncodes
  repeat' apply And.intro
  all_goals first
    | rfl
    | (intro i; rfl)
    | assumption

#assert_axioms spawn_rowEncodes_of_designation

/-- **attenuateA (`CapRowEncodes`) — pre + post blocks + a cap-digest param, NO publish ties.**
`CapRowEncodes env pre post capDigestNew` reads the pre/post frame blocks (no `state_commit` column) plus
`env.loc (prmCol paramA.CAP_DIGEST_NEW) = capDigestNew`; there are NO `env.pub` ties. The discharge plugs
`capDigestNew := env.loc (prmCol paramA.CAP_DIGEST_NEW)` and every conjunct is `rfl` — NO hypotheses. -/
theorem attenuateA_rowEncodes_of_designation (env : VmRowEnv) :
    Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.CapRowEncodes env
      (decodeCellPre env) (decodeCellPost env)
      (env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.paramA.CAP_DIGEST_NEW)) := by
  unfold Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.CapRowEncodes
  repeat' apply And.intro
  all_goals first
    | rfl
    | (intro i; rfl)
    | assumption

#assert_axioms attenuateA_rowEncodes_of_designation

/-- **bridge (`RowEncodes` over `RecordKernelState`) — a `structure`, not a `CellState` ∧-chain.**
`EffectVmEmitBridge.RowEncodes` is a `structure` over `RecordKernelState` (the ABSTRACT actor-column
move), so it has no unfoldable `∧`-body and the macro refuses it. Only its two param column reads
(`amount`/`dirBit`) are `env.loc`-determined — DISCHARGED to `rfl`. Its ledger ties (`preBal`/`postBal`:
the actor's asset-`a` balance) and the freeze/tick trace facts (`isRow`/`hiFix`/`nonce`/`capFix`/`resFix`/
`fldFix`) are the GENUINE `StarkSound`/ledger-seam residual — carried as hypotheses, never faked. -/
theorem bridge_rowEncodes_of_designation (env : VmRowEnv)
    (pre post : Dregg2.Exec.RecordKernelState) (a : Dregg2.Exec.AssetId) (actor : Dregg2.Exec.CellId)
    (hRow : Dregg2.Circuit.Emit.EffectVmEmitTransfer.IsTransferRow env)
    (hpre : env.loc (sbCol state.BALANCE_LO) = pre.bal actor a)
    (hpost : env.loc (saCol state.BALANCE_LO) = post.bal actor a)
    (hhi : env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI))
    (hnon : env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + 1)
    (hcap : env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT))
    (hres : env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED))
    (hfld : ∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i))) :
    Dregg2.Circuit.Emit.EffectVmEmitBridge.RowEncodes env pre post a actor
      (env.loc (prmCol param.AMOUNT)) (env.loc (prmCol param.DIRECTION)) where
  isRow   := hRow
  preBal  := hpre
  postBal := hpost
  amount  := rfl
  dirBit  := rfl
  hiFix   := hhi
  nonce   := hnon
  capFix  := hcap
  resFix  := hres
  fldFix  := hfld

#assert_axioms bridge_rowEncodes_of_designation

end Dregg2.Circuit.ClosureDesignationDischarge
