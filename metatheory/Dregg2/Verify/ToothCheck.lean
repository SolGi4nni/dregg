/-
# Dregg2.Verify.ToothCheck — the TEETH CHECKER (`#tooth_*`)

## The hole this closes

Every de-vacuated binding in this tree carries three teeth around its per-instance residual:

  * `*_unconditional_false` — dropping the residual makes the binding FALSE;
  * `*_refutable`           — the residual really HOLDS somewhere (it is not `True` in disguise);
  * `*_fires`               — at an honest instance the residual FAILS for EVERY hash (no floor).

The audits of 2026-08-01/02 found that the teeth, not the proofs, are where the repairs go wrong,
and every defect found was the SAME KIND: a tooth stated about a DIFFERENT OBJECT than the residual
it was cited as covering. `#assert_axioms` cannot see it — the teeth are all kernel-clean, they are
just theorems about something else. `#floor_ratchet` cannot see it — a tooth carries no floor.
`#free_conclusion_ratchet` cannot see it — a tooth's conclusion is not free.

The three measured instances:

  * `Circuit/CapRootBridge.capHeapOpen_unconditional_false` refutes heap-root injectivity; the
    theorem it was named for (`capHeapOpen_implies_authorizedB`) also carries `hfaith`, `hroot`,
    `hget`, `hmask`, `hwrite`. Refuting a weaker-hypothesis statement establishes NOTHING about a
    stronger one.
  * `Circuit/RecursiveAggregation` cited `HistoryAggregation.logChained_of_verified_unconditional_-
    false` for `non_omission_from_verification_of_noColl`, whose `EngineSound + hroot` stands where
    the other hypothesises `ChainBound` directly — again a different statement.
  * `Distributed/HistoryAggregation` cited `seamKernelColl_refutable`, which fires at
    `(honestStep, richStep)`, as the companion identifying `hno` as the hypothesis excluding a
    counterexample built at `(honestStep, honestStep)`.

All three are DECIDABLE FACTS ABOUT TYPES. This module decides them.

## What the commands are

  `#tooth_binders T`                          — list `T`'s binder telescope (diagnostic).
  `#tooth_minus T drops hno`                  — print `T`'s statement with the residual binder
                                                DELETED. This is the ONLY admissible statement of
                                                the `_unconditional_false` tooth.
  `#tooth_residual T drops hno`               — print the residual `R` of `hno : ¬ R`, and run the
                                                three REFUSALS on it (§3).
  `#tooth_unconditional_false U for T drops hno`
  `#tooth_refutable R for T drops hno`
  `#tooth_fires F for T drops hno`
  `#tooth_witness U`                          — read the counterexample tuple OUT OF the proof term
                                                of a hand-written `_unconditional_false`.
  `#tooth_same_witness U R for T drops hno`   — ⚑ the check that would have caught the third
                                                defect: does the `_refutable` tooth fire at the SAME
                                                instance the `_unconditional_false` breaks at?

`tooth_minus% T hno` is the same computation as a TERM, so a tooth can be STATED as

    theorem foo_unconditional_false : ¬ tooth_minus% foo hno := by …

and then it cannot drift from `foo` at all — the statement is not written by hand.

## §3 — the three REFUSALS, and why a checker that only compares types is not enough

A residual can be well-formed and still carry no content. Each refusal below is one of the four
ways a repair is itself vacuous, made mechanical:

 1. **Global-existential residual.** `P ∨ SpongeCollision hash` is FREE — the same pigeonhole that
    refutes the floor supplies the right disjunct (`Circuit.SpongeCollisionShirk.orBreak_sponge-
    Collision_iff_True`). Mechanically: the residual mentions ONLY arrow-typed binders of `T`. A
    sound residual names the PAIR, so it mentions a non-arrow binder.
 2. **Universally quantified side condition.** `¬ ∀ xs ys, Coll xs ys` IS injectivity rewritten.
    Mechanically: the residual is a `∀` at the surface.
 3. **Dependent residual.** If a later binder or the conclusion mentions `hno`, deleting it is not
    a statement at all. Mechanically: `hasAnyFVar`.

## MEASURED, 2026-08-03 — 23 of the tree's 34 `*_unconditional_false` teeth, run through
`#tooth_unconditional_false`

  * **9 EXACT** — literally `¬ (T minus hno)`. Including both of `CapRootBridge`'s §5½ teeth and
    `RecursiveAggregation.non_omission_from_verification_unconditional_false`.
  * **8 DERIVED** — sound by `derives`: an `And`-leaf of the conclusion (`aggFold_inj`, `stFold_inj`,
    `histDigest_inj`) or the hash pinned at a concrete collapsing one (`compress_binds`,
    `movedDigest`, `listDigest_binds`, `logHash_binds`).
  * **6 REFUSED** — each drops a HYPOTHESIS alongside the residual. One is the audit's known defect
    (`capHeapOpen_unconditional_false`). **Four of the other five confess the drop in their own
    docstrings** (`root_tooth_pins_kernel`, `verified_history_conserves`,
    `conserves_from_verification`, `recStateCommit_binds_kernel_faithful`) — documented, and until
    now not detected, so the drop could not go red. The sixth,
    `StateCommitReduce.recStateCommit_binds_kernel_unconditional_false`, argues in prose that its
    fixed `RH` covers the honest ones; the composition it needs (an inhabitant of
    `RestHashIffFrameFin`) is a real theorem in the tree but is not in the tooth's type, so the
    statement as written does not refute the obligation.

## What this does NOT check

It compares STATEMENTS. It does not know whether the counterexample tuple `#tooth_witness` reads
out of a proof is a good counterexample — that is what the proof is for. And `_fires` is checked to
be universal in the hash and closed elsewhere; whether the instance it names is HONEST is a
question about the model, not about the type. Both are named here so the gap is visible rather than
implied.

⚑ And `derives` has exactly one move it could sensibly grow: **discharging a `Prop` binder with a
named in-tree proof** (`given [restHashIffFrameFin_satisfiable]`), which is what the sixth refusal
above is one step from. It is deliberately NOT built: a `given` clause that silently accepts a
witness of the wrong shape would turn every refusal in this file into a green light, and the whole
value of the checker is that its refusals are the two-line kind that cannot be argued with.
-/
import Lean

set_option autoImplicit false

namespace Dregg2.Verify.ToothCheck

open Lean Meta Elab Command

/-! ## §1 — telescope surgery -/

/-- Delete index `i` from an array (total; out-of-range is the identity). -/
def eraseAt (xs : Array Expr) (i : Nat) : Array Expr :=
  (xs.toList.eraseIdx i).toArray

/-- The index of the binder with user name `nm`, if any. -/
def findBinder (xs : Array Expr) (nm : Name) : MetaM (Option Nat) := do
  for i in [0 : xs.size] do
    let d ← xs[i]!.fvarId!.getDecl
    if d.userName == nm then return some i
  return none

/-- A constant's type with its universe parameters replaced by fresh level METAVARIABLES.

Without this a universe-polymorphic theorem (`ListCommitRegrounded.listDigest_binds_of_noColl`,
`∀ {α : Type u} …`) cannot be matched against a tooth that instantiates `α := ℕ`: `Type u` with `u`
a rigid parameter does not unify with `Type 0`, and the checker reports a sound tooth as broken. -/
def freshType (n : Name) : MetaM Expr := do
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  return ci.type.instantiateLevelParams ci.levelParams us

/-- The index of the residual binder, plus every binder's user name — read once, so no command has
to open `T`'s telescope twice and risk answering about two different openings. -/
def binderIndexAndNames (thmName hypName : Name) : MetaM (Option Nat × Array Name) := do
  forallTelescope (← freshType thmName) fun zs _ => do
    let mut idx : Option Nat := none
    let mut names : Array Name := #[]
    for j in [0 : zs.size] do
      let d ← zs[j]!.fvarId!.getDecl
      names := names.push d.userName
      if d.userName == hypName then idx := some j
    return (idx, names)

/-- A readable rendering of a telescope, for error messages. -/
def binderList (xs : Array Expr) : MetaM MessageData := do
  let mut out : Array MessageData := #[]
  for i in [0 : xs.size] do
    let d ← xs[i]!.fvarId!.getDecl
    out := out.push m!"{i}. {d.userName} : {d.type}"
  return MessageData.joinSep out.toList "\n"

/-- `R` from `¬ R` or from `R → False`. -/
def peelNot? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``Not 1 then some e.appArg!
  else match e with
    | .forallE _ d b _ => if b == .const ``False [] then some d else none
    | _ => none

/-- **THE STATEMENT MINUS THE RESIDUAL.** `T`'s type with the binder named `hyp` deleted, every
other binder kept in place, the conclusion untouched.

This is the whole of "same binders": the type is not written by hand, so it cannot silently drop a
second hypothesis, weaken one, or answer about a different theorem. `#tooth_unconditional_false`
demands definitional equality with `¬` of this.

REFUSES (§3.3) if the conclusion or any later binder mentions the deleted one — then there is no
such statement, and quietly producing one would be worse than failing. -/
def minusOf (thmName hypName : Name) : MetaM Expr := do
  forallTelescope (← freshType thmName) fun xs body => do
    let some i ← findBinder xs hypName
      | throwError "#tooth: `{thmName}` has no binder named `{hypName}`.\nBinders:\n{← binderList xs}"
    let hv := xs[i]!.fvarId!
    if body.hasAnyFVar (· == hv) then
      throwError "#tooth REFUSED: the CONCLUSION of `{thmName}` mentions `{hypName}`, so \
`{thmName}` minus `{hypName}` is not a statement."
    for j in [i + 1 : xs.size] do
      let t ← inferType xs[j]!
      if t.hasAnyFVar (· == hv) then
        let d ← xs[j]!.fvarId!.getDecl
        throwError "#tooth REFUSED: binder `{d.userName}` of `{thmName}` depends on `{hypName}`, \
so the residual cannot be deleted in isolation."
    mkForallFVars (eraseAt xs i) body

/-! ## §2 — the residual, and the refusals it must survive -/

/-- Is this binder's type an arrow / `∀` (i.e. a HASH-like parameter rather than an instance datum)? -/
def isArrowType (e : Expr) : MetaM Bool := do
  return (← whnfR e).isForall

/-- Run `k` with `T`'s telescope as fvars, the residual binder's index, and the residual `R`.
Applies REFUSALS §3.1 and §3.2. -/
def withResidual {α : Type} (thmName hypName : Name)
    (k : Array Expr → Nat → Expr → MetaM α) : MetaM α := do
  forallTelescope (← freshType thmName) fun xs body => do
    let _ := body
    let some i ← findBinder xs hypName
      | throwError "#tooth: `{thmName}` has no binder named `{hypName}`.\nBinders:\n{← binderList xs}"
    let dom ← inferType xs[i]!
    let some r := peelNot? dom
      | throwError "#tooth REFUSED: binder `{hypName}` of `{thmName}` has type\n  {dom}\nwhich is \
not of the form `¬ R`. A residual is a NEGATED break event; anything else is an ordinary hypothesis \
and this checker says nothing about it."
    -- §3.2 — a universally quantified side condition IS injectivity rewritten.
    if r.isForall then
      throwError "#tooth REFUSED: the residual of `{hypName}` is\n  {r}\na ∀-quantified side \
condition. `¬ ∀ xs ys, Coll xs ys` is injectivity rewritten, not a per-instance residual."
    -- §3.1 — the residual must NAME an instance, not merely a hash.
    let mut namesDatum := false
    for j in [0 : xs.size] do
      if j == i then continue
      if !(r.hasAnyFVar (· == xs[j]!.fvarId!)) then continue
      unless ← isArrowType (← inferType xs[j]!) do namesDatum := true
    unless namesDatum do
      throwError "#tooth REFUSED: the residual\n  {r}\nmentions only arrow-typed binders of \
`{thmName}` — i.e. it is a GLOBAL break event about the hash alone. That disjunct is supplied by \
the same pigeonhole that refutes the floor (see `Circuit.SpongeCollisionShirk.orBreak_sponge-\
Collision_iff_True`). A sound residual NAMES THE PAIR."
    k xs i r

/-! ## §3 — `tooth_minus%`: state the tooth from the theorem, do not write it -/

/-- `tooth_minus% T hno` elaborates to `T`'s statement with the residual binder `hno` deleted.
Write the tooth as `theorem foo_uf : ¬ tooth_minus% foo hno := …` and it cannot drift. -/
elab "tooth_minus% " t:ident h:ident : term => do
  let thmName ← realizeGlobalConstNoOverloadWithInfo t
  minusOf thmName h.getId

/-! ## §4 — the checking commands -/

/-- Diagnostic: `T`'s binder telescope. -/
elab "#tooth_binders " t:ident : command => do
  let thmName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  liftTermElabM do
    let ci ← getConstInfo thmName
    forallTelescope ci.type fun xs body => do
      logInfo m!"{thmName}:\n{← binderList xs}\n⊢ {body}"

/-- `#tooth_minus T drops hno` — print the ONLY admissible `_unconditional_false` statement. -/
elab "#tooth_minus " t:ident " drops " h:ident : command => do
  let thmName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  liftTermElabM do
    let m ← minusOf thmName h.getId
    logInfo m!"the tooth for `{thmName}` must be:\n  ¬ ({m})"

/-- `#tooth_residual T drops hno` — print the residual and run the refusals. -/
elab "#tooth_residual " t:ident " drops " h:ident : command => do
  let thmName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  liftTermElabM do
    withResidual thmName h.getId fun _ _ r => do
      logInfo m!"residual of `{thmName}`.`{h.getId}`:\n  {r}\n(passed the three refusals)"

/-- The leaves of a nested `And`. `C₁ ∧ (C₂ ∧ C₃)` ↦ `#[C₁, C₂, C₃]`, and `C` ↦ `#[C]`. -/
partial def andLeaves (e : Expr) : Array Expr :=
  if e.isAppOfArity ``And 2 then
    let args := e.getAppArgs
    andLeaves args[0]! ++ andLeaves args[1]!
  else #[e]

/-- **THE DERIVABILITY RELATION `T ⟹ S`** — is `S` reachable from `T` by moves that a refutation of
`S` can be pushed back through? If `T ⟹ S` then `T → S`, hence `¬ S → ¬ T`, so a tooth refuting `S`
really does refute `T`. Exactly three moves, and the omissions are the point:

  * **KEEP** a binder whose domain both statements agree on (recurse under it);
  * **INSTANTIATE** a DATA binder — plain `∀`-elimination, no proof obligation. This is how a tooth
    that pins the hash at a concrete collapsing one (`StateCommitLeafRegrounded.compress_binds_-
    unconditional_false` at `constNode`) is sound: it refutes ONE instance of a `∀ h`, which refutes
    the `∀`;
  * **WEAKEN THE CONCLUSION** to an `And`-leaf — refuting less refutes more.

**NOT a move: instantiating a `Prop` binder, i.e. dropping a hypothesis.** That is the move both
measured defects made, and it goes the wrong way: fewer hypotheses is a STRONGER statement, whose
refutation is weaker and says nothing about `T`. `isProp` is the whole guard, and it is why
`capHeapOpen_unconditional_false` cannot reach `capHeapOpen_implies_authorizedB` minus `hno` — it
would have to discard `FaithfulCapTree`, `hget`, `hmask` and `hwrite`. -/
partial def derives (T S : Expr) : MetaM Bool := do
  if ← commitWhen (isDefEq T S) then return true
  if !T.isForall then
    -- conclusion position: only an `And`-leaf weakening is allowed.
    if S.isForall then return false
    for l in andLeaves T do
      if ← commitWhen (isDefEq l S) then return true
    return false
  match T with
  | .forallE n d b bi =>
    if S.isForall then
      let keep ← commitWhen do
        match S with
        | .forallE _ d' b' _ =>
          if ← isDefEq d d' then
            withLocalDecl n bi d fun x => derives (b.instantiate1 x) (b'.instantiate1 x)
          else pure false
        | _ => pure false
      if keep then return true
    -- ∀-elimination is available only for DATA binders; a Prop binder is a hypothesis and
    -- discarding it refutes a different, weaker statement.
    if ← Meta.isProp d then return false
    commitWhen do
      let mv ← mkFreshExprMVar d
      derives (b.instantiate1 mv) S
  | _ => return false

/-- Peel a tooth's leading `∀`s down to the negation it makes. `∀ RH, ¬ S RH` refutes `S RH₀` for
any `RH₀`, so a leading universal is sound and merely has to be got out of the way. -/
partial def withRefutedStatement {α : Type} (ty : Expr) (k : Expr → MetaM α) : MetaM α := do
  match peelNot? ty with
  | some s => k s
  | none =>
    match ty with
    | .forallE n d b bi => withLocalDecl n bi d fun x => withRefutedStatement (b.instantiate1 x) k
    | _ => throwError "the tooth is not a negation: it states\n  {ty}"

/-- **`#tooth_unconditional_false U for T drops hno`** — ERROR unless refuting `U` refutes `T` minus
`hno`, where `T minus hno` is COMPUTED from `T` (see `minusOf`) rather than compared against a
hand-written statement. That is the whole of "same binders": the tooth's obligation is not written
down anywhere a copy could drift from.

Reports **EXACT** when `U` is literally `¬ (T minus hno)`, and **DERIVED** when it is a sound
consequence by `derives` (a concluding `And`-leaf, and/or data binders instantiated). It REFUSES the
move both measured defects made — dropping a hypothesis alongside the residual. -/
elab "#tooth_unconditional_false " u:ident " for " t:ident " drops " h:ident : command => do
  let uName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo u
  let thmName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  liftTermElabM do
    let m ← minusOf thmName h.getId
    let want := mkApp (.const ``Not []) m
    let uTy ← freshType uName
    if ← isDefEq uTy want then
      logInfo m!"#tooth_unconditional_false [EXACT]: `{uName}` IS `{thmName}` minus `{h.getId}`, \
refuted."
      return
    withRefutedStatement uTy fun sTy => do
      unless ← derives m sTy do
        throwError "#tooth_unconditional_false FAILED.\n`{uName}` refutes\n  {sTy}\nwhich is NOT \
reachable from `{thmName}` minus `{h.getId}`\n  {m}\nby ∀-elimination of DATA binders or weakening \
of the conclusion. The move it needs is dropping a HYPOTHESIS, which refutes a strictly weaker \
statement and establishes nothing about this one."
      logInfo m!"#tooth_unconditional_false [DERIVED]: `{uName}` refutes\n  {sTy}\nwhich \
`{thmName}` minus `{h.getId}` implies, so it refutes the tooth's obligation."

/-- Every metavariable occurring in `e` that is assigned; fails the check if any assignment still
has free variables or unassigned metavariables (i.e. is not a CLOSED witness). -/
def assignmentsClosed (mvars : Array Expr) : MetaM (Array (Nat × Expr) × Array Nat) := do
  let mut closed : Array (Nat × Expr) := #[]
  let mut open_ : Array Nat := #[]
  for i in [0 : mvars.size] do
    let v ← instantiateMVars mvars[i]!
    if v.isMVar then continue
    if v.hasFVar || v.hasExprMVar then open_ := open_.push i
    else closed := closed.push (i, v)
  return (closed, open_)

/-- **`#tooth_refutable R for T drops hno`** — ERROR unless `R` exhibits `T`'s OWN residual holding
at a CLOSED instance.

"Its own residual" is definitional equality against the residual read off `T`'s binder, with `T`'s
telescope as metavariables; "closed instance" is that every assignment the match makes is a term
with no free variables and no unassigned metavariables. A `_refutable` about a hand-picked pair of
some OTHER predicate cannot match. -/
elab "#tooth_refutable " rt:ident " for " t:ident " drops " h:ident : command => do
  let rName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo rt
  let thmName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  liftTermElabM do
    -- run the refusals on the surface form first
    withResidual thmName h.getId fun _ _ _ => pure ()
    let (mvars, _, _) ← forallMetaTelescope (← freshType thmName)
    let (idx, _) ← binderIndexAndNames thmName h.getId
    let some i := idx | throwError "#tooth: `{thmName}` has no binder named `{h.getId}`"
    let dom ← inferType mvars[i]!
    let some r := peelNot? dom | throwError "#tooth: binder `{h.getId}` is not `¬ R`"
    let rTy ← freshType rName
    unless ← isDefEq rTy r do
      throwError "#tooth_refutable FAILED.\n`{rName}` states\n  {rTy}\nwhich is not an instance \
of `{thmName}`'s residual\n  {r}\nA refutation of some OTHER predicate is not a refutation of this \
residual."
    let (closed, open_) ← assignmentsClosed mvars
    unless open_.isEmpty do
      throwError "#tooth_refutable FAILED: `{rName}` leaves binders of `{thmName}` \
UNINSTANTIATED or open ({open_}). A refutability tooth must name a CLOSED instance."
    logInfo m!"#tooth_refutable: `{rName}` exhibits `{thmName}`'s residual at {closed.size} \
closed witnesses."

/-- **`#tooth_fires F for T drops hno`** — ERROR unless `F` states that `T`'s OWN residual FAILS,
at an instance that is UNIVERSAL in every arrow-typed (hash) binder.

The universality is the whole content: `aggColl_fires` holds for EVERY sponge, with no floor, which
is exactly the separation a global-existential disjunct provably cannot make. A `_fires` stated at
a named concrete hash is a `_refutable` wearing the wrong name and is REFUSED here. -/
elab "#tooth_fires " f:ident " for " t:ident " drops " h:ident : command => do
  let fName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo f
  let thmName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  liftTermElabM do
    withResidual thmName h.getId fun _ _ _ => pure ()
    let fTy ← freshType fName
    let (idx, _) ← binderIndexAndNames thmName h.getId
    forallTelescope fTy fun ys concl => do
      let (mvars, _, _) ← forallMetaTelescope (← freshType thmName)
      let some i := idx | throwError "#tooth: `{thmName}` has no binder named `{h.getId}`"
      let dom ← inferType mvars[i]!
      let some r := peelNot? dom | throwError "#tooth: binder `{h.getId}` is not `¬ R`"
      unless ← isDefEq concl (mkApp (.const ``Not []) r) do
        throwError "#tooth_fires FAILED.\n`{fName}` concludes\n  {concl}\nwhich is not `¬` of \
`{thmName}`'s residual\n  {r}"
      -- every arrow-typed binder the residual mentions must be UNIVERSAL in `F`.
      let ysSet := ys.map (fun e => e.fvarId!)
      for j in [0 : mvars.size] do
        if j == i then continue
        let ty ← inferType mvars[j]!
        unless ← isArrowType ty do continue
        let v ← instantiateMVars mvars[j]!
        if v.isMVar then continue
        let univ := match v with
          | .fvar id => ysSet.contains id
          | _ => false
        unless univ do
          throwError "#tooth_fires FAILED: `{fName}` instantiates the arrow-typed binder {j} \
of `{thmName}` at\n  {v}\nrather than quantifying over it. A `_fires` tooth must hold for EVERY \
hash — pinned at one hash it is a `_refutable`, not a firing."
      logInfo m!"#tooth_fires: `{fName}` refutes `{thmName}`'s residual, universally in every hash."

/-! ## §5 — reading the counterexample OUT of a hand-written tooth

`_unconditional_false` cannot be derived (see `Circuit.ToothCombinator`, §"what is irreducible"):
it needs a counterexample STATE satisfying every surviving hypothesis, and those proofs are domain
facts (`empty_caps_unauthorized`, `omitting_engine_sound`). What CAN be recovered mechanically is
WHICH state a hand-written tooth used — it is the argument vector the proof applies the universal
to — and that is enough to check the third defect. -/

/-- Every application of the fvar `f` inside `e`, as its argument vector. -/
partial def collectApps (f : FVarId) : Expr → Array (Array Expr) → Array (Array Expr)
  | e@(.app a b), acc =>
      let acc := if e.getAppFn == .fvar f then acc.push e.getAppArgs else acc
      collectApps f b (collectApps f a acc)
  | .lam _ t b _, acc => collectApps f b (collectApps f t acc)
  | .forallE _ t b _, acc => collectApps f b (collectApps f t acc)
  | .letE _ t v b _, acc => collectApps f b (collectApps f v (collectApps f t acc))
  | .mdata _ b, acc => collectApps f b acc
  | .proj _ _ b, acc => collectApps f b acc
  | _, acc => acc

/-- The counterexample tuples a `¬ (∀ …)` tooth applies its hypothesis to, longest first. -/
def witnessesOf (uName : Name) : MetaM (Array (Array Expr)) := do
  let ci ← getConstInfo uName
  let some v := (match ci with
      | .thmInfo ti => some ti.value
      | .defnInfo di => some di.value
      | _ => none)
    | throwError "#tooth_witness: `{uName}` has no proof term (axiom / opaque?)"
  lambdaTelescope v fun ys body => do
    if ys.isEmpty then
      throwError "#tooth_witness: `{uName}`'s proof does not open with the universal it refutes \
(no leading λ). A tooth of the form `fun hall => …` is what this reads."
    let f := ys[0]!.fvarId!
    let apps := collectApps f body #[]
    return apps.qsort (fun a b => a.size > b.size)

/-- **`#tooth_witness U`** — the counterexample tuple `U`'s proof feeds the universal it refutes.
The instance lives inside the proof, invisible in the type; this puts it on screen. -/
elab "#tooth_witness " u:ident : command => do
  let uName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo u
  liftTermElabM do
    let apps ← witnessesOf uName
    if apps.isEmpty then
      logWarning m!"#tooth_witness: `{uName}` never applies the universal it refutes — its \
counterexample is not an instantiation and cannot be compared."
    else
      let mut out : Array MessageData := #[]
      for a in apps do
        out := out.push m!"({a.size} args) {a.toList}"
      logInfo m!"#tooth_witness {uName}:\n{MessageData.joinSep out.toList "\n"}"

/-- What an instance of `T`'s residual assigns to each of `T`'s binders, keyed by the binder's NAME
— the `ROLE`. Unification (not structural zipping) does the work, so a residual whose pair is buried
inside an extractor call (`SpongeColl sponge (aggCollFind sponge a b rows rows')`) yields roles for
`a`, `b`, `rows`, `rows'` just as one whose arguments are the pair itself. -/
def rolesOfInstance (thmName hypName instName : Name) : MetaM (Array (Name × Expr)) := do
  let (idx, names) ← binderIndexAndNames thmName hypName
  let some i := idx | throwError "#tooth: `{thmName}` has no binder named `{hypName}`"
  let (mvars, _, _) ← forallMetaTelescope (← freshType thmName)
  let dom ← inferType mvars[i]!
  let some r := peelNot? dom | throwError "#tooth: binder `{hypName}` is not `¬ R`"
  let iTy ← freshType instName
  unless ← isDefEq iTy r do
    throwError "`{instName}` states\n  {iTy}\nwhich is not an instance of `{thmName}`'s residual\n\
  {r}\nA fact about some OTHER predicate is not a fact about this residual."
  let mut out : Array (Name × Expr) := #[]
  for j in [0 : mvars.size] do
    if j == i then continue
    let v ← instantiateMVars mvars[j]!
    if v.isMVar then continue          -- the residual does not mention this binder
    out := out.push (names[j]!, v)
  return out

/-- **⚑ `#tooth_same_witness U R for T drops hno`** — the SHARP check.

`U` breaks `T` minus `hno` at some tuple; `R` exhibits the residual at some tuple. Unless those are
the SAME tuple, `R` does not establish that `hno` is the hypothesis excluding `U`'s counterexample —
it establishes only that the residual is non-empty somewhere. That gap is the third measured defect
(`seamKernelColl_refutable` fires at `(honestStep, richStep)`; the counterexample is at
`(honestStep, honestStep)`).

Comparison is BY ROLE, not by position: `T`'s residual is structurally zipped against `R`'s type to
learn what `R` instantiated `s`/`s'`/`sponge` to, and the counterexample tuple read out of `U`'s
proof is indexed by the binder of `U`'s OWN statement carrying the same name. So it still answers
when `U`'s telescope is not `T`'s — which is the situation at
`HistoryAggregation.root_tooth_pins_kernel_unconditional_false`, where the structural envelope is
dropped alongside the residual and the file says so. -/
elab "#tooth_same_witness " u:ident rt:ident " for " t:ident " drops " h:ident : command => do
  let uName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo u
  let rName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo rt
  let thmName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  liftTermElabM do
    -- (a) what `R` instantiated each of `T`'s binders to.
    let roleVals ← rolesOfInstance thmName h.getId rName
    -- (b) the counterexample tuple `U`'s proof feeds its own universal, indexed by `U`'s binders.
    let uTy ← freshType uName
    let some sTy := peelNot? uTy
      | throwError "#tooth_same_witness: `{uName}` is not a negation."
    let uNames ← forallTelescope sTy fun ys _ => do
      let mut ns : Array Name := #[]
      for y in ys do ns := ns.push (← y.fvarId!.getDecl).userName
      return ns
    let apps ← witnessesOf uName
    let some ws := apps[0]? | throwError "#tooth_same_witness: `{uName}` never applies the \
universal it refutes; its counterexample cannot be compared."
    let mut agree : Array Name := #[]
    let mut differ : Array MessageData := #[]
    let mut unseen : Array Name := #[]
    for (n, v) in roleVals do
      match uNames.findIdx? (· == n) with
      | none => unseen := unseen.push n
      | some p =>
        match ws[p]? with
        | none => unseen := unseen.push n
        | some w =>
          if ← isDefEq w v then agree := agree.push n
          else differ := differ.push m!"role `{n}`: the counterexample of `{uName}` uses\n    \
{w}\n  but `{rName}` fires at\n    {v}"
    unless differ.isEmpty do
      throwError "#tooth_same_witness FAILED — `{rName}` does NOT fire at the instance `{uName}` \
breaks at:\n{MessageData.joinSep differ.toList "\n"}\nSo `{rName}` shows only that the residual is \
non-empty SOMEWHERE; it does not identify `{h.getId}` as the hypothesis that excludes THIS \
counterexample."
    if agree.isEmpty then
      throwError "#tooth_same_witness INCONCLUSIVE: no role of `{thmName}`'s residual was \
determined on both sides (unmatched: {unseen}). A green verdict here would be vacuous."
    logInfo m!"#tooth_same_witness: `{rName}` fires at exactly the instance `{uName}` breaks at \
(roles agreeing: {agree}; undetermined: {unseen})."

end Dregg2.Verify.ToothCheck
