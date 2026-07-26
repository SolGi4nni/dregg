/-
# Dregg2.Verify.InjSpelling — the INLINE `Function.Injective` spelling of a refuted floor.

`#floor_ratchet` keys on NAMED floor constants (`compressNInjective`, `Poseidon2SpongeCR`,
`cellLeafInjective`, …). A floor spelled INLINE as `Function.Injective f` sails straight through,
and the gate's own log said so on every run: "N `Function.Injective`-spelled sites ungated (known
residual)". That is a zero-cost bypass — `Poseidon2SpongeCR f` is *definitionally*
`Function.Injective f` at `f : List ℤ → ℤ`, so `(hCR : Poseidon2SpongeCR f)` is gated and
`(hCR : Function.Injective f)` is not, for the identical hypothesis.

This module supplies the missing half of the DETECTION side. It does not decide anything by name.

## The split, and why it is a split

Injectivity is not automatically refuted, so a blanket gate would be wrong in the noisy direction —
and a noisy gate gets disabled, which is how a gate is lost entirely.

  * A **COMPRESSING** function cannot be injective: `List ℤ → ℤ` at deployed BabyBear parameters
    (bounded range, infinite domain — the tree's own `HashFloorHonesty` teeth), or a whole-function
    digest `(CellId → AssetId → ℤ) → ℤ` (an UNCOUNTABLE domain into a countable codomain, refuted
    with no deployed hypothesis at all). Assuming injectivity there is the same sin as the named
    floors. GATED.
  * A **WIDENING or STRUCTURAL** function may be genuinely injective — `ℕ → List ℤ`, a constructor,
    a coordinate embedding, a parametric `β → ℤ` whose `β` is a type VARIABLE. Gating those is
    noise. NOT GATED.

## The refuted signature set is DERIVED, never hand-written

`signatures` computes the gated `(α, β)` pairs from the environment, two ways, both keyed on
CONTENT the tree already holds:

  * **Source A — the inline spelling of a named refuted floor.** For each floor `F` the ratchet has
    already DERIVED as refuted, keep it iff `F f` is DEFINITIONALLY `@Function.Injective α β f`,
    checked by `isDefEq` on a fresh local `f : α → β` — not by name, shape heuristic, or
    convention. Then writing `Function.Injective f` at those types IS writing `F f`, the
    declaration is exactly as vacuous, and the gate can say WHICH floor it is. Strength: whatever
    the named floor's is — for `List ℤ → ℤ`, refuted at deployed BabyBear parameters.
  * **Source B — an unconditional non-injectivity theorem.** An in-tree theorem
    `∀ …, ¬ Function.Injective (g : α → β)` whose `g` is universally quantified, whose `α`/`β` are
    concrete, and whose other hypotheses never mention `g`, says flatly that NO function of that
    signature is injective. Strength: total — no deployed parameter, no hash assumption.

So the way to gate a new compressing signature is to REFUTE it — either as a named floor, or as a
plain `¬ Function.Injective` theorem (`Dregg2/Verify/InjSpelledFloors.lean` does the latter for the
whole-function digests, by pure cardinality). The refutation is the content; the gate follows in
the same build, with no list to edit. And a signature with no in-tree refutation is NOT gated —
which is the honest reading of "we have not shown this one impossible", not a silent pass.

⚑ SCOPE, stated plainly. This gates HYPOTHESIS position only: a `∀`-binder whose domain is headed
by `Function.Injective` at a refuted signature. An occurrence in the conclusion is not an
assumption (and `¬ Function.Injective f` in the conclusion is a REFUTATION, the content the
campaign wants more of). Sites whose `α`/`β` are open (type variables, loose bvars) are NOT gated
and are reported as the parametric residual — `funcComponent (D : β → ℤ) (hD : Function.Injective D)`
with `β` a `Type` variable is genuinely parametric, and there are `β` at which it holds.
-/
import Lean

set_option autoImplicit false

namespace Dregg2.Verify.InjSpelling

open Lean Meta

/-- A REFUTED INLINE SIGNATURE: the domain/codomain pair of a refuted floor `F` whose application
`F f` is definitionally `@Function.Injective α β f`, together with the floor it is the spelling of
(so a gate failure can name the refutation the author is walking past). -/
structure Sig where
  /-- The injected function's domain. -/
  dom   : Expr
  /-- The injected function's codomain. -/
  cod   : Expr
  /-- The refuted floor this inline spelling is definitionally equal to. -/
  floor : Name
  deriving Inhabited

/-- **SOURCE A — the inline spelling of a NAMED refuted floor.**

A floor qualifies iff its type is `(α → β) → Prop` (one parameter, a NON-dependent function type)
and `F f` is `isDefEq` to `@Function.Injective α β f` for a fresh local `f`. Both halves matter:
the type shape is what makes `(α, β)` meaningful, and the `isDefEq` is what makes the claim
"this inline spelling IS that floor" a checked fact rather than a naming coincidence.

The strength here is exactly the named floor's: `Poseidon2SpongeCR` is refuted at DEPLOYED BabyBear
parameters (the domain `List ℤ` is countable, so injections exist in the abstract and the tree's
tooth needs the range bound). Gating the inline spelling therefore says precisely what gating the
named spelling says, which is the point — the two must not have different prices.

Floors that are NOT plain injectivity (`compressInjective`'s 2-to-1 `∀ a b c d, h a b = h c d →
a = c ∧ b = d`, `cellLeafInjective`'s per-index form, `MSISHard`'s `¬∃`) simply do not qualify and
contribute no signature — their inline spellings are a different residual, named in the report. -/
def signaturesOfFloors (floors : Array Name) : MetaM (Array Sig) := do
  let env ← getEnv
  let mut out : Array Sig := #[]
  for f in floors do
    let some ci := env.find? f | continue
    let .defnInfo di := ci | continue
    let .forallE _ dom body _ := di.type | continue
    unless body == .sort .zero do continue          -- `… → Prop`, exactly one parameter
    let .forallE _ a b _ := dom | continue          -- the parameter is a function type
    if a.hasLooseBVars || b.hasLooseBVars then continue   -- non-dependent, closed
    let ok ←
      try
        withLocalDeclD `f dom fun x => do
          let inj ← mkAppM ``Function.Injective #[x]
          isDefEq (mkAppN (mkConst f (di.levelParams.map mkLevelParam)) #[x]) inj
      catch _ => pure false
    if ok then
      unless out.any (fun s => s.dom == a && s.cod == b) do
        out := out.push ⟨a, b, f⟩
  return out

/-- **SOURCE B — an UNCONDITIONAL non-injectivity theorem.**

A theorem of the form `∀ …, ¬ @Function.Injective α β g` where

  * `g` is one of the `∀`-bound variables — so the claim is about EVERY function of that type;
  * `α` and `β` mention no telescope variable — so the signature is a concrete deployed type, not
    a parametric one (`not_injective_of_uncountable_domain {A B} (f : A → B)` is skipped here, and
    must be: there are `A`, `B` at which injections abound); and
  * NO OTHER binder's type mentions `g` — so no side hypothesis narrows which functions are meant.

Such a theorem says flatly: **no function `α → β` is injective**. Then `(h : Function.Injective f)`
at that signature is a hypothesis this tree proves false with no deployed parameter in sight —
strictly stronger than the named-floor case, and with no judgement call anywhere in the rule.

`Verify/InjSpelledFloors` supplies these for the whole-function digests
(`(CellId → AssetId → ℤ) → ℤ`, `Caps → ℤ`, `BornEmptySideTables → ℤ`, …), by pure cardinality.
Writing one more is how a new compressing signature becomes gated; there is no list to edit. -/
def signaturesOfRefutations (ours : Array Name) : MetaM (Array Sig) := do
  let env ← getEnv
  let mut out : Array Sig := #[]
  for nm in ours do
    let some ci := env.find? nm | continue
    let .thmInfo _ := ci | continue
    let (hasInj, hasNot) :=
      ci.type.foldConsts (false, false) fun c (i, n) =>
        (i || c == ``Function.Injective, n || c == ``Not)
    unless hasInj && hasNot do continue
    let r : Option (Expr × Expr) ←
      try
        forallTelescope ci.type fun xs body => do
          let .app (.const ``Not _) arg := body | return none
          unless arg.isApp && arg.getAppFn.isConstOf ``Function.Injective do return none
          let args := arg.getAppArgs
          unless args.size ≥ 3 do return none
          let a := args[0]!
          let b := args[1]!
          let .fvar fid := args[2]! | return none
          unless xs.any (fun x => x.fvarId! == fid) do return none
          if a.hasFVar || b.hasFVar then return none
          for x in xs do
            if x.fvarId! == fid then continue
            if (← inferType x).containsFVar fid then return none
          return some (a, b)
      catch _ => pure none
    if let some (a, b) := r then
      unless out.any (fun s => s.dom == a && s.cod == b) do
        out := out.push ⟨a, b, nm⟩
  return out

/-- The whole refuted-signature set: the inline spellings of the named refuted floors (Source A)
plus the signatures an in-tree theorem proves admit NO injection at all (Source B). -/
def signatures (ours : Array Name) (floors : Array Name) : MetaM (Array Sig) := do
  let a ← signaturesOfFloors floors
  let b ← signaturesOfRefutations ours
  let mut out := a
  for s in b do
    unless out.any (fun t => t.dom == s.dom && t.cod == s.cod) do out := out.push s
  return out

/-- Pretty key for a signature/occurrence, used for the residual histogram and for memoizing
`isDefEq` verdicts. -/
def sigKey (a b : Expr) : MetaM String := do
  pure s!"{← ppExpr a} ⟶ {← ppExpr b}"

/-- Every `@Function.Injective α β f` occurrence in HYPOTHESIS position of `ty`, read off the
`∀`-spine WITHOUT instantiating (binder domains carry loose bvars; occurrences whose `α`/`β` are
open are returned as-is and rejected by the caller). -/
def injBinders (ty : Expr) : Array (Expr × Expr) := Id.run do
  let mut t := ty
  let mut out : Array (Expr × Expr) := #[]
  while t.isForall do
    let d := t.bindingDomain!
    if d.isApp && d.getAppFn.isConstOf ``Function.Injective then
      let args := d.getAppArgs
      if args.size ≥ 3 then out := out.push (args[0]!, args[1]!)
    t := t.bindingBody!
  return out

/-- The verdict for one declaration TYPE.

`some n` — it binds `Function.Injective f` at a REFUTED signature, and `n` names the refutation:
either a floor this inline spelling is definitionally equal to (false at deployed BabyBear
parameters) or a theorem that no function of that type is injective at all (false everywhere).
GATE IT: the declaration says nothing about the deployed system either way.

`none` — either it binds no inline injectivity in hypothesis position, or the signatures it binds
have no in-tree refutation (widening / structural / parametric). NOT gated. -/
def classify (sigs : Array Sig) (memo : IO.Ref (Std.HashMap String (Option Name))) (ty : Expr) :
    MetaM (Option Name) := do
  for (a, b) in injBinders ty do
    if a.hasLooseBVars || b.hasLooseBVars then continue
    -- structural first: elaborated types agree constant-for-constant across the tree, so this is
    -- the hit path and costs no unfolding.
    let mut found : Option Name := none
    for s in sigs do
      if found.isNone && s.dom == a && s.cod == b then found := some s.floor
    if let some fl := found then return some fl
    -- δ-fallback, memoized: `Caps` vs `Label → List Cap` is the same signature spelled through an
    -- `abbrev`, and a gate that misses it under-measures — the exact failure this module repairs.
    let key ← sigKey a b
    match (← memo.get).get? key with
    | some v => if v.isSome then return v
    | none =>
      let mut v : Option Name := none
      for s in sigs do
        if v.isNone then
          let eq ← (try isDefEq s.dom a catch _ => pure false)
          if eq then
            let eq2 ← (try isDefEq s.cod b catch _ => pure false)
            if eq2 then v := some s.floor
      memo.modify (·.insert key v)
      if v.isSome then return v
  return none

/-- The residual: the inline-injectivity signatures a type binds that are NOT gated, as printable
keys. This is what makes the exempt half ACCOUNTED FOR rather than waved away — the report
histograms them, so "579 ungated" becomes a list of signatures with counts and a reason. -/
def residualKeys (sigs : Array Sig) (ty : Expr) : MetaM (Array String) := do
  let mut out : Array String := #[]
  let bs := injBinders ty
  if bs.isEmpty then
    -- `Function.Injective` occurs in the type but in NO hypothesis: it is in the conclusion (a
    -- refutation, or a statement that some construction IS injective), or inside a binder's own
    -- pi. Nothing is being assumed, so nothing is gated — but it must still be COUNTED, or the
    -- residual total silently disagrees with the site count.
    return #["«conclusion-or-nested», nothing assumed"]
  for (a, b) in bs do
    if a.hasLooseBVars || b.hasLooseBVars then
      unless out.contains "«open» ⟶ «open»" do out := out.push "«open» ⟶ «open»"
      continue
    let mut hitS := false
    for s in sigs do
      if s.dom == a && s.cod == b then hitS := true
    unless hitS do
      let k ← sigKey a b
      unless out.contains k do out := out.push k
  return out

end Dregg2.Verify.InjSpelling
