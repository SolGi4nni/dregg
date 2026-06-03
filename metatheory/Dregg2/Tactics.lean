/-
# Dregg2.Tactics — shared proof automation for the dregg2 metatheory.

Small helpers shared across modules and executable protocols. These close genuinely routine
goals (reflexivity, definitional simp, injection cleanup, linear arithmetic) — not a way
to make a real obligation look discharged. If a helper does not close a goal, the goal is
real: prove it properly or leave an explicit `sorry` with a one-line reason.
(Never `admit`, never a fresh `axiom`, never `native_decide` on a non-decidable prop.)
-/
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Ring
import Lean

/-! ## Axiom-hygiene tripwire — the `sorryAx` regression guard.

`#assert_axioms` elaborates to an error if the named declaration's axiom set escapes
`{propext, Classical.choice, Quot.sound}` (notably: any `sorryAx`). It can only reject,
never close a goal. Pin it under each proved keystone.

Defined at top level (outside the namespace) so the command token parses in every
importing module without needing `open`.

(Honest note on §8 oracles: `CryptoKernel`/`World`/`Verifiable` obligations enter as
typeclass parameters/hypotheses, NOT `axiom`-keyword declarations, so they do not appear
in `collectAxioms` and do not trip this guard. A genuine `axiom`-keyword oracle, were one
ever added, would need to be allow-listed by name with a comment — by design.) -/

open Lean Elab Command in
/-- `#assert_axioms foo` errors unless every axiom `foo` depends on is one of the three
standard kernel axioms (`propext`, `Classical.choice`, `Quot.sound`). In particular it
FAILS on `sorryAx`, catching a silent `sorry`-inheritance at build time. -/
elab "#assert_axioms" id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← Lean.collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := axs.filter (fun a => !allowed.contains a)
  unless bad.isEmpty do
    throwError "axiom-hygiene FAIL: {name} depends on non-kernel axioms {bad.toList} \
      (a `sorryAx` here means a silent `sorry` leaked into a 'PROVED' keystone)"

/-! ## `#assert_namespace_axioms` — module-wide axiom-hygiene pinning.

`#assert_namespace_axioms` pins every theorem under a namespace to the three standard
kernel axioms in one line: it walks `getEnv`, finds every theorem under the prefix, runs
`collectAxioms`, and throws if any depends on an axiom outside
`{propext, Classical.choice, Quot.sound}` (notably `sorryAx`). Pure rejector — it can only
error, never close a goal.

**The `except` list (honesty caveat).** A name in the `except` clause is skipped (and
reported). Use this for keystones that legitimately rest on a §8 oracle or a Law-1
`sorry`'d primitive — each skip must be justified by a comment, preserving the discipline
that a keystone resting on a primitive is not pinned.

(Like `#assert_axioms`, this only sees `axiom`-keyword declarations; §8 oracles that enter
as typeclass parameters / hypotheses do not appear in `collectAxioms`. By design.) -/

/-- `#assert_namespace_axioms NS (except a b …)?` — pin EVERY theorem under namespace `NS` to the
three standard kernel axioms, erroring on the first one that escapes (a `sorryAx` ⇒ a silent
`sorry` leaked). Names listed in `except` are skipped (they legitimately rest on a §8/Law-1
primitive — justify each with a comment). Logs the count pinned. Pure rejector. -/
syntax (name := assertNamespaceAxioms)
  "#assert_namespace_axioms" ident (" except " ident+)? : command

open Lean Elab Command in
elab_rules : command
  | `(command| #assert_namespace_axioms $ns:ident $[ except $excIds:ident*]?) => do
  let env ← getEnv
  let prefixName := ns.getId
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  -- Resolve the `except` names to fully-qualified constants (a typo is an `unknownConstant`
  -- error here, so the allow-out list cannot silently drift — same discipline as a bad pin).
  let exceptIdents : Array Ident := match excIds with
    | some arr => arr
    | none => #[]
  let exceptNames ← exceptIdents.toList.mapM fun id =>
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo id.raw
  let mut checked : Nat := 0
  let mut skipped : Nat := 0
  let mut seenExcept : List Name := []
  -- Walk the whole environment; `env.constants` is an `SMap Name ConstantInfo`.
  for (name, info) in env.constants.toList do
    -- direct or nested members of the namespace (`Dregg2.Spec.Guard.admits_all` etc.)
    unless prefixName.isPrefixOf name && prefixName != name do continue
    -- theorems only — skip defs, inductives, constructors, recursors, axioms themselves
    unless info.isThm do continue
    -- skip compiler-internal names (`_proof_`, `.match_`, equation lemmas, …)
    if name.isInternalDetail then continue
    if exceptNames.contains name then
      skipped := skipped + 1
      seenExcept := name :: seenExcept
      continue
    let axs ← collectAxioms name
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      throwError "axiom-hygiene FAIL: {name} depends on non-kernel axioms {bad.toList} \
        (a `sorryAx` here means a silent `sorry` leaked into a 'PROVED' keystone). \
        If this keystone legitimately rests on a §8/Law-1 primitive, add it to the \
        `except` clause with a justifying comment — do NOT weaken the theorem to pass."
    checked := checked + 1
  -- An `except` name that matched nothing in the namespace is dead allow-listing — surface it
  -- (a renamed/retired keystone left in the allow-out list is itself a drift to catch).
  for e in exceptNames do
    unless seenExcept.contains e do
      logWarning m!"#assert_namespace_axioms {prefixName}: `except` name {e} matched no \
        pinned theorem in this namespace (retired/renamed? remove it from the allow-out list)"
  logInfo m!"#assert_namespace_axioms {prefixName}: {checked} theorems pinned kernel-clean\
    {if skipped > 0 then m!", {skipped} skipped via `except`" else m!""}"

namespace Dregg2.Tactics

/-- `dregg_auto` — best-effort closer for *routine* obligations only: reflexivity,
`trivial`, definitional/hypothesis `simp`, linear arithmetic, propositional tautology.
Use it as the last step of a proof; if it fails, the goal carries real content. -/
macro "dregg_auto" : tactic =>
  `(tactic| first
    | rfl
    | trivial
    | (intros; first | rfl | trivial | simp_all | omega | tauto)
    | simp_all
    | omega
    | tauto)

/-- `option_inj at h` — collapse `some x = some y` (and any nested `(·,·) = (·,·)`) in `h`
to its component equalities; the standard first move when reading back a protocol step
that returned `some (newState…)`. -/
macro "option_inj" "at" h:ident : tactic =>
  `(tactic| simp only [Option.some.injEq, Prod.mk.injEq] at $h:ident)

/-! ## Effect-arm combinators (per-effect dispatch-proof helpers).

The `cases fa with` dispatch proofs over `FullActionA` repeat a small vocabulary of moves
per arm: reject the `none` (fail-closed) branch, substitute the committed state on `some`,
peel an `if gate then … else none`, discharge a balance-neutral edit. Each combinator below
expands to exactly those tactic steps — no oracle, no `native_decide`, so a wrong arm still
fails loudly. -/

/-- `reject_none h hk` — the FAIL-CLOSED `none` branch. `hk : f = none` rewrites the commit
hypothesis `h : f = some _` to `none = some _`, closed by `absurd`. -/
macro "reject_none" h:ident hk:ident : tactic =>
  `(tactic| (rw [$hk:ident] at $h:ident; exact absurd $h:ident (by simp)))

/-- `commit_subst h hk` — the `some` branch. `hk : f = some k'` rewrites `h`, peels the
`some`-injection, and substitutes the committed state into the goal. -/
macro "commit_subst" h:ident hk:ident : tactic =>
  `(tactic| (rw [$hk:ident] at $h:ident; simp only [Option.some.injEq] at $h:ident; subst $h:ident))

/-- `gate_peel hk with finisher` — peel an `if guard then some _ else none` inside a chained step
`hk : (if … then some _ else none) = some _`. Uses `split` (so the guard need NOT be named): the
`then` branch substitutes the committed kernel and runs `finisher`; the `else` branch is
FAIL-CLOSED against `hk`. -/
macro "gate_peel" hk:ident " with " fin:tactic : tactic =>
  `(tactic|
    (split at $hk:ident
     · simp only [Option.some.injEq] at $hk:ident
       subst $hk:ident
       $fin
     · exact absurd $hk:ident (by simp)))

-- NOTE: the balance-NEUTRAL finisher `bal_neutral` (the fourth combinator) lives in
-- `Dregg2/Exec/RecordKernel.lean`, next to the per-asset measure (`recTotalAssetWithEscrow`)
-- it unfolds — a tactic-macro must reference user globals from a site where they are in
-- scope (macro hygiene resolves the simp-lemma names at the DEFINITION site, not the use
-- site), so a domain-specific finisher belongs with its domain, not in this generic file.

end Dregg2.Tactics
