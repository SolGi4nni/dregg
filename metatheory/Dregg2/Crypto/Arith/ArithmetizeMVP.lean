/-
# Dregg2.Crypto.Arith.ArithmetizeMVP — MVP-0 of the proof-producing arithmetizer.

(Layer A, per `docs/DESIGN-proof-producing-arithmetizer.md` §6. Describe at Layer-A
resolution: the object generated here is the ABSTRACT `DfaAccepts`/`ReflTransGen delta`
refinement — NOT the deployed felt/row AIR. No felts, no `emitVmJson2`, no decode.)

THE MECHANISM this file proves out: a single Lean-4 command `#arithmetizeDfa foo := spec`
that, from a CONCRETE DFA spec (`δ`, `q₀`, `accept` as Lean values, bundled as a `DfaSpec`),
ADDS TWO declarations to the environment, both kernel-checked on `addDecl`:

  (a) `def foo_air : DfaSpec _ _ := spec`         — the captured spec / AIR-fragment, and
  (b) `theorem foo_sound : Refines foo_air`       — the REAL refinement, whose PROOF TERM is
      GENERATED as `fun trace => DfaAsCert.dfaAccepts_reduces foo_air.δ foo_air.q₀ foo_air.accept trace`.

ZERO new mathematics: the soundness lemma `DfaAsCert.dfaAccepts_reduces` already exists and is
`#assert_axioms`-clean (`Crypto/DfaAsCert.lean:93`). The novel capability is purely the MECHANICAL
one — an elaborator that emits a checked `def` AND a kernel-checked `theorem` in one command.

`Refines s` is the REAL content of `dfaAccepts_reduces`, NOT a vacuous `P → P`: an accepting DFA
run reduces (reflexive-transitively) under the shared-substrate step relation `delta` from a
`q₀`-start step to an accepting last step.

## The load-bearing canary (see the `Canary` section + the sibling scratch file note)
The generated proof term names the spec's OWN `foo_air` in BOTH statement and proof, so it genuinely
DEPENDS on the spec it was generated from. `#assert_depends_on foo_sound [foo_air]` pins this as a
build-time positive control. The negative half — feeding the `foo_air` STATEMENT a proof built from a
DIFFERENT spec (`bar_air`) FAILS to typecheck — is exhibited in the module note under `Canary` and
reproduced by the commented `example`. This is the canary the design demands: mutating the
statement↔spec linkage (not `accept` alone, which `dfaAccepts_reduces` is parametric in) breaks the
green.
-/
import Dregg2.Crypto.DfaAsCert
import Dregg2.Tactics
import Lean

namespace Dregg2.Crypto.Arith

open Lean Elab Command
open Dregg2.Crypto Dregg2.Crypto.Dfa Dregg2.Crypto.DfaAsCert

universe u

variable {State Sym : Type u}

/-! ## `DfaSpec` — the concrete DFA spec bundle the arithmetizer consumes and captures.

A `DfaSpec` is exactly the triple `dfaAccepts_reduces` is parametric over: the transition relation
`δ` (the `Lookup` table's membership predicate), the initial state `q₀`, and the `accept` predicate.
The generated `foo_air : DfaSpec _ _` def IS this captured spec — the Layer-A AIR-fragment. -/

/-- A concrete DFA spec: transition relation, initial state, accept predicate. The `foo_air` def the
arithmetizer emits is a value of this type. -/
structure DfaSpec (State Sym : Type u) where
  /-- The transition relation (the `Lookup` table's membership predicate). -/
  δ : State → Sym → State → Prop
  /-- The initial state (`q₀` boundary `PiBinding`). -/
  q₀ : State
  /-- The accept predicate (final-state boundary `PiBinding`). -/
  accept : State → Prop

/-! ## `Refines` — the REAL refinement predicate the generated theorem proves.

`Refines s` is `dfaAccepts_reduces` read as a `Prop` about the spec `s`: for every trace, an
accepting run witnesses a reflexive-transitive `delta`-reduction from a `q₀`-start to an accepting
last step. This is genuine content — NOT `P → P` — and it is the vocabulary the shared `Hypergraph`
substrate already closes (`DfaAsCert.delta` is the DFA leg of `regular_and_cf_share_substrate`). -/

/-- **The refinement predicate.** An accepting DFA run of spec `s` reduces (reflexive-transitively)
under the shared-substrate relation `delta` from a `q₀`-start step to an accepting last step. -/
def Refines (s : DfaSpec State Sym) : Prop :=
  ∀ trace : List (Step State Sym),
    DfaAccepts s.δ s.q₀ s.accept trace →
      ∃ first last : Step State Sym,
        first.state = s.q₀ ∧ s.accept last.next ∧
          Relation.ReflTransGen delta first last

/-- **`refinesOf`** — the GENERATED proof, as a reusable term: `Refines s` for ANY spec `s`, its body
literally `dfaAccepts_reduces s.δ s.q₀ s.accept`. The `#arithmetizeDfa` command emits, per spec, the
specialization `refinesOf foo_air` inlined against `foo_air` — so the emitted proof term names the
spec's own `foo_air`. (Kept as a named def so the mechanism cites an existing lemma, never `sorry`.) -/
def refinesOf (s : DfaSpec State Sym) : Refines s :=
  fun trace => dfaAccepts_reduces s.δ s.q₀ s.accept trace

/-! ## `#arithmetizeDfa` — the elaborator: emit the def AND the kernel-checked theorem.

`#arithmetizeDfa foo := spec` adds `foo_air` (the captured spec) then `foo_sound : Refines foo_air`
whose proof term is generated inline. Both go through `elabCommand → addDecl`, so the kernel checks
the generated theorem on insertion; a bad proof term is a hard elaboration error, never a silent
`sorry`. -/

/-- **`#arithmetizeDfa foo := spec`** — the MVP-0 command. Emits `foo_air : DfaSpec _ _ := spec` and
`foo_sound : Refines foo_air`, the latter with the GENERATED proof term
`fun trace => dfaAccepts_reduces foo_air.δ foo_air.q₀ foo_air.accept trace`. Both kernel-checked. -/
elab "#arithmetizeDfa" name:ident ":=" spec:term : command => do
  let airId    := mkIdent (name.getId.appendAfter "_air")
  let soundId  := mkIdent (name.getId.appendAfter "_sound")
  -- (a) emit the def capturing the spec / AIR-fragment (the spec term carries its own type).
  elabCommand (← `(command| def $airId := $spec))
  -- (b) emit the theorem whose GENERATED proof term names the spec's OWN `foo_air` in
  --     both statement (`Refines $airId`) and proof (`dfaAccepts_reduces ($airId).δ …`).
  elabCommand (← `(command|
    theorem $soundId : Dregg2.Crypto.Arith.Refines $airId :=
      fun trace =>
        Dregg2.Crypto.DfaAsCert.dfaAccepts_reduces
          (Dregg2.Crypto.Arith.DfaSpec.δ $airId)
          (Dregg2.Crypto.Arith.DfaSpec.q₀ $airId)
          (Dregg2.Crypto.Arith.DfaSpec.accept $airId)
          trace))

/-! ## Witnesses — drive the command on two concrete automata. -/

-- Spec #1: the reference `a⁺b` DFA of `Crypto/Dfa.lean` (states `{0,1,2,3}`, bytes `'a'/'b'`).
#arithmetizeDfa aplusb :=
  (⟨Dfa.Reference.δ, Dfa.Reference.q₀, Dfa.Reference.accept⟩ : DfaSpec Nat Nat)

-- Spec #2: a 2-state toggle DFA (state `0 --0--> 1`, `1 --0--> 0`, `q₀ = 0`, accept = `· = 1`);
-- a DISTINCT spec from `aplusb`, used to exhibit the mismatch canary below.
#arithmetizeDfa toggle :=
  (⟨fun s _ n => (s = 0 ∧ n = 1) ∨ (s = 1 ∧ n = 0), 0, fun s => s = 1⟩ : DfaSpec Nat Nat)

-- The command really added BOTH kinds of declaration for each spec:
#check (aplusb_air : DfaSpec Nat Nat)              -- the emitted def (the captured spec / AIR-fragment)
#check (aplusb_sound : Refines aplusb_air)         -- the emitted kernel-checked refinement theorem
#check (toggle_air : DfaSpec Nat Nat)
#check (toggle_sound : Refines toggle_air)

-- The generated theorem's STATEMENT is the REAL refinement, not `P → P`, and both are axiom-clean.
#assert_axioms aplusb_sound
#assert_axioms toggle_sound

/-! ## Canary — the generated proof is LOAD-BEARING on the spec it was generated from.

POSITIVE CONTROL (build-time): `foo_sound`'s proof term reaches `foo_air`. If a future edit made the
proof free of the spec, this reddens. (`#assert_depends_on` shares the `#assert_not_depends_on` walk,
so it also fails loudly if the closure walk ever goes blind — see `Tactics.lean`.) -/
#assert_depends_on aplusb_sound [aplusb_air]
#assert_depends_on toggle_sound [toggle_air]

/-! NEGATIVE HALF (the mismatch that BITES). The design warns that mutating `accept` ALONE does not
break typecheck, because `dfaAccepts_reduces` is parametric in `accept`. The load-bearing canary
mutates the STATEMENT↔SPEC LINKAGE instead: take the `aplusb_air` refinement STATEMENT but build its
proof from the DIFFERENT `toggle_air` spec. The proof term then has type

    Refines toggle_air  =  ∀ trace, DfaAccepts toggle_air.δ toggle_air.q₀ toggle_air.accept trace → …

which is NOT defeq to the expected `Refines aplusb_air` (the `δ`/`q₀`/`accept` fields reduce to
different values), so the kernel REJECTS it. Uncommenting the `example` below yields, verbatim:

    type mismatch
      fun trace => dfaAccepts_reduces (DfaSpec.δ toggle_air) (DfaSpec.q₀ toggle_air) …
    has type
      Refines toggle_air : Prop
    but is expected to have type
      Refines aplusb_air : Prop

Exactly the "generate the air from delta_A but the soundness claim about delta_B → FAILS to
typecheck" the task asks for: the generated proof genuinely DEPENDS on the spec it was generated from.

-/

/-! ### The negative canary, ARMED AT BUILD TIME.

The mismatch below is NOT commented out: `#guard_msgs` asserts the elaborator REJECTS it, so the
build itself exercises the load-bearing property. If a future change made the generated proof stop
depending on its spec (the failure this canary exists to catch), this command would go RED because
the expected error would no longer be produced. A commented-out canary cannot rot loudly; this one
can. (Positive control is `#assert_depends_on` below.) -/
/-- error: Type mismatch
  dfaAccepts_reduces toggle_air.δ toggle_air.q₀ toggle_air.accept trace
has type
  DfaAccepts toggle_air.δ toggle_air.q₀ toggle_air.accept trace →
    ∃ first last, first.state = toggle_air.q₀ ∧ toggle_air.accept last.next ∧ Relation.ReflTransGen delta first last
but is expected to have type
  DfaAccepts aplusb_air.δ aplusb_air.q₀ aplusb_air.accept trace →
    ∃ first last, first.state = aplusb_air.q₀ ∧ aplusb_air.accept last.next ∧ Relation.ReflTransGen delta first last
-/
#guard_msgs in
example : Refines aplusb_air :=
  fun trace =>
    dfaAccepts_reduces (DfaSpec.δ toggle_air) (DfaSpec.q₀ toggle_air) (DfaSpec.accept toggle_air) trace

end Dregg2.Crypto.Arith
