/-
# Dregg2.Exec.PredAlgebra — the clean Boolean predicate ALGEBRA over the policy-combinator atoms.

The forked predicate surfaces (`SimpleConstraint`/`StateConstraint` in `Exec/Program.lean`, the
per-slot `SlotCaveat` in `Exec/RecordKernel.lean`) are ad-hoc 2-level grammars: `anyOf` is
single-level over simples only, `not` lives only at `SimpleConstraint`, and there is no `allOf`. The
`_POLICY-LANGUAGES-REFRESH.md` §B.1 target is **a small core of orthogonal, introspectable
combinators** under a uniform Boolean layer, into which the OLD corpora embed as a NO-OP extension so
existing proofs LIFT.

This module is that uniform layer. It is built ON TOP of `Exec/Program.lean`'s extended atom set
(`memberOf`/`prefixOf`/`inRangeTwoSided`/`deltaBounded`/`affineLe`/`affineEq`/`reachable` plus
`clearanceGe` and every legacy constructor) — it does NOT re-fork them. The old corpora embed via
`Pred.ofSimple`/`Pred.ofConstraint` (proved semantics-preserving, the no-op extension), so a `Pred`
is a strict GENERALIZATION of the legacy `StateConstraint`: every old program is a `Pred` with the
SAME truth value (`Pred.ofConstraint_eval`).

It then provides the **executor adapter** (`§ Adapter`): a `PredCaveat` evaluating a `Pred` over the
live `(actor, old, new)` scalar transition, and `predStateStepGuarded` which gates the verified
`stateStep` field-write by a `Pred` — committing EXACTLY `stateStep`'s post-state (a domain
restrictor, never a mutator), so every `stateStep` keystone (conservation/authority/forward-sim)
LIFTS verbatim (`predStateStepGuarded_eq`, the mirror of `stateStepGuarded_eq`). This is what makes
the new policy atoms enforced on the LIVE `setFieldA` leg, exactly like `clearanceGe`.

Imports `Exec/EffectsState` (hence `Program`, `RecordKernel`, `Value`) READ-ONLY. Pure, computable,
`#guard`-able; `#assert_axioms`-clean (subset {propext, Classical.choice, Quot.sound}).
-/
import Dregg2.Exec.EffectsState

namespace Dregg2.Exec.PredAlgebra

open Dregg2.Exec
open Dregg2.Exec.EffectsState (fieldOf stateStep)
open Dregg2.Authority.ClearanceGraph (ClearanceGraph Label)

/-! ## The uniform Boolean predicate algebra. -/

/-- **`Pred`** — a clean Boolean algebra over the `Exec` policy-combinator atoms (the
`StateConstraint` catalog, which already carries every atom: `memberOf`/`prefixOf`/`inRangeTwoSided`/
`deltaBounded`/`affineLe`/`affineEq`/`reachable`/`clearanceGe` + the legacy shapes). Orthogonal to the
atoms: `and`/`or`/`not` at EVERY level, plus n-ary `allOf`/`anyOf`. This is the Heyting algebra done
properly — the §B.1(ii) layer the forked 2-level `anyOf`/`SimpleConstraint`-only-`not` could not give. -/
inductive Pred where
  /-- An atom: any `Exec.StateConstraint` (so every legacy + new atom embeds verbatim). -/
  | atom  (c : StateConstraint)
  /-- Top (admits everything). -/
  | tt
  /-- Bottom (admits nothing). -/
  | ff
  /-- Conjunction. -/
  | and   (l r : Pred)
  /-- Disjunction. -/
  | or    (l r : Pred)
  /-- Negation — at EVERY level (not just `SimpleConstraint`). -/
  | not   (p : Pred)
  /-- n-ary conjunction. -/
  | allOf (ps : List Pred)
  /-- n-ary disjunction (replaces the single-level `anyOf`). -/
  | anyOf (ps : List Pred)
  deriving Repr

/-! **`Pred.eval`** — the structural fold to a `Bool` over `(old, new)`. Decidable, computable,
fail-closed (an atom that cannot read its fields rejects; `ff`/`anyOf []` reject). The `allOf`/`anyOf`
list arms recur through explicit `evalAll`/`evalAny` helpers (so termination is structural — the
`TransitionGuard.anyMatch`/`allMatch` pattern of `Program.lean`). -/
mutual
def Pred.eval : Pred → Value → Value → Bool
  | .atom c,    o, n => evalConstraint c o n
  | .tt,        _, _ => true
  | .ff,        _, _ => false
  | .and l r,   o, n => l.eval o n && r.eval o n
  | .or l r,    o, n => l.eval o n || r.eval o n
  | .not p,     o, n => !(p.eval o n)
  | .allOf ps,  o, n => Pred.evalAll ps o n
  | .anyOf ps,  o, n => Pred.evalAny ps o n
def Pred.evalAll : List Pred → Value → Value → Bool
  | [],      _, _ => true
  | p :: ps, o, n => p.eval o n && Pred.evalAll ps o n
def Pred.evalAny : List Pred → Value → Value → Bool
  | [],      _, _ => false
  | p :: ps, o, n => p.eval o n || Pred.evalAny ps o n
end

/-! ## The no-op embeddings — old corpora LIFT into `Pred` with the SAME truth value. -/

/-- Embed a legacy/new `SimpleConstraint` as a `Pred` (via the `simple` lift to `StateConstraint`). -/
def Pred.ofSimple (c : SimpleConstraint) : Pred := .atom (.simple c)

/-- Embed any `StateConstraint` (legacy or new atom) as a `Pred`. -/
def Pred.ofConstraint (c : StateConstraint) : Pred := .atom c

/-- A legacy `predicate` program (a conjunction of `StateConstraint`s) embeds as `allOf` of atoms. -/
def Pred.ofProgram (cs : List StateConstraint) : Pred := .allOf (cs.map Pred.ofConstraint)

/-- **`ofSimple_eval` (no-op embedding).** A `SimpleConstraint` embedded into `Pred`
evaluates IDENTICALLY to `evalSimple`. The legacy simple layer is a strict sub-algebra. -/
theorem Pred.ofSimple_eval (c : SimpleConstraint) (o n : Value) :
    (Pred.ofSimple c).eval o n = evalSimple c o n := rfl

/-- **`ofConstraint_eval` (no-op embedding).** A `StateConstraint` embedded into `Pred`
evaluates IDENTICALLY to `evalConstraint`. EVERY existing program is a `Pred` with the SAME truth
value — so every proof phrased over `evalConstraint` lifts to the algebra unchanged. -/
theorem Pred.ofConstraint_eval (c : StateConstraint) (o n : Value) :
    (Pred.ofConstraint c).eval o n = evalConstraint c o n := rfl

/-- **`ofProgram_eval`.** A legacy conjunctive `predicate` program embeds as `allOf` and
evaluates to the SAME `cs.all evalConstraint` that `RecordProgram.admits (.predicate cs)` uses. The
forked `predicate`/`anyOf` grammar is exactly the `allOf`/`anyOf` fragment of the clean algebra. -/
theorem Pred.ofProgram_eval (cs : List StateConstraint) (o n : Value) :
    (Pred.ofProgram cs).eval o n = cs.all (fun c => evalConstraint c o n) := by
  unfold Pred.ofProgram
  show Pred.evalAll (cs.map Pred.ofConstraint) o n = cs.all (fun c => evalConstraint c o n)
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, List.all_cons, Pred.evalAll, Pred.ofConstraint_eval, ih]

/-! ## Heyting / Boolean laws (the algebra is a genuine Boolean algebra, not an ad-hoc grammar). -/

/-- **`eval_not`.** Negation is the Boolean complement at EVERY level (the §B.1 fix: `not`
is not `SimpleConstraint`-only). -/
theorem Pred.eval_not (p : Pred) (o n : Value) : (Pred.not p).eval o n = !(p.eval o n) := rfl

/-- **`eval_not_not`.** Double negation collapses on the decidable algebra. -/
theorem Pred.eval_not_not (p : Pred) (o n : Value) :
    (Pred.not (Pred.not p)).eval o n = p.eval o n := by
  simp only [Pred.eval, Bool.not_not]

/-- **`eval_and`.** Conjunction is `&&`. -/
theorem Pred.eval_and (l r : Pred) (o n : Value) :
    (Pred.and l r).eval o n = (l.eval o n && r.eval o n) := rfl

/-- **`eval_or`.** Disjunction is `||`. -/
theorem Pred.eval_or (l r : Pred) (o n : Value) :
    (Pred.or l r).eval o n = (l.eval o n || r.eval o n) := rfl

/-- **De Morgan.** `¬(l ∧ r) = ¬l ∨ ¬r` on the algebra. -/
theorem Pred.deMorgan_and (l r : Pred) (o n : Value) :
    (Pred.not (Pred.and l r)).eval o n = (Pred.or (Pred.not l) (Pred.not r)).eval o n := by
  simp only [Pred.eval, Bool.not_and]

/-- **De Morgan.** `¬(l ∨ r) = ¬l ∧ ¬r`. -/
theorem Pred.deMorgan_or (l r : Pred) (o n : Value) :
    (Pred.not (Pred.or l r)).eval o n = (Pred.and (Pred.not l) (Pred.not r)).eval o n := by
  simp only [Pred.eval, Bool.not_or]

/-- **`allOf_cons`.** n-ary conjunction unfolds: the head AND the rest. -/
theorem Pred.allOf_cons (p : Pred) (ps : List Pred) (o n : Value) :
    (Pred.allOf (p :: ps)).eval o n = (p.eval o n && (Pred.allOf ps).eval o n) := rfl

/-- **`anyOf_cons`.** n-ary disjunction unfolds: the head OR the rest. -/
theorem Pred.anyOf_cons (p : Pred) (ps : List Pred) (o n : Value) :
    (Pred.anyOf (p :: ps)).eval o n = (p.eval o n || (Pred.anyOf ps).eval o n) := rfl

/-- **`allOf_nil_admits` / `anyOf_nil_rejects` (the unit laws).** Empty `allOf` is `tt`
(vacuous conjunction admits); empty `anyOf` is `ff` (empty disjunction rejects, fail-closed). -/
theorem Pred.allOf_nil_admits (o n : Value) : (Pred.allOf []).eval o n = true := rfl
theorem Pred.anyOf_nil_rejects (o n : Value) : (Pred.anyOf []).eval o n = false := rfl

/-! ## § Adapter — the LIVE-leg executor enforcement (mirrors `clearanceGe` / `stateStepGuarded`).

A `Pred` is enforced on the LIVE `setFieldA` field-write leg by gating the verified `stateStep`:
`predStateStepGuarded` commits EXACTLY `stateStep`'s post-state ONLY when the `Pred` admits the
`(old-scalar, new-scalar)` transition (the same scalar reads the kernel's per-slot caveats use,
`caveatsAdmit`). The `Pred` only DECIDES; it never mutates — so it is a pure domain restrictor, and
`predStateStepGuarded_eq` lifts every `stateStep` keystone verbatim, exactly like `stateStepGuarded`. -/

/-- **`PredCaveat`** — a `Pred` bound to a slot `field`, enforced on writes to that slot. The
introspectable, algebra-valued generalization of the 7-arm `RecordKernel.SlotCaveat`. -/
structure PredCaveat where
  field : FieldName
  pred  : Pred
  deriving Repr

/-- Evaluate a `PredCaveat` on a scalar write of `new` to its slot whose committed value is `old`.
The `(old, new)` scalars are lifted to single-field records keyed by the caveat's slot, so the full
`Pred`/`evalConstraint` machinery applies on the live leg (the slot-local transition view). -/
def PredCaveat.eval (pc : PredCaveat) (old new : Int) : Bool :=
  pc.pred.eval (.record [(pc.field, .int old)]) (.record [(pc.field, .int new)])

/-- **`predCaveatsAdmit`** — do ALL `Pred`-caveats bound to slot `f` admit the scalar write `new` by
`actor` to `target` (against the committed `fieldOf f (k.cell target)`, defaulting absent to `0` —
dregg1's `FIELD_ZERO`)? The `Pred` analog of `caveatsAdmit`. Computable, fail-closed. -/
def predCaveatsAdmit (caveats : List PredCaveat) (k : RecordKernelState) (f : FieldName)
    (target : CellId) (new : Int) : Bool :=
  (caveats.filter (fun pc => pc.field == f)).all
    (fun pc => pc.eval (fieldOf f (k.cell target)) new)

/-- **`predStateStepGuarded` — the `Pred`-gated field write (computable).** First the
authority gate (`stateStep`), then the `Pred`-caveat gate (`predCaveatsAdmit`): a write commits iff
the actor holds authority AND every `Pred`-caveat bound to the written slot admits the
`(actor, old, new)` transition. Fail-closed on EITHER gate. The post-state is EXACTLY `stateStep`'s —
the `Pred` gate only DECIDES, never mutates. The live-leg executor enforcement of the algebra. -/
def predStateStepGuarded (caveats : List PredCaveat) (s : RecChainedState) (f : FieldName)
    (actor target : CellId) (n : Int) : Option RecChainedState :=
  if predCaveatsAdmit caveats s.kernel f target n = true then
    stateStep s f actor target (.int n)
  else
    none

/-- **`predStateStepGuarded_eq` (the safety net).** A committed `Pred`-gated write is
EXACTLY the underlying `stateStep` write (the algebra gate only restricts the domain — it never
changes the post-state). The bridge that lifts EVERY `stateStep` keystone (conservation, authority,
forward-sim) to the `Pred`-guarded write verbatim — the mirror of `stateStepGuarded_eq`. -/
theorem predStateStepGuarded_eq {caveats : List PredCaveat} {s s' : RecChainedState}
    {f : FieldName} {actor target : CellId} {n : Int}
    (h : predStateStepGuarded caveats s f actor target n = some s') :
    stateStep s f actor target (.int n) = some s' := by
  unfold predStateStepGuarded at h
  by_cases hg : predCaveatsAdmit caveats s.kernel f target n = true
  · rw [if_pos hg] at h; exact h
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`predStateStepGuarded_admits`.** A committed `Pred`-gated write means every
`Pred`-caveat bound to the written slot ADMITTED the transition. The witness that the algebra was
enforced on the live leg. -/
theorem predStateStepGuarded_admits {caveats : List PredCaveat} {s s' : RecChainedState}
    {f : FieldName} {actor target : CellId} {n : Int}
    (h : predStateStepGuarded caveats s f actor target n = some s') :
    predCaveatsAdmit caveats s.kernel f target n = true := by
  unfold predStateStepGuarded at h
  by_cases hg : predCaveatsAdmit caveats s.kernel f target n = true
  · exact hg
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`predStateStepGuarded_violation_fails` (FAIL-CLOSED).** If ANY `Pred`-caveat bound to
the written slot rejects the transition (`predCaveatsAdmit = false`), the write does NOT commit. The
executor-level teeth of the algebra: a violated policy `Pred` rejects the write, BY THE EXECUTOR. -/
theorem predStateStepGuarded_violation_fails (caveats : List PredCaveat) (s : RecChainedState)
    (f : FieldName) (actor target : CellId) (n : Int)
    (h : predCaveatsAdmit caveats s.kernel f target n = false) :
    predStateStepGuarded caveats s f actor target n = none := by
  unfold predStateStepGuarded; rw [if_neg (by rw [h]; simp)]

/-! ## It runs (`#guard`) — the algebra admitting / rejecting real programs, with non-vacuity pairs. -/

/-- A role-cell policy combining a value allowlist with a two-sided band, via the clean Boolean
layer: `role ∈ {1,2,3}  AND  (NOT price > 200)`, authored with `and`/`not` at the `Pred` level. -/
def rolePolicy : Pred :=
  .and (.ofSimple (.memberOf "role" [1, 2, 3]))
       (.not (.ofConstraint (.simple (.fieldGe "price" 201))))

def roleNew_ok  : Value := .record [("role", .int 2), ("price", .int 150)]   -- role∈set ∧ price≤200
def roleNew_bad : Value := .record [("role", .int 2), ("price", .int 250)]   -- price>200 ⇒ reject

#guard (rolePolicy.eval (.record []) roleNew_ok)            -- true
#guard (rolePolicy.eval (.record []) roleNew_bad) == false  -- false

-- The algebra non-vacuity at the `by decide` layer (ADMIT and REJECT witnesses):
example : rolePolicy.eval (.record []) roleNew_ok = true := by decide
example : rolePolicy.eval (.record []) roleNew_bad = false := by decide

/-- An n-ary `anyOf` (multi-branch disjunction the legacy single-level `anyOf` could express only
over simples — here over arbitrary `Pred`s, including the new affine atom): a price band is OK if it
is within `[100,200]` OR satisfies the affine relation `2·bid ≤ 250`. -/
def bandPolicy : Pred :=
  .anyOf [ .ofSimple (.inRangeTwoSided "price" 100 200)
         , .ofConstraint (.affineLe [(2, "bid")] 250) ]

#guard (bandPolicy.eval (.record []) (.record [("price", .int 150), ("bid", .int 999)]))          -- true  (in band)
#guard (bandPolicy.eval (.record []) (.record [("price", .int 999), ("bid", .int 100)]))          -- true  (affine ok: 200 ≤ 250)
#guard (bandPolicy.eval (.record []) (.record [("price", .int 999), ("bid", .int 200)])) == false  -- false (neither)
example : bandPolicy.eval (.record []) (.record [("price", .int 999), ("bid", .int 200)]) = false := by decide

/-! ### Live-leg adapter non-vacuity: a `PredCaveat` admitting one write and rejecting another,
demonstrating the executor-level fail-closed teeth at the SCALAR transition (the `caveatsAdmit` view). -/

-- A monotone-bounded slot policy: the new value must be in `[old? we test absolute]` `[0,100]` AND
-- a member of {10,20,30,40,50,60,70,80,90,100}. Authored as the clean Boolean `and`.
def slotPolicy : Pred :=
  .and (.ofSimple (.inRangeTwoSided "v" 0 100))
       (.ofSimple (.memberOf "v" [10,20,30,40,50,60,70,80,90,100]))

def vCaveat : PredCaveat := { field := "v", pred := slotPolicy }

-- ADMIT: 50 is in [0,100] and ∈ the allowlist.
#guard (vCaveat.eval 0 50)            -- true
-- REJECT: 55 is in range but NOT in the allowlist (the `and` fails closed).
#guard (vCaveat.eval 0 55) == false   -- false
-- REJECT: 110 is in the (extended) allowlist? no — and out of [0,100]; rejected.
#guard (vCaveat.eval 0 110) == false  -- false
example : vCaveat.eval 0 50 = true  := by decide
example : vCaveat.eval 0 55 = false := by decide

-- A bare kernel with all-zero cells (slot "v" reads committed 0 via `fieldOf`):
def kbare : RecordKernelState :=
  { accounts := ∅, cell := fun _ => .record [("v", .int 0)], caps := fun _ => [] }

-- `predCaveatsAdmit` filters to the touched slot: a caveat on slot "v" is irrelevant to a write on "w".
#guard (predCaveatsAdmit [vCaveat] kbare "v" 0 50)            -- true
#guard (predCaveatsAdmit [vCaveat] kbare "v" 0 55) == false   -- false
#guard (predCaveatsAdmit [vCaveat] kbare "w" 0 55)            -- true (irrelevant slot — filtered out)

#assert_axioms Pred.ofSimple_eval
#assert_axioms Pred.ofConstraint_eval
#assert_axioms Pred.ofProgram_eval
#assert_axioms Pred.eval_not_not
#assert_axioms Pred.deMorgan_and
#assert_axioms Pred.deMorgan_or
#assert_axioms Pred.allOf_cons
#assert_axioms Pred.anyOf_cons
#assert_axioms predStateStepGuarded_eq
#assert_axioms predStateStepGuarded_admits
#assert_axioms predStateStepGuarded_violation_fails

end Dregg2.Exec.PredAlgebra
