/-
# Dregg2.Calculus.Biorthogonality — dregg guard classes ARE behaviours (transcendental-syntax bridge S1+S2).

THE PROGRAM (`docs/TRANSCENDENTAL-SYNTAX-BRIDGE.md`): derive dregg's guard algebra from the
foundations of logic. Girard's transcendental syntax defines a TYPE as a biorthogonally-closed
BEHAVIOUR — a set `B` with `B = B^⊥⊥` under a testing relation (the stella engine's
`orthogonal_set` / `biorth` / `is_behaviour`, `~/dev/stella/crates/stella-core/src/mll.rs:2070/2088/2104`,
are the reference shapes; everything below is built natively). dregg's guard classes were EMITTED
and CLASSIFIED (`Dregg2/Calculus/DreggCalculus.lean`), never shown orthogonally closed. This module
closes S1+S2 of the bridge for the literal/order guard-atom family, plus the executor-gate weld:

  * **S1 — the orthogonality relation.** A refutation `r` is a fail-closed TEST drawn from the live
    guard-atom catalog; `t ⊥ r` ("`t` survives `r`") is the test's REAL evaluator
    (`Exec.evalConstraintCtx`, `Dregg2/Exec/Program.lean:690` — the same evaluator
    `RecordProgram.admitsCtx` discharges). Decidable. The guard discharge is EXACTLY
    orthogonality-to-the-test-set (`Adm_eq_coOrth`), a refusal pins a concrete counter-witness
    (`refusal_pins_counterwitness` — the fail-closed dual), and the duality needed for the
    double-orthogonal is `orth_duality` (the contravariant Galois connection).
  * **S2 — biorthogonal closure.** `guard_class_is_biorthogonally_closed`: for EVERY guard `g` of
    the family (a finite conjunction of literal/order atoms), `Adm(g) = Adm(g)^⊥⊥` — the admission
    set IS a behaviour. Non-vacuity BOTH polarities: `demo_behaviour_proper` (an inhabited, proper
    behaviour) and `singleton_not_behaviour` (a candidate set whose closure STRICTLY grows —
    `closure_grows`/`closure_witness_new` — so the closure does real work).
  * **THE EXECUTOR WELD.** The same closure at the real fail-closed admission gate: the slot-caveat
    discharge `caveatsAdmit` (`Dregg2/Exec/EffectsState.lean:248`, the gate of `stateStepGuarded:258`)
    IS membership in the orthogonal of the slot's caveat set (`caveatsAdmit_is_orthogonality`,
    definitional), every caveat class is a behaviour (`caveat_class_is_behaviour`), and every
    committed calculus reduction LANDS in a behaviour (`reduces_lands_in_behaviour`, via
    `reduces_admits_guard`). The caveat universe also yields the sharpest false witness:
    `SlotCaveat.eval` FACTORS through actor-only / transition-only projections (`eval_mix`), so
    behaviours there are "rectangular" — a non-rectangular pair-set is NOT closed
    (`pair_not_behaviour`).
  * **S3 (begun).** The ADDITIVE fragment is recovered: behaviours are closed under intersection
    (`coOrth_union` — the `&` of the reconstructed logic), guard conjunction IS the behaviour meet
    (`behaviour_meet`), and ATTENUATION (the affine face) is the antitone action of refutation
    growth (`attenuation_is_refutation_growth`, strictness `attenuation_strict_demo`): adding
    caveats grows the test set and SHRINKS the behaviour — never amplifies. The LINEAR face
    (conservation / `⊗`) is NOT reachable in this per-turn orthogonality: per-asset conservation
    (`reachable_total_zero`) is a relation between PAIRED moves (Σδ = 0 across a composite), i.e.
    a property of a tensor of behaviours over COMPOSITE turns, not a membership predicate of one
    turn against one test. That tensor (stella's `tensor` = `(A^⊥ ∪ B^⊥)^⊥` over composite
    universes) is the named S3 continuation — left open here, honestly.
  * **S4 (gesture only).** Each atom of the family carries its guard MODALITY
    (`LitTest.modality` → `GuardModality.actor`/`.order`), so each behaviour `Adm(g)` carries the
    multiset of modalities of its test set — and `DreggCalculus.modality_price_is_tier` already
    prices a modality by its I-confluence tier. Recasting that price as a GRADING ON BEHAVIOURS
    (the coordination cost as a modality on `^⊥`) is S4, not done here.

HONEST SCOPE: this proves "a dregg guard is a behaviour" for (a) the literal/order atom family of
`Exec/Program.lean` (8 atom shapes, closed under finite conjunction) and (b) the executor's ENTIRE
live slot-caveat gate (all 8 `SlotCaveat` shapes, the gate every committed `gwrite` passes). It
does NOT yet cover the heap/temporal/epistemic atom families (same recipe expected — their
evaluators are decidable Bool tests too), nor S3's linear tensor, nor S5.

No `sorry`, no `:= True`, no `native_decide`; every keystone `#assert_axioms`-pinned.
-/
import Dregg2.Calculus.DreggCalculus
import Dregg2.Exec.Program
import Mathlib.Data.Set.Basic

namespace Dregg2.Calculus.Biorth

open Dregg2.Exec
open Dregg2.Exec.EffectsState

/-! ## §1 — The generic orthogonality core.

A heterogeneous testing relation `perp : T → R → Prop` ("the object `t` SURVIVES the test `r`").
`orthSet S` is `S^⊥` (the tests every member of `S` survives — the refutation set the class
excludes against); `coOrthSet X` is `X^⊥` on the other side (the objects surviving every test in
`X`). `biorth = coOrthSet ∘ orthSet` is the double-orthogonal; a BEHAVIOUR is a fixed point.
These are the Lean-native shapes of stella's `orthogonal_set`/`biorth`/`is_behaviour`
(`stella-core/src/mll.rs:2070/2088/2104`), stated for an arbitrary relation so both
instantiations below (the literal/order family and the executor caveat gate) share one proof of
the closure laws. -/

variable {T R : Type*}

/-- `S^⊥` — the tests (refutations) that EVERY member of `S` survives. -/
def orthSet (perp : T → R → Prop) (S : Set T) : Set R := {r | ∀ t ∈ S, perp t r}

/-- `X^⊥` (other side) — the objects that survive EVERY test in `X`. -/
def coOrthSet (perp : T → R → Prop) (X : Set R) : Set T := {t | ∀ r ∈ X, perp t r}

/-- `S^⊥⊥` — the biorthogonal closure. -/
def biorth (perp : T → R → Prop) (S : Set T) : Set T := coOrthSet perp (orthSet perp S)

/-- A BEHAVIOUR: a set equal to its own double-orthogonal (stella's `is_behaviour`). -/
def IsBehaviour (perp : T → R → Prop) (S : Set T) : Prop := biorth perp S = S

/-- **The duality (S1 sanity: the "symmetry" the double-orth needs).** `orthSet`/`coOrthSet`
form a contravariant Galois connection: `S` survives all of `X` iff `X` is among the tests all
of `S` survives. For a heterogeneous relation this is exactly the symmetry orthogonality
requires. -/
theorem orth_duality (perp : T → R → Prop) (S : Set T) (X : Set R) :
    S ⊆ coOrthSet perp X ↔ X ⊆ orthSet perp S := by
  constructor
  · intro h r hr t ht; exact h ht r hr
  · intro h t ht r hr; exact h hr t ht

/-- `S ⊆ S^⊥⊥` — closure is extensive. -/
theorem subset_biorth (perp : T → R → Prop) (S : Set T) : S ⊆ biorth perp S :=
  (orth_duality perp S (orthSet perp S)).mpr (fun _ hr => hr)

/-- `X ⊆ (X^⊥)^⊥` on the test side. -/
theorem subset_orth_coOrth (perp : T → R → Prop) (X : Set R) :
    X ⊆ orthSet perp (coOrthSet perp X) :=
  (orth_duality perp (coOrthSet perp X) X).mp (fun _ ht => ht)

/-- `orthSet` is antitone (more objects ⇒ fewer common tests). -/
theorem orthSet_antitone (perp : T → R → Prop) {S₁ S₂ : Set T} (h : S₁ ⊆ S₂) :
    orthSet perp S₂ ⊆ orthSet perp S₁ :=
  fun _ hr t ht => hr t (h ht)

/-- `coOrthSet` is antitone (more tests ⇒ fewer survivors). -/
theorem coOrth_antitone (perp : T → R → Prop) {X₁ X₂ : Set R} (h : X₁ ⊆ X₂) :
    coOrthSet perp X₂ ⊆ coOrthSet perp X₁ :=
  fun _ ht r hr => ht r (h hr)

/-- **The triple law** `S^⊥⊥⊥ = S^⊥` (the antitone-Galois collapse): a refutation set is already
closed. With `subset_biorth` this is the whole engine of the closure facts. -/
theorem orthSet_triple (perp : T → R → Prop) (S : Set T) :
    orthSet perp (biorth perp S) = orthSet perp S :=
  Set.Subset.antisymm
    (orthSet_antitone perp (subset_biorth perp S))
    (subset_orth_coOrth perp (orthSet perp S))

/-- **Every orthogonal is a behaviour**: `X^⊥ = (X^⊥)^⊥⊥` for any test set `X`. The kernel fact
behind S2: admission sets are orthogonals, hence behaviours. -/
theorem coOrth_isBehaviour (perp : T → R → Prop) (X : Set R) :
    IsBehaviour perp (coOrthSet perp X) :=
  Set.Subset.antisymm
    (coOrth_antitone perp (subset_orth_coOrth perp X))
    (subset_biorth perp (coOrthSet perp X))

/-- The closure is idempotent: `S^⊥⊥` is always a behaviour. -/
theorem biorth_isBehaviour (perp : T → R → Prop) (S : Set T) :
    IsBehaviour perp (biorth perp S) :=
  coOrth_isBehaviour perp (orthSet perp S)

/-- A set is a behaviour IFF it is the orthogonal of SOME test set — "types are sets of the
form `X^⊥`", the transcendental-syntax definition of a type. -/
theorem isBehaviour_iff_coOrth (perp : T → R → Prop) (S : Set T) :
    IsBehaviour perp S ↔ ∃ X : Set R, S = coOrthSet perp X :=
  ⟨fun h => ⟨orthSet perp S, h.symm⟩, fun ⟨_, hX⟩ => hX ▸ coOrth_isBehaviour perp _⟩

/-- **S3 (additive `&`): behaviours are closed under intersection** — the orthogonal of a UNION
of test sets is the MEET of the orthogonals. The additive conjunction of the reconstructed
fragment, generically. -/
theorem coOrth_union (perp : T → R → Prop) (X Y : Set R) :
    coOrthSet perp (X ∪ Y) = coOrthSet perp X ∩ coOrthSet perp Y := by
  ext t
  simp only [coOrthSet, Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, or_imp, forall_and]

/-! ### The list-guard layer (shared by both instantiations).

A dregg guard of a decidable atom family is a FINITE LIST of tests, discharged conjunctively and
fail-closed by a `Bool` evaluator (`List.all` — exactly the executor's shapes:
`RecordProgram.admitsCtx`'s `cs.all`, `caveatsAdmit`'s `.all`). `listAdm` is its admission set;
the lemmas below are the S1 sanity + S2 closure for ANY such evaluator. -/

section ListGuard

variable (survB : T → R → Bool)

/-- The admission set of a finite conjunctive guard `g` under the evaluator `survB`. -/
def listAdm (g : List R) : Set T := {t | g.all (survB t) = true}

/-- Admission unfolded: survive every test on the list. -/
theorem mem_listAdm_iff (g : List R) (t : T) :
    t ∈ listAdm survB g ↔ ∀ r ∈ g, survB t r = true := by
  simp only [listAdm, Set.mem_setOf_eq, List.all_eq_true]

/-- **S1 sanity (generic): the guard discharge IS orthogonality to the guard's test set.**
`Adm(g) = (tests of g)^⊥`. -/
theorem listAdm_eq_coOrth (g : List R) :
    listAdm survB g = coOrthSet (fun t r => survB t r = true) {r | r ∈ g} :=
  Set.ext fun t => mem_listAdm_iff survB g t

/-- **S2 (generic): every finite conjunctive guard class is a behaviour** — it is an orthogonal
(`listAdm_eq_coOrth`), and orthogonals are behaviours (`coOrth_isBehaviour`). -/
theorem listAdm_isBehaviour (g : List R) :
    IsBehaviour (fun t r => survB t r = true) (listAdm survB g) := by
  rw [listAdm_eq_coOrth]
  exact coOrth_isBehaviour _ _

/-- Guard conjunction is the behaviour MEET (the additive `&` at the list level). -/
theorem listAdm_append (g g' : List R) :
    listAdm survB (g ++ g') = listAdm survB g ∩ listAdm survB g' := by
  ext t
  simp only [mem_listAdm_iff, List.mem_append, Set.mem_inter_iff, or_imp, forall_and]

/-- A larger test list admits LESS (the affine/attenuation direction, generically). -/
theorem listAdm_antitone {g g' : List R} (h : ∀ r ∈ g, r ∈ g') :
    listAdm survB g' ⊆ listAdm survB g := fun t ht =>
  (mem_listAdm_iff survB g t).mpr fun r hr => (mem_listAdm_iff survB g' t).mp ht r (h r hr)

/-- **Fail-closed refusal pins a counter-witness (generic):** a turn is refused IFF some test on
the guard EXCLUDES it — the refutation is constructively exhibitable, never a bare "no". -/
theorem listAdm_refusal (g : List R) (t : T) :
    t ∉ listAdm survB g ↔ ∃ r ∈ g, survB t r = false := by
  rw [mem_listAdm_iff]
  constructor
  · intro h
    by_contra hc
    refine h fun r hr => ?_
    cases hb : survB t r with
    | true  => rfl
    | false => exact absurd ⟨r, hr, hb⟩ hc
  · rintro ⟨r, hr, hf⟩ hall
    exact absurd ((hall r hr).symm.trans hf) (by decide)

end ListGuard

/-! ## §2 — S1 for dregg: the literal/order guard-atom family.

The SIMPLEST live family (`docs/TRANSCENDENTAL-SYNTAX-BRIDGE.md` S2's prescription): the
actor/literal/order atoms of `Dregg2/Exec/Program.lean` — `senderIs`/`senderInField` (the WHO,
`Program.lean:101/105`), `balanceGe`/`balanceLe` (the local-resource literal, `:108/:112`), the
field literals `fieldEquals`/`fieldGe`/`fieldLe` (`:58-:62`), and the order-relational comparator
`fieldLeField` (`StateConstraint.fieldLeField`, `:127`). A TURN, for this family, is exactly what
the family's evaluator reads: the turn context (`TurnCtx` — sender/balance/revealedHash,
`Program.lean:659`) plus the `(old, new)` record pair. A REFUTATION is one atom; `t ⊥ r` is the
atom's REAL evaluator `evalConstraintCtx` (`Program.lean:690`) — the same function
`RecordProgram.admitsCtx` (`:697`) discharges, so the orthogonality is the deployed fail-closed
semantics, not a parallel one. Decidable by construction. -/

/-- A turn, as this atom family observes it: the turn context + the `(old, new)` record pair. -/
structure Turn where
  ctx : TurnCtx
  old : Value
  new : Value

/-- **The refutation space**: one literal/order guard atom = one fail-closed test. Each
constructor DENOTES its live constraint (`LitTest.constraint`); nothing here has its own
semantics. -/
inductive LitTest where
  /-- `senderIs k` — the turn's sender is exactly `k` (`SimpleConstraint.senderIs`). -/
  | senderIs      (k : Int)
  /-- `senderInField f` — the sender equals the identity held in `new[f]`
  (`SimpleConstraint.senderInField`, dregg1 `SenderInSlot`). -/
  | senderInField (f : FieldName)
  /-- `balanceGe v` — the cell's own post-turn balance is `≥ v` (`SimpleConstraint.balanceGe`,
  dregg1 `BalanceGte`). -/
  | balanceGe     (v : Int)
  /-- `balanceLe v` — the balance is `≤ v` (`SimpleConstraint.balanceLe`, dregg1 `BalanceLte`). -/
  | balanceLe     (v : Int)
  /-- `fieldEquals f v` — `new[f] = v` (the literal pin). -/
  | fieldEquals   (f : FieldName) (v : Int)
  /-- `fieldGe f v` — `new[f] ≥ v`. -/
  | fieldGe       (f : FieldName) (v : Int)
  /-- `fieldLe f v` — `new[f] ≤ v`. -/
  | fieldLe       (f : FieldName) (v : Int)
  /-- `fieldLeField l r` — `new[l] ≤ new[r]` (the order-relational comparator,
  `StateConstraint.fieldLeField`, dregg1 `FieldLteField`). -/
  | fieldLeField  (l r : FieldName)
  deriving Repr, DecidableEq

/-- The live constraint each test denotes — the FAITHFULNESS anchor: a `LitTest` is a name for a
deployed `StateConstraint`, evaluated by the deployed evaluator. -/
def LitTest.constraint : LitTest → StateConstraint
  | .senderIs k       => .simple (.senderIs k)
  | .senderInField f  => .simple (.senderInField f)
  | .balanceGe v      => .simple (.balanceGe v)
  | .balanceLe v      => .simple (.balanceLe v)
  | .fieldEquals f v  => .simple (.fieldEquals f v)
  | .fieldGe f v      => .simple (.fieldGe f v)
  | .fieldLe f v      => .simple (.fieldLe f v)
  | .fieldLeField l r => .fieldLeField l r

/-- **The orthogonality evaluator** — `t` survives `r` iff the REAL ctx-aware evaluator admits
the transition (`evalConstraintCtx`, `Program.lean:690`; fail-closed throughout). -/
def survivesB (t : Turn) (r : LitTest) : Bool :=
  evalConstraintCtx t.ctx r.constraint t.old t.new

/-- **S1 — the orthogonality relation `t ⊥ r`**: the turn SURVIVES the fail-closed test. -/
def Survives (t : Turn) (r : LitTest) : Prop := survivesB t r = true

/-- The relation is DECIDABLE (the family is finite-test/decidable, as required). -/
instance (t : Turn) (r : LitTest) : Decidable (Survives t r) :=
  inferInstanceAs (Decidable (survivesB t r = true))

/-- Faithfulness, definitionally: surviving a test IS being admitted by its deployed constraint
under the deployed evaluator. -/
theorem survives_denotes (t : Turn) (r : LitTest) :
    Survives t r ↔ evalConstraintCtx t.ctx r.constraint t.old t.new = true :=
  Iff.rfl

/-! ### Guards = finite conjunctions of atoms; admission; the S1 sanity lemmas. -/

/-- The Bool admission gate of a guard (a finite conjunction of atoms) — `List.all`, exactly the
shape of `RecordProgram.admitsCtx`'s `cs.all` arm (`Program.lean:701`). Fail-closed. -/
def admitsB (g : List LitTest) (t : Turn) : Bool := g.all (survivesB t)

/-- The guard discharge: `g` ADMITS `t`. Decidable. -/
def Admits (g : List LitTest) (t : Turn) : Prop := admitsB g t = true

instance (g : List LitTest) (t : Turn) : Decidable (Admits g t) :=
  inferInstanceAs (Decidable (admitsB g t = true))

/-- `Adm(g)` — the admission set (the candidate behaviour). -/
def Adm (g : List LitTest) : Set Turn := {t | Admits g t}

/-- The guard's test set, as a set of refutations. -/
def testSet (g : List LitTest) : Set LitTest := {r | r ∈ g}

/-- Admission unfolded: survive every atom of the guard. -/
theorem admits_iff (g : List LitTest) (t : Turn) :
    Admits g t ↔ ∀ r ∈ g, Survives t r :=
  mem_listAdm_iff survivesB g t

/-- **The guard weld**: `Admits` IS the deployed program-level admission — a guard `g` is the
`RecordProgram.predicate` over its denoted constraints, discharged by `admitsCtx`
(`Program.lean:697`). The orthogonality below is therefore about the REAL admission gate. -/
theorem admits_is_program_admitsCtx (g : List LitTest) (t : Turn) (method : Nat) :
    Admits g t ↔
      (RecordProgram.predicate (g.map LitTest.constraint)).admitsCtx t.ctx method t.old t.new
        = true := by
  simp only [Admits, admitsB, RecordProgram.admitsCtx, List.all_map, Function.comp_def]
  exact Iff.rfl

/-- **S1 sanity: the guard discharge is EXACTLY orthogonality to the guard's test set** —
`Adm(g) = (testSet g)^⊥`. A turn is admitted iff it survives every refutation the guard fields. -/
theorem Adm_eq_coOrth (g : List LitTest) :
    Adm g = coOrthSet Survives (testSet g) :=
  listAdm_eq_coOrth survivesB g

/-- **S1 sanity (fail-closed dual): a refusal pins a counter-witness.** `t ∉ Adm(g)` iff some
atom of `g` constructively EXCLUDES `t` — the refutation is exhibitable. -/
theorem refusal_pins_counterwitness (g : List LitTest) (t : Turn) :
    t ∉ Adm g ↔ ∃ r ∈ g, survivesB t r = false :=
  listAdm_refusal survivesB g t

/-- Every atom of `g` belongs to `Adm(g)^⊥` (a guard's own tests are among its refutations). -/
theorem self_mem_refutations (g : List LitTest) {r : LitTest} (hr : r ∈ g) :
    r ∈ orthSet Survives (Adm g) := by
  intro t ht
  exact (admits_iff g t).mp ht r hr

/-- **S1 sanity (the spec's phrasing): `g admits t` is EXACTLY `t ⊥ g^⊥`** — admitted iff `t`
survives EVERY refutation in the guard's refutation set `Adm(g)^⊥` (non-orthogonality to nothing
there). Forward = extensivity of closure; backward rides `self_mem_refutations`. -/
theorem admits_iff_survives_all_refutations (g : List LitTest) (t : Turn) :
    Admits g t ↔ ∀ r ∈ orthSet Survives (Adm g), Survives t r := by
  constructor
  · intro h r hr; exact hr t h
  · intro h
    exact (admits_iff g t).mpr fun r hr => h r (self_mem_refutations g hr)

/-! ## §3 — S2: THE THEOREM. The literal/order guard class is biorthogonally closed. -/

/-- **`guard_class_is_biorthogonally_closed` — THE BRIDGE THEOREM (S2, the conjecture of
`docs/TRANSCENDENTAL-SYNTAX-BRIDGE.md`, proved for this family).** For EVERY guard `g` of the
literal/order atom family (any finite conjunction of the 8 atom shapes),
`Adm(g) = Adm(g)^⊥⊥`: the admission set is its own double-orthogonal. A dregg guard of this
family IS a stella behaviour — its class is FORCED by the orthogonality, not assembled. The
proof is the transcendental-syntax mechanism itself: `Adm(g)` is an ORTHOGONAL
(`Adm_eq_coOrth` — admission IS passing the tests) and orthogonals are behaviours
(`coOrth_isBehaviour`, via the triple law). -/
theorem guard_class_is_biorthogonally_closed (g : List LitTest) :
    IsBehaviour Survives (Adm g) :=
  listAdm_isBehaviour survivesB g

/-- The single-atom corollary: each atom's own admission class is a behaviour. -/
theorem atom_class_is_behaviour (r : LitTest) :
    IsBehaviour Survives (Adm [r]) :=
  guard_class_is_biorthogonally_closed [r]

/-! ### Non-vacuity, TRUE polarity: an inhabited, PROPER behaviour.

A real guard (actor pin + resource floor + order comparator), one turn it admits, one it
refuses — the behaviour is neither empty nor everything. -/

/-- A demo guard: sender 7, balance ≥ 10, `new[tail] ≤ new[head]`. -/
def gDemo : List LitTest := [.senderIs 7, .balanceGe 10, .fieldLeField "tail" "head"]

/-- A turn `gDemo` admits. -/
def tIn : Turn :=
  { ctx := { sender := some 7, balance := some 12, revealedHash := none },
    old := .record [],
    new := .record [("tail", .int 1), ("head", .int 3)] }

/-- A turn `gDemo` refuses (wrong sender). -/
def tOut : Turn :=
  { ctx := { sender := some 8, balance := some 12, revealedHash := none },
    old := .record [],
    new := .record [("tail", .int 1), ("head", .int 3)] }

/-- **Non-vacuity (TRUE polarity)**: `Adm(gDemo)` is a behaviour with a member AND a non-member —
a meaningful type, not a degenerate one. -/
theorem demo_behaviour_proper :
    Admits gDemo tIn ∧ ¬ Admits gDemo tOut ∧ IsBehaviour Survives (Adm gDemo) :=
  ⟨by decide, by decide, guard_class_is_biorthogonally_closed gDemo⟩

/-! ### Non-vacuity, FALSE polarity: a candidate set whose closure STRICTLY grows.

The closure is not vacuous: the literal/order family is OLD-STATE-BLIND (none of its 8 atoms
reads `old` — `survives_old_blind`, by cases over the family), so no test set can separate two
turns differing only in `old`. A singleton `{tA}` therefore has `tB ∈ {tA}^⊥⊥ \ {tA}` for the
old-twiddled `tB` — the candidate is NOT a behaviour and the closure does real work. (This is
also an honest finding about the family: its behaviours are blind to the pre-state; the
TRANSITION atoms — `immutable`/`monotonic`/… — live in the caveat gate below, which is exactly
where the executor enforces them.) -/

/-- The family never reads the old state: every atom evaluates identically across `old`. -/
theorem survives_old_blind (c : TurnCtx) (o₁ o₂ n : Value) (r : LitTest) :
    survivesB ⟨c, o₁, n⟩ r = survivesB ⟨c, o₂, n⟩ r := by
  cases r <;> rfl

/-- The false-witness pair: identical context and post-state, different pre-state. -/
def tA : Turn := { ctx := TurnCtx.empty, old := .record [("x", .int 0)], new := .record [] }
/-- See `tA`. -/
def tB : Turn := { ctx := TurnCtx.empty, old := .record [("x", .int 1)], new := .record [] }

theorem tA_ne_tB : tA ≠ tB := by
  intro h
  have h2 : Value.scalar tA.old "x" = Value.scalar tB.old "x" :=
    congrArg (fun t : Turn => Value.scalar t.old "x") h
  exact absurd h2 (by decide)

/-- The closure of `{tA}` captures the NEW element `tB`: every test `tA` survives, `tB` survives
too (old-blindness), so `tB ∈ {tA}^⊥⊥`. -/
theorem closure_witness_new : tB ∈ biorth Survives ({tA} : Set Turn) := by
  intro r hr
  have h1 : Survives tA r := hr tA rfl
  show survivesB tB r = true
  exact (survives_old_blind TurnCtx.empty (.record [("x", .int 1)]) (.record [("x", .int 0)])
    (.record []) r).trans h1

/-- **Non-vacuity (FALSE polarity)**: `{tA}` is NOT a behaviour — its closure strictly grows
(`tB` enters; `tB ≠ tA`). The biorthogonal closure is doing real work; the S2 theorem is not
vacuously true of every set. -/
theorem singleton_not_behaviour : ¬ IsBehaviour Survives ({tA} : Set Turn) := by
  intro h
  have hmem : tB ∈ ({tA} : Set Turn) := h ▸ closure_witness_new
  have heq : tB = tA := hmem
  exact tA_ne_tB heq.symm

/-- The strict growth, packaged: `{tA} ⊆ {tA}^⊥⊥` always, and here the inclusion is PROPER. -/
theorem closure_grows :
    ({tA} : Set Turn) ⊆ biorth Survives {tA}
      ∧ tB ∈ biorth Survives ({tA} : Set Turn) ∧ tB ∉ ({tA} : Set Turn) :=
  ⟨subset_biorth Survives {tA}, closure_witness_new,
   fun hmem => tA_ne_tB (show tB = tA from hmem).symm⟩

/-! ## §4 — THE EXECUTOR WELD: the live fail-closed gate is the same orthogonality.

The calculus's reduction is gated by `caveatsAdmit` (`EffectsState.lean:248` — the slot-caveat
discharge inside `stateStepGuarded:258`; `DreggCalculus.reduces_admits_guard` certifies it on
every committed reduction). That gate is ALREADY a list-guard admission over the `SlotCaveat`
test family (`RecordKernel.lean:87`, evaluator `SlotCaveat.eval:148` — the TRANSITION atoms
`immutable`/`monotonic`/`writeOnce`/… the literal family above cannot see). So the SAME closure
applies to the executor's entire live caveat surface, definitionally. -/
namespace Cav

/-- A turn as the caveat gate observes it: the acting cell + the `(old, new)` scalar transition
on the written slot (`SlotCaveat.eval`'s exact domain). -/
structure CTurn where
  actor : CellId
  old   : Int
  new   : Int
  deriving Repr, DecidableEq

/-- Orthogonality evaluator at the executor gate: the LIVE `SlotCaveat.eval`
(`RecordKernel.lean:148`), verbatim. -/
def survivesB (t : CTurn) (r : SlotCaveat) : Bool := r.eval t.actor t.old t.new

/-- `t ⊥ r` at the executor gate. Decidable. -/
def Survives (t : CTurn) (r : SlotCaveat) : Prop := survivesB t r = true

instance (t : CTurn) (r : SlotCaveat) : Decidable (Survives t r) :=
  inferInstanceAs (Decidable (survivesB t r = true))

/-- The Bool admission gate of a caveat list (the executor's `List.all` shape). -/
def admitsB (g : List SlotCaveat) (t : CTurn) : Bool := g.all (survivesB t)

/-- The caveat-list discharge: `g` ADMITS the transition `t`. Decidable. -/
def Admits (g : List SlotCaveat) (t : CTurn) : Prop := admitsB g t = true

instance (g : List SlotCaveat) (t : CTurn) : Decidable (Admits g t) :=
  inferInstanceAs (Decidable (admitsB g t = true))

/-- The admission set of a caveat list (the slot's installed guard). -/
def Adm (g : List SlotCaveat) : Set CTurn := {t | Admits g t}

/-- **Every slot-caveat class is a behaviour** — the S2 theorem at the executor's own gate, for
ALL 8 live caveat shapes and any finite caveat list a factory installs. -/
theorem caveat_class_is_behaviour (g : List SlotCaveat) :
    IsBehaviour Survives (Adm g) :=
  listAdm_isBehaviour survivesB g

/-- **THE WELD (definitional): `caveatsAdmit` IS orthogonality-set membership.** The executor's
fail-closed slot discharge (`EffectsState.lean:248`) — filter the slot's caveats, `List.all` the
evaluator — is, term for term, membership of the observed transition in the admission set of the
slot's caveat list. `Iff.rfl`: the deployed gate and the orthogonality are THE SAME function. -/
theorem caveatsAdmit_is_orthogonality (k : RecordKernelState) (f : FieldName)
    (actor target : CellId) (n : Int) :
    caveatsAdmit k f actor target n = true ↔
      (⟨actor, fieldOf f (k.cell target), n⟩ : CTurn) ∈
        Adm ((k.slotCaveats target).filter (fun cav => cav.field == f)) :=
  Iff.rfl

/-- **Every committed reduction lands in a behaviour.** A calculus reduction
(`DreggCalculus.Reduces`, = `stateStepGuarded`) certifies its guard held
(`reduces_admits_guard`); by the weld, the observed transition is a MEMBER of the slot's
admission set — which is biorthogonally CLOSED. The runtime's every committed step is membership
in a behaviour, attested (the receipt row of `reduces_is_attested`). -/
theorem reduces_lands_in_behaviour {s s' : RecChainedState} {actor target : Cell}
    {f : FieldName} {n : Int}
    (h : Reduces s (.gwrite actor target f n) s') :
    (⟨actor, fieldOf f (s.kernel.cell target), n⟩ : CTurn) ∈
        Adm ((s.kernel.slotCaveats target).filter (fun cav => cav.field == f))
      ∧ IsBehaviour Survives
          (Adm ((s.kernel.slotCaveats target).filter (fun cav => cav.field == f))) :=
  ⟨(caveatsAdmit_is_orthogonality s.kernel f actor target n).mp (reduces_admits_guard h),
   caveat_class_is_behaviour _⟩

/-! ### Non-vacuity at the executor gate. TRUE: a proper caveat behaviour. FALSE: the caveat
test family FACTORS (every `SlotCaveat` reads the actor ONLY or the transition ONLY —
`eval_mix`), so caveat behaviours are "rectangular" in actor × transition; a non-rectangular
pair-set is NOT closed — its closure adds the mixed corner. -/

/-- TRUE polarity: the `immutable`-slot behaviour admits the identity write and refuses a
rewrite (and is a behaviour by `caveat_class_is_behaviour`). -/
theorem cav_demo_proper :
    Admits [.immutable "owner"] (⟨0, 5, 5⟩ : CTurn)
      ∧ ¬ Admits [.immutable "owner"] (⟨0, 5, 6⟩ : CTurn) :=
  ⟨by decide, by decide⟩

/-- **The factorization (mix) lemma**: every live caveat shape reads the actor ONLY
(`senderAuthorized`/`clearanceGe`) or the `(old,new)` transition ONLY (the other six) — so two
survivors may always be MIXED: take the first's actor with the second's transition. By cases
over all 8 shapes, each side definitional. -/
theorem eval_mix {r : SlotCaveat} {a₁ a₂ : CellId} {o₁ n₁ o₂ n₂ : Int}
    (h₁ : r.eval a₁ o₁ n₁ = true) (h₂ : r.eval a₂ o₂ n₂ = true) :
    r.eval a₁ o₂ n₂ = true := by
  cases r <;> first | exact h₂ | exact h₁

/-- The non-rectangular candidate: two unrelated admitted transitions… -/
def c₁ : CTurn := ⟨0, 0, 1⟩
/-- …by two different actors… -/
def c₂ : CTurn := ⟨1, 5, 6⟩
/-- …and the MIXED corner (actor of `c₁`, transition of `c₂`) the closure must add. -/
def cMix : CTurn := ⟨0, 5, 6⟩

/-- The candidate pair-set `{c₁, c₂}`. -/
def pairSet : Set CTurn := {t | t = c₁ ∨ t = c₂}

/-- Every test both `c₁` and `c₂` survive, the mixed corner survives (`eval_mix`):
`cMix ∈ {c₁,c₂}^⊥⊥`. -/
theorem mix_in_closure : cMix ∈ biorth Survives pairSet := by
  intro r hr
  have h1 : Survives c₁ r := hr c₁ (Or.inl rfl)
  have h2 : Survives c₂ r := hr c₂ (Or.inr rfl)
  exact eval_mix h1 h2

theorem mix_not_in_pair : cMix ∉ pairSet := by
  intro h
  have h' : cMix = c₁ ∨ cMix = c₂ := h
  rcases h' with h | h
  · exact absurd (congrArg CTurn.old h) (by decide)
  · exact absurd (congrArg CTurn.actor h) (by decide)

/-- **Non-vacuity (FALSE polarity) at the executor gate**: `{c₁, c₂}` is NOT a behaviour — the
closure adds the mixed corner. The caveat gate's behaviours are exactly as expressive as its
test family (actor-rectangles × transition-sets), no more: the closure detects what the family
cannot carve. -/
theorem pair_not_behaviour : ¬ IsBehaviour Survives pairSet := by
  intro h
  exact mix_not_in_pair (h ▸ mix_in_closure)

end Cav

/-! ## §5 — S3 (begun): the substructural face of the behaviour structure.

What IS recovered here, for this family:

  * **The additive `&`**: behaviours are closed under meet (`coOrth_union` generically;
    `behaviour_meet`/`meet_is_behaviour` for guards) — guard conjunction is the additive
    conjunction of the reconstructed fragment.
  * **The AFFINE face — attenuation is the antitone action of refutation growth.** Attaching
    caveats to a capability (`attenuate keep`, the proven non-amplification discipline —
    `DreggCalculus.attenuation_is_scope_restriction`) GROWS the test set; by antitonicity the
    behaviour can only SHRINK (`attenuation_is_refutation_growth`, strict on a witness:
    `attenuation_strict_demo`). "Authority weakens or discards, never amplifies" is, on the
    behaviour side, exactly `coOrth_antitone`. This is the affine discipline AS a property of
    the orthogonality — the S3 direction, landed for this family.

What is NOT recovered here (the named obstruction): the LINEAR face. Per-asset conservation
(`reachable_total_zero`; the `move` verb, separated from `gwrite` by
`VerbCompression.gwrite_conservation_trivializes`) is a constraint on PAIRED writes — `Σδ = 0`
across a composite — and is therefore not a membership predicate of ONE turn against ONE test in
this per-turn orthogonality. Reaching it requires the TENSOR of behaviours over composite turns
(stella's `tensor = (A^⊥ ∪ B^⊥)^⊥` over a composite universe; `mll.rs:2137`). That construction
(turn pairs as objects, paired tests, conservation as a behaviour of the tensor) is the honest
S3 continuation; nothing about this family blocks it, but it is real new structure, not a
corollary — left open. -/

/-- Guard conjunction IS the behaviour meet. -/
theorem behaviour_meet (g g' : List LitTest) :
    Adm (g ++ g') = Adm g ∩ Adm g' :=
  listAdm_append survivesB g g'

/-- The meet of two guard behaviours is a behaviour (the additive `&`, on dregg guards). -/
theorem meet_is_behaviour (g g' : List LitTest) :
    IsBehaviour Survives (Adm g ∩ Adm g') :=
  behaviour_meet g g' ▸ guard_class_is_biorthogonally_closed (g ++ g')

/-- **Attenuation = refutation growth (the affine face).** Adding caveats to a guard can only
SHRINK its behaviour — the non-amplification discipline as antitonicity of the orthogonality. -/
theorem attenuation_is_refutation_growth (g extra : List LitTest) :
    Adm (g ++ extra) ⊆ Adm g := by
  rw [behaviour_meet]
  exact Set.inter_subset_left

/-- Attenuation generally: a guard with MORE tests admits LESS. -/
theorem Adm_antitone {g g' : List LitTest} (h : ∀ r ∈ g, r ∈ g') :
    Adm g' ⊆ Adm g :=
  listAdm_antitone survivesB h

/-- Attenuation is STRICT on a witness: `tIn` passes the bare actor pin but not the
balance-attenuated guard — the caveat really cuts. -/
theorem attenuation_strict_demo :
    Admits [LitTest.senderIs 7] tIn
      ∧ ¬ Admits ([LitTest.senderIs 7] ++ [LitTest.balanceGe 100]) tIn :=
  ⟨by decide, by decide⟩

/-! ## §6 — S4 (gesture only): the modality grading on behaviours.

Each atom of the family carries its guard modality in the calculus's index
(`DreggCalculus.GuardModality`): the sender/balance/field-literal atoms are the ACTOR/literal
family (`GuardModality.actor`, whose atom module IS `Exec.Program`'s `SimpleConstraint`), and
the `fieldLeField` comparator is the order-relational shape (`GuardModality.order`'s `≤`-gate
form). So every behaviour `Adm(g)` of this family carries the modalities of its test set, and
`DreggCalculus.modality_price_is_tier` already prices a modality by its I-confluence tier. S4
proper — recasting that price as a grading on `^⊥` (coordination cost as a modality on the
orthogonality) — is NOT done here; this def only fixes the index the grading would act on. -/

/-- The calculus modality of each atom (the index `modality_price` grades). -/
def LitTest.modality : LitTest → GuardModality
  | .senderIs _ | .senderInField _ | .balanceGe _ | .balanceLe _ => .actor
  | .fieldEquals _ _ | .fieldGe _ _ | .fieldLe _ _               => .actor
  | .fieldLeField _ _                                            => .order

/-- The family spans exactly the actor and order modalities. -/
theorem modality_span (r : LitTest) :
    r.modality = GuardModality.actor ∨ r.modality = GuardModality.order := by
  cases r <;> simp [LitTest.modality]

/-! ## §7 — Computational spot-checks (the relation is meaningful, both ways). -/

-- the orthogonality relation distinguishes turns:
#guard survivesB tIn (.senderIs 7)
#guard !(survivesB tOut (.senderIs 7))
#guard survivesB tIn (.fieldLeField "tail" "head")
#guard !(survivesB tIn (.fieldLeField "head" "tail"))
-- admission gates compute, both polarities:
#guard admitsB gDemo tIn
#guard !(admitsB gDemo tOut)
-- the executor-gate evaluator, both polarities:
#guard Cav.survivesB ⟨0, 5, 5⟩ (.immutable "owner")
#guard !(Cav.survivesB ⟨0, 5, 6⟩ (.immutable "owner"))
-- the mixed corner really is admitted by the tests the pair shares (e.g. monotonic):
#guard Cav.survivesB Biorth.Cav.cMix (.monotonic "x")

/-! ## §8 — Axiom hygiene. -/

-- §1 the generic core
#assert_axioms orth_duality
#assert_axioms subset_biorth
#assert_axioms orthSet_triple
#assert_axioms coOrth_isBehaviour
#assert_axioms biorth_isBehaviour
#assert_axioms isBehaviour_iff_coOrth
#assert_axioms coOrth_union
#assert_axioms listAdm_isBehaviour
#assert_axioms listAdm_refusal
-- §2 S1: the relation + sanity
#assert_axioms survives_denotes
#assert_axioms admits_is_program_admitsCtx
#assert_axioms Adm_eq_coOrth
#assert_axioms refusal_pins_counterwitness
#assert_axioms admits_iff_survives_all_refutations
-- §3 S2: THE THEOREM + non-vacuity both polarities
#assert_axioms guard_class_is_biorthogonally_closed
#assert_axioms atom_class_is_behaviour
#assert_axioms demo_behaviour_proper
#assert_axioms survives_old_blind
#assert_axioms singleton_not_behaviour
#assert_axioms closure_grows
-- §4 the executor weld + its non-vacuity
#assert_axioms Cav.caveat_class_is_behaviour
#assert_axioms Cav.caveatsAdmit_is_orthogonality
#assert_axioms Cav.reduces_lands_in_behaviour
#assert_axioms Cav.cav_demo_proper
#assert_axioms Cav.eval_mix
#assert_axioms Cav.pair_not_behaviour
-- §5 S3: the additive + affine faces
#assert_axioms behaviour_meet
#assert_axioms meet_is_behaviour
#assert_axioms attenuation_is_refutation_growth
#assert_axioms Adm_antitone
#assert_axioms attenuation_strict_demo
-- §6 the modality index
#assert_axioms modality_span

end Dregg2.Calculus.Biorth
