/-
# Dregg2.Exec.Program — the RecordProgram as the coalgebra structure-map (over records).

`RecordProgram` is the coalgebra structure-map — the `AdmissibleTurn ⇒ Cell` arrow.
Faithfully transcribed from dregg1's ~21-variant `StateConstraint` catalog
(`cell/src/program.rs`), but **name-keyed** over the Preserves `Value`/`Schema` of
`Exec/Value.lean`, not bit-positioned over 8 fixed slots.

`RecordProgram.admits` is the admissibility filter: the *domain* of the structure-map. It is
decidable and computable. Every constraint reads specific named fields (`Value.scalar`), so
under `flatten` each constraint is a Boolean function of a known set of wires — exactly what
the circuit compiler (`RecordCircuit`) places onto `fieldOffset` columns.

The Heyting fragment (`anyOf` ⊔ / `not` ¬) realizes `Laws.predicate_heyting` (`dregg2 §1.5`).
Witnessed/sender/cross-cell (`boundDelta`) constraints are *declared* here and routed to their
seam downstream, exactly as dregg1's scalar evaluator defers `BoundDelta`/`Witnessed`.

Pure, computable, `#eval`-able; imports `Exec.Value` and the (already-proved) orphaned
`Authority.ClearanceGraph` lattice primitive so the predicate language can express SGM-style
clearance mandates inline (`clearanceGe`, wired to `dominatesD`).
-/
import Dregg2.Exec.Value
import Dregg2.Authority.ClearanceGraph

namespace Dregg2.Exec

open Dregg2.Authority.ClearanceGraph (ClearanceGraph Label dominatesD)

/-! ## Field access into a record `Value`. -/

/-- Look up a named field's value in a record (`none` if not a record / field absent). -/
def Value.field : Value → FieldName → Option Value
  | .record fs, f => (fs.find? (fun p => p.1 == f)).map (·.2)
  | _,          _ => none

/-- Read a named field as a scalar `Int` (`none` if absent or not an `int`). Constraints that
need a missing/ill-typed field **fail closed** (the `none` propagates to `false`). -/
def Value.scalar (v : Value) (f : FieldName) : Option Int :=
  match v.field f with
  | some (.int i) => some i
  | _             => none

/-- Sum the scalar values of named fields; `none` if any is absent/ill-typed (fail-closed). -/
def sumScalars (v : Value) (fields : List FieldName) : Option Int :=
  fields.foldr
    (fun f acc => match acc, v.scalar f with
                  | some s, some x => some (s + x)
                  | _,      _      => none)
    (some 0)

/-! ## The constraint catalog (name-keyed; the structural subset of dregg1's 21). -/

/-- **Simple (non-witnessed, non-recursive-except-`not`) constraints** — the fragment
admissible inside `anyOf` and under `not` (mirrors dregg1's `SimpleStateConstraint`, the
Heyting-liftable subset). -/
inductive SimpleConstraint where
  /-- `new[field] = value`. -/
  | fieldEquals (field : FieldName) (value : Int)
  /-- `new[field] ≥ value`. -/
  | fieldGe     (field : FieldName) (value : Int)
  /-- `new[field] ≤ value`. -/
  | fieldLe     (field : FieldName) (value : Int)
  /-- `new[field] = old[field]` (read-only after init; absent-old ⇒ first write allowed). -/
  | immutable   (field : FieldName)
  /-- `old[field] = 0/absent ⇒ any; else new[field] = old[field]` (register-once). -/
  | writeOnce   (field : FieldName)
  /-- `new[field] ≥ old[field]` (append-only / monotone counter). -/
  | monotonic   (field : FieldName)
  /-- `new[field] > old[field]` (strictly increasing — bids, sequence numbers). -/
  | strictMono  (field : FieldName)
  /-- `new[field] = old[field] + delta`. -/
  | fieldDelta  (field : FieldName) (delta : Int)
  /-- **`memberOf field set`** — value allowlist: `new[field] ∈ set`. The one-sided
  value-set the pair-table `allowedTransitions` cannot express ("`new[role] ∈ {admin,editor,viewer}`"
  without enumerating every `(old,new)` pair). Decidable, fail-closed (absent/ill-typed ⇒ `false`). -/
  | memberOf    (field : FieldName) (set : List Int)
  /-- **`prefixOf segFields prefix`** — namespace/path prefix containment: the ordered scalar
  path read from `segFields` (e.g. `["seg0","seg1",…]`) STARTS WITH `prefix : List Int`. The canonical
  nameservice policy "a subdomain may only be registered under a namespace the actor owns" — a structural
  prefix over the record substrate (each path segment is a named scalar). Fail-closed: a missing segment
  shorter than `prefix` ⇒ `false`. Mirrors the Rust datalog `feature_glob` path-prefix
  (`token/src/datalog_verify.rs:1398`). -/
  | prefixOf    (segFields : List FieldName) (pre : List Int)
  /-- **`inRangeTwoSided field lo hi`** — two-sided absolute value band: `lo ≤ new[field] ≤ hi`
  (the existing `fieldDeltaInRange` is RELATIVE to `old`; this is the ABSOLUTE band). AMM/price-band
  cells. Fail-closed. -/
  | inRangeTwoSided (field : FieldName) (lo hi : Int)
  /-- **`deltaBounded field d`** — REAL two-sided delta: `|new[field] − old[field]| ≤ d`. The
  catalog's `boundDelta`/`FieldDeltaInRange` are one-sided or relative-range; this is the symmetric
  absolute bound on change magnitude. Fail-closed on absent old/new. -/
  | deltaBounded (field : FieldName) (d : Int)
  /-- **Negation** (the Heyting `¬`) — accept iff `inner` rejects. Unboxed inner ⇒ no
  unbounded nesting (`dregg2 §1.5` Heyting fragment). -/
  | not         : SimpleConstraint → SimpleConstraint
  deriving Repr

/-- **The full state-constraint catalog** — simple constraints plus the cross-slot,
conservation, state-machine, disjunction, and (declared-but-deferred) cross-cell variants. -/
inductive StateConstraint where
  /-- Lift a simple constraint. -/
  | simple        : SimpleConstraint → StateConstraint
  /-- `new[left] ≤ new[right]` (queue tail ≤ head). -/
  | fieldLeField  (left right : FieldName)
  /-- `Σ new[fields] = value` (intra-cell post-state sum). -/
  | sumEquals     (fields : List FieldName) (value : Int)
  /-- `Σ new[inputs] = Σ old[inputs] + Σ new[outputs]` (intra-cell conservation across the
  transition — dregg1 `SumEqualsAcross`). -/
  | sumEqualsAcross (inputs outputs : List FieldName)
  /-- `new[field] ∈ [old[field] + lo, old[field] + hi]` (bounded growth). -/
  | fieldDeltaInRange (field : FieldName) (lo hi : Int)
  /-- `(old[field], new[field]) ∈ allowed` (a bounded state machine). -/
  | allowedTransitions (field : FieldName) (allowed : List (Int × Int))
  /-- **Single-level disjunction** (the Heyting `⊔`) over simple constraints. -/
  | anyOf         (variants : List SimpleConstraint)
  /-- **Cross-cell binding (γ.2)** — `this[localField]` delta vs `peer[peerField]` delta.
  DECLARED here; the single-cell evaluator defers it (returns `true`), exactly like dregg1's
  scalar evaluator — it is discharged by the JointTurn aggregate (Build 4). `eqOpp = true` is
  `EqualAndOpposite` (bilateral conservation), `false` is `Equal`. -/
  | boundDelta    (localField : FieldName) (peer : Nat) (peerField : FieldName) (eqOpp : Bool)
  /-- **Clearance / lattice compare (SGM mandate)** — admits iff the actor's clearance label
  (read from `new[actorLabelField]` as a numeric `Label.id`) DOMINATES the slot's sensitivity
  label `boxLabel` in the clearance graph `g`. Wires the proved-sound `ClearanceGraph.dominatesD`
  (`Authority/ClearanceGraph.lean:53`, soundness `dominates_of_dominatesD :92`) into the predicate
  language: "a write to this slot is admitted only if the actor is cleared at least as high as the
  slot's sensitivity". Decidable, computable, FAIL-CLOSED (absent/ill-typed actor-label field ⇒
  `false`). This is what makes an SGM clearance mandate enforceable INLINE by the executor rather
  than precomputed into an `admitTable`. -/
  | clearanceGe   (g : ClearanceGraph) (actorLabelField : FieldName) (boxLabel : Label)
  /-- **`affineLe terms c`** — affine inequality `Σ kᵢ·new[fᵢ] ≤ c` over named scalar fields
  (`terms : List (Int × FieldName)`, each `(kᵢ, fᵢ)`). The general multi-field arithmetic relation the
  catalog lacked: subsumes `fieldLeField l r` as `[(1,l),(-1,r)] ≤ 0` and gives price-band / `a+b ≤ c`
  invariants. Maps to a PLONK linear gate. Fail-closed: any absent/ill-typed term field ⇒ `false`. -/
  | affineLe      (terms : List (Int × FieldName)) (c : Int)
  /-- **`affineEq terms c`** — affine equation `Σ kᵢ·new[fᵢ] = c`. Subsumes `sumEquals` (all `kᵢ=1`)
  and re-expresses conservation. Maps to a PLONK linear gate. Fail-closed. -/
  | affineEq      (terms : List (Int × FieldName)) (c : Int)
  /-- **`reachable g fromField toLabel`** — DAG-prerequisite / reachability: the label read from
  `new[fromField]` (as `Label.id`) reaches/dominates `toLabel` in the graph `g` (`dominatesD`). The
  workflow-prerequisite predicate "this step is admissible only if a prerequisite marker is reached"
  (CWM advance / SGM admit), reusing the proved-sound `ClearanceGraph.dominatesD`. Distinct from
  `clearanceGe`: that fixes the box-label and reads the ACTOR's label; `reachable` reads an arbitrary
  state field as the source. Fail-closed on absent/ill-typed `fromField`. -/
  | reachable     (g : ClearanceGraph) (fromField : FieldName) (toLabel : Label)
  deriving Repr

/-! ## Evaluation — the executable admissibility check. -/

/-- A decidable `Int` comparison as a `Bool`. -/
private def intLe (a b : Int) : Bool := decide (a ≤ b)
private def intLt (a b : Int) : Bool := decide (a < b)

/-- Read the ordered scalar path from a list of segment field-names (`none` if ANY segment is
absent/ill-typed — fail-closed, so a path shorter than a queried prefix cannot match). -/
def readPath (v : Value) (segFields : List FieldName) : Option (List Int) :=
  segFields.foldr
    (fun f acc => match v.scalar f, acc with
                  | some x, some xs => some (x :: xs)
                  | _,      _       => none)
    (some [])

/-- `Σ kᵢ·v[fᵢ]` over named scalar fields (`none` if ANY field is absent/ill-typed — fail-closed). -/
def affineSum (v : Value) (terms : List (Int × FieldName)) : Option Int :=
  terms.foldr
    (fun t acc => match acc, v.scalar t.2 with
                  | some s, some x => some (s + t.1 * x)
                  | _,      _      => none)
    (some 0)

/-- Read a named field as a numeric clearance `Label` (`Label.id`), `none` if absent/ill-typed
(fail-closed: a `clearanceGe` over a missing actor-label field cannot be satisfied). The actor's
clearance level is stored as an `Int` scalar in the record and lifted to `Label.id`. -/
def actorLabelOf (v : Value) (f : FieldName) : Option Label :=
  (v.scalar f).map (fun i => Label.id i.toNat)

/-- **Evaluate a simple constraint** against `(old, new)`. Fail-closed on absent/ill-typed
fields (`none ⇒ false`). Recurses only through `not`. -/
def evalSimple : SimpleConstraint → Value → Value → Bool
  | .fieldEquals f val, _,   new => new.scalar f == some val
  | .fieldGe f val,     _,   new => match new.scalar f with | some x => intLe val x | none => false
  | .fieldLe f val,     _,   new => match new.scalar f with | some x => intLe x val | none => false
  | .immutable f,       old, new => match old.scalar f with
                                    | none   => true                        -- init: first write allowed
                                    | some a => new.scalar f == some a
  | .writeOnce f,       old, new => match old.scalar f with
                                    | none      => true
                                    | some 0    => true                     -- unwritten ⇒ any
                                    | some a    => new.scalar f == some a
  | .monotonic f,       old, new => match old.scalar f, new.scalar f with
                                    | some a, some b => intLe a b | _, _ => false
  | .strictMono f,      old, new => match old.scalar f, new.scalar f with
                                    | some a, some b => intLt a b | _, _ => false
  | .fieldDelta f d,    old, new => match old.scalar f, new.scalar f with
                                    | some a, some b => b == a + d | _, _ => false
  | .memberOf f set,    _,   new => match new.scalar f with
                                    | some x => set.contains x | none => false
  | .prefixOf segs pre, _,   new => match readPath new segs with
                                    | some path => pre.isPrefixOf path | none => false
  | .inRangeTwoSided f lo hi, _, new => match new.scalar f with
                                    | some x => intLe lo x && intLe x hi | none => false
  | .deltaBounded f d,  old, new => match old.scalar f, new.scalar f with
                                    | some a, some b => intLe (-d) (b - a) && intLe (b - a) d
                                    | _, _ => false
  | .not c,             old, new => !(evalSimple c old new)

/-- **Evaluate a full state constraint** against `(old, new)`. -/
def evalConstraint : StateConstraint → Value → Value → Bool
  | .simple c,              old, new => evalSimple c old new
  | .fieldLeField l r,      _,   new => match new.scalar l, new.scalar r with
                                        | some a, some b => intLe a b | _, _ => false
  | .sumEquals fs val,      _,   new => sumScalars new fs == some val
  | .sumEqualsAcross ins outs, old, new =>
      match sumScalars new ins, sumScalars old ins, sumScalars new outs with
      | some ni, some oi, some no => ni == oi + no
      | _, _, _ => false
  | .fieldDeltaInRange f lo hi, old, new =>
      match old.scalar f, new.scalar f with
      | some a, some b => intLe (a + lo) b && intLe b (a + hi)
      | _, _ => false
  | .allowedTransitions f allowed, old, new =>
      match old.scalar f, new.scalar f with
      | some a, some b => allowed.any (fun p => p.1 == a && p.2 == b)
      | _, _ => false
  | .anyOf variants,        old, new => variants.any (fun c => evalSimple c old new)
  | .boundDelta _ _ _ _,    _,   _   => false    -- FAIL-CLOSED: cross-cell delta is NOT evaluable in
                                                 -- the single-cell evaluator (no peer state in scope).
                                                 -- Matches dregg1's `evaluate` (`program.rs:1956`),
                                                 -- which returns `Err(BoundDeltaNotWired)` = REJECT here;
                                                 -- the bilateral discharge happens in the JointTurn /
                                                 -- CoordinatedCaveat path, NOT this gate. (Was `=> true`,
                                                 -- a fail-OPEN soundness hole — any program relying on a
                                                 -- `boundDelta` for safety had NO teeth.)
  | .clearanceGe g af box,  _,   new =>
      match actorLabelOf new af with
      | some actorLabel => dominatesD g actorLabel box
      | none            => false                 -- absent/ill-typed actor-label field ⇒ fail-closed
  | .affineLe terms c,      _,   new =>
      match affineSum new terms with
      | some s => intLe s c | none => false      -- absent/ill-typed term field ⇒ fail-closed
  | .affineEq terms c,      _,   new =>
      match affineSum new terms with
      | some s => s == c | none => false         -- absent/ill-typed term field ⇒ fail-closed
  | .reachable g ff toL,    _,   new =>
      match actorLabelOf new ff with
      | some fromLabel => dominatesD g fromLabel toL
      | none           => false                  -- absent/ill-typed source field ⇒ fail-closed

/-! ## RecordProgram + TransitionGuard dispatch + default-deny. -/

/-- Guard naming which transitions a `Cases` arm applies to (`cell/src/program.rs`). -/
inductive TransitionGuard where
  | always
  | methodIs    (method : Nat)
  | slotChanged (field : FieldName)
  | anyOf       (children : List TransitionGuard)
  | allOf       (children : List TransitionGuard)
  deriving Repr

mutual
/-- Does a guard dispatch on the action's *method/effect* (vs being a pure state guard)?
Used for default-deny: a `Cases` value with a method-dispatching arm denies unknown methods. -/
def TransitionGuard.isMethodDispatching : TransitionGuard → Bool
  | .always         => false
  | .methodIs _     => true
  | .slotChanged _  => false
  | .anyOf cs       => anyDispatching cs
  | .allOf cs       => anyDispatching cs
def anyDispatching : List TransitionGuard → Bool
  | []        => false
  | g :: rest => g.isMethodDispatching || anyDispatching rest
end

mutual
/-- Evaluate a guard against `(method, old, new)`. -/
def TransitionGuard.matches : TransitionGuard → Nat → Value → Value → Bool
  | .always,        _,      _,   _   => true
  | .methodIs m,    method, _,   _   => m == method
  | .slotChanged f, _,      old, new => !(old.scalar f == new.scalar f)
  | .anyOf cs,      method, old, new => anyMatch cs method old new
  | .allOf cs,      method, old, new => allMatch cs method old new
def anyMatch : List TransitionGuard → Nat → Value → Value → Bool
  | [],        _,      _,   _   => false
  | g :: rest, method, old, new => g.matches method old new || anyMatch rest method old new
def allMatch : List TransitionGuard → Nat → Value → Value → Bool
  | [],        _,      _,   _   => true
  | g :: rest, method, old, new => g.matches method old new && allMatch rest method old new
end

/-- One operation-scoped case: a guard + the constraints that bind when it matches. -/
structure TransitionCase where
  guard       : TransitionGuard
  constraints : List StateConstraint
  deriving Repr

/-- **The RecordProgram** — the developer-authored coalgebra structure-map. -/
inductive RecordProgram where
  /-- Terminal program: every (authorized) transition admissible. -/
  | none
  /-- A conjunction of constraints (the legacy `Always`-case shape). -/
  | predicate (constraints : List StateConstraint)
  /-- Operation-scoped cases; **no matching case ⇒ default-deny**. -/
  | cases     (cases : List TransitionCase)
  /-- An opaque AIR; admissibility = "carries a proof the circuit accepts" (Build 3). -/
  | circuit   (hash : Nat)
  deriving Repr

/-- **`admits` — the admissibility filter (the structure-map's domain).** Decidable, computable,
fail-closed. `none` admits all; `predicate` ANDs its constraints; `cases` ANDs every *matching*
arm's constraints and **denies when no arm matches** (the partial, default-deny arrow); `circuit`
denies in the pure evaluator (it needs the proof — discharged in `RecordCircuit`, Build 3). -/
def RecordProgram.admits : RecordProgram → Nat → Value → Value → Bool
  | .none,           _,      _,   _   => true
  | .predicate cs,   _,      old, new => cs.all (fun c => evalConstraint c old new)
  | .cases tcs,      method, old, new =>
      match tcs.filter (fun tc => tc.guard.matches method old new) with
      | []      => false                                              -- default-deny on no match
      | m :: ms => (m :: ms).all (fun tc => tc.constraints.all (fun c => evalConstraint c old new))
  | .circuit _,      _,      _,   _   => false

/-! ## Basic laws (the structure-map is a genuine, Heyting-respecting, fail-closed filter). -/

/-- The terminal program admits every transition. -/
theorem admits_none (m : Nat) (o n : Value) : RecordProgram.admits .none m o n = true := rfl

/-- A `predicate` program is exactly the conjunction of its constraints (definitional). -/
theorem admits_predicate (cs : List StateConstraint) (m : Nat) (o n : Value) :
    RecordProgram.admits (.predicate cs) m o n = cs.all (fun c => evalConstraint c o n) := rfl

/-- **Default-deny.** An empty `Cases` (and any `Cases` with no matching arm) denies. -/
theorem admits_cases_nil (m : Nat) (o n : Value) :
    RecordProgram.admits (.cases []) m o n = false := rfl

/-- A `Circuit` program is never admitted by the *pure* evaluator (it needs its proof). -/
theorem admits_circuit (h : Nat) (m : Nat) (o n : Value) :
    RecordProgram.admits (.circuit h) m o n = false := rfl

/-- **Negation is the Boolean complement** (the Heyting `¬` on the predicate algebra). -/
theorem evalSimple_not (c : SimpleConstraint) (o n : Value) :
    evalSimple (.not c) o n = !(evalSimple c o n) := rfl

/-- **Double negation collapses** (`¬¬c = c` on the decidable predicate algebra). -/
theorem evalSimple_not_not (c : SimpleConstraint) (o n : Value) :
    evalSimple (.not (.not c)) o n = evalSimple c o n := by
  simp [evalSimple]

/-- **Disjunction is `∃`/`any`** (the Heyting `⊔`). -/
theorem evalConstraint_anyOf (vs : List SimpleConstraint) (o n : Value) :
    evalConstraint (.anyOf vs) o n = vs.any (fun c => evalSimple c o n) := rfl

/-- **`boundDelta` now FAILS CLOSED (the soundness fix).** The single-cell evaluator REJECTS
every `boundDelta` constraint (was the silent-`true` fail-OPEN hole `Program.lean:144`). The cross-cell
delta is discharged at the JointTurn/CoordinatedCaveat seam, never admitted here. Mirrors dregg1's
`evaluate` returning `Err(BoundDeltaNotWired)` (`program.rs:1956`). -/
theorem evalConstraint_boundDelta_fails (lf : FieldName) (p : Nat) (pf : FieldName) (e : Bool)
    (o n : Value) : evalConstraint (.boundDelta lf p pf e) o n = false := rfl

/-- **`clearanceGe` admit-characterization.** The gate admits IFF the actor's clearance
label (read from `new[af]`) is present AND DOMINATES the slot's sensitivity label `box` in the
clearance graph `g` (`dominatesD`). Wires the proved-sound lattice primitive into admission. -/
theorem evalConstraint_clearanceGe_iff (g : ClearanceGraph) (af : FieldName) (box : Label)
    (o n : Value) :
    evalConstraint (.clearanceGe g af box) o n = true ↔
      ∃ actorLabel, actorLabelOf n af = some actorLabel ∧ dominatesD g actorLabel box = true := by
  unfold evalConstraint
  cases h : actorLabelOf n af with
  | none   => simp [h]
  | some a => simp [h]

/-- **`clearanceGe` ⇒ semantic dominance (soundness of the new atom).** An ADMITTED
`clearanceGe` write means the actor's clearance label `dominates` the slot's sensitivity
label in `g` (the `Prop`-level reflexive-transitive closure) — reusing the orphaned-but-proved
`dominates_of_dominatesD` (`ClearanceGraph.lean:92`). So the predicate language now has REAL lattice
teeth, not a precomputed table. -/
theorem evalConstraint_clearanceGe_sound (g : ClearanceGraph) (af : FieldName) (box : Label)
    (o n : Value) (h : evalConstraint (.clearanceGe g af box) o n = true) :
    ∃ actorLabel, actorLabelOf n af = some actorLabel ∧
      Dregg2.Authority.ClearanceGraph.dominates g actorLabel box := by
  obtain ⟨a, ha, hd⟩ := (evalConstraint_clearanceGe_iff g af box o n).mp h
  exact ⟨a, ha, Dregg2.Authority.ClearanceGraph.dominates_of_dominatesD g hd⟩

/-! ## New atom admit-characterizations (the policy-combinator core) — each PROVED. -/

/-- **`memberOf` admit-char.** Admits IFF the field is present and its value is in the
allowlist. Real teeth: a value not in `set` is rejected. -/
theorem evalSimple_memberOf_iff (f : FieldName) (set : List Int) (o n : Value) :
    evalSimple (.memberOf f set) o n = true ↔
      ∃ x, n.scalar f = some x ∧ set.contains x = true := by
  unfold evalSimple
  cases h : n.scalar f with
  | none   => simp
  | some x => simp

/-- **`prefixOf` admit-char.** Admits IFF the path reads (all segments present) AND the
queried prefix is a list-prefix of it. The structural nameservice containment. -/
theorem evalSimple_prefixOf_iff (segs : List FieldName) (pre : List Int) (o n : Value) :
    evalSimple (.prefixOf segs pre) o n = true ↔
      ∃ path, readPath n segs = some path ∧ pre.isPrefixOf path = true := by
  unfold evalSimple
  cases h : readPath n segs with
  | none      => simp
  | some path => simp

/-- **`inRangeTwoSided` admit-char.** Admits IFF the field is present and lies in `[lo,hi]`. -/
theorem evalSimple_inRangeTwoSided_iff (f : FieldName) (lo hi : Int) (o n : Value) :
    evalSimple (.inRangeTwoSided f lo hi) o n = true ↔
      ∃ x, n.scalar f = some x ∧ lo ≤ x ∧ x ≤ hi := by
  unfold evalSimple
  cases h : n.scalar f with
  | none   => simp
  | some x => simp [intLe, decide_eq_true_eq]

/-- **`deltaBounded` admit-char (REAL two-sided).** Admits IFF both old and new are present
and `|new − old| ≤ d` (symmetric: `-d ≤ new−old ≤ d`). -/
theorem evalSimple_deltaBounded_iff (f : FieldName) (d : Int) (o n : Value) :
    evalSimple (.deltaBounded f d) o n = true ↔
      ∃ a b, o.scalar f = some a ∧ n.scalar f = some b ∧ -d ≤ b - a ∧ b - a ≤ d := by
  unfold evalSimple
  cases ha : o.scalar f with
  | none   => simp
  | some a =>
    cases hb : n.scalar f with
    | none   => simp
    | some b => simp [intLe, decide_eq_true_eq]

/-- **`affineLe` admit-char.** Admits IFF every term-field reads AND the affine combination
`Σ kᵢ·new[fᵢ] ≤ c`. The general arithmetic relation. -/
theorem evalConstraint_affineLe_iff (terms : List (Int × FieldName)) (c : Int) (o n : Value) :
    evalConstraint (.affineLe terms c) o n = true ↔
      ∃ s, affineSum n terms = some s ∧ s ≤ c := by
  unfold evalConstraint
  cases h : affineSum n terms with
  | none   => simp [h]
  | some s => simp [h, intLe]

/-- **`affineEq` admit-char.** Admits IFF every term-field reads AND `Σ kᵢ·new[fᵢ] = c`. -/
theorem evalConstraint_affineEq_iff (terms : List (Int × FieldName)) (c : Int) (o n : Value) :
    evalConstraint (.affineEq terms c) o n = true ↔
      ∃ s, affineSum n terms = some s ∧ s = c := by
  unfold evalConstraint
  cases h : affineSum n terms with
  | none   => simp [h]
  | some s => simp [h]

/-- **`reachable` ⇒ semantic dominance (soundness).** An admitted `reachable` means the
source-field's label `dominates`/reaches `toLabel` in `g` (lifting `dominatesD` to the
`Prop`-level closure via the proved-sound `dominates_of_dominatesD`). The DAG-prerequisite teeth. -/
theorem evalConstraint_reachable_sound (g : ClearanceGraph) (ff : FieldName) (toL : Label)
    (o n : Value) (h : evalConstraint (.reachable g ff toL) o n = true) :
    ∃ fromLabel, actorLabelOf n ff = some fromLabel ∧
      Dregg2.Authority.ClearanceGraph.dominates g fromLabel toL := by
  have hiff : evalConstraint (.reachable g ff toL) o n = true ↔
      ∃ fromLabel, actorLabelOf n ff = some fromLabel ∧ dominatesD g fromLabel toL = true := by
    unfold evalConstraint
    cases hf : actorLabelOf n ff with
    | none          => simp [hf]
    | some fromLabel => simp [hf]
  obtain ⟨fromLabel, hf, hd⟩ := hiff.mp h
  exact ⟨fromLabel, hf, Dregg2.Authority.ClearanceGraph.dominates_of_dominatesD g hd⟩

/-! ## It runs (`#eval`) — real programs admitting / denying real record transitions. -/

/-- A counter cell: one scalar field `count`, program = "count only ever increases". -/
def counterProgram : RecordProgram := .predicate [.simple (.monotonic "count")]

def counterOld : Value := .record [("count", .int 5)]
def counterUp  : Value := .record [("count", .int 7)]   -- 7 ≥ 5  → admitted
def counterDn  : Value := .record [("count", .int 3)]   -- 3 ≥ 5? → denied

#guard (counterProgram.admits 0 counterOld counterUp)  --  true
#guard (counterProgram.admits 0 counterOld counterDn) == false  --  false

/-- A bounded state machine on `status`: only Open(0)→Claimed(1)→Paid(2). -/
def smProgram : RecordProgram :=
  .predicate [.allowedTransitions "status" [(0, 1), (1, 2)]]

#guard (smProgram.admits 0 (.record [("status", .int 0)]) (.record [("status", .int 1)]))  --  true  (Open→Claimed)
#guard (smProgram.admits 0 (.record [("status", .int 0)]) (.record [("status", .int 2)])) == false  --  false (Open↛Paid)

/-- A `Cases` program: on method `1` (a "deposit"), balance must strictly increase; any other
method has no matching arm and is **default-denied**. -/
def depositOnly : RecordProgram :=
  .cases [⟨.methodIs 1, [.simple (.strictMono "balance")]⟩]

def balLo : Value := .record [("balance", .int 100)]
def balHi : Value := .record [("balance", .int 150)]

#guard (depositOnly.admits 1 balLo balHi)  --  true  (method 1, balance ↑)
#guard (depositOnly.admits 1 balHi balLo) == false  --  false (method 1, balance ↓)
#guard (depositOnly.admits 2 balLo balHi) == false  --  false (method 2: no matching case → default-deny)

/-- Intra-cell conservation: `Σ new[ins] = Σ old[ins] + Σ new[outs]` (a split). -/
def splitProgram : RecordProgram := .predicate [.sumEqualsAcross ["a"] ["b"]]
-- old a=10; new a=4, b=6  ⇒  4 = 10 + 6? no.  new a=16, b=6 ⇒ 16 = 10 + 6 ✓
#guard (splitProgram.admits 0 (.record [("a", .int 10)]) (.record [("a", .int 16), ("b", .int 6)]))  --  true

/-! ### `boundDelta` is FAIL-CLOSED (the soundness-fix non-vacuity).  A program guarded ONLY by a
`boundDelta` now REJECTS every single-cell transition (was a fail-OPEN `true`). -/
def boundDeltaProgram : RecordProgram :=
  .predicate [.boundDelta "amt" 1 "amt" true]
-- Every single-cell write is rejected: the cross-cell delta is not evaluable here (fail-closed).
#guard (boundDeltaProgram.admits 0 (.record [("amt", .int 5)]) (.record [("amt", .int 5)])) == false  --  false
#guard (boundDeltaProgram.admits 0 (.record [("amt", .int 5)]) (.record [("amt", .int 6)])) == false  --  false

/-! ### `clearanceGe` (the SGM clearance mandate) — non-vacuity over the demo clearance ladder.

A three-level clearance ladder `top ⊐ mid ⊐ low` (ids 3 ⊐ 2 ⊐ 1).  A cell slot has sensitivity
`mid` (id 2); a write is admitted ONLY when the actor's clearance label (carried in the `clearance`
field of `new`) dominates `mid`.  `top` (3) and `mid` (2) are admitted; `low` (1) is REJECTED. -/
def clearanceLadder : ClearanceGraph :=
  { edges :=
      [ (Label.id 3, Label.id 2)      -- top ⊐ mid
      , (Label.id 2, Label.id 1) ] }  -- mid ⊐ low

/-- A slot whose sensitivity label is `mid` (id 2): a write requires actor clearance ≥ mid. -/
def clearanceProgram : RecordProgram :=
  .predicate [.clearanceGe clearanceLadder "clearance" (Label.id 2)]

-- ADMITTED: actor carries clearance `top` (3) — 3 dominates 2 (top ⊐ mid, edge).
#guard (clearanceProgram.admits 0 (.record [("clearance", .int 1)]) (.record [("clearance", .int 3)]))  --  true
-- ADMITTED: actor carries clearance `mid` (2) — reflexive dominance.
#guard (clearanceProgram.admits 0 (.record [("clearance", .int 1)]) (.record [("clearance", .int 2)]))  --  true
-- REJECTED: actor carries clearance `low` (1) — low does NOT dominate mid (no upward edge).
#guard (clearanceProgram.admits 0 (.record [("clearance", .int 2)]) (.record [("clearance", .int 1)])) == false  --  false
-- REJECTED: actor-label field absent — fail-closed.
#guard (clearanceProgram.admits 0 (.record [("clearance", .int 2)]) (.record [("other", .int 3)])) == false  --  false

/-- Non-vacuity at the theorem layer: the ADMIT case witnesses `dominatesD` AND lifts to the
`Prop`-level `dominates` (the proved soundness reduction). -/
example : evalConstraint (.clearanceGe clearanceLadder "clearance" (Label.id 2))
    (.record [("clearance", .int 1)]) (.record [("clearance", .int 3)]) = true := by decide

example : evalConstraint (.clearanceGe clearanceLadder "clearance" (Label.id 2))
    (.record [("clearance", .int 2)]) (.record [("clearance", .int 1)]) = false := by decide

/-! ### Policy-combinator atom non-vacuity — each atom ADMITS a real transition AND REJECTS one.
(The mandatory anti-vacuity pair; all `by decide`, no `native_decide`.) -/

-- memberOf: a role slot admitting only {1 admin, 2 editor, 3 viewer}.
def roleProgram : RecordProgram := .predicate [.simple (.memberOf "role" [1, 2, 3])]
#guard (roleProgram.admits 0 (.record [("role", .int 0)]) (.record [("role", .int 2)]))          -- true  (editor ∈ set)
#guard (roleProgram.admits 0 (.record [("role", .int 0)]) (.record [("role", .int 9)])) == false  -- false (9 ∉ set)
example : evalSimple (.memberOf "role" [1,2,3]) (.record []) (.record [("role", .int 2)]) = true := by decide
example : evalSimple (.memberOf "role" [1,2,3]) (.record []) (.record [("role", .int 9)]) = false := by decide

-- prefixOf: a 2-segment path must register UNDER the namespace [10, 20] (owned by the actor).
def nsProgram : RecordProgram := .predicate [.simple (.prefixOf ["seg0", "seg1", "seg2"] [10, 20])]
-- ADMIT: path [10,20,7] starts with [10,20].
#guard (nsProgram.admits 0 (.record []) (.record [("seg0", .int 10), ("seg1", .int 20), ("seg2", .int 7)]))  -- true
-- REJECT: path [10,99,7] does NOT start with [10,20].
#guard (nsProgram.admits 0 (.record []) (.record [("seg0", .int 10), ("seg1", .int 99), ("seg2", .int 7)])) == false  -- false
-- REJECT: a segment missing ⇒ fail-closed.
#guard (nsProgram.admits 0 (.record []) (.record [("seg0", .int 10), ("seg1", .int 20)])) == false  -- false
example : evalSimple (.prefixOf ["a","b"] [10]) (.record []) (.record [("a", .int 10), ("b", .int 5)]) = true := by decide
example : evalSimple (.prefixOf ["a","b"] [10]) (.record []) (.record [("a", .int 11), ("b", .int 5)]) = false := by decide

-- inRangeTwoSided: a price slot constrained to the absolute band [100, 200].
def priceProgram : RecordProgram := .predicate [.simple (.inRangeTwoSided "price" 100 200)]
#guard (priceProgram.admits 0 (.record []) (.record [("price", .int 150)]))          -- true
#guard (priceProgram.admits 0 (.record []) (.record [("price", .int 250)])) == false  -- false (above band)
example : evalSimple (.inRangeTwoSided "p" 100 200) (.record []) (.record [("p", .int 100)]) = true := by decide
example : evalSimple (.inRangeTwoSided "p" 100 200) (.record []) (.record [("p", .int 99)])  = false := by decide

-- deltaBounded: a balance may move by at most ±5 per turn (REAL two-sided).
def jitterProgram : RecordProgram := .predicate [.simple (.deltaBounded "bal" 5)]
#guard (jitterProgram.admits 0 (.record [("bal", .int 100)]) (.record [("bal", .int 104)]))          -- true  (+4)
#guard (jitterProgram.admits 0 (.record [("bal", .int 100)]) (.record [("bal", .int 96)]))           -- true  (−4)
#guard (jitterProgram.admits 0 (.record [("bal", .int 100)]) (.record [("bal", .int 110)])) == false  -- false (+10)
#guard (jitterProgram.admits 0 (.record [("bal", .int 100)]) (.record [("bal", .int 90)]))  == false  -- false (−10)
example : evalSimple (.deltaBounded "x" 5) (.record [("x", .int 0)]) (.record [("x", .int 5)])  = true  := by decide
example : evalSimple (.deltaBounded "x" 5) (.record [("x", .int 0)]) (.record [("x", .int 6)])  = false := by decide
example : evalSimple (.deltaBounded "x" 5) (.record [("x", .int 0)]) (.record [("x", .int (-6))]) = false := by decide

-- affineLe: a price band `2·bid ≤ ask + 100`, i.e. 2·bid − ask ≤ 100.
def bandProgram : RecordProgram := .predicate [.affineLe [(2, "bid"), (-1, "ask")] 100]
#guard (bandProgram.admits 0 (.record []) (.record [("bid", .int 60), ("ask", .int 40)]))           -- true  (120−40=80 ≤ 100)
#guard (bandProgram.admits 0 (.record []) (.record [("bid", .int 90), ("ask", .int 40)])) == false   -- false (180−40=140 > 100)
example : evalConstraint (.affineLe [(2,"b"),(-1,"a")] 100) (.record []) (.record [("b", .int 60),("a", .int 40)]) = true := by decide
example : evalConstraint (.affineLe [(2,"b"),(-1,"a")] 100) (.record []) (.record [("b", .int 90),("a", .int 40)]) = false := by decide

-- affineEq: conservation `in = out0 + out1` re-expressed as `in − out0 − out1 = 0`.
def consvProgram : RecordProgram := .predicate [.affineEq [(1, "inp"), (-1, "o0"), (-1, "o1")] 0]
#guard (consvProgram.admits 0 (.record []) (.record [("inp", .int 10), ("o0", .int 6), ("o1", .int 4)]))          -- true  (10−6−4=0)
#guard (consvProgram.admits 0 (.record []) (.record [("inp", .int 10), ("o0", .int 6), ("o1", .int 3)])) == false  -- false (10−6−3=1)
example : evalConstraint (.affineEq [(1,"i"),(-1,"o")] 0) (.record []) (.record [("i", .int 7),("o", .int 7)]) = true := by decide
example : evalConstraint (.affineEq [(1,"i"),(-1,"o")] 0) (.record []) (.record [("i", .int 7),("o", .int 6)]) = false := by decide

-- reachable: a workflow `step` field must reach the prerequisite marker `done` (id 1) in the DAG.
-- DAG: step-id 2 (review) reaches 1 (drafted); step-id 3 (publish) reaches 2 reaches 1.
def workflowDag : ClearanceGraph :=
  { edges := [ (Label.id 3, Label.id 2), (Label.id 2, Label.id 1) ] }
def workflowProgram : RecordProgram := .predicate [.reachable workflowDag "step" (Label.id 1)]
-- ADMIT: step 3 (publish) reaches prerequisite 1.
#guard (workflowProgram.admits 0 (.record []) (.record [("step", .int 3)]))          -- true
-- REJECT: step 4 is not in the DAG ⇒ cannot reach 1.
#guard (workflowProgram.admits 0 (.record []) (.record [("step", .int 4)])) == false  -- false
example : evalConstraint (.reachable workflowDag "step" (Label.id 1)) (.record []) (.record [("step", .int 3)]) = true := by decide
example : evalConstraint (.reachable workflowDag "step" (Label.id 1)) (.record []) (.record [("step", .int 4)]) = false := by decide

#assert_axioms evalConstraint_boundDelta_fails
#assert_axioms evalConstraint_clearanceGe_iff
#assert_axioms evalConstraint_clearanceGe_sound
#assert_axioms evalSimple_memberOf_iff
#assert_axioms evalSimple_prefixOf_iff
#assert_axioms evalSimple_inRangeTwoSided_iff
#assert_axioms evalSimple_deltaBounded_iff
#assert_axioms evalConstraint_affineLe_iff
#assert_axioms evalConstraint_affineEq_iff
#assert_axioms evalConstraint_reachable_sound

end Dregg2.Exec
