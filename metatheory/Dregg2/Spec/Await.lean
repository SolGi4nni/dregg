/-
# Dregg2.Spec.Await — the await family factored into its two orthogonal halves.

The executable `Dregg2.Await` presents the await family as one continuation primitive with
four faces. This module makes the sharper structural claim:

> **The await family factors as a direct sum of two orthogonal components:**
>
>   `await  ≅  (temporal discharge : a Guard deferred over time)  ⊕  (dataflow : a
>             promise graph)`.
>
>   * The **temporal** summand answers *"is this turn admissible yet?"* — a `Spec.Guard`
>     of the `witnessed` (third-party) kind whose discharge is deferred over a `Height`:
>     a `Conditional`. Its resolution is exactly `Guard.admits` of that witnessed guard,
>     gated by a deadline. A `Conditional` is a third-party caveat deferred over time,
>     reusing `Authority.Discharge.admits_mono_discharge` verbatim.
>
>   * The **dataflow** summand answers *"where does the awaited value come from?"* — a
>     `Promise`/`EventualRef`: a handle to a value produced by a pending step, and a
>     `PromiseGraph` is a DAG of such handles (the CapTP pipelining graph). It carries
>     a value-future and a dependency edge, no predicate-over-time.

`await_two_faces` proves the substantive claim: the temporal coordinate carries its full
`Guard`-over-time semantics (`conditional_is_temporal_guard`) regardless of the paired
dataflow coordinate. The four faces of `Dregg2.Await` are recovered as projections:
`discharge`/`intent`/`ConditionalTurn` = the temporal projection;
`zkpromise`/`promiseGraph` = the dataflow projection.

Abstract carriers throughout: `Gateway` is the third-party identity; `Height` is an
abstract linear order, never `Nat`-for-semantics.
-/
import Dregg2.Spec.Guard
import Dregg2.Await
import Dregg2.Authority.Discharge
import Dregg2.Tactics
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort
import Mathlib.Order.Extension.Linear

namespace Dregg2.Spec

open Dregg2.Laws
open Dregg2.Authority (Caveat Token Discharges)

-- The `Height`/`Node` instances are carried as section variables so the *spec* reads
-- uniformly; several individual keystones don't consume them. These are spurious
-- section-variable lints, not real unused-binder bugs — silence them file-wide.
set_option linter.unusedSectionVars false

/-! ## §0 — Abstract `Height`: the temporal axis as a bare linear order.

The deadline/now comparison is the *only* structure the temporal half needs of time. We
take it abstractly as a `LinearOrder` — there is no arithmetic on heights here, only the
`≤` of "has the deadline passed?". This keeps the temporal half `Nat`-free at the
semantics level (cf. the `Caveat.Height := Nat` *demo* alias, which is for `#eval` only).
-/

variable {Height : Type} [LinearOrder Height]

/-! ## §1 — THE TEMPORAL HALF: a `Conditional` = a `witnessed` Guard deferred over time.

We instantiate `Spec.Guard` at the verify seam where the *statement* is a third-party
`Gateway` and the *witness supply* is a `Discharges Gateway` (the `Authority.Caveat`
discharge environment: which gateways have settled). The `Verifiable` instance routes the
witnessed branch straight to "has this gateway discharged?" — making a witnessed guard a
third-party caveat, exactly the `Authority.Discharge` reading.
-/

variable {Gateway : Type} {Request : Type}

/-- The verify-seam instance that makes a `witnessed g` guard mean *"gateway `g` has
discharged"*. The `Statement` is the `Gateway`; the `Witness` supply is a
`Discharges Gateway`; `Verify g d := d g`. This is the *single* point where the temporal
half borrows the `Authority.Caveat` discharge environment — a witnessed guard becomes a
third-party caveat. -/
instance gatewayVerifiable : Verifiable Gateway (Discharges Gateway) where
  Verify g d := d g

/-- The verify-seam reduction for `gatewayVerifiable`: `Verify g d` is `d g`. A `@[simp]`
lemma so the `witnessed`-guard's `admits` rewrites to "gateway discharged" definitionally. -/
@[simp] theorem gatewayVerifiable_verify (g : Gateway) (d : Discharges Gateway) :
    Verifiable.Verify (self := gatewayVerifiable) g d = d g := rfl

/-- **`Conditional`** — a third-party `Guard` whose discharge is **deferred over time**.
It carries:
  * `gateway`  — the third-party `Gateway` whose settlement resolves it (the witnessed
    statement of the underlying `Spec.Guard.witnessed`);
  * `deadline` — the `Height` past which an unresolved conditional **expires**;
  * `height`   — the current `Height` (the scheduler's clock).

A `Conditional` IS a `ConditionalTurn`/`discharge` face: a suspended turn that holds open
until either its gateway discharges (it resolves) or the deadline passes (it expires). The
underlying object is literally `Guard.witnessed gateway` (see `guard`). -/
structure Conditional (Gateway Request Height : Type) where
  /-- The third-party gateway whose discharge resolves this conditional. -/
  gateway  : Gateway
  /-- The timeout height: past this, an unresolved conditional expires. -/
  deadline : Height
  /-- The current scheduler clock. -/
  height   : Height

namespace Conditional

/-- The underlying `Spec.Guard` of a conditional: the `witnessed` (third-party) guard on
its gateway. This is the unification anchor — a `Conditional` *decorates* this single
`Guard` with a deadline and a clock. The `Request` parameter is the guard's request type;
the witnessed branch ignores the request (it reads only the witness supply). -/
def guard (c : Conditional Gateway Request Height) :
    Guard Request Gateway :=
  Guard.witnessed c.gateway

/-- The three-valued resolution state of a conditional. -/
inductive State where
  /-- Not yet discharged, deadline not yet passed: still suspended. -/
  | Pending
  /-- The gateway discharged in time: the turn is live. -/
  | Resolved
  /-- The deadline passed with the gateway still undischarged: timed out. -/
  | Expired
  deriving DecidableEq, Repr

open State

/-- **`resolve c req d`** — the resolution of a conditional under request `req` and the
current discharge environment `d`:

  * **`Resolved`** iff the underlying witnessed guard discharges (`d gateway`) AND the
    clock is within the deadline (`height ≤ deadline`);
  * **`Expired`** iff the deadline has *strictly* passed (`deadline < height`) and the
    gateway has not discharged;
  * **`Pending`** otherwise (within deadline, gateway not yet settled).

Resolution is therefore `Guard.admits` of the witnessed guard, **gated by**
`height ≤ deadline` — the content of `conditional_is_temporal_guard`. -/
def resolve (c : Conditional Gateway Request Height)
    (req : Request) (d : Discharges Gateway) : State :=
  if c.guard.admits req (fun _ => d) = true then
    if c.height ≤ c.deadline then Resolved else Expired
  else
    if c.deadline < c.height then Expired else Pending

/-! ## §2 — `conditional_is_temporal_guard` (the temporal keystone).

A `Conditional`'s resolution is exactly `Guard.admits` of its witnessed guard, gated by
`height ≤ deadline`: a `ConditionalTurn` is a third-party caveat (`Spec.Guard`) deferred
over time. -/

/-- **`conditional_is_temporal_guard`** — a conditional resolves to `Resolved` iff its
underlying `Spec.Guard.witnessed gateway` admits (under the discharge environment `d`)
and the clock is within the deadline (`height ≤ deadline`). -/
theorem conditional_is_temporal_guard (c : Conditional Gateway Request Height)
    (req : Request) (d : Discharges Gateway) :
    c.resolve req d = State.Resolved ↔
      (c.guard.admits req (fun _ => d) = true ∧ c.height ≤ c.deadline) := by
  unfold resolve
  by_cases hadm : c.guard.admits req (fun _ => d) = true
  · simp only [hadm, if_true]
    by_cases hdl : c.height ≤ c.deadline <;> simp [hdl]
  · simp only [Bool.not_eq_true] at hadm
    simp only [hadm]
    -- the not-admitted branch can never be `Resolved`
    by_cases hexp : c.deadline < c.height <;> simp [hexp]

/-- **`resolved_iff_gateway_discharged`** — unfolding one step further: a conditional is
`Resolved` exactly when its gateway has settled (`d c.gateway = true`) and the clock is
within the deadline. -/
theorem resolved_iff_gateway_discharged (c : Conditional Gateway Request Height)
    (req : Request) (d : Discharges Gateway) :
    c.resolve req d = State.Resolved ↔ (d c.gateway = true ∧ c.height ≤ c.deadline) := by
  rw [conditional_is_temporal_guard]
  constructor <;> (rintro ⟨h1, h2⟩; refine ⟨?_, h2⟩)
  · simpa [guard] using h1
  · simpa [guard] using h1

/-! ## §3 — `resolve_monotone` (reuses `admits_mono_discharge`).

Once `Resolved`, never un-resolves: discharge moves forward only. The
`Authority.Discharge.admits_mono_discharge` keystone applies by reading the conditional's
gateway as a single third-party `Caveat` in a one-caveat `Token`. -/

/-- A conditional, viewed as a one-caveat `Token`: a biscuit carrying the single
third-party caveat on its gateway. This is the bridge through which the
`Authority.Discharge` monotonicity keystone applies to a `Conditional` *unchanged* — a
conditional is a one-rung attenuation chain. -/
def asToken (c : Conditional Gateway Request Height) : Token Request Gateway :=
  { kind := .biscuit, caveats := [Caveat.thirdParty c.gateway] }

/-- The conditional's "gateway discharged" predicate equals its one-caveat token's
`admits`. The seam that lets `admits_mono_discharge` speak about a `Conditional`. -/
theorem gateway_admits_eq_token (c : Conditional Gateway Request Height)
    (req : Request) (d : Discharges Gateway) :
    (c.guard.admits req (fun _ => d) = true) ↔ (c.asToken).admits req d = true := by
  simp [guard, asToken, Token.admits, Caveat.ok]

/-- **`resolve_monotone`** — if the discharge environment only accumulates
(`Discharges.le d d'` — a settled gateway stays settled) and the clock does not move, a
`Resolved` conditional stays `Resolved`. Discharge resolves forward only. Proof applies
`admits_mono_discharge` via `asToken`. -/
theorem resolve_monotone (c : Conditional Gateway Request Height)
    (req : Request) {d d' : Discharges Gateway}
    (hle : Dregg2.Authority.Discharges.le d d')
    (h : c.resolve req d = State.Resolved) :
    c.resolve req d' = State.Resolved := by
  rw [conditional_is_temporal_guard] at h ⊢
  obtain ⟨hadm, hdl⟩ := h
  refine ⟨?_, hdl⟩
  -- move the discharged-ness forward through the keystone
  rw [gateway_admits_eq_token] at hadm ⊢
  exact Dregg2.Authority.admits_mono_discharge c.asToken req hle hadm

/-- **`expired_stays_expired`** — once `Expired`, an undischarged conditional stays
`Expired` as long as its gateway remains undischarged (the deadline cannot un-pass).
Stated for the genuine-timeout case (gateway never settled), which is the permanently
expired state. -/
theorem expired_stays_expired (c : Conditional Gateway Request Height)
    (req : Request) (d d' : Discharges Gateway)
    (hund' : d' c.gateway = false)
    (h : c.resolve req d = State.Expired) :
    c.resolve req d' = State.Expired := by
  -- the deadline has passed — DERIVED from `h` (both ways `resolve` yields `Expired`
  -- force `¬ height ≤ deadline`, i.e. `deadline < height` in the linear order).
  have hpast : c.deadline < c.height := by
    apply not_le.mp
    intro hle
    unfold resolve at h
    revert h
    by_cases hadm : c.guard.admits req (fun _ => d) = true <;>
      simp [hadm, hle]
  unfold resolve
  have hadm' : c.guard.admits req (fun _ => d') = true ↔ d' c.gateway = true := by
    simp [guard]
  by_cases hx : c.guard.admits req (fun _ => d') = true
  · rw [hadm'] at hx; rw [hx] at hund'; exact absurd hund' (by simp)
  · simp only [Bool.not_eq_true] at hx
    simp [hx, hpast]

/-! ## §4 — THE DATAFLOW HALF: a `Promise`/`EventualRef` and a `PromiseGraph` (DAG).

The orthogonal summand. A `Promise` is a *handle to a value produced by a pending step*;
a `PromiseGraph` is a DAG of such handles (mirrors `Await.promiseGraph`, the CapTP
pipelining graph). This half carries NO predicate-over-time — only a value-future and a
dependency edge. We keep the node carrier abstract (a `Finset` of node ids over a
`DecidableEq` carrier) so acyclicity/topological statements are faithful, not `Nat`-coded.
-/

variable {Node : Type} [DecidableEq Node]

/-- **`Promise`/`EventualRef`** — a reference to a value produced by a *pending* step,
identified by a `Node` id and tagged with whether it has resolved. This is the dataflow
face's atom: a value-future, with no guard and no deadline. (`fulfilled = true` ⇒ the
slot holds its value; `false` ⇒ still pending / possibly broken.) -/
structure Promise (Node : Type) where
  /-- The node id producing this promise's value. -/
  id        : Node
  /-- Has the producing step resolved this promise's value? -/
  fulfilled : Bool

/-- An `EventualRef` is exactly a `Promise` — the CapTP "eventual reference" naming. -/
abbrev EventualRef := Promise

/-- **`PromiseGraph`** — a DAG of promises (mirrors `Await.promiseGraph`). `nodes` is the
finite carrier of promise ids; `dep i j` means *promise `i` awaits promise `j`'s value*
(`i` depends on `j`, i.e. `j` must resolve first). This is the pure dataflow shape: nodes
+ a dependency edge relation, no predicate-over-time anywhere. -/
structure PromiseGraph (Node : Type) where
  /-- The finite set of promise ids in the graph. -/
  nodes : Finset Node
  /-- `dep i j` : promise `i` depends on (awaits) promise `j`. -/
  dep   : Node → Node → Prop

namespace PromiseGraph

/-- The transitive closure of the dependency edge: `Depends g i j` iff `i` (transitively)
awaits `j`. A promise's *transitive* dependencies are everything that must resolve before
it can. -/
inductive Depends (g : PromiseGraph Node) : Node → Node → Prop where
  /-- A direct edge. -/
  | edge {i j} : g.dep i j → Depends g i j
  /-- Transitivity along the dataflow. -/
  | trans {i j k} : Depends g i j → Depends g j k → Depends g i k

/-- **`Acyclic g`** — no promise (transitively) depends on itself: the dataflow graph has
no cycle. This is well-formedness for a promise graph — a promise that awaited its own
future would be a deadlock, exactly what acyclicity forbids. -/
def Acyclic (g : PromiseGraph Node) : Prop := ∀ i, ¬ Depends g i i

/-! ### §5 — `pipeline_topological`: acyclic ⇒ resolves in topological order.

On an acyclic graph, `Depends` is a strict partial order (irreflexive + transitive) on the
finite carrier `g.nodes`, which guarantees a topological resolution order exists. Both the
strict-partial-order content and the explicit `IsTopoOrder` list are proved below via the
Szpilrajn linear extension (`extend_partialOrder`) and `Finset.sort`. -/

/-- A list `order` is a **topological order** for `g` iff it lists exactly `g.nodes` and,
whenever `i` depends on `j`, `j` appears **before** `i` (dependencies resolve first). This
is the faithful "resolves in topological order" statement — no promise is scheduled before
something it awaits. -/
def IsTopoOrder (g : PromiseGraph Node) (order : List Node) : Prop :=
  (∀ n, n ∈ order ↔ n ∈ g.nodes) ∧
  (∀ i j, g.dep i j → i ∈ order → j ∈ order →
    order.idxOf j ≤ order.idxOf i)

/-- **`depends_irrefl`** — on an acyclic graph, `Depends` is irreflexive: the
content of `Acyclic`, repackaged as the irreflexivity half of a strict partial order. A
promise never transitively awaits itself. -/
theorem depends_irrefl (g : PromiseGraph Node) (hac : Acyclic g) (i : Node) :
    ¬ Depends g i i := hac i

/-- **`depends_trans`** — `Depends` is transitive (it is a transitive closure):
the transitivity half of the strict partial order. Together with `depends_irrefl` this
makes `Depends` a **strict partial order** on the nodes of an acyclic promise graph — the
exact precondition under which a topological order is guaranteed to exist (every finite
strict partial order admits a linear extension; Szpilrajn). -/
theorem depends_trans (g : PromiseGraph Node) {i j k : Node}
    (hij : Depends g i j) (hjk : Depends g j k) : Depends g i k :=
  Depends.trans hij hjk

/-- **`idxOf_le_of_pairwise` — the sorted-list index lemma.** In a list `l` whose
elements are `Pairwise`-related by a relation `s` that is transitive, antisymmetric, and
total (a linear order on its carrier), if `a, b ∈ l` and `s a b`, then `a` appears no later
than `b` (`idxOf a ≤ idxOf b`). This is the bridge from "the sort respects `s`" to "the
output list respects `s` positionally" — the workhorse behind the topological-order
construction. Proof: if `b` came strictly before `a`, `Pairwise` would force `s b a`, and
antisymmetry with `s a b` would identify `a = b`, contradicting the strict index gap. -/
private theorem idxOf_le_of_pairwise (s : Node → Node → Prop)
    [IsTrans Node s] [Std.Antisymm s] [Std.Total s]
    (l : List Node) (hp : l.Pairwise s)
    {a b : Node} (ha : a ∈ l) (hb : b ∈ l) (hab : s a b) :
    l.idxOf a ≤ l.idxOf b := by
  by_contra hlt
  rw [Nat.not_le] at hlt
  have hbl : l.idxOf b < l.length := List.idxOf_lt_length_of_mem hb
  have hal : l.idxOf a < l.length := List.idxOf_lt_length_of_mem ha
  have hgb : l[l.idxOf b] = b := List.getElem_idxOf hbl
  have hga : l[l.idxOf a] = a := List.getElem_idxOf hal
  have hsba : s b a := by
    have := (List.pairwise_iff_getElem.1 hp) (l.idxOf b) (l.idxOf a) hbl hal hlt
    rwa [hgb, hga] at this
  have heq : a = b := Std.Antisymm.antisymm a b hab hsba
  rw [heq] at hlt
  exact absurd hlt (lt_irrefl _)

/-- **`pipeline_topological`** — on an acyclic graph, a topological resolution order exists.
`Depends` is a strict partial order on the finite carrier `g.nodes`; the explicit
`IsTopoOrder` list is constructed via the Szpilrajn linear extension (`extend_partialOrder`)
of the reversed reflexive closure `r a b := a = b ∨ Depends g b a`, sorted over `g.nodes`
by `Finset.sort`. A dependency `dep i j` gives `r j i`, so `j` precedes `i` in the sorted
list (`idxOf_le_of_pairwise`): dependencies resolve first. -/
theorem pipeline_topological (g : PromiseGraph Node) (hac : Acyclic g) :
    -- the strict-partial-order content: no self-dependency, transitive …
    ((∀ i, ¬ Depends g i i) ∧
     (∀ i j k, Depends g i j → Depends g j k → Depends g i k)) ∧
    -- … hence a topological resolution order EXISTS (Szpilrajn linear extension + sort).
    (∃ order : List Node, IsTopoOrder g order) := by
  classical
  refine ⟨⟨depends_irrefl g hac, fun _ _ _ => depends_trans g⟩, ?_⟩
  -- The reversed reflexive closure of `Depends`: a partial order whose linear extension,
  -- sorted over `g.nodes`, IS a topological order (dependencies precede their dependents).
  let r : Node → Node → Prop := fun a b => a = b ∨ Depends g b a
  have htrans : ∀ a b c, r a b → r b c → r a c := by
    rintro a b c (rfl | hab) (rfl | hbc)
    · exact Or.inl rfl
    · exact Or.inr hbc
    · exact Or.inr hab
    · exact Or.inr (depends_trans g hbc hab)
  have hantisymm : ∀ a b, r a b → r b a → a = b := by
    rintro a b (rfl | hab) (h2 | hba)
    · rfl
    · rfl
    · exact h2.symm
    · exact absurd (depends_trans g hab hba) (hac b)
  haveI ipo : IsPartialOrder Node r :=
    { refl := fun _ => Or.inl rfl, trans := htrans, antisymm := hantisymm }
  obtain ⟨s, hlin, hrs⟩ := extend_partialOrder r
  haveI : IsLinearOrder Node s := hlin
  haveI : DecidableRel s := Classical.decRel s
  refine ⟨g.nodes.sort s, ?_, ?_⟩
  · -- the sorted list lists exactly `g.nodes`.
    intro n; exact Finset.mem_sort s
  · -- and respects dependencies: `dep i j ⇒ r j i ⇒ s j i ⇒ j precedes i`.
    intro i j hdep hi hj
    have hsji : s j i := hrs _ _ (Or.inr (Depends.edge hdep))
    exact idxOf_le_of_pairwise s (g.nodes.sort s) (Finset.pairwise_sort g.nodes s) hj hi hsji

/-! ### §6 — `broken_promise_propagates`: failure flows along the dataflow edges. -/

/-- **`Resolves g res i`** — promise `i` resolves under the resolution assignment
`res : Node → Bool` iff `i` itself is marked resolved **and** every promise it directly
depends on resolves. This is the dataflow propagation rule: a promise needs its inputs.
We state it as a hypothesis-bundle (a `res` is *consistent* when it obeys this rule). -/
def Consistent (g : PromiseGraph Node) (res : Node → Bool) : Prop :=
  ∀ i j, g.dep i j → res i = true → res j = true

/-- **`broken_promise_propagates`** — a broken promise's direct dependents cannot resolve:
if `res` is consistent and `j` is broken, any `i` with `g.dep i j` is also broken.
Proof: contraposition on `Consistent`. -/
theorem broken_promise_propagates (g : PromiseGraph Node) (res : Node → Bool)
    (hcon : Consistent g res) {i j : Node}
    (hdep : g.dep i j) (hbroken : res j = false) :
    res i = false := by
  by_contra hi
  simp only [Bool.not_eq_false] at hi
  have : res j = true := hcon i j hdep hi
  rw [this] at hbroken
  exact absurd hbroken (by simp)

/-- **`broken_promise_propagates_trans`** — failure propagates the full transitive length:
if `j` is broken and `i` transitively depends on `j`, then `i` is also broken. -/
theorem broken_promise_propagates_trans (g : PromiseGraph Node) (res : Node → Bool)
    (hcon : Consistent g res) {i j : Node}
    (hdep : Depends g i j) (hbroken : res j = false) :
    res i = false := by
  induction hdep with
  | edge h => exact broken_promise_propagates g res hcon h hbroken
  | trans _ _ ih₁ ih₂ => exact ih₁ (ih₂ hbroken)

end PromiseGraph

/-! ## §7 — UNIFY: `await_two_faces` — temporal-discharge ⊕ dataflow.

The await family = (temporal-discharge `Guard`) ⊕ (dataflow promise graph). An `Await` is
the *pair* of the two summands: a promise is a value-future, a conditional is a
predicate-over-time. That these are two *separate* coordinates is a definitional fact of the
`Await` product (its field projections are `rfl`); the substantive `await_two_faces` keystone
records the load-bearing half — that the temporal coordinate keeps its full `Guard` semantics
no matter what the dataflow coordinate holds. -/

/-- **`Await`** — the await primitive, factored: a temporal `Conditional` (the
predicate-over-time half) paired with a dataflow `Promise` (the value-future half). The
four faces of `Dregg2.Await` are recovered as projections: `discharge`/`intent`/
`ConditionalTurn` = `.cond`; `zkpromise`/`promiseGraph` = `.prom`. -/
structure Await (Gateway Request Height Node : Type) where
  /-- The temporal-discharge summand: a `Guard` deferred over time. -/
  cond : Conditional Gateway Request Height
  /-- The dataflow summand: a value-future / eventual reference. -/
  prom : Promise Node

/-- **`await_two_faces`** — the temporal coordinate carries its full `Guard` semantics
regardless of the dataflow coordinate. An `Await ⟨c, p⟩`'s temporal projection resolves to
`Resolved` iff its underlying witnessed `Spec.Guard` admits and the clock is within the
deadline (`conditional_is_temporal_guard`), for any paired promise `p`. The product-field
projections (`cond`/`prom`) are definitional; the substantive content here is that the
temporal `Guard`-over-time semantics are independent of the dataflow coordinate. -/
theorem await_two_faces
    (c : Conditional Gateway Request Height) (p : Promise Node)
    (req : Request) (d : Discharges Gateway) :
    (Await.cond ⟨c, p⟩).resolve req d = State.Resolved ↔
      (c.guard.admits req (fun _ => d) = true ∧ c.height ≤ c.deadline) :=
  conditional_is_temporal_guard c req d

/-- **`temporal_face_is_await_discharge` — connect to `Await.four_faces_unify`.**
The temporal half of `Spec.Await` is the same object as the `discharge`/authority face of
the executable `Dregg2.Await`: both are a third-party caveat (a `witnessed`/`thirdParty`
guard) awaiting its gateway's settlement. We exhibit the link structurally — a `Conditional`
extracts to a one-caveat `Authority.Token` (its `asToken`), and that token's admissibility
is *definitionally* the conditional's underlying-guard admission. So `Spec.Await`'s temporal
summand and `Await.discharge` are the SAME `discharge` face, now equipped with a deadline. -/
theorem temporal_face_is_await_discharge (c : Conditional Gateway Request Height)
    (req : Request) (d : Discharges Gateway) :
    (c.asToken).admits req d = true ↔ c.guard.admits req (fun _ => d) = true :=
  (gateway_admits_eq_token c req d).symm

end Conditional

/-! ## §8 — Axiom-hygiene tripwires.

Pin every keystone to the three standard kernel axioms. -/

#assert_axioms Conditional.PromiseGraph.pipeline_topological
#assert_axioms Conditional.conditional_is_temporal_guard
#assert_axioms Conditional.resolved_iff_gateway_discharged
#assert_axioms Conditional.resolve_monotone
#assert_axioms Conditional.expired_stays_expired
#assert_axioms Conditional.gateway_admits_eq_token
#assert_axioms Conditional.PromiseGraph.depends_irrefl
#assert_axioms Conditional.PromiseGraph.depends_trans
#assert_axioms Conditional.PromiseGraph.broken_promise_propagates
#assert_axioms Conditional.PromiseGraph.broken_promise_propagates_trans
#assert_axioms Conditional.await_two_faces
#assert_axioms Conditional.temporal_face_is_await_discharge

end Dregg2.Spec
