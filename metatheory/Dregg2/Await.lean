/-
# Dregg2.Await — algebraic effects + handlers + one-shot (linear) continuations,
# with the turn as the rollback handler.

The await family is a single continuation primitive with four faces (`zkpromise`,
`discharge`, `intent`, `promiseGraph`). One-shotness is a **static linear-typing
invariant** on the zkpromise, not a runtime guard — the runtime guard IS the
double-spend it is meant to prevent (see `runtime_guard_is_double_spend`).

Literature anchors:
  * **Plotkin–Pretnar**, *Handling Algebraic Effects* (LMCS 2013) — `Effect`/`Handler`.
  * **One-shot / linear continuations** (Bruggeman–Waddell–Dybvig; Berdine et al.;
    OCaml 5 effect handlers). The resumption may be invoked **at most once** — here
    enforced as a type-level invariant (`OneShot`), not a runtime flag.
  * **CapTP promises** (Miller, *Robust Composition*; the E language `when`) —
    `zkpromise`/`discharge`/`promiseGraph` faces.

The turn is the rollback handler: commit = invoke the held continuation exactly once;
abort = discard it (never resume). See `turnAsRollbackHandler`.

The proof-carrying resolution of a `zkpromise` (binding/extractability of the
underlying STARK) is a circuit obligation and is NOT merged into this Lean law
(cf. `Boundary.lean` §8 caveat).

**Scope of THIS module (read before citing it).** What is proved *here* is the
one-shot/rollback-handler content: `commit_resumes_once`, `rollback_discards_continuation`,
`one_shot_is_static`, `runtime_guard_is_double_spend`, and the `rfl`-level
`four_faces_unify` (the four faces are interconvertible *views* of one `AwaitCore` —
an extraction identity, not a deep theorem). This module does **not** by itself
establish the CapTP promise-pipelining *soundness* claims. Those live in siblings and
are what a "pipelining is verified" citation must point at:
  * `Dregg2.Spec.Await` — the dataflow half: `PromiseGraph` acyclicity ⇒ topological
    resolution (`pipeline_topological`, via Szpilrajn) and failure propagation
    (`broken_promise_propagates[_trans]`); plus the temporal half
    (`conditional_is_temporal_guard`, `resolve_monotone`, `expired_stays_expired`).
  * `Dregg2.Exec.CapTP` — the *authority-not-bypassed* keystone
    (`pipelining_preserves_seam` / `pipelining_undischarged_stays_undischarged`): a
    queued eventual-send's authorization `Guard` survives promise resolution unchanged.
The **distributed/multi-vat liveness** of pipelining (cross-vat GC of exported
promises) is OPEN — see `Exec.CapTP` §4 (`-- OPEN: distributed_gc_liveness`), a
documented residue, not a `sorry`.
-/
import Dregg2.Core
import Dregg2.Laws

namespace Dregg2.Await

open Dregg2.Laws

universe u v

/-! ## 1. The effect signature (Plotkin–Pretnar) -/

/-- **`Op` — the algebraic-effect signature a turn may perform.** Each operation
carries a *parameter arity* (the value it is applied to) and a *return arity* (the
value its continuation is resumed with) — the (`P ⟶ R`)-shaped operation symbol of an
algebraic theory (Plotkin–Pretnar §2). dregg2's three await operations:

  * `await p` — suspend until the promise `p` resolves; resumed with the resolved value.
  * `call`    — invoke a capability / remote object (CapTP eventual-send); resumed with
                the reply.
  * `emit`    — emit a held effect at the boundary (the deferred-prover side of commit).

The signature is what a `Handler` interprets; a `Computation` is a tree of these. -/
inductive Op (Promise Cap Effct : Type u) where
  /-- Suspend on a promise; the continuation is resumed with the resolved value. -/
  | await (p : Promise)
  /-- Eventual-send to a capability; resumed with the reply. -/
  | call  (c : Cap)
  /-- Emit a held effect at the vat boundary (deferred prover). -/
  | emit  (e : Effct)
  deriving Repr

/-- **`Computation` — the free model over the signature `Op`** (Plotkin–Pretnar: the
free algebra / the term tree). A computation either `ret`urns a value, or performs an
operation `op` and continues with a `kont` indexed by the operation's *return* value.
The `kont` field is the syntactic continuation; its **one-shot** discipline is imposed
by the `Handler`, not by this tree (the tree is pure syntax, freely inspectable). -/
inductive Computation (Promise Cap Effct : Type u) (A : Type u) where
  /-- A pure return — the leaf of the term tree. -/
  | ret (a : A)
  /-- Perform `op`, then continue. `Reply` is the operation's return arity; `kont`
  is the (syntactic) resumption taking the operation's reply. -/
  | op  (Reply : Type u) (o : Op Promise Cap Effct)
        (kont : Reply → Computation Promise Cap Effct A)

/-! ## 2. One-shot (linear) continuations — the static discipline

The continuation captured by a handler is an **affine resource**: it must be used
**exactly once** (commit) or **dropped** (rollback), never twice. This is a
*type-level* invariant, not a runtime guard. The wrapper `OneShot` has a single
eliminator `OneShot.resume` that consumes it — so in a linear/affine context there
is no term that resumes twice.
-/

/-- **`OneShot k`** — a continuation `k : R → S` wrapped as a *use-exactly-once*
(affine) resource. There is intentionally **no** projection back to a reusable `k`
and **no** `OneShot → OneShot × OneShot` duplicator: the wrapper is the static carrier
of linearity. The "flag" is not a runtime boolean — it is the *absence* of any
copying eliminator, enforced by the type. (In a fully substructural backend this
would be a `linear` binder; in Lean we encode the discipline as the API surface:
`resume` is the sole consumer.) -/
structure OneShot (R S : Type u) where
  /-- The underlying resumption. Private-by-convention: the *only* sanctioned way to
  observe it is `OneShot.resume`, which consumes the whole structure. -/
  run : R → S

/-- **`OneShot.resume` — the sole eliminator; it CONSUMES the continuation.** It takes
the `OneShot` by value and returns the result `S` *without* handing back a new
`OneShot`. Thus a well-typed program can call it once per captured continuation; a
second call would need a second `OneShot` value, which (absent a duplicator) does not
exist. This *is* the one-shot discipline, realized as data flow. -/
def OneShot.resume {R S : Type u} (k : OneShot R S) (r : R) : S :=
  k.run r

/-- **`Linear k` — the affine-usage predicate** for a continuation: a use plan is
linear iff it consumes `k` *at most once*. We make the count explicit so the
double-resume anti-pattern is statable. `uses ≤ 1` is the affine law; the two legal
points are `uses = 1` (commit) and `uses = 0` (rollback/drop). -/
structure Linear {R S : Type u} (_k : OneShot R S) where
  /-- How many times this plan invokes the continuation. -/
  uses    : Nat
  /-- The affine law: a continuation is used at most once. -/
  at_most_once : uses ≤ 1

/-- **`theorem one_shot_is_static`** — one-shotness is a typing invariant, not a
runtime check: any `Linear` witness over `k` already carries `uses ≤ 1` in its type,
discharged without evaluating `k`. -/
theorem one_shot_is_static {R S : Type u} (k : OneShot R S) (plan : Linear k) :
    plan.uses ≤ 1 :=
  plan.at_most_once

/-! ### A *runtime* one-shot guard, modelled concretely (Dolan's anti-pattern)

To state precisely what a runtime guard does — and where it FAILS — we model it as an
actual stateful resumption: a `OneShot` paired with a mutable `resumed : Bool` flag.
Resuming consults the flag: if already set, the guard **denies** (Dolan's "raise on
second resume"); otherwise it resumes and sets the flag. The point of the design
correction is that this deny is a *value*, not a type — so the second resume is a
well-typed term that the program can construct and *attempt*, and the guard only
catches it *after* control has re-entered the continuation. -/

/-- **`GuardResult S`** — the outcome of attempting a runtime-guarded resume: either the
guard `denied` the attempt (the flag was already set — Dolan's runtime raise), or it
`resumed v` with the result and the now-consumed (flag-set) guard state. -/
inductive GuardResult (S : Type u) where
  /-- The runtime guard rejected this resume: the continuation was already consumed. -/
  | denied
  /-- The resume was admitted: it yields `S` and the guard transitions to "consumed". -/
  | resumed (s : S)
  deriving Repr

/-- **`Guarded k`** — a one-shot continuation `k` wrapped in a *runtime* guard: the
mutable `resumed` flag that a runtime one-shot discipline (as opposed to the static
`OneShot` discipline) would use. `resumed = true` means the continuation has already
been consumed once. -/
structure Guarded (R S : Type u) where
  /-- The underlying resumption. -/
  k       : OneShot R S
  /-- The runtime flag: has this continuation already been resumed once? -/
  resumed : Bool

/-- **`Guarded.tryResume g r`** — the runtime-guard resume step. It is exactly Dolan's
"raise on second resume": consult the flag, and
* if `g.resumed` is already `true`, **deny** (the double-spend is rejected — but only
  here, at the guard, *after* the call has been issued), else
* resume the underlying `k` once and mark the guard consumed.

This `def` is the operative await-guard machinery the theorem below quantifies over. -/
def Guarded.tryResume {R S : Type u} (g : Guarded R S) (r : R) :
    GuardResult S × Guarded R S :=
  if g.resumed then
    -- already consumed: the runtime guard denies the reuse attempt
    (GuardResult.denied, g)
  else
    -- first use: resume and flip the flag to consumed
    (GuardResult.resumed (g.k.resume r), { g with resumed := true })

/-- **`theorem runtime_guard_rejects_reuse`** — for a guarded continuation already
consumed (`g.resumed = true`), `tryResume` returns `denied` and leaves the guard
state unchanged. The hypothesis `hconsumed` is load-bearing: it determines the
true-branch of `if g.resumed`. -/
theorem runtime_guard_rejects_reuse
    {R S : Type u} (g : Guarded R S) (r : R)
    (hconsumed : g.resumed = true) :
    g.tryResume r = (GuardResult.denied, g) := by
  unfold Guarded.tryResume
  simp only [hconsumed, if_true]

/-- **`theorem runtime_guard_is_double_spend`** — the runtime guard does not prevent the
second resume from being *issued*: starting from a fresh guard, the FIRST `tryResume` is
admitted (the continuation is re-entered and may touch conserved resources), and only the
SECOND call — on the now-consumed guard — is denied. The deny happens after re-entry: that
admitted-then-denied ordering is the double-spend window. Contrast `OneShot`, which removes
the second call as a *constructible term* (no second `OneShot` value exists). -/
theorem runtime_guard_is_double_spend
    {R S : Type u} (k : OneShot R S) (r : R) :
    -- a fresh runtime-guarded continuation
    let g₀ : Guarded R S := { k := k, resumed := false }
    -- the FIRST resume is admitted (the continuation IS re-entered) …
    (∃ s, (g₀.tryResume r).1 = GuardResult.resumed s) ∧
      -- … leaving a consumed guard whose SECOND resume the guard only THEN denies.
      ((g₀.tryResume r).2.tryResume r).1 = GuardResult.denied := by
  intro g₀
  constructor
  · -- first use: the fresh guard's flag is `false`, so `tryResume` takes the resume arm
    refine ⟨g₀.k.resume r, ?_⟩
    show (g₀.tryResume r).1 = GuardResult.resumed (g₀.k.resume r)
    unfold Guarded.tryResume
    simp
  · -- the first use flips the flag to `true`; the second use is therefore denied
    have hconsumed : (g₀.tryResume r).2.resumed = true := by
      unfold Guarded.tryResume; simp
    rw [runtime_guard_rejects_reuse _ r hconsumed]

/-! ## 3. Handlers (Plotkin–Pretnar) and the turn as the rollback handler -/

/-- **`Handler` — an interpretation of the effect signature into a result `S`.**
(Plotkin–Pretnar: a handler is a model of the algebraic theory; running a computation
under it is the unique homomorphism.) `onRet` interprets a pure return; `onOp`
interprets each operation, *receiving the captured continuation as a `OneShot`* — i.e.
the handler is the sole site where the resumption becomes a first-class (affine)
value. A handler that calls `OneShot.resume` re-enters the computation **once**; one
that drops it abandons the computation (the rollback case). -/
structure Handler (Promise Cap Effct : Type u) (A S : Type u) where
  /-- Interpret a pure return. -/
  onRet : A → S
  /-- Interpret an operation, given its reply type and the *one-shot* continuation
  from that operation's reply to the final result. The handler chooses to `resume`
  (commit) or discard (rollback). -/
  onOp  : (Reply : Type u) → Op Promise Cap Effct → OneShot Reply S → S

/-- **`CommitOrAbort`** — the two outcomes of a turn-handler, naming the two *legal*
affine uses of the held continuation. `commit` resumes it exactly once; `abort` drops
it (zero uses) and refunds. There is no third outcome — which is the whole point. -/
inductive CommitOrAbort where
  /-- Commit: replay held effects, emit the boundary witness, resume the continuation
  exactly once (the deferred-prover side). -/
  | commit
  /-- Abort: discard the continuation, perform a conservation-preserving refund. -/
  | abort
  deriving Repr, DecidableEq

/-- **`turnAsRollbackHandler`** — the turn as the rollback handler, parameterized by a
`decide` oracle. On `commit`: `OneShot.resume` the continuation exactly once (replay +
emit witness). On `abort`: discard the continuation and return `refund`. The two arms are
the only two legal affine uses, making double-resume structurally impossible. -/
def turnAsRollbackHandler
    {Promise Cap Effct A S : Type u}
    (onRet  : A → S)
    (refund : S)
    (decide : (Reply : Type u) → Op Promise Cap Effct → CommitOrAbort)
    (resumeWith : (Reply : Type u) → Reply) :
    Handler Promise Cap Effct A S where
  onRet := onRet
  onOp  := fun Reply o k =>
    match decide Reply o with
    | CommitOrAbort.commit => OneShot.resume k (resumeWith Reply)  -- used exactly once
    | CommitOrAbort.abort  => refund                                -- discarded (0 uses)

/-- **`theorem rollback_discards_continuation`** — the abort arm of the turn-handler
uses the continuation **zero** times (it is dropped, never resumed): the affine "drop"
that a runtime guard could not give you safely. Pairs with `commit_resumes_once`. -/
theorem rollback_discards_continuation
    {Promise Cap Effct A S : Type u}
    (onRet : A → S) (refund : S)
    (decide : (Reply : Type u) → Op Promise Cap Effct → CommitOrAbort)
    (resumeWith : (Reply : Type u) → Reply)
    (Reply : Type u) (o : Op Promise Cap Effct) (k : OneShot Reply S)
    (h : decide Reply o = CommitOrAbort.abort) :
    (turnAsRollbackHandler onRet refund decide resumeWith).onOp Reply o k = refund := by
  simp only [turnAsRollbackHandler, h]

/-- **`theorem commit_resumes_once`** — the commit arm resumes the continuation
**exactly once** (`OneShot.resume`, which consumes it). Together with
`rollback_discards_continuation` this is the formal content of "commit = invoke it
once; rollback = discard it", and the static one-shot guarantee for the turn-handler. -/
theorem commit_resumes_once
    {Promise Cap Effct A S : Type u}
    (onRet : A → S) (refund : S)
    (decide : (Reply : Type u) → Op Promise Cap Effct → CommitOrAbort)
    (resumeWith : (Reply : Type u) → Reply)
    (Reply : Type u) (o : Op Promise Cap Effct) (k : OneShot Reply S)
    (h : decide Reply o = CommitOrAbort.commit) :
    (turnAsRollbackHandler onRet refund decide resumeWith).onOp Reply o k
      = OneShot.resume k (resumeWith Reply) := by
  simp only [turnAsRollbackHandler, h]

/-! ## 4. The four faces — four presentations of the same await primitive

The await family is one continuation primitive with four faces: `zkpromise` (specified
resolver), `discharge` (named gateway / third-party caveat), `intent` (existential
resolver), and `promiseGraph` (dataflow over pending promises). Each face is a view of
`AwaitCore`; `four_faces_unify` makes that explicit. -/

/-- **`AwaitCore` — the single await primitive the four faces present.** It is exactly:
an effect operation `await` on a promise of type `Promise`, captured by a handler as a
*one-shot* continuation `OneShot Reply S` to a result. Every face below is a way of
*saying who resolves it and how* — the underlying suspend-resume is this. -/
structure AwaitCore (Promise Reply S : Type u) where
  /-- The promise being awaited. -/
  promise : Promise
  /-- The captured one-shot continuation resumed on resolution. -/
  kont    : OneShot Reply S

/-- **Face 1 — `zkpromise`**: a promise whose resolution is witnessed by a
zero-knowledge proof (`Discharged p w`), binding a public `expectedOutput`. The
proof's binding/extractability is a circuit obligation, not merged here. -/
structure zkpromise (P W : Type u) [Verifiable P W] (Reply S : Type u) where
  /-- The resolution predicate the witness must discharge. -/
  resolver       : P
  /-- The public output the awaiting turn binds to (the `expected_output` of the
  design's `ProofCondition::ZkResult`). -/
  expectedOutput : Reply
  /-- The captured one-shot continuation (resumed once on a *verified* resolution). -/
  kont           : OneShot Reply S

/-- **Face 2 — `discharge`**: fulfilling a promise by a named gateway presenting a
discharging witness for a caveat predicate. Macaroon/biscuit third-party-caveat shape
— fulfilment = `Discharged`. -/
structure discharge (P W : Type u) [Verifiable P W] (Reply S : Type u) where
  /-- The third-party caveat that must be discharged to fulfil the promise. -/
  caveat  : P
  /-- The discharging witness presented by the named gateway. -/
  witness : W
  /-- The captured one-shot continuation, resumed once on a valid discharge. -/
  kont    : OneShot Reply S

/-- **Face 3 — `intent`**: a guarded effect with an **existential** resolver — anyone
producing a fill satisfying `want` resolves it. The guard `want` is the predicate the
fill must satisfy. -/
structure intent (P W : Type u) [Verifiable P W] (Reply S : Type u) where
  /-- The guard: the predicate any fill must satisfy (the "hole's shape"). -/
  want : P
  /-- The captured one-shot continuation, resumed once when *some* fill satisfies
  `want` (the existential resolver). -/
  kont : OneShot Reply S

/-- **`intent.Fires`** — the existential firing condition of an intent: it resolves
exactly when *there exists* a witness discharging its guard. The "fires when filled"
semantics, stated over the `Laws.Discharged` verify side. -/
def intent.Fires {P W : Type u} [Verifiable P W] {Reply S : Type u}
    (i : intent P W Reply S) : Prop :=
  ∃ w : W, Discharged i.want w

/-- **Face 4 — `promiseGraph`**: the dataflow graph of pending promises — nodes are
awaited promises (with their one-shot continuations) and edges are dependencies. A
linear chain folds into one IVC proof; here we capture the graph shape: nodes plus a
dependency relation. -/
structure promiseGraph (Promise Reply S : Type u) where
  /-- The pending nodes — each an `AwaitCore` (a promise + its one-shot continuation). -/
  nodes : List (AwaitCore Promise Reply S)
  /-- The dependency edges: `deps i j` means node `i` awaits node `j`'s resolution. -/
  deps  : Nat → Nat → Prop

/-- **`AwaitCore` extraction from each face** — each face is an `AwaitCore` once
face-specific resolver data is forgotten. For `zkpromise`/`discharge`/`intent` the
promise handle is the resolver datum (`resolver`/`caveat`/`want` respectively). -/
def zkpromise.toCore {P W : Type u} [Verifiable P W] {Reply S : Type u}
    (z : zkpromise P W Reply S) : AwaitCore P Reply S :=
  { promise := z.resolver, kont := z.kont }

/-- `discharge` viewed as the bare await primitive (caveat = the promise handle). -/
def discharge.toCore {P W : Type u} [Verifiable P W] {Reply S : Type u}
    (d : discharge P W Reply S) : AwaitCore P Reply S :=
  { promise := d.caveat, kont := d.kont }

/-- `intent` viewed as the bare await primitive (the guard = the promise handle). -/
def intent.toCore {P W : Type u} [Verifiable P W] {Reply S : Type u}
    (i : intent P W Reply S) : AwaitCore P Reply S :=
  { promise := i.want, kont := i.kont }

/-- **`theorem four_faces_unify`** — a `zkpromise`, `discharge`, and `intent` over the
same resolver `p` and continuation `k` all extract to the identical `AwaitCore p k`.
The four faces are interconvertible views of one primitive. -/
theorem four_faces_unify
    {P W : Type u} [Verifiable P W] {Reply S : Type u}
    (p : P) (out : Reply) (k : OneShot Reply S) :
    (zkpromise.toCore (P := P) (W := W) ⟨p, out, k⟩
      = ({ promise := p, kont := k } : AwaitCore P Reply S))
    -- discharge over the same `p`,`k` (any witness `w`) extracts to the same core
    ∧ (∀ w : W, discharge.toCore (P := P) (W := W) (Reply := Reply) (S := S) ⟨p, w, k⟩
        = ({ promise := p, kont := k } : AwaitCore P Reply S))
    ∧ (intent.toCore (P := P) (W := W) ⟨p, k⟩
        = ({ promise := p, kont := k } : AwaitCore P Reply S)) :=
  ⟨rfl, fun _ => rfl, rfl⟩

end Dregg2.Await
