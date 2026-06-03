/-
# Dregg2.Proof.LTS — the operational small-step LTS + forward-simulation square.

Closes the `Exec ⊑ Abstract` forward-simulation square for the single-cell record kernel. The
abstract step `recAbsStep` bundles three operational facts:

  (C) conservation:    `a'.balanceTotal = a.balanceTotal`
  (A) authority frame: `a'.authGraph    = a.authGraph`   (a balance transfer mutates no edge)
  (G) grounding:       the turn is authorized in `a.authGraph` (ownership ∨ `Graph.has`)

(G) is load-bearing: the step is authorized, not just conservative.

Also closes the authority-turn half via `recKDelegate` / `authAbsStep` (balance FIXED, a genuine
`Endow`/`AuthStep` fires), and unions both into `AbsStep'`.

The key obstruction is documented as `transfer_fires_no_authStep`: a balance transfer's graph
effect is the identity, and no no-op `AuthStep` exists, so the `AuthStep`-firing abstract step is
the correct model for authority turns — not balance turns.

No `axiom`/`admit`/`native_decide`/`sorry`. Read-only consumer of `RecordKernel`,
`ExecRefinement`, `Authority`.
-/
import Dregg2.Exec.RecordKernel
import Dregg2.Exec.AuthTurn
import Dregg2.Spec.ExecRefinement
import Dregg2.Spec.Authority

namespace Dregg2.Proof.LTS

open Dregg2.Exec
open Dregg2.Spec
open Dregg2.Authority (Caps Label)
open scoped BigOperators

/-! ## §1 — Abstraction function for the record kernel. -/

/-- The abstract state denoted by a record-kernel state: `recTotal` and `execGraph`. -/
def recAbsOf (k : RecordKernelState) : AbstractState :=
  { balanceTotal := recTotal k
    authGraph    := execGraph k.caps }

/-! ## §2 — `recAbsStep` — the abstract small-step transition relation. -/

/-- **`recAbsStep t a a'`** — the abstract small-step LTS edge for a balance turn `t`:

  * (C) conservation — `a'.balanceTotal = a.balanceTotal`;
  * (A) authority frame — `a'.authGraph = a.authGraph` (balance turns mutate no edge);
  * (G) grounding — `t` is authorized in `a.authGraph` (ownership ∨ `Graph.has`).

(G) makes this an authorized step rather than a bare conservation identity. -/
def recAbsStep (t : Turn) (a a' : AbstractState) : Prop :=
  -- (C) conservation: the balance-domain total is preserved.
  a'.balanceTotal = a.balanceTotal ∧
  -- (A) authority frame: a balance turn leaves the authority graph fixed.
  a'.authGraph = a.authGraph ∧
  -- (G) grounding: the turn is authorized in the authority graph (ownership ∨ reachability).
  (t.actor = t.src ∨ (a.authGraph).has t.actor t.src)

/-- The abstract LTS edge with the turn existentially closed: `a ⟶ a'` iff some authorized
balance turn realizes `recAbsStep`. -/
def AbsStep (a a' : AbstractState) : Prop :=
  ∃ t : Turn, recAbsStep t a a'

/-! ## §3 — The forward-simulation square.

```
              recAbsOf
   k  ──────────────────▶  recAbsOf k
   │                          │
   │ recKExec k turn = k'     │ recAbsStep turn
   ▼                          ▼
   k' ─────────────────▶  recAbsOf k'
              recAbsOf
```

Every committed `recKExec` step is matched by a genuine abstract step `recAbsStep`. -/

/-- **KEYSTONE — `recAbsStep_forward`.** The forward-simulation square: every committed
record-cell turn is matched by `recAbsStep`. Assembled from (C) ← `recKExec_conserves`,
(A) ← `recKExec_frame`, (G) ← `exec_authz_grounds_in_graph ∘ recKExec_authorized`. -/
theorem recAbsStep_forward (k k' : RecordKernelState) (turn : Turn)
    (h : recKExec k turn = some k') :
    recAbsStep turn (recAbsOf k) (recAbsOf k') := by
  refine ⟨?_, ?_, ?_⟩
  · -- (C) conservation: `recTotal k' = recTotal k`.
    simp only [recAbsOf]
    exact recKExec_conserves k k' turn h
  · -- (A) authority frame: `execGraph k'.caps = execGraph k.caps` (caps preserved).
    simp only [recAbsOf]
    rw [(recKExec_frame k k' turn h).2]
  · -- (G) grounding: the committed turn is grounded in `execGraph k.caps`.
    simp only [recAbsOf]
    exact exec_authz_grounds_in_graph k.caps turn (recKExec_authorized k k' turn h)

/-- Turn-index-closed form: every committed record step is matched by an `AbsStep`. -/
theorem recAbsStep_forward_exists (k k' : RecordKernelState) (turn : Turn)
    (h : recKExec k turn = some k') :
    AbsStep (recAbsOf k) (recAbsOf k') :=
  ⟨turn, recAbsStep_forward k k' turn h⟩

/-- Refines-shape: there exists `a' = recAbsOf k'` with `recAbsStep turn (recAbsOf k) a'`. The
bottom edge of `exec_step_refines`'s square is now a genuine abstract transition. -/
theorem recAbsStep_refines (k k' : RecordKernelState) (turn : Turn)
    (h : recKExec k turn = some k') :
    ∃ a', a' = recAbsOf k' ∧ recAbsStep turn (recAbsOf k) a' :=
  ⟨recAbsOf k', rfl, recAbsStep_forward k k' turn h⟩

/-! ## §3.1 — Lifting the square to whole runs. -/

/-- The reflexive-transitive closure of `AbsStep` — the run-level abstract LTS. Head-recursive,
mirroring `Execution.Run`. -/
inductive AbsRun : AbstractState → AbstractState → Prop where
  | refl (a : AbstractState) : AbsRun a a
  | step {a a' a'' : AbstractState} (s : AbsStep a a') (rest : AbsRun a' a'') : AbsRun a a''

/-- Every concrete record-kernel `Run` is matched by an `AbsRun` between the abstractions of its
endpoints. The square is stable under iteration. -/
theorem recAbsStep_run_forward {k k' : RecordKernelState}
    (hrun : Execution.Run recKernelSystem k k') :
    AbsRun (recAbsOf k) (recAbsOf k') := by
  -- Induct on the run via its recursor, with the motive reading the endpoints through `recAbsOf`.
  refine Execution.Run.rec
    (motive := fun a b _ => AbsRun (recAbsOf a) (recAbsOf b)) ?_ ?_ hrun
  · intro s; exact AbsRun.refl _
  · intro s t u hstep _ ih
    obtain ⟨turn, hturn⟩ := hstep
    exact AbsRun.step (recAbsStep_forward_exists _ _ turn hturn) ih

/-! ## §4 — Non-vacuity: `recAbsStep` genuinely constrains its arguments. -/

/-- `recAbsStep t a a'` entails `t` is authorized in `a`'s authority graph — the (G) conjunct
distinguishing `recAbsStep` from a bare conservation identity. -/
theorem recAbsStep_grounded {t : Turn} {a a' : AbstractState}
    (h : recAbsStep t a a') :
    t.actor = t.src ∨ (a.authGraph).has t.actor t.src :=
  h.2.2

/-- `recAbsStep` is not always-true: a turn with actor ≠ src over the empty authority graph
fails the (G) conjunct. -/
theorem recAbsStep_not_vacuous :
    ∃ (t : Turn) (a a' : AbstractState), ¬ recAbsStep t a a' := by
  -- actor 0, src 1 (actor ≠ src), over the empty authority graph.
  refine ⟨{ actor := 0, src := 1, dst := 2, amt := 0 },
          { balanceTotal := 0, authGraph := fun _ _ => False },
          { balanceTotal := 0, authGraph := fun _ _ => False }, ?_⟩
  rintro ⟨_, _, hg⟩
  rcases hg with hown | hreach
  · exact absurd hown (by decide)
  · obtain ⟨_, hedge⟩ := hreach
    exact hedge

/-! ## §5 — The obstruction: a balance transfer fires no `AuthStep`.

A balance transfer's graph effect is the identity (`recKExec_frame`), but every `AuthStep`
constructor mutates the graph via `addEdge`/`removeEdge` — so no no-op `AuthStep G G` exists.
The faithful abstract step for a balance transfer is `recAbsStep` (authority fixed); the
`AuthStep`-firing half of the LTS belongs to an authority-mutating executable kernel, which is
the named residue. -/

/-- Rights carrier for the obstruction statement (`Unit`-rights, matching `ExecRights`). -/
abbrev ObsRights := ExecRights

/-- **`transfer_fires_no_authStep`** — on the empty graph, no `AuthStep G G` exists: generative
constructors add an edge (so `G' ≠ G` on the empty graph) and restrictive ones require a held
cap (impossible on the empty graph). A balance transfer, whose graph effect is the identity, is
therefore not an `AuthStep` firing. -/
theorem transfer_fires_no_authStep
    (consents : Label → Prop) :
    ¬ Spec.AuthStep (CellId := Label) (Rights := ObsRights) consents
        (fun _ _ => False) (fun _ _ => False) := by
  -- An `addEdge` post-graph always HOLDS the freshly-added edge (the right disjunct) — so it
  -- cannot equal the empty graph. We package that as a reusable contradiction.
  have hadd : ∀ (G : Spec.Graph Label ObsRights) (h : Label) (c : Cap Label ObsRights),
      (fun _ _ => False) = Spec.addEdge G h c → False := by
    intro G h c hr
    -- evaluate both sides at the added edge `(h, c)`: LHS = False, RHS holds (right disjunct).
    have : (Spec.addEdge G h c) h c := Or.inr ⟨rfl, rfl⟩
    rw [← hr] at this; exact this
  intro hstep
  cases hstep with
  | gen hgen =>
      -- Every generative act adds an edge: its `result` is `G' = addEdge …`; but `G' = False`.
      cases hgen with
      | introduce h => exact hadd _ _ _ h.result
      | amplify h => exact hadd _ _ _ h.result
      | mint h => exact hadd _ _ _ h.result
      | endow h => exact hadd _ _ _ h.result
  | restrict hres =>
      -- Every restrictive act requires a HELD cap on the (empty) pre-graph — impossible.
      cases hres with
      | attenuate h => exact h.holds_cap
      | revoke h => exact h.holds_cap

/-- The abstract graph is fixed across a committed record step — the (A) conjunct of `recAbsStep`.
Together with `transfer_fires_no_authStep` this gives the full obstruction: the graph is fixed
but no no-op `AuthStep` exists. -/
theorem balance_turn_graph_is_fixed (k k' : RecordKernelState) (turn : Turn)
    (h : recKExec k turn = some k') :
    (recAbsOf k').authGraph = (recAbsOf k).authGraph := by
  simp only [recAbsOf]
  rw [(recKExec_frame k k' turn h).2]

/-! ## §6 — Axiom-hygiene tripwires. -/

#assert_axioms recAbsStep_forward
#assert_axioms recAbsStep_forward_exists
#assert_axioms recAbsStep_refines
#assert_axioms recAbsStep_run_forward
#assert_axioms recAbsStep_grounded
#assert_axioms recAbsStep_not_vacuous
#assert_axioms transfer_fires_no_authStep
#assert_axioms balance_turn_graph_is_fixed

/-! ## §7 — The authority-turn half + the union `AbsStep'`.

`Exec/AuthTurn.lean` provides `recKDelegate` (the executable generative delegation act) with
`recKDelegate_frame` (balance unchanged) and `recKDelegate_execGraph` (the cap-edit is
`Spec.addEdge`). Here we close the authority-turn forward-simulation square and union it with the
balance half into the complete single-cell LTS. -/

/-- **`authAbsStep consents a a'`** — the abstract LTS edge for an authority turn:

  * (C') `a'.balanceTotal = a.balanceTotal` — an authority turn moves no balance;
  * (A') `Spec.AuthStep consents a.authGraph a'.authGraph` — the authority graph genuinely steps.

This is the dual of `recAbsStep`: balance fixed, an `AuthStep` fires. -/
def authAbsStep (consents : Label → Prop) (a a' : AbstractState) : Prop :=
  -- (C') the balance domain is fixed (an authority turn is conservation-trivial).
  a'.balanceTotal = a.balanceTotal ∧
  -- (A') the authority graph genuinely steps via an authorized `Spec.AuthStep`.
  Spec.AuthStep (CellId := Label) (Rights := ExecRights) consents a.authGraph a'.authGraph

/-- **KEYSTONE — `authAbsStep_forward`.** Every committed `recKDelegate` is matched by
`authAbsStep`: (C') from `recKDelegate_frame`, (A') from a `Spec.Endow` whose `holds_source` is
`recKDelegate_grounds`, `nonAmplifying` is `confers_refl`, and `result` is
`recKDelegate_execGraph`. -/
theorem authAbsStep_forward (consents : Label → Prop)
    (k k' : RecordKernelState) (delegator recipient t : Label)
    (h : Exec.recKDelegate k delegator recipient t = some k') :
    authAbsStep consents (recAbsOf k) (recAbsOf k') := by
  -- The post-state's caps are the granted table; extract that equation.
  have hk' : k' = { k with caps := Exec.grant k.caps recipient (Authority.Cap.node t) } := by
    unfold Exec.recKDelegate at h
    by_cases hg : (k.caps delegator).any (fun cap => Exec.confersEdgeTo t cap) = true
    · rw [if_pos hg] at h; exact (Option.some.injEq _ _ ▸ h).symm
    · rw [if_neg hg] at h; exact absurd h (by simp)
  refine ⟨?_, ?_⟩
  · -- (C') the balance total is fixed (the DUAL frame).
    simp only [recAbsOf]
    exact (Exec.recKDelegate_frame k k' delegator recipient t h).1
  · -- (A') the authority graph fires a genuine `Endow` generative `AuthStep`.
    simp only [recAbsOf]
    -- `execGraph k'.caps = addEdge (execGraph k.caps) recipient ⟨t,()⟩` — the `Endow.result`.
    have hres : execGraph k'.caps
        = Spec.addEdge (execGraph k.caps) recipient (⟨t, ()⟩ : Spec.Cap Label ExecRights) := by
      rw [hk']
      exact Exec.recKDelegate_execGraph k.caps recipient t
    -- Build the `Endow`: parent = delegator, child = recipient, cap = source = ⟨t,()⟩.
    refine Spec.AuthStep.gen (Spec.GenAct.endow (parent := delegator) (child := recipient)
      (cap := ⟨t, ()⟩) (source := ⟨t, ()⟩) ?_)
    exact
      { holds_source := Exec.recKDelegate_grounds k k' delegator recipient t h
        nonAmplifying := Spec.confers_refl _
        result := hres }

/-! ### §7.1 — The union `AbsStep'` — the complete single-cell LTS. -/

/-- The complete single-cell abstract LTS edge: either a balance turn (`AbsStep`, authority fixed)
or an authority turn (`authAbsStep`, a genuine `AuthStep` fires with balance fixed). -/
def AbsStep' (consents : Label → Prop) (a a' : AbstractState) : Prop :=
  AbsStep a a' ∨ authAbsStep consents a a'

/-- A committed balance turn is matched by `AbsStep'` via the `AbsStep` disjunct. -/
theorem absStep'_forward_balance (consents : Label → Prop)
    (k k' : RecordKernelState) (turn : Turn) (h : recKExec k turn = some k') :
    AbsStep' consents (recAbsOf k) (recAbsOf k') :=
  Or.inl (recAbsStep_forward_exists k k' turn h)

/-- A committed authority turn is matched by `AbsStep'` via the `authAbsStep` disjunct. -/
theorem absStep'_forward_authority (consents : Label → Prop)
    (k k' : RecordKernelState) (delegator recipient t : Label)
    (h : Exec.recKDelegate k delegator recipient t = some k') :
    AbsStep' consents (recAbsOf k) (recAbsOf k') :=
  Or.inr (authAbsStep_forward consents k k' delegator recipient t h)

/-- Both executable transition kinds (balance via `recKExec`, authority via `recKDelegate`) are
matched by `AbsStep'`. The complete single-cell forward-simulation square. -/
theorem absStep'_forward (consents : Label → Prop) (k k' : RecordKernelState)
    (h : (∃ turn, recKExec k turn = some k') ∨
         (∃ delegator recipient t, Exec.recKDelegate k delegator recipient t = some k')) :
    AbsStep' consents (recAbsOf k) (recAbsOf k') := by
  rcases h with ⟨turn, hb⟩ | ⟨delegator, recipient, t, ha⟩
  · exact absStep'_forward_balance consents k k' turn hb
  · exact absStep'_forward_authority consents k k' delegator recipient t ha

/-! ### §7.2 — Non-vacuity of `authAbsStep`. -/

/-- `authAbsStep` entails the authority graph steps via a genuine `AuthStep`. -/
theorem authAbsStep_graph_steps {consents : Label → Prop} {a a' : AbstractState}
    (h : authAbsStep consents a a') :
    Spec.AuthStep (CellId := Label) (Rights := ExecRights) consents a.authGraph a'.authGraph :=
  h.2

/-- `authAbsStep` is not always-true: over the empty graph (held fixed) no `authAbsStep` holds,
because no `AuthStep G G` exists on the empty graph. The (A') conjunct is load-bearing. -/
theorem authAbsStep_not_vacuous (consents : Label → Prop) :
    ∃ a a' : AbstractState, ¬ authAbsStep consents a a' := by
  refine ⟨{ balanceTotal := 0, authGraph := fun _ _ => False },
          { balanceTotal := 0, authGraph := fun _ _ => False }, ?_⟩
  rintro ⟨_, hstep⟩
  exact transfer_fires_no_authStep consents hstep

/-! ## §7.3 — Axiom-hygiene tripwires. -/

#assert_axioms authAbsStep_forward
#assert_axioms absStep'_forward_balance
#assert_axioms absStep'_forward_authority
#assert_axioms absStep'_forward
#assert_axioms authAbsStep_graph_steps
#assert_axioms authAbsStep_not_vacuous

/-! ## §8 — Summary.

The single-cell operational LTS is complete:
  * balance turn (`recKExec`) → `recAbsStep` (authority fixed, conservation + grounding);
  * authority turn (`recKDelegate`) → `authAbsStep` (balance fixed, genuine `Endow`/`AuthStep`);
  * union `AbsStep'` matches both (`absStep'_forward`).
Non-vacuous (`recAbsStep_not_vacuous`, `authAbsStep_not_vacuous`), axiom-clean.

-- OPEN: the cross-cell / whole-history graph bookkeeping lifted to a multi-cell adversary model
--   (concurrent cells, an adversary scheduler) — the coinductive `Boundary` keystone. Not a gap
--   in the single-cell square; the next layer up.
-/

end Dregg2.Proof.LTS
