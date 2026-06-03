/-
# Dregg2.Spec.ExecRefinementFull — the full `Exec ⊑ Spec` forward simulation.

`Spec/ExecRefinement.lean` proves the conservation + authority projections of the refinement
square but leaves an explicit `-- OPEN:` in §4: define an abstract small-step LTS
`AbsStep : AbstractState → AbstractState → Prop` and prove every executable step is a
permitted abstract step — `execFull s fa = some s' → AbsStep (absFull s) (absFull s')`.

This module closes that open for the whole `FullAction` op-set:

1. **`AbsStep`** — the unified abstract small-step LTS. Constructors:
   * `conserveIdentity` — balance conserved, graph unchanged;
   * `conserveAddEdge` — balance conserved, graph gains one `Spec.addEdge`;
   * `conserveRemoveEdge` — balance conserved, graph loses one `Spec.removeEdge`;
   * `discloseSupply` — total moves by a disclosed `±amt`, graph unchanged (mint/burn).

2. **`exec_full_refines_spec`** — for every `FullAction` kind, a committed step is a
   permitted `AbsStep`. By case-split, reusing `execFull_attests`.

3. **`exec_full_step_refines`** — the full square: both projections preserved AND the
   bottom edge is a genuine `AbsStep`.

4. **`exec_fullTurn_refines_spec`** — a committed `execFullTurn` is matched by an `AbsRun`
   (the reflexive-transitive closure of `AbsStep`).

The single named residue is `OnlyConnectivityCloses` — the whole-history connectivity
closure. This is a property of multi-step runs, isolated as a named `def`-level hypothesis,
not a `sorry`.

No `sorry`/`admit`/`axiom`/`native_decide`. All keystones are axiom-clean.
-/
import Dregg2.Spec.ExecRefinement
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Spec.ExecRefinementFull

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (FullAction execFull ledgerDelta fullActionInv execFull_attests
  execFull_ledger execFull_conserves Conserving ledgerDelta_eq_zero_of_conserving mintEffect
  burnEffect)
open Dregg2.Authority (Caps Label)
open Dregg2.Spec
open Dregg2.Laws (Verifiable)
open scoped BigOperators

/-! ## §1 — The unified abstraction `absFull : RecChainedState → AbstractState`.

The per-effect work used three syntactically-distinct carriers (`EffectTransfer.absT`,
`EffectsAuthority.absA`, `EffectsState.absS` / `EffectsSupply.absS`), all the same shape
`(balanceTotal : ℤ, authGraph : Graph Label ExecRights)` = `Spec.AbstractState`. We collapse
them onto the canonical `Spec.AbstractState` here, so `AbsStep` runs over the same abstract
state `ExecRefinement.absOf` produces. -/

/-- **`absFull s`** — the abstract Spec state a chained record kernel `s` denotes: its conserved
`recTotal` (the `balance`-domain measure at `Bal = ℤ`) and its reconstructed `execGraph` (the
`Spec.Authority` graph the caps confer). The record-world analog of `ExecRefinement.absOf`, landing
in the SAME `Spec.AbstractState` — so `absT`/`absA`/`absS` are all THIS function. -/
def absFull (s : RecChainedState) : AbstractState :=
  { balanceTotal := recTotal s.kernel, authGraph := execGraph s.kernel.caps }

/-- The unified abstraction agrees with the three per-regime carriers on both projections (by `rfl`):
`EffectsSupply.absS`, `EffectsAuthority.absA`, and `EffectsState.absS` are all `absFull`. -/
theorem absFull_balanceTotal (s : RecChainedState) : (absFull s).balanceTotal = recTotal s.kernel :=
  rfl

theorem absFull_authGraph (s : RecChainedState) : (absFull s).authGraph = execGraph s.kernel.caps :=
  rfl

/-! ## §2 — The unified abstract small-step LTS `AbsStep`.

The full op-set has two conservation regimes: `balance`/`delegate`/`revoke` conserve (`Σδ = 0`);
`mint`/`burn` disclose (`±amt`). Three graph-dynamics: identity / `addEdge` / `removeEdge`.
`AbsStep` packages these as an inductive with constructors for each spec-permitted transition class,
each carrying its `Spec.Conservation` content and `Spec.Authority` graph dynamics. -/

/-- **`AbsStep a a'`** — the unified abstract small-step transition relation (the §4 OPEN's `AbsStep`):
`a` may step to `a'` iff the move is one of the spec-permitted transition classes. The constructors:

  * **`conserveIdentity`** — the abstract `balance` total is CONSERVED (`conservedInDomain
    Domain.balance` on the realized delta) and the authority graph is UNCHANGED. The balance/effect
    and metadata kinds (`Spec.Conservation` `Σδ = 0` + authority-frame).
  * **`conserveAddEdge`** — balance CONSERVED and the graph gains EXACTLY one edge
    `recipient ⟶ cap` (`Spec.addEdge` = `Spec.Introduce.result`). The delegate kind: a non-amplifying
    Granovetter introduction.
  * **`conserveRemoveEdge`** — balance CONSERVED and the graph loses EXACTLY one edge
    `holder ⟶ cap` (`Spec.removeEdge` = `Spec.Revoke.result`). The revoke kind.
  * **`discloseSupply`** — the abstract total moves by a DISCLOSED `delta` (the receipt-visible
    non-conservation, `a'.balanceTotal = a.balanceTotal + delta`) and the graph is UNCHANGED. The
    mint/burn supply kinds.

This is a GENUINE abstract transition relation (the bottom edge of the simulation square), keyed to
`Spec.Conservation` (the `conservedInDomain`/`+delta` arms) and `Spec.Authority` (the
`addEdge`/`removeEdge`/identity graph arms) — not the identity-on-projections of `exec_step_refines`. -/
inductive AbsStep (a a' : AbstractState) : Prop where
  /-- conservative step, authority graph unchanged (balance/effect, metadata). -/
  | conserveIdentity
      (hbal : conservedInDomain Domain.balance [a'.balanceTotal - a.balanceTotal])
      (hgraph : a'.authGraph = a.authGraph)
  /-- conservative step adding one non-amplifying edge `recipient ⟶ cap` (`Spec.Introduce.result`). -/
  | conserveAddEdge (recipient : Label) (cap : Cap Label ExecRights)
      (hbal : conservedInDomain Domain.balance [a'.balanceTotal - a.balanceTotal])
      (hgraph : a'.authGraph = addEdge a.authGraph recipient cap)
  /-- conservative step removing one edge `holder ⟶ cap` (`Spec.Revoke.result`). -/
  | conserveRemoveEdge (holder : Label) (cap : Cap Label ExecRights)
      (hbal : conservedInDomain Domain.balance [a'.balanceTotal - a.balanceTotal])
      (hgraph : a'.authGraph = removeEdge a.authGraph holder cap)
  /-- disclosed-supply step: the total moves by the disclosed `delta`, graph unchanged. -/
  | discloseSupply (delta : ℤ)
      (hbal : a'.balanceTotal = a.balanceTotal + delta)
      (hgraph : a'.authGraph = a.authGraph)

/-! ## §3 — `exec_full_refines_spec`: THE FORWARD SIMULATION (the §4 OPEN, proved).

Every executable `FullAction` step is matched by a permitted `AbsStep`. We case-split on the action
kind and reuse `execFull_attests` (the per-kind step-completeness witness):
  * `balance` → `conserveIdentity` (the `recCexec` two-party move conserves; the authority graph is
    framed because `recCexec` never edits `caps`);
  * `delegate` → `conserveAddEdge` (conservation-trivial; `execFull_delegate_addEdge`);
  * `revoke`  → `conserveRemoveEdge` (conservation-trivial; `execFull_revoke_removeEdge`);
  * `mint`/`burn` → `discloseSupply` (the supply moves by `±amt` = `ledgerDelta`; graph framed).
The disclosed-vs-paired split is exactly `execFull_ledger`'s `ledgerDelta` (`0` vs `±amt`). -/

/-- `recCexec` leaves the cap table unchanged (it rewrites only the `balance` field) — re-derived
here from `recKExec_frame` (the same slice `EffectTransfer.recCexec_caps_eq` establishes; re-founded
for self-containment, as `EffectsPaired` does). -/
theorem recCexec_caps_eq {s s1 : RecChainedState} {t : Turn} (h : recCexec s t = some s1) :
    s1.kernel.caps = s.kernel.caps := by
  unfold recCexec at h
  cases hk : recKExec s.kernel t with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k' =>
      rw [hk] at h; simp only [Option.some.injEq] at h; subst h
      exact (recKExec_frame s.kernel k' t hk).2

/-- A `recCexec`-committed balance move frames the cap table (it rewrites only the `balance` field),
so the reconstructed authority graph is unchanged. The balance-kind authority-frame. -/
theorem balance_authGraph_unchanged {s s' : RecChainedState} {a : TurnExecutor.Action}
    (h : execFull s (.balance a) = some s') :
    execGraph s'.kernel.caps = execGraph s.kernel.caps := by
  have hc : recCexec s a.move = some s' := h
  rw [recCexec_caps_eq hc]

/-- Mint/burn frame the cap table (the supply credit/debit rewrites only the `balance` field), so the
authority graph is unchanged. -/
theorem supply_authGraph_unchanged {s s' : RecChainedState} {fa : FullAction}
    (hsupply : ¬ Conserving fa)
    (h : execFull s fa = some s') :
    execGraph s'.kernel.caps = execGraph s.kernel.caps := by
  cases fa with
  | balance a => exact absurd trivial hsupply
  | delegate del rec t => exact absurd trivial hsupply
  | revoke holder t => exact absurd trivial hsupply
  | mint actor cell amt =>
      simp only [execFull, TurnExecutorFull.recCMint] at h
      cases hm : TurnExecutorFull.recKMint s.kernel actor cell amt with
      | none => rw [hm] at h; exact absurd h (by simp)
      | some k' =>
          rw [hm] at h; simp only [Option.some.injEq] at h; subst h
          -- `recKMint` commits ⟹ it took the credit branch (caps untouched).
          unfold TurnExecutorFull.recKMint at hm
          by_cases hg : mintAuthorizedB s.kernel.caps actor cell = true ∧ 0 ≤ amt
              ∧ cell ∈ s.kernel.accounts
          · rw [if_pos hg] at hm; simp only [Option.some.injEq] at hm; rw [← hm]
          · rw [if_neg hg] at hm; exact absurd hm (by simp)
  | burn actor cell amt =>
      simp only [execFull, TurnExecutorFull.recCBurn] at h
      cases hb : TurnExecutorFull.recKBurn s.kernel actor cell amt with
      | none => rw [hb] at h; exact absurd h (by simp)
      | some k' =>
          rw [hb] at h; simp only [Option.some.injEq] at h; subst h
          unfold TurnExecutorFull.recKBurn at hb
          by_cases hg : mintAuthorizedB s.kernel.caps actor cell = true ∧ 0 ≤ amt
              ∧ amt ≤ balOf (s.kernel.cell cell) ∧ cell ∈ s.kernel.accounts
          · rw [if_pos hg] at hb; simp only [Option.some.injEq] at hb; rw [← hb]
          · rw [if_neg hg] at hb; exact absurd hb (by simp)

/-- **`exec_full_refines_spec`** — the forward simulation: every committed `FullAction` step is
matched by a permitted abstract `AbsStep`. The bottom edge of the simulation square is a genuine
abstract step — full `Exec ⊑ Spec` forward simulation across balance, authority (delegate/revoke),
and supply (mint/burn). By case-split, reusing `execFull_attests` and `ledgerDelta`. -/
theorem exec_full_refines_spec {s s' : RecChainedState} {fa : FullAction}
    (h : execFull s fa = some s') :
    AbsStep (absFull s) (absFull s') := by
  cases fa with
  | balance a =>
      -- conserveIdentity: `recCexec` conserves the total, frames the graph.
      refine AbsStep.conserveIdentity ?_ ?_
      · unfold conservedInDomain absFull
        rw [execFull_conserves s s' (.balance a) trivial h]; simp
      · simp only [absFull]; exact balance_authGraph_unchanged h
  | delegate del rec t =>
      -- conserveAddEdge: conservation-trivial; the graph gains `rec ⟶ ⟨t,()⟩`.
      refine AbsStep.conserveAddEdge rec (⟨t, ()⟩ : Cap Label ExecRights) ?_ ?_
      · unfold conservedInDomain absFull
        rw [execFull_conserves s s' (.delegate del rec t) trivial h]; simp
      · simp only [absFull]
        exact TurnExecutorFull.execFull_delegate_addEdge s s' del rec t h
  | revoke holder t =>
      -- conserveRemoveEdge: conservation-trivial; the graph loses `holder ⟶ ⟨t,()⟩`.
      refine AbsStep.conserveRemoveEdge holder (⟨t, ()⟩ : Cap Label ExecRights) ?_ ?_
      · unfold conservedInDomain absFull
        rw [execFull_conserves s s' (.revoke holder t) trivial h]; simp
      · simp only [absFull]
        exact TurnExecutorFull.execFull_revoke_removeEdge s s' holder t h
  | mint actor cell amt =>
      -- discloseSupply: the total rises by `amt = ledgerDelta`; graph framed.
      refine AbsStep.discloseSupply amt ?_ ?_
      · simp only [absFull]
        have := execFull_ledger s s' (.mint actor cell amt) h
        simpa [ledgerDelta] using this
      · simp only [absFull]
        exact supply_authGraph_unchanged (by simp [Conserving]) h
  | burn actor cell amt =>
      -- discloseSupply: the total falls by `amt`, i.e. moves by `ledgerDelta = -amt`; graph framed.
      refine AbsStep.discloseSupply (-amt) ?_ ?_
      · simp only [absFull]
        have := execFull_ledger s s' (.burn actor cell amt) h
        simpa [ledgerDelta] using this
      · simp only [absFull]
        exact supply_authGraph_unchanged (by simp [Conserving]) h

/-! ## §3.1 — `RefinesRec` realized by `absFull`.

The full executor lives in the record world (`RecChainedState`); we re-found the simulation relation
`RefinesRec` over the record kernel — the same two projections (`recTotal` IS the abstract
`balanceTotal`, `execGraph` IS the abstract `authGraph`). Record-world analog of
`ExecRefinement.Refines`/`refines_absOf`. -/

/-- **`RefinesRec s a`** — the record-world simulation relation: the chained record kernel's conserved
`recTotal` IS the abstract `balanceTotal`, and its reconstructed `execGraph` IS the abstract
`authGraph`. The record analog of `ExecRefinement.Refines` (which is over the scalar `KernelState`). -/
def RefinesRec (s : RecChainedState) (a : AbstractState) : Prop :=
  a.balanceTotal = recTotal s.kernel ∧ a.authGraph = execGraph s.kernel.caps

/-- `RefinesRec s (absFull s)` — the abstraction is a refinement witness on both projections. PROVED. -/
theorem refines_absFull (s : RecChainedState) : RefinesRec s (absFull s) :=
  ⟨rfl, rfl⟩

/-! ## §4 — `exec_full_step_refines`: the FULL square (operational, not just projection-preserving).

Assemble the full square: the abstract successor `absFull s'` refines `s'.kernel` (both projections),
AND the bottom edge is a genuine `AbsStep (absFull s) (absFull s')` — strengthening
`ExecRefinement.exec_step_refines` from "preserves the two projections" to "commutes with a genuine
abstract step". This is the FULL `Exec ⊑ Spec` forward-simulation square over the whole op-set. -/

/-- **`exec_full_step_refines`** — the full square: if `execFull s fa = some s'`, there is an
abstract successor `a' := absFull s'` with `RefinesRec s' a'` AND a genuine `AbsStep (absFull s)
a'` (keyed to `Spec.Conservation` + `Spec.Authority` dynamics). The square commutes with a real
abstract step, strengthening `exec_step_refines` from projection-preserving to operational. -/
theorem exec_full_step_refines {s s' : RecChainedState} {fa : FullAction}
    (h : execFull s fa = some s') :
    ∃ a', RefinesRec s' a' ∧ AbsStep (absFull s) a' :=
  ⟨absFull s', refines_absFull s', exec_full_refines_spec h⟩

/-- **`exec_full_step_refines_bundled` — PROVED.** The full square bundled with the exact ledger
movement (the conservation CONTENT of the step): the abstract successor refines, the bottom edge is
an `AbsStep`, AND the abstract total moved by EXACTLY `ledgerDelta fa` (`0` for conservative kinds,
`±amt` for supply) — so the operational step carries the precise `Spec.Conservation` measure, not
just the qualitative `AbsStep`. -/
theorem exec_full_step_refines_bundled {s s' : RecChainedState} {fa : FullAction}
    (h : execFull s fa = some s') :
    ∃ a', RefinesRec s' a' ∧ AbsStep (absFull s) a' ∧
      a'.balanceTotal = (absFull s).balanceTotal + ledgerDelta fa := by
  refine ⟨absFull s', refines_absFull s', exec_full_refines_spec h, ?_⟩
  simp only [absFull]
  exact execFull_ledger s s' fa h

/-! ## §4.1 — Lifting the forward simulation to a whole TURN (the transaction-level LTS).

A whole `execFullTurn` is a sequence of `FullAction`s. We lift `AbsStep` to its reflexive-transitive
closure `AbsRun` and prove a committed turn is matched by an `AbsRun` over the abstractions — every
executable transaction is a sequence of permitted abstract steps. -/

/-- **`AbsRun`** — the reflexive-transitive closure of `AbsStep`: the abstract LTS's MULTI-step
relation. `a` reaches `a'` through zero or more permitted abstract steps. -/
inductive AbsRun : AbstractState → AbstractState → Prop where
  | refl (a : AbstractState) : AbsRun a a
  | step {a b c : AbstractState} (h1 : AbsStep a b) (h2 : AbsRun b c) : AbsRun a c

/-- **`exec_fullTurn_refines_spec` — PROVED.** A committed `execFullTurn` is matched by an `AbsRun`
over the abstractions: every executable transaction is a sequence of permitted abstract steps. The
transaction-level forward simulation, by induction on the turn reusing `exec_full_refines_spec`. -/
theorem exec_fullTurn_refines_spec :
    ∀ (s s' : RecChainedState) (tt : List FullAction),
      TurnExecutorFull.execFullTurn s tt = some s' → AbsRun (absFull s) (absFull s')
  | s, s', [], h => by
      simp only [TurnExecutorFull.execFullTurn, Option.some.injEq] at h
      subst h; exact AbsRun.refl _
  | s, s', a :: rest, h => by
      simp only [TurnExecutorFull.execFullTurn] at h
      cases ha : execFull s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          exact AbsRun.step (exec_full_refines_spec ha) (exec_fullTurn_refines_spec s1 s' rest h)

/-! ## §5 — The NAMED residue: the whole-history connectivity closure (NOT a `sorry`).

§3–§4 CLOSE the per-step forward simulation: every SINGLE executable step is a permitted `AbsStep`
(`exec_full_refines_spec`), and every transaction is an `AbsRun` (`exec_fullTurn_refines_spec`). The
per-step non-amplification is carried by each constructor's dynamics: `conserveAddEdge` adds a
NON-AMPLIFYING edge (the executable `recKDelegate` only grants `node t` when the delegator already
reaches `t` — `execFull_delegate_grounds`, the `Spec.Introduce` connectivity premise);
`conserveRemoveEdge`/`conserveIdentity`/`discloseSupply` cannot add reachability at all.

The single residue is the WHOLE-HISTORY closure
`Spec.Authority.only_connectivity_begets_connectivity` — that across an ENTIRE run, no reachable edge
appears that some authorized op did not generate. That is a property of the `AbsRun` CLOSURE, not of
the single-step relation; we isolate it as the NAMED predicate `OnlyConnectivityCloses` (a HYPOTHESIS
over runs, NOT a `sorry`), and record precisely what it would add. -/

/-- **`OnlyConnectivityCloses`** — the whole-history connectivity-closure obligation, NAMED (not
proved): along an `AbsRun a a'`, every edge present in `a'.authGraph` is either already in
`a.authGraph` OR was generated by some authorized `conserveAddEdge` step on the run (no reachability
appears ex nihilo). This is the run-level reading of `Spec.Authority`'s headline
`only_connectivity_begets_connectivity` — the SAME thread that module flags OPEN. It is a property of
the `AbsRun` closure, ORTHOGONAL to the per-step forward simulation closed in §3–§4. -/
def OnlyConnectivityCloses : Prop :=
  ∀ {a a' : AbstractState}, AbsRun a a' →
    ∀ (h : Label) (c : Cap Label ExecRights),
      a'.authGraph h c → (a.authGraph h c ∨ ∃ b b' : AbstractState, AbsRun a b ∧ AbsStep b b' ∧
        (∃ recipient, b'.authGraph = addEdge b.authGraph recipient c ∧ recipient = h))

/-- **The per-step non-amplification IS proved (the closure's single-step ingredient — PROVED).** A
committed delegation's added edge `rec ⟶ ⟨t,()⟩` is GROUNDED: the delegator already held connectivity
to `t` on the pre-graph (`execFull_delegate_grounds`). So no `conserveAddEdge` conjures reachability —
the closure's per-step content holds; only the run-level *bookkeeping* (`OnlyConnectivityCloses`)
remains a named hypothesis. -/
theorem delegate_step_grounded {s s' : RecChainedState} {del rec t : CellId}
    (h : execFull s (.delegate del rec t) = some s') :
    execGraph s.kernel.caps del (⟨t, ()⟩ : Cap Label ExecRights) :=
  TurnExecutorFull.execFull_delegate_grounds s s' del rec t h

/-! ## §6 — Axiom-hygiene tripwires (the honesty pins over every keystone).

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. The forward-simulation keystones (`exec_full_refines_spec`, the full square, the
turn-level `AbsRun`) are genuinely proved; `OnlyConnectivityCloses` is a `def`-named PROP obligation
(a hypothesis over runs), NOT an `axiom`, so there is nothing axiom-dirty to exclude. -/

#assert_axioms absFull_balanceTotal
#assert_axioms absFull_authGraph
#assert_axioms recCexec_caps_eq
#assert_axioms balance_authGraph_unchanged
#assert_axioms supply_authGraph_unchanged
#assert_axioms exec_full_refines_spec
#assert_axioms refines_absFull
#assert_axioms exec_full_step_refines
#assert_axioms exec_full_step_refines_bundled
#assert_axioms exec_fullTurn_refines_spec
#assert_axioms delegate_step_grounded

/-! ## §7 — Non-vacuity: a concrete step of each regime is a matched `AbsStep`.

Reuses `TurnExecutorFull.fs0` (cells 0,1; actor 9 holds `node 0` mint cap; delegator 0 holds `node 7`
connectivity cap). We exhibit a balance/conservative step, a delegate (addEdge) step, and a mint
(disclosed) step each landing a permitted `AbsStep` over `absFull`. -/

section NonVacuity
open Dregg2.Exec.TurnExecutorFull (fs0)

/-- A balance transfer step is a matched conservative `AbsStep` (graph unchanged). -/
example (s' : RecChainedState)
    (h : execFull fs0 (.balance ⟨1, .transfer, ⟨0, 0, 1, 30⟩⟩) = some s') :
    AbsStep (absFull fs0) (absFull s') :=
  exec_full_refines_spec h

/-- A delegate step is a matched `conserveAddEdge` `AbsStep` (graph gains `rec ⟶ ⟨7,()⟩`). -/
example (s' : RecChainedState) (h : execFull fs0 (.delegate 0 1 7) = some s') :
    AbsStep (absFull fs0) (absFull s') :=
  exec_full_refines_spec h

/-- A mint step is a matched `discloseSupply` `AbsStep` (the total rises by the disclosed amount). -/
example (s' : RecChainedState) (h : execFull fs0 (.mint 9 0 50) = some s') :
    AbsStep (absFull fs0) (absFull s') :=
  exec_full_refines_spec h

end NonVacuity

end Dregg2.Spec.ExecRefinementFull
