/-
# Metatheory.PolisAuthExecGraph — viability over the DEPLOYED authority executor's own graph.

`PolisAuthLive`/`PolisAuthAtlas` compute the delegation rule-base from a `Caps` and then EDIT that
`Caps` by hand to model a delegate/revoke. `PolisAuthExec` governs the deployed `Kernel.exec` — but
that executor only moves balance; it holds `caps` FIXED, so it can neither delegate nor revoke. This
file closes the op-set gap: viability is connectivity in the executor's OWN reconstructed authority
graph (`Dregg2.Spec.execGraph`, the graph `authorizedB` reads), and the cap-state changes are the
DEPLOYED authority turns `Dregg2.Exec.recKDelegate` / `recKRevokeTarget` — not a Lean-side edit.

The weld rides the executor's already-proven graph-change equalities:
  * `recKDelegate_execGraph` — a committed Granovetter delegation IS `Spec.addEdge` on `execGraph`;
  * `recKRevokeTarget_execGraph` — a target revocation IS `Spec.removeEdge` on `execGraph`;
  * `recKDelegate_grounds` — the delegation gate witnesses the source edge (`Spec.Endow.holds_source`).

So:
  * `delegate_unlocks_reach` / `exec_delegate_unlocks` — running the deployed delegate turn makes the
    recipient REACH the target in the executor's own graph (the added edge), no hand-edit.
  * `revoke_forecloses_reach` / `exec_revoke_forecloses` — running the deployed revoke turn FORECLOSES
    the holder (the removed edge), straight from `removeEdge`.
  * `reachGovGraph_refuses_revoke` — the polis governor SHIELDS the executor's foreclosing revoke
    (`genGovStep` over the reach floor), and `reachGovGraph_admits_delegate` passes the unlock.

The reachability is read from the SAME `execGraph` the deployed `authorizedB`/`exec` authorize
against, and every cap change is a real `recKDelegate`/`recKRevokeTarget` turn of the deployed
authority executor. No load-bearing `True`; non-vacuity is `decide`-checked on a concrete
2-cell graph.
-/
import Dregg2.Exec.AuthTurn
import Polis.PolisGovernorTheory

namespace Metatheory.PolisAuthExecGraph

open Dregg2.Exec
open Dregg2.Authority (Caps Cap Auth Label)
open Dregg2.Spec (execGraph addEdge removeEdge ExecRights)
open Metatheory.PolisGovernorTheory

/-! ## §1. Polis viability = connectivity in the deployed executor's authority graph. -/

/-- **`ReachesGraph caps b t`** — cell `b` can reach `t` iff it holds an edge to `t` in the
executor's OWN reconstructed authority graph `execGraph` (the graph `authorizedB` reads). This is
`Spec.Graph.has` of `execGraph` — viability over the deployed authority structure, not a hand-rolled
rule-base. -/
def ReachesGraph (caps : Caps) (b t : Label) : Prop := (execGraph caps).has b t

/-! ## §2. The deployed delegate turn UNLOCKS reach; the deployed revoke turn FORECLOSES it. -/

/-- **`delegate_unlocks_reach`.** When `delegator` holds an edge to `t` (the Granovetter gate),
copying its held `t`-cap to `recipient` — exactly what the deployed `recKDelegate` does on commit —
makes `recipient` reach `t` in the executor's graph. Rides `recKDelegate_execGraph` (the cap-edit IS
`addEdge`). -/
theorem delegate_unlocks_reach (caps : Caps) (delegator recipient t : Label)
    (hg : t = delegator ∨ (caps delegator).any (fun cap => confersEdgeTo t cap) = true) :
    ReachesGraph (grant caps recipient (delegatedCapTo caps delegator t)) recipient t := by
  refine ⟨(), ?_⟩
  rw [recKDelegate_execGraph caps delegator recipient t hg]
  exact Or.inr ⟨rfl, rfl⟩

/-- **`exec_delegate_unlocks`.** The same fact phrased over the deployed executor: a COMMITTED
`recKDelegate` turn leaves `recipient` reaching `t` in the post-state's authority graph. The gate is
discharged by the executor's own `recKDelegate_grounds` (the source edge held). -/
theorem exec_delegate_unlocks (k k' : RecordKernelState) (delegator recipient t : Label)
    (h : recKDelegate k delegator recipient t = some k') :
    ReachesGraph k'.caps recipient t := by
  -- ⚑ the gate is OWNER-OR-CONNECTIVITY as of the 2026-07-31 cutover; reach is unlocked on BOTH
  -- paths (the self path grants the implicit `Cap.node t`, which confers the edge just as a copied
  -- held cap does), so this governance conclusion is unchanged.
  have hg : t = delegator ∨ (k.caps delegator).any (fun cap => confersEdgeTo t cap) = true :=
    (recKDelegate_grounds k k' delegator recipient t h).imp id
      (fun hs => by rwa [execGraph_eq_any] at hs)
  have h2 : k' = { k with caps := grant k.caps recipient (delegatedCapTo k.caps delegator t) } := by
    unfold recKDelegate at h; rw [if_pos hg] at h; exact (Option.some.inj h).symm
  rw [h2]; exact delegate_unlocks_reach k.caps delegator recipient t hg

/-- **`revoke_forecloses_reach`.** Filtering out every `t`-conferring cap from `holder` — exactly the
deployed `recKRevokeTarget` cap-edit — leaves `holder` UNABLE to reach `t` in the executor's graph.
Rides `recKRevokeTarget_execGraph` (the cap-edit IS `removeEdge`), which kills the `holder ⟶ t`
edge outright. -/
theorem revoke_forecloses_reach (caps : Caps) (holder t : Label) :
    ¬ ReachesGraph
        (fun l => if l = holder then (caps l).filter (fun cap => ¬ confersEdgeTo t cap) else caps l)
        holder t := by
  rintro ⟨r, hr⟩
  rw [recKRevokeTarget_execGraph caps holder t] at hr
  cases r
  exact hr.2 ⟨rfl, rfl⟩

/-- **`exec_revoke_forecloses`.** The same over the deployed executor: after a `recKRevokeTarget`
turn (which always commits), the holder no longer reaches the revoked target in the post-state's
authority graph. -/
theorem exec_revoke_forecloses (k : RecordKernelState) (holder t : Label) :
    ¬ ReachesGraph (recKRevokeTarget k holder t).caps holder t := by
  have hcaps : (recKRevokeTarget k holder t).caps
      = fun l => if l = holder then (k.caps l).filter (fun cap => ¬ confersEdgeTo t cap)
                 else k.caps l := rfl
  rw [hcaps]; exact revoke_forecloses_reach k.caps holder t

/-! ## §3. The polis governor over the deployed-executor reach floor. -/

open Classical in
noncomputable instance instDecReachesGraph (b t : Label) :
    DecidablePred (fun c => ReachesGraph c b t) := fun _ => Classical.propDecidable _

/-- The governor over the reach floor: admit the executor's proposed next cap-state iff agent `b`
still reaches `t` in its authority graph, else SHIELD (keep the prior caps). `genGovStep` over
`ReachesGraph · b t`. -/
noncomputable def reachGovGraph (b t : Label) (caps caps' : Caps) : Caps :=
  genGovStep (fun c => ReachesGraph c b t) (fun _ c' => c') caps caps'

/-- **`reachGovGraph_refuses_revoke`.** The polis SHIELDS the deployed revoke turn that forecloses
the holder: `recKRevokeTarget` breaks the reach floor (`exec_revoke_forecloses`), so the governor
keeps the prior cap-state. Foreclosure by a real executor revoke is refused. -/
theorem reachGovGraph_refuses_revoke (k : RecordKernelState) (holder t : Label) (caps : Caps) :
    reachGovGraph holder t caps (recKRevokeTarget k holder t).caps = caps := by
  unfold reachGovGraph genGovStep
  rw [if_neg (exec_revoke_forecloses k holder t)]

/-- **`reachGovGraph_admits_delegate`.** The polis PASSES the deployed delegate turn that keeps the
recipient viable: a committed `recKDelegate` leaves `recipient` reaching `t`
(`exec_delegate_unlocks`), so the governor admits the executor's proposed cap-state unchanged. -/
theorem reachGovGraph_admits_delegate (k k' : RecordKernelState) (recipient t : Label)
    (delegator : Label) (caps : Caps) (h : recKDelegate k delegator recipient t = some k') :
    reachGovGraph recipient t caps k'.caps = k'.caps := by
  unfold reachGovGraph genGovStep
  rw [if_pos (exec_delegate_unlocks k k' delegator recipient t h)]

/-! ## §4. Concrete non-vacuity — a 2-cell graph, decided on the engine. -/

def A : Label := 0
def B : Label := 1
def C : Label := 2

/-- `A` holds a `node` cap to `B` (an edge `A ⟶ B`); `C` holds nothing. -/
def capsA : Caps := fun s => if s = A then [Cap.node B] else []

/-- `A` reaches `B` directly (the held `node B` cap is the edge). -/
theorem A_reaches_B : ReachesGraph capsA A B := by
  refine ⟨(), ?_⟩; rw [execGraph_eq_any]; decide

/-- BEFORE delegation, `C` does NOT reach `B` (it holds no edge). -/
theorem C_not_reaches_B : ¬ ReachesGraph capsA C B := by
  rintro ⟨r, hr⟩; cases r; rw [execGraph_eq_any] at hr; exact absurd hr (by decide)

/-- `A` holds the edge to `B`, so the deployed delegation gate fires (non-vacuous premise). -/
theorem capsA_gate : (capsA A).any (fun cap => confersEdgeTo B cap) = true := by decide

/-- **AFTER the deployed delegate turn `A ▸ C` of `B`, `C` reaches `B`** — the unlock is the
executor's own `addEdge`, run on the real cap-state, not a hand-edit. -/
theorem C_reaches_B_after_delegate :
    ReachesGraph (grant capsA C (delegatedCapTo capsA A B)) C B :=
  delegate_unlocks_reach capsA A C B (Or.inr capsA_gate)

/-- **AFTER the deployed revoke turn on `A`'s edge to `B`, `A` no longer reaches `B`** — the executor's
own `removeEdge`. -/
theorem A_foreclosed_after_revoke :
    ¬ ReachesGraph
        (fun l => if l = A then (capsA l).filter (fun cap => ¬ confersEdgeTo B cap) else capsA l)
        A B :=
  revoke_forecloses_reach capsA A B

/-! ## §5. Axiom hygiene. -/

#print axioms delegate_unlocks_reach
#print axioms exec_delegate_unlocks
#print axioms revoke_forecloses_reach
#print axioms exec_revoke_forecloses
#print axioms reachGovGraph_refuses_revoke
#print axioms C_reaches_B_after_delegate

/-!
Viability over the deployed authority executor, in one breath:

  1. `ReachesGraph caps b t := (execGraph caps).has b t` — connectivity in the executor's OWN
     reconstructed authority graph (the one `authorizedB` reads).
  2. `exec_delegate_unlocks` / `exec_revoke_forecloses` — running the DEPLOYED `recKDelegate` /
     `recKRevokeTarget` turn unlocks / forecloses reach, via the executor's proven `addEdge` /
     `removeEdge` graph-change equalities — no hand-edited `Caps`.
  3. `reachGovGraph_refuses_revoke` / `_admits_delegate` — the polis governor shields the foreclosing
     executor revoke and passes the viability-preserving executor delegate.
-/

end Metatheory.PolisAuthExecGraph
