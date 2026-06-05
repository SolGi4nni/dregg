/-
# Dregg2.Exec.AuthTurn — the authority-mutating executable kernel transition.

`recKExec` is a balance turn: it rewrites `balance` and preserves `caps`, holding the authority
graph fixed. This module builds the dual — an authority-mutating kernel that edits `caps` (a
Granovetter delegate or a revoke) rather than the balance field — and proves:
  * the dual frame: `recTotal` is unchanged by an authority turn (conservation-trivial);
  * the graph-change equalities: the cap-edit IS `Spec.addEdge`/`removeEdge` on `execGraph`,
    making the cap-edit's abstract image a `Spec.AuthStep`.

Why `execGraph` matches: rights are abstracted to `ExecRights = Unit` (connectivity skeleton), so a
`Spec.Cap Label ExecRights` is determined by its target (`c = ⟨t, ()⟩ ↔ c.target = t`). Hence
granting any held concrete cap that confers an edge to `t` IS `addEdge … ⟨t,()⟩`, and revoking all
`t`-conferring caps IS `removeEdge … ⟨t,()⟩` — i.e. `Spec.Introduce.result` / `Spec.Revoke.result`
verbatim, without upgrading concrete endpoint rights into control.

No `axiom`/`admit`/`native_decide`/`sorry`. Reuses `Exec/Caps.lean`, `Spec.Authority`, and
`Spec.ExecRefinement.execGraph`.
-/
import Dregg2.Exec.RecordKernel
import Dregg2.Exec.Caps
import Dregg2.Spec.ExecRefinement
import Dregg2.Spec.Authority

namespace Dregg2.Exec

open Dregg2.Authority (Caps Cap Auth Label)
open Dregg2.Spec (execGraph ExecRights addEdge removeEdge)

/-! ## §1 — The per-cap edge predicate `execGraph` reads, named. -/

/-- Does `cap` confer a connectivity edge to target `t`? A `node t` cap, or an `endpoint t`-
carrying-`write` cap. This is exactly `execGraph`'s `.any` body — the per-cap test the reconstructed
graph reads. -/
def confersEdgeTo (t : Label) (cap : Cap) : Bool :=
  (cap == Cap.node t) ||
  (match cap with
   | .endpoint t' rights => (t' == t) && rights.contains Auth.write
   | _ => false)

/-- `execGraph` unfolded through `confersEdgeTo`: the Spec edge `h ⟶ c` is present iff some cap in
`h`'s slot `confersEdgeTo c.target`. A bridge for graph-change proofs. -/
theorem execGraph_eq_any (caps : Caps) (h : Label) (c : Spec.Cap Label ExecRights) :
    execGraph caps h c = ((caps h).any (fun cap => confersEdgeTo c.target cap) = true) := rfl

/-! ## §2 — `ExecRights = Unit`: a Spec cap is determined by its target.

The graph carrier abstracts rights to `Unit`, so `⟨t, ()⟩` is the unique Spec cap to `t`, making
`c = ⟨t,()⟩ ↔ c.target = t` and collapsing the cap-edit's effect to a single `addEdge`/`removeEdge`
on the Spec edge `⟨t,()⟩`. -/

/-- `c = ⟨t, ()⟩ ↔ c.target = t` (the rights component is `Unit`, hence always `()`). -/
theorem specCap_eq_iff_target (c : Spec.Cap Label ExecRights) (t : Label) :
    c = ⟨t, ()⟩ ↔ c.target = t := by
  constructor
  · intro h; rw [h]
  · intro h
    obtain ⟨ct, cr⟩ := c
    cases cr
    simp only at h
    subst h
    rfl

/-! ## §3 — `recKDelegate` — the executable Granovetter delegation.

Edits `caps` and leaves the `cell`/balance state untouched. Fail-closed: gates on the delegator
already holding connectivity to `t` — "only connectivity begets connectivity" (the Granovetter
`Introduce` premise). On commit it copies the concrete held cap that witnesses the premise, rather
than manufacturing a fresh `node t` control cap. -/

/-- The introducer's held cap conferring an edge to `t` (executable `lookup_by_target`): the first
cap in `h`'s slot that `confersEdgeTo t`, or `Cap.null` if none. -/
def heldCapTo (caps : Caps) (h t : Label) : Cap :=
  ((caps h).find? (fun cap => confersEdgeTo t cap)).getD Cap.null

/-- The executable authority turn: `delegator` copies to `recipient` the concrete cap it already
holds that confers an edge to `t`. Commits only when the delegator already holds such a cap
(Granovetter connectivity premise); on commit rewrites only `caps`, leaving every balance intact.
This preserves the abstract `addEdge` behavior while avoiding rights amplification. -/
def recKDelegate (k : RecordKernelState) (delegator recipient t : Label) :
    Option RecordKernelState :=
  -- The delegator must already hold a cap conferring an edge to `t` (`Spec.Endow.holds_source`).
  if (k.caps delegator).any (fun cap => confersEdgeTo t cap) = true then
    some { k with caps := grant k.caps recipient (heldCapTo k.caps delegator t) }
  else
    none

/-! ### §3.RIGHTS — The attenuating delegation (the genuine `is_attenuation` mirror).

`recKDelegate` copies the witness cap unchanged. `recKDelegateAtten` is the explicitly attenuating
variant: locate the held cap, attenuate to `keep`, and grant the attenuated cap. The granted cap's
conferred rights are `⊆` the held cap's (`attenuate_confRights_le`) — the genuine `granted.rights ≤
held.rights` over `ExecAuth`, not a `()≤()` collapse. -/

/-- The rights-carrying Granovetter delegation (faithful `apply_introduce`): on commit, grant
`recipient` the delegator's held cap to `t` attenuated to `keep`. The granted cap carries real
rights `⊆` the held cap's (`attenuate_confRights_le`). Fail-closed: no held cap to `t` ⇒ none. -/
def recKDelegateAtten (k : RecordKernelState) (delegator recipient t : Label) (keep : List Auth) :
    Option RecordKernelState :=
  if (k.caps delegator).any (fun cap => confersEdgeTo t cap) = true then
    some { k with caps := grant k.caps recipient (attenuate keep (heldCapTo k.caps delegator t)) }
  else
    none

/-- The executable revocation authority turn: `holder` drops every cap conferring an edge to `t`,
removing the `execGraph` edge to `t` (matching abstract `removeEdge`). Always commits; rewrites
only `caps`, leaving balances intact. -/
def recKRevokeTarget (k : RecordKernelState) (holder t : Label) : RecordKernelState :=
  { k with caps := fun l => if l = holder then (k.caps l).filter (fun cap => ¬ confersEdgeTo t cap)
                            else k.caps l }

/-! ## §4 — The dual frame lemma: an authority turn preserves `recTotal`.

Where a balance turn holds `caps` fixed, an authority turn holds `recTotal` fixed — proved by the
cap-edit touching only `caps` (so `cell`, hence `balOf`, hence `recTotal`, is unchanged). -/

/-- A committed delegation preserves `recTotal` and `accounts` (edits only `caps`). -/
theorem recKDelegate_frame (k k' : RecordKernelState) (delegator recipient t : Label)
    (h : recKDelegate k delegator recipient t = some k') :
    recTotal k' = recTotal k ∧ k'.accounts = k.accounts ∧ k'.cell = k.cell := by
  unfold recKDelegate at h
  by_cases hg : (k.caps delegator).any (fun cap => confersEdgeTo t cap) = true
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨?_, rfl, rfl⟩
    -- `recTotal` reads only `accounts` and `cell`, both unchanged by the `caps`-only edit.
    rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- A committed ordinary delegation grants exactly the delegator's held `t`-conferring cap. -/
theorem recKDelegate_grants (k k' : RecordKernelState) (delegator recipient t : Label)
    (h : recKDelegate k delegator recipient t = some k') :
    heldCapTo k.caps delegator t ∈ k'.caps recipient := by
  unfold recKDelegate at h
  by_cases hg : (k.caps delegator).any (fun cap => confersEdgeTo t cap) = true
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    exact grant_adds k.caps recipient (heldCapTo k.caps delegator t)
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- A copied held cap is non-amplifying against the cap it copies, over the real `ExecAuth` lattice. -/
theorem recKDelegate_copy_non_amplifying (caps : Caps) (delegator t : Label) :
    confRights (heldCapTo caps delegator t) ≤ confRights (heldCapTo caps delegator t) :=
  le_rfl

/-- A target-revocation preserves `recTotal` and `accounts` (edits only `caps`). -/
theorem recKRevokeTarget_frame (k : RecordKernelState) (holder t : Label) :
    recTotal (recKRevokeTarget k holder t) = recTotal k ∧
      (recKRevokeTarget k holder t).accounts = k.accounts ∧
      (recKRevokeTarget k holder t).cell = k.cell := by
  -- `recKRevokeTarget` edits only `caps`; `recTotal`/`accounts`/`cell` are untouched.
  refine ⟨rfl, rfl, rfl⟩

/-- A single cap confers an edge to at most one target: if `cap` confers edges to both `a` and `t`
then `a = t`. Used to show the revoke filter removes precisely the edge to `t`. -/
theorem confersEdgeTo_unique (cap : Cap) (a t : Label)
    (ha : confersEdgeTo a cap = true) (ht : confersEdgeTo t cap = true) : a = t := by
  unfold confersEdgeTo at ha ht
  rw [Bool.or_eq_true] at ha ht
  cases cap with
  | null => simp at ha
  | node tn =>
      simp only [beq_iff_eq, Cap.node.injEq, reduceCtorEq, or_false] at ha ht
      rw [← ha, ← ht]
  | endpoint te re =>
      simp only [reduceCtorEq, false_or, Bool.and_eq_true, beq_iff_eq] at ha ht
      rw [← ha.1, ← ht.1]

/-- When the delegator holds some cap conferring an edge to `t`, `heldCapTo` returns an actual
member of its slot that `confersEdgeTo t` (executable `lookup_by_target` succeeds). -/
theorem heldCapTo_mem (caps : Caps) (delegator t : Label)
    (hg : (caps delegator).any (fun cap => confersEdgeTo t cap) = true) :
    heldCapTo caps delegator t ∈ caps delegator
      ∧ confersEdgeTo t (heldCapTo caps delegator t) = true := by
  unfold heldCapTo
  rw [List.any_eq_true] at hg
  obtain ⟨c, hmem, hconf⟩ := hg
  -- `find?` with a satisfied predicate returns `some`, and the result satisfies the predicate.
  cases hfind : (caps delegator).find? (fun cap => confersEdgeTo t cap) with
  | none =>
      -- impossible: `c` satisfies the predicate, so `find?` cannot be `none`.
      rw [List.find?_eq_none] at hfind
      exact absurd hconf (by simpa using hfind c hmem)
  | some d =>
      simp only [Option.getD_some]
      exact ⟨List.mem_of_find?_eq_some hfind, List.find?_some hfind⟩

/-- Granting any concrete cap that confers the target edge reconstructs as adding that single
connectivity edge in the abstract `ExecRights = Unit` graph. This is the rights-parametric version
of the old `node t` graph lemma. -/
theorem grant_conferring_execGraph (caps : Caps) (recipient t : Label) (cap : Cap)
    (hcap : confersEdgeTo t cap = true) :
    execGraph (grant caps recipient cap)
      = addEdge (execGraph caps) recipient (⟨t, ()⟩ : Spec.Cap Label ExecRights) := by
  funext h c
  -- Unfold both sides to a `Prop` equality and prove by `propext`.
  show ((grant caps recipient cap h).any (fun cap' => confersEdgeTo c.target cap') = true)
      = (execGraph caps h c ∨ (h = recipient ∧ c = ⟨t, ()⟩))
  apply propext
  unfold grant
  by_cases hh : h = recipient
  · subst hh
    -- the edited slot: `grant` prepends a cap that already confers the target edge.
    rw [if_pos rfl]
    rw [execGraph_eq_any]
    simp only [List.any_cons, Bool.or_eq_true]
    constructor
    · rintro (hnew | hrest)
      · -- the new cap can confer only one connectivity target, so it is the edge to `t`.
        refine Or.inr ⟨by trivial, ?_⟩
        have ht : c.target = t := confersEdgeTo_unique cap c.target t hnew hcap
        exact (specCap_eq_iff_target c t).mpr ht
      · exact Or.inl hrest
    · rintro (hpre | ⟨_, hc⟩)
      · exact Or.inr hpre
      · -- `c = ⟨t,()⟩` ⟹ `c.target = t` ⟹ the granted cap confers the edge.
        have ht : c.target = t := (specCap_eq_iff_target c t).mp hc
        exact Or.inl (by simpa [ht] using hcap)
  · -- an untouched slot: the graph is unchanged and the added-edge disjunct is false.
    rw [if_neg hh, execGraph_eq_any]
    constructor
    · intro hpre; exact Or.inl hpre
    · rintro (hpre | ⟨heq, _⟩)
      · exact hpre
      · exact absurd heq hh

/-! ## §5 — The graph-change lemma: the cap-edit IS `addEdge`/`removeEdge`.

`execGraph` of the post-state equals `Spec.addEdge`/`Spec.removeEdge` of the single Spec edge
`⟨t,()⟩` applied to `execGraph` of the pre-state — verbatim `Spec.Introduce.result` /
`Spec.Revoke.result`. Proved by `funext`/`propext` reducing `.any` over the edited slot. -/

/-- After copying the delegator's held `t`-conferring cap to `recipient`, the reconstructed graph
equals the pre-graph with edge `recipient ⟶ ⟨t,()⟩` added — `Spec.Introduce.result` verbatim,
without assuming the concrete cap was `node t`. -/
theorem recKDelegate_execGraph (caps : Caps) (delegator recipient t : Label)
    (hg : (caps delegator).any (fun cap => confersEdgeTo t cap) = true) :
    execGraph (grant caps recipient (heldCapTo caps delegator t))
      = addEdge (execGraph caps) recipient (⟨t, ()⟩ : Spec.Cap Label ExecRights) := by
  exact grant_conferring_execGraph caps recipient t (heldCapTo caps delegator t)
    (heldCapTo_mem caps delegator t hg).2

/-- After revoking every `t`-conferring cap from `holder`, the reconstructed graph equals the
pre-graph with edge `holder ⟶ ⟨t,()⟩` removed — `Spec.Revoke.result` verbatim. -/
theorem recKRevokeTarget_execGraph (caps : Caps) (holder t : Label) :
    execGraph (fun l => if l = holder then (caps l).filter (fun cap => ¬ confersEdgeTo t cap)
                        else caps l)
      = removeEdge (execGraph caps) holder (⟨t, ()⟩ : Spec.Cap Label ExecRights) := by
  funext h c
  show ((if h = holder then (caps h).filter (fun cap => ¬ confersEdgeTo t cap) else caps h).any
          (fun cap => confersEdgeTo c.target cap) = true)
      = (execGraph caps h c ∧ ¬ (h = holder ∧ c = ⟨t, ()⟩))
  apply propext
  by_cases hh : h = holder
  · subst hh
    rw [if_pos rfl, execGraph_eq_any]
    -- the `.any` over the filtered list: a surviving cap confers `c.target` iff it did before AND
    -- it is not a `t`-conferring cap; but a cap conferring `c.target` is `t`-conferring iff `c.target = t`.
    constructor
    · intro hany
      -- some cap survives the filter and confers `c.target`.
      rw [List.any_eq_true] at hany
      obtain ⟨cap, hmem, hconf⟩ := hany
      rw [List.mem_filter] at hmem
      obtain ⟨hmem, hnotT⟩ := hmem
      simp only [decide_not, Bool.not_eq_true', decide_eq_false_iff_not] at hnotT
      refine ⟨?_, ?_⟩
      · -- the edge is present in the pre-graph (this surviving cap witnesses it).
        rw [List.any_eq_true]; exact ⟨cap, hmem, hconf⟩
      · -- `c ≠ ⟨t,()⟩`: else `c.target = t`, so the cap conferring `c.target` is `t`-conferring,
        -- contradicting that it survived the `¬ confersEdgeTo t` filter.
        rintro ⟨_, hc⟩
        have htc : c.target = t := (specCap_eq_iff_target c t).mp hc
        rw [htc] at hconf
        exact hnotT hconf
    · rintro ⟨hpre, hne⟩
      -- the edge is present in the pre-graph and `c.target ≠ t`.
      rw [List.any_eq_true] at hpre ⊢
      obtain ⟨cap, hmem, hconf⟩ := hpre
      refine ⟨cap, ?_, hconf⟩
      rw [List.mem_filter]
      refine ⟨hmem, ?_⟩
      -- the conferring cap is NOT `t`-conferring: else `c.target = t`, contradicting `hne`.
      simp only [decide_not, Bool.not_eq_true', decide_eq_false_iff_not]
      intro hcontra
      have htgt : c.target = t := confersEdgeTo_unique cap c.target t hconf hcontra
      exact hne ⟨rfl, (specCap_eq_iff_target c t).mpr htgt⟩
  · rw [if_neg hh, execGraph_eq_any]
    constructor
    · intro hpre; exact ⟨hpre, fun heq => absurd heq.1 hh⟩
    · intro hpre; exact hpre.1

/-! ## §6 — Granovetter grounding: the gate witnesses `Spec.Endow.holds_source`.

On commit, the delegator holds the Spec source edge `delegator ⟶ ⟨t,()⟩` in `execGraph` —
"only connectivity begets connectivity". -/

/-- A committed delegation holds the Spec source edge `delegator ⟶ ⟨t,()⟩` on `execGraph` —
exactly `Spec.Endow.holds_source`. -/
theorem recKDelegate_grounds (k k' : RecordKernelState) (delegator recipient t : Label)
    (h : recKDelegate k delegator recipient t = some k') :
    execGraph k.caps delegator (⟨t, ()⟩ : Spec.Cap Label ExecRights) := by
  unfold recKDelegate at h
  by_cases hg : (k.caps delegator).any (fun cap => confersEdgeTo t cap) = true
  · -- a held `t`-conferring cap IS the Spec source edge `delegator ⟶ ⟨t,()⟩`.
    rw [execGraph_eq_any]; exact hg
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ### §6.RIGHTS — the rights-delegation grounds in a genuinely-held cap and attenuates it.

When `recKDelegateAtten` commits: (a) `heldCapTo` is a real member of the delegator's slot that
`confersEdgeTo t`; (b) the granted cap's real conferred rights are `⊆` the held cap's
(`is_attenuation` over `ExecAuth`) — granted-vs-held, not self-vs-self. -/

/-- A committed rights-delegation grants a cap whose real authority is `⊆` the introducer's held
cap: `confRights (attenuate keep held) ≤ confRights held` over `ExecAuth`. The genuine
`is_attenuation(held, granted)` inequality via `attenuate_confRights_le`. -/
theorem recKDelegateAtten_non_amplifying (caps : Caps) (delegator t : Label) (keep : List Auth) :
    confRights (attenuate keep (heldCapTo caps delegator t))
      ≤ confRights (heldCapTo caps delegator t) :=
  attenuate_confRights_le keep (heldCapTo caps delegator t)

/-- On commit, the recipient holds the attenuated cap (`attenuate keep (heldCapTo …)`) in its slot. -/
theorem recKDelegateAtten_grants (k k' : RecordKernelState) (delegator recipient t : Label)
    (keep : List Auth) (h : recKDelegateAtten k delegator recipient t keep = some k') :
    attenuate keep (heldCapTo k.caps delegator t) ∈ k'.caps recipient := by
  unfold recKDelegateAtten at h
  by_cases hg : (k.caps delegator).any (fun cap => confersEdgeTo t cap) = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    exact grant_adds k.caps recipient (attenuate keep (heldCapTo k.caps delegator t))
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- The rights-delegation edits only `caps`, so `recTotal`/`accounts`/`cell` are fixed. -/
theorem recKDelegateAtten_frame (k k' : RecordKernelState) (delegator recipient t : Label)
    (keep : List Auth) (h : recKDelegateAtten k delegator recipient t keep = some k') :
    recTotal k' = recTotal k ∧ k'.accounts = k.accounts ∧ k'.cell = k.cell := by
  unfold recKDelegateAtten at h
  by_cases hg : (k.caps delegator).any (fun cap => confersEdgeTo t cap) = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- A committed rights-delegation holds the source edge `delegator ⟶ ⟨t,()⟩` on `execGraph`. -/
theorem recKDelegateAtten_grounds (k k' : RecordKernelState) (delegator recipient t : Label)
    (keep : List Auth) (h : recKDelegateAtten k delegator recipient t keep = some k') :
    execGraph k.caps delegator (⟨t, ()⟩ : Spec.Cap Label ExecRights) := by
  unfold recKDelegateAtten at h
  by_cases hg : (k.caps delegator).any (fun cap => confersEdgeTo t cap) = true
  · rw [execGraph_eq_any]; exact hg
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §7 — Axiom-hygiene tripwires. -/

#assert_axioms recKDelegate_frame
#assert_axioms recKDelegate_grants
#assert_axioms recKDelegate_copy_non_amplifying
#assert_axioms recKRevokeTarget_frame
#assert_axioms grant_conferring_execGraph
#assert_axioms recKDelegate_execGraph
#assert_axioms recKRevokeTarget_execGraph
#assert_axioms recKDelegate_grounds
#assert_axioms confersEdgeTo_unique
#assert_axioms specCap_eq_iff_target
#assert_axioms heldCapTo_mem
#assert_axioms recKDelegateAtten_non_amplifying
#assert_axioms recKDelegateAtten_grants
#assert_axioms recKDelegateAtten_frame
#assert_axioms recKDelegateAtten_grounds

/-! ## §8 — It runs (`#eval`). -/

/-- A record state where delegator 0 holds a `node 7` cap. -/
def rsCap : RecordKernelState :=
  { rs0 with caps := fun l => if l = 0 then [Cap.node 7] else [] }

-- Delegator 0 holds a cap to target 7; delegates connectivity to 7 to recipient 1. Commits.
#guard ((recKDelegate rsCap 0 1 7).isSome)  --  true (delegator 0 holds a `node 7` cap)
-- A delegator with no connectivity to the target cannot delegate it:
#guard ((recKDelegate rsCap 5 1 9).isSome) == false  --  false (5 holds no cap conferring an edge to 9)
-- After delegation, recipient 1 holds the `node 7` cap (the new edge to 7):
#guard (((recKDelegate rsCap 0 1 7).map (fun k => k.caps 1)).getD []) == [Cap.node 7]  --  [Cap.node 7]
-- Revocation always commits (it only subtracts): revoking 7 from 0 empties its slot.
#guard (((recKRevokeTarget rsCap 0 7).caps 0)) == []  --  [] (the `node 7` cap is filtered out)

/-- A state where delegator 0 holds only endpoint-write authority to target 7. -/
def rsEndpointWrite : RecordKernelState :=
  { rs0 with caps := fun l => if l = 0 then [Cap.endpoint 7 [Auth.write]] else [] }

-- Ordinary delegation copies the held endpoint cap; it does not upgrade write into `node`/control.
#guard (((recKDelegate rsEndpointWrite 0 1 7).map (fun k => k.caps 1)).getD []) == [Cap.endpoint 7 [Auth.write]]  -- [Cap.endpoint 7 [Auth.write]]

end Dregg2.Exec
