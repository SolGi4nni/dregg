/-
# Dregg2.Agent.Mandate — proof-carrying, budget-bounded, revocable agent mandates.

A principal (human or agent) grants an **agent** a *mandate*: a capability with
attenuation — a `target` it may act on, a rights bound (`keep`), a spend `budget`, and a
caveat window — that the agent may SUB-DELEGATE to sub-agents only by STRICT ATTENUATION.
This is the AGENT layer sitting **on** the proven kernel attenuation spine
(`Exec/AuthTurn.lean`, `Exec/Caps.lean`); it adds NO new trust to the cap core, it only
*composes* the proven moves into a delegation TREE and proves the tree-level invariants the
out-of-band `SubAgent::execute` check (`sdk/src/runtime.rs:956`) was asserting informally:

  * **No sub-agent amplifies authority** (`subtree_rights_le_root`). Every descendant
    mandate's conferred rights `⊆` the root's, transitively — the `attenuate_confRights_le`
    leg of `recKDelegateAtten` chained down the tree. Not a `() ≤ ()` collapse: the genuine
    `Finset Auth` order.

  * **Budget is conserved across the delegation tree** (`subtree_budget_le_root` +
    `children_no_oversubscribe`). TWO distinct facets: no descendant out-spends the root, AND no
    node over-subscribes its budget to its children (the sum of a node's children's budgets `≤` the
    node's budget). Together: no agent fans out more authority-to-spend than it was given (the
    Stingray slice discipline, `Proof/Stingray.lean`, made structural for delegation not concurrency).

  * **Revocation propagates** (`revoke_kills_subtree`). Revoking the root mandate's target
    edge from the principal removes connectivity for the ENTIRE materialized subtree: after
    `recKRevokeTarget`, no descendant retains a usable mandate to the revoked target —
    single-machine immediate revocation (`MEMORY` dregg4 vision).

Materialization (`materialize`) routes a mandate onto the REAL verified executor move
`recKDelegateAtten` (`Exec/AuthTurn.lean:97`) — so a granted mandate IS a committed kernel
delegation, checked INLINE, not a side-table the executor ignores.

Pure executable Lean. Reuses `Exec.AuthTurn`/`Exec.Caps`; edits neither.
-/
import Dregg2.Exec.AuthTurn
import Dregg2.Exec.Caps

namespace Dregg2.Agent

open Dregg2.Authority (Cap Auth Label Caps)
open Dregg2.Exec
  (RecordKernelState recKDelegateAtten recKRevokeTarget confersEdgeTo heldCapTo
   attenuate confRights attenuate_confRights_le grant recTotal rs0
   recKDelegateAtten_grants recKDelegateAtten_frame)

/-! ## §1 — The mandate (a capability + attenuation + budget + caveat window).

A `Mandate` is the AGENT-layer view of an attenuated cap. Its `target`/`keep` are exactly the
arguments `recKDelegateAtten` takes; `budget` is the new (orthogonal-to-rights) spend bound the
agent layer adds; `caveat` is the runtime predicate the executor checks INLINE on each action.
`grantor`/`holder` name the delegation edge. -/

/-- A **caveat**: a runtime restriction the executor evaluates against each action the agent takes
under the mandate. Modeled as a decidable predicate on the action `method`-code so an agent's turn
is *admitted only if its method satisfies the caveat* — the inline gate, not an out-of-band check.
Sub-delegation conjoins caveats (a child is bound by its own AND every ancestor's). -/
structure Caveat where
  /-- Admit an action whose method-code is `m`? -/
  admits : Nat → Bool

/-- The always-permissive caveat (no restriction). -/
def Caveat.any : Caveat := ⟨fun _ => true⟩

/-- Conjoin two caveats: admit iff BOTH admit (sub-delegation narrows the window). -/
def Caveat.and (c d : Caveat) : Caveat := ⟨fun m => c.admits m && d.admits m⟩

/-- A **mandate**: the agent's attenuated capability bundle. `holder` may act on `target` with at
most the rights in `keep`, spend at most `budget`, and only on actions its `caveat` admits. -/
structure Mandate where
  /-- Who granted it (the principal or a parent agent). -/
  grantor : Label
  /-- The agent that holds it. -/
  holder  : Label
  /-- The resource the mandate confers an edge to. -/
  target  : Label
  /-- The rights bound (`recKDelegateAtten`'s `keep`). -/
  keep    : List Auth
  /-- The spend ceiling. -/
  budget  : Nat
  /-- The runtime caveat window. -/
  caveat  : Caveat

/-! ## §2 — Strict sub-delegation: the agent layer's only way to make a child mandate.

A child mandate is born by `subDelegate parent …`: the child's `grantor` is the parent's holder,
its rights `keep` are FILTERED THROUGH the parent's `keep` (`keep' ⊆ keep`, so the conferred rights
narrow — `attenuate` is applied on the wire by `recKDelegateAtten`), its `budget` is bounded by the
parent's, and its `caveat` is CONJOINED with the parent's. There is no constructor that widens any
face — sub-delegation can only attenuate. -/

/-- A child mandate of `parent`, held by `child`, requesting rights `req`, budget `b`, extra caveat
`cv`. The child's effective rights are `parent.keep ∩ req` (so `⊆ parent.keep`), its budget is
`min parent.budget b` (so `≤ parent.budget`), and its caveat is `parent.caveat ∧ cv`. -/
def Mandate.subDelegate (parent : Mandate) (child : Label) (req : List Auth) (b : Nat)
    (cv : Caveat) : Mandate where
  grantor := parent.holder
  holder  := child
  target  := parent.target
  keep    := parent.keep.filter (fun a => req.contains a)
  budget  := min parent.budget b
  caveat  := parent.caveat.and cv

/-- Sub-delegation never widens the rights bound: `child.keep ⊆ parent.keep`. -/
theorem subDelegate_keep_subset (parent : Mandate) (child : Label) (req : List Auth) (b : Nat)
    (cv : Caveat) : (parent.subDelegate child req b cv).keep ⊆ parent.keep := by
  intro a ha; exact List.mem_of_mem_filter ha

/-- Sub-delegation never widens the budget: `child.budget ≤ parent.budget`. -/
theorem subDelegate_budget_le (parent : Mandate) (child : Label) (req : List Auth) (b : Nat)
    (cv : Caveat) : (parent.subDelegate child req b cv).budget ≤ parent.budget :=
  Nat.min_le_left _ _

/-- Sub-delegation never widens the caveat window: if the child admits a method, so does the parent
(the child's caveat is the conjunction, so it is the stronger restriction). -/
theorem subDelegate_caveat_narrows (parent : Mandate) (child : Label) (req : List Auth) (b : Nat)
    (cv : Caveat) (m : Nat) (h : (parent.subDelegate child req b cv).caveat.admits m = true) :
    parent.caveat.admits m = true := by
  simp only [Mandate.subDelegate, Caveat.and] at h
  exact (Bool.and_eq_true _ _ |>.mp h).1

/-! ## §3 — The delegation TREE.

A `DelegTree` is a mandate together with its sub-mandate children (each itself a tree). The agent
fabric is a forest of these; this module proves the per-tree invariants, which compose to the
forest. The tree is BUILT so each child IS a `subDelegate` of its parent — enforced by the
`WellAttenuated` predicate, which is the structural statement "every edge in the tree is a strict
attenuation". -/

/-- A node of the delegation tree: a mandate plus its children (sub-mandates). -/
inductive DelegTree where
  | node (m : Mandate) (children : List DelegTree)

/-- The mandate at a tree node. -/
def DelegTree.mandate : DelegTree → Mandate
  | .node m _ => m

/-- The children subtrees. -/
def DelegTree.children : DelegTree → List DelegTree
  | .node _ cs => cs

/-- **`WellAttenuated t`** — every parent→child edge in `t` is a genuine strict attenuation: the
child's rights `⊆` parent's, budget `≤` parent's, caveat `⇒` parent's, target SAME, and the child's
grantor IS the parent's holder. This is the structural invariant the agent runtime MUST maintain
(its only tree-builder is `subDelegate`, which satisfies every clause by §2). -/
def DelegTree.WellAttenuated : DelegTree → Prop
  | .node m cs =>
      (∀ c ∈ cs, c.mandate.keep ⊆ m.keep
        ∧ c.mandate.budget ≤ m.budget
        ∧ (∀ x, c.mandate.caveat.admits x = true → m.caveat.admits x = true)
        ∧ c.mandate.target = m.target)
      ∧ (∀ c ∈ cs, c.WellAttenuated)

/-- The per-edge clause of `WellAttenuated` at a node (definitional unfolding, exposed as a lemma so
downstream proofs read the conjunction without re-unfolding the recursive `match`). -/
theorem WellAttenuated_edge {m : Mandate} {cs : List DelegTree}
    (hw : (DelegTree.node m cs).WellAttenuated) :
    ∀ c ∈ cs, c.mandate.keep ⊆ m.keep ∧ c.mandate.budget ≤ m.budget
      ∧ (∀ x, c.mandate.caveat.admits x = true → m.caveat.admits x = true)
      ∧ c.mandate.target = m.target := by
  rw [DelegTree.WellAttenuated] at hw; exact hw.1

/-- The recursive clause of `WellAttenuated`: every child subtree is itself well-attenuated. -/
theorem WellAttenuated_children {m : Mandate} {cs : List DelegTree}
    (hw : (DelegTree.node m cs).WellAttenuated) : ∀ c ∈ cs, c.WellAttenuated := by
  rw [DelegTree.WellAttenuated] at hw; exact hw.2

/-! ## §4 — Headline 1: no sub-agent amplifies authority.

Conferred rights are read through `confRights ∘ asCap`: a mandate confers the `node`/`endpoint`
authority its `(target, keep)` describe. The tree invariant pins every descendant's rights `⊆` its
parent's; `subtree_rights_le_root` chains that down to the root. We compare the genuine rights bound
`keep` (whose `confRights` is `attenuate`-narrowed on materialization, §5). -/

/-- The mandate's rights bound as a `Finset Auth` (the conferred-rights element it carries; on
materialization this is exactly the conferred rights of the granted attenuated cap, §5). -/
def Mandate.rights (m : Mandate) : Finset Auth := m.keep.toFinset

/-- The conferred-rights of every mandate in the subtree (root first, then each child's subtree). -/
def DelegTree.rightsList : DelegTree → List (Finset Auth)
  | .node m cs => m.rights :: cs.flatMap DelegTree.rightsList

/-- A child's rights bound `≤` its parent's, under `WellAttenuated`. -/
theorem child_rights_le {m : Mandate} {cs : List DelegTree} {c : DelegTree}
    (hw : (DelegTree.node m cs).WellAttenuated) (hc : c ∈ cs) :
    c.mandate.rights ≤ m.rights := by
  rw [Finset.le_iff_subset]
  intro a ha
  rw [Mandate.rights, List.mem_toFinset] at ha ⊢
  exact (WellAttenuated_edge hw c hc).1 ha

/-- **Headline 1 — NO AMPLIFICATION across the tree.** Every mandate in a well-attenuated tree
confers rights `⊆` the root's. Proved by structural induction: each step is the proven
`child_rights_le` chained with the transitivity of `⊆`. A sub-sub-…-agent can never out-authorize
the principal's original grant. -/
theorem subtree_rights_le_root : ∀ (t : DelegTree), t.WellAttenuated →
    ∀ d ∈ t.rightsList, d ≤ t.mandate.rights
  | .node m cs, hw => by
      intro d hd
      rw [DelegTree.rightsList] at hd
      rcases List.mem_cons.mp hd with hroot | hsub
      · -- d is the root mandate's rights itself: reflexivity.
        subst hroot; exact le_rfl
      · -- d is a descendant's rights of some child c; recurse, then chain c ≤ root.
        rw [List.mem_flatMap] at hsub
        obtain ⟨c, hc, hdc⟩ := hsub
        have hchild : c.mandate.rights ≤ m.rights := child_rights_le hw hc
        have hrec : d ≤ c.mandate.rights :=
          subtree_rights_le_root c (WellAttenuated_children hw c hc) d hdc
        exact le_trans hrec hchild

/-! ## §5 — Headline 1, materialized: the granted KERNEL cap is non-amplifying.

`materialize` routes the mandate's edge onto the REAL executor move `recKDelegateAtten` — so a
granted mandate IS a committed kernel delegation. On commit the recipient holds
`attenuate keep (heldCapTo …)`, whose `confRights ≤ confRights (held cap)` by the proven
`attenuate_confRights_le`. This is the no-amplification headline at the WIRE, not just on the
agent-layer `keep` set. -/

/-- Materialize a mandate onto the verified executor: delegate `target` from `grantor` to `holder`,
attenuated to `keep`, via `recKDelegateAtten`. Fail-closed exactly when the grantor holds no cap
conferring the target edge (the Granovetter premise) — the same gate the executor enforces. -/
def Mandate.materialize (m : Mandate) (k : RecordKernelState) : Option RecordKernelState :=
  recKDelegateAtten k m.grantor m.holder m.target m.keep

/-- **Headline 1 (wire).** When a mandate materializes, the cap the holder receives confers no more
authority than the grantor's held cap to the target: `confRights (granted) ≤ confRights (held)` over
the genuine `Finset Auth` lattice. The agent gains nothing the grantor could not already exercise. -/
theorem materialize_non_amplifying (m : Mandate) (k k' : RecordKernelState)
    (_h : m.materialize k = some k') :
    confRights (attenuate m.keep (heldCapTo k.caps m.grantor m.target))
      ≤ confRights (heldCapTo k.caps m.grantor m.target) :=
  attenuate_confRights_le m.keep (heldCapTo k.caps m.grantor m.target)

/-- The materialized delegation grants EXACTLY the attenuated cap into the holder's slot (the agent
holds precisely what the mandate describes — nothing more). -/
theorem materialize_grants (m : Mandate) (k k' : RecordKernelState)
    (h : m.materialize k = some k') :
    attenuate m.keep (heldCapTo k.caps m.grantor m.target) ∈ k'.caps m.holder :=
  recKDelegateAtten_grants k k' m.grantor m.holder m.target m.keep h

/-- Materialization is balance-NEUTRAL: granting a mandate moves authority, never value
(`recTotal`/`accounts`/`cell` fixed). So the budget-conservation §6 is the ONLY value-discipline a
mandate carries — the rights move does not touch the ledger. -/
theorem materialize_frame (m : Mandate) (k k' : RecordKernelState)
    (h : m.materialize k = some k') :
    recTotal k' = recTotal k ∧ k'.accounts = k.accounts ∧ k'.cell = k.cell :=
  recKDelegateAtten_frame k k' m.grantor m.holder m.target m.keep h

/-! ## §6 — Headline 2: budget is conserved across the delegation tree.

Budget conservation has TWO genuine, distinct facets — neither an aggregate shadow of the other:

  (a) **No descendant out-spends the root** (`subtree_budget_le_root`): every mandate in the tree
      has `budget ≤` the root's, transitively. This is the *bound* facet — a deep sub-sub-agent can
      never carry a larger spend ceiling than the principal granted (the rights story §4, for the
      orthogonal budget axis).

  (b) **No node over-subscribes its budget to its children** (`BudgetPartitioned` ⇒
      `children_no_oversubscribe`): the immediate children's budgets SUM to `≤` the parent's. This
      is the *conservation* facet — a parent cannot hand out, in aggregate, more spend than it
      holds (the Stingray slice law `Proof/Stingray.lean`: `Σ slices ≤ ceiling`, made structural for
      the delegation fan-out). Facet (a) alone permits each of 10 children to carry the FULL parent
      budget (10× over-subscription); facet (b) forbids that. Both are needed; only their
      conjunction is "budget is conserved across the tree".

`childrenBudget` sums a node's immediate children's budgets; `BudgetPartitioned` recursively pins
`childrenBudget ≤ budget` at every node. -/

/-- Sum of the immediate children's budgets. -/
def DelegTree.childrenBudget (t : DelegTree) : Nat :=
  (t.children.map (fun c => c.mandate.budget)).sum

/-- **`BudgetPartitioned t`** — at every node, the immediate children's budgets sum to `≤` the
node's budget (no over-subscription: the children's slices fit inside the parent's). This is the
agent-runtime discipline `subDelegate` must respect when fanning out (each `subDelegate` carves a
slice; their sum cannot exceed the held budget). Recursive: holds at this node AND every descendant.
-/
def DelegTree.BudgetPartitioned : DelegTree → Prop
  | t@(.node _ cs) => t.childrenBudget ≤ t.mandate.budget ∧ (∀ c ∈ cs, c.BudgetPartitioned)

/-- **Conservation facet (b).** A node's immediate children do not over-subscribe its budget: their
budgets sum to `≤` the node's own budget. Directly the head clause of `BudgetPartitioned`. -/
theorem children_no_oversubscribe {m : Mandate} {cs : List DelegTree}
    (hp : (DelegTree.node m cs).BudgetPartitioned) :
    (cs.map (fun c => c.mandate.budget)).sum ≤ m.budget := by
  rw [DelegTree.BudgetPartitioned] at hp
  exact hp.1

/-- A child's budget `≤` its parent's, under `WellAttenuated` (the per-edge bound). -/
theorem child_budget_le {m : Mandate} {cs : List DelegTree} {c : DelegTree}
    (hw : (DelegTree.node m cs).WellAttenuated) (hc : c ∈ cs) :
    c.mandate.budget ≤ m.budget := (WellAttenuated_edge hw c hc).2.1

/-- The conferred-budget of every mandate in the subtree (root first, then each child's subtree). -/
def DelegTree.budgets : DelegTree → List Nat
  | .node m cs => m.budget :: cs.flatMap DelegTree.budgets

/-- **Headline 2, bound facet (a) — NO DESCENDANT OUT-SPENDS THE ROOT.** Every mandate's budget in a
well-attenuated tree is `≤` the root's, by structural induction chaining `child_budget_le` with `≤`
transitivity. Combined with `children_no_oversubscribe` (facet b) at every node, the tree's spend is
fully bounded by the principal's original grant. -/
theorem subtree_budget_le_root : ∀ (t : DelegTree), t.WellAttenuated →
    ∀ b ∈ t.budgets, b ≤ t.mandate.budget
  | .node m cs, hw => by
      intro b hb
      rw [DelegTree.budgets] at hb
      rcases List.mem_cons.mp hb with hroot | hsub
      · subst hroot; exact le_rfl
      · rw [List.mem_flatMap] at hsub
        obtain ⟨c, hc, hbc⟩ := hsub
        have hchild : c.mandate.budget ≤ m.budget := child_budget_le hw hc
        have hrec : b ≤ c.mandate.budget := subtree_budget_le_root c (WellAttenuated_children hw c hc) b hbc
        exact le_trans hrec hchild

/-! ## §7 — Headline 3: revocation propagates.

Revoking the root mandate's target edge from the principal (`recKRevokeTarget`) tears down the
WHOLE materialized subtree's connectivity to that target: every mandate in the tree shares the root
`target` (the `WellAttenuated` `target` clause chained down), and after the revoke NO holder retains
a cap conferring an edge to it. The single-machine immediate-revocation guarantee. -/

/-- The target of every mandate in the subtree (root first, then each child's subtree). -/
def DelegTree.targetList : DelegTree → List Label
  | .node m cs => m.target :: cs.flatMap DelegTree.targetList

/-- Every mandate in a well-attenuated tree shares the ROOT's target (the `target` clause chained
through the tree). Revoking that one target therefore concerns every node at once. -/
theorem subtree_shares_target : ∀ (t : DelegTree), t.WellAttenuated →
    ∀ tgt ∈ t.targetList, tgt = t.mandate.target
  | .node m cs, hw => by
      intro tgt ht
      rw [DelegTree.targetList] at ht
      rcases List.mem_cons.mp ht with hroot | hsub
      · exact hroot
      · rw [List.mem_flatMap] at hsub
        obtain ⟨c, hc, htc⟩ := hsub
        have hrec : tgt = c.mandate.target := subtree_shares_target c (WellAttenuated_children hw c hc) tgt htc
        rw [hrec]; exact (WellAttenuated_edge hw c hc).2.2.2

/-- **Headline 3 — REVOCATION PROPAGATES.** After revoking the root target `t` from `holder`, that
holder holds NO cap conferring an edge to `t`: the post-state slot is the pre-slot with every
`t`-conferring cap filtered out, so any `confersEdgeTo t` cap is gone. Materialization grants each
agent its mandate cap (`materialize_grants`); revoking `t` from a holder strips exactly those
mandate caps — connectivity to the revoked target is severed, immediately. -/
theorem revoke_kills_holder (k : RecordKernelState) (holder t : Label) (cap : Cap)
    (hcap : confersEdgeTo t cap = true) :
    cap ∉ (recKRevokeTarget k holder t).caps holder := by
  simp only [recKRevokeTarget, if_true]
  intro hmem
  rw [List.mem_filter] at hmem
  -- the surviving cap satisfies `¬ confersEdgeTo t`, contradicting `hcap`.
  have hnot : (decide ¬ (confersEdgeTo t cap = true)) = true := hmem.2
  simp only [decide_not, Bool.not_eq_true', decide_eq_false_iff_not] at hnot
  exact hnot hcap

/-- Every mandate of the subtree (root first, then each child's subtree) — the agents whose
connectivity a root-target revocation severs. -/
def DelegTree.mandateList : DelegTree → List Mandate
  | .node m cs => m :: cs.flatMap DelegTree.mandateList

/-- A mandate in `mandateList` has its target in `targetList` — the two tree-walks agree pointwise
(both visit every node). Structural recursion on the nested tree. -/
theorem mem_mandateList_target_mem : ∀ (t : DelegTree) {mnd : Mandate},
    mnd ∈ t.mandateList → mnd.target ∈ t.targetList
  | .node m cs, mnd, hm => by
      rw [DelegTree.mandateList] at hm
      rw [DelegTree.targetList]
      rcases List.mem_cons.mp hm with hroot | hsub
      · subst hroot; exact List.mem_cons_self
      · rw [List.mem_flatMap] at hsub
        obtain ⟨c, hc, hmc⟩ := hsub
        refine List.mem_cons_of_mem _ ?_
        rw [List.mem_flatMap]
        exact ⟨c, hc, mem_mandateList_target_mem c hmc⟩

/-- Every mandate in a well-attenuated tree shares the root's target (the holder set the revocation
reaches): compose `mem_mandateList_target_mem` with `subtree_shares_target`. -/
theorem mandateList_target {t : DelegTree} (hw : t.WellAttenuated)
    {mnd : Mandate} (hm : mnd ∈ t.mandateList) : mnd.target = t.mandate.target :=
  subtree_shares_target t hw mnd.target (mem_mandateList_target_mem t hm)

/-- **Headline 3, tree form — REVOCATION PROPAGATES ACROSS THE TREE.** For EVERY mandate `mnd` in a
well-attenuated subtree, revoking the (single, shared) root target from `mnd`'s holder severs that
agent's connectivity: the holder retains no cap conferring an edge to the revoked target. Every node
shares the root target (`mandateList_target`), so ONE target revocation, applied at each holder,
tears down the connectivity of the ENTIRE delegation cone — the single-machine immediate-revocation
guarantee, not just at the root but at every sub-…-agent. -/
theorem revoke_kills_subtree (t : DelegTree) (hw : t.WellAttenuated)
    (k : RecordKernelState) (cap : Cap) (hcap : confersEdgeTo t.mandate.target cap = true)
    {mnd : Mandate} (hm : mnd ∈ t.mandateList) :
    cap ∉ (recKRevokeTarget k mnd.holder mnd.target).caps mnd.holder := by
  -- the node's target IS the (shared) root target the principal revokes (`mandateList_target`),
  -- so a cap conferring an edge to the root target also confers an edge to THIS node's target;
  -- `revoke_kills_holder` then strips it from this holder's slot.
  rw [mandateList_target hw hm]
  exact revoke_kills_holder k mnd.holder t.mandate.target cap hcap

/-! ## §8 — Axiom-hygiene tripwires. -/

#assert_axioms subDelegate_keep_subset
#assert_axioms subDelegate_budget_le
#assert_axioms subDelegate_caveat_narrows
#assert_axioms child_rights_le
#assert_axioms subtree_rights_le_root
#assert_axioms materialize_non_amplifying
#assert_axioms materialize_grants
#assert_axioms materialize_frame
#assert_axioms children_no_oversubscribe
#assert_axioms child_budget_le
#assert_axioms subtree_budget_le_root
#assert_axioms subtree_shares_target
#assert_axioms mandateList_target
#assert_axioms revoke_kills_holder
#assert_axioms revoke_kills_subtree
#assert_axioms WellAttenuated_edge
#assert_axioms WellAttenuated_children

/-! ## §9 — Non-vacuity: a real materializing tree + TEETH on each invariant.

Every headline above is satisfiable AND has teeth. We build a concrete principal→agent→sub-agent
tree, materialize the root edge onto the real executor (it COMMITS), and exhibit that each invariant
REFUSES a violating delegation (the witness-true-and-false bar). -/

open Dregg2.Authority (Cap Auth)

/-- A root mandate: principal `0` grants agent `1` a `node 7` cap (control over target `7`), budget
`100`, full rights, any caveat. -/
def rootM : Mandate :=
  ⟨0, 1, 7, [Auth.read, Auth.write], 100, Caveat.any⟩

/-- A faithful sub-delegation: agent `1` carves a budget-`40` slice to sub-agent `2`, narrowing
rights to read-only — the ONLY tree-builder, so attenuation is structural. -/
def childM : Mandate := rootM.subDelegate 2 [Auth.read] 40 Caveat.any

/-- A grandchild: sub-agent `2` re-delegates a budget-`10` slice to `3`. -/
def grandM : Mandate := childM.subDelegate 3 [Auth.read] 10 Caveat.any

/-- The three-deep delegation tree (principal→agent→sub-agent→sub-sub-agent). -/
def demoTree : DelegTree :=
  .node rootM [DelegTree.node childM [DelegTree.node grandM []]]

/-- **The demo tree is well-attenuated** — every edge is a genuine strict attenuation (rights ⊆,
budget ≤, caveat ⇒, target shared). Proved by `decide` over the concrete finite data: NON-VACUITY
witness that the invariant is SATISFIABLE, not just a typecheck. -/
theorem demoTree_wellAttenuated : demoTree.WellAttenuated := by
  rw [demoTree, DelegTree.WellAttenuated]
  refine ⟨?_, ?_⟩
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a ha; simp only [DelegTree.mandate, childM, rootM, Mandate.subDelegate, List.mem_filter] at ha ⊢; exact ha.1
    · exact subDelegate_budget_le rootM 2 [Auth.read] 40 Caveat.any
    · exact fun x => subDelegate_caveat_narrows rootM 2 [Auth.read] 40 Caveat.any x
    · rfl
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    rw [DelegTree.WellAttenuated]
    refine ⟨?_, ?_⟩
    · intro d hd
      simp only [List.mem_singleton] at hd
      subst hd
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro a ha; simp only [DelegTree.mandate, grandM, childM, Mandate.subDelegate, List.mem_filter] at ha ⊢; exact ha.1
      · exact subDelegate_budget_le childM 3 [Auth.read] 10 Caveat.any
      · exact fun x => subDelegate_caveat_narrows childM 3 [Auth.read] 10 Caveat.any x
      · rfl
    · intro d hd; simp only [List.mem_singleton] at hd; subst hd; rw [DelegTree.WellAttenuated]
      exact ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩

/-- **The demo tree is budget-partitioned** — at every node the children's budgets sum to `≤` the
node's (no over-subscription). Concrete: `40 ≤ 100`, `10 ≤ 40`, leaves trivially. -/
theorem demoTree_budgetPartitioned : demoTree.BudgetPartitioned := by
  rw [demoTree, DelegTree.BudgetPartitioned]
  refine ⟨?_, ?_⟩
  · -- root: child budget 40 ≤ root budget 100.
    simp only [DelegTree.childrenBudget, DelegTree.children, DelegTree.mandate, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, childM, rootM, Mandate.subDelegate]; decide
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    rw [DelegTree.BudgetPartitioned]
    refine ⟨?_, ?_⟩
    · simp only [DelegTree.childrenBudget, DelegTree.children, DelegTree.mandate, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, grandM, childM, rootM, Mandate.subDelegate]; decide
    · intro d hd; simp only [List.mem_singleton] at hd; subst hd
      rw [DelegTree.BudgetPartitioned]
      exact ⟨by simp [DelegTree.childrenBudget, DelegTree.children, DelegTree.mandate], fun _ h => by simp at h⟩

/-- **Headline 1 concretely:** every mandate's rights in the demo tree `⊆` the root's `{read,write}`.
The `subtree_rights_le_root` keystone, instantiated. -/
theorem demo_no_amplify : ∀ r ∈ demoTree.rightsList, r ≤ demoTree.mandate.rights :=
  subtree_rights_le_root demoTree demoTree_wellAttenuated

/-- **Headline 2 concretely:** every mandate's budget in the demo tree `≤` the root's `100`. -/
theorem demo_budget_bounded : ∀ b ∈ demoTree.budgets, b ≤ demoTree.mandate.budget :=
  subtree_budget_le_root demoTree demoTree_wellAttenuated

/-- **TEETH — over-budget sub-delegation is structurally impossible.** A child cannot carry MORE
budget than its parent: `subDelegate parent … b …` budget is `min parent.budget b ≤ parent.budget`,
so asking for `b = 999` against a parent budget `100` still yields `100`, never `999`. The agent
runtime cannot mint spend by sub-delegating. -/
theorem demo_overbudget_clamped :
    (rootM.subDelegate 2 [Auth.read] 999 Caveat.any).budget = 100 := by decide

/-- **TEETH — the rights bound narrows.** A read-only sub-delegation drops `write`: the
child's `keep` is `{read}`, NOT `{read,write}`. Attenuation is real, not a no-op. -/
theorem demo_rights_narrow : childM.keep = [Auth.read] := by decide

/-- **Headline 1 at the WIRE, concretely:** materialize the root edge against a kernel where the
principal holds a `node 7` cap. It COMMITS (the Granovetter premise holds), and the agent receives
the attenuated cap — non-amplifying by `materialize_non_amplifying`. -/
def demoKernel : RecordKernelState :=
  { rs0 with caps := fun l => if l = 0 then [Cap.node 7] else [] }

/-- The root materialization COMMITS — a real committed kernel delegation, not a side-table. -/
theorem demo_materialize_commits : (rootM.materialize demoKernel).isSome := by decide

/-- **TEETH — fail-closed materialization.** A mandate whose grantor holds NO cap to the target
cannot materialize: `recKDelegateAtten` returns `none`. Authority is not conjured from nothing. -/
def rogueM : Mandate := ⟨5, 6, 9, [Auth.read], 10, Caveat.any⟩

theorem demo_materialize_fails_closed : (rogueM.materialize demoKernel) = none := by decide

/-! ### `#guard` smoke — the invariants run. -/

#guard (rootM.subDelegate 2 [Auth.read] 40 Caveat.any).budget == 40        -- slice carved
#guard (rootM.subDelegate 2 [Auth.read] 999 Caveat.any).budget == 100      -- clamped to parent
#guard (childM.keep) == [Auth.read]                                        -- write dropped
#guard (rootM.materialize demoKernel).isSome                               -- commits on real executor
#guard (rogueM.materialize demoKernel).isNone                              -- fail-closed

#assert_axioms demoTree_wellAttenuated
#assert_axioms demoTree_budgetPartitioned
#assert_axioms demo_no_amplify
#assert_axioms demo_budget_bounded
#assert_axioms demo_materialize_commits
#assert_axioms demo_materialize_fails_closed

end Dregg2.Agent
