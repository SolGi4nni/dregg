/-
# Dregg2.Firmament.SeL4Composition — a dregg turn INSIDE a protection domain preserves BOTH invariants.

The seL4 grounding so far (`SeL4Abstract.lean`, the `f4ce6c7e5` pilot) grounds ONE dregg leg
(cap-non-amplification on `derive`) in transcribed l4v text. This module advances the COMPOSITION the
grounding was built toward: when a dregg cap-operation runs *inside an seL4 protection domain's CNode*
(realized as the kernel `mint`/`revoke` on the PD's derivation tree, `SeL4Kernel.lean`), it preserves —
JOINTLY, with ONE witness —

  * **the seL4 kernel's OWN derivation-tree invariant** (`MintedChildrenAttenuated`: every live minted
    cap's rights are `⊆` its parent's), and
  * **dregg's cap-non-amplification** (the `AssuranceCase.running_entry_sound` leg shape: a delegated
    cap confers `⊆` the held authority).

This is NOT a restatement of either invariant. The content is that the SAME `grantOk` /
`authNarrowerOrEqual` decision (the Rust `is_attenuation`, `local.rs:106`) that gates the kernel `mint`
is the decision that bounds dregg's conferred authority — so a dregg delegation, embedded as a kernel
mint, is a step that keeps the PD's cap-space well-formed AND keeps Granovetter non-amplification, and
the two preservations are one fact viewed at two layers. The composition theorem
(`dregg_turn_in_pd_preserves_both`) states exactly that conjunction over a real `mint` step, with the
seL4 invariant carried as a CNode-wide predicate that the step provably preserves (the inductive heart,
not a per-step tautology).

## What "a dregg turn inside a PD" means here (the scope, honestly)

The dregg cap-operations that touch a c-list are `Exec.attenuate`/`derive` (narrow + hand out) and the
firmament `CNode.mint`/`revoke` (the kernel realization at n=1). A dregg *turn* that delegates a cap is,
at the kernel layer, a `mint` of an attenuated child into the recipient's CNode (the firmament hosts the
dregg executor as a protection-domain component, `REORIENT` "rbg hosts dregg"). We model the turn's
*cap-space effect* as that `mint`, and prove it preserves both invariants. We do NOT model the turn's
ledger effect here (conservation is `running_entry_sound`'s separate leg, already proved); the
composition advanced here is the AUTHORITY composition — the one the seL4 grounding is about. The PD
boundary is the CNode: a cap minted across it (parent in one slot, child in the recipient's slot of the
same n=1 CNode) is the cross-PD delegation, and `MintedChildrenAttenuated` is the boundary law.

## The seL4 invariant we preserve (transcribed-grounded)

`MintedChildrenAttenuated cn` := every live slot that was `mintedFrom` a (live) parent holds rights `⊆`
the parent's. This is the dregg n=1 reading of the l4v `cdt`/`pas_refined` `state_objs_in_policy`
upper-bound (`Positional.lean:19`: "the policy is an UPPER BOUND on conferred authority — authority ⊆
caps, an invariant, never growth"). The kernel `mint` maintains it by construction (`mint` refuses an
amplifying child, `mint_refuses_amplification`); `revoke` maintains it by removing a subtree (removing
slots cannot create an over-broad child). We prove `mint` preserves it (the load-bearing step) and that
the resulting child satisfies the dregg authority bound — the same `grantOk`.

Discipline: axiom-clean (`#assert_all_clean` at the close), no `sorry`, no `native_decide`. Builds on the
existing `SeL4Kernel` mint/attenuation theorems and the `SeL4Abstract` α-grounding — no new kernel model,
no core `Auth` edit. `notify` participates for free (the rights lattice `AuthReq` is unchanged by the
new `Auth.notify`; a notify cap minted into a PD is governed by the SAME `grantOk`).
-/
import Dregg2.Firmament.SeL4Kernel
import Dregg2.Tactics

namespace Dregg2.Firmament.SeL4Composition

open Dregg2.Firmament.SeL4Kernel (CNode Slot SlotId mint_child_attenuates_parent
  mint_refuses_amplification mint_records_parent)
open Dregg2.Exec.CapTPConcrete (AuthReq authNarrowerOrEqual authNarrowerOrEqual_trans
  authNarrowerOrEqual_refl)
open Dregg2.Firmament (grantOk)

/-! ## §1 — The seL4 protection-domain cap-space invariant (the boundary law). -/

/-- **`childAttenuatesParent cn s`** — the per-slot leg of the PD invariant: if slot `s` is live and was
`mintedFrom` a live parent `p`, then `s`'s rights are `⊆` `p`'s (`authNarrowerOrEqual s.rights
p.rights`). An ORIGINAL cap (`mintedFrom = none`) trivially satisfies it; a minted cap whose parent has
been revoked (parent slot dead) also trivially satisfies it (the edge dangles — and the child is itself
doomed by the transitive revoke, so this is sound at n=1). The real content is the minted-from-LIVE case.
-/
def childAttenuatesParent (cn : CNode) (s : SlotId) : Prop :=
  match cn.get s with
  | none => True
  | some child =>
    match child.mintedFrom with
    | none => True
    | some parent =>
      match cn.get parent with
      | none => True
      | some p => authNarrowerOrEqual child.rights p.rights = true

/-- **`MintedChildrenAttenuated cn`** — the seL4 PD derivation-tree invariant: EVERY slot's cap
attenuates its parent (`∀ s, childAttenuatesParent cn s`). This is the dregg n=1 transcription of the
l4v `pas_refined` authority upper-bound (`Positional.lean:19`): conferred authority never grows along a
derivation edge. The kernel `mint`/`revoke` are exactly the operations that must preserve it; this module
proves `mint` does (§2), and that the dregg authority bound rides the same witness (§3). -/
def MintedChildrenAttenuated (cn : CNode) : Prop := ∀ s : SlotId, childAttenuatesParent cn s

/-- The empty CNode satisfies the invariant vacuously (no slots) — the CapDL-boot base case. -/
theorem mintedChildrenAttenuated_empty : MintedChildrenAttenuated CNode.empty := by
  intro s
  simp [childAttenuatesParent, CNode.get, CNode.empty]

/-! ### §1.5 — The allocator well-formedness invariant (`nextSlot` is fresh).

The freshness the preservation needs — that a newly-minted slot id (`cn.nextSlot`) is NOT already live —
is itself a CNode invariant, not a free fact: `WellFormed cn` says every live slot id is `< cn.nextSlot`
(the monotone kernel allocator `install`/`mint` only ever insert at `nextSlot` then bump it). This is
part of seL4's own cap-space well-formedness (the `cdt`/`is_original_cap` allocator discipline). We carry
it alongside `MintedChildrenAttenuated`, prove `mint` preserves it, and derive `get nextSlot = none`. -/

/-- **`WellFormed cn`** — the kernel cap-space allocator invariant: every live slot id is strictly below
`cn.nextSlot` (freshness), AND every live slot's derivation parent (`mintedFrom = some p`) is itself an
id below `cn.nextSlot` (NO DANGLING parent pointer to an unallocated id). The second clause is part of
seL4's `cdt` well-formedness — a child cap is always minted from an EXISTING parent, never from a future
slot. Both clauses are maintained by `install`/`mint` (insert at `nextSlot`, bump; mint's child points at
the live `parent < nextSlot`). The dangling clause is what makes `MintedChildrenAttenuated` PRESERVABLE:
without it, an old slot could dangle a `mintedFrom` at the freshly-minted id and break the invariant. -/
def WellFormed (cn : CNode) : Prop :=
  (∀ (s : SlotId) (slot : Slot), (s, slot) ∈ cn.slots → s < cn.nextSlot)
  ∧ (∀ (s : SlotId) (slot : Slot) (par : SlotId),
       (s, slot) ∈ cn.slots → slot.mintedFrom = some par → par < cn.nextSlot)

/-- The empty CNode is well-formed (no slots). -/
theorem wellFormed_empty : WellFormed CNode.empty := by
  refine ⟨?_, ?_⟩ <;> (intro s slot <;> simp [CNode.empty])

/-- **`nextSlot` is not live in a well-formed CNode** — `get cn.nextSlot = none`. The freshness fact the
preservation rests on, DERIVED from `WellFormed`'s freshness clause. If `get nextSlot` found a slot, that
slot's key would be `nextSlot`, but `WellFormed` forces every live key `< nextSlot` — contradiction. -/
theorem nextSlot_get_none (cn : CNode) (hwf : WellFormed cn) : cn.get cn.nextSlot = none := by
  unfold CNode.get
  -- `find? = none` (then `.map Prod.snd = none`): every entry's key is `< nextSlot ≠ nextSlot`.
  have hfn : cn.slots.find? (fun p => p.1 == cn.nextSlot) = none := by
    rw [List.find?_eq_none]
    intro entry hmem
    -- entry.1 < nextSlot (WellFormed freshness clause) ⇒ entry.1 ≠ nextSlot ⇒ ¬(entry.1 == nextSlot)
    have hlt := hwf.1 entry.1 entry.2 (by cases entry; exact hmem)
    simp only [Bool.not_eq_true, beq_eq_false_iff_ne, ne_eq]
    exact Nat.ne_of_lt hlt
  rw [hfn]; rfl

/-- **No live slot dangles its `mintedFrom` at `nextSlot`** — DERIVED from `WellFormed`'s no-dangling
clause: a live slot's parent is `< nextSlot`, so it is never the fresh id `nextSlot`. This is precisely
what excludes the pathological "an old slot points at the just-minted child" case in the preservation. -/
theorem mintedFrom_ne_nextSlot (cn : CNode) (hwf : WellFormed cn)
    (s' : SlotId) (slot : Slot) (hmem : (s', slot) ∈ cn.slots)
    (hmf : slot.mintedFrom = some cn.nextSlot) : False := by
  have hlt := hwf.2 s' slot cn.nextSlot hmem hmf
  exact Nat.lt_irrefl _ hlt

/-- `get s' = some child` gives `(s', child) ∈ slots` — the bridge from `get` to list membership the
no-dangling clause needs. -/
theorem mem_of_get (cn : CNode) (s' : SlotId) (child : Slot) (hgs : cn.get s' = some child) :
    (s', child) ∈ cn.slots := by
  unfold CNode.get at hgs
  cases hf : cn.slots.find? (fun p => p.1 == s') with
  | none => rw [hf] at hgs; simp at hgs
  | some entry =>
    rw [hf] at hgs
    simp only [Option.map_some, Option.some.injEq] at hgs
    have hmem : entry ∈ cn.slots := List.mem_of_find?_eq_some hf
    have hkey : (entry.1 == s') = true := by
      have := List.find?_some hf; simpa using this
    have hk : entry.1 = s' := by simpa using hkey
    -- entry = (entry.1, entry.2) = (s', child)
    have : entry = (s', child) := by
      rw [← hgs]; rw [← hk]
    rw [this] at hmem; exact hmem

/-- A successful `mint` sets `cn'.nextSlot = s + 1` with `s = cn.nextSlot` (the bump), and `cn'.slots =
(s, child) :: cn.slots`. The structural read of `mint`'s success branch. -/
theorem mint_fresh_eq_nextSlot
    (cn : CNode) (parent : SlotId) (p : Slot) (narrower : AuthReq) (s : SlotId) (cn' : CNode)
    (hp : cn.get parent = some p)
    (hmint : cn.mint parent narrower = some (s, cn')) :
    s = cn.nextSlot := by
  unfold CNode.mint at hmint
  rw [hp] at hmint
  by_cases hgate : grantOk p.rights narrower
  · simp only [hgate, if_true, Option.some.injEq, Prod.mk.injEq] at hmint
    exact hmint.1.symm
  · simp [hgate] at hmint

/-- `mint` PRESERVES `WellFormed` — the fresh child sits at `nextSlot < nextSlot+1`, every old key
`< nextSlot < nextSlot+1`, and `nextSlot` bumps to `nextSlot+1`. So the allocator invariant survives a
dregg delegation, the companion to §2's `MintedChildrenAttenuated` preservation. -/
theorem mint_preserves_wellFormed
    (cn : CNode) (parent : SlotId) (p : Slot) (narrower : AuthReq) (s : SlotId) (cn' : CNode)
    (hp : cn.get parent = some p)
    (hwf : WellFormed cn)
    (hmint : cn.mint parent narrower = some (s, cn')) :
    WellFormed cn' := by
  -- `parent` is live in `cn`, so `parent < cn.nextSlot` (freshness clause) — the fresh child's
  -- `mintedFrom = some parent` is then `< nextSlot < nextSlot+1`, maintaining the no-dangling clause.
  have hparmem : (parent, p) ∈ cn.slots := mem_of_get cn parent p hp
  have hparlt : parent < cn.nextSlot := hwf.1 parent p hparmem
  unfold CNode.mint at hmint
  rw [hp] at hmint
  by_cases hgate : grantOk p.rights narrower
  · simp only [hgate, if_true, Option.some.injEq, Prod.mk.injEq] at hmint
    obtain ⟨hs, hcn⟩ := hmint
    subst hs; subst hcn
    refine ⟨?_, ?_⟩
    · -- freshness clause: every key < nextSlot + 1
      intro s' slot' hmem'
      simp only [List.mem_cons] at hmem'
      rcases hmem' with heq | hold
      · rw [Prod.mk.injEq] at heq; rw [heq.1]; exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (hwf.1 s' slot' hold)
    · -- no-dangling clause: every live slot's mintedFrom parent < nextSlot + 1
      intro s' slot' par hmem' hmf'
      simp only [List.mem_cons] at hmem'
      rcases hmem' with heq | hold
      · -- the fresh child: mintedFrom = some parent, parent < nextSlot < nextSlot + 1
        rw [Prod.mk.injEq] at heq
        rw [heq.2] at hmf'
        -- the fresh slot's mintedFrom is `some parent`; so par = parent
        simp only [Option.some.injEq] at hmf'
        rw [← hmf']
        exact Nat.lt_succ_of_lt hparlt
      · -- an old slot: its parent < nextSlot (old no-dangling) < nextSlot + 1
        exact Nat.lt_succ_of_lt (hwf.2 s' slot' par hold hmf')
  · simp [hgate] at hmint

/-- `nextSlot` is not live in `cn` (the bare form `mint_fresh_ne_parent` uses), DERIVED from `WellFormed`.
-/
theorem nextSlot_not_live (cn : CNode) (hwf : WellFormed cn) (p : Slot)
    (hp : cn.get cn.nextSlot = some p) : False := by
  rw [nextSlot_get_none cn hwf] at hp
  exact absurd hp (by simp)

/-! ## §2 — `mint` (a dregg delegation, at the kernel layer) PRESERVES the PD invariant.

The load-bearing step: minting an attenuated child into the PD's CNode keeps every slot attenuating its
parent. The new child attenuates its (existing) parent by `mint_child_attenuates_parent`; every OTHER
slot's leg is unchanged because `mint` only INSERTS a fresh slot (it never mutates an existing slot's
rights or `mintedFrom`), so an existing slot's parent-lookup and rights are exactly as before. This is
the inductive heart — NOT a per-step tautology: it requires that the fresh slot is genuinely a leaf whose
single new edge is attenuating, and that insertion is conservative on every prior edge. -/

/-- A successful `mint` only ADDS the fresh child slot `s` at `cn.nextSlot`; every pre-existing slot id
`s' ≠ s` resolves to the SAME slot in `cn'` as in `cn`. (The allocator is monotone — `s = cn.nextSlot`
is fresh — and `mint` conses one entry, so `get` on any old id is unchanged.) The frame lemma the
preservation rests on. -/
theorem mint_get_old
    (cn : CNode) (parent : SlotId) (narrower : AuthReq) (s : SlotId) (cn' : CNode)
    (hmint : cn.mint parent narrower = some (s, cn')) (s' : SlotId) (hne : s' ≠ s) :
    cn'.get s' = cn.get s' := by
  unfold CNode.mint at hmint
  cases hp : cn.get parent with
  | none => rw [hp] at hmint; simp at hmint
  | some p =>
    rw [hp] at hmint
    by_cases hgate : grantOk p.rights narrower
    · simp only [hgate, if_true, Option.some.injEq, Prod.mk.injEq] at hmint
      obtain ⟨hs, hcn⟩ := hmint
      subst hs; subst hcn
      -- cn'.slots = (cn.nextSlot, child) :: cn.slots ; get s' skips the fresh head (s' ≠ nextSlot).
      -- find? on a cons: the head key is `cn.nextSlot`, which ≠ s' (hne, since s = nextSlot), so find?
      -- skips it and continues into cn.slots.
      unfold CNode.get
      rw [List.find?_cons_of_neg]
      -- the head predicate `(cn.nextSlot, child).1 == s'` is false:
      simp only [beq_iff_eq]
      exact fun h => hne h.symm
    · simp [hgate] at hmint

/-- The freshly-minted child slot is at `s = cn.nextSlot`, and the mint's `parent` is an EXISTING slot
(`s ≠ parent`, since `parent` was live before the fresh allocation). DERIVED from `WellFormed` (the fresh
id `nextSlot` is not live, so it cannot equal the live `parent`). -/
theorem mint_fresh_ne_parent
    (cn : CNode) (parent : SlotId) (p : Slot) (narrower : AuthReq) (s : SlotId) (cn' : CNode)
    (hwf : WellFormed cn)
    (hp : cn.get parent = some p)
    (hmint : cn.mint parent narrower = some (s, cn')) :
    s ≠ parent := by
  have hs : s = cn.nextSlot := mint_fresh_eq_nextSlot cn parent p narrower s cn' hp hmint
  subst hs
  intro hcontra
  -- hcontra : cn.nextSlot = parent. Rewrite parent ↦ nextSlot in hp: `cn.get nextSlot = some p`
  -- means nextSlot is live — contradicts WellFormed freshness (`nextSlot_not_live`).
  rw [← hcontra] at hp
  exact nextSlot_not_live cn hwf p hp

/-- **`mint` PRESERVES the PD invariant** (the composition's seL4 half). If `cn` is well-formed and
satisfies `MintedChildrenAttenuated`, and `mint parent narrower = some (s, cn')`, then `cn'` satisfies it
too: the fresh child attenuates its parent (`mint_child_attenuates_parent`), and every other slot's leg
is unchanged (`mint_get_old`). So a dregg delegation, run as a kernel mint into the PD, keeps the PD's
cap-space well-formed — the seL4 kernel invariant is maintained by the dregg step. -/
theorem mint_preserves_invariant
    (cn : CNode) (parent : SlotId) (p : Slot) (narrower : AuthReq) (s : SlotId) (cn' : CNode)
    (hwf : WellFormed cn)
    (hp : cn.get parent = some p)
    (hinv : MintedChildrenAttenuated cn)
    (hmint : cn.mint parent narrower = some (s, cn')) :
    MintedChildrenAttenuated cn' := by
  intro s'
  have hatt := mint_child_attenuates_parent cn parent p narrower s cn' hp hmint
  have hmf := mint_records_parent cn parent p narrower s cn' hp hmint
  have hsne : s ≠ parent := mint_fresh_ne_parent cn parent p narrower s cn' hwf hp hmint
  by_cases hs' : s' = s
  · -- the fresh child: its only new edge is to `parent`, and it attenuates it.
    rw [hs']
    -- parent slot still `p` in cn' (it's an OLD slot, parent ≠ s):
    have hpar' : cn'.get parent = some p := by
      rw [mint_get_old cn parent narrower s cn' hmint parent (fun h => hsne h.symm)]; exact hp
    -- the child at s: rights = narrower, mintedFrom = some parent.
    rcases hgs : cn'.get s with _ | child
    · simp [childAttenuatesParent, hgs]
    · have hmf' : child.mintedFrom = some parent := by
        have := hmf; rw [hgs] at this; simpa using this
      have hr' : child.rights = narrower := by
        have := hatt.1; rw [CNode.rightsAt, hgs] at this; simpa using this
      simp only [childAttenuatesParent, hgs, hmf', hpar', hr']
      exact hatt.2
  · -- an OLD slot: get is unchanged, and its parent (if any) is also an old slot with unchanged rights.
    have hgetold : cn'.get s' = cn.get s' := mint_get_old cn parent narrower s cn' hmint s' hs'
    have hinvs' := hinv s'
    rcases hgs : cn.get s' with _ | child
    · simp [childAttenuatesParent, hgetold, hgs]
    · rcases hmf2 : child.mintedFrom with _ | parent'
      · simp [childAttenuatesParent, hgetold, hgs, hmf2]
      · by_cases hps : parent' = s
        · -- parent' = s = nextSlot: an OLD live slot `s'` would dangle its `mintedFrom` at the fresh id.
          -- The WellFormed no-dangling clause FORBIDS this (`mintedFrom_ne_nextSlot`) — contradiction.
          exfalso
          have hsfresh : s = cn.nextSlot := mint_fresh_eq_nextSlot cn parent p narrower s cn' hp hmint
          have hmem : (s', child) ∈ cn.slots := mem_of_get cn s' child hgs
          have hmfns : child.mintedFrom = some cn.nextSlot := by rw [hmf2, hps, hsfresh]
          exact mintedFrom_ne_nextSlot cn hwf s' child hmem hmfns
        · -- parent' ≠ s: its lookup is unchanged in cn', so the leg is exactly hinvs'.
          have hpar'' : cn'.get parent' = cn.get parent' :=
            mint_get_old cn parent narrower s cn' hmint parent' hps
          simp only [childAttenuatesParent, hgetold, hgs, hmf2, hpar'']
          simp only [childAttenuatesParent, hgs, hmf2] at hinvs'
          exact hinvs'

/-! ## §3 — THE COMPOSITION: a dregg delegation-as-mint preserves BOTH invariants, ONE witness.

The payoff. A dregg cap-delegation, executed inside the PD as a kernel `mint`, simultaneously:
  (1) keeps the seL4 PD cap-space well-formed (`MintedChildrenAttenuated`, §2), and
  (2) confers on the recipient an authority `⊆` the delegator's held authority (dregg's
      `running_entry_sound` non-amplification leg shape, here on the `AuthReq` rights lattice),
and the SAME `grantOk`/`authNarrowerOrEqual narrower p.rights` decision discharges both. Not a
restatement: the conjunction over one real step, witnessed by one decision. -/

/-- **`dregg_turn_in_pd_preserves_both` — THE COMPOSITION THEOREM.** A successful dregg delegation,
realized as the kernel `mint parent narrower` inside a PD whose cap-space satisfies the seL4 invariant,
yields a state where BOTH hold:
  * **seL4 half:** `MintedChildrenAttenuated cn'` — the PD derivation tree stays well-formed (no minted
    child amplifies its parent), the kernel's own `cdt` upper-bound invariant; and
  * **dregg half:** the child's conferred rights are `⊆` the parent's (`authNarrowerOrEqual narrower
    p.rights`), the `running_entry_sound` non-amplification leg on `AuthReq` — the recipient gains no
    authority the delegator lacked.
ONE witness (`hatt.2 = grantOk p.rights narrower`) discharges both: the kernel's mint-gate decision IS
dregg's non-amplification decision. So running a dregg delegation inside an seL4 protection domain
preserves dregg's authority guarantee AND seL4's cap-space invariant, jointly. -/
theorem dregg_turn_in_pd_preserves_both
    (cn : CNode) (parent : SlotId) (p : Slot) (narrower : AuthReq) (s : SlotId) (cn' : CNode)
    (hwf : WellFormed cn)
    (hp : cn.get parent = some p)
    (hinv : MintedChildrenAttenuated cn)
    (hmint : cn.mint parent narrower = some (s, cn')) :
    -- (1) seL4 PD invariants preserved (the derivation-tree attenuation AND the allocator freshness —
    -- both halves of the kernel's own cap-space well-formedness):
    MintedChildrenAttenuated cn' ∧ WellFormed cn'
    -- (2) dregg non-amplification (the recipient's authority ⊆ the delegator's), the SAME witness:
      ∧ authNarrowerOrEqual narrower p.rights = true
      ∧ cn'.rightsAt s = some narrower :=
  ⟨mint_preserves_invariant cn parent p narrower s cn' hwf hp hinv hmint,
   mint_preserves_wellFormed cn parent p narrower s cn' hp hwf hmint,
   (mint_child_attenuates_parent cn parent p narrower s cn' hp hmint).2,
   (mint_child_attenuates_parent cn parent p narrower s cn' hp hmint).1⟩

/-- **A refused (amplifying) dregg delegation leaves the PD UNTOUCHED — fail-closed, both invariants
trivially intact.** If `mint` refuses (the delegation would amplify, `grantOk = false`), it returns
`none`: there is no `cn'`, so the PD cap-space is unchanged and the invariant trivially still holds. The
negative polarity of the composition: an over-broad dregg delegation is rejected at the kernel mint-gate,
exactly as dregg's `attenuate` would refuse to widen — the two refusals coincide. -/
theorem dregg_amplifying_delegation_refused_in_pd
    (cn : CNode) (parent : SlotId) (p : Slot) (narrower : AuthReq)
    (hp : cn.get parent = some p)
    (hamp : grantOk p.rights narrower = false) :
    cn.mint parent narrower = none :=
  mint_refuses_amplification cn parent p narrower hp hamp

/-- **The composition transitively closes: a CHAIN of dregg delegations inside the PD keeps the
invariant.** Two successive mints (delegate, then sub-delegate from the child) both preserve
`MintedChildrenAttenuated`, so a delegation chain of any length stays well-formed (by iterating §2). The
sub-delegated rights are `⊆` the original by `authNarrowerOrEqual_trans` — the n=1 reading of "a
delegation chain never amplifies along its length". Witnessed here for one sub-delegation step. -/
theorem dregg_subdelegation_chain_preserves
    (cn : CNode) (parent : SlotId) (p : Slot) (narrower : AuthReq) (s : SlotId) (cn' : CNode)
    (mid : Slot) (subNarrower : AuthReq) (s2 : SlotId) (cn'' : CNode)
    (hwf : WellFormed cn)
    (hp : cn.get parent = some p)
    (hinv : MintedChildrenAttenuated cn)
    (hmint : cn.mint parent narrower = some (s, cn'))
    (hmid : cn'.get s = some mid)
    (hmint2 : cn'.mint s subNarrower = some (s2, cn'')) :
    MintedChildrenAttenuated cn'' ∧ WellFormed cn''
      ∧ authNarrowerOrEqual subNarrower p.rights = true := by
  have hwf' : WellFormed cn' := mint_preserves_wellFormed cn parent p narrower s cn' hp hwf hmint
  have hinv' : MintedChildrenAttenuated cn' :=
    mint_preserves_invariant cn parent p narrower s cn' hwf hp hinv hmint
  have hinv'' : MintedChildrenAttenuated cn'' :=
    mint_preserves_invariant cn' s mid subNarrower s2 cn'' hwf' hmid hinv' hmint2
  have hwf'' : WellFormed cn'' := mint_preserves_wellFormed cn' s mid subNarrower s2 cn'' hmid hwf' hmint2
  refine ⟨hinv'', hwf'', ?_⟩
  -- subNarrower ⊆ mid.rights (this mint) and mid.rights = narrower ⊆ p.rights (prev mint) ⇒ trans.
  have hsub : authNarrowerOrEqual subNarrower mid.rights = true :=
    (mint_child_attenuates_parent cn' s mid subNarrower s2 cn'' hmid hmint2).2
  have hmidr : mid.rights = narrower := by
    have hch := (mint_child_attenuates_parent cn parent p narrower s cn' hp hmint).1
    rw [CNode.rightsAt, hmid] at hch
    simpa using hch
  have hpar : authNarrowerOrEqual narrower p.rights = true :=
    (mint_child_attenuates_parent cn parent p narrower s cn' hp hmint).2
  rw [hmidr] at hsub
  exact authNarrowerOrEqual_trans hsub hpar

/-! ## §4 — Axiom hygiene. Every load-bearing composition theorem is kernel-clean. -/

#assert_all_clean [
  mintedChildrenAttenuated_empty,
  wellFormed_empty,
  nextSlot_get_none,
  mint_fresh_eq_nextSlot,
  mint_preserves_wellFormed,
  mint_get_old,
  mint_fresh_ne_parent,
  mint_preserves_invariant,
  dregg_turn_in_pd_preserves_both,
  dregg_amplifying_delegation_refused_in_pd,
  dregg_subdelegation_chain_preserves
]

end Dregg2.Firmament.SeL4Composition
