/-
# Dregg2.Games.PathOfAngels.RelicNamespace — relic ids are ONE namespace.

A `RelicId` is not a per-mission label.  `WorldState.discoveredRelics` is a single
`Finset RelicId` that every mission's contribution is unioned into
(`Core.applyContribution`), and the wire renders it as one flat array — so two
missions that name the same number name the SAME relic, for the whole world, for
ever.  Nothing in `MissionSpec` said so, and on 2026-08-08 the seven-game bundle
proved it: Deck Descent (mission 5) claimed `{5, 6, 7, 8}` back when nothing else
occupied that range, and then Artificer Logic and Vent Crawl enrolled as missions
6 and 7 with relics 6 and 7.  Relic 6 meant two different things in one signed
catalog.  It was invisible until all three games shared a bundle: a solo enrolment
has nothing to collide with.

## The rule

Relic ids are **globally unique**, and every mission owns a **contiguous block** of
them derived from its own mission id:

    relicSlot m k = m.value * MISSION_RELIC_BLOCK + k        (k < MISSION_RELIC_BLOCK)
    RelicId.owner r = r.value / MISSION_RELIC_BLOCK

`owner` is a total function on the whole namespace, so every relic id belongs to
exactly one mission and a mission's block is exactly the fibre of `owner`
(`owner_eq_iff_mem_block`).  Two missions with different ids therefore have
disjoint allowlists **by arithmetic** (`allowlists_disjoint`) — there is no range
to hand-pick, and the eighth game gets its block without anyone allocating one.

⚠ This is deliberately NOT per-mission scoping.  Scoping a relic to `(mission,
relic)` would make intersection meaningless, but it is a lie about the deployed
object: the world holds one set of relics, not one set per mission, and the judge,
the records view and the node's genesis config all read that flat set.

## MISSION_RELIC_BLOCK is the signer's cap, not a new number

`poa-curator` (`poa-curator/src/lib.rs`, `MAX_RELICS_PER_MISSION`) already refuses
a catalog mission that declares more than **16** relics.  The block width is that
same 16, so "stay inside your block" *implies* the cap that the signer enforces —
and implies `MissionSpec.allowed_relics_bounded` (`MISSION_RELIC_LIMIT = 4096`,
the wire ceiling) as well.  One number, three enforcement points, and the curator
recomputes `owner` with its own copy so a disagreement is a refusal rather than a
silent widening.

Relic id 0..15 are owned by mission `⟨0⟩`, which is not a mission — mission ids
start at 1.  That is the intended consequence: every allowlist written before this
rule (`{1}`, `{2}`, … , `{5,6,7,8}`) is now owned by nobody and REFUSES rather
than being reinterpreted.
-/
import Dregg2.Games.PathOfAngels.Core

namespace Dregg2.Games.PathOfAngels

/-- Width of a mission's relic block, and therefore the largest allowlist a
mission can declare.  Equal to `poa-curator`'s `MAX_RELICS_PER_MISSION`. -/
abbrev MISSION_RELIC_BLOCK : Nat := 16

/-- The `k`-th relic of a mission.  Total in `k`; only `k < MISSION_RELIC_BLOCK`
lands in the mission's own block, and `relicSlot_owner` is stated with that
hypothesis rather than clamping silently. -/
def relicSlot (mission : MissionId) (slot : Nat) : RelicId :=
  ⟨mission.value * MISSION_RELIC_BLOCK + slot⟩

/-- The mission that owns a relic id.  Total on the whole namespace: every relic
has exactly one owner, which is what makes a collision unrepresentable rather
than merely avoided. -/
def RelicId.owner (relic : RelicId) : MissionId :=
  ⟨relic.value / MISSION_RELIC_BLOCK⟩

theorem relicSlot_owner (mission : MissionId) {slot : Nat}
    (h : slot < MISSION_RELIC_BLOCK) : (relicSlot mission slot).owner = mission := by
  obtain ⟨value⟩ := mission
  simp only [relicSlot, RelicId.owner, MissionId.mk.injEq, MISSION_RELIC_BLOCK] at h ⊢
  omega

/-- A mission's block is EXACTLY the fibre of `owner`: being owned by `m` and
being one of `m`'s `MISSION_RELIC_BLOCK` slots are the same thing.  Without this
direction "block" would be a name for a sufficient condition rather than for the
partition, and a relic could be owned by a mission that cannot name it. -/
theorem owner_eq_iff_mem_block (m : MissionId) (r : RelicId) :
    r.owner = m ↔ ∃ slot, slot < MISSION_RELIC_BLOCK ∧ r = relicSlot m slot := by
  constructor
  · intro h
    obtain ⟨value⟩ := r
    have hv : value / MISSION_RELIC_BLOCK = m.value := congrArg MissionId.value h
    refine ⟨value % MISSION_RELIC_BLOCK, Nat.mod_lt _ (by decide), ?_⟩
    simp only [relicSlot, RelicId.mk.injEq, MISSION_RELIC_BLOCK] at hv ⊢
    omega
  · rintro ⟨slot, hslot, rfl⟩
    exact relicSlot_owner m hslot

/-- Every relic a mission declares lies in the mission's own block.  Decidable, so
the emitter discharges it by computation and cannot carry an unproved allowlist. -/
def MissionSpec.relicsOwned (mission : MissionSpec) : Prop :=
  ∀ relic ∈ mission.allowedRelics, relic.owner = mission.missionId

instance (mission : MissionSpec) : Decidable mission.relicsOwned :=
  inferInstanceAs (Decidable (∀ relic ∈ mission.allowedRelics, _))

/-- ⚑ **The guarantee.**  Two missions with different ids cannot claim the same
relic — for ANY two missions that keep to their blocks, not for the seven that
happen to be in today's bundle.  This is what makes the eighth game safe without
anyone re-checking the first seven. -/
theorem allowlists_disjoint (a b : MissionSpec)
    (ha : a.relicsOwned) (hb : b.relicsOwned) (hne : a.missionId ≠ b.missionId) :
    Disjoint a.allowedRelics b.allowedRelics :=
  Finset.disjoint_left.mpr fun relic hra hrb =>
    hne ((ha relic hra).symm.trans (hb relic hrb))

/-- Discharge `relicsOwned` against LITERALS.  A mission definition takes digests
as parameters, so its projections carry free variables and `decide` refuses to run
on them even though the allowlist does not mention a single digest; naming the two
projections by `rfl` leaves a closed goal that `decide` does settle. -/
theorem relicsOwned_of_literals (mission : MissionSpec) (id : MissionId)
    (relics : Finset RelicId) (hid : mission.missionId = id)
    (hrelics : mission.allowedRelics = relics)
    (h : ∀ relic ∈ relics, relic.owner = id) : mission.relicsOwned := by
  intro relic hr
  rw [hrelics] at hr
  rw [hid]
  exact h relic hr

/-- The same fact in the shape a reader checks against a catalog: no relic is in
two missions' allowlists. -/
theorem no_relic_in_two_missions (a b : MissionSpec)
    (ha : a.relicsOwned) (hb : b.relicsOwned) (hne : a.missionId ≠ b.missionId)
    (relic : RelicId) (hra : relic ∈ a.allowedRelics) : relic ∉ b.allowedRelics :=
  fun hrb => Finset.disjoint_left.mp (allowlists_disjoint a b ha hb hne) hra hrb

/-! ## The floor is refutable

A rule that nothing can fail is not a rule.  These two record the ACTUAL defect —
the allowlists the catalog carried until 2026-08-08 — as facts, so the guarantee
above is known to exclude something. -/

/-- Deck Descent's pre-namespace allowlist is not owned by mission 5: relic ⟨5⟩ is
owned by mission ⟨0⟩. -/
theorem legacy_descent_allowlist_is_not_owned :
    ¬ (∀ relic ∈ ({⟨5⟩, ⟨6⟩, ⟨7⟩, ⟨8⟩} : Finset RelicId), relic.owner = (⟨5⟩ : MissionId)) := by
  decide

/-- ⚑ The collision that shipped: Deck Descent's `{5,6,7,8}` and Artificer Logic's
`{6}` are NOT disjoint, and neither is Vent Crawl's `{7}`.  One signed catalog,
counter 9, in which relic 6 denoted two different things. -/
theorem legacy_descent_artificer_vent_collided :
    ¬ Disjoint ({⟨5⟩, ⟨6⟩, ⟨7⟩, ⟨8⟩} : Finset RelicId) ({⟨6⟩} : Finset RelicId) ∧
    ¬ Disjoint ({⟨5⟩, ⟨6⟩, ⟨7⟩, ⟨8⟩} : Finset RelicId) ({⟨7⟩} : Finset RelicId) := by
  constructor <;> decide

#assert_axioms relicSlot_owner
#assert_axioms owner_eq_iff_mem_block
#assert_axioms allowlists_disjoint
#assert_axioms no_relic_in_two_missions
#assert_axioms legacy_descent_allowlist_is_not_owned
#assert_axioms legacy_descent_artificer_vent_collided

/-! ## Canonical rendering

The emitted `allowed_relics` array is a LIST, the proved-about allowlist is a
`Finset`, and until now the emitter took the list as a free parameter beside the
mission — so every theorem about `mission.allowedRelics` was a theorem about an
object the bytes did not have to agree with.  `RelicList` closes that: a rendering
carries a proof that it is exactly the set, and that it is strictly ascending
(which is what `poa-curator` requires of `allowed_relics` and what nothing
previously proved). -/
structure RelicList (relics : Finset RelicId) where
  values : List RelicId
  complete : values.toFinset = relics
  ascending : values.Pairwise (fun a b => a.value < b.value)

namespace RelicList

/-- Build a rendering against LITERALS, the companion of `relicsOwned_of_literals`:
name the literal set the mission's allowlist is (by `rfl`), then discharge the two
list obligations on closed terms `decide` can run on. -/
def ofLiteral {relics : Finset RelicId} (values : List RelicId)
    (literal : Finset RelicId) (hEq : relics = literal)
    (hcomplete : values.toFinset = literal)
    (hascending : values.Pairwise (fun a b => a.value < b.value)) : RelicList relics where
  values := values
  complete := by rw [hEq]; exact hcomplete
  ascending := hascending

/-- The wire projection: the exact numbers rendered into `allowed_relics`. -/
def numbers {relics : Finset RelicId} (list : RelicList relics) : List Nat :=
  list.values.map RelicId.value

theorem mem_iff {relics : Finset RelicId} (list : RelicList relics) (relic : RelicId) :
    relic ∈ list.values ↔ relic ∈ relics := by
  obtain ⟨values, complete, _⟩ := list
  subst complete
  simp

end RelicList

end Dregg2.Games.PathOfAngels
