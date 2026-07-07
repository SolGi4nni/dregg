/-
StickyCorrect — session affinity as a refinement of an independent contract.

The stickiness layer (`Sticky.Basic`, `Sticky.Routing`) is a concrete machine:
a pin table over a rendezvous-hash selector. This file states the *behavioural
contract* a session-affinity policy must meet, phrased WITHOUT reference to that
machine — no hash, no pin table, no `chosen`/`route` — and proves the deployed
selector satisfies it.

The contract `ConsistentAffinity` treats an affinity policy as a black box
`A : membership → key → request-ordinal → backend?`. The third argument is the
*request ordinal*: the `r`-th consecutive request a session makes over a fixed
membership. This is not a phantom the adapter discards — it is threaded through
the DEPLOYED operational step: the deployed observable at ordinal `r` is the
backend `Sticky.route` returns after `r` prior routing steps have run for that
key (each of which may have re-pinned the table). Exposing the ordinal in the
interface is what gives `deterministic` teeth: "the same session lands on the
same backend on every one of its requests" is a claim a wrong policy — one whose
choice drifts as the table evolves, or that reads a per-request value — can
violate, and here it is discharged by a real theorem about `route`'s table
evolution, not by an adapter that drops the distinguishing input. The four
clauses:

  * `deterministic` — over a membership with distinct ids, every request ordinal
    for the same key observes the same backend. Stability of a session across
    the real request stream the deployed step generates.
  * `present`       — an assigned backend is always a current member; a departed
    backend is never handed back.
  * `total`         — a nonempty pool always yields an assignment.
  * `minimalDisruption` — shrink or reorder the membership set; every key whose
    backend survived keeps exactly that backend.

`stickyAffinity_correct` proves the deployed `Sticky.route` selector, iterated
over the request stream, is a model of the contract. The non-vacuity theorems at
the bottom exhibit three wrong policies — one whose choice drifts across
requests (unstable), one that returns a departed backend, one that reshuffles
surviving keys — and prove each FAILS the contract. The `route`-level lemmas bind
the operational step directly: every request in a session observes the identical
backend, a live pin is stable across repeated requests, and a dead pin remaps to
a present member.
-/

import Sticky.Basic
import Sticky.Routing

namespace Sticky

open Proxy

/-! ### The independent contract -/

/-- A session-affinity policy as a black box: it maps the current membership set,
a session key, and a *request ordinal* (which request in the session's stream) to
an assigned backend (or `none` on an empty pool). Nothing here mentions hashing,
pins, or the deployed machine. -/
abbrev AffinityFn := List Backend → Nat → Nat → Option Backend

/-- The behavioural contract of a consistent, sticky session-affinity policy,
stated over an abstract `AffinityFn`. -/
structure ConsistentAffinity (A : AffinityFn) : Prop where
  /-- Over a membership with distinct ids, the same key observes the same backend
  on every request ordinal: a session is deterministic and stable across the
  whole request stream. -/
  deterministic : ∀ bs k r r', idsNodup bs → A bs k r = A bs k r'
  /-- An assigned backend is always a current member — a departed backend is
  never returned. -/
  present : ∀ bs k r b, A bs k r = some b → b ∈ bs
  /-- A nonempty pool always yields an assignment. -/
  total : ∀ bs k r, bs ≠ [] → (A bs k r).isSome
  /-- Minimal disruption: shrink or reorder the membership set (any subset with
  distinct ids); every key whose assigned backend survives keeps exactly that
  backend. Contrapositive: a key moves only when its backend leaves the set. -/
  minimalDisruption : ∀ bs bs' k r b, idsNodup bs → idsNodup bs' →
    (∀ c ∈ bs', c ∈ bs) → A bs k r = some b → b ∈ bs' → A bs' k r = some b

/-! ### The deployed request stream -/

/-- The table state after `n` consecutive routing steps for key `k` over the
fixed membership `bs`, starting from `t`. This is exactly the state the deployed
`route` reads on the `n`-th request of a session: the first request may write a
fresh pin, and every later request runs against the table the previous one left.
`routeIter … 0` is the initial table; `routeIter … (n+1)` is the table `route`
produces from `routeIter … n`. -/
def routeIter (hash : Nat → Nat → Nat) (bs : List Backend) (t : Table) (k : Nat) :
    Nat → Table
  | 0 => t
  | n + 1 => (route hash bs (routeIter hash bs t k n) k).1

/-- **One deployed step preserves the observation.** Under distinct ids, running
`route` and reading the choice off the table it leaves behind gives the same
backend as reading it off the table before the step. This is the crux: a
first-request winner is *written back* as a pin (`update t k b.id`), and that pin
resolves — via `lookupId` under `idsNodup` — to exactly the same backend, so the
next request is not free to drift. -/
theorem route_preserves_chosen {hash : Nat → Nat → Nat} {bs : List Backend}
    {t : Table} {k : Nat} (hnd : idsNodup bs) :
    chosen hash bs (route hash bs t k).1 k = chosen hash bs t k := by
  cases hp : pinned bs t k with
  | some b =>
    have hroute : route hash bs t k = (t, some b) := by simp only [route, hp]
    rw [hroute]
  | none =>
    cases hr : rendezvous hash k bs with
    | some b =>
      have hroute : route hash bs t k = (update t k b.id, some b) := by
        simp only [route, hp, hr]
      rw [hroute]
      have hrhs : chosen hash bs t k = some b := by
        rw [chosen_of_no_pin hp]; exact hr
      have hpin' : pinned bs (update t k b.id) k = some b := by
        simp only [pinned, update_self]
        exact lookupId_eq_some_of_mem hnd (rendezvous_mem hr) rfl
      rw [chosen_of_pin hpin', hrhs]
    | none =>
      have hroute : route hash bs t k = (t, none) := by simp only [route, hp, hr]
      rw [hroute]

/-- **The observation is constant along the request stream.** Under distinct ids,
the backend a request observes is the same on every request ordinal `n`: the
deployed step's own table evolution never changes which backend the session
lands on. Proved by iterating `route_preserves_chosen`. -/
theorem chosen_routeIter {hash : Nat → Nat → Nat} {bs : List Backend} {t : Table}
    {k : Nat} (hnd : idsNodup bs) :
    ∀ n, chosen hash bs (routeIter hash bs t k n) k = chosen hash bs t k
  | 0 => by simp only [routeIter]
  | n + 1 => by
    simp only [routeIter]
    rw [route_preserves_chosen hnd]
    exact chosen_routeIter hnd n

/-- The deployed observable: the backend `Sticky.route` returns on the `n`-th
request of a session — the choice read off `routeIter`, the table state that many
consecutive routing steps have produced. The request ordinal is genuinely
consumed: distinct ordinals feed `route` distinct (evolving) table states. -/
def stickyAffinity (hash : Nat → Nat → Nat) (t : Table) : AffinityFn :=
  fun bs k n => (route hash bs (routeIter hash bs t k n) k).2

/-- **The request ordinal is absorbed by the deployed step (under distinct ids).**
The backend observed on the `n`-th request equals `chosen hash bs t k` — the very
first observation. This is the theorem that discharges `deterministic`: it is a
fact about `route` re-pinning and `lookupId` resolving, NOT a definitional
identity, so the `deterministic` clause has real content. -/
theorem stickyAffinity_eq_chosen (hash : Nat → Nat → Nat) (t : Table)
    {bs : List Backend} {k : Nat} (n : Nat) (hnd : idsNodup bs) :
    stickyAffinity hash t bs k n = chosen hash bs t k := by
  simp only [stickyAffinity]
  rw [route_snd_eq_chosen]
  exact chosen_routeIter hnd n

/-! ### The deployed selector is a model of the contract -/

/-- A nonempty pool always produces a chosen backend: a live pin resolves, or the
rendezvous winner exists. -/
theorem chosen_total {hash : Nat → Nat → Nat} {bs : List Backend} {t : Table}
    {k : Nat} (hne : bs ≠ []) : (chosen hash bs t k).isSome := by
  cases hp : pinned bs t k with
  | some b => simp [chosen_of_pin hp]
  | none => rw [chosen_of_no_pin hp]; exact rendezvous_total hne

/-- **Refinement.** The deployed `Sticky.route` selector, iterated over a
session's request stream, satisfies the independent session-affinity contract,
for every hash function and every initial pin table. Each clause discharges to a
fact about the real selector: `deterministic` is `stickyAffinity_eq_chosen` (the
request ordinal is absorbed by the deployed re-pin); `present` is `chosen_mem`;
`total` is `chosen_total`; `minimalDisruption` is `sticky_minimal_disruption`
after collapsing both ordinals to the first observation. -/
theorem stickyAffinity_correct (hash : Nat → Nat → Nat) (t : Table) :
    ConsistentAffinity (stickyAffinity hash t) where
  deterministic := fun _ _ r r' hnd => by
    rw [stickyAffinity_eq_chosen hash t r hnd, stickyAffinity_eq_chosen hash t r' hnd]
  present := fun _ _ _ _ h => by
    simp only [stickyAffinity] at h
    rw [route_snd_eq_chosen] at h
    exact chosen_mem h
  total := fun _ _ _ hne => by
    simp only [stickyAffinity]
    rw [route_snd_eq_chosen]
    exact chosen_total hne
  minimalDisruption := fun _ _ _ r _ hnd hnd' hsub hsel hb' => by
    rw [stickyAffinity_eq_chosen hash t r hnd] at hsel
    rw [stickyAffinity_eq_chosen hash t r hnd']
    exact sticky_minimal_disruption hnd hnd' hsub hsel hb'

/-! ### Operational (route-level) corollaries -/

/-- **Session determinism at the deployed step.** Under distinct ids, any two
requests of a session — the `m`-th and the `n`-th consecutive `route` step for the
same key over the same membership — observe the identical backend. This binds the
operational `route` directly, over the real stream of table states the step
generates: same session key + same membership ⇒ same backend across real
requests. -/
theorem route_trajectory_deterministic {hash : Nat → Nat → Nat} {bs : List Backend}
    {t : Table} {k : Nat} (hnd : idsNodup bs) (m n : Nat) :
    (route hash bs (routeIter hash bs t k m) k).2
      = (route hash bs (routeIter hash bs t k n) k).2 := by
  rw [route_snd_eq_chosen, route_snd_eq_chosen, chosen_routeIter hnd, chosen_routeIter hnd]

/-- **Session stability at the deployed step.** A key pinned to a present member
routes to that member, and a second request over the same membership observes the
identical backend: the pin is a stable fixed point while its backend lives.
Binds the operational `route`. -/
theorem sticky_route_repeat_stable {hash : Nat → Nat → Nat} {bs : List Backend}
    {t : Table} {k bid : Nat} {b : Backend}
    (hnd : idsNodup bs) (hpin : t k = some bid) (hmem : b ∈ bs) (hid : b.id = bid) :
    (route hash bs t k).2 = some b ∧
    (route hash bs (route hash bs t k).1 k).2 = some b := by
  have h1 : route hash bs t k = (t, some b) := sticky_stability hnd hpin hmem hid
  have h2 : route hash bs (route hash bs t k).1 k = route hash bs t k :=
    sticky_stability_idem hnd hpin hmem hid
  exact ⟨by rw [h1], by rw [h2, h1]⟩

/-- **Failover to a present member at the deployed step.** When the pinned backend
has left the eligible set (its id is absent) and the pool is nonempty, the routing
step remaps the key to the rendezvous winner `b`, records `b.id` as the new pin,
and `b` is a current member. A dead pin is never handed back. Binds `route`. -/
theorem sticky_route_failover_present {hash : Nat → Nat → Nat} {bs : List Backend}
    {t : Table} {k bid : Nat} {b : Backend}
    (hpin : t k = some bid) (habsent : bid ∉ bs.map Backend.id)
    (hwin : rendezvous hash k bs = some b) :
    route hash bs t k = (update t k b.id, some b) ∧ b ∈ bs :=
  ⟨failover_repin_winner hpin habsent hwin, rendezvous_mem hwin⟩

/-! ### Non-vacuity: wrong policies FAIL the contract

Two witness backends with distinct identities. -/

/-- Witness backend `#0`. -/
def bA : Backend := ⟨0, 1, 0, 0, true, .active⟩
/-- Witness backend `#1`. -/
def bB : Backend := ⟨1, 1, 0, 0, true, .active⟩

/-- A policy whose choice drifts across the request stream, handing the same key
on the same membership set two different backends on two different requests. -/
def driftingPolicy : AffinityFn := fun _ _ r => some (if r = 0 then bA else bB)

/-- **Instability is rejected.** `driftingPolicy` violates `deterministic`: over
the distinct-id set `[bA, bB]`, the same key yields `bA` on request `0` and `bB`
on request `1`. -/
theorem driftingPolicy_not_affinity : ¬ ConsistentAffinity driftingPolicy := by
  intro h
  have key := h.deterministic [bA, bB] 0 0 1 (by simp only [idsNodup]; decide)
  simp only [driftingPolicy] at key
  exact absurd key (by decide)

/-- A policy that always returns a fixed backend, even when it is not a member. -/
def keepDeparted : AffinityFn := fun _ _ _ => some bA

/-- **Keeping a departed backend is rejected.** `keepDeparted` violates `present`:
on the empty membership set it still returns `bA ∉ []`. -/
theorem keepDeparted_not_affinity : ¬ ConsistentAffinity keepDeparted := by
  intro h
  exact absurd (h.present [] 0 0 bA rfl) (by simp)

/-- A policy that returns the head of the membership list — order-dependent, so
it moves a surviving key when the set is presented in a different order. -/
def pickFirst : AffinityFn := fun bs _ _ => bs.head?

/-- **Reshuffling a survivor is rejected.** `pickFirst` violates
`minimalDisruption`: over `[bA, bB]` it assigns `bA`, but over the same set
reordered as `[bB, bA]` — a subset with distinct ids, in which `bA` still lives —
it assigns `bB`, moving a key whose backend never left. -/
theorem pickFirst_not_affinity : ¬ ConsistentAffinity pickFirst := by
  intro h
  have hsub : ∀ c ∈ [bB, bA], c ∈ [bA, bB] := by decide
  have key := h.minimalDisruption [bA, bB] [bB, bA] 0 0 bA
    (by simp only [idsNodup]; decide) (by simp only [idsNodup]; decide) hsub rfl (by decide)
  simp only [pickFirst, List.head?_cons] at key
  exact absurd key (by decide)

end Sticky
