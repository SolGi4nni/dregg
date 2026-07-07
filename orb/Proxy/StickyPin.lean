/-
StickyPin — cookie-carried session affinity over the policy chain.

Reference cookie persistence: the proxy issues a cookie naming the chosen
backend; on later requests the cookie's backend is used DIRECTLY — bypassing
the balancing policy — as long as that backend can still take new work. A dead
pin (backend gone, unhealthy, draining, or down) falls back to the ordinary
policy chain, which yields a fresh backend to re-pin.

This is affinity BY IDENTITY, strictly stronger than hash affinity: a
rendezvous key keeps its backend only while the pool is stable modulo
removals, whereas a pin survives ANY pool change that keeps the pinned
backend eligible (additions included — where a hash key may be re-homed onto
a new backend, a pin never moves).

The pin deliberately overrides TIER fallback too: a session pinned to a
backend that got demoted to a backup tier (or whose primaries recovered)
stays where its server-side session state lives. Only eligibility (healthy ∧
active) gates the pin — the same gate new selection uses.

Theorems:

  * `selectPinned_affinity` — **the pin binds**: while the pinned backend is
    eligible, it IS the selection (under `idsNodup`, the very backend);
  * `selectPinned_dead_pin` / `selectPinned_no_pin` — **exact fallback**: a
    dead or absent pin makes the pinned selector literally equal to the plain
    policy chain — re-balancing is the proven chain, not an ad-hoc path;
  * `selectPinned_eligible` — every verdict (pinned or re-balanced) is an
    eligible member of the pool: a stale cookie can never resurrect a down
    backend;
  * `selectPinned_total` — totality is inherited from the chain's.
-/

import Proxy.Balance

namespace Proxy

/-- First backend carrying identity `bid` (the cookie value), scanning left
to right. Under `idsNodup` it is the unique one. -/
def findId (bid : Nat) : List Backend → Option Backend
  | [] => none
  | b :: bs => if b.id = bid then some b else findId bid bs

theorem findId_mem {bid : Nat} {bs : List Backend} {b : Backend}
    (h : findId bid bs = some b) : b ∈ bs := by
  induction bs generalizing b with
  | nil => cases h
  | cons c rest ih =>
    simp only [findId] at h
    split at h
    · cases h; exact List.mem_cons_self c rest
    · exact List.mem_cons_of_mem _ (ih h)

theorem findId_id {bid : Nat} {bs : List Backend} {b : Backend}
    (h : findId bid bs = some b) : b.id = bid := by
  induction bs generalizing b with
  | nil => cases h
  | cons c rest ih =>
    simp only [findId] at h
    split at h
    · cases h; assumption
    · exact ih h

theorem findId_some {bid : Nat} {bs : List Backend} {w : Backend}
    (hmem : w ∈ bs) (hid : w.id = bid) : (findId bid bs).isSome := by
  induction bs with
  | nil => cases hmem
  | cons c rest ih =>
    simp only [findId]
    split
    · rfl
    · rename_i hne
      rcases List.mem_cons.mp hmem with hw | hw
      · exact absurd (hw ▸ hid) hne
      · exact ih hw

theorem findId_none {bid : Nat} {bs : List Backend}
    (h : findId bid bs = none) : ∀ b ∈ bs, b.id ≠ bid := by
  intro b hb hbid
  have := findId_some hb hbid
  rw [h] at this
  cases this

/-- Pinned selection: an eligible backend carrying the cookie's identity wins
outright; otherwise (no cookie, unknown id, or ineligible pin) fall back to
the plain policy chain. -/
def selectPinned (pin : Option Nat) (ps : List Policy) (ctx : Ctx)
    (bs : List Backend) : Option Backend :=
  match pin with
  | none => selectChain ps ctx bs
  | some bid =>
    match findId bid (eligibleOf bs) with
    | some b => some b
    | none => selectChain ps ctx bs

/-- No cookie ⇒ the pinned selector IS the plain chain. -/
theorem selectPinned_no_pin {ps : List Policy} {ctx : Ctx}
    {bs : List Backend} : selectPinned none ps ctx bs = selectChain ps ctx bs :=
  rfl

/-- **The pin binds.** While any eligible backend carries the pinned id, the
selection carries that id and is eligible; under `idsNodup` it is the pinned
backend itself. The balancing policy is bypassed entirely. -/
theorem selectPinned_affinity {bid : Nat} {ps : List Policy} {ctx : Ctx}
    {bs : List Backend} {w : Backend} (hmem : w ∈ bs) (hid : w.id = bid)
    (helig : w.eligible = true) :
    ∃ b, selectPinned (some bid) ps ctx bs = some b
      ∧ b.id = bid ∧ b ∈ bs ∧ b.eligible = true := by
  have hw : w ∈ eligibleOf bs := mem_eligibleOf.mpr ⟨hmem, helig⟩
  have hsome := findId_some hw hid
  cases hf : findId bid (eligibleOf bs) with
  | none => rw [hf] at hsome; cases hsome
  | some b =>
    have hbmem := mem_eligibleOf.mp (findId_mem hf)
    exact ⟨b, by simp [selectPinned, hf], findId_id hf, hbmem.1, hbmem.2⟩

/-- **The pin binds, uniquely.** With distinct ids, the eligible pinned
backend is exactly the selection. -/
theorem selectPinned_affinity_unique {bid : Nat} {ps : List Policy}
    {ctx : Ctx} {bs : List Backend} {w : Backend} (hnd : idsNodup bs)
    (hmem : w ∈ bs) (hid : w.id = bid) (helig : w.eligible = true) :
    selectPinned (some bid) ps ctx bs = some w := by
  obtain ⟨b, hsel, hbid, hbmem, _⟩ :=
    selectPinned_affinity (ps := ps) (ctx := ctx) hmem hid helig
  rw [hsel, eq_of_id_eq hnd hbmem hmem (by rw [hbid, hid])]

/-- **Exact fallback.** When no eligible backend carries the pinned id (the
backend left, went unhealthy, or is draining/down), the pinned selector is
literally the plain policy chain: re-balancing inherits every chain theorem. -/
theorem selectPinned_dead_pin {bid : Nat} {ps : List Policy} {ctx : Ctx}
    {bs : List Backend}
    (hdead : ∀ b ∈ bs, b.eligible = true → b.id ≠ bid) :
    selectPinned (some bid) ps ctx bs = selectChain ps ctx bs := by
  cases hf : findId bid (eligibleOf bs) with
  | none => simp [selectPinned, hf]
  | some b =>
    have hbmem := mem_eligibleOf.mp (findId_mem hf)
    exact absurd (findId_id hf) (hdead b hbmem.1 hbmem.2)

/-- A pinned verdict — by pin or by fallback — is an eligible pool member: a
stale cookie can never route to an unhealthy, draining, or removed backend. -/
theorem selectPinned_eligible {pin : Option Nat} {ps : List Policy}
    {ctx : Ctx} {bs : List Backend} {b : Backend}
    (h : selectPinned pin ps ctx bs = some b) :
    b ∈ bs ∧ b.eligible = true := by
  cases pin with
  | none =>
    have := selectChain_eligible h
    exact ⟨this.1, this.2.1⟩
  | some bid =>
    simp only [selectPinned] at h
    cases hf : findId bid (eligibleOf bs) with
    | some c =>
      rw [hf] at h
      cases h
      exact mem_eligibleOf.mp (findId_mem hf)
    | none =>
      rw [hf] at h
      have := selectChain_eligible h
      exact ⟨this.1, this.2.1⟩

/-- Totality: the pinned selector succeeds whenever the plain chain does (and
also whenever the pin is live, per `selectPinned_affinity`). -/
theorem selectPinned_total {pin : Option Nat} {ps : List Policy} {ctx : Ctx}
    {bs : List Backend} (h : (selectChain ps ctx bs).isSome) :
    (selectPinned pin ps ctx bs).isSome := by
  cases pin with
  | none => exact h
  | some bid =>
    simp only [selectPinned]
    cases hf : findId bid (eligibleOf bs) with
    | some c => rfl
    | none => exact h

end Proxy
