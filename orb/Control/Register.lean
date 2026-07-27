import Control

/-!
# Control.Register — the node registration lifecycle

This module models the **registration / login fan-out** of the coordination
server built in `Control`: what happens to a `Registration` after it first
enters the registry. Three transitions on the existing `Control.ControlState`,
each derived from the public `tailcfg` / `headscale` behaviour:

* **key expiry** (`expire`) — a node key carries an expiry timestamp
  (`tailcfg.Node.KeyExpiry`, unix seconds, `0` = never). Once wall-clock time
  passes a nonzero expiry, the registration is marked `.expired` and must
  re-authenticate; an expired node is `reject`ed by the netmap poll exactly like
  an unregistered one.
* **key rotation** (`rotateKey`) — a node re-keys by presenting its previous key
  as `RegisterRequest.oldNodeKey`. The registry re-keys the existing entry to the
  new node key while preserving the node's stable identity (`id`, `user`); this
  is a rename of the registration, not a new node.
* **ephemeral reap** (`reapEphemeral`) — an ephemeral node
  (`RegisterRequest.ephemeral`) is removed from the registry on disconnect, so it
  is never again distributed as a peer.

Everything is defined as pure functions over `Control.ControlState`; `Control.step`
is untouched. The theorems compose with the foundation's safety invariant
`Control.control_netmap_needs_authorized` (only an `.authorized` registration
receives a netmap), so "expired ⇒ no netmap" and "reaped ⇒ absent" are corollaries
of the same authorization discipline.
-/

namespace Control
namespace Register

open Control

/-! ## §1  Key expiry -/

/-- Mark a single registration `.expired` when its node key has a nonzero expiry
that lies strictly in the past. A `keyExpiry` of `0` ("never expires") and any
future expiry are left exactly as they were. -/
def expireReg (now : Nat) (r : Registration) : Registration :=
  if 0 < r.node.keyExpiry ∧ r.node.keyExpiry < now then
    { r with status := .expired }
  else r

/-- Advance the registry to time `now`: every registration whose node key has
expired is marked `.expired`; all others (never-expiring or not-yet-expired) are
untouched. -/
def expire (now : Nat) (s : ControlState) : ControlState :=
  { s with nodes := s.nodes.map (expireReg now) }

/-- **An expired key drops authorization.** A registration whose node key has a
nonzero, past expiry is, after `expire now`, present under the same node key with
status `.expired` — hence `isAuthorized = false`. This is the transition that
composes with `control_netmap_needs_authorized`. -/
theorem expire_expired_not_authorized (now : Nat) (s : ControlState) (r : Registration)
    (hmem : r ∈ s.nodes) (hexp : 0 < r.node.keyExpiry) (hlt : r.node.keyExpiry < now) :
    ∃ r', r' ∈ (expire now s).nodes ∧ r'.nodeKey = r.nodeKey
      ∧ r'.status = .expired ∧ r'.status.isAuthorized = false := by
  refine ⟨{ r with status := .expired }, ?_, rfl, rfl, rfl⟩
  simp only [expire]
  apply List.mem_map.mpr
  refine ⟨r, hmem, ?_⟩
  have hc : 0 < r.node.keyExpiry ∧ r.node.keyExpiry < now := ⟨hexp, hlt⟩
  simp only [expireReg, if_pos hc]

/-- **A live key keeps its status.** A registration whose key never expires
(`keyExpiry = 0`) or whose expiry is still in the future (`now ≤ keyExpiry`)
survives `expire now` unchanged — the exact same record, with the exact same
status, is still in the registry. -/
theorem expire_preserves_live (now : Nat) (s : ControlState) (r : Registration)
    (hmem : r ∈ s.nodes) (hlive : r.node.keyExpiry = 0 ∨ now ≤ r.node.keyExpiry) :
    r ∈ (expire now s).nodes := by
  simp only [expire]
  apply List.mem_map.mpr
  refine ⟨r, hmem, ?_⟩
  simp only [expireReg]
  rcases hlive with h | h
  · rw [if_neg (by rintro ⟨h0, hlt⟩; omega)]
  · rw [if_neg (by rintro ⟨h0, hlt⟩; omega)]

/-- **An expired registration gets no netmap.** If, after `expire now`, the node
polling with `req.nodeKey` is registered but `.expired`, the poll is `reject`ed —
no netmap is emitted. This is the contrapositive of
`control_netmap_needs_authorized` (an `.expired` status is not `.authorized`), so
`expire` never widens who can pull a netmap. -/
theorem expired_gets_no_netmap (pol : Policy) (now : Nat) (s : ControlState)
    (req : MapRequest) (r : Registration)
    (hl : lookupReg (expire now s).nodes req.nodeKey = some r)
    (hexp : r.status = .expired) :
    (step pol (expire now s) (.mapPoll req)).2 = .reject := by
  simp [step, hl, hexp, NodeStatus.isAuthorized]

/-! ## §2  Key rotation -/

/-- Re-key a single registration: if its current key is `old`, replace both the
registry key and the node's overlay key with `new`, leaving every other field —
crucially the stable `id` and owning `user` — intact. Registrations under other
keys are untouched. -/
def rotateReg (old new : NodeKey) (r : Registration) : Registration :=
  if r.nodeKey = old then
    { r with nodeKey := new, node := { r.node with key := new } }
  else r

/-- Rotate the registry from node key `old` to `new` (the `oldNodeKey` login
flow): the entry keyed by `old` is re-keyed to `new`, preserving its identity. -/
def rotateKey (old new : NodeKey) (s : ControlState) : ControlState :=
  { s with nodes := s.nodes.map (rotateReg old new) }

/-- A successful lookup returns a registration actually keyed by the searched
key. -/
theorem lookupReg_nodeKey (l : List Registration) (k : NodeKey) (r : Registration)
    (h : lookupReg l k = some r) : r.nodeKey = k := by
  induction l with
  | nil => simp [lookupReg] at h
  | cons a t ih =>
    simp only [lookupReg] at h
    by_cases ha : a.nodeKey = k
    · rw [if_pos ha] at h
      simp only [Option.some.injEq] at h
      subst h; exact ha
    · rw [if_neg ha] at h; exact ih h

/-- Under rotation, the first-match lookup of the *new* key finds the rotated
form of whatever the *old* key resolved to — provided the new key was not
already present (so no earlier entry shadows the re-keyed one). -/
theorem lookupReg_map_rotate (old new : NodeKey) :
    ∀ (l : List Registration) (r0 : Registration),
      lookupReg l old = some r0 → lookupReg l new = none →
      lookupReg (l.map (rotateReg old new)) new = some (rotateReg old new r0) := by
  intro l
  induction l with
  | nil => intro r0 hold _; simp [lookupReg] at hold
  | cons h t ih =>
    intro r0 hold hnew
    simp only [lookupReg] at hold hnew
    simp only [List.map_cons, lookupReg]
    by_cases hho : h.nodeKey = old
    · rw [if_pos hho] at hold
      simp only [Option.some.injEq] at hold
      subst hold
      have hkey : (rotateReg old new h).nodeKey = new := by
        simp only [rotateReg, if_pos hho]
      rw [if_pos hkey]
    · rw [if_neg hho] at hold
      have hkey : (rotateReg old new h).nodeKey = h.nodeKey := by
        simp only [rotateReg, if_neg hho]
      by_cases hhn : h.nodeKey = new
      · rw [if_pos hhn] at hnew; simp at hnew
      · rw [if_neg hhn] at hnew
        rw [if_neg (by rw [hkey]; exact hhn)]
        exact ih r0 hold hnew

/-- **Rotation preserves node identity.** If `old` was registered and `new` was
not, then after `rotateKey old new` the new key resolves to a registration that
is keyed by `new` yet carries the same stable `node.id` and owning `node.user`
as the old entry — a rename, not a new node. -/
theorem rotate_preserves_identity (old new : NodeKey) (s : ControlState) (r0 : Registration)
    (hold : lookupReg s.nodes old = some r0)
    (hnew : lookupReg s.nodes new = none) :
    ∃ r', lookupReg (rotateKey old new s).nodes new = some r'
        ∧ r'.nodeKey = new ∧ r'.node.id = r0.node.id ∧ r'.node.user = r0.node.user := by
  have hk : r0.nodeKey = old := lookupReg_nodeKey s.nodes old r0 hold
  refine ⟨rotateReg old new r0, ?_, ?_, ?_, ?_⟩
  · simp only [rotateKey]
    exact lookupReg_map_rotate old new s.nodes r0 hold hnew
  · simp [rotateReg, hk]
  · simp [rotateReg, hk]
  · simp [rotateReg, hk]

/-! ## §3  Ephemeral reap -/

/-- Remove the registration keyed by `nk` (an ephemeral node disconnecting):
drop every entry whose node key is `nk` from the registry. -/
def reapEphemeral (nk : NodeKey) (s : ControlState) : ControlState :=
  { s with nodes := s.nodes.filter (fun r => r.nodeKey ≠ nk) }

/-- After filtering out a key, the first-match lookup of that key finds nothing. -/
theorem lookupReg_filter_ne (l : List Registration) (nk : NodeKey) :
    lookupReg (l.filter (fun r => r.nodeKey ≠ nk)) nk = none := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    by_cases hh : h.nodeKey = nk
    · have hfc : (h :: t).filter (fun r => r.nodeKey ≠ nk)
              = t.filter (fun r => r.nodeKey ≠ nk) := by simp [List.filter_cons, hh]
      rw [hfc]; exact ih
    · have hfc : (h :: t).filter (fun r => r.nodeKey ≠ nk)
              = h :: t.filter (fun r => r.nodeKey ≠ nk) := by simp [List.filter_cons, hh]
      rw [hfc]
      simp only [lookupReg, if_neg hh]
      exact ih

/-- **A reaped node is gone.** After `reapEphemeral nk`, looking the node up by
its key yields `none`, so it can never again be returned as a peer in any
netmap. -/
theorem reap_removes (nk : NodeKey) (s : ControlState) :
    lookupReg (reapEphemeral nk s).nodes nk = none := by
  simp only [reapEphemeral]
  exact lookupReg_filter_ne s.nodes nk

/-- **Reaping is targeted.** Removing key `nk` leaves every registration under a
*different* key in place — the reap touches only the departing ephemeral node. -/
theorem reap_preserves_others (nk : NodeKey) (s : ControlState) (r : Registration)
    (hmem : r ∈ s.nodes) (hne : r.nodeKey ≠ nk) :
    r ∈ (reapEphemeral nk s).nodes := by
  simp only [reapEphemeral]
  rw [List.mem_filter]
  exact ⟨hmem, by simp [hne]⟩

end Register
end Control

#print axioms Control.Register.expire_expired_not_authorized
#print axioms Control.Register.expire_preserves_live
#print axioms Control.Register.expired_gets_no_netmap
#print axioms Control.Register.lookupReg_nodeKey
#print axioms Control.Register.lookupReg_map_rotate
#print axioms Control.Register.rotate_preserves_identity
#print axioms Control.Register.lookupReg_filter_ne
#print axioms Control.Register.reap_removes
#print axioms Control.Register.reap_preserves_others
