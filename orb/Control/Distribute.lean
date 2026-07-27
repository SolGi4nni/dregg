import Control
/-!
# Control.Distribute — netmap distribution + the netmap→WireGuard seam

Two roadmap components built on the `Control` foundation, each closing a loop the
report named:

* **§A Netmap distribution (deltas).** The coordination server does not resend a
  full netmap on every poll; it sends a `MapResponse.delta` the client folds into
  its current view (`NetMap.applyDelta`). This module gives the server side — the
  delta *computation* — and proves the loop closes: the client's fold of the
  server's delta reconstructs exactly the intended peer set. (Assumption-free: the
  resync delta sends the new peer set as `changed` and the departed ids as
  `removed`, and the fold provably drops every stale survivor.)

* **§B netmap → WireGuard cryptokey routing.** The dataplane programs the tunnel
  with `NetMap.toWgPeers` — each authorized peer's `Node` translated to a real
  `Wireguard.Peer.PeerCfg`. This module shows the translation composes with
  drorb's *already-verified* cryptokey routing (`Wireguard.Peer.bestPlen`,
  `lookupPeer`): a destination is routed to a translated peer iff some netmap
  `allowedIPs` prefix admits it — the netmap authorization *is* the routing table,
  with no new proof obligation on the matcher (the prefix test is definitionally
  the WireGuard one).
-/

namespace Control.Distribute

open Control

/-! ## §A  Netmap distribution — the delta computation and its reconstruction -/

/-- The **resync delta** from an old peer set to a new one: announce the whole new
peer set as `changed`, and mark every departed node id (present in old, absent in
new) as `removed`. This is what the server emits when a node reconnects or its
view is rebuilt — a `delta`-shaped message that nonetheless carries the complete
target set, so its fold needs no id-uniqueness assumption to be exact. -/
def resyncDelta (oldPeers newPeers : List Node) : MapResponse :=
  let newIds := newPeers.map (·.id)
  let removed := (oldPeers.map (·.id)).filter (fun i => !newIds.contains i)
  .delta newPeers removed []

/-- Every node id carried in a `resyncDelta`'s new set is, of course, a new id. -/
theorem resync_changed_ids (newPeers : List Node) (p : Node)
    (hp : p ∈ newPeers) : (newPeers.map (·.id)).contains p.id = true := by
  simp only [List.contains_eq_mem, decide_eq_true_eq, List.mem_map]
  exact ⟨p, hp, rfl⟩

/-- **The distribution loop closes.** Folding the server's resync delta into the
client's current netmap reconstructs *exactly* the new peer set — no duplicated,
stale, or dropped peers, and with no id-uniqueness hypothesis. This is the
correctness of netmap delta distribution: the client that applies the delta ends
up holding the peer set the server intended. -/
theorem resync_reconstructs (nm : NetMap) (newPeers : List Node) :
    (nm.applyDelta (resyncDelta nm.peers newPeers)).peers = newPeers := by
  simp only [resyncDelta, NetMap.applyDelta]
  -- survivors: old peers neither removed nor superseded by a changed record — none.
  suffices hsurv :
      (nm.peers.filter (fun p => (((nm.peers.map (·.id)).filter
          (fun i => !(newPeers.map (·.id)).contains i)).all (· ≠ p.id)))).filter
          (fun p => ((newPeers.map (·.id)).all (· ≠ p.id))) = [] by
    rw [hsurv, List.append_nil]
  rw [List.filter_eq_nil_iff]
  intro p hp hpred
  simp only [List.mem_filter] at hp
  obtain ⟨hpmem, hnotremoved⟩ := hp
  -- p survived the `removed` filter ⇒ p.id is NOT departed ⇒ p.id ∈ newIds
  have hpidnew : (newPeers.map (·.id)).contains p.id = true := by
    cases hcont : (newPeers.map (·.id)).contains p.id with
    | true => rfl
    | false =>
      exfalso
      rw [List.all_eq_true] at hnotremoved
      have hmemrem : p.id ∈ (nm.peers.map (·.id)).filter
          (fun i => !(newPeers.map (·.id)).contains i) := by
        rw [List.mem_filter]
        exact ⟨by simp only [List.mem_map]; exact ⟨p, hpmem, rfl⟩, by rw [hcont]; rfl⟩
      have := hnotremoved p.id hmemrem
      simp at this
  -- but then the survivor predicate `all (·≠p.id)` over newIds is false at p.id
  rw [List.all_eq_true] at hpred
  have hmemnew : p.id ∈ newPeers.map (·.id) := by
    rw [List.contains_eq_mem, decide_eq_true_eq] at hpidnew; exact hpidnew
  have := hpred p.id hmemnew
  simp at this

/-! ## §B  netmap → WireGuard cryptokey routing -/

/-- **The prefix bridge.** A `Control.Prefix` matches an address exactly when its
WireGuard cryptokey-routing translation does — definitionally, because
`Prefix.toWgCidr` is field-identical and both matchers are the same `bitAt` test.
So no matcher is re-proved across the seam. -/
theorem prefix_matches_toWgCidr (p : Prefix) (ip : Bytes) :
    p.matches ip = (Prefix.toWgCidr p).matches ip := rfl

/-- The cryptokey-routing prefix set a translated peer carries is exactly the
node's `allowedIPs`, translated prefix-for-prefix. -/
theorem wgPeer_allowed_eq (n : Node) :
    (Node.toWgPeer n).allowed = n.allowedIPs.map Prefix.toWgCidr := rfl

/-- **Routing admits exactly the netmap-authorized prefixes.** If WireGuard
cryptokey routing over a translated node's allowed set admits `ip` (with best
prefix length `k`), then the node had an `allowedIPs` prefix that matches `ip`
with that length — routing never admits an address the netmap did not authorize. -/
theorem wg_route_needs_allowed (n : Node) (ip : Bytes) (k : Nat)
    (h : Wireguard.Peer.bestPlen (Node.toWgPeer n).allowed ip = some k) :
    ∃ p ∈ n.allowedIPs, p.matches ip = true ∧ p.bits = k := by
  rw [wgPeer_allowed_eq] at h
  obtain ⟨c, hcmem, hcmatch, hcplen⟩ := Wireguard.Peer.bestPlen_mem _ ip k h
  simp only [List.mem_map] at hcmem
  obtain ⟨p, hpmem, hpc⟩ := hcmem
  refine ⟨p, hpmem, ?_, ?_⟩
  · rw [prefix_matches_toWgCidr, hpc]; exact hcmatch
  · rw [← hpc] at hcplen; simpa [Prefix.toWgCidr] using hcplen

/-- **No route without authorization.** If cryptokey routing over the translated
allowed set does not resolve `ip`, then no `allowedIPs` prefix of the node matches
it — the dropped-packet (fail-closed) side of the seam. -/
theorem wg_no_route_no_allowed (n : Node) (ip : Bytes)
    (h : Wireguard.Peer.bestPlen (Node.toWgPeer n).allowed ip = none) :
    ∀ p ∈ n.allowedIPs, p.matches ip = false := by
  rw [wgPeer_allowed_eq] at h
  intro p hpmem
  have hc : Prefix.toWgCidr p ∈ n.allowedIPs.map Prefix.toWgCidr := by
    simp only [List.mem_map]; exact ⟨p, hpmem, rfl⟩
  have := Wireguard.Peer.bestPlen_none _ ip h (Prefix.toWgCidr p) hc
  rw [prefix_matches_toWgCidr]; exact this

end Control.Distribute
