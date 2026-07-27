import Control

/-!
# DERP relay-map distribution

The coordination server hands each node a **DERP map**: a set of relay regions
that form the encrypted-relay fallback path when a direct connection cannot be
established. Each node advertises a *home* region (`Node.derp`), and that home
must name a region that actually appears in the distributed map — otherwise the
node's fallback path points at a relay region that does not exist.

This module models that fan-out and proves the key soundness property: in a
valid distribution every node (self and every peer) has a home region that is a
real member of the map. This mirrors the coordination server's registry lookup
(`Control.lookupReg`) with a first-match region lookup.

This is `Control.Derp`, the DERP-map *distribution* component. It is unrelated
to the top-level `Derp` module (the DERP wire-frame protocol).
-/

namespace Control.Derp

open Control

/-- A DERP relay region: an id, a short region code, the relay endpoints that
live in the region, and the UDP port on which those relays also answer STUN
Binding requests. Shape follows public `tailcfg.DERPRegion` / `tailcfg.DERPNode`.

`stunPort = 0` means **not advertised**: the projection omits `STUNPort` from the
wire node, and a client then probes tailscale's default 3478. A homelab plane that
runs no STUN service leaves it 0 and behaves exactly as before this field existed
— which is why every theorem below, and every existing `rfl`, is untouched: the
routing invariants read `regionID` only and never look at an endpoint or a port. -/
structure DerpRegion where
  regionID : Nat
  regionCode : Bytes
  nodes : List Endpoint
  /-- UDP port of the region's STUN Binding server; `0` ⇒ not advertised. -/
  stunPort : Nat := 0
  /-- The TLS certificate name a client must accept for the region's relays, as ASCII
  bytes; `[]` ⇒ not advertised. A self-hosted relay presents a certificate no public
  CA signed, so `derphttp` is told to pin it by hash instead of building a PKI path:
  the value is `sha256-raw:<hex sha256 of the leaf DER>`. With nothing advertised a
  stock client verifies the relay against the system roots, which for a self-signed
  leaf can only fail — so this field is what makes a self-hosted DERP region reachable
  at all over HTTPS. `[]` reproduces the pre-existing served shape byte for byte, and
  the routing invariants read `regionID` only, so nothing below is affected. -/
  certName : Bytes := []
  deriving Repr, DecidableEq

/-- A DERP map: the list of relay regions the server distributes to a node.
Shape follows public `tailcfg.DERPMap`. -/
structure DerpMap where
  regions : List DerpRegion
  deriving Repr

/-- First-match region lookup over a region list, mirroring `Control.lookupReg`.
Returns the first region whose `regionID` equals `rid`. -/
def lookupRegion : List DerpRegion → Nat → Option DerpRegion
  | [], _ => none
  | r :: t, rid => if r.regionID = rid then some r else lookupRegion t rid

/-- The region a given id resolves to in the map (first match), or `none`. -/
def DerpMap.lookup (dm : DerpMap) (rid : Nat) : Option DerpRegion :=
  lookupRegion dm.regions rid

/-- Whether the map contains a region with the given id. -/
def DerpMap.hasRegion (dm : DerpMap) (rid : Nat) : Bool :=
  (dm.lookup rid).isSome

/-- A node's home DERP region is valid iff the map contains that region. -/
def nodeHomeValid (dm : DerpMap) (n : Node) : Bool :=
  dm.hasRegion n.derp

/-- A distribution of `dm` to netmap `nm` is valid when the node itself and
every peer have a home region present in the map. -/
def validDistribution (dm : DerpMap) (nm : NetMap) : Prop :=
  nodeHomeValid dm nm.self = true ∧ ∀ p ∈ nm.peers, nodeHomeValid dm p = true

/-- First-match region lookup is sound: if it succeeds, the region it returns is
genuinely a member of the list and carries the asked-for id. -/
theorem lookupRegion_sound :
    ∀ (l : List DerpRegion) (rid : Nat) (region : DerpRegion),
      lookupRegion l rid = some region → region ∈ l ∧ region.regionID = rid := by
  intro l
  induction l with
  | nil =>
    intro rid region h
    simp only [lookupRegion] at h
    contradiction
  | cons hd tl ih =>
    intro rid region h
    simp only [lookupRegion] at h
    split at h
    · rename_i hcond
      injection h with h'
      subst h'
      exact ⟨List.mem_cons_self, hcond⟩
    · obtain ⟨hmem, hid⟩ := ih rid region h
      exact ⟨List.mem_cons_of_mem hd hmem, hid⟩

/-- **Lookup soundness.** A successful map lookup returns a real region of the
map whose id is exactly the one requested — the map never fabricates a region. -/
theorem derp_lookup_sound (dm : DerpMap) (rid : Nat) (region : DerpRegion)
    (h : dm.lookup rid = some region) :
    region ∈ dm.regions ∧ region.regionID = rid :=
  lookupRegion_sound dm.regions rid region h

/-- **A valid home is a real region.** If a node's home is valid then the map
actually contains a region with that home id — no dangling relay. -/
theorem derp_home_in_map (dm : DerpMap) (n : Node)
    (h : nodeHomeValid dm n = true) :
    ∃ region ∈ dm.regions, region.regionID = n.derp := by
  simp only [nodeHomeValid, DerpMap.hasRegion] at h
  cases hl : dm.lookup n.derp with
  | none =>
    rw [hl] at h
    simp at h
  | some region =>
    obtain ⟨hmem, hid⟩ := derp_lookup_sound dm n.derp region hl
    exact ⟨region, hmem, hid⟩

/-- **Fail-closed.** If the map has no region for a node's home id, the home is
invalid — a missing region can never read as a valid home. -/
theorem derp_no_region_home_invalid (dm : DerpMap) (n : Node)
    (h : dm.lookup n.derp = none) :
    nodeHomeValid dm n = false := by
  unfold nodeHomeValid DerpMap.hasRegion
  rw [h]
  rfl

/-- **Headline: every distributed peer routes to a real relay region.** In a
valid distribution, each peer in the netmap has a home DERP region that is a
genuine member of the distributed map. -/
theorem valid_distribution_peer_home (dm : DerpMap) (nm : NetMap)
    (h : validDistribution dm nm) :
    ∀ p ∈ nm.peers, ∃ region ∈ dm.regions, region.regionID = p.derp := by
  unfold validDistribution at h
  obtain ⟨_, hpeers⟩ := h
  intro p hp
  exact derp_home_in_map dm p (hpeers p hp)

#print axioms lookupRegion_sound
#print axioms derp_lookup_sound
#print axioms derp_home_in_map
#print axioms derp_no_region_home_invalid
#print axioms valid_distribution_peer_home

end Control.Derp
