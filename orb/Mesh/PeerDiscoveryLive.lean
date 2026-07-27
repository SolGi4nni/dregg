/-
# PeerDiscoveryLive — driving PROVEN peer discovery over the netmap, byte-level, NO crypto

The coordination server hands each node a **netmap** (`Control.NetMap`): its own
record, its authorized peers (each a `Control.Node` with identity keys, overlay
addresses, and candidate direct endpoints), plus DNS and packet-filter. **Peer
discovery** is the node-side derivation *from that netmap* of the set of
reachable peers and, per peer, the candidate endpoints to try — the input the
DISCO probing FSM (`Disco`) then works on. This lane isolates that derivation as
sans-IO, proven Lean and drives it over the byte level.

The derivation is deliberately inert and crypto-free: from a `NetMap`, `discover`
projects each peer `Node` to a `DiscoveredPeer` (its stable id, node key, and
candidate endpoints). Two facts pin it down:

  * `discovery_reflects_netmap` — the reachable-peer view is *exactly* the
    netmap's peer list, key-for-key and endpoint-for-endpoint, in order:
    discovery neither invents, drops, nor reorders a reachable peer, and carries
    each one's endpoints faithfully.
  * `discovery_drops_removed` — after folding a `MapResponse.delta` that removes
    a peer id (and does not re-add it under `changed`), NO discovered peer
    carries that id: a peer removed from the netmap is dropped from discovery.
    Composes `Control.netmap_delta_removes`.

And the security seam to DISCO (why "reachable" is not "usable"):

  * `discovery_seeds_unprobed` — seeding a discovered endpoint into the DISCO
    candidate table enters it `unprobed`; selection will NOT put it into use
    until a Pong verifies it. Discovery makes a peer *reachable* (a candidate);
    it does NOT authenticate a path. The anti-spoof gate
    (`Disco.disco_no_promote_without_pong`) still holds. Composes the Control
    netmap layer with the Disco probing FSM — the two ground-truth stones.

## Honesty / realization boundary (the NetmapLive / RelayMeshLive discipline)

This is **drorb-native** and **pure**: `discover`, the fold, and the DISCO
seeding all run in this one process over the modelled Lean values (no socket, no
FFI, no crypto — a discovery derivation calls zero `@[extern]` opaques), so the
selftest runs under `lake env lean --run`. Everything structural here is the
proven Lean; the faithfulness of the derivation itself is proven below, and the
selftest witnesses those equalities on concrete values. Interop against a live
coordination server (which additionally needs the ts2021 Noise-IK sealed channel
and the byte-exact JSON `MapResponse` wire) is a named residual — the
socket/crypto-bound analogue is `ControlLive` (built binary, cannot run under the
pure interpreter).

Usage:
  peer-discovery-live selftest
-/
import Control
import Disco

namespace PeerDiscoveryLive

open Control

/-! ## §1  The derivation: reachable peers + their endpoints, from the netmap -/

/-- One discovered peer: its stable numeric id, its overlay/WireGuard node key,
and the candidate direct endpoints to probe (`Control.Node.endpoints`). This is
exactly the slice of a netmap `Node` peer discovery yields to the DISCO FSM. -/
structure DiscoveredPeer where
  id        : Nat
  key       : NodeKey
  endpoints : List Endpoint
deriving Repr, DecidableEq

/-- **Peer discovery over the netmap.** The reachable-peer view derived from a
netmap: each authorized peer `Node` becomes a `DiscoveredPeer` carrying its id,
node key, and candidate endpoints. Order- and multiplicity-preserving. -/
def discover (nm : NetMap) : List DiscoveredPeer :=
  nm.peers.map (fun n => { id := n.id, key := n.key, endpoints := n.endpoints })

/-! ## §2  Faithfulness — discovery reflects the netmap, and drops removed peers -/

/-- **Discovery reflects the netmap.** The reachable peers derived from a netmap
are exactly its peer list — same node keys and same candidate endpoints, in the
same order. Discovery neither fabricates, drops, nor reorders a reachable peer,
and carries each one's endpoints verbatim. A real equation over every `nm`, not
`P → P`: the selftest witnesses it on a concrete netmap. -/
theorem discovery_reflects_netmap (nm : NetMap) :
    (discover nm).map (fun d => (d.key, d.endpoints))
      = nm.peers.map (fun n => (n.key, n.endpoints)) := by
  simp only [discover, List.map_map]
  rfl

/-- **A discovered peer is a genuine netmap peer.** Every discovered entry comes
from a peer node actually in the netmap — no phantom peers. -/
theorem discovery_sound (nm : NetMap) (d : DiscoveredPeer) (hd : d ∈ discover nm) :
    ∃ n ∈ nm.peers, d.id = n.id ∧ d.key = n.key ∧ d.endpoints = n.endpoints := by
  simp only [discover, List.mem_map] at hd
  obtain ⟨n, hn, rfl⟩ := hd
  exact ⟨n, hn, rfl, rfl, rfl⟩

/-- **A peer removed from the netmap is dropped from discovery.** After folding a
`MapResponse.delta` that removes id `id` and does not re-add it (it is not among
the delta's `changed` full records), NO discovered peer carries that id — the
departed peer vanishes from the reachable set. Composes
`Control.netmap_delta_removes`; the non-re-add hypothesis is the genuine
side-condition (a delta may remove then re-announce). Not `P → P`. -/
theorem discovery_drops_removed (nm : NetMap) (changed : List Node) (removed : List Nat)
    (patch : List PeerChange) (id : Nat) (hid : id ∈ removed)
    (hnadd : id ∉ changed.map (·.id)) :
    ∀ d ∈ discover (nm.applyDelta (.delta changed removed patch)), d.id ≠ id := by
  intro d hd hdid
  simp only [discover, List.mem_map] at hd
  obtain ⟨n, hn, rfl⟩ := hd
  -- d = ⟨n.id, n.key, n.endpoints⟩, so hdid : n.id = id
  have hnid : n.id = id := hdid
  have hnc : n ∈ changed :=
    Control.netmap_delta_removes nm changed removed patch id hid n hn hnid
  exact hnadd (List.mem_map.mpr ⟨n, hnc, hnid⟩)

/-! ## §3  The seam to DISCO — a discovered endpoint is a candidate, not a path

Discovery says which peers are reachable and hands the DISCO FSM their candidate
endpoints. It does NOT authenticate a path: an endpoint learned from the netmap
enters the candidate table `unprobed` and is used only after a Pong verifies it.
This composes the Control netmap layer with the Disco probing FSM. -/

/-- Fold a `Control.Endpoint` (address bytes + UDP port) into the opaque `addr`
the DISCO FSM keys candidates on. -/
def toDiscoEndpoint (e : Control.Endpoint) : Disco.Endpoint :=
  { addr := (e.addr.foldl (fun a b => a * 256 + b.toNat) 0) * 65536 + e.port }

/-- **A discovered endpoint is only a candidate — it still needs a Pong.**
Seeding a discovered endpoint into the DISCO candidate table adds it `unprobed`,
and selection will NOT put it into use until a Pong verifies it. Discovery
determines *reachability*; it does not authenticate a *path*. The anti-spoofing
discipline (`Disco.disco_no_promote_without_pong`) still gates the endpoint —
mirrors `Disco.disco_reflexive_needs_pong` for a netmap-discovered candidate. -/
theorem discovery_seeds_unprobed (cfg : Disco.Config) (s : Disco.St) (e : Control.Endpoint)
    (hnew : Disco.lookup s.eps (toDiscoEndpoint e) = none) :
    Disco.lookup (Disco.step cfg s (.addCandidate (toDiscoEndpoint e))).1.eps
        (toDiscoEndpoint e) = some Disco.EpState.unprobed ∧
    Disco.Output.usePath (toDiscoEndpoint e)
      ∉ (Disco.step cfg (Disco.step cfg s (.addCandidate (toDiscoEndpoint e))).1
          .selectPath).2 := by
  have hstep : (Disco.step cfg s (.addCandidate (toDiscoEndpoint e))).1
      = { eps := (toDiscoEndpoint e, Disco.EpState.unprobed) :: s.eps } := by
    simp [Disco.step, hnew]
  rw [hstep]
  refine ⟨by simp [Disco.lookup], ?_⟩
  intro hmem
  obtain ⟨lat, hin⟩ := Disco.disco_no_promote_without_pong cfg _ (toDiscoEndpoint e) hmem
  rcases List.mem_cons.mp hin with heq | htl
  · injection heq with _ h2; exact absurd h2 (by simp)
  · exact Disco.lookup_none_not_mem hnew (Disco.EpState.verified lat) htl

/-! ## §4  Byte / rendering helpers (pure; mirrors NetmapLive / RelayMeshLive) -/

def toHex (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.toList.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

def toHexL (b : Bytes) : String := toHex ⟨b.toArray⟩

def textOrHex (b : Bytes) : String := (String.fromUTF8? ⟨b.toArray⟩).getD (toHexL b)

/-- A fixed 32-byte placeholder key value. -/
def dummyKey (v : UInt8) : Bytes := List.replicate 32 v

/-- A netmap node with the fixed scaffolding filled in and distinct endpoints. -/
def mkNode (id : Nat) (name : String) (keyByte : UInt8) (v4 : Bytes) (epLast : UInt8) : Node :=
  { id, stableID := s!"stable-{id}".toUTF8.toList, name := name.toUTF8.toList, user := 1,
    key := ⟨dummyKey keyByte⟩, machine := ⟨dummyKey (keyByte + 1)⟩, disco := ⟨dummyKey (keyByte + 2)⟩,
    addresses  := [{ addr := v4, bits := 32 }],
    allowedIPs := [{ addr := v4, bits := 32 }],
    endpoints  := [{ addr := [192, 168, 1, epLast], port := 41641 }],
    derp := 1, online := true, keyExpiry := 0, authorized := true }

/-! ## §5  The selftest — peer discovery over the netmap, one process, NO crypto -/

def selftest : IO UInt32 := do
  IO.println "== peer-discovery-live selftest : reachable peers + endpoints from the netmap, NO crypto =="

  -- ── the node's current netmap, before folding the server's delta ──
  let selfNode := mkNode 0 "self.example.ts.net" 0x10 [100,64,0,1] 10
  let peerOld  := mkNode 7 "old.example.ts.net"  0x20 [100,64,0,7] 70   -- REMOVED by the delta
  let peerKeep := mkNode 9 "keep.example.ts.net" 0x30 [100,64,0,9] 90   -- survives untouched
  let peerNew  := mkNode 42 "peer.example.ts.net" 0xab [100,64,0,2] 42  -- ADDED by the delta
  let dns0 : DnsConfig := DnsConfig.empty
  let nm0 : NetMap :=
    { self := selfNode, peers := [peerOld, peerKeep], dns := dns0, packetFilter := [] }

  -- ── discover the reachable peers from the current netmap ──
  let disc0 := discover nm0
  IO.println s!"\n-- discovery over the initial netmap --"
  for d in disc0 do
    let eps := d.endpoints.map (fun ep => s!"{ep.addr}:{ep.port}")
    IO.println s!"  reachable id={d.id}  key={toHexL (d.key.pub.take 4)}…  endpoints={eps}"

  -- discovery_reflects_netmap, witnessed on the concrete netmap (keys + endpoints)
  let discKeys  := disc0.map (fun d => (d.key.pub, d.endpoints.map (·.addr)))
  let peerKeys  := nm0.peers.map (fun n => (n.key.pub, n.endpoints.map (·.addr)))
  let reflects  := discKeys == peerKeys
  IO.println s!"\n-- cross-check (realizes discovery_reflects_netmap) --"
  IO.println s!"discovered keys+endpoints == netmap peers : {reflects}"
  IO.println s!"reachable count == netmap peer count       : {disc0.length == nm0.peers.length}"

  -- ── fold a delta: remove peerOld, add peerNew (a field patch rides along) ──
  let patch : PeerChange :=
    { nodeID := peerKeep.id, online := some false, endpoints := none, key := none }
  let delta : MapResponse := .delta [peerNew] [peerOld.id] [patch]
  let nmApplied := nm0.applyDelta delta
  let disc1 := discover nmApplied

  IO.println s!"\n-- discovery after the delta (remove peerOld, add peerNew) --"
  for d in disc1 do
    IO.println s!"  reachable id={d.id}  name-key={toHexL (d.key.pub.take 2)}…"
  let discIds  := disc1.map (·.id)
  let removedGone := !discIds.contains peerOld.id
  let newPresent  := discIds.contains peerNew.id
  let keepPresent := discIds.contains peerKeep.id
  IO.println s!"\n-- cross-check (realizes discovery_drops_removed) --"
  IO.println s!"removed peer (id 7) dropped from discovery : {removedGone}"
  IO.println s!"added peer (id 42) present                 : {newPresent}"
  IO.println s!"untouched peer (id 9) still reachable      : {keepPresent}"

  -- ── the DISCO seam: a discovered endpoint is only a candidate (unprobed) ──
  -- Seed peerNew's discovered endpoint into an empty DISCO table; it enters
  -- `unprobed`, and selection does NOT put it into use (no Pong yet).
  let cfg : Disco.Config := { authPong := fun _ _ => false }
  let some dNew := disc1.find? (fun d => d.id == peerNew.id)
    | do IO.eprintln "added peer not discovered — cannot seed DISCO"; return 1
  let some ep0 := dNew.endpoints.head?
    | do IO.eprintln "discovered peer has no endpoint to seed"; return 1
  let dep := toDiscoEndpoint ep0
  let seeded := Disco.step cfg Disco.init (.addCandidate dep)
  let stAfter := seeded.1
  let isUnprobed := Disco.lookup stAfter.eps dep == some Disco.EpState.unprobed
  let selectOut := (Disco.step cfg stAfter .selectPath).2
  let noUse := !(selectOut.contains (Disco.Output.usePath dep))
  IO.println s!"\n-- DISCO seam (realizes discovery_seeds_unprobed) --"
  IO.println s!"discovered endpoint seeds candidate UNPROBED : {isUnprobed}"
  IO.println s!"selection does NOT use it (needs a Pong)     : {noUse}"

  if reflects && (disc0.length == nm0.peers.length) && removedGone && newPresent
     && keepPresent && isUnprobed && noUse then do
    IO.println "\nPASS — reachable peers + endpoints derived from the netmap exactly match it;"
    IO.println "       a peer removed from the netmap is dropped from discovery; a discovered"
    IO.println "       endpoint enters DISCO unprobed and is not used until a Pong verifies it."
    IO.println "PEER DISCOVERY LIVE-WIRED (drorb-native, byte-level, NO crypto, verified over Control+Disco)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the peer-discovery pipeline did not cross-check."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do
    IO.eprintln "usage: peer-discovery-live selftest"
    return 1

end PeerDiscoveryLive

def main (args : List String) : IO UInt32 := PeerDiscoveryLive.main args
