/-
# NetmapLive — driving the PROVEN netmap fold over the byte level

The `Control` foundation models the coordination-server ("control plane") of a
mesh VPN as sans-IO, proven Lean. This lane is about the **format-agnostic
netmap layer** — the part that is reusable independent of any handshake or
crypto:

  * the netmap delta fold (`NetMap.applyDelta`): a `full` replaces the map, a
    `keepAlive` is identity, a `delta` adds/updates `changed` peers and drops
    `removed` ones (`netmap_keepAlive_id`, `netmap_full_replaces`,
    `netmap_delta_removes`);
  * cryptokey-routing translation (`NetMap.toWgPeers`): every authorized peer
    `Node` becomes a real `Wireguard.Peer.PeerCfg` (`wgpeers_complete`,
    `wgpeer_allowed_preserved`);
  * MagicDNS resolution (`DnsConfig.resolve`): a name → overlay-address lookup
    over the netmap's DNS records (`dns_resolve_sound`).

`ControlLive` already drives this through the ts2021 Noise-IK sealed channel —
but that path is crypto-bound (its selftest calls x25519 / chacha, so it can only
run as a built binary, NOT under the pure Lean interpreter). This lane isolates
the **inert, format-agnostic layer**: a self-delimiting `MapResponse` codec built
from the proven `Control` codec algebra (`putNat`/`putSeq`/`putNode`/… and their
round-trips), and a `selftest` that drives the WHOLE chain — encode a delta,
decode it, fold it, translate to WireGuard peers, resolve MagicDNS — with **no
crypto whatsoever**, so it runs under `lake env lean --run`.

## Honesty / realization boundary (the DnsResolveLive / DiscoLive discipline)

This is **drorb-native** and **pure**: the encoder and the decoder are our own
spec-conformant peers speaking a modelled binary framing (NOT the ts2021 sealed
channel, NOT real upstream coordination-server interop, which additionally needs
the byte-exact JSON wire and the Noise-IK seal — the named residual). No
socket, no FFI call: the reused C objects are linked only to satisfy the shared
executable link line. Everything structural/codec here is the proven Lean; the
gap the selftest discharges by construction (not by proof) is that this exe
faithfully CALLS the proven Lean functions on real bytes. The faithfulness of
the decode→fold→translate chain ITSELF is proven below as `netmap_fold_faithful`
(composing the wire-codec round-trip with the fold + translation + resolution).

Usage:
  netmap-live selftest
-/
import Control

namespace NetmapLive

open Control

/-! ## §1  A self-delimiting `MapResponse` codec, over the proven codec algebra

The `Control` foundation gives self-delimiting round-tripping codecs for every
field type (`putNat`/`getNat`, `putSeq`/`getSeq`, `putNode`/`getNode`,
`putNetMap`/`getNetMap`, …). We only need two new pieces — an optional-field codec
and a `PeerChange` codec — and then the three-arm `MapResponse` framing. Each
piece carries its own round-trip theorem, all chaining to `getMapResponse_put`. -/

/-- An optional field: a presence byte, then the value if present. -/
def putOption {α} (enc : α → Bytes) : Option α → Bytes
  | none   => putBool false
  | some a => putBool true ++ enc a

def getOption {α} (dec : Bytes → Option (α × Bytes)) (bs : Bytes) :
    Option (Option α × Bytes) :=
  match getBool bs with
  | some (false, r) => some (none, r)
  | some (true, r) =>
    match dec r with
    | some (a, r2) => some (some a, r2)
    | none => none
  | none => none

theorem getOption_putOption {α} (enc : α → Bytes) (dec : Bytes → Option (α × Bytes))
    (hrt : ∀ a t, dec (enc a ++ t) = some (a, t)) (o : Option α) (t : Bytes) :
    getOption dec (putOption enc o ++ t) = some (o, t) := by
  cases o with
  | none => simp [putOption, getOption, getBool_putBool]
  | some a =>
    have h1 : putOption enc (some a) ++ t = putBool true ++ (enc a ++ t) := by
      simp [putOption, List.append_assoc]
    rw [h1]
    simp only [getOption, getBool_putBool, hrt]

/-- The `Endpoint`-list codec used inside a `PeerChange` (an optional field of a
list of endpoints). -/
def putEndpoints (es : List Endpoint) : Bytes := putSeq putEndpoint es
def getEndpoints (bs : Bytes) : Option (List Endpoint × Bytes) := getSeq getEndpoint bs
theorem getEndpoints_put (es : List Endpoint) (t : Bytes) :
    getEndpoints (putEndpoints es ++ t) = some (es, t) :=
  getSeq_putSeq putEndpoint getEndpoint getEndpoint_put es t

/-- `tailcfg.PeerChange` framing: node id, then the three optional patched
fields (online / endpoints / node-key). The fold ignores the patch, but the
codec carries it faithfully so the full `MapResponse.delta` round-trips. -/
def putPeerChange (pc : PeerChange) : Bytes :=
  putNat pc.nodeID ++
  putOption putBool pc.online ++
  putOption putEndpoints pc.endpoints ++
  putOption putNodeKey pc.key

def getPeerChange (bs : Bytes) : Option (PeerChange × Bytes) := do
  let (nodeID, r) ← getNat bs
  let (online, r) ← getOption getBool r
  let (endpoints, r) ← getOption getEndpoints r
  let (key, r) ← getOption getNodeKey r
  some ({ nodeID, online, endpoints, key }, r)

theorem getPeerChange_put (pc : PeerChange) (t : Bytes) :
    getPeerChange (putPeerChange pc ++ t) = some (pc, t) := by
  obtain ⟨nodeID, online, endpoints, key⟩ := pc
  simp [putPeerChange, getPeerChange, List.append_assoc, getNat_putNat,
    getOption_putOption putBool getBool getBool_putBool,
    getOption_putOption putEndpoints getEndpoints getEndpoints_put,
    getOption_putOption putNodeKey getNodeKey getNodeKey_put]

/-- `tailcfg.MapResponse` framing: a tag byte selects the arm — `0` full netmap,
`1` incremental delta (changed ‖ removed ‖ patch), `2` bare keep-alive. -/
def putMapResponse : MapResponse → Bytes
  | .full nm => putNat 0 ++ putNetMap nm
  | .delta changed removed patch =>
      putNat 1 ++ putSeq putNode changed ++ putSeq putNat removed ++ putSeq putPeerChange patch
  | .keepAlive => putNat 2

def getMapResponse (bs : Bytes) : Option (MapResponse × Bytes) :=
  match getNat bs with
  | some (0, r) =>
    match getNetMap r with
    | some (nm, r2) => some (.full nm, r2)
    | none => none
  | some (1, r) => do
    let (changed, r) ← getSeq getNode r
    let (removed, r) ← getSeq getNat r
    let (patch, r) ← getSeq getPeerChange r
    some (.delta changed removed patch, r)
  | some (2, r) => some (.keepAlive, r)
  | _ => none

/-- **The `MapResponse` wire round-trip.** Every arm encodes then decodes back
verbatim, leaving the trailing bytes untouched — the workhorse the faithfulness
theorem composes with the fold. -/
theorem getMapResponse_put (m : MapResponse) (t : Bytes) :
    getMapResponse (putMapResponse m ++ t) = some (m, t) := by
  cases m with
  | full nm =>
    simp only [putMapResponse, getMapResponse, List.append_assoc, getNat_putNat, getNetMap_put]
  | delta changed removed patch =>
    simp [putMapResponse, getMapResponse, List.append_assoc, getNat_putNat,
      getSeq_putSeq putNode getNode getNode_put,
      getSeq_putSeq putNat getNat getNat_putNat,
      getSeq_putSeq putPeerChange getPeerChange getPeerChange_put]
  | keepAlive =>
    simp only [putMapResponse, getMapResponse, getNat_putNat]

/-! ## §2  The faithfulness theorem

The running loop's decode→fold→translate chain applies EXACTLY the proven
decision. Given any `MapResponse m` serialized by `putMapResponse` (into a buffer
with arbitrary trailing bytes `t`), decoding it with `getMapResponse`, folding it
into the current netmap `nm0` (`applyDelta`), translating to the WireGuard peer
table (`toWgPeers`), and resolving a MagicDNS `name` over the resulting DNS
config produces PRECISELY what the model computes by folding the SAME decision
`m` — the bytes on the wire realize the model, mediated only by the proven codec
round-trip (`getMapResponse_put`).

Not a `P → P`: it is inhabited (the selftest below produces such a buffer and
witnesses the equality on concrete bytes) and its content is the codec round-trip
composed with the fold, translation, and resolution — a real equation over every
`nm0`, `m`, `name`, and trailing `t`. -/
theorem netmap_fold_faithful (nm0 : NetMap) (m : MapResponse) (name t : Bytes) :
    (getMapResponse (putMapResponse m ++ t)).map
        (fun r => ((nm0.applyDelta r.1).toWgPeers, (nm0.applyDelta r.1).dns.resolve name))
      = some ((nm0.applyDelta m).toWgPeers, (nm0.applyDelta m).dns.resolve name) := by
  rw [getMapResponse_put m t]; rfl

/-- The decode→fold→translate chain alone (WireGuard peer table), the direct
analogue of `ControlLive.control_applies_netmap_faithfully` but over the pure
(crypto-free) `MapResponse` codec. -/
theorem netmap_wgpeers_faithful (nm0 : NetMap) (m : MapResponse) (t : Bytes) :
    (getMapResponse (putMapResponse m ++ t)).map (fun r => (nm0.applyDelta r.1).toWgPeers)
      = some (nm0.applyDelta m).toWgPeers := by
  rw [getMapResponse_put m t]; rfl

/-! ## §3  Byte helpers (pure; mirrors DnsResolveLive) -/

def toHex (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.toList.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

def toHexL (b : Bytes) : String := toHex ⟨b.toArray⟩

/-- Render a byte list that is UTF-8 text as text (for names), else hex. -/
def textOrHex (b : Bytes) : String := (String.fromUTF8? ⟨b.toArray⟩).getD (toHexL b)

/-- A fixed 32-byte placeholder key value. -/
def dummyKey (v : UInt8) : Bytes := List.replicate 32 v

/-- A netmap node with the fixed scaffolding filled in. -/
def mkNode (id : Nat) (name : String) (keyByte : UInt8) (v4 : Bytes) : Node :=
  { id, stableID := s!"stable-{id}".toUTF8.toList, name := name.toUTF8.toList, user := 1,
    key := ⟨dummyKey keyByte⟩, machine := ⟨dummyKey (keyByte + 1)⟩, disco := ⟨dummyKey (keyByte + 2)⟩,
    addresses  := [{ addr := v4, bits := 32 }],
    allowedIPs := [{ addr := v4, bits := 32 }],
    endpoints  := [{ addr := [192,168,1,50], port := 41641 }],
    derp := 1, online := true, keyExpiry := 0, authorized := true }

/-! ## §4  The selftest — the netmap fold over the byte level, one process, NO crypto -/

def selftest : IO UInt32 := do
  IO.println "== netmap-live selftest : format-agnostic netmap fold, byte-level, NO crypto =="

  -- ── the node's current netmap, before folding the server's delta ──
  let selfNode := mkNode 0 "self.example.ts.net" 0x10 [100,64,0,1]
  let peerOld  := mkNode 7 "old.example.ts.net"  0x20 [100,64,0,7]   -- to be REMOVED by the delta
  let peerKeep := mkNode 9 "keep.example.ts.net" 0x30 [100,64,0,9]   -- survives (not touched)
  let peerNew  := mkNode 42 "peer.example.ts.net" 0xab [100,64,0,2]  -- ADDED by the delta
  let dns0 : DnsConfig :=
    { domains := ["example.ts.net".toUTF8.toList],
      records := [(peerNew.name, [100,64,0,2]), (peerKeep.name, [100,64,0,9])] }
  let nm0 : NetMap :=
    { self := selfNode, peers := [peerOld, peerKeep], dns := dns0, packetFilter := [] }

  IO.println s!"\n-- initial netmap (before fold) --"
  IO.println s!"peers                  : {nm0.peers.map (fun p => textOrHex p.name)}"

  -- ── the incremental delta: add peerNew, remove peerOld (a field patch rides along) ──
  let patch : PeerChange :=
    { nodeID := peerKeep.id, online := some false, endpoints := none, key := none }
  let delta : MapResponse := .delta [peerNew] [peerOld.id] [patch]

  -- ENCODE it with the proven codec algebra, DECODE it back
  let wire := putMapResponse delta
  IO.println s!"\n-- delta serialized (putMapResponse) --"
  IO.println s!"wire bytes             : {wire.length}B  {toHexL (wire.take 24)}…"
  let some (decoded, rest) := getMapResponse wire
    | do IO.eprintln "getMapResponse FAILED to decode the delta"; return 1
  let decodeOk := (rest.isEmpty) && (putMapResponse decoded == putMapResponse delta)
  IO.println s!"getMapResponse∘putMapResponse == delta (wire round-trip realized) : {decodeOk}"
  if !decodeOk then do IO.eprintln "delta did NOT round-trip"; return 1

  -- ── fold the DECODED delta, translate to WG peers, resolve MagicDNS ──
  let nmApplied := nm0.applyDelta decoded
  let wgPeers   := nmApplied.toWgPeers
  let dnsResult := nmApplied.dns.resolve peerNew.name

  IO.println s!"\n-- netmap folded (decode → applyDelta → toWgPeers → resolve) --"
  IO.println s!"peers after fold       : {nmApplied.peers.map (fun p => textOrHex p.name)}"
  IO.println s!"removed peer gone       : {!(nmApplied.peers.map (·.id)).contains peerOld.id}"
  IO.println s!"survivor kept           : {(nmApplied.peers.map (·.id)).contains peerKeep.id}"
  IO.println s!"new peer present        : {(nmApplied.peers.map (·.id)).contains peerNew.id}"
  for p in wgPeers do
    let cidrs := p.allowed.map (fun c => s!"{c.addr}/{c.plen}")
    IO.println s!"  WG peer  spub={toHex p.spub}  allowedIPs={cidrs}"
  match dnsResult with
  | some addr => IO.println s!"MagicDNS resolve       : {textOrHex peerNew.name} -> {addr}"
  | none      => IO.println s!"MagicDNS resolve       : {textOrHex peerNew.name} -> (no record)"

  -- ── the faithfulness cross-check: wire decode∘fold∘toWgPeers∘resolve == model ──
  -- `netmap_fold_faithful` PROVES these are equal for the serialized buffer; here
  -- we witness it on the concrete bytes (spub key lists + resolved address).
  let nmModel   := nm0.applyDelta delta
  let modelWg   := nmModel.toWgPeers
  let modelDns  := nmModel.dns.resolve peerNew.name
  let wireKeys  := wgPeers.map (fun p => p.spub.toList)
  let modelKeys := modelWg.map (fun p => p.spub.toList)
  let faithful  := (wireKeys == modelKeys) && !wgPeers.isEmpty
  let dnsFaithful := dnsResult == modelDns
  let dnsExpected := dnsResult == some ([100,64,0,2] : Bytes)

  IO.println s!"\n-- cross-check (realizes netmap_fold_faithful) --"
  IO.println s!"wire WG peers == model WG peers  : {wireKeys == modelKeys}"
  IO.println s!"wire DNS == model DNS            : {dnsFaithful}"
  IO.println s!"WG peer table non-empty          : {!wgPeers.isEmpty}"
  IO.println s!"MagicDNS resolved 100.64.0.2     : {dnsExpected}"

  -- ── the two definitional laws, byte-level: keepAlive is identity, full replaces ──
  let some (kaDecoded, _) := getMapResponse (putMapResponse .keepAlive)
    | do IO.eprintln "getMapResponse FAILED on keepAlive"; return 1
  let kaId := (nm0.applyDelta kaDecoded).peers.map (·.id) == nm0.peers.map (·.id)
  let fullMap : NetMap := { self := selfNode, peers := [peerNew], dns := dns0, packetFilter := [] }
  let some (fullDecoded, _) := getMapResponse (putMapResponse (.full fullMap))
    | do IO.eprintln "getMapResponse FAILED on full"; return 1
  let fullReplaces := (nm0.applyDelta fullDecoded).peers.map (·.id) == [peerNew.id]
  IO.println s!"\n-- byte-level definitional laws --"
  IO.println s!"keepAlive is identity on netmap  : {kaId}"
  IO.println s!"full replaces the netmap         : {fullReplaces}"

  if decodeOk && faithful && dnsFaithful && dnsExpected && kaId && fullReplaces then do
    IO.println "\nPASS — delta serialized, decoded, folded; WG peers programmed, MagicDNS resolved;"
    IO.println "       the decode→fold→toWgPeers→resolve chain equals the proven model decision."
    IO.println "NETMAP FOLD LIVE-WIRED (drorb-native, byte-level, NO crypto, verified codec+fold)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the netmap-fold pipeline did not cross-check."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do
    IO.eprintln "usage: netmap-live selftest"
    return 1

end NetmapLive

def main (args : List String) : IO UInt32 := NetmapLive.main args
