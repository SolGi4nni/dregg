/-
# KeyRotateLive — driving PROVEN node-key rotation over the netmap, byte-level, NO crypto

The coordination server keeps a **registry** (`Control.ControlState.nodes`): each
node is a `Control.Registration` keyed by its overlay/WireGuard node key
(`Control.NodeKey`), carrying its netmap record (`Control.Node`, with the stable
`id` / `stableID` / owning `user` that survive a re-key) and an authorization
status. When a node **re-keys** — presenting its previous key as the login's
`oldNodeKey` — the server re-keys the existing entry to the new node key while
preserving the node's stable identity: a rename of the registration, NOT a new
node. The old key is thereafter retired (it resolves to nothing, so no netmap is
ever served under it again).

This lane isolates that rotation as sans-IO, proven Lean and drives it over the
byte level. The rotation logic itself is the ground-truth foundation
`Control.Register.rotateKey` / `rotateReg` and its identity theorem
`Control.Register.rotate_preserves_identity`; this file adds:

  * `keyrotate_preserves_identity` — after `rotateKey old new`, the *new* key
    resolves to a registration keyed by `new` that carries the SAME stable
    `id`, owning `user`, `stableID`, AND authorization `status` as the old entry
    (identity + authorization survive the re-key; only the key changes). A
    strengthening of the foundation's `rotate_preserves_identity`.
  * `keyrotate_retires_old` — after `rotateKey old new` (with `old ≠ new`), the
    *old* key resolves to `none`: it is fully retired from the registry, so a
    map-poll under the old key can only be `reject`ed.
  * `keyrotate_serves_new` — end-to-end through `Control.step`: an authorized
    node that re-keys is served its full netmap under the new key, and that
    netmap's `self` record carries the preserved identity (`id`/`user`).
  * `keyrotate_old_rejected` — end-to-end: a map-poll under the retired old key
    yields `.reject` (no netmap), composing `keyrotate_retires_old` with `step`.

## Honesty / realization boundary (the NetmapLive / PeerDiscoveryLive discipline)

This is **native** and **PURE**: `rotateKey`, `lookupReg`, and `step` all run in
this one process over the modelled Lean values. NO socket, NO FFI, NO crypto —
the rotation is a registry/identity computation that calls zero `@[extern]`
opaques — so the selftest runs under `lake env lean --run`. Everything
structural here is the proven Lean; the faithfulness of the rotation itself is
proven below, and the selftest witnesses those equalities on concrete values.

Interop against a live coordination server (which additionally needs the ts2021
Noise-IK sealed channel and the byte-exact JSON login/`MapResponse` wire) is a
named residual — the socket/crypto-bound analogue is the built `ControlLive`
binary, which cannot run under the pure interpreter. There is deliberately NO
deployed HTTP endpoint that emits raw netmap key-rotation: on the wire it is
carried inside the sealed control channel, out of scope for this crypto-free
logic lane. What runs here is exactly what is proven here.

Usage:
  key-rotate-live selftest
-/
import Control
import Control.Register

namespace Mesh
namespace KeyRotateLive

open Control
open Control.Register

/-! ## §1  Retiring the old key: a proven registry lemma

After mapping every registration through `rotateReg old new`, no registration is
keyed by `old` any more (each `old`-keyed entry becomes `new`-keyed, and no other
entry ever acquires key `old`), provided `old ≠ new`. Hence the first-match
lookup of `old` finds nothing. This is the exact dual of the foundation's
`lookupReg_map_rotate` (which tracks where the NEW key lands). -/
theorem lookupReg_map_rotate_old_none (old new : NodeKey) (hne : old ≠ new) :
    ∀ (l : List Registration),
      lookupReg (l.map (rotateReg old new)) old = none := by
  intro l
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp only [List.map_cons, lookupReg]
    have hkey : (rotateReg old new h).nodeKey ≠ old := by
      by_cases hho : h.nodeKey = old
      · simp only [rotateReg, if_pos hho]; exact fun hc => hne hc.symm
      · simp only [rotateReg, if_neg hho]; exact hho
    rw [if_neg hkey]
    exact ih

/-! ## §2  The two required rotation theorems -/

/-- **Rotation preserves identity (and authorization).** If `old` was registered
and `new` was not, then after `rotateKey old new` the *new* key resolves to a
registration that is keyed by `new` yet carries the SAME stable `node.id`, owning
`node.user`, opaque `node.stableID`, and authorization `status` as the old entry.
A re-key renames the registration and moves the key it is filed under; it changes
nothing about who the node is or whether it is authorized. Strengthens the
foundation's `Control.Register.rotate_preserves_identity` (which pins `id`/`user`)
with `stableID` and `status`. -/
theorem keyrotate_preserves_identity (old new : NodeKey) (s : ControlState)
    (r0 : Registration)
    (hold : lookupReg s.nodes old = some r0)
    (hnew : lookupReg s.nodes new = none) :
    ∃ r', lookupReg (rotateKey old new s).nodes new = some r'
        ∧ r'.nodeKey = new
        ∧ r'.node.id = r0.node.id
        ∧ r'.node.user = r0.node.user
        ∧ r'.node.stableID = r0.node.stableID
        ∧ r'.status = r0.status := by
  have hk : r0.nodeKey = old := lookupReg_nodeKey s.nodes old r0 hold
  refine ⟨rotateReg old new r0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [rotateKey] using lookupReg_map_rotate old new s.nodes r0 hold hnew
  · simp [rotateReg, hk]
  · simp [rotateReg, hk]
  · simp [rotateReg, hk]
  · simp [rotateReg, hk]
  · simp [rotateReg, hk]

/-- **Rotation retires the old key.** After `rotateKey old new` (with a genuine
re-key, `old ≠ new`), the *old* key resolves to `none`: it is gone from the
registry. Every entry that was filed under `old` has been re-keyed to `new`, and
nothing else ever acquires key `old`. -/
theorem keyrotate_retires_old (old new : NodeKey) (s : ControlState)
    (hne : old ≠ new) :
    lookupReg (rotateKey old new s).nodes old = none := by
  simp only [rotateKey]
  exact lookupReg_map_rotate_old_none old new hne s.nodes

/-! ## §3  End-to-end through `Control.step`: the served netmap

The two theorems above are registry facts; these lift them through the actual
serving transition `Control.step` (`.mapPoll`), so they speak about the netmap a
polling node actually receives. -/

/-- **The re-keyed node is served under its new key, with its identity intact.**
If `old` was an *authorized* registration and `new` was free, then after
`rotateKey old new` a map-poll presenting the new key produces a full netmap
whose `self` record carries the SAME `id` and owning `user` as the pre-rotation
entry. Composes `keyrotate_preserves_identity` with `step`'s authorized-serve
branch. -/
theorem keyrotate_serves_new (pol : Policy) (old new : NodeKey) (s : ControlState)
    (r0 : Registration) (req : MapRequest)
    (hold : lookupReg s.nodes old = some r0)
    (hnew : lookupReg s.nodes new = none)
    (hauth : r0.status = .authorized)
    (hreq : req.nodeKey = new) :
    ∃ nm : NetMap,
      (step pol (rotateKey old new s) (.mapPoll req)).2 = .mapResp (.full nm)
      ∧ nm.self.id = r0.node.id
      ∧ nm.self.user = r0.node.user := by
  obtain ⟨r', hlook, _hkey, hid, huser, _hsid, hstatus⟩ :=
    keyrotate_preserves_identity old new s r0 hold hnew
  refine ⟨buildNetMap (rotateKey old new s) r', ?_, ?_, ?_⟩
  · have hla : lookupReg (rotateKey old new s).nodes req.nodeKey = some r' := by
      rw [hreq]; exact hlook
    simp only [step, hla]
    rw [hstatus, hauth]
    simp [NodeStatus.isAuthorized]
  · simpa [buildNetMap] using hid
  · simpa [buildNetMap] using huser

/-- **A poll under the retired old key is rejected — no netmap.** After
`rotateKey old new` (with `old ≠ new`), a map-poll presenting the old key can
only yield `.reject`: the key resolves to nothing, so `step` takes its
`none`-branch. Composes `keyrotate_retires_old` with `step`. -/
theorem keyrotate_old_rejected (pol : Policy) (old new : NodeKey) (s : ControlState)
    (req : MapRequest)
    (hne : old ≠ new)
    (hreq : req.nodeKey = old) :
    (step pol (rotateKey old new s) (.mapPoll req)).2 = .reject := by
  have hnone : lookupReg (rotateKey old new s).nodes req.nodeKey = none := by
    rw [hreq]; exact keyrotate_retires_old old new s hne
  simp only [step, hnone]

/-! ## §4  Byte helpers (pure; mirrors NetmapLive) -/

def toHex (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.toList.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

def toHexL (b : Bytes) : String := toHex ⟨b.toArray⟩

def textOrHex (b : Bytes) : String := (String.fromUTF8? ⟨b.toArray⟩).getD (toHexL b)

/-- A fixed 32-byte placeholder key value (a distinct byte per key). -/
def mkKey (v : UInt8) : NodeKey := ⟨List.replicate 32 v⟩

/-- A netmap node with the fixed scaffolding filled in. -/
def mkNode (id : Nat) (name : String) (user : Nat) (key : NodeKey) (v4 : Bytes) : Node :=
  { id, stableID := s!"stable-{id}".toUTF8.toList, name := name.toUTF8.toList, user,
    key, machine := ⟨List.replicate 32 0xEE⟩, disco := ⟨List.replicate 32 0xDD⟩,
    addresses  := [{ addr := v4, bits := 32 }],
    allowedIPs := [{ addr := v4, bits := 32 }],
    endpoints  := [{ addr := [192,168,1,50], port := 41641 }],
    derp := 1, online := true, keyExpiry := 0, authorized := true }

/-- An authorized registration keyed by `key`. -/
def mkReg (key : NodeKey) (node : Node) : Registration :=
  { nodeKey := key, node, status := .authorized }

/-- A one-shot map-poll request presenting `key`. -/
def mkPoll (key : NodeKey) : MapRequest :=
  { version := 1, nodeKey := key, discoKey := ⟨List.replicate 32 0xDD⟩,
    endpoints := [], stream := false, omitPeers := false, readOnly := true }

/-- Render a registration as `id@keyprefix` (avoids nested string interpolation). -/
def regTag (r : Registration) : String :=
  let idStr := toString r.node.id
  idStr ++ "@" ++ toHexL (r.nodeKey.pub.take 2)

/-! ## §5  The selftest — node-key rotation over the netmap, one process, NO crypto -/

def selftest : IO UInt32 := do
  IO.println "== key-rotate-live selftest : node-key rotation over the netmap, NO crypto =="

  -- ── the registry before rotation: three authorized nodes ──
  let oldKey := mkKey 0x11        -- the node that will re-key
  let newKey := mkKey 0x22        -- its fresh key (not yet in the registry)
  let otherKey := mkKey 0x33      -- an untouched neighbour
  let selfKey := mkKey 0x44       -- the polling self-node

  let nodeR  := mkNode 7  "rekeying.example.net"  100 oldKey   [100,64,0,7]
  let nodeO  := mkNode 9  "neighbour.example.net" 100 otherKey [100,64,0,9]
  let nodeS  := mkNode 1  "self.example.net"      100 selfKey  [100,64,0,1]
  let regR := mkReg oldKey nodeR
  let regO := mkReg otherKey nodeO
  let regS := mkReg selfKey nodeS
  let dns0 : DnsConfig := { domains := ["example.net".toUTF8.toList], records := [] }
  let s0 : ControlState := { nodes := [regR, regO, regS], filter := [], dns := dns0 }
  let pol : Policy := { authorizes := fun _ _ => true }

  IO.println s!"\n-- registry before rotation --"
  IO.println s!"nodes (id@key)         : {s0.nodes.map regTag}"
  IO.println s!"rekeying node          : id={nodeR.id} user={nodeR.user} stable={textOrHex nodeR.stableID}"
  IO.println s!"old key                : {toHexL (oldKey.pub.take 4)}…"
  IO.println s!"new key                : {toHexL (newKey.pub.take 4)}…"

  -- sanity: old key present, new key absent (the rotate_preserves_identity hyps)
  let oldPresent := (lookupReg s0.nodes oldKey).isSome
  let newAbsent  := (lookupReg s0.nodes newKey).isNone
  IO.println s!"old key registered      : {oldPresent}"
  IO.println s!"new key free            : {newAbsent}"

  -- ── ROTATE: old → new (the oldNodeKey re-key login) ──
  let s1 := rotateKey oldKey newKey s0

  IO.println s!"\n-- registry after rotateKey old→new --"
  IO.println s!"nodes (id@key)         : {s1.nodes.map regTag}"

  -- (a) identity preserved under the NEW key
  let rNewOpt := lookupReg s1.nodes newKey
  let identityOk :=
    match rNewOpt with
    | some r' => r'.nodeKey == newKey && r'.node.id == nodeR.id
                 && r'.node.user == nodeR.user && r'.node.stableID == nodeR.stableID
                 && (r'.status == NodeStatus.authorized)
    | none => false
  IO.println s!"new key resolves        : {rNewOpt.isSome}"
  IO.println s!"  → same id/user/stable/status (keyrotate_preserves_identity) : {identityOk}"

  -- (b) old key RETIRED
  let oldRetired := (lookupReg s1.nodes oldKey).isNone
  IO.println s!"old key retired (→none) : {oldRetired}  (keyrotate_retires_old)"

  -- (c) the neighbour is untouched
  let neighbourKept :=
    match lookupReg s1.nodes otherKey with
    | some r => r.node.id == nodeO.id
    | none => false
  IO.println s!"neighbour untouched     : {neighbourKept}"

  -- ── END-TO-END through Control.step: what the polling node actually receives ──
  IO.println s!"\n-- served netmap (Control.step .mapPoll) --"

  -- new key polls → full netmap, self identity intact
  let servedNew := (step pol s1 (.mapPoll (mkPoll newKey))).2
  let servesUnderNew :=
    match servedNew with
    | .mapResp (.full nm) => nm.self.id == nodeR.id && nm.self.user == nodeR.user
    | _ => false
  IO.println s!"poll(new key) serves netmap w/ preserved identity : {servesUnderNew}  (keyrotate_serves_new)"

  -- old key polls → reject (retired)
  let servedOld := (step pol s1 (.mapPoll (mkPoll oldKey))).2
  let oldRejected := match servedOld with | .reject => true | _ => false
  IO.println s!"poll(old key) rejected (no netmap)                : {oldRejected}  (keyrotate_old_rejected)"

  -- the re-keyed node is still an authorized peer of the self-node, under the new key
  let selfServed := (step pol s1 (.mapPoll (mkPoll selfKey))).2
  let peerRekeyed :=
    match selfServed with
    | .mapResp (.full nm) =>
      (nm.peers.filter (fun p => p.id == nodeR.id)).any (fun p => p.key == newKey)
    | _ => false
  IO.println s!"re-keyed node appears as peer under NEW key        : {peerRekeyed}"

  IO.println s!"\n-- cross-check: selftest values realize the proven theorems --"
  IO.println s!"identityOk        (keyrotate_preserves_identity) : {identityOk}"
  IO.println s!"oldRetired        (keyrotate_retires_old)        : {oldRetired}"
  IO.println s!"servesUnderNew    (keyrotate_serves_new)         : {servesUnderNew}"
  IO.println s!"oldRejected       (keyrotate_old_rejected)       : {oldRejected}"

  if oldPresent && newAbsent && identityOk && oldRetired && neighbourKept
     && servesUnderNew && oldRejected && peerRekeyed then do
    IO.println "\nPASS — node re-keyed old→new: netmap entry updated, identity + authorization"
    IO.println "       preserved, old key retired; served under the new key, rejected under the old."
    IO.println "KEY-ROTATION LIVE-WIRED (native, NO crypto, verified rotation + netmap serve)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the key-rotation pipeline did not cross-check."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do
    IO.eprintln "usage: key-rotate-live selftest"
    return 1

end KeyRotateLive
end Mesh

def main (args : List String) : IO UInt32 := Mesh.KeyRotateLive.main args

#print axioms Mesh.KeyRotateLive.lookupReg_map_rotate_old_none
#print axioms Mesh.KeyRotateLive.keyrotate_preserves_identity
#print axioms Mesh.KeyRotateLive.keyrotate_retires_old
#print axioms Mesh.KeyRotateLive.keyrotate_serves_new
#print axioms Mesh.KeyRotateLive.keyrotate_old_rejected
