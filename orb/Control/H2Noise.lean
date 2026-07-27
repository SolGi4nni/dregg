/-
# Control.H2Noise — HTTP/2 over the ts2021 Noise channel: the LAST transport layer

After the byte-exact `Noise_IK` handshake (`Control.Channel.Ts2021.step` → `.up`,
`ControlLive.control_handshake_refines`), a stock tailscale client does NOT send
raw framed control messages. It opens an **HTTP/2 session with prior knowledge**
INSIDE the noise channel and issues the control RPCs as h2 requests:

  * `POST /machine/register`  — body = `json.Marshal(RegisterRequest)`, response =
    `json.Unmarshal` of the body (`control/controlclient/direct.go` @v1.98.8:
    `url = "%s/machine/register"` (L787), `bodyData = encode(request)` = plain
    `json.Marshal` (L1469 `encode`), `decode(res,&resp)` = plain `json.Unmarshal`
    (L1416 `decode`)).
  * `POST /machine/map` (`Stream:true`) — body = `json.Marshal(MapRequest)` with
    `request.Compress = "zstd"` (direct.go L1123); the response body is a stream of
    `[u32-LE length][zstd frame]` messages, each a compressed JSON `MapResponse`
    (`binary.LittleEndian.Uint32(siz)` L1256, `decodeMsg` = `zstdframe.AppendDecode`
    then `json.Unmarshal` L1434).

The h2 transport is **prior-knowledge h2c**: `control/ts2021/client.go` @v1.98.8
builds `&http.Transport{Protocols: new(http.Protocols)}` and calls
`tr.Protocols.SetUnencryptedHTTP2(true)` (L165-172) — the client sends the 24-byte
HTTP/2 client preface directly on the noise `net.Conn`, no HTTP/1.1 Upgrade, no TLS
ALPN. That is EXACTLY what drorb's verified engine `H2.Conn.feed` consumes
(`clientPreface`, `feed_preface_invalid`).

## What this module is

The verified composition that turns the decrypted noise record stream into an h2
session and routes the control RPCs to the PROVEN coordination:

  1. `recordWireFrame`/`recordWireDeframe` — the `controlbase` record wire framing
     `[msgType=4][len:u16BE][sealed]` (`control/controlbase/messages.go`:
     `msgTypeRecord=4`, `headerLen=3`, `maxMessageSize=4096`), proven inverse.
  2. `mkHandler` — the `H2.Conn.Handler` that routes `POST /machine/register` to the
     PROVEN pre-auth gate (`Control.PreAuth.registerWithPreAuth`) and
     `POST /machine/map` to the PROVEN coordination netmap, emitting JSON (via the
     proven `Control.Tailcfg` codec + `TailcfgWire.renderStr`) as the h2 response.
  3. `registerDecide_gate` — the load-bearing theorem: the register RPC's decision
     over the wire is EXACTLY the proven gate's `machineAuthorized`, mediated only by
     the proven JSON round-trips (`parseStr_renderStr`, `fromJson?_toJson`).

The h2 engine's own correctness (`H2.Conn.feed`, its RFC-obligation theorems), the
record layer (`Control.Ts2021Record.record_roundtrip`), the pre-auth gate
(`registerWithPreAuth` / `preauth_matches_policy_step`) and the JSON codec
(`*.fromJson?_toJson`) are UNCHANGED and load-bearing here — this module COMPOSES
them; it does not reimplement any of them.

## Realization boundary (named, honest)

* The **zstd frame** wrapping each `MapResponse` (`zstdRawFrame`) is a raw-block
  zstd container built host-side — a deterministic byte layout the stock decoder
  (`klauspost/compress/zstd` via `zstdframe.AppendDecode`) accepts. It carries no
  drorb refinement (like the record wire framing and the HTTP head parse); it is
  cross-checked my-hand against stock `zstd -d`.
* The **map netmap→wire projection** is now the PROVEN `Control.Join.servedNetMapWire`
  (`servedNetMapWire_filters` / `servedWireA_filter_is_acl_compile`): the served
  `MapResponse` carries the ACL-compiler `PacketFilters["base"]`, the proven netmap
  peers/DNS, drorb's DERP, and the polling node's PROVEN IPAM `/32` (`Control.Ipam`).
  The hand-built `mapResponseWire` residual is REMOVED (see §5).
* The record open/seal and the h2 feed are CALLED by the untrusted IO loop
  (`ControlLive.h2coord`); that the socket moves those bytes faithfully is
  discharged by construction (the live run), exactly as the handshake shim is.
-/
import Control.PreAuthKey
import Control.Join
import Control.Expiry
import Control.Ipam
import Control.Tailcfg
import Control.TailcfgWire
import Control.TailcfgBridge
import Control.Ts2021Record
import Control.Ts2021Core
import H2.Conn
import H2.HpackEncode
import Reactor.H2
import Crypto

namespace Control.H2Noise

open Control (Bytes)
open Control.Tailcfg (Json)

/-! ## §1  Byte helpers -/

/-- UTF-8 bytes of a string as the engine's `List UInt8`. -/
def s2b (s : String) : List UInt8 := s.toUTF8.toList

/-- Decode a byte list as a UTF-8 string, if it is valid UTF-8. -/
def b2s (b : List UInt8) : Option String := String.fromUTF8? ⟨b.toArray⟩

/-- The model's abstract `hash`, instantiated with HACL*/EverCrypt SHA-256
(F*-verified) — exactly `ControlLive.sha256Bytes` / `PreAuthMintTool.sha256Bytes`. -/
def sha256Bytes (b : Bytes) : Bytes := (Crypto.sha256 ⟨b.toArray⟩).toList

/-! ## §2  The `controlbase` record wire framing (host message-boundary metadata)

`[msgType=4][len:u16BE][sealed]` (`control/controlbase/messages.go`: `msgTypeRecord
= 4`, `headerLen = 3`; `control/controlbase/conn.go`: `maxMessageSize = 4096`, the
`len` field is the ciphertext length). This is the same byte-boundary metadata the
Rust host framer (`crates/dataplane/src/control.rs` `record_frame`) writes; the
sealed payload itself is produced/consumed only by the verified AEAD. -/

def msgTypeRecord : UInt8 := 4
def recordHeaderLen : Nat := 3
def maxMessageSize : Nat := 4096

/-- Frame one already-sealed record payload: `[4][len:u16BE][sealed]`. -/
def recordWireFrame (sealed : List UInt8) : List UInt8 :=
  msgTypeRecord :: UInt8.ofNat (sealed.length / 256) :: UInt8.ofNat (sealed.length % 256) :: sealed

/-- Deframe the leading record off a wire prefix: the sealed payload and the octet
count consumed, or `none` if the prefix is not (yet) one complete, well-typed
record. Total and bounded. -/
def recordWireDeframe (pfx : List UInt8) : Option (List UInt8 × Nat) :=
  match pfx with
  | t :: hi :: lo :: rest =>
    if t = msgTypeRecord then
      let len := hi.toNat * 256 + lo.toNat
      if len + recordHeaderLen ≤ maxMessageSize ∧ len ≤ rest.length then
        some (rest.take len, recordHeaderLen + len)
      else none
    else none
  | _ => none

/-! ### The record AEAD — the PROVEN counter-managed record layer (glue removed)

★ FINDING (this lane): the earlier `sealRecordRaw`/`openRecordRaw` here were a
raw-ChaCha workaround, needed because `Control.Ts2021Record.sealRecord`/`openRecord`
wrap the ciphertext in a drorb-native `[recordTag=3][uvarint len][ct]` frame INSIDE
the record — NOT the ts2021 wire. That workaround is now REMOVED. The live record
path is `Control.Ts2021Record.sealRecordTs2021` / `openRecordTs2021`: the
counter-managed entry points over `Control.Ts2021Wire.sealRecord` / `openRecord`,
which are the byte-exact `controlbase` framing `[type=4][u16 BE len][raw ciphertext]`
(`Ts2021Wire.parseRecord_encodeRecord`, `Ts2021Wire.record_seal_open`), with the
big-endian record nonce (`recordNonce`) and empty AAD — exactly `encryptLocked`.
`record_roundtrip_ts2021` closes the AEAD round-trip over that framing. The live IO
loop (`ControlLive.h2Loop` / `sendH2Out`) drives those proven entry points directly;
no raw seal/open remains here. -/

/-- **The record wire framing round-trips.** A sealed payload that fits a record
(`len ≤ maxMessageSize - 3`) frames and deframes back to exactly itself, consuming
exactly `3 + len` octets, for any trailing bytes. Not a `P → P`: it is the concrete
byte inverse the IO loop relies on. -/
theorem recordWireDeframe_frame (sealed rest : List UInt8)
    (hlen : sealed.length + recordHeaderLen ≤ maxMessageSize) :
    recordWireDeframe (recordWireFrame sealed ++ rest) = some (sealed, recordHeaderLen + sealed.length) := by
  have e256 : (UInt8.size : Nat) = 256 := rfl
  have h256 : sealed.length < 65536 := by
    simp only [maxMessageSize, recordHeaderLen] at hlen; omega
  have hhi : (UInt8.ofNat (sealed.length / 256)).toNat = sealed.length / 256 :=
    UInt8.toNat_ofNat_of_lt (by rw [e256]; omega)
  have hlo : (UInt8.ofNat (sealed.length % 256)).toNat = sealed.length % 256 :=
    UInt8.toNat_ofNat_of_lt (by rw [e256]; omega)
  have hrecon : sealed.length / 256 * 256 + sealed.length % 256 = sealed.length :=
    Nat.div_add_mod' _ _
  have hcond : sealed.length + recordHeaderLen ≤ maxMessageSize ∧ sealed.length ≤ (sealed ++ rest).length :=
    ⟨hlen, by simp⟩
  have htake : (sealed ++ rest).take sealed.length = sealed := List.take_left ..
  simp only [recordWireFrame, recordWireDeframe, List.cons_append, hhi, hlo, hrecon,
    if_pos hcond, htake, if_true]

/-! ## §3  h2 response builders (pre-encoded HPACK blocks) -/

/-- A 200 response header block for a JSON body: `:status: 200`, `content-type:
application/json`, HPACK-encoded (literal without indexing — `H2.HpackEncode`). -/
def okJsonBlock : List UInt8 :=
  H2.HpackEncode.encodeHeaders [(s2b ":status", s2b "200"), (s2b "content-type", s2b "application/json")]

/-- A 200 response block for the map long-poll body (opaque octet stream). -/
def okStreamBlock : List UInt8 :=
  H2.HpackEncode.encodeHeaders [(s2b ":status", s2b "200"),
    (s2b "content-type", s2b "application/octet-stream")]

/-- A 404 response block. -/
def notFoundBlock : List UInt8 :=
  H2.HpackEncode.encodeHeaders [(s2b ":status", s2b "404")]

/-! ## §4  The register RPC — routed to the PROVEN pre-auth gate

`Control.PreAuth.registerWithPreAuth` is the proven admission door (a valid pre-auth
key ⇒ `MachineAuthorized`; `preauth_matches_policy_step` forbids bypass). The wire
`RegisterRequest` JSON is decoded by the proven `Control.Tailcfg` codec; the pre-auth
secret is the UTF-8 bytes of the `Auth.AuthKey` string (headscale hashes the key
string), so the coord's key store (`mint sha256Bytes secret`) matches. -/

/-- The coord's fixed configuration for a registration decision.

`derp` is the **advertised** DERPMap — the region/endpoint a served `MapResponse`
tells the client to dial. It defaults to `Control.Join.drorbDerpMap` (loopback
`127.0.0.1:3340`), which is right for a same-host plane; the live serve overrides it
with `Control.Join.drorbDerpMapAt <host>` from `DRORB_DERP_ADDR` so a client on
ANOTHER host is handed a REACHABLE relay instead of its own loopback. Only the
advertised endpoint IP varies: `servedMapForAt_filter_is_acl_compile` /
`servedMapForAt_self_addr` / `servedMapForAt_peer_addr` below are proven `∀ dm`, so
the ACL, addressing, and peer views are INVARIANT under this knob. -/
structure Cfg where
  store   : Control.PreAuth.Store
  control : Control.ControlState
  now     : Nat
  derp    : Control.Derp.DerpMap := Control.Join.drorbDerpMap
  baseURL : String := ""  -- control URL for interactive-enrolment AuthURL (default: unset)

/-- Bridge a wire `Tailcfg.RegisterRequest` to the coordination core's
`Control.RegisterRequest`. The `authKey` bytes are the UTF-8 of the `Auth.AuthKey`
string; the node key is decoded from `"nodekey:<hex>"` (`Control.Bridge.NodeKey.ofText`,
proven inverse), 32 zero bytes if malformed (the decision keys on `authKey`, not the
node key — `validate` inspects only the key). -/
def coreOf (rr : Control.Tailcfg.RegisterRequest) : Control.RegisterRequest :=
  let authKey : Bytes := s2b ((rr.auth.bind (·.authKey)).getD "")
  let nk : Bytes := (Control.Bridge.NodeKey.ofText rr.nodeKey).getD (List.replicate 32 0)
  { version := rr.version, nodeKey := ⟨nk⟩, oldNodeKey := ⟨[]⟩,
    machineKey := ⟨List.replicate 32 0⟩, authKey := authKey,
    expiry := 0, ephemeral := rr.ephemeral, followup := false }

/-- Decide the register RPC from the request-body JSON string: parse (proven codec),
bridge, run the PROVEN gate, and surface `machineAuthorized`. A malformed body is a
clean `false` (not admitted). -/
def registerDecide (cfg : Cfg) (bodyStr : String) : Bool :=
  match Control.TailcfgWire.parseStr bodyStr with
  | some j =>
    match Control.Tailcfg.RegisterRequest.fromJson? j with
    | some rr =>
      -- ★INTERACTIVE ENROLMENT admission: the proven pre-auth gate ADMITS, OR the operator
      -- already authorized this node in the durable registry (`.authorized`, the door
      -- `drorb-ctl nodes approve` opens). Mirrors the allocFor gate at ControlLive.lean.
      (Control.PreAuth.registerWithPreAuth sha256Bytes cfg.store cfg.control cfg.now (coreOf rr)).response.machineAuthorized
        || (match Control.lookupReg cfg.control.nodes (coreOf rr).nodeKey with
            | some r => r.status.isAuthorized
            | none   => false)
    | none => false
  | none => false

/-- **The register RPC over the wire IS the proven gate.** For any wire
`RegisterRequest rr`, the decision `registerDecide` computes on `rr`'s marshaled JSON
equals `registerWithPreAuth`'s `machineAuthorized` on the bridged core request —
mediated only by the proven `parseStr ∘ renderStr = id` and `fromJson? ∘ toJson = id`.
Load-bearing: it composes the JSON codec round-trips with the pre-auth gate. -/
theorem registerDecide_gate (cfg : Cfg) (rr : Control.Tailcfg.RegisterRequest) :
    registerDecide cfg (Control.TailcfgWire.renderStr (Control.Tailcfg.RegisterRequest.toJson rr))
      = ((Control.PreAuth.registerWithPreAuth sha256Bytes cfg.store cfg.control cfg.now (coreOf rr)).response.machineAuthorized
          || (match Control.lookupReg cfg.control.nodes (coreOf rr).nodeKey with
              | some r => r.status.isAuthorized
              | none   => false)) := by
  simp only [registerDecide, Control.TailcfgWire.parseStr_renderStr,
    Control.Tailcfg.RegisterRequest.fromJson?_toJson]

/-- **Operator approval admits over the wire.** If the operator has already authorized
the node (`.authorized` in the durable registry — the door `drorb-ctl nodes approve`
opens), the register RPC's wire decision is `true` regardless of the pre-auth key. This
is the load-bearing half FIX 1 adds: a keyless-approved node reaches `MachineAuthorized`,
so the client reaches Running. (`registerDecide_gate` remains the exact wire↔decision
equation; this is its operator-side corollary.) -/
theorem registerDecide_operator_admits (cfg : Cfg) (rr : Control.Tailcfg.RegisterRequest)
    (r : Control.Registration)
    (hlk : Control.lookupReg cfg.control.nodes (coreOf rr).nodeKey = some r)
    (hauth : r.status.isAuthorized = true) :
    registerDecide cfg (Control.TailcfgWire.renderStr (Control.Tailcfg.RegisterRequest.toJson rr)) = true := by
  simp only [registerDecide_gate, hlk, hauth, Bool.or_true]

/-- The register RPC's h2 response: `RegisterResponse{MachineAuthorized}` as JSON,
framed by the engine as HEADERS + DATA. -/
def registerRsp (cfg : Cfg) (body : List UInt8) : H2.Conn.Rsp :=
  let authorized := (b2s body).elim false (registerDecide cfg)
  -- ★INTERACTIVE ENROLMENT (keyless). An UNAUTHORIZED register (no valid pre-auth key)
  -- is handed an AuthURL `<DRORB_CONTROL_URL>/register/<nonce>`, nonce = the node-key hex
  -- (the value `drorb-ctl nodes approve <nonce>` matches, `nodes pending` prints). A stock
  -- `tailscale up` PRINTS this URL and holds until the operator approves. `authorized` is
  -- UNCHANGED (still `= registerDecide cfg body`, so `registerDecide_gate` holds); we only
  -- ADD the AuthURL. An authorized register (valid pre-auth key) gets `authURL := none`.
  let authURL : Option String :=
    if authorized then none
    else
      (do let s ← b2s body
          let j ← Control.TailcfgWire.parseStr s
          let rr ← Control.Tailcfg.RegisterRequest.fromJson? j
          let nkHex := (Control.Bridge.NodeKey.toText (coreOf rr).nodeKey.pub).drop 8
          if cfg.baseURL.isEmpty then none else some s!"{cfg.baseURL}/register/{nkHex}")
  let resp : Control.Tailcfg.RegisterResponse :=
    { authURL := authURL, nodeKeyExpired := false, machineAuthorized := authorized }
  let json := Control.TailcfgWire.renderStr (Control.Tailcfg.RegisterResponse.toJson resp)
  { block := okJsonBlock, body := s2b json, status := 200 }

/-! ## §5  The map RPC — the served netmap as an h2 long-poll body

The response body is one `[u32-LE len][zstd frame]` message carrying a JSON
`MapResponse`. The netmap→wire projection is the PROVEN `Control.Join.servedNetMapWire`
(`servedNetMapWire_filters`): `PacketFilters["base"]` = the ACL-compiler output, peers
+ DNS from the proven netmap, the DERP region NAMES drorb's own verified relay
`127.0.0.1:3340` (`Control.Join.drorbDerp*`), and the polling node's address is a PROVEN
`Control.Ipam` allocation. No hand-built self view remains. -/

/-- 4-byte little-endian length prefix (the stock client reads `binary.LittleEndian`,
direct.go L1256). -/
def u32le (n : Nat) : List UInt8 :=
  [UInt8.ofNat (n % 256), UInt8.ofNat (n / 256 % 256),
   UInt8.ofNat (n / 65536 % 256), UInt8.ofNat (n / 16777216 % 256)]

/-- Split a byte list into raw-block-sized chunks (≤ 65535 ≤ 128 KiB block max). -/
partial def rawChunks : List UInt8 → List (List UInt8)
  | [] => []
  | xs => xs.take 65535 :: rawChunks (xs.drop 65535)

/-- One zstd raw-block frame header: `[Block_Size:21 << 3 | Raw(0)<<1 | Last]` as a
3-byte little-endian `Block_Header` (RFC 8878 §3.1.1.2). -/
def rawBlockHeader (size : Nat) (last : Bool) : List UInt8 :=
  let v := size * 8 + (if last then 1 else 0)   -- Block_Type = 0 (Raw_Block)
  [UInt8.ofNat (v % 256), UInt8.ofNat (v / 256 % 256), UInt8.ofNat (v / 65536 % 256)]

/-- A minimal zstd frame containing `data` as raw (uncompressed) blocks: Magic
`0xFD2FB528`, `Frame_Header_Descriptor = 0x00` (no dict, no checksum, not
single-segment), `Window_Descriptor = 0x60` (windowLog 22 = 4 MiB, so Block_Maximum
= 128 KiB), then raw blocks with `Last_Block` on the final one. Accepted by the stock
`klauspost/compress/zstd` decoder (`zstdframe.AppendDecode`). Host codec — cross-checked
my-hand against stock `zstd -d`; carries no drorb refinement. -/
partial def zstdRawFrame (data : List UInt8) : List UInt8 :=
  let magic : List UInt8 := [0x28, 0xB5, 0x2F, 0xFD]
  let hdr   : List UInt8 := [0x00, 0x60]  -- FHD, Window_Descriptor
  let chunks := match rawChunks data with | [] => [[]] | cs => cs   -- at least one (empty) block
  let n := chunks.length
  let blocks := (chunks.zipIdx).flatMap (fun (c, i) =>
    rawBlockHeader c.length (i + 1 = n) ++ c)
  magic ++ hdr ++ blocks

/-! ### The served netmap is the PROVEN `Control.Join.servedNetMapWire`

The hand-built `mapResponseWire` is REPLACED by `Control.Join.servedNetMapWire` —
the wire refinement of the coordination `NetMap` whose `PacketFilters["base"]` IS
the ACL-compiler output (`Control.Join.servedWireA_filter_is_acl_compile`), with
peers / DNS / DERP projected from the proven netmap.

★ MULTI-NODE FIX (this lane). The earlier `servedMapFor` UPSERTED the polling node with a
constant `pollIp = cgnatPool.alloc []` (deterministically `100.64.0.1`) on EVERY poll —
so every distinct node re-registered as `100.64.0.1` and multi-node was broken (the
`GROUND` the lane names). That constant-address self-injection is REMOVED. `servedMapFor`
is now literally `Control.Join.servedNetMapWire base k`: it serves the polling node's
registration **out of the PERSISTENT `base` ControlState** — the node the live coordinator
has already IPAM-allocated (`Control.Ipam.cgnatPool.alloc (usedOf …)`) and persisted
(`Control.Store.Event.addrAllocated`, stamped by `Store.applyEvent`). So node X is served
its OWN stable address as Self and the OTHER registered nodes as Peers (each at its own
distinct address + tags + the ACL). Distinctness is `Control.Ipam.liveAlloc_distinct`;
stability across X's separate register/map connections is `Control.Store.addrAllocated_stable`. -/

/-- **The served `MapResponse` IS `Control.Join.servedNetMapWire`** over the PERSISTENT
coordination state: the polling node `k` is looked up in `base` (where the live
coordinator has already registered + IPAM-addressed it) and served its stable address as
Self, with the other registered nodes as Peers. An unknown key gets the empty response. -/
def servedMapFor (base : Control.ControlState) (k : Control.NodeKey) : Control.Tailcfg.MapResponse :=
  Control.Join.servedNetMapWire base k

/-- **The served `MapResponse` over an ARBITRARY ADVERTISED DERPMap** — the SAME proven
projection `Control.Join.servedNetMapWireAt`, parameterized by the DERPMap the client is
told to dial. The live serve passes `Control.Join.drorbDerpMapAt <DRORB_DERP_ADDR>` so a
cross-host client gets a reachable relay; `servedMapFor` is exactly this at the loopback
`drorbDerpMap`. -/
def servedMapForAt (dm : Control.Derp.DerpMap) (base : Control.ControlState)
    (k : Control.NodeKey) : Control.Tailcfg.MapResponse :=
  Control.Join.servedNetMapWireAt dm base k

/-- `servedMapFor` IS `servedMapForAt drorbDerpMap` — threading the advertised addr
generalizes the served map, it does not replace it. -/
theorem servedMapFor_eq_at : servedMapFor = servedMapForAt Control.Join.drorbDerpMap := rfl

/-- Decode a wire `"nodekey:<hex>"` to the coordination core `NodeKey` (proven
inverse `Control.Bridge.NodeKey.ofText`); 32 zero bytes if malformed. -/
def coreKeyOf (nkStr : String) : Control.NodeKey :=
  ⟨(Control.Bridge.NodeKey.ofText nkStr).getD (List.replicate 32 0)⟩

/-- The map RPC's h2 response body: `[u32-LE len][zstd(JSON MapResponse)]`, the
`MapResponse` now the PROVEN `Control.Join.servedNetMapWire`. -/
def mapRsp (cfg : Cfg) (body : List UInt8) : H2.Conn.Rsp :=
  let reqOpt : Option Control.Tailcfg.MapRequest :=
    (do let s ← b2s body
        let j ← Control.TailcfgWire.parseStr s
        Control.Tailcfg.MapRequest.fromJson? j)
  let nkStr := (reqOpt.map (·.nodeKey)).getD "nodekey:00"
  -- A `MapRequest{Stream:true}` is a LONG-POLL: keep the h2 stream open so the
  -- coord can push updated MapResponses (peer joins) as DATA frames on it. The
  -- first response is the full netmap; deltas are pushed by `ControlLive.pushLoop`.
  let streaming := (reqOpt.map (·.stream)).getD false
  let k := coreKeyOf nkStr
  -- ★SELF-EXPIRY at the INITIAL serve (stream open). If THIS polling node's OWN key is
  -- expired in the durable registry (`drorb-ctl nodes expire` -> `Register.expire` ->
  -- `.expired`), serve the PROVEN re-auth response (`Control.Expiry.reauthResponse`: the
  -- self node MachineAuthorized=false + online=false, peers=none -- `expired_self_reauth`)
  -- instead of a stale authorized netmap. `finalizeReg` stamps `node.authorized := true`
  -- (=> wire MachineAuthorized=true) even on an expired node, so without this a client
  -- RECONNECTING after `nodes expire` bounces straight back to Running; the reauth wire
  -- overrides MachineAuthorized=false so it re-authenticates (NeedsLogin). An authorized
  -- or still-PENDING self is served the ordinary `servedMapForAt` (its proofs stand --
  -- this only diverts the `.expired` self).
  let mr := match Control.lookupReg cfg.control.nodes k with
    | some r =>
      if decide (r.status = Control.NodeStatus.expired)
      then Control.Expiry.reauthResponse r
      else servedMapForAt cfg.derp cfg.control k
    | none => servedMapForAt cfg.derp cfg.control k
  let json := Control.TailcfgWire.renderStr
    (Control.TailcfgWire.dropNulls (Control.Tailcfg.MapResponse.toJson mr))
  let z := zstdRawFrame (s2b json)
  { block := okStreamBlock, body := u32le z.length ++ z, status := 200, keepOpen := streaming }

/-! ## §6  The h2 handler — routing the control RPCs -/

/-- The `H2.Conn.Handler` a drorb coord serves over the noise channel: route
`POST /machine/register` to the proven gate and `POST /machine/map` to the served
netmap; everything else is `404`. The engine owns the h2 protocol; this owns the
content. -/
def mkHandler (cfg : Cfg) : H2.Conn.Handler := fun req =>
  if req.method = s2b "POST" ∧ req.target = s2b "/machine/register" then
    registerRsp cfg req.body
  else if req.method = s2b "POST" ∧ req.target = s2b "/machine/map" then
    mapRsp cfg req.body
  else
    { block := notFoundBlock, body := [], status := 404 }

/-- The HPACK decoder the engine reads request header blocks with — the deployed
gateway decoder (`Reactor.H2.h2Huffman`, RFC 7541 Huffman). -/
def decoder : H2.Hpack.HuffmanDecoder := Reactor.H2.h2Huffman

/-- Drive one chunk of decrypted noise-record plaintext into the h2 engine, returning
the successor connection state, the h2 output octets to seal back, and the close flag.
This is `H2.Conn.feed` at the deployment site — the verified engine, unmodified. -/
def feedChunk (cfg : Cfg) (st : H2.Conn.ConnState) (plaintext : List UInt8) :
    H2.Conn.ConnState × List UInt8 × Bool :=
  H2.Conn.feed decoder (mkHandler cfg) st plaintext

/-! ## §7  Executable my-hand demonstration (drives the REAL engine + REAL gate) -/

/-- The demo pre-auth secret (UTF-8 of a `tskey`-style string), and the coord config
whose key store holds ONLY its SHA-256 hash. -/
def demoSecretStr : String := "tskey-auth-drorb-h2noise-selftest"
def demoAttrs : Control.PreAuth.KeyAttrs :=
  { reusable := true, ephemeral := false, expiry := 0, tags := [], user := 0 }
def demoCfg : Cfg :=
  { store := [Control.PreAuth.mint sha256Bytes (s2b demoSecretStr) demoAttrs],
    control := Control.Join.coordState Control.Acl.demoPolicy Control.Join.demoDomains [],
    now := 1000 }

/-- A wire `RegisterRequest` presenting the demo pre-auth key. -/
def demoRegReq : Control.Tailcfg.RegisterRequest :=
  { version := 138, nodeKey := "nodekey:" ++ String.ofList (List.replicate 64 '1'),
    auth := some { authKey := some demoSecretStr } }

/-- A wire `RegisterRequest` presenting a WRONG key. -/
def demoBadReq : Control.Tailcfg.RegisterRequest :=
  { demoRegReq with auth := some { authKey := some "tskey-auth-WRONG" } }

-- The proven gate admits the valid key and rejects the wrong one THROUGH the wire
-- JSON round-trip (`registerDecide_gate` witnessed on concrete requests). These are
-- driven at RUNTIME in `ControlLive.h2selftest` because the decision calls EverCrypt
-- SHA-256 (`Crypto.sha256`, `@[extern]`), which the elaborator's interpreter cannot
-- run; the linked `control-live` exe evaluates them my-hand (see report).

-- The record wire framing round-trips on a concrete sealed payload (pure — checked
-- at elaboration time):
#guard recordWireDeframe (recordWireFrame (List.replicate 80 0x41) ++ [0xAA, 0xBB]) = some (List.replicate 80 0x41, 83)

/-! ### The served-map composition theorems — the wire ACL IS the proven compile -/

/-- The demo coordination control state (ACL-compiled filter + MagicDNS), the same
`Control.Join.coordState` the live `h2coord` builds. -/
def demoControl : Control.ControlState :=
  Control.Join.coordState Control.Acl.demoPolicy Control.Join.demoDomains []

/-- A concrete polling node key (32 bytes) for the runtime demonstrations. -/
def demoPollKey : Control.NodeKey := ⟨List.replicate 32 0x2a⟩
/-- A second registered node key, so the served map has a real PEER. -/
def demoPeerKey : Control.NodeKey := ⟨List.replicate 32 0x3b⟩

/-- A registered, IPAM-addressed node — the shape the live coordinator persists (a
`Store.nodeRegistered` node stamped by a `Store.addrAllocated` event, `Ipam.stampV4`),
homed on drorb's DERP region. `ip` is the node's PROVEN IPAM allocation. -/
def regNodeAt (k : Control.NodeKey) (id ip : Nat) (nm : String) : Control.Registration :=
  { nodeKey := k, status := .authorized,
    node := Control.Ipam.stampV4
      { id := id, stableID := s2b nm, name := s2b nm, user := 1,
        key := k, machine := ⟨k.pub⟩, disco := ⟨List.replicate 32 0⟩,
        addresses := [], allowedIPs := [], endpoints := [],
        derp := Control.Join.drorbRegionID, online := true, keyExpiry := 0,
        authorized := true, tags := [] } ip }

/-- The PERSISTENT demo coordination state: two IPAM-addressed nodes — the poll node at its
stable `100.64.0.1` and a peer at `100.64.0.2` — with the ACL-compiled filter + MagicDNS.
This is the shape the live `h2coordMulti` accept loop rebuilds from the replayed durable
log on each connection. -/
def demoControlReg : Control.ControlState :=
  Control.Join.coordState Control.Acl.demoPolicy Control.Join.demoDomains
    [ regNodeAt demoPollKey 1 Control.Ipam.ip1 "node-1.ts.net"
    , regNodeAt demoPeerKey 2 Control.Ipam.ip2 "node-2.ts.net" ]

/-- **IPAM produced the served addresses.** The two nodes' stable addresses are exactly
the proven `Control.Ipam.cgnatPool` allocator's first two free addresses — `100.64.0.1`
then `100.64.0.2` allocated against the first (`liveAlloc_distinct` makes them distinct). -/
theorem demo_addrs_are_ipam_alloc :
    Control.Ipam.cgnatPool.alloc [] = some Control.Ipam.ip1
    ∧ Control.Ipam.cgnatPool.alloc [Control.Ipam.ip1] = some Control.Ipam.ip2 := by
  constructor <;> native_decide

/-- **★ THE SERVED-MAP ACL THEOREM.** For the registered poll key, the served map's
`PacketFilters["base"]` equals the ACL-compiler output `compiledPacketFilter
Acl.demoPolicy` (= `(Acl.compile demoPolicy).map ruleConv`, about which
`Control.Acl.policy_default_deny` / `policy_allow_iff_entry` are load-bearing),
projected to the wire — composed through `Control.Join.servedNetMapWire_filters`.
The client receives the PROVEN default-deny compilation, never a hand-built filter. -/
theorem servedMapFor_filter_is_acl_compile :
    (servedMapFor demoControlReg demoPollKey).packetFilters
      = some [("base", (Control.Join.compiledPacketFilter Control.Acl.demoPolicy).map
                Control.Join.filterRuleToWire)] := by
  have h : Control.lookupReg demoControlReg.nodes demoPollKey
      = some (regNodeAt demoPollKey 1 Control.Ipam.ip1 "node-1.ts.net") := by
    simp [demoControlReg, Control.Join.coordState, Control.lookupReg, regNodeAt]
  rw [servedMapFor, Control.Join.servedNetMapWire_filters _ _ _ h]
  rfl

/-- **The served self node is addressed by ITS OWN stable IPAM `/32`.** The map served to
the poll node carries `100.64.0.1/32` — the `Control.Ipam` allocation persisted for THAT
node, not a per-poll constant. -/
theorem servedMapFor_self_addr :
    (servedMapFor demoControlReg demoPollKey).node.map (·.addresses) = some ["100.64.0.1/32"] := by
  native_decide

/-- **★ MULTI-NODE: distinct self, mutual peer.** The map served to the poll node carries
the OTHER registered node as a Peer at its OWN distinct address `100.64.0.2/32` — so two
nodes get DISTINCT addresses and SEE each other (the gate, at the wire-projection level). -/
theorem servedMapFor_peer_addr :
    (servedMapFor demoControlReg demoPollKey).peers.map (·.map (·.addresses))
      = some [["100.64.0.2/32"]] := by native_decide

/-- **The peer's map, symmetrically, serves the poll node back as its peer at `.1`.** -/
theorem servedMapFor_peer_view :
    (servedMapFor demoControlReg demoPeerKey).node.map (·.addresses) = some ["100.64.0.2/32"]
    ∧ (servedMapFor demoControlReg demoPeerKey).peers.map (·.map (·.addresses))
        = some [["100.64.0.1/32"]] := by
  constructor <;> native_decide

/-- **The served self node is machine-authorized.** -/
theorem servedMapFor_self_authorized :
    (servedMapFor demoControlReg demoPollKey).node.map (·.machineAuthorized) = some true := by
  native_decide

/-- **The served map homes the node on drorb's DERP region.** -/
theorem servedMapFor_homederp :
    (servedMapFor demoControlReg demoPollKey).derpMap.map (·.regions.map (·.1)) = some ["1"] := by
  native_decide

/-! ### ★ THE ADVERTISED-DERP THREADING — routable, and PROVABLY only that

`servedMapForAt` lets the live serve advertise a REACHABLE relay
(`drorbDerpMapAt <DRORB_DERP_ADDR>`) instead of the client's own loopback. The three
theorems below are the reason that knob is safe to turn: for EVERY advertised DERPMap
the served self node, the served peers, and the served ACL are IDENTICAL to the
loopback serve — the advertised addr moves the `DERPMap` field and NOTHING else. So
`servedMapFor_filter_is_acl_compile` / `_self_addr` / `_peer_addr` / `_self_authorized`
above remain the operative facts about the routable serve, not just the loopback one. -/

/-- **The advertised DERPMap does not move the served SELF node.** -/
theorem servedMapForAt_node (dm : Control.Derp.DerpMap) (base : Control.ControlState)
    (k : Control.NodeKey) : (servedMapForAt dm base k).node = (servedMapFor base k).node := by
  simp only [servedMapForAt, servedMapFor, Control.Join.servedNetMapWireAt,
    Control.Join.servedNetMapWire]
  cases Control.lookupReg base.nodes k <;> rfl

/-- **The advertised DERPMap does not move the served PEERS.** -/
theorem servedMapForAt_peers (dm : Control.Derp.DerpMap) (base : Control.ControlState)
    (k : Control.NodeKey) : (servedMapForAt dm base k).peers = (servedMapFor base k).peers := by
  simp only [servedMapForAt, servedMapFor, Control.Join.servedNetMapWireAt,
    Control.Join.servedNetMapWire]
  cases Control.lookupReg base.nodes k <;> rfl

/-- **The advertised DERPMap does not move the served ACL.** The routable serve carries
the SAME `PacketFilters["base"]` — the ACL-compiler output — as the loopback serve. -/
theorem servedMapForAt_filters (dm : Control.Derp.DerpMap) (base : Control.ControlState)
    (k : Control.NodeKey) :
    (servedMapForAt dm base k).packetFilters = (servedMapFor base k).packetFilters := by
  simp only [servedMapForAt, servedMapFor, Control.Join.servedNetMapWireAt,
    Control.Join.servedNetMapWire]
  cases Control.lookupReg base.nodes k <;> rfl

/-- **★ THE ROUTABLE-DERP THEOREM (the gate, stated).** For EVERY advertised host and
EVERY registered polling node, the served `MapResponse`'s DERP region-1 node advertises
`ipToWire host` as the IPv4 the stock client dials. Instantiated at the live
`DRORB_DERP_ADDR`, this is exactly "the cross-host client is told the LAN IP, not
`127.0.0.1`". -/
theorem servedMapForAt_derp_advertises (host : Bytes) (base : Control.ControlState)
    (k : Control.NodeKey) (r : Control.Registration)
    (h : Control.lookupReg base.nodes k = some r) :
    ((servedMapForAt (Control.Join.drorbDerpMapAt host) base k).derpMap.bind
        (·.regions.head?)).bind (fun kv => kv.2.nodes.head?.bind (·.ipv4))
      = some (Control.Join.ipToWire host) := by
  simp only [servedMapForAt, Control.Join.servedNetMapWireAt, h, Control.Join.netMapToWire]
  rfl

/-- The ACL-compile refinement, transported to the ROUTABLE serve: for every advertised
DERPMap the served filter is still the proven `Control.Acl.compile` output. -/
theorem servedMapForAt_filter_is_acl_compile (dm : Control.Derp.DerpMap) :
    (servedMapForAt dm demoControlReg demoPollKey).packetFilters
      = some [("base", (Control.Join.compiledPacketFilter Control.Acl.demoPolicy).map
                Control.Join.filterRuleToWire)] := by
  rw [servedMapForAt_filters]; exact servedMapFor_filter_is_acl_compile

/-- Self/peer addressing, transported to the ROUTABLE serve. -/
theorem servedMapForAt_self_addr (dm : Control.Derp.DerpMap) :
    (servedMapForAt dm demoControlReg demoPollKey).node.map (·.addresses)
      = some ["100.64.0.1/32"] := by
  rw [servedMapForAt_node]; exact servedMapFor_self_addr

theorem servedMapForAt_peer_addr (dm : Control.Derp.DerpMap) :
    (servedMapForAt dm demoControlReg demoPollKey).peers.map (·.map (·.addresses))
      = some [["100.64.0.2/32"]] := by
  rw [servedMapForAt_peers]; exact servedMapFor_peer_addr

/-- The LIVE cross-host instance, as a CLOSED term: advertising `192.168.50.39` makes the
served DERPMap carry `192.168.50.39` — the exact bytes a stock client on another host
reads to reach the relay. (`#guard` below evaluates it.) -/
def demoRoutableHost : Bytes := [192, 168, 50, 39]

theorem servedMapForAt_derp_routable_demo :
    ((servedMapForAt (Control.Join.drorbDerpMapAt demoRoutableHost)
        demoControlReg demoPollKey).derpMap.bind (·.regions.head?)).bind
        (fun kv => kv.2.nodes.head?.bind (·.ipv4))
      = some "192.168.50.39" := by native_decide

/-- ...and the LOOPBACK serve is the one that says `127.0.0.1` — the bug this threading
fixes, pinned so a regression is visible. -/
theorem servedMapFor_derp_loopback_demo :
    ((servedMapFor demoControlReg demoPollKey).derpMap.bind (·.regions.head?)).bind
        (fun kv => kv.2.nodes.head?.bind (·.ipv4))
      = some "127.0.0.1" := by native_decide

#guard ((servedMapForAt (Control.Join.drorbDerpMapAt demoRoutableHost)
  demoControlReg demoPollKey).derpMap.bind (·.regions.head?)).bind
  (fun kv => kv.2.nodes.head?.bind (·.ipv4)) == some "192.168.50.39"
#guard ((servedMapForAt (Control.Join.drorbDerpMapAt demoRoutableHost)
  demoControlReg demoPollKey).node.map (·.addresses)) == some ["100.64.0.1/32"]

#print axioms servedMapFor_eq_at
#print axioms servedMapForAt_node
#print axioms servedMapForAt_peers
#print axioms servedMapForAt_filters
#print axioms servedMapForAt_derp_advertises
#print axioms servedMapForAt_filter_is_acl_compile

-- Runtime evidence (closed terms) — DISTINCT addresses + MUTUAL peers:
#guard Control.Ipam.cgnatPool.alloc [Control.Ipam.ip1] == some Control.Ipam.ip2
#guard (servedMapFor demoControlReg demoPollKey).node.map (·.addresses) == some ["100.64.0.1/32"]
#guard (servedMapFor demoControlReg demoPollKey).peers.map (·.map (·.addresses)) == some [["100.64.0.2/32"]]
#guard (servedMapFor demoControlReg demoPeerKey).node.map (·.addresses) == some ["100.64.0.2/32"]
#guard (servedMapFor demoControlReg demoPeerKey).peers.map (·.map (·.addresses)) == some [["100.64.0.1/32"]]
#guard (servedMapFor demoControlReg demoPollKey).node.map (·.machineAuthorized) == some true
#guard (servedMapFor demoControlReg demoPollKey).derpMap.map (·.regions.map (·.1)) == some ["1"]

#print axioms registerDecide_gate
#print axioms recordWireDeframe_frame
#print axioms servedMapFor_filter_is_acl_compile
#print axioms demo_addrs_are_ipam_alloc
#print axioms servedMapFor_self_addr
#print axioms servedMapFor_peer_addr
#print axioms servedMapFor_peer_view

end Control.H2Noise
