/-
# ControlLive — driving the PROVEN ts2021 control plane over the byte level

The `Control` foundation and `Control.Channel` model the coordination server
("control plane") of a mesh VPN as sans-IO, proven Lean: the ts2021 Noise-IK
handshake as a transition system (`Control.Channel.step` to `.up`, keys agreeing
via `handshake_keys_agree`), the AEAD-sealed control frame carrying every wire
message (`seal_open` and the `{regReq,mapReq,regResp,mapResp}_channel_roundtrip`
lemmas), the server transition system (`Control.step`: register → authorize →
mapPoll → netmap), the netmap delta fold (`NetMap.applyDelta`), MagicDNS
resolution (`DnsConfig.resolve`), and cryptokey-routing translation
(`NetMap.toWgPeers`).

None of that logic was wired into a running binary. This executable is that
wiring: a `selftest` that drives BOTH ends — a **coord** (responder) and a
**node** (initiator) — over the byte level in one process (no sockets yet), so
the whole PROVEN pipeline is EXERCISED end to end:

  1. both ends drive `Control.Channel.Ts2021.step` — the **byte-exact**
     `controlbase` handshake FSM — to `.up`, exchanging the real 101-byte
     initiation and 51-byte response frames, transport keys agreeing (the
     runtime cross-check confirms what `Ts2021.handshake_refines` proves:
     node.send == coord.recv, node.recv == coord.send);
  2. the node builds + seals a `RegisterRequest` under its send key; the coord
     opens it under the matching receive key and runs `Control.step .register`,
     authorizing the machine under a `Policy`;
  3. the node seals a `MapRequest`; the coord opens it and runs
     `Control.step .mapPoll`, replying with a sealed `MapResponse.full` carrying
     the authorized-peer netmap;
  4. the node opens the response (`openMapResp`), folds `NetMap.applyDelta`,
     resolves a MagicDNS name (`DnsConfig.resolve`), and programs the WireGuard
     peer table (`NetMap.toWgPeers`);
  5. it prints the resulting WG peers + DNS result and a PASS/FAIL cross-check
     against the model decision — the realization of
     `control_applies_netmap_faithfully`.

## Honesty / realization boundary (the DiscoLive discipline)

The **handshake** is byte-exact `controlbase`: `Control.Channel.Ts2021.step`
over `Control.Ts2021Core`'s plain `Noise_IK_25519_ChaChaPoly_BLAKE2s`, emitting
the real 101-byte initiation and 51-byte response frames (the layouts
`Control/RealCaptureKat.lean` parses out of REAL tailscale-1.98.8 capture bytes,
and `control-ts2021-channel-kat` checks field by field). What is still
drorb-native is the **post-handshake record** layer below and the tailnet auth
key — a live stock client additionally needs an operator-provided auth key
(the named residual in `Control/Channel.lean §7`). Like DiscoLive / wg-live this is a live cross-check,
not part of the trusted core: everything cryptographic/structural is the proven
Lean. The gap the selftest discharges (by construction, not by proof) is that
this exe faithfully CALLS the proven Lean functions on real bytes; the
faithfulness of the decode→apply chain ITSELF is proven below as
`control_applies_netmap_faithfully`.

Usage:
  control-live selftest
-/
import Control.Ts2021Wire
import Control.Ts2021Record
import Control.PreAuthKey
import Control.Store
import Control.Durable
import Control.Admin
import Control.Expiry
import Control.Join
import Control.Policy
import Control.Tags
import Control.H2Noise
import Control.Tailcfg
import Control.TailcfgWire
import H2.Conn
import H2.HpackEncode
import Crypto
import Std.Sync.Mutex

namespace ControlLive

open Control
open Control.Channel (bytesOf baOf initiatorTx responderTx)
open Control.Ts2021Wire (nonce0 frameInitiation frameResponse AeadExpands noiseResponse Sym)

/-! ## The Phase-0 faithfulness theorem

The running loop's decode→apply chain applies EXACTLY the proven decision. Given
the coord's decided `MapResponse m` sealed into a frame under its send key, the
node's `openMapResp` (= parseFrame → chachaOpen → getMapResp) followed by the
netmap fold (`applyDelta`) and cryptokey-routing translation (`toWgPeers`)
produces PRECISELY what the model computes by folding the SAME decision `m` — the
bytes on the wire realize the model, mediated only by the proven round-trips
(`frame_roundtrip`, `seal_open`, `getMapResp_put`, chained by
`mapResp_channel_roundtrip`). Not a `P → P`: it is inhabited (the selftest below
produces such a `frame`) and its content is the crypto+codec round-trip. -/
theorem control_applies_netmap_faithfully
    (sk rk nonce : ByteArray) (nm0 : NetMap) (m : MapResponse)
    (hk : sk = rk) {frame : Control.Bytes}
    (hs : Control.Channel.sealMapResp sk nonce m = some frame) :
    (Control.Channel.openMapResp rk nonce frame).map
        (fun r => (nm0.applyDelta r).toWgPeers)
      = some (nm0.applyDelta m).toWgPeers := by
  rw [Control.Channel.mapResp_channel_roundtrip sk rk nonce m hk hs]
  rfl

#print axioms control_applies_netmap_faithfully

/-! ## Phase-1 : the live handshake refines the proven BYTE-EXACT FSM

Phase 0 drove the handshake over the byte level in one process. Phase 1 splits
into two OS processes over a real TCP socket: a **coord** that listens/accepts
and a **node** that connects. The socket driver (below) moves the **actual
`controlbase` frames** — the 101-byte initiation and the 51-byte response — and
feeds them verbatim to `Control.Channel.Ts2021.step`. Nothing is re-derived
host-side: the host reads a frame header, reads `len` more bytes, and hands the
whole frame to the FSM.

This theorem is the refinement obligation the two-process run discharges, and it
is the **byte-exact** one. The previous version of this theorem drove §2's
WireGuard-reuse FSM (`Control.Channel.step`), whose `Ev` carried already-parsed
public keys and whose IKpsk2 ratchet is NOT transcript-identical to a stock
ts2021 peer; the deployed `control-live coord` the dataplane splices to was
therefore not byte-exact on the hand-off. It now is: the statement below is over
`Ts2021.step`, the transitions the socket loop actually invokes, on the frames
the socket actually carries.

It is `Control.Channel.Ts2021.handshake_refines` instantiated at the deployment
site, and it consumes `Control.Ts2021Transcript.transcripts_coincide` (via
`readInitiation_noiseInitiation` / `readResponse_noiseResponse`) for the fact
that the two ends reach the same Noise state. Key agreement is a CONCLUSION, not
a hypothesis; `hRespOk` is a liveness-only hypothesis (see the `handshake_refines`
docstring for why it cannot be discharged from the present axiom set).

Realization boundary (named): the socket driver realizes the model by *calling*
`Ts2021.step` on the bytes `recv`/`send` moved; that the C shim faithfully moves
those bytes is discharged by construction (the live 2-process run), exactly as
`control_applies_netmap_faithfully` handles the decode->apply chain. -/
open Control.Channel Control.Channel.Ts2021 in
theorem control_handshake_refines
    (nodeSess coordSess : Control.Channel.Ts2021.Session)
    (sI : Sym) (initFrame : Control.Bytes)
    (aeadExpands : AeadExpands)
    (hRoleC : coordSess.role = .coord)
    (hPeerS : nodeSess.peerS = coordSess.spub)
    (hVer : nodeSess.version < 65536)
    (bEi : Crypto.x25519Base nodeSess.epriv  = some nodeSess.epub)
    (bSi : Crypto.x25519Base nodeSess.spriv  = some nodeSess.spub)
    (bSr : Crypto.x25519Base coordSess.spriv = some coordSess.spub)
    (bEr : Crypto.x25519Base coordSess.epriv = some coordSess.epub)
    (hei : nodeSess.epub.size = 32) (hsi : nodeSess.spub.size = 32)
    (her : coordSess.epub.size = 32)
    (hRespOk : ∃ respMsg sR,
        noiseResponse sI coordSess.epriv coordSess.epub nodeSess.epub nodeSess.spub
          ByteArray.empty = some (respMsg, sR))
    (hStart : Control.Channel.Ts2021.step nodeSess .fresh .start
                = (.awaitResp sI, .sendInit initFrame)) :
    ∃ (respFrame niNoise nrNoise : Control.Bytes) (m : ByteArray),
      initFrame = frameInitiation nodeSess.version niNoise ∧ niNoise.length = 96 ∧
      respFrame = frameResponse nrNoise ∧ nrNoise.length = 48 ∧
      Control.Channel.Ts2021.step coordSess .fresh (.recvInit initFrame)
          = (.up (responderTx m), .sendResp respFrame) ∧
      Control.Channel.Ts2021.step nodeSess (.awaitResp sI) (.recvResp respFrame)
          = (.up (initiatorTx m), .idle) ∧
      (initiatorTx m).send = (responderTx m).recv ∧
      (initiatorTx m).recv = (responderTx m).send :=
  Control.Channel.Ts2021.handshake_refines aeadExpands hRoleC hPeerS hVer
    bEi bSi bSr bEr hei hsi her hRespOk hStart

#print axioms control_handshake_refines

/-! ## The untrusted TCP socket seam

The client half (connect/send/recvExact/close) is reused from `ffi/derp_net.c`
(the same shim `derp-live` uses); the server half (listen/accept) is
`ffi/control_net.c`, the only server capability derp_net.c lacks. These are the
untrusted environment — they move bytes and hold no protocol state. -/

@[extern "drorb_tcp_connect"]
opaque tcpConnect (host : String) (port : UInt16) : IO UInt32
@[extern "drorb_tcp_send"]
opaque tcpSend (fd : UInt32) (payload : ByteArray) : IO Unit
@[extern "drorb_tcp_recv_exact"]
opaque tcpRecvExact (fd : UInt32) (nbytes : UInt32) (timeoutMs : UInt32) : IO (Option ByteArray)
@[extern "drorb_tcp_close"]
opaque tcpClose (fd : UInt32) : IO Unit
@[extern "drorb_tcp_listen"]
opaque tcpListen (port : UInt16) : IO UInt32
@[extern "drorb_tcp_accept"]
opaque tcpAccept (lfd : UInt32) (timeoutMs : UInt32) : IO (Option UInt32)

/-! ## Liveness ticks — how long the coordinator waits, and what it does with a
wait that ended in nothing

A quiet homelab tailnet is the TARGET deployment, not a degenerate case: nodes
hold their map long-poll open and rarely dial fresh, so long stretches with no
new inbound connection and no client record are the NORMAL steady state. Every
bound below therefore has to answer the same question — "what happens when
nothing happened?" — with "keep serving", never with "shut down".

Read ONCE at process start (`initialize`), so a knob is a start-time decision and
not a per-tick re-read on the serving path.
-/

/-- How long one `tcpAccept` waits before the accept loop regains control, in ms
(`DRORB_ACCEPT_TICK_MS`, default 300000 = 5 min).

The bound itself is KEPT deliberately. `tcpAccept` is a blocking `poll` inside
the FFI shim, so an unbounded wait parks the coordinator's accept thread in C
with no way to come back for anything else — the periodic return to Lean is what
lets the loop log liveness, and is where a shutdown check or a reaper would go.
It is a LIVENESS TICK, not a lifetime. What changed is what an expired tick
MEANS: see `acceptIdleExitTicks`. -/
initialize acceptTickMs : UInt32 ← do
  match ← IO.getEnv "DRORB_ACCEPT_TICK_MS" with
  | some s => match s.toNat? with
              | some n => pure (UInt32.ofNat (max n 100))
              | none   => pure 300000
  | none   => pure 300000

/-- How many CONSECUTIVE idle accept ticks END the process
(`DRORB_ACCEPT_IDLE_EXIT`, default `0` = NEVER).

THE IDLE-EXIT FIX. `acceptLoop` used to print "accept idle 300s; exiting" and
RETURN on the very first timeout. A coordinator that went five minutes without a
NEW inbound connection therefore stopped serving — and because the policy-reload
and approval watcher tasks keep the Lean runtime alive, the process did not even
exit: it lingered holding the listening socket with nobody accepting, so client
dials piled up unanswered in the kernel backlog (observed: Recv-Q 5 on the LISTEN
socket, five noise initiations unread, and `tailscale up` on a new node timing
out) and no supervisor ever saw a failure to restart from. Idleness is now the
normal state; only an operator who explicitly asks — a one-shot test harness that
wants the process to end — gets a lifetime. -/
initialize acceptIdleExitTicks : Nat ← do
  match ← IO.getEnv "DRORB_ACCEPT_IDLE_EXIT" with
  | some s => pure (s.toNat?.getD 0)
  | none   => pure 0

/-- How many `pushLoop` ticks cap ONE open map long-poll
(`DRORB_PUSH_MAX_TICKS`, default `0` = no cap).

THE SIBLING. This bound used to be a hard `240`. A tick with nothing to push is
one `pushDrainTimeout` (500 ms), so a HEALTHY, perfectly quiet client had its map
stream closed by the coordinator every ~2 minutes; it then redialled, which is
precisely why the idle-exit bug above never fired in the restart probe — one bug
was masking the other (observed live: "push stream 5 hit time bound; closing"
followed by "opened map long-poll on stream 1", on a loop).

What the bound was FOR is reaping a stream whose client vanished without the
socket erroring, and that job is already done by the periodic
`MapResponse{KeepAlive}` below: a send on a dead socket makes `sendH2Out` return
`none` and ends the loop. Against a client that vanished with no FIN at all, the
keepalive still ends the loop — at the kernel's retransmit timeout rather than in
two minutes. That is a FAILURE bound; the old 240 was a HEALTH bound, and a
health bound on a long-poll is a disconnect generator. -/
initialize pushMaxTicks : Nat ← do
  match ← IO.getEnv "DRORB_PUSH_MAX_TICKS" with
  | some s => pure (s.toNat?.getD 0)
  | none   => pure 0

/-! ## Byte helpers (mirrors DiscoLive/DerpLive) -/

def ofHex (s : String) : ByteArray := Id.run do
  let cs := s.toList.filter (fun c => c ≠ ' ' ∧ c ≠ '\n')
  let hexVal : Char → Option UInt8 := fun c =>
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
    else none
  let rec go : List Char → ByteArray → ByteArray
    | hi :: lo :: rest, acc =>
      match hexVal hi, hexVal lo with
      | some h, some l => go rest (acc.push (h * 16 + l))
      | _, _ => acc
    | _, acc => acc
  go cs (ByteArray.mk #[])

def toHex (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.toList.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

def toHexL (b : Control.Bytes) : String := toHex (baOf b)

/-- Render a byte list that is UTF-8 text as text (for names), else hex. -/
def textOrHex (b : Control.Bytes) : String := (String.fromUTF8? (baOf b)).getD (toHexL b)

/-- The `controlbase` protocol version this peer announces in the initiation
header and binds into the Noise prologue. 138 is the capability version a REAL
tailscale-1.98.8 client advertised in the captured initiation frame
(`Control/testdata/initiation_frame.bin` bytes `[0:2] = 00 8a`, checked by
`Control/RealCaptureKat.lean`). -/
def tsVersion : Nat := 138

/-- A fixed 32-byte placeholder key value. -/
def dummyKey (v : UInt8) : Control.Bytes := List.replicate 32 v

/-! ## The pre-auth admission gate + the durable coordination store, wired LIVE

The live register handler below drives the PROVEN `Control.PreAuth.registerWithPreAuth`
(admission gated by `preAuthPolicy`, non-bypass by `preauth_matches_policy_step`) and
backs it with `Control.Store` (append an event per state change, replay the log on
startup — `restart_sound` made live). Nothing here reimplements the gate or the replay;
this is the byte/IO realization that CALLS the proven functions, exactly like the socket
shim realizes the handshake FSM. -/

/-- Audited AWS-LC CSPRNG (`aws_lc_rs::rand::fill`) via `ffi/crypto_shim.c`
`drorb_rand_bytes` — NEVER `rand`. Fail-closed (empty ByteArray on error). Same shim
`preauth-mint` draws its secret from. -/
@[extern "drorb_rand_bytes"]
opaque randBytes (len : UInt32) : IO ByteArray

/-- The model's abstract `hash`, instantiated with HACL*/EverCrypt SHA-256 (F*-verified),
exactly as `PreAuthMintTool.sha256Bytes`. The pre-auth store holds only these hashes. -/
def sha256Bytes (b : Control.Bytes) : Control.Bytes := (Crypto.sha256 ⟨b.toArray⟩).toList

/-- Reusable, never-expiring, untagged, user-0 key attributes — the shape the
`Control.Store.PreauthKey` schema round-trips faithfully (keyHash/reusable/used). Richer
attributes (expiry/tags/user, one-shot spend) are a NAMED residual of the current
persisted-key schema, not exercised by this live path. -/
def reusableAttrs : Control.PreAuth.KeyAttrs :=
  { reusable := true, ephemeral := false, expiry := 0, tags := [], user := 0 }

/-- Reconstruct a `Control.PreAuth.KeyRecord` (the admission gate's key model) from a
persisted `Control.Store.PreauthKey`.

★FIXED 2026-07-25 — this used to be `{ reusableAttrs with reusable := pk.reusable }`,
which DROPPED the persisted `tags`, `user`, `ephemeral`, `expiry` and `revoked` on the
floor and was labelled a "named residual". It was in fact a live fault: an operator who
ran `drorb-ctl preauthkeys create --user 7 --tags tag:web` got a node admitted with NO
tags and user 0, so the whole tag-at-enrolment path was dead in the running coordinator
(and a REVOKED key still admitted). It is now the proven-lossless
`Control.Store.PreauthKey.toRecord` — every persisted field maps across
(`paRecordOf_lossless` below, and `Control.Admin.mintedKey_toRecord_eq_mint`: the record
a `drorb-ctl` mint persists views back as exactly `Control.PreAuth.mint`). -/
def paRecordOf (pk : Control.Store.PreauthKey) : Control.PreAuth.KeyRecord :=
  Control.Store.PreauthKey.toRecord pk

/-- **The enrolment path carries the key's tags and owner.** Reconstructing a persisted
key for the admission gate preserves every attribute the operator minted — in particular
`tags` and `user`, which `Control.PreAuth.registerWithPreAuth` then stamps onto the node
(`preauth_admit`) and `Control.Tags.tagBindings` later gates on. General over the key. -/
theorem paRecordOf_lossless (pk : Control.Store.PreauthKey) :
    (paRecordOf pk).attrs.tags = pk.tags
    ∧ (paRecordOf pk).attrs.user = pk.user
    ∧ (paRecordOf pk).attrs.expiry = pk.expiry
    ∧ (paRecordOf pk).attrs.ephemeral = pk.ephemeral
    ∧ (paRecordOf pk).revoked = pk.revoked :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **A `drorb-ctl`-minted key reaches the gate as exactly `PreAuth.mint`.** Composing
`paRecordOf_lossless` with `Control.Admin.mintedKey_toRecord_eq_mint`: what the operator
minted (attributes and all) is what the live admission gate validates. So a key minted
`--user 7 --tags tag:web` admits a node carrying `tag:web` owned by user 7
(`Control.PreAuth.preauth_admit`). -/
theorem paRecordOf_minted (hash : Control.Bytes → Control.Bytes)
    (secret : Control.Bytes) (a : Control.PreAuth.KeyAttrs) :
    paRecordOf (Control.Admin.mintedKey hash secret a) = Control.PreAuth.mint hash secret a :=
  Control.Admin.mintedKey_toRecord_eq_mint hash secret a

/-- The fixed pre-auth secret of this drorb-native test tailnet: the two-process
coord/node share it out of band, and the coord's key store holds ONLY its SHA-256 hash
(hashed at rest). A real tailnet mints a per-device key from the CSPRNG (`preauth-mint`)
and hands the operator the secret — the named residual in `Control/Channel.lean §7`. -/
def testAuthSecret : Control.Bytes :=
  (ofHex "5ec5e7000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c").toList

/-- Serve the coordination state with the PROVEN pieces wired in
(`Control.Join.coordState`): `filter` = `compiledPacketFilter Acl.demoPolicy` (the ACL
compiler output, `served_filter_is_acl_compile`), `dns` = MagicDNS `buildDns`; every node
homed on drorb's own verified DERP region (`drorbDerpMap`, `served_derp_names_drorb`). -/
def servedControl (regs : List Control.Registration) : Control.ControlState :=
  Control.Join.coordState Control.Acl.demoPolicy Control.Join.demoDomains regs

/-- A static, already-authorized demo peer of this drorb-native test tailnet — a rich
node (overlay address `100.64.0.2`, a `/24` subnet route, an endpoint) homed on drorb's
DERP region. It is STATIC tailnet config recomputed each boot (like the ACL policy and the
DERPMap), NOT a persisted registration — the event log carries only the minimal `nodeOf`
records that `Control.Store` replays; address/route allocation for registered nodes is a
named residual (unmodeled here). Included in the served netmap so a freshly-registered
node receives a non-trivial peer + WireGuard allowedIPs. -/
def demoPeerReg : Control.Registration :=
  let peerNode : Node :=
    { id := 42, stableID := "peer-stable-id".toUTF8.toList,
      name := "peer.example.ts.net".toUTF8.toList, user := 1,
      key := ⟨dummyKey 0xab⟩, machine := ⟨dummyKey 0xcd⟩, disco := ⟨dummyKey 0xef⟩,
      addresses  := [{ addr := [100,64,0,2], bits := 32 }],
      allowedIPs := [{ addr := [100,64,0,2], bits := 32 }, { addr := [10,0,0,0], bits := 24 }],
      endpoints  := [{ addr := [192,168,1,50], port := 41641 }],
      derp := Control.Join.drorbRegionID, online := true, keyExpiry := 0, authorized := true }
  { nodeKey := peerNode.key, node := peerNode, status := .authorized }

/-- A map-poll request from `k` (long-poll stream). -/
def pollReqOf (k : Control.NodeKey) : Control.MapRequest :=
  { version := 1, nodeKey := k, discoKey := ⟨[]⟩, endpoints := [],
    stream := true, omitPeers := false, readOnly := false }

/-! ### The in-process GATE: mint → pre-auth register → map → kill → replay → still-known

`control-live gate <logfile>` drives the whole admission+persistence pipeline my-hand with
the PROVEN functions and a REAL file:

  1. mint a pre-auth key from the audited CSPRNG (only its SHA-256 hash is stored);
  2. a node presents the key in `RegisterRequest.authKey`; `registerWithPreAuth` ADMITS it
     (`MachineAuthorized`), the same door as `Control.step` under `preAuthPolicy`;
  3. append the durable events (`keyMinted` hashed-at-rest, `nodeRegistered` carrying the
     authorization DECISION) and `encodeLog` them to `<logfile>`;
  4. serve `MapResponse.full` with the ACL-compiled PacketFilter + drorb DERPMap;
  5. **kill + restart**: a fresh read of `<logfile>` → `decodeLog` → `replay` from empty
     recovers the node STILL `.authorized` — no re-registration — and serves the netmap
     again. This is `restart_sound` ∘ `decodeLog_encodeLog`, realized on disk. -/
/-- Parse a dotted-quad `"a.b.c.d"` into 4 bytes (the advertised DERP host IP). -/
def parseDottedQuad (s : String) : Option (List UInt8) :=
  let parts := s.splitOn "."
  let nums := parts.filterMap (fun p => p.toNat?)
  if parts.length == 4 && nums.length == 4 && nums.all (· < 256)
  then some (nums.map (·.toUInt8)) else none

/-- The advertised DERP relay host: `DRORB_DERP_ADDR` (dotted-quad) if set + valid,
else drorb's loopback default. This is the IP a stock client dials to reach the relay;
`DRORB_DERP_LISTEN` (in `derp-relay`) is the interface the relay actually binds. -/
def derpAdvHost : IO (List UInt8) := do
  match ← IO.getEnv "DRORB_DERP_ADDR" with
  | none => pure Control.Join.drorbDerpHost
  | some str => match parseDottedQuad str with
    | some bs => pure bs
    | none => do
      IO.eprintln s!"DRORB_DERP_ADDR={str} is not a dotted-quad; advertising loopback"
      pure Control.Join.drorbDerpHost

/-- The **advertised DERP port**: `DRORB_DERP_PORT` if set + in range, else drorb's
default `3340`. `scripts/run-tailnet.sh` passes the SAME value it binds the relay on
(`DERP_PORT`), so the served netmap cannot advertise a port nothing listens on. The
invariants hold for EVERY port: `Join.drorbDerpMapAtPort_names_drorb` /
`_valid` / `Join.derpMapToWireAtPort_ipv4`. -/

def derpAdvPort : IO Nat := do
  match ← IO.getEnv "DRORB_DERP_PORT" with
  | none => pure Control.Join.drorbDerpPort
  | some str => match str.toNat? with
    | some n => if n > 0 && n < 65536 then pure n else do
        IO.eprintln s!"DRORB_DERP_PORT={str} is out of range; advertising {Control.Join.drorbDerpPort}"
        pure Control.Join.drorbDerpPort
    | none => do
      IO.eprintln s!"DRORB_DERP_PORT={str} is not a number; advertising {Control.Join.drorbDerpPort}"
      pure Control.Join.drorbDerpPort

/-- The **advertised STUN port**: `DRORB_STUN_PORT` if set + in range, else `0`
meaning *not advertised*.

This is the knob that decides whether a stock client can discover a **direct** path at
all. `netcheck` learns a node's own reflexive transport address only by sending a STUN
Binding request to the STUN service of a DERP region in the served netmap; with nothing
advertised it probes tailscale's default `3478`, gets no answer, reports `udp=false`, and
its endpoint set holds only local-interface candidates — so peers that do not already
share a link never get past the relay.

`scripts/run-tailnet.sh` passes the SAME value it binds `stun-live server` on, so the
served netmap cannot advertise a STUN port nothing listens on — the exact discipline
`DRORB_DERP_PORT` already has. `0` reproduces the pre-existing served shape byte for byte
(`Join.derpMapToWireAtPort_no_stunPort`), and every invariant holds for EVERY value:
`Join.drorbDerpMapAtPortStun_names_drorb` / `_valid` / `_relay_unmoved`, and
`Join.derpMapToWireAtPortStun_stunPort` pins that the advertised port IS this number. -/
def stunAdvPort : IO Nat := do
  match ← IO.getEnv "DRORB_STUN_PORT" with
  | none => pure 0
  | some str => match str.toNat? with
    | some n => if n > 0 && n < 65536 then pure n else do
        IO.eprintln s!"DRORB_STUN_PORT={str} is out of range; NOT advertising a STUN service"
        pure 0
    | none => do
      IO.eprintln s!"DRORB_STUN_PORT={str} is not a number; NOT advertising a STUN service"
      pure 0

/-- The **advertised DERP CertName**: `DRORB_DERP_CERTNAME` if set, else `[]` meaning
*not advertised*.

This is the knob that decides whether a stock client can reach the relay over HTTPS at
all. `derphttp` dials `https://<host>:<DERPPort>/derp`; a self-hosted relay's leaf is
signed by no public CA, so the only way the dial succeeds is for the served node to name
`CertName = "sha256-raw:<hex sha256 of the leaf DER>"`, which makes the client PIN that
exact certificate (`tlsdial.SetConfigExpectedCertHash`) instead of verifying a path.

`scripts/run-tailnet.sh` derives the value from the SHA-256 of the certificate file the
TLS front actually presents (`derp-relay certname`), so the advertised pin cannot drift
from the presented leaf — the same discipline `DRORB_DERP_PORT` has against the bound
port. `[]` reproduces the pre-existing served shape byte for byte
(`Join.derpMapToWireAtPortStun_no_certName`); the advertised value is pinned by
`Join.derpMapToWireAtPortStunCert_certName`, and the relay endpoint is unmoved by it
(`Join.derpMapToWireAtPortStunCert_ipv4`). -/
def derpAdvCertName : IO Control.Bytes := do
  match ← IO.getEnv "DRORB_DERP_CERTNAME" with
  | none => pure []
  | some s => pure s.toUTF8.data.toList

/-- The **advertised DERPMap** the live serve hands clients: `drorbDerpMapAtPortStun` the
`DRORB_DERP_ADDR` host, `DRORB_DERP_PORT` port and `DRORB_STUN_PORT` STUN port
(loopback:3340, STUN unadvertised, if unset). This is the ONE place the routable addr
enters the serve path; it is threaded as an explicit argument from `h2coordMulti` down to
the `H2Noise.Cfg`, never read per-connection. Turning this knob is proved to move ONLY
the advertised DERP endpoint: `H2Noise.servedMapForAt_node` / `_peers` / `_filters` show
the served self, peers, and ACL are IDENTICAL for every advertised DERPMap, and
`H2Noise.servedMapForAt_derp_advertises` shows the served region-1 node IPv4 IS the
advertised host. -/
def derpAdvMap : IO Control.Derp.DerpMap := do
  pure (Control.Join.drorbDerpMapAtPortStunCert (← derpAdvHost) (← derpAdvPort)
          (← stunAdvPort) (← derpAdvCertName))

/-- The **control URL** clients dialed (`tailscale up --login-server=<this>`), used as
the `AuthURL` prefix for the interactive (non-preauth) enrolment path: a node with no
valid pre-auth key is told to open `<DRORB_CONTROL_URL>/register/<nonce>` and holds until
the operator `drorb-ctl nodes approve`s it. Read ONCE and threaded into every
`H2Noise.Cfg`; the loopback default is right for a same-host bring-up. -/
def controlBaseURL : IO String := do
  match ← IO.getEnv "DRORB_CONTROL_URL" with
  | some u => pure u
  | none   => pure "https://drorb"

/-- Is the store already in the framed append-only format? (Reads only the magic.) -/
def storeIsFramed (logPath : String) : IO Bool := do
  try
    let h ← IO.FS.Handle.mk logPath IO.FS.Mode.read
    let head ← h.read (USize.ofNat Control.Store.storeMagic.length)
    pure (Control.Store.storeMagic.isPrefixOf head.toList)
  catch _ => pure false

/-- Rewrite the whole store ATOMICALLY **and DURABLY** in the framed format
(`Control.Durable.commitAtomic`): write a sibling temp file, force ITS data, `rename` it
over the store, then force the containing DIRECTORY so the rename itself is on stable
storage. A POSIX rename is atomic, so a crash leaves either the old store or the new one
— never a half-written live store, which is what `writeBinFile` (open `O_TRUNC`, then
write) left behind on every single append; the two `fsync`s are what extend that from
"survives a killed process" to "survives a power cut" (`Control.Durable`). This is also
the call that MIGRATES a legacy count-prefixed store; the coordinator makes it once at
startup, after which every event is a pure append. -/
def storeWriteAll (logPath : String) (events : List Control.Store.Event) : IO Unit :=
  Control.Durable.commitAtomic logPath ⟨(Control.Store.encodeStore events).toArray⟩

/-- APPEND events to the store DURABLY (`Control.Durable.commitAppend`): open
`O_APPEND`, write ONLY the new frames, then `fsync` the file. The bytes at risk in a
crash are the bytes of the event being appended and nothing else — which is exactly the
shape `Control.Store.recover_torn_write` covers — and once this returns, those bytes are
on stable storage, so the registration the coordinator is about to ACKNOWLEDGE cannot be
undone by a power cut. If the file is not (yet) framed, fall back to the atomic full
rewrite. -/
def storeAppend (logPath : String) (prior : List Control.Store.Event)
    (newEvents : List Control.Store.Event) : IO Unit := do
  if ← storeIsFramed logPath then
    Control.Durable.commitAppend logPath ⟨(newEvents.flatMap Control.Store.putFrame).toArray⟩
  else
    storeWriteAll logPath (prior ++ newEvents)

/-- Log line naming the advertised relay endpoint, so the operator can SEE (in
`coord.out`) whether a cross-host client will be handed a reachable relay or loopback. -/
def announceDerp (who : String) (dm : Control.Derp.DerpMap) : IO Unit := do
  let ip := (dm.regions.head?.bind (·.nodes.head?)).elim "?" (fun e => Control.Join.ipToWire e.addr)
  let pt := (dm.regions.head?.bind (·.nodes.head?)).elim "?" (fun e => toString e.port)
  IO.println s!"{who}: advertising DERP region {Control.Join.drorbRegionID} at {ip}:{pt} (DRORB_DERP_ADDR/DRORB_DERP_PORT)"
  -- The STUN service the region advertises. Absent it, a stock client's netcheck
  -- reports udp=false and never learns a reflexive endpoint, so a DIRECT path can only
  -- ever happen between peers that already share a link.
  match dm.regions.head?.map (·.stunPort) with
  | some sp =>
      if sp == 0 then
        IO.println s!"{who}:   NOTE no STUN port advertised — clients will probe the 3478 default, get no answer,"
        IO.println s!"{who}:        report udp=false, and learn NO reflexive endpoint (set DRORB_STUN_PORT=<port> and run `stun-live server <port>`)"
      else
        IO.println s!"{who}:   STUN Binding server advertised at {ip}:{sp} (DRORB_STUN_PORT) — clients can learn their reflexive endpoint"
  | none => pure ()
  if ip == "127.0.0.1" then
    IO.println s!"{who}:   NOTE loopback — a client on ANOTHER host cannot reach this relay; set DRORB_DERP_ADDR=<this host's LAN IP>"

def gate (logPath : String) : IO UInt32 := do
  IO.println "== control-live GATE : mint -> pre-auth register -> map -> KILL -> replay -> still-known =="
  let now := 1000

  -- ── 1. mint a pre-auth key from the AUDITED AWS-LC CSPRNG; store only its hash ──
  let secretBA ← randBytes 32
  if secretBA.size ≠ 32 then do IO.eprintln "gate: CSPRNG failed (empty secret)"; return 1
  let secret : Control.Bytes := secretBA.toList
  let keyRec := Control.PreAuth.mint sha256Bytes secret reusableAttrs
  let paStore : Control.PreAuth.Store := [keyRec]
  let pk : Control.Store.PreauthKey := { key := keyRec.keyHash, reusable := true, used := false }
  IO.println s!"minted pre-auth key : sha256(secret)={toHex ⟨keyRec.keyHash.toArray⟩}"
  IO.println s!"  reusable={pk.reusable}  (the 256-bit secret is NOT stored — only the hash)"

  -- ── seed one prior-authorized peer (via the PROVEN replay), so the netmap has a peer ──
  let peerKey : Control.NodeKey := ⟨List.replicate 32 0x33⟩
  let peerReq : Control.RegisterRequest :=
    { version := 1, nodeKey := peerKey, oldNodeKey := ⟨[]⟩,
      machineKey := ⟨List.replicate 32 0x44⟩, authKey := secret,
      expiry := 0, ephemeral := false, followup := false }
  let seedEvents : List Control.Store.Event :=
    [ Control.Store.Event.keyMinted pk, Control.Store.Event.nodeRegistered peerReq true ]
  let seeded := Control.Store.replay seedEvents

  -- ── 2. a node presents the key; registerWithPreAuth ADMITS it (proven gate) ──
  let nodeKey : Control.NodeKey := ⟨List.replicate 32 0x11⟩
  let regReq : Control.RegisterRequest :=
    { version := 1, nodeKey := nodeKey, oldNodeKey := ⟨[]⟩,
      machineKey := ⟨List.replicate 32 0x22⟩, authKey := secret,
      expiry := 0, ephemeral := false, followup := false }
  let admit := Control.PreAuth.registerWithPreAuth sha256Bytes paStore seeded.control now regReq
  let authorized := admit.response.machineAuthorized
  IO.println s!"\n-- pre-auth register --"
  IO.println s!"registerWithPreAuth -> RegisterResponse.machineAuthorized = {authorized}"
  if !authorized then do IO.eprintln "gate: a VALID key was NOT admitted"; return 1
  -- a WRONG key is rejected (non-bypass witnessed live)
  let badReq := { regReq with nodeKey := ⟨List.replicate 32 0x99⟩, authKey := secret.map (· + 1) }
  let rejected := (Control.PreAuth.registerWithPreAuth sha256Bytes paStore seeded.control now badReq).response.machineAuthorized
  IO.println s!"a WRONG secret -> machineAuthorized = {rejected} (must be false)"
  if rejected then do IO.eprintln "gate: a wrong key was admitted — GATE BYPASSED"; return 1

  -- ── 3. APPEND the durable events + PERSIST the encoded log ──
  let log : List Control.Store.Event := seedEvents ++ [ Control.Store.Event.nodeRegistered regReq authorized ]
  let logBytes := Control.Store.encodeStore log
  storeWriteAll logPath log
  IO.println s!"\n-- persist --"
  IO.println s!"appended nodeRegistered(decision) + persisted {log.length} events ({logBytes.length}B) to {logPath}"

  -- ── 4. serve MapResponse.full : ACL PacketFilter + drorb DERPMap + peers from netmap ──
  let served := servedControl admit.state'.nodes
  let (_, reply) := Control.step (Control.PreAuth.preAuthPolicy sha256Bytes paStore now) served (.mapPoll (pollReqOf nodeKey))
  let some nm := (match reply with | .mapResp (.full nm) => some nm | _ => none)
    | do IO.eprintln "gate: coord did not serve a full netmap"; return 1
  let filterIsAcl := nm.packetFilter == Control.Join.compiledPacketFilter Control.Acl.demoPolicy
  let derpNamesDrorb :=
    (Control.Join.drorbDerpMap.regions.head?.map (·.regionID)) == some Control.Join.drorbRegionID
  IO.println s!"\n-- served MapResponse.full --"
  IO.println s!"peers={nm.peers.length}  filterRules={nm.packetFilter.length}  dnsRecords={nm.dns.records.length}"
  IO.println s!"  PacketFilter == Join.compiledPacketFilter Acl.demoPolicy : {filterIsAcl}"
  IO.println s!"  DERPMap region names drorb's verified relay (127.0.0.1:3340) : {derpNamesDrorb}"
  if !(filterIsAcl && derpNamesDrorb) then do IO.eprintln "gate: served netmap missing ACL filter / drorb DERP"; return 1

  -- ADVERTISED DERP addr: the endpoint IP the served DERPMap carries, i.e. the addr a
  -- stock client on ANOTHER host dials to reach the relay. `DRORB_DERP_ADDR` overrides
  -- the loopback default; the wire projection is `Join.servedNetMapWireAt` over
  -- `drorbDerpMapAt host`, whose invariants (`drorbDerpMapAt_names_drorb`,
  -- `drorbDerpMapAt_valid`, `derpMapToWireAt_ipv4`) hold for EVERY advertised host.
  let advHost ← derpAdvHost
  let advPort ← derpAdvPort
  let advWire := Control.Join.servedNetMapWireAt
    (Control.Join.drorbDerpMapAtPort advHost advPort) served nodeKey
  let advNode := (advWire.derpMap.bind (·.regions.head?)).bind (fun kv => kv.2.nodes.head?)
  let advNodeIpv4 := advNode.bind (·.ipv4)
  let advNodePort := advNode.bind (·.port)
  let advOk := advNodeIpv4 == some (Control.Join.ipToWire advHost) && advNodePort == some advPort
  IO.println s!"  DERPMap ADVERTISES relay at {Control.Join.ipToWire advHost}:{advPort} — wire IPv4:port the client dials = {advNodeIpv4}:{advNodePort} (matches advertised host+port: {advOk})"
  if !advOk then do IO.eprintln "gate: advertised DERP IPv4:port does not match DRORB_DERP_ADDR/DRORB_DERP_PORT"; return 1

  -- ── 5. KILL + RESTART : a fresh process reads ONLY the log, replays, node still known ──
  IO.println s!"\n-- KILL + RESTART (fresh read of {logPath}, empty memory) --"
  let bytes ← IO.FS.readBinFile logPath
  let events := Control.Store.recoverStore bytes.toList
  if events.isEmpty then
    do IO.eprintln "gate: durable log failed to decode after restart"; return 1
  let restored := Control.Store.replay events
  IO.println s!"replayed {events.length} events from disk; registry has {restored.control.nodes.length} node(s)"
  let some regNode := Control.lookupReg restored.control.nodes nodeKey
    | do IO.eprintln "gate: node LOST after restart (re-registration would be required) — FAIL"; return 1
  let stillAuthorized := regNode.status == NodeStatus.authorized
  IO.println s!"registered node key[0]={regNode.nodeKey.pub.headD 0} recovered, status={repr regNode.status}, authorized={stillAuthorized}"
  -- serve the netmap AGAIN on the restored registry — WITHOUT the node re-registering
  let served2 := servedControl restored.control.nodes
  let (_, reply2) := Control.step (Control.PreAuth.preAuthPolicy sha256Bytes (restored.preauth.map paRecordOf) now) served2 (.mapPoll (pollReqOf nodeKey))
  let servedAgain := (match reply2 with | .mapResp (.full _) => true | _ => false)
  IO.println s!"post-restart map-poll (NO re-register) served a full netmap : {servedAgain}"

  if authorized && !rejected && filterIsAcl && derpNamesDrorb && stillAuthorized && servedAgain then do
    IO.println "\nPASS — pre-auth key MINTED (hashed at rest), node ADMITTED by the proven"
    IO.println "       registerWithPreAuth gate, events PERSISTED, MapResponse served with the"
    IO.println "       ACL-compiled PacketFilter + drorb DERPMap; after KILL+RESTART the durable"
    IO.println "       log REPLAYED and the node is STILL known + authorized (no re-register)."
    IO.println "LIVE PRE-AUTH REGISTER + DURABLE PERSISTENCE COMPLETE (drorb-native, proven gate + replay)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the pre-auth register / persistence pipeline did not cross-check."
    return 1

/-! ## The selftest — both ends over the byte level -/

def selftest : IO UInt32 := do
  IO.println "== control-live selftest : ts2021 Noise-IK control plane, byte-level, both ends =="

  -- Key material (curve25519 scalars; clamping handled inside x25519).
  let mpriv   := ofHex "a01111111111111111111111111111111111111111111111111111111111111a"  -- node machine static
  let nEpriv  := ofHex "c03333333333333333333333333333333333333333333333333333333333333c"  -- node ephemeral
  let sPriv   := ofHex "b02222222222222222222222222222222222222222222222222222222222222b"  -- coord server static
  let sEpriv  := ofHex "d04444444444444444444444444444444444444444444444444444444444444d"  -- coord ephemeral
  let noKPriv := ofHex "e05555555555555555555555555555555555555555555555555555555555555e"  -- node overlay node-key
  let dsKPriv := ofHex "f06666666666666666666666666666666666666666666666666666666666666f"  -- node disco key

  let some mpub  := Crypto.x25519Base mpriv  | do IO.eprintln "x25519Base(machine) failed"; return 1
  let some nEpub := Crypto.x25519Base nEpriv | do IO.eprintln "x25519Base(node eph) failed"; return 1
  let some sPub  := Crypto.x25519Base sPriv  | do IO.eprintln "x25519Base(server static) failed"; return 1
  let some sEpub := Crypto.x25519Base sEpriv | do IO.eprintln "x25519Base(server eph) failed"; return 1
  let some nkPub := Crypto.x25519Base noKPriv | do IO.eprintln "x25519Base(node key) failed"; return 1
  let some dsPub := Crypto.x25519Base dsKPriv | do IO.eprintln "x25519Base(disco key) failed"; return 1

  let nodeOverlayKey : NodeKey := ⟨bytesOf nkPub⟩
  let nodeDiscoKey   : DiscoKey := ⟨bytesOf dsPub⟩
  let nodeMachineKey : MachineKey := ⟨bytesOf mpub⟩

  IO.println s!"node machine  pub : {toHex mpub}"
  IO.println s!"node overlay  key : {toHex nkPub}"
  IO.println s!"coord server  pub : {toHex sPub}"

  -- ── 1. the BYTE-EXACT ts2021 handshake, both ends, through the PROVEN FSM ──
  let nodeSess : Control.Channel.Ts2021.Session :=
    { role := .node, version := tsVersion, spriv := mpriv, spub := mpub,
      epriv := nEpriv, epub := nEpub, peerS := sPub }
  let coordSess : Control.Channel.Ts2021.Session :=
    { role := .coord, version := tsVersion, spriv := sPriv, spub := sPub,
      epriv := sEpriv, epub := sEpub, peerS := ByteArray.empty }

  -- node: .fresh --start--> .awaitResp, EMITTING the 101-byte initiation frame
  let (nodeP1, o1) := Control.Channel.Ts2021.step nodeSess .fresh .start
  let some initFrame := (match o1 with | .sendInit f => some f | _ => none)
    | do IO.eprintln "node did not emit an initiation frame"; return 1
  -- coord: .fresh --recvInit--> .up on THAT frame, emitting the 51-byte response
  let (coordP, oc) := Control.Channel.Ts2021.step coordSess .fresh (.recvInit initFrame)
  let some respFrame := (match oc with | .sendResp f => some f | _ => none)
    | do IO.eprintln "coord did not emit a response frame"; return 1
  -- node: .awaitResp --recvResp--> .up on THAT frame
  let (nodeP,  _on) := Control.Channel.Ts2021.step nodeSess nodeP1 (.recvResp respFrame)

  let some coordTx := (match coordP with | .up tx => some tx | _ => none)
    | do IO.eprintln "coord did not reach .up"; return 1
  let some nodeTx := (match nodeP with | .up tx => some tx | _ => none)
    | do IO.eprintln "node did not reach .up"; return 1

  let keysAgree :=
    (nodeTx.send.toList == coordTx.recv.toList) && (nodeTx.recv.toList == coordTx.send.toList)
  let ifa := baOf initFrame
  let rfa := baOf respFrame
  let framesExact :=
    initFrame.length == 101 && respFrame.length == 51 &&
    (ifa.get! 2 == 1) && (ifa.get! 0 == 0 && ifa.get! 1 == 138) &&
    (ifa.get! 3 == 0 && ifa.get! 4 == 96) &&
    (rfa.get! 0 == 2) && (rfa.get! 1 == 0 && rfa.get! 2 == 48) &&
    (ifa.extract 5 37).data.toList == nEpub.data.toList &&
    (rfa.extract 3 35).data.toList == sEpub.data.toList
  IO.println "\n-- handshake (BYTE-EXACT controlbase ts2021) --"
  IO.println s!"initiation frame : {initFrame.length}B  {toHexL (initFrame.take 5)}... (ver|type|len header)"
  IO.println s!"response   frame : {respFrame.length}B  {toHexL (respFrame.take 3)}... (type|len header)"
  IO.println s!"frames match messages.go layout (101/51, ver=138, type 1/2, len 96/48, cleartext e) : {framesExact}"
  IO.println s!"node  send key : {toHex nodeTx.send}"
  IO.println s!"coord recv key : {toHex coordTx.recv}"
  IO.println s!"transport keys agree (node.send==coord.recv ∧ node.recv==coord.send) : {keysAgree}"
  if !keysAgree then do IO.eprintln "handshake keys did NOT agree"; return 1
  if !framesExact then do IO.eprintln "handshake frames were NOT byte-exact"; return 1
  IO.println "handshake UP (byte-exact Noise_IK; `Ts2021.handshake_refines` realized on real crypto)."

  -- ── the coordination server's world: one already-authorized peer to hand down ──
  let peerNode : Node :=
    { id := 42, stableID := "peer-stable-id".toUTF8.toList,
      name := "peer.example.ts.net".toUTF8.toList, user := 1,
      key := ⟨dummyKey 0xab⟩, machine := ⟨dummyKey 0xcd⟩, disco := ⟨dummyKey 0xef⟩,
      addresses  := [{ addr := [100,64,0,2], bits := 32 }],
      allowedIPs := [{ addr := [100,64,0,2], bits := 32 }, { addr := [10,0,0,0], bits := 24 }],
      endpoints  := [{ addr := [192,168,1,50], port := 41641 }],
      derp := 1, online := true, keyExpiry := 0, authorized := true }
  let peerReg : Registration := { nodeKey := peerNode.key, node := peerNode, status := .authorized }
  let serverDns : DnsConfig :=
    { domains := ["example.ts.net".toUTF8.toList],
      records := [(peerNode.name, [100,64,0,2])] }
  let serverFilter : PacketFilter :=
    [{ srcIPs := [{ addr := [100,64,0,0], bits := 10 }],
       dstPorts := [{ net := { addr := [100,64,0,0], bits := 10 }, ports := { first := 0, last := 65535 } }],
       protos := [] }]
  let s0 : ControlState := { nodes := [peerReg], filter := serverFilter, dns := serverDns }
  let pol : Policy := { authorizes := fun _ _ => true }

  -- ── the post-handshake TRANSPORT RECORD layer: one RecordState per direction ──
  -- Each direction keeps its own big-endian record counter (`controlbase`
  -- conn.go). node→coord and coord→node advance independently; every seal/open
  -- runs through the exhaustion-checked entry point (`sealMsg`/`openMsg`), never
  -- a hand-picked nonce. The node-send and coord-send counters start at 0.
  let mut nodeSend  : Control.Ts2021Record.RecordState := ⟨nodeTx.send, 0⟩
  let mut coordRecv : Control.Ts2021Record.RecordState := ⟨coordTx.recv, 0⟩
  let mut coordSend : Control.Ts2021Record.RecordState := ⟨coordTx.send, 0⟩
  let mut nodeRecv  : Control.Ts2021Record.RecordState := ⟨nodeTx.recv, 0⟩

  -- ── 2. node → RegisterRequest, sealed through nodeSend@0; coord opens through coordRecv@0 ──
  let regReq : RegisterRequest :=
    { version := 1, nodeKey := nodeOverlayKey, oldNodeKey := ⟨[]⟩, machineKey := nodeMachineKey,
      authKey := "tskey-auth-selftest".toUTF8.toList, expiry := 0, ephemeral := false, followup := false }
  let .ok (regFrame, nodeSend') := Control.Ts2021Record.sealMsg Control.putRegReq nodeSend regReq
    | do IO.eprintln "sealMsg RegisterRequest refused (errCipherExhausted or AEAD)"; return 1
  let .ok (regReq', coordRecv') := Control.Ts2021Record.openMsg (Control.getRegReq) coordRecv regFrame
    | do IO.eprintln "coord could not open RegisterRequest"; return 1
  nodeSend := nodeSend'; coordRecv := coordRecv'
  let regOk := regReq' == regReq && nodeSend.ctr == 1 && coordRecv.ctr == 1
  IO.println "\n-- register (record counter 0 -> 1, node->coord) --"
  IO.println s!"node -> RegisterRequest frame ({(baOf regFrame).size}B) @ctr 0, coord opened @ctr 0, decoded==sent, both ctr->1 : {regOk}"
  if !regOk then do IO.eprintln "RegisterRequest did not round-trip through RecordState"; return 1
  let (s1, regReply) := Control.step pol s0 (.register regReq')
  let regAuthorized :=
    match regReply with | .registerResp r => r.machineAuthorized | _ => false
  IO.println s!"coord Control.step .register -> machineAuthorized : {regAuthorized}"
  if !regAuthorized then do IO.eprintln "node was not authorized"; return 1

  -- ── 3. node → MapRequest, sealed through nodeSend@1 (SAME counter, +1); coord opens @1 ──
  let mapReq : MapRequest :=
    { version := 1, nodeKey := nodeOverlayKey, discoKey := nodeDiscoKey,
      endpoints := [{ addr := [192,168,1,10], port := 41641 }],
      stream := true, omitPeers := false, readOnly := false }
  let .ok (mapFrame, nodeSend'') := Control.Ts2021Record.sealMsg Control.putMapReq nodeSend mapReq
    | do IO.eprintln "sealMsg MapRequest refused (errCipherExhausted or AEAD)"; return 1
  let .ok (mapReq', coordRecv'') := Control.Ts2021Record.openMsg (Control.getMapReq) coordRecv mapFrame
    | do IO.eprintln "coord could not open MapRequest"; return 1
  nodeSend := nodeSend''; coordRecv := coordRecv''
  let mapOk := mapReq' == mapReq && nodeSend.ctr == 2 && coordRecv.ctr == 2
  IO.println "\n-- map poll (record counter 1 -> 2, node->coord, one counter for the direction) --"
  IO.println s!"node -> MapRequest frame ({(baOf mapFrame).size}B) @ctr 1, coord opened @ctr 1, decoded==sent, both ctr->2 : {mapOk}"
  if !mapOk then do IO.eprintln "MapRequest did not round-trip through RecordState"; return 1
  let (_s2, mapReply) := Control.step pol s1 (.mapPoll mapReq')
  let some mresp := (match mapReply with | .mapResp m => some m | _ => none)
    | do IO.eprintln "coord REJECTED the poll (node not authorized?)"; return 1

  -- ── 4. coord seals MapResponse through coordSend@0; node opens through nodeRecv@0 ──
  --    (the coord→node direction has its OWN counter, independent of node→coord above)
  let .ok (respFrame, coordSend') := Control.Ts2021Record.sealMsg Control.Channel.putMapResp coordSend mresp
    | do IO.eprintln "sealMsg MapResponse refused (errCipherExhausted or AEAD)"; return 1
  let .ok (mresp', nodeRecv') := Control.Ts2021Record.openMsg (Control.Channel.getMapResp) nodeRecv respFrame
    | do IO.eprintln "node could not open MapResponse"; return 1
  coordSend := coordSend'; nodeRecv := nodeRecv'
  IO.println "\n-- map response (record counter 0 -> 1, coord->node, independent direction) --"
  IO.println s!"coord -> MapResponse frame ({(baOf respFrame).size}B) @ctr 0, node opened @ctr 0, both ctr->1 : {coordSend.ctr == 1 && nodeRecv.ctr == 1}"

  -- the node's current (self-only) netmap, before folding the server's response
  let selfNode : Node :=
    { id := 0, stableID := [], name := "self.example.ts.net".toUTF8.toList, user := 1,
      key := nodeOverlayKey, machine := nodeMachineKey, disco := nodeDiscoKey,
      addresses := [{ addr := [100,64,0,1], bits := 32 }], allowedIPs := [], endpoints := [],
      derp := 1, online := true, keyExpiry := 0, authorized := true }
  let nm0 : NetMap := { self := selfNode, peers := [], dns := DnsConfig.empty, packetFilter := [] }

  let nmApplied := nm0.applyDelta mresp'          -- fold the decoded response
  let wgPeers   := nmApplied.toWgPeers            -- program the WireGuard peer table
  let dnsResult := nmApplied.dns.resolve peerNode.name  -- MagicDNS resolution over the netmap DNS

  IO.println s!"\n-- netmap applied (coord -> node, {(baOf respFrame).size}B sealed frame) --"
  IO.println s!"peers in netmap        : {nmApplied.peers.length}"
  IO.println s!"packet-filter rules    : {nmApplied.packetFilter.length}"
  for p in wgPeers do
    let cidrs := p.allowed.map (fun c => s!"{c.addr}/{c.plen}")
    IO.println s!"  WG peer  spub={toHex p.spub}  allowedIPs={cidrs}"
  match dnsResult with
  | some addr => IO.println s!"MagicDNS resolve       : {textOrHex peerNode.name} -> {addr}"
  | none      => IO.println s!"MagicDNS resolve       : {textOrHex peerNode.name} -> (no record)"

  -- ── 5. the faithfulness cross-check: wire decode∘fold∘toWgPeers == model decision ──
  -- `control_applies_netmap_faithfully` PROVES these are equal for the sealed frame;
  -- here we witness it on the concrete bytes (spub key lists compared).
  let modelWg := (nm0.applyDelta mresp).toWgPeers
  let wireKeys  := wgPeers.map (fun p => p.spub.toList)
  let modelKeys := modelWg.map (fun p => p.spub.toList)
  let faithful := (wireKeys == modelKeys) && !wgPeers.isEmpty
  let dnsGood := dnsResult == some ([100,64,0,2] : Control.Bytes)

  IO.println "\n-- cross-check (realizes control_applies_netmap_faithfully) --"
  IO.println s!"wire WG peers == model WG peers : {wireKeys == modelKeys}"
  IO.println s!"WG peer table non-empty         : {!wgPeers.isEmpty}"
  IO.println s!"MagicDNS resolved as expected   : {dnsGood}"

  -- ── 6. EXHAUSTION enforcement: a near-exhaustion send counter REFUSES ──
  -- `controlbase` (conn.go) declares the cipher exhausted at invalidNonce=2^64-1
  -- (errCipherExhausted). The proof `sealChecked_exhausted` makes that refusal
  -- total; here we witness it live: a RecordState sitting at invalidNonce refuses
  -- to seal (no frame is produced), while the last valid counter (2^64-2) still
  -- seals. `sealMsg` refusing at the boundary is the enforcement the live loop
  -- inherits, so no frame is ever emitted under an out-of-range record nonce.
  let exhaustedTx : Control.Ts2021Record.RecordState := ⟨coordTx.send, Control.Ts2021Wire.invalidNonce⟩
  let lastValidTx : Control.Ts2021Record.RecordState := ⟨coordTx.send, Control.Ts2021Wire.invalidNonce - 1⟩
  let exhaustedRefuses :=
    match Control.Ts2021Record.sealMsg Control.Channel.putMapResp exhaustedTx mresp with
    | .error Control.Ts2021Record.RecordErr.exhausted => true
    | _                                               => false
  let lastValidSeals :=
    match Control.Ts2021Record.sealMsg Control.Channel.putMapResp lastValidTx mresp with
    | .ok _ => true
    | _     => false
  IO.println "\n-- exhaustion (errCipherExhausted at counter 2^64-1) --"
  IO.println s!"send counter = 2^64-1 (invalidNonce) REFUSES to seal (errCipherExhausted) : {exhaustedRefuses}"
  IO.println s!"send counter = 2^64-2 (last valid)   still seals                          : {lastValidSeals}"

  let counters := regOk && mapOk && (coordSend.ctr == 1) && (nodeRecv.ctr == 1)
    && exhaustedRefuses && lastValidSeals

  if keysAgree && framesExact && regOk && regAuthorized && mapOk && faithful && dnsGood && counters then do
    IO.println "\nPASS — BYTE-EXACT handshake UP, node authorized, netmap applied, WG peers programmed;"
    IO.println "       control messages sealed/opened through the big-endian RecordState (per-direction"
    IO.println "       counters 0→1→2 and 0→1), exhaustion refused at 2^64-1;"
    IO.println "       the decode→apply→toWgPeers chain equals the proven model decision."
    IO.println "FULL CONTROL-PLANE EXCHANGE COMPLETE (drorb-native, byte-level, verified crypto+codec)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the control-plane pipeline did not cross-check."
    return 1

/-! ## Phase-1 : two REAL processes over TCP (coord + node)

The selftest above drove both ends over the byte level in ONE process. Here they
are split into two OS processes speaking over a real TCP socket. The socket
carries three things: the **byte-exact 101-byte `controlbase` initiation frame**,
the **byte-exact 51-byte response frame**, and length-prefixed sealed control
frames. The `Control.Channel.Ts2021.step` FSM and the sealed-frame codecs are the
SAME proven functions the selftest used; only the transport changed. Each
handshake frame is read header-first — `[type/ver][…][len:u16BE]` fixes how many
bytes follow — so the host trusts the wire length field, exactly as
`handshake_refines` pins the layouts. -/

def recvTimeout : UInt32 := 15000

/-- Big-endian 4-byte length prefix (untrusted socket framing, distinct from the
proven inner frame codec — the C-shim sibling of DerpLive's `be32`). -/
def be32enc (n : Nat) : ByteArray :=
  ByteArray.mk #[(n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]
def be32dec (b : ByteArray) : Nat :=
  (b.get! 0).toNat * 16777216 + (b.get! 1).toNat * 65536 + (b.get! 2).toNat * 256 + (b.get! 3).toNat

/-- Send a sealed control frame length-prefixed. -/
def sendFrame (fd : UInt32) (frame : Control.Bytes) : IO Unit := do
  let fb := baOf frame
  tcpSend fd (be32enc fb.size)
  tcpSend fd fb

/-- Read one length-prefixed sealed control frame off the stream. -/
def recvFrame (fd : UInt32) : IO (Option Control.Bytes) := do
  match ← tcpRecvExact fd 4 recvTimeout with
  | none => return none
  | some hb =>
    match ← tcpRecvExact fd (UInt32.ofNat (be32dec hb)) recvTimeout with
    | none => return none
    | some pb => return some (bytesOf pb)

/-- Shared fixed key material of this drorb-native test tailnet — the SAME
constants the selftest uses, so the two processes' Noise-IK handshake agrees. A
real tailnet supplies these per device out of band (the named residual). -/
structure Km where
  mpriv : ByteArray
  mpub : ByteArray
  nEpriv : ByteArray
  nEpub : ByteArray
  sPriv : ByteArray
  sPub : ByteArray
  sEpriv : ByteArray
  sEpub : ByteArray
  nkPub : ByteArray
  dsPub : ByteArray

def mkKeys : IO (Option Km) := do
  let mpriv   := ofHex "a01111111111111111111111111111111111111111111111111111111111111a"
  let nEpriv  := ofHex "c03333333333333333333333333333333333333333333333333333333333333c"
  let sPriv   := ofHex "b02222222222222222222222222222222222222222222222222222222222222b"
  let sEpriv  := ofHex "d04444444444444444444444444444444444444444444444444444444444444d"
  let noKPriv := ofHex "e05555555555555555555555555555555555555555555555555555555555555e"
  let dsKPriv := ofHex "f06666666666666666666666666666666666666666666666666666666666666f"
  match Crypto.x25519Base mpriv, Crypto.x25519Base nEpriv, Crypto.x25519Base sPriv,
        Crypto.x25519Base sEpriv, Crypto.x25519Base noKPriv, Crypto.x25519Base dsKPriv with
  | some mpub, some nEpub, some sPub, some sEpub, some nkPub, some dsPub =>
      return some { mpriv, mpub, nEpriv, nEpub, sPriv, sPub, sEpriv, sEpub, nkPub, dsPub }
  | _, _, _, _, _, _ => return none

/-- The coord's already-authorized peer + tailnet config (drorb-native world). -/
def coordState : ControlState :=
  let peerNode : Node :=
    { id := 42, stableID := "peer-stable-id".toUTF8.toList,
      name := "peer.example.ts.net".toUTF8.toList, user := 1,
      key := ⟨dummyKey 0xab⟩, machine := ⟨dummyKey 0xcd⟩, disco := ⟨dummyKey 0xef⟩,
      addresses  := [{ addr := [100,64,0,2], bits := 32 }],
      allowedIPs := [{ addr := [100,64,0,2], bits := 32 }, { addr := [10,0,0,0], bits := 24 }],
      endpoints  := [{ addr := [192,168,1,50], port := 41641 }],
      derp := 1, online := true, keyExpiry := 0, authorized := true }
  { nodes := [{ nodeKey := peerNode.key, node := peerNode, status := .authorized }],
    filter :=
      [{ srcIPs := [{ addr := [100,64,0,0], bits := 10 }],
         dstPorts := [{ net := { addr := [100,64,0,0], bits := 10 }, ports := { first := 0, last := 65535 } }],
         protos := [] }],
    dns := { domains := ["example.ts.net".toUTF8.toList],
             records := [(peerNode.name, [100,64,0,2])] } }

/-- Read one byte-exact `controlbase` handshake frame off the stream. The
initiation frame is `[ver:u16BE][type=1][len:u16BE][noise]` (5-byte header) and
the response is `[type=2][len:u16BE][noise]` (3-byte header): peek the leading
byte to tell them apart, read the fixed header, then read `len` more bytes. The
host reads exactly what the length field declares — the frame layout
`Control.Channel.Ts2021.handshake_refines` proves. -/
def recvHandshakeFrame (fd : UInt32) : IO (Option Control.Bytes) := do
  -- one byte to disambiguate: 0x01 leads an initiation's version (u16BE, so the
  -- high byte is 0 for versions < 256... but the type byte at offset 2 is the
  -- reliable tag); we branch on message type by reading the 5-byte-or-3-byte head.
  match ← tcpRecvExact fd 3 recvTimeout with
  | none => return none
  | some head3 =>
    -- response: [type=2][len:u16BE]
    if head3.get! 0 == 2 then
      let len := (head3.get! 1).toNat * 256 + (head3.get! 2).toNat
      match ← tcpRecvExact fd (UInt32.ofNat len) recvTimeout with
      | none => return none
      | some body => return some (bytesOf (head3 ++ body))
    else
      -- initiation: [ver:u16BE][type=1][len:u16BE]; we have 3 of the 5 header
      -- bytes (ver_hi, ver_lo, type); read the 2-byte length, then the payload.
      match ← tcpRecvExact fd 2 recvTimeout with
      | none => return none
      | some lenb =>
        let len := (lenb.get! 0).toNat * 256 + (lenb.get! 1).toNat
        match ← tcpRecvExact fd (UInt32.ofNat len) recvTimeout with
        | none => return none
        | some body => return some (bytesOf (head3 ++ lenb ++ body))

/-- Read the durable event log off disk, TORN-TAIL TOLERANT. The bytes go to the
PROVEN `Control.Store.recoverStore`: a store carrying the framed (append-only) magic
is recovered frame by frame, so every event durably appended before a torn tail
survives (`Control.Store.recoverStore_torn_write` — a coordinator SIGKILLed part-way
through an append replays to exactly its pre-append state); a store written by an
older drorb still loads through the legacy count-prefixed decoder
(`Control.Store.recoverStore_legacy`). A missing file is the empty log.

This replaces an all-or-nothing `decodeLog`: ONE truncated byte used to make the
whole log undecodable and the coordinator started EMPTY, so every node lost its
address on the next poll. -/
def loadLog (logPath : String) : IO (List Control.Store.Event) := do
  try
    let bytes ← IO.FS.readBinFile logPath
    pure (Control.Store.recoverStore bytes.toList)
  catch _ => return []

/-- COORD process: replay the durable log on startup (restart-safe), accept a node, drive
the responder handshake to `.up`, then run the PROVEN pre-auth register gate
(`registerWithPreAuth` under `preAuthPolicy`), emit a sealed `RegisterResponse`, PERSIST
the `nodeRegistered` event, and serve the map-poll with the ACL PacketFilter + drorb
DERPMap. A second run against the same log replays it and knows the node already. -/
def coord (port : UInt16) (logPath : String) : IO UInt32 := do
  IO.println s!"== control-live COORD : ts2021 responder + pre-auth gate + durable log, 127.0.0.1:{port} =="

  -- ── replay the durable log on startup: recover the pre-restart registry + keys ──
  let events0 ← loadLog logPath
  let restored := Control.Store.replay events0
  IO.println s!"coord: replayed {events0.length} durable event(s) from {logPath}; registry has {restored.control.nodes.length} node(s)"
  for r in restored.control.nodes do
    IO.println s!"coord:   known node key[0]={r.nodeKey.pub.headD 0} status={repr r.status} (recovered, no re-register)"
  -- the admission key store: the fixed test key + any replayed minted keys
  let paStore : Control.PreAuth.Store :=
    (Control.PreAuth.mint sha256Bytes testAuthSecret reusableAttrs) :: restored.preauth.map paRecordOf

  let some k ← mkKeys | do IO.eprintln "coord: key derivation failed"; return 1
  let lfd ← tcpListen port
  IO.println "coord: listening; waiting for a node to connect..."
  let some cfd ← tcpAccept lfd 60000 | do IO.eprintln "coord: accept timed out"; tcpClose lfd; return 1
  IO.println "coord: node connected (accepted a real TCP connection)."

  -- 1. read the byte-exact 101-byte INITIATION frame, drive the FSM to .up
  let some initFrame ← recvHandshakeFrame cfd
    | do IO.eprintln "coord: no initiation frame"; tcpClose cfd; tcpClose lfd; return 1
  IO.println s!"coord: recv initiation frame ({initFrame.length}B, type={(baOf initFrame).get! 2})"
  let coordSess : Control.Channel.Ts2021.Session :=
    { role := .coord, version := tsVersion, spriv := k.sPriv, spub := k.sPub,
      epriv := k.sEpriv, epub := k.sEpub, peerS := ByteArray.empty }
  let (coordP, out) := Control.Channel.Ts2021.step coordSess .fresh (.recvInit initFrame)
  let some coordTx := (match coordP with | .up tx => some tx | _ => none)
    | do IO.eprintln "coord: handshake did not reach .up"; tcpClose cfd; tcpClose lfd; return 1
  match out with
  | .sendResp respFrame =>
      IO.println s!"coord: emit response frame ({respFrame.length}B, type={(baOf respFrame).get! 0})"
      tcpSend cfd (baOf respFrame)
  | _ => do IO.eprintln "coord: no response to emit"; tcpClose cfd; tcpClose lfd; return 1
  IO.println s!"coord: handshake UP (byte-exact); recv key : {toHex coordTx.recv}"

  let now := 0
  -- per-direction record counters: coord RECV reads node→coord (RegReq@0, MapReq@1);
  -- coord SEND writes coord→node (RegResp@0, MapResp@1). Every open/seal is checked.
  let mut coordRecv : Control.Ts2021Record.RecordState := ⟨coordTx.recv, 0⟩
  let mut coordSend : Control.Ts2021Record.RecordState := ⟨coordTx.send, 0⟩

  -- 2. sealed RegisterRequest -> PROVEN registerWithPreAuth gate -> sealed RegisterResponse
  let some regFrame ← recvFrame cfd | do IO.eprintln "coord: no RegisterRequest"; tcpClose cfd; tcpClose lfd; return 1
  let .ok (regReq', coordRecv') := Control.Ts2021Record.openMsg (Control.getRegReq) coordRecv regFrame
    | do IO.eprintln "coord: could not open RegisterRequest through RecordState"; tcpClose cfd; tcpClose lfd; return 1
  coordRecv := coordRecv'
  let admit := Control.PreAuth.registerWithPreAuth sha256Bytes paStore restored.control now regReq'
  let regAuthorized := admit.response.machineAuthorized
  IO.println s!"coord: opened RegisterRequest @rec-ctr 0 (->{coordRecv.ctr}); registerWithPreAuth (preAuthPolicy) -> machineAuthorized : {regAuthorized}"
  let .ok (regRespFrame, coordSend') := Control.Ts2021Record.sealMsg Control.putRegResp coordSend admit.response
    | do IO.eprintln "coord: sealMsg RegisterResponse refused"; tcpClose cfd; tcpClose lfd; return 1
  coordSend := coordSend'
  sendFrame cfd regRespFrame
  IO.println s!"coord: sealed RegisterResponse ({(baOf regRespFrame).size}B) @snd-ctr 0 delivered."
  -- PERSIST: append the nodeRegistered event (the DECISION) and rewrite the durable log
  let events1 := events0 ++ [ Control.Store.Event.nodeRegistered regReq' regAuthorized ]
  storeWriteAll logPath events1
  IO.println s!"coord: persisted nodeRegistered event -> {events1.length} events on disk ({logPath})."

  -- 3. sealed MapRequest -> Control.step .mapPoll on the ACL/DERP-wired served state
  let some mapFrame ← recvFrame cfd | do IO.eprintln "coord: no MapRequest"; tcpClose cfd; tcpClose lfd; return 1
  let .ok (mapReq', _) := Control.Ts2021Record.openMsg (Control.getMapReq) coordRecv mapFrame
    | do IO.eprintln "coord: could not open MapRequest through RecordState"; tcpClose cfd; tcpClose lfd; return 1
  let served := servedControl (demoPeerReg :: admit.state'.nodes)
  let (_s2, mapReply) := Control.step (Control.PreAuth.preAuthPolicy sha256Bytes paStore now) served (.mapPoll mapReq')
  let some mresp := (match mapReply with | .mapResp m => some m | _ => none)
    | do IO.eprintln "coord: rejected the poll (node not authorized?)"; tcpClose cfd; tcpClose lfd; return 1
  let .ok (respFrame, _) := Control.Ts2021Record.sealMsg Control.Channel.putMapResp coordSend mresp
    | do IO.eprintln "coord: sealMsg MapResponse refused"; tcpClose cfd; tcpClose lfd; return 1
  sendFrame cfd respFrame
  let filterN := match mresp with | .full nm => nm.packetFilter.length | _ => 0
  IO.println s!"coord: sealed MapResponse.full ({(baOf respFrame).size}B) @snd-ctr 1 delivered ({filterN} ACL filter rule(s), DERPMap names drorb relay)."
  tcpClose cfd; tcpClose lfd
  IO.println "coord: DONE (drorb-native responder, proven pre-auth gate + durable log, real TCP)."
  return 0

/-- NODE process: connect, drive the initiator handshake to `.up` over the
socket, register + poll, then apply the netmap and program the WG peers. -/
def node (host : String) (port : UInt16) : IO UInt32 := do
  IO.println s!"== control-live NODE : ts2021 initiator, connecting {host}:{port} =="
  let some k ← mkKeys | do IO.eprintln "node: key derivation failed"; return 1
  let nodeOverlayKey : NodeKey := ⟨bytesOf k.nkPub⟩
  let nodeDiscoKey   : DiscoKey := ⟨bytesOf k.dsPub⟩
  let nodeMachineKey : MachineKey := ⟨bytesOf k.mpub⟩

  let fd ← tcpConnect host port
  IO.println "node: connected (real TCP)."
  let nodeSess : Control.Channel.Ts2021.Session :=
    { role := .node, version := tsVersion, spriv := k.mpriv, spub := k.mpub,
      epriv := k.nEpriv, epub := k.nEpub, peerS := k.sPub }
  -- 1. .start EMITS the byte-exact 101-byte initiation frame; send it
  let (nodeP1, o1) := Control.Channel.Ts2021.step nodeSess .fresh .start
  let some initFrame := (match o1 with | .sendInit f => some f | _ => none)
    | do IO.eprintln "node: FSM did not emit an initiation frame"; tcpClose fd; return 1
  tcpSend fd (baOf initFrame)
  IO.println s!"node: sent byte-exact initiation frame ({initFrame.length}B)."
  -- receive the 51-byte response frame, drive .recvResp to .up
  let some respFrame ← recvHandshakeFrame fd
    | do IO.eprintln "node: no handshake response"; tcpClose fd; return 1
  IO.println s!"node: recv response frame ({respFrame.length}B, type={(baOf respFrame).get! 0})"
  let (nodeP, _on) := Control.Channel.Ts2021.step nodeSess nodeP1 (.recvResp respFrame)
  let some nodeTx := (match nodeP with | .up tx => some tx | _ => none)
    | do IO.eprintln "node: handshake did not reach .up"; tcpClose fd; return 1
  IO.println s!"node: handshake UP (byte-exact); send key : {toHex nodeTx.send}"

  -- the per-direction record counters: node's SEND counter writes node→coord
  -- frames (RegReq@0, MapReq@1); node's RECV counter reads coord→node (RegResp@0, MapResp@1).
  let mut nodeSend : Control.Ts2021Record.RecordState := ⟨nodeTx.send, 0⟩
  let mut nodeRecv : Control.Ts2021Record.RecordState := ⟨nodeTx.recv, 0⟩
  -- 2. seal + send RegisterRequest (send counter 0 -> 1), presenting the pre-auth key
  let regReq : RegisterRequest :=
    { version := 1, nodeKey := nodeOverlayKey, oldNodeKey := ⟨[]⟩, machineKey := nodeMachineKey,
      authKey := testAuthSecret, expiry := 0, ephemeral := false, followup := false }
  let .ok (regFrame, nodeSend') := Control.Ts2021Record.sealMsg Control.putRegReq nodeSend regReq
    | do IO.eprintln "node: sealMsg RegisterRequest refused"; tcpClose fd; return 1
  nodeSend := nodeSend'
  sendFrame fd regFrame
  IO.println s!"node: sent sealed RegisterRequest @ctr 0 (presenting pre-auth key)."
  -- read the sealed RegisterResponse (recv counter 0 -> 1); gate on machineAuthorized
  let some regRespFrame ← recvFrame fd | do IO.eprintln "node: no RegisterResponse"; tcpClose fd; return 1
  let .ok (regResp', nodeRecv') := Control.Ts2021Record.openMsg (Control.getRegResp) nodeRecv regRespFrame
    | do IO.eprintln "node: could not open RegisterResponse through RecordState"; tcpClose fd; return 1
  nodeRecv := nodeRecv'
  IO.println s!"node: opened RegisterResponse @ctr 0 -> machineAuthorized={regResp'.machineAuthorized}"
  if !regResp'.machineAuthorized then do
    IO.eprintln "node: coord REJECTED registration (pre-auth key not admitted)"; tcpClose fd; return 1
  -- 3. seal + send MapRequest (send counter 1 -> 2)
  let mapReq : MapRequest :=
    { version := 1, nodeKey := nodeOverlayKey, discoKey := nodeDiscoKey,
      endpoints := [{ addr := [192,168,1,10], port := 41641 }],
      stream := true, omitPeers := false, readOnly := false }
  let .ok (mapFrame, nodeSend'') := Control.Ts2021Record.sealMsg Control.putMapReq nodeSend mapReq
    | do IO.eprintln "node: sealMsg MapRequest refused"; tcpClose fd; return 1
  nodeSend := nodeSend''
  sendFrame fd mapFrame
  IO.println s!"node: sent sealed MapRequest @ctr 1 (send counter -> {nodeSend.ctr})."

  -- 4. recv sealed MapResponse, open through nodeRecv@1, applyDelta, toWgPeers
  let some respFrame ← recvFrame fd | do IO.eprintln "node: no MapResponse"; tcpClose fd; return 1
  let .ok (mresp', _) := Control.Ts2021Record.openMsg (Control.Channel.getMapResp) nodeRecv respFrame
    | do IO.eprintln "node: could not open MapResponse through RecordState"; tcpClose fd; return 1
  let selfNode : Node :=
    { id := 0, stableID := [], name := "self.example.ts.net".toUTF8.toList, user := 1,
      key := nodeOverlayKey, machine := nodeMachineKey, disco := nodeDiscoKey,
      addresses := [{ addr := [100,64,0,1], bits := 32 }], allowedIPs := [], endpoints := [],
      derp := 1, online := true, keyExpiry := 0, authorized := true }
  let nm0 : NetMap := { self := selfNode, peers := [], dns := DnsConfig.empty, packetFilter := [] }
  let nmApplied := nm0.applyDelta mresp'
  let wgPeers   := nmApplied.toWgPeers
  IO.println s!"node: opened + applied MapResponse ({(baOf respFrame).size}B) -> {nmApplied.peers.length} peer(s), {nmApplied.packetFilter.length} filter rule(s)."
  for p in wgPeers do
    let cidrs := p.allowed.map (fun c => s!"{c.addr}/{c.plen}")
    IO.println s!"node:   WG peer spub={toHex p.spub} allowedIPs={cidrs}"
  tcpClose fd
  if wgPeers.isEmpty then do
    IO.eprintln "node: FAIL — no WG peers programmed"; return 1
  else do
    IO.println "node: DONE — handshake UP, netmap applied, WG peers programmed over real TCP."
    return 0

/-! ## Phase-2 : HTTP/2 over the ts2021 Noise channel — the LAST transport layer

A stock tailscale client, after the byte-exact handshake, opens an HTTP/2 session
(prior-knowledge h2c) INSIDE the noise channel and sends the control RPCs as h2
requests (`POST /machine/register`, `POST /machine/map`). This driver feeds the
DECRYPTED noise-record plaintext into drorb's VERIFIED H2 engine
(`H2.Conn.feed`, via `Control.H2Noise.feedChunk`) and routes the requests to the
PROVEN pre-auth gate / served netmap (`Control.H2Noise.mkHandler`), sealing the h2
response bytes back into `controlbase` records. The record open/seal
(`Control.Ts2021Record`), the h2 engine, the gate and the JSON codec are all the
proven Lean, unchanged. -/

def h2RecvTimeout : UInt32 := 120000

/-- Split h2 output into ≤4000-byte records (< controlbase `maxPlaintextSize` = 4077). -/
partial def chunk4000 : List UInt8 → List (List UInt8)
  | [] => []
  | xs => xs.take 4000 :: chunk4000 (xs.drop 4000)

/-- Frame a raw record ciphertext as the `controlbase` wire record
`[type=4][len:u16BE][ciphertext]` (ByteArray). -/
def recordWireBA (ct : ByteArray) : ByteArray :=
  ByteArray.mk #[4, UInt8.ofNat (ct.size / 256), UInt8.ofNat (ct.size % 256)] ++ ct

/-- Seal the h2 output as `controlbase` records via the PROVEN record layer
(`Control.Ts2021Record.sealRecordTs2021`: `Ts2021Wire.sealRecord` framing at
`recordNonce ctr`) and send them; returns the advanced send counter. -/
def sendH2Out (fd : UInt32) (key : ByteArray) (sndCtr : Nat) (out : List UInt8) :
    IO (Option Nat) := do
  let mut ctr := sndCtr
  for chunk in chunk4000 out do
    -- PROVEN record layer: `Ts2021Wire.sealRecord` framing `[4][u16BE len][raw ct]`
    -- at `recordNonce ctr` (byte-exact controlbase; `record_seal_open`).
    match Control.Ts2021Record.sealRecordTs2021 ⟨key, ctr⟩ chunk with
    | some (frame, _) => tcpSend fd (baOf frame); ctr := ctr + 1
    | none => return none
  return some ctr

/-- The h2-over-noise loop: read one `controlbase` record `[4][len:u16BE][ct]`, OPEN it
through the PROVEN record layer (`Control.Ts2021Record.openRecordTs2021`, `Ts2021Wire.openRecord`
at `recordNonce recCtr`), feed the plaintext to the VERIFIED h2 engine, SEAL + send the
response records (`sealRecordTs2021`). Per-direction record counters threaded manually
(big-endian `recordNonce`). -/
partial def h2Loop (cfg : Control.H2Noise.Cfg) (fd : UInt32)
    (rKey sKey : ByteArray) (recCtr sndCtr : Nat) (st : H2.Conn.ConnState) : IO UInt32 := do
  match ← tcpRecvExact fd 3 h2RecvTimeout with
  | none => IO.println "h2coord: client closed the noise channel (h2 session ended)"; return 0
  | some hdr =>
    if hdr.get! 0 != 4 then do IO.eprintln s!"h2coord: non-record msg type {hdr.get! 0}"; return 1
    let len := (hdr.get! 1).toNat * 256 + (hdr.get! 2).toNat
    match ← tcpRecvExact fd (UInt32.ofNat len) h2RecvTimeout with
    | none => do IO.eprintln "h2coord: short record body"; return 1
    | some sealed =>
      -- PROVEN record layer: reconstruct the full controlbase frame and OPEN via
      -- `Ts2021Record.openRecordTs2021` (`Ts2021Wire.openRecord` at `recordNonce recCtr`).
      match Control.Ts2021Record.openRecordTs2021 ⟨rKey, recCtr⟩ (bytesOf hdr ++ bytesOf sealed) with
      | none => do IO.eprintln s!"h2coord: record @ctr {recCtr} failed to OPEN (AEAD)"; return 1
      | some (plain, _) =>
        let (st', out, close) := Control.H2Noise.feedChunk cfg st plain
        match ← sendH2Out fd sKey sndCtr out with
        | none => do IO.eprintln "h2coord: seal refused (cipher exhausted)"; return 1
        | some sndCtr' =>
          if close then do IO.println "h2coord: h2 engine closed (GOAWAY); done"; return 0
          else h2Loop cfg fd rKey sKey (recCtr + 1) sndCtr' st'

/-- COORD process speaking HTTP/2 over noise: drive the responder handshake to `.up`,
then run the h2-over-noise loop routing `/machine/register` (proven gate) and
`/machine/map` (served netmap). Splice target for `crates/dataplane/src/control.rs`. -/
def h2coord (port : UInt16) (logPath : String) : IO UInt32 := do
  IO.println s!"== control-live H2COORD : ts2021 + HTTP/2-over-noise control RPCs, 127.0.0.1:{port} =="
  let events0 ← loadLog logPath
  let restored := Control.Store.replay events0
  let paStore : Control.PreAuth.Store :=
    (Control.PreAuth.mint sha256Bytes testAuthSecret reusableAttrs)
      :: (Control.PreAuth.mint sha256Bytes (Control.H2Noise.s2b Control.H2Noise.demoSecretStr) reusableAttrs)
      :: restored.preauth.map paRecordOf
  let some k ← mkKeys | do IO.eprintln "h2coord: key derivation failed"; return 1
  IO.println s!"h2coord: server Noise static pub (set DRORB_CONTROL_NOISE_PUB to this) : {toHex k.sPub}"
  let lfd ← tcpListen port
  IO.println "h2coord: listening; waiting for a node to connect..."
  let some cfd ← tcpAccept lfd 120000 | do IO.eprintln "h2coord: accept timed out"; tcpClose lfd; return 1
  IO.println "h2coord: node connected."
  let some initFrame ← recvHandshakeFrame cfd
    | do IO.eprintln "h2coord: no initiation frame"; tcpClose cfd; tcpClose lfd; return 1
  IO.println s!"h2coord: recv initiation frame ({initFrame.length}B, type={(baOf initFrame).get! 2})"
  let coordSess : Control.Channel.Ts2021.Session :=
    { role := .coord, version := tsVersion, spriv := k.sPriv, spub := k.sPub,
      epriv := k.sEpriv, epub := k.sEpub, peerS := ByteArray.empty }
  let (coordP, out) := Control.Channel.Ts2021.step coordSess .fresh (.recvInit initFrame)
  let some coordTx := (match coordP with | .up tx => some tx | _ => none)
    | do IO.eprintln "h2coord: handshake did not reach .up"; tcpClose cfd; tcpClose lfd; return 1
  match out with
  | .sendResp respFrame =>
      IO.println s!"h2coord: emit response frame ({respFrame.length}B)"; tcpSend cfd (baOf respFrame)
  | _ => do IO.eprintln "h2coord: no response to emit"; tcpClose cfd; tcpClose lfd; return 1
  IO.println s!"h2coord: handshake UP; entering HTTP/2-over-noise. recv key: {toHex coordTx.recv}"
  let derpAdv ← derpAdvMap
  announceDerp "h2coord" derpAdv
  let cfg : Control.H2Noise.Cfg :=
    { store := paStore,
      control := Control.Join.coordState Control.Acl.demoPolicy Control.Join.demoDomains restored.control.nodes,
      now := 0,
      derp := derpAdv }
  let r ← h2Loop cfg cfd coordTx.recv coordTx.send 0 0 H2.Conn.initState
  tcpClose cfd; tcpClose lfd
  return r

/-! ## Phase-3 : a MULTI-NODE tailnet — persistent cross-connection ControlState + IPAM

`h2coord` (Phase 2) accepts ONE noise connection and serves it. A stock tailscale client
dials a FRESH noise connection per RPC (register, then map), and the served self-address
was the constant first-free IPAM address `100.64.0.1` on EVERY poll — so distinct nodes
all collided on `100.64.0.1` and multi-node was broken.

`h2coordMulti` is the fix. It holds a PERSISTENT cross-connection ControlState: a durable
`Control.Store` event log guarded by a `Std.Mutex`, surviving every connection AND a
restart-replay. The FIRST connection that carries a node's `NodeKey` (register or map)
triggers a PROVEN IPAM allocation (`Control.Ipam.cgnatPool.alloc (Control.Ipam.usedOf …)`,
distinct by `Control.Ipam.liveAlloc_distinct`); the coordinator appends
`nodeRegistered` + `addrAllocated` (kept stable by `Control.Store.addrAllocated_stable`)
and persists. Every subsequent map poll serves `Control.Join.servedNetMapWire` over the
replayed state: the node's OWN stable address as Self, the OTHER registered nodes as Peers
(each at its distinct address + the ACL). Two clients A/B thus get `100.64.0.1` /
`100.64.0.2` and see each other. Connections are handled concurrently (`IO.asTask`) so a
map long-poll never blocks another node's register.

Realization boundary (named): the node key is read back off the VERIFIED h2 engine's
successor `ConnState` (the request body the engine assembled into the closed stream), and
allocation/persistence is untrusted IO around the PROVEN `Ipam`/`Store` functions — the
same discipline as the record/handshake shims. -/

/-- Home a replayed registration on drorb's DERP region (+ online + a distinct id/name
derived from its stamped IPAM address), keeping its allocated `/32`. The durable
`nodeOf`/`addrAllocated` node carries `derp=0`/`id=0`/`name=[]`; this gives the served
netmap a real home DERP and a distinct identity so `tailscale status` shows each peer as a
distinct, addressed node. -/
def finalizeReg (r : Control.Registration) : Control.Registration :=
  let ipNat := (r.node.addresses.head?).elim 0 (fun p => Control.Ipam.v4ToNat p.addr)
  let idn := ipNat - Control.Ipam.cgnatPool.net
  { r with node := { r.node with
      derp := Control.Join.drorbRegionID, online := true, authorized := true,
      id := idn, machine := ⟨r.nodeKey.pub⟩,
      name := s!"node-{idn}.ts.net".toUTF8.toList,
      stableID := s!"drorb-{idn}".toUTF8.toList } }

/-! ### OPERATOR POLICY — the coord serves the ACL from a HuJSON FILE, not `demoPolicy`

A homelab runs ITS policy. `loadPolicy` reads a HuJSON file (path from `DRORB_POLICY`
or the CLI), parses it via the PROVEN `Control.Policy.parseHuPolicy` (`parsePolicy_wf` :
a `.ok` policy is a well-formed compiler input), and hands the resulting
`Control.Acl.Policy` to `servedFrom`, which compiles it via `Control.Acl.compile` inside
`Control.Join.coordState`. `Control.Join.servedNetMapWire_filters` then holds for the
OPERATOR policy: the served `PacketFilters["base"]` IS `(Acl.compile operatorPolicy)`,
projected — default-deny + the ACL-is-served theorem carry over verbatim (see
`ControlLive.servedFrom_filter_is_operator_compile` below).

★SAFE DEFAULT: an absent / unreadable / unparseable policy file yields `safeDefaultPolicy`
= the EMPTY policy `{ groups := [], acls := [] }`, whose `Acl.compile` is `[]` — the
**deny-all** filter (`Control.Join.served_empty_denies`). We fail CLOSED: a
misconfigured coord denies every flow, never opens one. -/

/-- The fail-closed default when no operator policy is available: deny everything.
`Control.Acl.compile safeDefaultPolicy = []`, the empty (default-deny) packet filter. -/
def safeDefaultPolicy : Control.Acl.Policy := { groups := [], acls := [] }

/-- Read + parse the operator HuJSON policy. Path precedence: explicit `pathOverride`,
else env `DRORB_POLICY`. On any failure (no path, missing file, HuJSON/`wf` reject) we
log and fall back to `safeDefaultPolicy` (deny-all) — the coord NEVER serves an
un-vetted filter. Returns the proven-well-formed `Control.Acl.Policy`. -/
def loadPolicy (pathOverride : Option String := none) : IO Control.Acl.Policy := do
  let path? ← match pathOverride with
    | some p => pure (some p)
    | none   => IO.getEnv "DRORB_POLICY"
  match path? with
  | none =>
      IO.println "policy: no DRORB_POLICY set — serving SAFE DEFAULT (deny-all)"
      pure safeDefaultPolicy
  | some path =>
      match ← (do try pure (some (← IO.FS.readFile path)) catch _ => pure none) with
      | none =>
          IO.eprintln s!"policy: cannot read '{path}' — serving SAFE DEFAULT (deny-all)"
          pure safeDefaultPolicy
      | some text =>
          match Control.Policy.parseHuPolicy text with
          | .ok pol =>
              IO.println s!"policy: loaded '{path}' — {pol.acls.length} ACL rule(s), {pol.groups.length} selector binding(s), {pol.tagOwners.length} tagOwner declaration(s); serving Acl.compile(withTagBindings(parsePolicy(file), registry))"
              pure pol
          | .error e =>
              IO.eprintln s!"policy: '{path}' REJECTED ({e}) — serving SAFE DEFAULT (deny-all)"
              pure safeDefaultPolicy

/-- The served coordination state, rebuilt from the durable event log on each poll: replay
it (`Control.Store.replay` — restart-sound), home + id/name every node (`finalizeReg`), and
wire the OPERATOR ACL-compiled filter + MagicDNS (`Control.Join.coordState pol`).
`servedNetMapWire` serves each node's stable Self + the other nodes as Peers from THIS,
with `PacketFilters["base"] = Acl.compile pol` (`servedFrom_filter_is_operator_compile`). -/
def servedRegs (events : List Control.Store.Event) : List Control.Registration :=
  (Control.Store.replay events).control.nodes.map finalizeReg

/-- The nodes whose tags may bind: only `.authorized` registrations. A node awaiting
`drorb-ctl nodes approve` (or one an operator EXPIRED — replay marks it `.expired`)
contributes no tag binding, so a pending device cannot be pre-tagged into reach.
★Residual, named: a node whose `keyExpiry` has passed WITHOUT a recorded `nodeExpired`
event is still `.authorized` here; `Control.Expiry` drops it from every served peer list
at serve time, so it has no path, but its address stays in the tag binding until the
clock event lands. See `Control.Tags`' "What is NOT proven". -/
def taggableNodes (regs : List Control.Registration) : List Control.Node :=
  (regs.filter (fun r => decide (r.status = Control.NodeStatus.authorized))).map (·.node)

/-- ★**The SERVED policy** = the operator's HuJSON policy with its `tag:` selectors bound
against the live registry, under the file's own `tagOwners` gate
(`Control.Tags.withTagBindings`). This is the only place `Acl.Policy.tags` is ever
written — `Control.Policy.parsePolicy_tags_empty` proves the file cannot write it. -/
def servedPolicy (pol : Control.Acl.Policy) (events : List Control.Store.Event)
    : Control.Acl.Policy :=
  Control.Tags.withTagBindings pol (taggableNodes (servedRegs events))

def servedFrom (pol : Control.Acl.Policy) (events : List Control.Store.Event) : Control.ControlState :=
  Control.Join.coordState (servedPolicy pol events) Control.Join.demoDomains
    (servedRegs events)

/-- ★**THE OPERATOR-ACL-IS-SERVED THEOREM.** For any operator policy `pol`, durable log,
and authorized key, the served wire `PacketFilters["base"]` IS the operator policy's ACL
compilation `(Control.Join.compiledPacketFilter pol) = (Acl.compile pol).map ruleConv`,
projected to the wire — NOT `demoPolicy`. Composes `Control.Join.servedNetMapWire_filters`
with `coordState`'s `filter := compiledPacketFilter pol` (definitional). With
`Control.Policy.parsePolicy_wf` (`pol` is well-formed) + `Control.Acl.policy_default_deny`,
the served filter for the OPERATOR FILE is sound default-deny. -/
theorem servedFrom_filter_is_operator_compile
    (pol : Control.Acl.Policy) (events : List Control.Store.Event) (k : Control.NodeKey)
    (r : Control.Registration)
    (h : Control.lookupReg (servedFrom pol events).nodes k = some r) :
    (Control.Join.servedNetMapWire (servedFrom pol events) k).packetFilters
      = some [("base", (Control.Join.compiledPacketFilter (servedPolicy pol events)).map
                Control.Join.filterRuleToWire)] :=
  -- `servedNetMapWire_filters` gives `= some [("base", (servedFrom pol events).filter.map …)]`;
  -- `(servedFrom pol events).filter` is definitionally `compiledPacketFilter (servedPolicy …)`
  -- (`coordState` sets `filter := compiledPacketFilter …`), so the RHS is accepted up to defeq.
  Control.Join.servedNetMapWire_filters (servedFrom pol events) k r h

/-- ★**THE SERVED TAG BINDINGS ARE THE REGISTRY PROJECTION.** The `tags` table the
compiler resolves `tag:` selectors through is *exactly* `Control.Tags.tagBindings` of the
policy's own `tagOwners` over the authorized registry — never anything the policy file
supplied (`Control.Policy.parsePolicy_tags_empty`). Composed with
`Control.Tags.tagBindings_owned`, every served tag binding names a tag its bearer's owner
is permitted to apply; composed with `Control.Tags.no_owned_bearer_dropped`, a source
that is not a legitimate bearer is default-DROPPED by the served filter. -/
theorem servedFrom_tags_are_registry_projection
    (pol : Control.Acl.Policy) (events : List Control.Store.Event) :
    (servedPolicy pol events).tags
      = Control.Tags.tagBindings pol.tagOwners (taggableNodes (servedRegs events)) := rfl

/-- **The binding step changes nothing else about the operator's policy** — same groups,
same ACL entries, same `tagOwners`. -/
theorem servedFrom_policy_preserved
    (pol : Control.Acl.Policy) (events : List Control.Store.Event) :
    (servedPolicy pol events).groups = pol.groups
    ∧ (servedPolicy pol events).acls = pol.acls
    ∧ (servedPolicy pol events).tagOwners = pol.tagOwners :=
  ⟨rfl, rfl, rfl⟩

-- The operator-ACL-is-served theorem is proof-irrelevant (only the standard axioms);
-- with `Control.Policy.parsePolicy_wf` the served operator filter is sound default-deny.
#print axioms servedFrom_filter_is_operator_compile
#print axioms paRecordOf_lossless
#print axioms paRecordOf_minted
#print axioms servedFrom_tags_are_registry_projection
#print axioms servedFrom_policy_preserved
#print axioms Control.Policy.parsePolicy_wf
#print axioms Control.Policy.parsePolicy_tags_empty
#print axioms Control.Tags.tagBindings_owned
#print axioms Control.Tags.no_owned_bearer_dropped
#print axioms Control.Policy.parsed_default_deny

/-- A minimal register-shaped request for a node key (used when only a map poll carried the
key; the `nodeRegistered` event only needs the key — the address is the `addrAllocated`). -/
def minimalReq (k : Control.NodeKey) : Control.RegisterRequest :=
  { version := 1, nodeKey := k, oldNodeKey := ⟨[]⟩, machineKey := ⟨k.pub⟩,
    authKey := [], expiry := 0, ephemeral := false, followup := false }

/-- Read the (nodeKey, register-shaped request) pairs the client sent on this connection,
off the VERIFIED h2 engine's successor `ConnState`: each completed stream's assembled body
(`H2.Conn.StreamRec.body`) is the request JSON; parse it as a `RegisterRequest` (else a
`MapRequest`) via the PROVEN `Control.Tailcfg` codec and bridge the node key
(`Control.H2Noise.coreKeyOf`, proven inverse). This is how the untrusted IO loop learns
WHICH node connected so it can IPAM-allocate + persist. -/
def reqKeysOf (st : H2.Conn.ConnState) : List (Control.NodeKey × Control.RegisterRequest) :=
  st.streams.filterMap (fun (p : Nat × H2.Conn.StreamRec) =>
    -- A stream whose body was already consumed (`pruneConsumed`) carries nothing to
    -- parse; skipping it here is what makes the drain O(live streams), not O(history).
    if p.2.body.isEmpty then none else
    (do
      let s ← String.fromUTF8? ⟨p.2.body.toArray⟩
      let j ← Control.TailcfgWire.parseStr s
      match Control.Tailcfg.RegisterRequest.fromJson? j with
      | some rr =>
          let k := Control.H2Noise.coreKeyOf rr.nodeKey
          some (k, Control.H2Noise.coreOf rr)
      | none =>
          match Control.Tailcfg.MapRequest.fromJson? j with
          | some mr =>
              let k := Control.H2Noise.coreKeyOf mr.nodeKey
              some (k, minimalReq k)
          | none => none))

/-- Bridge a wire `netip.AddrPort` string (`"a.b.c.d:port"`) to a core `Endpoint` via the
PROVEN `Control.Bridge.AddrPort4.ofText` (inverse of the `endpointToWire` renderer,
`AddrPort4.ofText_toText`). v4-only (the demo tailnet); a malformed / v6 endpoint is
dropped. -/
def coreEndpointOf (s : String) : Option Control.Endpoint := do
  let ap ← Control.Bridge.AddrPort4.ofText s
  some { addr := [ap.addr.a, ap.addr.b, ap.addr.c, ap.addr.d], port := ap.port }

/-- Read the (nodeKey, reported NAT state) pairs off the VERIFIED h2 engine's successor
`ConnState`: each completed stream body that parses as a `MapRequest` (proven codec)
carries the client's `DiscoKey` + `Endpoints` (`Control.RealMapKat.mapRequestPoll_discoKey`
/ `_endpoints` pin these on real capture bytes). The disco key is bridged via the proven
`Control.Bridge.DiscoKey.ofText`, each endpoint via `coreEndpointOf`. A request that
carried NEITHER a disco key NOR endpoints yields nothing (no NAT state to store). This is
how the untrusted loop learns a node's magicsock NAT state so it can serve it to peers
(`Control.Join.applyNatState` → `Control.Join.withNat_disco_served`). -/
def natReportOfStream (p : Nat × H2.Conn.StreamRec) :
    Option (Control.NodeKey × Control.Join.NatReport) :=
  -- Fast path for a CONSUMED body (`pruneConsumed`): semantics-identical to running the
  -- parse chain on `[]` (`natReportOfStream_empty_body_unguarded`), without the parse.
  if p.2.body.isEmpty then none else
  (do
    let s ← String.fromUTF8? ⟨p.2.body.toArray⟩
    let j ← Control.TailcfgWire.parseStr s
    let mr ← Control.Tailcfg.MapRequest.fromJson? j
    let disco : Control.DiscoKey :=
      ⟨(mr.discoKey.bind Control.Bridge.DiscoKey.ofText).getD []⟩
    let eps : List Control.Endpoint :=
      (mr.endpoints.getD []).filterMap coreEndpointOf
    if disco.pub.isEmpty && eps.isEmpty then none
    else some (Control.H2Noise.coreKeyOf mr.nodeKey, { disco := disco, endpoints := eps }))

/-- ★ The batch is emitted OLDEST-FIRST, and that ordering is load-bearing.
`H2.Conn.setStream` PREPENDS, and a completed body is never pruned from
`ConnState.streams`, so the live list is newest-FIRST and holds the node's whole
`MapRequest` history. `Control.Join.natUpsert` is last-write-wins, so consuming
`st.streams` in its native order applied the OLDEST report LAST: a node whose NAT mapping
had moved kept being served under its DEAD endpoint for the rest of the connection.
Invisible on one L2 (the endpoint set never changes); across two NATs it pins the tailnet
to the relay forever, because the peer punches at a port the NAT no longer maps.

Reversing here makes the batch chronological, which is exactly the hypothesis
`Control.Join.natUpsertAll_last_endpoints` needs; `natReportsOf_setStream_newest_last`
below discharges it. -/
def natReportsOf (st : H2.Conn.ConnState) : List (Control.NodeKey × Control.Join.NatReport) :=
  st.streams.reverse.filterMap natReportOfStream

/-- ★ **The MOST RECENTLY written stream's report is LAST in the batch.** For any
connection state, after the engine records a body on stream `sid` that yields a report,
`natReportsOf` ends with exactly that report — so the chronological fold
`Control.Join.natUpsertAll` stores it, and (by `natUpsertAll_last_endpoints`) the served
endpoints are the FRESH ones. This is the seam obligation the coordinator was violating. -/
theorem natReportsOf_setStream_newest_last
    (st : H2.Conn.ConnState) (sid : Nat) (sr : H2.Conn.StreamRec)
    (k : Control.NodeKey) (r : Control.Join.NatReport)
    (h : natReportOfStream (sid, sr) = some (k, r)) :
    ∃ pre, natReportsOf (H2.Conn.setStream st sid sr) = pre ++ [(k, r)] :=
  ⟨((st.streams.filter (fun q => q.1 != sid)).reverse).filterMap natReportOfStream, by
    simp [natReportsOf, H2.Conn.setStream, h]⟩

/-! ### §7.0c  PRUNING the consumed request bodies — the O(history) drain

`H2.Conn.setStream` PREPENDS and NOTHING ever removed a completed request body from
`H2.Conn.ConnState.streams`, so a node's whole `MapRequest` history stayed live on its
connection for as long as the connection did. Every reader above
(`natReportsOf` / `reqKeysOf` / `streamingMapOf`) walks that list and JSON-PARSES every
body it finds, and the coordinator runs all three on EVERY decrypted record. A stock
client sends a short `MapRequest{OmitPeers, Endpoints}` whenever magicsock's candidate
set moves, so on a long-lived tailnet the per-record work grows without bound in the
number of requests the node has already made, and so does the retained body memory.
That is the SAME defect the endpoint-ordering bug was a symptom of: the coordinator was
re-offering STALE reports because the stale bodies were still there to re-offer.

The fix is to consume a body ONCE. `pruneConsumed` clears the `body` of every stream
that is CLOSED and holds NO parked request (`H2.Conn.StreamRec.req = none`), which is
exactly the shape `H2.Conn.respond` / `H2.Conn.streamError` leave behind AFTER the
request was dispatched to the handler. The drain loops call it immediately after folding
the batch, so a report is folded exactly once, at the drain where its body completed.

**Why the engine cannot notice.** This used to be argued by ENUMERATING the two
`StreamRec.body` read sites in `H2/Conn.lean` (the DATA branch of `handleFrame`, and the
`respond … {req with body := sr.body}` in `finishTrailers`) and giving a guard for each.
That argument is only as good as the list: a third read site added tomorrow breaks it
silently. It is now a THEOREM over the engine's own transition function —
`H2.Conn.feed_congr`, transferred to this predicate as `feed_pruneConsumed` below: two
connection states that agree after pruning are INDISTINGUISHABLE to `feed`. Same output
octets, same close flag, successor states again agreeing after pruning. Every read site
is covered by construction, including any added later.

The naive shape of that commutation —
`feed cfg (pruneConsumed st) = pruneConsumed (feed cfg st)`, with no outer prune on the
left — is FALSE, and `H2.Conn.feed_pruneBodies_naive_false` exhibits the counterexample:
the ENGINE creates consumed bodies as it runs (a RST_STREAM, or any dispatched response,
leaves `.closed` / `req = none` with the assembled body still on the record), and only the
right-hand side gets to prune those. See `feed_pruneConsumed` for the difference, spelled
out. -/

/-- A stream whose request body has already been DISPATCHED: closed, with no parked
request head. `H2.Conn.respond` sets exactly this (`state := .closed`, `req := none`) on
the branch that finishes a response, and `H2.Conn.streamError` sets it on an aborted
stream. A stream still ACCUMULATING a body is `.open`/`.halfClosedRemote` and holds
`req := some _`, and the map long-poll stays `.halfClosedRemote` — neither is pruned. -/
def streamConsumed (p : Nat × H2.Conn.StreamRec) : Bool :=
  p.2.state == .closed && p.2.req.isNone

/-- ★ **Consume the folded bodies.** Clear the assembled request body of every stream
whose request was already dispatched, keeping the stream RECORD (its state, windows and
parked response bytes are untouched — the h2 engine's §5.1 accounting must not move).
Called by the drain loops immediately AFTER the batch is folded, so the next record's
drain re-parses only the bodies that are genuinely still live. -/
def pruneConsumed (st : H2.Conn.ConnState) : H2.Conn.ConnState :=
  { st with streams := st.streams.map (fun p =>
      if streamConsumed p then (p.1, { p.2 with body := [] }) else p) }

/-- Pruning touches ONLY `body`, and only on consumed streams: the stream ids, and every
field the h2 engine's protocol decisions read (`state`, `window`, `pending`, `req`,
`clen`, `recvd`), are pointwise unchanged. -/
theorem pruneConsumed_preserves_protocol_fields (st : H2.Conn.ConnState) :
    (pruneConsumed st).streams.map
        (fun p => (p.1, p.2.state, p.2.window, p.2.pending, p.2.req, p.2.clen, p.2.recvd))
      = st.streams.map
        (fun p => (p.1, p.2.state, p.2.window, p.2.pending, p.2.req, p.2.clen, p.2.recvd)) := by
  simp only [pruneConsumed, List.map_map]
  apply List.map_congr_left
  intro p _
  by_cases h : streamConsumed p <;> simp [Function.comp, h]

/-- The stream ids are unchanged, so `H2.Conn.getStream` still finds exactly the same
streams (with, at most, an emptied body). -/
theorem pruneConsumed_keys (st : H2.Conn.ConnState) :
    (pruneConsumed st).streams.map (·.1) = st.streams.map (·.1) := by
  simp only [pruneConsumed, List.map_map]
  apply List.map_congr_left
  intro p _
  by_cases h : streamConsumed p <;> simp [Function.comp, h]

/-- Pruning is idempotent: a second drain removes nothing further. -/
theorem pruneConsumed_idem (st : H2.Conn.ConnState) :
    pruneConsumed (pruneConsumed st) = pruneConsumed st := by
  have key : ∀ p : Nat × H2.Conn.StreamRec,
      (if streamConsumed (if streamConsumed p then (p.1, { p.2 with body := [] }) else p) then
        ((if streamConsumed p then (p.1, { p.2 with body := [] }) else p).1,
          { (if streamConsumed p then (p.1, { p.2 with body := [] }) else p).2 with body := [] })
      else (if streamConsumed p then (p.1, { p.2 with body := [] }) else p))
      = (if streamConsumed p then (p.1, { p.2 with body := [] }) else p) := by
    intro p
    by_cases h : streamConsumed p
    · have h2 : streamConsumed (p.1, { p.2 with body := ([] : H2.Bytes) }) = true := by
        simpa [streamConsumed] using h
      simp only [h, if_pos, h2]
    · simp only [h, if_neg, Bool.false_eq_true, if_false]
  simp only [pruneConsumed, List.map_map]
  congr 1
  refine List.map_congr_left (fun p _ => ?_)
  simpa [Function.comp] using key p

/-- A consumed stream carries NO body after the prune. -/
theorem pruneConsumed_body_gone (st : H2.Conn.ConnState) (p : Nat × H2.Conn.StreamRec)
    (hmem : p ∈ (pruneConsumed st).streams) (hc : streamConsumed p) : p.2.body = [] := by
  simp only [pruneConsumed, List.mem_map] at hmem
  obtain ⟨q, _, hq⟩ := hmem
  by_cases h : streamConsumed q
  · simp [h] at hq; subst hq; rfl
  · simp [h] at hq; subst hq; exact absurd hc (by simpa using h)

/-! #### One step of that proof, kept for readability

`step_closed_recvData_streamClosed` is the fact the DATA case of `H2.Conn.handleFrame_congr`
turns on: a closed stream refuses DATA with a §5.4.2 STREAM_CLOSED connection error decided
WITHOUT the body. It is a step of the theorem now, not the whole argument. -/

/-- A closed stream rejects DATA — so `handleFrame` never reaches `sr.body ++ data`. -/
theorem step_closed_recvData_streamClosed (es : Bool) :
    H2.Stream.step .closed (.recvData es) = .streamClosed := by
  cases es <;> rfl

/-! #### The reporting seam after pruning -/

/-- A stream with an EMPTY body yields no NAT report. (`natReportOfStream`'s fast path is
faithful: with an empty body the underlying parse chain — `String.fromUTF8? #[] = some ""`
then `Control.TailcfgWire.parseStr "" = none` — already returned `none`, so the guard
changes speed, not semantics; `natReportOfStream_empty_body_unguarded` states exactly
that.) -/
theorem natReportOfStream_empty_body (sid : Nat) (sr : H2.Conn.StreamRec)
    (h : sr.body = []) : natReportOfStream (sid, sr) = none := by
  simp [natReportOfStream, h]

/-- The fast path added no new behaviour: on an empty body the ORIGINAL parse chain
(no guard) evaluates to `none` on the nose. -/
theorem natReportOfStream_empty_body_unguarded (sid : Nat) (sr : H2.Conn.StreamRec)
    (h : sr.body = []) :
    (do
      let s ← String.fromUTF8? ⟨sr.body.toArray⟩
      let j ← Control.TailcfgWire.parseStr s
      let mr ← Control.Tailcfg.MapRequest.fromJson? j
      let disco : Control.DiscoKey :=
        ⟨(mr.discoKey.bind Control.Bridge.DiscoKey.ofText).getD []⟩
      let eps : List Control.Endpoint :=
        (mr.endpoints.getD []).filterMap coreEndpointOf
      if disco.pub.isEmpty && eps.isEmpty then none
      else some (Control.H2Noise.coreKeyOf mr.nodeKey, { disco := disco, endpoints := eps }))
      = (none : Option (Control.NodeKey × Control.Join.NatReport)) := by
  rw [h]; rfl

/-- ★ **NOTHING a pruned drain re-offers comes from a consumed stream.** After pruning,
`natReportsOf` is exactly the reports of the streams that are still LIVE — the completed
history contributes nothing, no matter where `H2.Conn.setStream` has since moved it in the
list. This is the property the ordering fix was compensating for: the fold no longer has
to be handed a chronological *history* because there IS no history in the batch. -/
theorem natReportsOf_pruneConsumed (st : H2.Conn.ConnState) :
    natReportsOf (pruneConsumed st)
      = (st.streams.filter (fun p => !streamConsumed p)).reverse.filterMap
          natReportOfStream := by
  simp only [natReportsOf, pruneConsumed, ← List.map_reverse, ← List.filter_reverse]
  generalize st.streams.reverse = l
  induction l with
  | nil => rfl
  | cons p t ih =>
      by_cases h : streamConsumed p
      · simp [List.filterMap_cons, List.filter_cons, h,
              natReportOfStream_empty_body p.1 { p.2 with body := [] } rfl, ih]
      · simp [List.filterMap_cons, List.filter_cons, h, ih]

/-- ★ **"Last one wins" survives pruning — and the seam obligation is discharged on the
PRUNED state too.** `natReportsOf_setStream_newest_last` is stated for an ARBITRARY
`ConnState`, so it holds verbatim of a pruned one: whatever the drain loop carries
forward, the next completed report is still LAST in the batch and therefore still the one
`Control.Join.natUpsertAll` stores. Pruning does not weaken the ordering property; it
removes the history the property had to defend against. -/
theorem natReportsOf_pruneConsumed_setStream_newest_last
    (st : H2.Conn.ConnState) (sid : Nat) (sr : H2.Conn.StreamRec)
    (k : Control.NodeKey) (r : Control.Join.NatReport)
    (h : natReportOfStream (sid, sr) = some (k, r)) :
    ∃ pre, natReportsOf (H2.Conn.setStream (pruneConsumed st) sid sr) = pre ++ [(k, r)] :=
  natReportsOf_setStream_newest_last (pruneConsumed st) sid sr k r h

/-- ★ **…and "last one wins" becomes TRIVIAL: the batch is a SINGLETON.** When every
stream the connection still carries has been consumed (the steady state of a drain loop
that prunes — the only live stream is the one whose body just completed), the batch the
coordinator folds is exactly `[(k, r)]`. `Control.Join.natUpsertAll_singleton` then makes
the fold a single `natUpsert`, so there is no ordering question left to get wrong: the
stale-endpoint bug is not merely ordered correctly, it is unrepresentable. -/
theorem natReportsOf_pruneConsumed_singleton
    (st : H2.Conn.ConnState) (sid : Nat) (sr : H2.Conn.StreamRec)
    (k : Control.NodeKey) (r : Control.Join.NatReport)
    (h : natReportOfStream (sid, sr) = some (k, r))
    (hall : ∀ p ∈ st.streams, streamConsumed p) :
    natReportsOf (H2.Conn.setStream (pruneConsumed st) sid sr) = [(k, r)] := by
  have hfil : ((pruneConsumed st).streams.filter (fun q => q.1 != sid)).reverse.filterMap
      natReportOfStream = [] := by
    simp only [pruneConsumed, ← List.map_reverse, ← List.filter_reverse, List.filter_map]
    generalize hl : st.streams.reverse = l
    have hall' : ∀ p ∈ l, streamConsumed p := by
      intro p hp; exact hall p (by rw [← List.mem_reverse, hl]; exact hp)
    clear hl
    induction l with
    | nil => rfl
    | cons q t ih =>
        have hq : streamConsumed q := hall' q (by simp)
        have ht : ∀ p ∈ t, streamConsumed p := fun p hp => hall' p (by simp [hp])
        by_cases hs : (q.1 != sid)
        · simp [List.filter_cons, List.filterMap_cons, hs, hq, Function.comp,
                natReportOfStream_empty_body q.1 { q.2 with body := [] } rfl, ih ht]
        · simp [List.filter_cons, List.filterMap_cons, hs, hq, Function.comp, ih ht]
  simp [natReportsOf, H2.Conn.setStream, h, hfil]

/-! #### ★ The engine-level licence: pruning a consumed body is UNOBSERVABLE

The two guards above are the two `StreamRec.body` read sites in today's
`H2/Conn.lean`, walked by hand. That argument is an ENUMERATION: it is only as good
as the list, and a third read site added tomorrow would break it silently.

`H2.Conn.feed_congr` replaces the enumeration with a theorem over the engine's own
transition function: two connection states that agree after pruning are
INDISTINGUISHABLE to `feed` — same output octets, same close flag, and successor
states that again agree after pruning. It is proven by induction over
`feed`/`pump`/`handleFrame`/`respond`/`flushAll`/`applySettings`, so every read site
is covered by construction, including any added later.

`pruneConsumed` IS that pruning (`pruneConsumed_eq_pruneBodies`, definitional), so the
statement transfers verbatim. -/

/-- `ControlLive.streamConsumed` is `H2.Conn.bodyConsumed` on the record. -/
theorem streamConsumed_eq_bodyConsumed (p : Nat × H2.Conn.StreamRec) :
    streamConsumed p = H2.Conn.bodyConsumed p.2 := rfl

/-- ★ `pruneConsumed` IS the engine-level pruning `H2.Conn.pruneBodies`. -/
theorem pruneConsumed_eq_pruneBodies (st : H2.Conn.ConnState) :
    pruneConsumed st = H2.Conn.pruneBodies st := by
  simp only [pruneConsumed, H2.Conn.pruneBodies]
  congr 1
  apply List.map_congr_left
  intro p _
  by_cases h : streamConsumed p = true
  · rw [if_pos h, H2.Conn.blindPair,
      H2.Conn.blindRec_of (show H2.Conn.bodyConsumed p.2 = true by
        rw [← streamConsumed_eq_bodyConsumed]; exact h)]
  · rw [if_neg h, H2.Conn.blindPair,
      H2.Conn.blindRec_of_not (show H2.Conn.bodyConsumed p.2 = false by
        rw [← streamConsumed_eq_bodyConsumed]; simpa using h)]

/-- ★ **THE COMMUTATION THEOREM the drain rests on.** Feeding the engine a state whose
CONSUMED bodies were pruned emits byte-identical output and the same close decision, and
lands in a state that differs from the unpruned run only in consumed bodies. No engine
step can read a body `pruneConsumed` cleared, because no engine step can tell the two
runs apart.

**How this differs from the naive form.** The naive statement
`feed cfg (pruneConsumed st) = pruneConsumed (feed cfg st)` — with NO outer prune on the
left — is FALSE, and `H2.Conn.feed_pruneBodies_naive_false` exhibits a counterexample (one
RST_STREAM). It fails for a reason that has nothing to do with the engine reading a pruned
body: the engine CREATES consumed bodies as it runs (RST_STREAM, and every dispatched
response, leave `state = .closed`, `req = none` and the assembled body still on the
record). The right-hand side prunes those; the left-hand side, whose prune ran BEFORE the
step, cannot. Demanding the naive equality would demand the ENGINE prune, which is not its
job. Pruning-modulo-pruning is the property the drain actually needs, and it is the strong
one: it says the emitted bytes are equal ON THE NOSE. -/
theorem feed_pruneConsumed (hd : H2.Hpack.HuffmanDecoder) (handler : H2.Conn.Handler)
    (st : H2.Conn.ConnState) (input : H2.Bytes) :
    H2.Conn.pruneOut (H2.Conn.feed hd handler (pruneConsumed st) input)
      = H2.Conn.pruneOut (H2.Conn.feed hd handler st input) := by
  rw [pruneConsumed_eq_pruneBodies]
  exact H2.Conn.feed_pruneBodies hd handler st input

/-- ★ **Not one served octet moves** when the drain prunes. -/
theorem feed_pruneConsumed_bytes (hd : H2.Hpack.HuffmanDecoder) (handler : H2.Conn.Handler)
    (st : H2.Conn.ConnState) (input : H2.Bytes) :
    (H2.Conn.feed hd handler (pruneConsumed st) input).2
      = (H2.Conn.feed hd handler st input).2 := by
  rw [pruneConsumed_eq_pruneBodies]
  exact H2.Conn.feed_pruneBodies_bytes hd handler st input

/-- ★ …and the successor states agree once both are pruned — so the NEXT drain, and every
drain after it, sees the same connection. -/
theorem feed_pruneConsumed_state (hd : H2.Hpack.HuffmanDecoder) (handler : H2.Conn.Handler)
    (st : H2.Conn.ConnState) (input : H2.Bytes) :
    pruneConsumed (H2.Conn.feed hd handler (pruneConsumed st) input).1
      = pruneConsumed (H2.Conn.feed hd handler st input).1 := by
  rw [pruneConsumed_eq_pruneBodies, pruneConsumed_eq_pruneBodies,
    pruneConsumed_eq_pruneBodies]
  exact H2.Conn.feed_pruneBodies_state hd handler st input

/-- ★ The drain-loop form: pruning at EVERY drain (`pruneConsumed_idem`) or never keeps
the connection in the same equivalence class, so an arbitrarily long run of
prune-then-feed steps is byte-equivalent to the unpruned run. -/
theorem feed_pruneConsumed_congr (hd : H2.Hpack.HuffmanDecoder) (handler : H2.Conn.Handler)
    (st₁ st₂ : H2.Conn.ConnState) (h : pruneConsumed st₁ = pruneConsumed st₂)
    (input : H2.Bytes) :
    H2.Conn.pruneOut (H2.Conn.feed hd handler st₁ input)
      = H2.Conn.pruneOut (H2.Conn.feed hd handler st₂ input) := by
  refine H2.Conn.feed_congr hd handler ?_ input
  show H2.Conn.pruneBodies st₁ = H2.Conn.pruneBodies st₂
  rw [← pruneConsumed_eq_pruneBodies, ← pruneConsumed_eq_pruneBodies]
  exact h

#assert_axioms feed_pruneConsumed ⊆ [stdAxioms]
#assert_axioms feed_pruneConsumed_bytes ⊆ [stdAxioms]
#assert_axioms feed_pruneConsumed_state ⊆ [stdAxioms]
#assert_axioms feed_pruneConsumed_congr ⊆ [stdAxioms]
#assert_axioms pruneConsumed_eq_pruneBodies ⊆ [stdAxioms]
#assert_axioms H2.Conn.feed_congr ⊆ [stdAxioms]
#assert_axioms H2.Conn.feed_pruneBodies_naive_false ⊆ [stdAxioms]
#assert_nonvacuous feed_pruneConsumed
#assert_nonvacuous feed_pruneConsumed_bytes
#assert_nonvacuous H2.Conn.feed_congr

/-! #### The SCALING measurement, pinned as a build-time check

`histBody` is a genuine `MapRequest` rendered by the PROVEN codec
(`Control.Tailcfg.MapRequest.toJson` → `Control.TailcfgWire.renderStr`), so the bodies
below are exactly the shape `natReportOfStream` parses off the wire. `histState n` is the
`ConnState` a coordinator holds after a node has made `n` completed requests on one
connection and still holds its map long-poll open — which is what every drain re-parsed.

`#guard` runs these at BUILD time, so the numbers cannot rot. -/

/-- A real (codec-rendered) `MapRequest` body reporting one endpoint on port `port`. -/
def histBody (port : Nat) : List UInt8 :=
  (Control.H2Noise.s2b (Control.TailcfgWire.renderStr
    (Control.Tailcfg.MapRequest.toJson
      { version := 84, nodeKey := "nodekey:68", discoKey := some "discokey:7e",
        endpoints := some [s!"10.77.2.2:{port}"] })))

/-- A CLOSED, already-dispatched stream carrying that body — what `H2.Conn.respond`
leaves behind. -/
def histClosed (sid port : Nat) : Nat × H2.Conn.StreamRec :=
  (sid, { state := .closed, req := none, body := histBody port })

/-- The connection after `n` completed `MapRequest`s plus one OPEN map long-poll (stream
`1`, `.halfClosedRemote` — the state `respond`'s `keepOpen` branch leaves). Newest-first,
exactly as `H2.Conn.setStream` builds it. -/
def histState (n : Nat) : H2.Conn.ConnState :=
  { streams :=
      (List.range n).reverse.map (fun i => histClosed (2 * i + 3) (41641 + i))
      ++ [(1, { state := .halfClosedRemote, req := none, body := histBody 41641 })] }

/-- The number of bodies a drain actually JSON-parses: `natReportsOf` attempts a parse for
every stream whose body is nonempty (the guarded fast path skips the rest). -/
def parseAttempts (st : H2.Conn.ConnState) : Nat :=
  st.streams.countP (fun p => !p.2.body.isEmpty)

-- ★ BEFORE: 50 completed requests + the open long-poll = 51 bodies re-parsed on EVERY
-- record, and 51 NAT reports re-folded — 50 of them stale replays of history.
#guard parseAttempts (histState 50) = 51
#guard (natReportsOf (histState 50)).length = 51

-- ★ AFTER: 1. Only the live long-poll body is parsed, and only ITS report is folded;
-- the 50 consumed bodies are gone and no longer re-offered.
#guard parseAttempts (pruneConsumed (histState 50)) = 1
#guard (natReportsOf (pruneConsumed (histState 50))).length = 1

-- The same shape at 200 accumulated requests: the unpruned cost tracks history exactly
-- (linear per record, quadratic over the connection); the pruned cost stays at 1.
#guard parseAttempts (histState 200) = 201
#guard parseAttempts (pruneConsumed (histState 200)) = 1

/-- ★ The measurement as a THEOREM rather than a build-time check: after pruning, the
number of bodies a drain parses is the number of streams that are still live — it does
not depend on how many requests the connection has already served. -/
theorem parseAttempts_pruneConsumed (st : H2.Conn.ConnState) :
    parseAttempts (pruneConsumed st)
      = st.streams.countP (fun p => !p.2.body.isEmpty && !streamConsumed p) := by
  simp only [parseAttempts, pruneConsumed, List.countP_map]
  apply List.countP_congr
  intro p _
  by_cases h : streamConsumed p <;> simp [Function.comp, h]

/-- **Operator diagnostic** (`DRORB_DEBUG_MAPREQ=1`): dump each completed request body the
verified h2 engine assembled, verbatim. This is the only way to answer "what did the
client actually SEND" without a decrypting proxy — the ts2021 record layer means tcpdump
shows ciphertext. It reads the SAME `ConnState` the serve path reads and changes nothing.
-/
def dumpBodies (where_ : String) (st : H2.Conn.ConnState) : IO Unit := do
  match ← IO.getEnv "DRORB_DEBUG_MAPREQ" with
  | none => pure ()
  | some _ =>
    for (sid, rec) in st.streams do
      match String.fromUTF8? ⟨rec.body.toArray⟩ with
      | some body => if body.length > 0 then
          IO.println s!"h2coord-multi: [{where_}] stream {sid} body ({body.length}B): {body}"
      | none => pure ()

/-- Upsert a node's reported disco + endpoints into the shared per-tailnet NAT table
(`Control.Join.natUpsert`, last-write-wins), under its mutex. Serialized alongside the
durable-log allocation so a node's disco/endpoints persist across its polls and become
visible to a peer's concurrent map-poll. -/
def storeNat (gmtx : Std.Mutex Nat) (cmtx : Std.Mutex (List Control.NodeKey))
    (dmtx : Std.Mutex Control.Join.NatTable)
    (nk : Control.NodeKey) (rep : Control.Join.NatReport) : IO Unit := do
  -- ★ REPORT THE DELTA, do not re-announce the state. A stock client re-sends its disco
  -- key on every `MapRequest`, and its OPEN map long-poll keeps a `MapRequest` body live
  -- on the connection (`pruneConsumed` cannot clear a stream the client has not finished
  -- with), so a coordinator that folded every report unconditionally bumped the tailnet
  -- generation — and pushed a netmap delta to every peer — on records that changed
  -- NOTHING. `Control.Join.natUpsert_lookup_noop` is the licence: when the report merges
  -- to the stored value the upsert only reorders the table, `natLookup` agrees at EVERY
  -- key, and there is nothing for a push to carry. The table write, the changelog append
  -- and the generation bump are therefore all conditional on a REAL change.
  let changed ← dmtx.atomically do
    let t ← get
    let merged := match Control.Join.natLookup t nk with
      | some old => Control.Join.natMerge old rep
      | none     => rep
    if Control.Join.natLookup t nk = some merged then
      pure false
    else do
      set (Control.Join.natUpsert t nk rep)
      pure true
  -- Operator-visible: WHAT magicsock state this node reported. An endpoint count of 0 on
  -- every poll is exactly the shape of a tailnet that can never leave the relay — peers
  -- are served no candidates to probe. (`natMerge` keeps the last NONEMPTY set, so a
  -- disco-only streaming request cannot clobber a good endpoint report.)
  IO.println s!"h2coord-multi: NAT report from node key[0]={nk.pub.headD 0}: disco {rep.disco.pub.length}B, {rep.endpoints.length} endpoint(s) {rep.endpoints.map Control.Join.endpointToWire}{if changed then "" else " (unchanged — no netmap push)"}"
  -- A node reported fresh disco/endpoints — record THIS node as the changed peer in
  -- the per-tailnet changelog (targeted push), then bump the tailnet generation. The
  -- NAT write is already committed; APPEND to the changelog BEFORE the gen bump so a
  -- push loop that observes the advanced gen also observes the changelog entry.
  -- Skipped entirely when the report was a no-op (`natUpsert_lookup_noop`): a generation
  -- bump with an unchanged table is a push storm with no content.
  if changed then
    cmtx.atomically (do let c ← get; set (c ++ [nk]))
    gmtx.atomically (do let g ← get; set (g + 1))

/-- IPAM-allocate + persist a node's address under the durable-log mutex, IDEMPOTENTLY: a
node already registered WITH an address is left untouched (its IP is STABLE — the whole
point); a new node (or one still address-less) gets the next free CGNAT address
(`Control.Ipam.cgnatPool.alloc (usedOf …)`, distinct by `liveAlloc_distinct`), and the
coordinator appends `nodeRegistered` + `addrAllocated` and rewrites the durable log. The
allocation is fully serialized, so two concurrent registrations never collide. -/
def allocFor (gmtx : Std.Mutex Nat) (cmtx : Std.Mutex (List Control.NodeKey))
    (mtx : Std.Mutex (List Control.Store.Event)) (logPath : String)
    (paStore : Control.PreAuth.Store)
    (nk : Control.NodeKey) (req : Control.RegisterRequest) : IO Unit := do
  let allocated ← mtx.atomically do
    let events ← get
    let restored := Control.Store.replay events
    let known := Control.lookupReg restored.control.nodes nk
    let hasAddr : Bool := match known with
                   | some r => !r.node.addresses.isEmpty
                   | none   => false
    if hasAddr then pure false
    else
      -- ★ADMISSION GATE (interactive path). A node is authorized+allocated iff it
      -- presented a VALID pre-auth key (`registerWithPreAuth`, the proven gate) OR the
      -- operator already approved it (`.authorized` in the durable state — the door
      -- `drorb-ctl nodes approve` opens). Otherwise it is held PENDING (`.registered`,
      -- NO address): the coord issued it an AuthURL and it re-polls until approved. This
      -- is what makes `control_peers_all_authorized` bind the live coord — a PENDING node
      -- never gets an address and never enters a peer's netmap.
      -- ★THE ADMISSION ATTRIBUTES. `registerWithPreAuth` stamps the admitting key's
      -- `user` + `tags` on the node it returns (`preauth_admit`) — but that state is
      -- thrown away here; what survives is the LOG, and `Event.nodeRegistered` replays
      -- through `Control.nodeOf` (`user := 0`, `tags := []`). So the resolved attributes
      -- are persisted explicitly as `nodeUserSet` + `nodeTagsSet`, exactly the durable
      -- triple `Control.Admin.admissionTriple_carries_attrs` is proved about. Without
      -- them the served (replayed) state saw every node as user 0 with no tags and the
      -- tag-ownership gate had nothing to gate on.
      let verdict := Control.PreAuth.validate sha256Bytes paStore 0 req.authKey
      let admitAttrs? : Option Control.PreAuth.KeyAttrs :=
        match verdict with | .admit a => some a | .reject _ => none
      let attrEvents : List Control.Store.Event :=
        match admitAttrs? with
        | some a => [ Control.Store.Event.nodeUserSet nk a.user
                    , Control.Store.Event.nodeTagsSet nk a.tags ]
        | none => []
      let admitted : Bool :=
        (Control.PreAuth.registerWithPreAuth sha256Bytes paStore restored.control 0 req).response.machineAuthorized
        || (match known with | some r => r.status.isAuthorized | none => false)
      if admitted then
        match Control.Ipam.cgnatPool.alloc (Control.Ipam.usedOf restored.control.nodes) with
        | some ip =>
            let newEvs :=
              [ Control.Store.Event.nodeRegistered req true, Control.Store.Event.addrAllocated nk ip ]
              ++ attrEvents
            let events' := events ++ newEvs
            set events'
            storeAppend logPath events newEvs
            let idn := ip - Control.Ipam.cgnatPool.net
            let attrNote := match admitAttrs? with
              | some a => s!" user={a.user} tags={a.tags.length}"
              | none => " (operator-approved; no key attrs)"
            IO.println s!"h2coord-multi: ALLOCATED 100.64.0.{idn} to node key[0]={nk.pub.headD 0}{attrNote} (persisted {events'.length} events)"
            pure true
        | none => IO.eprintln "h2coord-multi: CGNAT pool exhausted"; pure false
      else
        match known with
        | some _ => pure false  -- already PENDING (recorded once); no dup event, no netmap
        | none =>
            let newEvs := [ Control.Store.Event.nodeRegistered req false ]
            let events' := events ++ newEvs
            set events'
            storeAppend logPath events newEvs
            IO.println s!"h2coord-multi: PENDING node key[0]={nk.pub.headD 0} (no pre-auth key) — issued AuthURL, awaiting `drorb-ctl nodes approve {(toHexL nk.pub).take 12}…` (persisted {events'.length} events)"
            pure false
  -- A NEW node registered — record IT as the changed peer in the per-tailnet
  -- changelog (so every OPEN map long-poll pushes a delta carrying ONLY this node,
  -- not the whole peer set), then bump the generation. Append BEFORE the bump.
  if allocated then do
    cmtx.atomically (do let c ← get; set (c ++ [nk]))
    gmtx.atomically (do let g ← get; set (g + 1))

/-- The map stream a client opened as a LONG-POLL, read off the VERIFIED h2
engine's `ConnState`: the completed stream whose assembled body parses (proven
codec) as a `MapRequest` with `Stream:true`, paired with its stream id + node key.
This is how the untrusted loop learns WHICH open stream to push netmap deltas on. -/
def streamingMapOf (st : H2.Conn.ConnState) : Option (Nat × Control.NodeKey) :=
  (st.streams.filterMap (fun (p : Nat × H2.Conn.StreamRec) =>
    if p.2.body.isEmpty then none else
    (do
      let s ← String.fromUTF8? ⟨p.2.body.toArray⟩
      let j ← Control.TailcfgWire.parseStr s
      let mr ← Control.Tailcfg.MapRequest.fromJson? j
      if mr.stream then some (p.1, Control.H2Noise.coreKeyOf mr.nodeKey) else none))).head?

/-- **The TARGETED per-peer netmap delta.** Given a node's PROVEN wire netmap
(`wire = Control.Join.servedNetMapWire ctrl nk`) and the list of node keys that
CHANGED, the pushed `MapResponse` carries in `PeersChanged` EXACTLY the changed
peers VISIBLE to `nk` — the changed keys ∩ this node's ACL/tailnet peer set
(`wire.peers`, already ACL-scoped by `servedNetMapWire`). It SELECTS entries out
of the proven `wire.peers` (never fabricating one), so the served-wire refinement
stays load-bearing (`scopedDelta_peers_sublist`): a join pushes ONE peer per open
stream, not the whole set. A changed key not in `wire.peers` (excluded by the ACL,
or the node's own key) drops out — natural per-tailnet scoping. -/
def scopedDelta (wire : Control.Tailcfg.MapResponse) (changed : List Control.NodeKey) :
    Control.Tailcfg.MapResponse :=
  let changedTexts := changed.map (fun kc => Control.Bridge.NodeKey.toText kc.pub)
  let scopedPeers := (wire.peers.getD []).filter (fun p => changedTexts.contains p.key)
  { peersChanged := some scopedPeers, packetFilters := wire.packetFilters }

/-- **The scoped delta is a SUB-PROJECTION of the proven netmap.** Every peer the
targeted push emits was already a peer of `wire` (= `servedNetMapWire ctrl nk`) —
the delta never invents a peer, it only restricts the proven set to the changed
ones. This is what keeps `servedNetMapWire` load-bearing under the scoping. -/
theorem scopedDelta_peers_sublist (wire : Control.Tailcfg.MapResponse)
    (changed : List Control.NodeKey) :
    ∀ p ∈ (scopedDelta wire changed).peersChanged.getD [], p ∈ wire.peers.getD [] := by
  intro p hp
  simp only [scopedDelta, Option.getD] at hp
  exact (List.mem_filter.mp hp).1

#print axioms scopedDelta_peers_sublist

/-! #### Deterministic my-hand evidence: a join pushes ONE peer, not N.

A concrete 4-node authorized `ControlState`: node A (key `0x01…`) sees 3 peers in
its PROVEN `servedNetMapWire`; when node D (key `0x04…`) joins, the `scopedDelta`
to A carries EXACTLY 1 entry in `PeersChanged` — not the whole 3-peer set. This
inspects the real `MapResponse` the push loop emits, at compile time. -/
private def tReg (b : UInt8) : Control.Registration :=
  { nodeKey := ⟨List.replicate 32 b⟩
  , node := Control.nodeOf
      { version := 0, nodeKey := ⟨List.replicate 32 b⟩, oldNodeKey := ⟨[]⟩,
        machineKey := ⟨List.replicate 32 b⟩, authKey := [], expiry := 0,
        ephemeral := false, followup := false } true
  , status := .authorized }

private def tState : Control.ControlState :=
  { nodes := [tReg 1, tReg 2, tReg 3, tReg 4], filter := [], dns := Control.DnsConfig.empty }

-- A's FULL proven netmap has N = 3 peers …
#guard ((Control.Join.servedNetMapWire tState ⟨List.replicate 32 (1 : UInt8)⟩).peers.getD []).length == 3
-- … but the TARGETED delta when D (key 0x04…) joins carries exactly 1 (not N).
#guard ((scopedDelta (Control.Join.servedNetMapWire tState ⟨List.replicate 32 (1 : UInt8)⟩)
          [(⟨List.replicate 32 (4 : UInt8)⟩ : Control.NodeKey)]).peersChanged.getD []).length == 1
-- … and that 1 entry IS node D (its key), not some other peer.
#guard ((scopedDelta (Control.Join.servedNetMapWire tState ⟨List.replicate 32 (1 : UInt8)⟩)
          [(⟨List.replicate 32 (4 : UInt8)⟩ : Control.NodeKey)]).peersChanged.getD
          []).all (fun p => p.key == Control.Bridge.NodeKey.toText (List.replicate 32 (4 : UInt8)))

/-- How long the push loop waits for a client record before going round again. It
REPLACES the loop's old fixed `IO.sleep 500`, so the push cadence is unchanged — the
socket is simply drained instead of ignored for the same 500 ms. -/
def pushDrainTimeout : UInt32 := 500

/-- The SERVER-PUSH long-poll: after the first full netmap is served on a
`MapRequest{Stream:true}` stream (kept OPEN by `H2.Conn.Rsp.keepOpen`), this owns
the connection and watches the shared tailnet GENERATION (`gmtx`, bumped by
`allocFor` on a new node + `storeNat` on fresh disco/endpoints). When it advances,
it rebuilds this node's netmap and PUSHES a `MapResponse{PeersChanged}` delta —
the peers are the PROVEN `Control.Join.servedNetMapWire` peers — sealed via the
proven record layer (`sendH2Out` → `Ts2021Record.sealRecordTs2021`) as an h2 DATA
frame (`H2.Conn.dataFrame`, `END_STREAM` clear) on the open stream. So an
already-connected client learns a new peer WITHOUT re-polling (the ping blocker).
A periodic `MapResponse{KeepAlive:true}` keeps the stream live AND is the liveness
probe that ends it: `sendH2Out` returning `none` on a gone socket is what reaps the
loop. There is no health-based cap — a quiet client is a healthy client
(`pushMaxTicks`, default off). Deltas via `PeersChanged` match stock tailscale
(`control/controlclient/direct.go`: the 2nd+ streamed message is a delta). -/
partial def pushLoop (gmtx : Std.Mutex Nat) (cmtx : Std.Mutex (List Control.NodeKey))
    (pmtx : Std.Mutex Control.Acl.Policy)
    (mtx : Std.Mutex (List Control.Store.Event))
    (dmtx : Std.Mutex Control.Join.NatTable) (derpAdv : Control.Derp.DerpMap)
    (paStore : Control.PreAuth.Store) (logPath : String)
    (fd : UInt32) (sKey : ByteArray) (sndCtr : Nat) (mapSid : Nat)
    (nk : Control.NodeKey) (lastGen : Nat) (lastSeq : Nat)
    (lastPeerKeys : List String) (selfDelivered : Bool) (ticks : Nat)
    (rKey : ByteArray) (recCtr : Nat) (st : H2.Conn.ConnState) : IO Unit := do
  if pushMaxTicks != 0 && ticks ≥ pushMaxTicks then
    IO.println s!"h2coord-multi: push stream {mapSid} hit the configured tick cap ({pushMaxTicks}); closing"
    return
  -- ★THE READ HALF — the endpoint reports this loop used to drop on the floor.
  --
  -- A stock client MULTIPLEXES its later requests onto the SAME h2 connection that
  -- carries its open map long-poll — in particular the short
  -- `MapRequest{OmitPeers:true, Endpoints:[…]}` it sends whenever magicsock's candidate
  -- set changes (`Control.RealMapKat.mapRequestPoll_endpoints` pins exactly that shape on
  -- real capture bytes). Once `h2LoopCapture` handed the connection over, this loop was
  -- WRITE-ONLY, so those records were never read: they sat unread in the kernel receive
  -- queue (observed live against tailscale 1.98.8: `Recv-Q 2099`, `lastrcv` 110 s), the
  -- NAT table never learned a single endpoint, every served peer went out with
  -- `Endpoints: null`, and NO client could attempt a direct path — the whole tailnet was
  -- pinned to the relay by a missing `recv`.
  --
  -- Draining here runs the client's record through the SAME verified pipeline
  -- `h2LoopCapture` uses (`Ts2021Record.openRecordTs2021` → `H2Noise.feedChunk` →
  -- `natReportsOf` → `storeNat`), which is what makes `Control.Join.withNat_endpoints_served`
  -- load-bearing on a live connection instead of only on the first record. A `storeNat`
  -- bumps the generation, so the peer's own open stream is pushed the new endpoints by the
  -- very next tick of ITS push loop.
  let (sndCtr, recCtr, st) ← (do
    match ← tcpRecvExact fd 3 pushDrainTimeout with
    | none => pure (sndCtr, recCtr, st)   -- no client record this tick
    | some hdr =>
      if hdr.get! 0 != 4 then pure (sndCtr, recCtr, st) else
      let len := (hdr.get! 1).toNat * 256 + (hdr.get! 2).toNat
      match ← tcpRecvExact fd (UInt32.ofNat len) h2RecvTimeout with
      | none => pure (sndCtr, recCtr, st)
      | some sealed =>
        match Control.Ts2021Record.openRecordTs2021 ⟨rKey, recCtr⟩ (bytesOf hdr ++ bytesOf sealed) with
        | none => do
            IO.eprintln s!"h2coord-multi: push-drain record @ctr {recCtr} failed to OPEN"
            pure (sndCtr, recCtr, st)
        | some (plain, _) =>
          let events ← mtx.atomically get
          let tbl ← dmtx.atomically get
          let pol ← pmtx.atomically get
          let baseURL ← controlBaseURL
          let cfg : Control.H2Noise.Cfg :=
            { store := paStore, control := Control.Join.applyNatState tbl (servedFrom pol events),
              now := 0, derp := derpAdv, baseURL := baseURL }
          let (st', out, _close) := Control.H2Noise.feedChunk cfg st plain
          dumpBodies "push-drain" st'
          for (nk2, rep) in natReportsOf st' do
            if nk2.pub ≠ List.replicate 32 0 then storeNat gmtx cmtx dmtx nk2 rep
          for (nk2, req) in reqKeysOf st' do
            if nk2.pub ≠ List.replicate 32 0 then allocFor gmtx cmtx mtx logPath paStore nk2 req
          -- ★ The batch is FOLDED (both loops above ran on `st'`); consume those bodies
          -- so the next tick of this loop re-parses only what is still live. Without this
          -- the push loop re-parsed and re-stored the node's whole `MapRequest` history on
          -- every record, for as long as the long-poll stayed open (`pruneConsumed`).
          let st' := pruneConsumed st'
          match ← sendH2Out fd sKey sndCtr out with
          | none => pure (sndCtr, recCtr + 1, st')
          | some c => pure (c, recCtr + 1, st'))
  let gen ← gmtx.atomically get
  let log ← cmtx.atomically get
  let seq := log.length
  -- The peers that CHANGED since THIS stream last delivered: the changelog suffix
  -- (`allocFor` appends a joining node; `storeNat` appends an endpoint-updating node).
  let newKeys := log.drop lastSeq
  -- Helper: seal a `MapResponse` as a zstd'd h2 DATA frame on the open stream, then
  -- recurse with the given cursor/peer-set/self state. `none` on a dead socket ends it.
  let sendDelta := fun (m : Control.Tailcfg.MapResponse) (lp : List String) (sd : Bool)
      (label : String) => do
    let json := Control.TailcfgWire.renderStr
      (Control.TailcfgWire.dropNulls (Control.Tailcfg.MapResponse.toJson m))
    let z := Control.H2Noise.zstdRawFrame (Control.H2Noise.s2b json)
    let frameBody := Control.H2Noise.u32le z.length ++ z
    match ← sendH2Out fd sKey sndCtr (H2.Conn.dataFrame mapSid false frameBody) with
    | some c =>
        IO.println s!"h2coord-multi: PUSHED {label} to node key[0]={nk.pub.headD 0} on OPEN stream {mapSid} (gen {lastGen}->{gen}, seq {lastSeq}->{seq})"
        pushLoop gmtx cmtx pmtx mtx dmtx derpAdv paStore logPath fd sKey c mapSid nk gen seq lp sd 0 rKey recCtr st
    | none => IO.println s!"h2coord-multi: push stream {mapSid} send failed; closing"; return
  -- Only recompute the node's netmap when the tailnet advanced (gen bump / changelog
  -- suffix) or Self has not yet been delivered — the wire is the PROVEN servedNetMapWire.
  if gen != lastGen || !newKeys.isEmpty || !selfDelivered then
    let events ← mtx.atomically get
    let tbl ← dmtx.atomically get
    let pol ← pmtx.atomically get
    let ctrl := Control.Join.applyNatState tbl (servedFrom pol events)
    let wire := Control.Join.servedNetMapWire ctrl nk
    let curPeerKeys := (wire.peers.getD []).map (·.key)
    -- Self carries an address once THIS node is authorized+allocated (pending -> approved).
    let selfHasAddr : Bool := match wire.node with
                              | some n => !n.addresses.isEmpty
                              | none   => false
    -- ★SELF-EXPIRY: THIS polling node's OWN key was expired (`drorb-ctl nodes expire` ->
    -- `Store.Event.nodeExpired` -> `Register.expire` demotes it to `.expired`, adopted live
    -- by `approvalWatcher`). `Control.Register`/`Control.Expiry` prove `.expired.isAuthorized
    -- = false`; the map-path re-auth signal is `Control.Expiry.reauthResponse`
    -- (`expired_self_reauth`: node MachineAuthorized=false, online=false, peers=none).
    let selfReg := Control.lookupReg ctrl.nodes nk
    let selfExpired : Bool := match selfReg with
                              | some r => decide (r.status = Control.NodeStatus.expired)
                              | none   => false
    -- Peers this node used to see that are GONE now (expiry / leave) vs newly VISIBLE.
    let removed := lastPeerKeys.filter (fun k => !curPeerKeys.contains k)
    let added   := curPeerKeys.filter (fun k => !lastPeerKeys.contains k)
    if selfExpired then
      -- ★ITEM 4 (SELF removal) — the polling node's OWN key expired. Push it the PROVEN
      -- `Control.Expiry.reauthResponse` (MachineAuthorized=false, peers dropped) ONCE, then
      -- CLOSE the stream: a stock client reading MachineAuthorized=false on its own node
      -- re-authenticates (NeedsLogin) and re-registers. This replaces the old "ACL delta,
      -- no peer change" that left the expired node stale on its open stream.
      let m : Control.Tailcfg.MapResponse :=
        match selfReg with
        | some r => Control.Expiry.reauthResponse r
        | none   => { node := none, peers := none }
      let json := Control.TailcfgWire.renderStr
        (Control.TailcfgWire.dropNulls (Control.Tailcfg.MapResponse.toJson m))
      let z := Control.H2Noise.zstdRawFrame (Control.H2Noise.s2b json)
      let frameBody := Control.H2Noise.u32le z.length ++ z
      let _ ← sendH2Out fd sKey sndCtr (H2.Conn.dataFrame mapSid false frameBody)
      IO.println s!"h2coord-multi: PUSHED SELF-EXPIRY reauth (MachineAuthorized=false, peers dropped) to node key[0]={nk.pub.headD 0} on stream {mapSid}; closing => client re-auths (NeedsLogin)"
      return
    else if selfHasAddr && !selfDelivered then
      -- ★ITEM 3 — SELF-ADDRESS ON APPROVAL. The (interactively-approved) node's own
      -- open stream gets the FULL PROVEN netmap (`servedNetMapWire`): Self carrying its
      -- newly-allocated IP + current peers + ACL. It reaches Running WITH an IP, no re-poll.
      sendDelta wire curPeerKeys true "SELF netmap (approved: Self+peers, full servedNetMapWire)"
    else if !removed.isEmpty then
      -- ★ITEM 4 (removal) — a peer EXPIRED / LEFT (`approvalWatcher` adopted the grown log,
      -- `servedNetMapWire` no longer lists it). Re-serve the fresh PROVEN netmap so the
      -- node's LIVE peer set DROPS it. (`PeersRemoved` is by NodeID, but served wire ids are
      -- 0, so a full re-serve — still a projection of `servedNetMapWire` — is the live drop.)
      sendDelta wire curPeerKeys selfDelivered s!"netmap re-serve ({removed.length} peer(s) REMOVED live)"
    else
      -- ★ITEM 4 (add) — TARGETED join delta. `scopedDelta` selects, out of the PROVEN
      -- `servedNetMapWire` peers, EXACTLY the changelog-changed ones visible to `nk`
      -- (`scopedDelta_peers_sublist`) — one entry per join, not the whole peer set.
      let delta := scopedDelta wire newKeys
      let scopedPeers := delta.peersChanged.getD []
      if !scopedPeers.isEmpty then
        sendDelta delta curPeerKeys selfDelivered s!"PeersChanged delta ({scopedPeers.length} peer(s), TARGETED)"
      else if !added.isEmpty then
        -- A peer became visible WITHOUT a changelog append (operator approve bumps only the
        -- generation) — re-serve the fresh PROVEN netmap so this node gains the new peer.
        sendDelta wire curPeerKeys selfDelivered s!"netmap re-serve ({added.length} peer(s) ADDED live)"
      else if gen != lastGen then
        -- gen advanced, no peer change (operator ACL reload): PacketFilters-only delta.
        sendDelta { packetFilters := wire.packetFilters } curPeerKeys selfDelivered "ACL delta (operator PacketFilters, no peer change)"
      else
        -- changelog advanced but nothing visible changed for this node — advance cursor.
        pushLoop gmtx cmtx pmtx mtx dmtx derpAdv paStore logPath fd sKey sndCtr mapSid nk gen seq curPeerKeys selfDelivered (ticks + 1) rKey recCtr st
  else
    if ticks % 100 == 99 then
      let ka : Control.Tailcfg.MapResponse := { keepAlive := true }
      let json := Control.TailcfgWire.renderStr
        (Control.TailcfgWire.dropNulls (Control.Tailcfg.MapResponse.toJson ka))
      let z := Control.H2Noise.zstdRawFrame (Control.H2Noise.s2b json)
      let frameBody := Control.H2Noise.u32le z.length ++ z
      match ← sendH2Out fd sKey sndCtr (H2.Conn.dataFrame mapSid false frameBody) with
      | some c => pushLoop gmtx cmtx pmtx mtx dmtx derpAdv paStore logPath fd sKey c mapSid nk lastGen lastSeq lastPeerKeys selfDelivered (ticks + 1) rKey recCtr st
      | none => return
    else
      pushLoop gmtx cmtx pmtx mtx dmtx derpAdv paStore logPath fd sKey sndCtr mapSid nk lastGen lastSeq lastPeerKeys selfDelivered (ticks + 1) rKey recCtr st

/-- The h2-over-noise loop that CAPTURES the final `ConnState`. Like `h2Loop` but it
re-snapshots the durable state (`servedFrom`) on EVERY record — so even a re-poll on a
reused connection serves the freshest netmap — and returns the accumulated `ConnState` so
the caller can read the request node key(s) off it. -/
partial def h2LoopCapture (gmtx : Std.Mutex Nat) (cmtx : Std.Mutex (List Control.NodeKey))
    (pmtx : Std.Mutex Control.Acl.Policy)
    (mtx : Std.Mutex (List Control.Store.Event))
    (dmtx : Std.Mutex Control.Join.NatTable) (derpAdv : Control.Derp.DerpMap)
    (paStore : Control.PreAuth.Store) (logPath : String) (fd : UInt32) (rKey sKey : ByteArray)
    (recCtr sndCtr : Nat) (st : H2.Conn.ConnState) : IO H2.Conn.ConnState := do
  match ← tcpRecvExact fd 3 h2RecvTimeout with
  | none => return st
  | some hdr =>
    if hdr.get! 0 != 4 then return st
    let len := (hdr.get! 1).toNat * 256 + (hdr.get! 2).toNat
    match ← tcpRecvExact fd (UInt32.ofNat len) h2RecvTimeout with
    | none => return st
    | some sealed =>
      match Control.Ts2021Record.openRecordTs2021 ⟨rKey, recCtr⟩ (bytesOf hdr ++ bytesOf sealed) with
      | none => do IO.eprintln s!"h2coord-multi: record @ctr {recCtr} failed to OPEN"; return st
      | some (plain, _) =>
        let events ← mtx.atomically get
        let tbl ← dmtx.atomically get
        let pol ← pmtx.atomically get
        -- Serve each node its peers WITH the disco key + endpoints those peers last
        -- reported (`applyNatState`), so magicsock can seal DISCO probes + attempt a
        -- direct path (`Control.Join.withNat_disco_served`); DERP home stays drorb's
        -- region as the fallback (`nodeToWire_homeDERP`). The ACL served is the OPERATOR
        -- policy compiled (`servedFrom pol`), not `demoPolicy`.
        -- ★The served MapResponse carries the ADVERTISED (routable) DERPMap, so a
        -- cross-host client dials the reachable relay instead of its own 127.0.0.1.
        -- `servedMapForAt_filters` / `_node` / `_peers`: the ACL + addressing served here
        -- are unchanged by that addr — only the DERP endpoint moves.
        -- The control URL clients dialed, for the interactive-enrolment AuthURL a
        -- keyless RegisterRequest gets back (`DRORB_CONTROL_URL`, loopback default).
        let baseURL ← controlBaseURL
        let cfg : Control.H2Noise.Cfg :=
          { store := paStore, control := Control.Join.applyNatState tbl (servedFrom pol events),
            now := 0, derp := derpAdv, baseURL := baseURL }
        let (st', out, close) := Control.H2Noise.feedChunk cfg st plain
        dumpBodies "h2loop" st'
        -- STORE this connection's reported disco + endpoints so a peer's poll serves them.
        for (nk, rep) in natReportsOf st' do
          if nk.pub ≠ List.replicate 32 0 then storeNat gmtx cmtx dmtx nk rep
        -- Register + persist any node whose request stream completed on THIS
        -- record, BEFORE the connection closes. A stock client holds its h2
        -- connection(s) open for the map long-poll, so allocation-at-close never
        -- fires; doing it per-record makes a node registered on one connection
        -- visible (via the shared durable ControlState under `mtx`) to its own
        -- map-poll on a concurrent connection, so `Control.Join.servedNetMapWire`
        -- returns a self `Node` instead of the empty (`{}`) response. Idempotent
        -- (`allocFor` skips a node that already holds an address).
        for (nk, req) in reqKeysOf st' do
          if nk.pub ≠ List.replicate 32 0 then allocFor gmtx cmtx mtx logPath paStore nk req
        -- ★ The batch is FOLDED; consume those bodies (`pruneConsumed`). `stP` is what
        -- every continuation below carries forward, so no later drain re-parses or
        -- re-stores this record's requests. `streamingMapOf` is deliberately read off the
        -- UNPRUNED `st'` just below: the long-poll stream it looks for is
        -- `.halfClosedRemote` (never pruned), so reading the pre-prune state keeps that
        -- seam byte-identical to before this change.
        let stP := pruneConsumed st'
        match ← sendH2Out fd sKey sndCtr out with
        | none => do IO.eprintln "h2coord-multi: seal refused"; return stP
        | some sndCtr' =>
          if close then return stP
          else
            -- A `MapRequest{Stream:true}` just got its first netmap on an OPEN
            -- stream: hand the connection to the SERVER-PUSH loop so this client
            -- learns later peer joins WITHOUT re-polling (the ping blocker).
            match streamingMapOf st' with
            | some (mapSid, nk) =>
                let g0 ← gmtx.atomically get
                let s0 ← cmtx.atomically get
                -- Seed the push loop's peer-set + self state from the netmap THIS stream
                -- was just served (the PROVEN `servedNetMapWire` over the fresh state), so
                -- it only pushes FUTURE changes: joins (targeted `scopedDelta`), removals
                -- (re-serve), and — if this node is still PENDING (no Self addr) — its Self
                -- address the moment an operator approves it. Cursor at the current changelog
                -- length (the first netmap already carried the whole peer set).
                let wire0 := Control.Join.servedNetMapWire (Control.Join.applyNatState tbl (servedFrom pol events)) nk
                let peerKeys0 := (wire0.peers.getD []).map (·.key)
                let self0 : Bool := match wire0.node with
                                    | some n => !n.addresses.isEmpty
                                    | none   => false
                IO.println s!"h2coord-multi: node key[0]={nk.pub.headD 0} opened map long-poll on stream {mapSid} (gen {g0}, seq {s0.length}, self-addr {self0}); entering push loop"
                pushLoop gmtx cmtx pmtx mtx dmtx derpAdv paStore logPath fd sKey sndCtr' mapSid nk g0 s0.length peerKeys0 self0 0 rKey (recCtr + 1) stP
                return stP
            | none => h2LoopCapture gmtx cmtx pmtx mtx dmtx derpAdv paStore logPath fd rKey sKey (recCtr + 1) sndCtr' stP

/-- Serve ONE noise connection: byte-exact ts2021 handshake to `.up`, then the h2-over-noise
loop (routing `/machine/register` to the proven gate, `/machine/map` to the served
netmap), then read the node key(s) off the final `ConnState` and IPAM-allocate + persist. -/
def serveConn (gmtx : Std.Mutex Nat) (cmtx : Std.Mutex (List Control.NodeKey))
    (pmtx : Std.Mutex Control.Acl.Policy)
    (mtx : Std.Mutex (List Control.Store.Event))
    (dmtx : Std.Mutex Control.Join.NatTable) (derpAdv : Control.Derp.DerpMap) (logPath : String)
    (paStore : Control.PreAuth.Store) (k : Km) (cfd : UInt32) : IO Unit := do
  try
    let some initFrame ← recvHandshakeFrame cfd | do IO.eprintln "h2coord-multi: no initiation"; tcpClose cfd
    let coordSess : Control.Channel.Ts2021.Session :=
      { role := .coord, version := tsVersion, spriv := k.sPriv, spub := k.sPub,
        epriv := k.sEpriv, epub := k.sEpub, peerS := ByteArray.empty }
    let (coordP, out) := Control.Channel.Ts2021.step coordSess .fresh (.recvInit initFrame)
    let some coordTx := (match coordP with | .up tx => some tx | _ => none)
      | do IO.eprintln "h2coord-multi: handshake failed"; tcpClose cfd
    match out with
    | .sendResp respFrame => tcpSend cfd (baOf respFrame)
    | _ => do IO.eprintln "h2coord-multi: no response frame"; tcpClose cfd; return
    let finalSt ← h2LoopCapture gmtx cmtx pmtx mtx dmtx derpAdv paStore logPath cfd coordTx.recv coordTx.send 0 0 H2.Conn.initState
    tcpClose cfd
    for (nk, rep) in natReportsOf finalSt do
      if nk.pub ≠ List.replicate 32 0 then storeNat gmtx cmtx dmtx nk rep
    for (nk, req) in reqKeysOf finalSt do
      if nk.pub ≠ List.replicate 32 0 then allocFor gmtx cmtx mtx logPath paStore nk req
  catch e => IO.eprintln s!"h2coord-multi: connection error: {e}"

/-- Accept connections forever, handling each concurrently (`IO.asTask`) so a map long-poll
never blocks another node's register.

An accept that ends in a TIMEOUT is not an event: it is the absence of one. The bounded
`tcpAccept` (`acceptTickMs`) is kept — it is what returns control to Lean on a cadence
instead of parking the thread in a C `poll` forever — but an expired tick now LOGS and
LOOPS. `idle` counts consecutive empty ticks purely so the log says how long the tailnet
has been quiet, and so an operator who deliberately wants a bounded lifetime can have one
(`acceptIdleExitTicks`, default never). -/
partial def acceptLoop (gmtx : Std.Mutex Nat) (cmtx : Std.Mutex (List Control.NodeKey))
    (pmtx : Std.Mutex Control.Acl.Policy)
    (mtx : Std.Mutex (List Control.Store.Event))
    (dmtx : Std.Mutex Control.Join.NatTable) (derpAdv : Control.Derp.DerpMap) (logPath : String)
    (paStore : Control.PreAuth.Store) (k : Km) (lfd : UInt32) (idle : Nat := 0) : IO Unit := do
  match ← tcpAccept lfd acceptTickMs with
  | none =>
      let idle := idle + 1
      if acceptIdleExitTicks != 0 && idle ≥ acceptIdleExitTicks then
        IO.println s!"h2coord-multi: accept idle {idle} tick(s) of {acceptTickMs}ms and DRORB_ACCEPT_IDLE_EXIT={acceptIdleExitTicks}; exiting as configured"
      else
        IO.println s!"h2coord-multi: accept idle tick {idle} ({acceptTickMs}ms, no NEW inbound connection) — STILL LISTENING; open map long-polls are unaffected"
        acceptLoop gmtx cmtx pmtx mtx dmtx derpAdv logPath paStore k lfd idle
  | some cfd =>
      let _ ← IO.asTask (serveConn gmtx cmtx pmtx mtx dmtx derpAdv logPath paStore k cfd)
      acceptLoop gmtx cmtx pmtx mtx dmtx derpAdv logPath paStore k lfd 0

/-- The modification stamp of `path` (`sec·10⁹ + nsec`), or `0` if it cannot be stat'd
(missing/unreadable). Used by `reloadWatcher` to detect an operator editing the policy. -/
def policyMtime (path : String) : IO Int := do
  try
    let md ← (System.FilePath.mk path).metadata
    pure (md.modified.sec * 1000000000 + (md.modified.nsec.toNat : Int))
  catch _ => pure 0

/-- ★**POLICY RELOAD** (the control-plane admin trigger = a file re-read on change).
Every second, re-`stat` the operator policy file; when its mtime advances (an operator
edited `DRORB_POLICY`), re-`loadPolicy` (proven `parseHuPolicy`, fail-closed to
`safeDefaultPolicy`), SWAP it into `pmtx`, and BUMP the tailnet generation (`gmtx`) so
every OPEN map long-poll's `pushLoop` re-serves the NEW `Acl.compile pol` in a pushed
`MapResponse{PacketFilters,PeersChanged}` delta — the live ACL update reaches connected
clients WITHOUT a re-poll. (A SIGHUP handler would trigger the same swap; the file-mtime
watch is the portable, no-FFI admin trigger and is what the reload gate demonstrates.) -/
partial def reloadWatcher (pmtx : Std.Mutex Control.Acl.Policy) (gmtx : Std.Mutex Nat)
    (path : String) (lastStamp : Int) : IO Unit := do
  IO.sleep 1000
  let stamp ← policyMtime path
  if stamp != lastStamp && stamp != 0 then
    IO.println s!"policy: '{path}' changed (mtime {stamp}) — RELOADING + pushing to open streams"
    let pol ← loadPolicy (some path)
    pmtx.atomically (set pol)
    gmtx.atomically (do let g ← get; set (g + 1))
    reloadWatcher pmtx gmtx path stamp
  else
    reloadWatcher pmtx gmtx path lastStamp

/-- ★**APPROVAL WATCHER** (the interactive-enrolment admin trigger). Every second,
re-read the durable log off disk; when it has GROWN beyond the in-memory event count, an
OUT-OF-BAND writer (`drorb-ctl nodes approve`, which appends `nodeRegistered … true` +
`addrAllocated`) has approved a pending node. Adopt the disk log into `mtx` and BUMP the
generation (`gmtx`) so every OPEN map long-poll's `pushLoop` re-serves the now-authorized
peer, AND the approved node's next register followup sees `.authorized` (→
`H2Noise.registerRespFor` returns `MachineAuthorized=true`). The coord's OWN writes keep
`disk == mem` (it sets `mtx` then writes the file), so `disk.length > mem.length` fires
ONLY on an external approve — no self-trigger, no spurious bump. Mirrors `reloadWatcher`
(portable, no-FFI, off the hot path). -/
partial def approvalWatcher (mtx : Std.Mutex (List Control.Store.Event))
    (gmtx : Std.Mutex Nat) (logPath : String) : IO Unit := do
  IO.sleep 1000
  let disk ← loadLog logPath
  let mem ← mtx.atomically get
  if disk.length > mem.length then
    IO.println s!"approval: durable log grew {mem.length} -> {disk.length} (out-of-band `drorb-ctl` approve) — adopting + pushing to open streams"
    mtx.atomically (set disk)
    gmtx.atomically (do let g ← get; set (g + 1))
  approvalWatcher mtx gmtx logPath

/-- COORD process for a MULTI-NODE tailnet: persistent durable ControlState + IPAM, over
HTTP/2-over-noise, concurrent connections. Distinct nodes get distinct stable addresses and
appear in each other's netmap. The served ACL is the OPERATOR policy (`policyPath?`, else
`DRORB_POLICY` HuJSON file → proven `parseHuPolicy` → `Acl.compile`), reloaded live on
file change. -/
def h2coordMulti (port : UInt16) (logPath : String)
    (policyPath? : Option String := none) : IO UInt32 := do
  IO.println s!"== control-live H2COORD-MULTI : persistent multi-node tailnet, 127.0.0.1:{port} =="
  let events0 ← loadLog logPath
  let restored0 := Control.Store.replay events0
  IO.println s!"h2coord-multi: replayed {events0.length} durable events; {restored0.control.nodes.length} node(s) known"
  -- ★DURABILITY: normalise the store to the FRAMED append-only format (atomic
  -- temp+rename), once, here. After this every event append is a pure `O_APPEND` of
  -- that event's frame, so a crash mid-append costs at most that one event
  -- (`Control.Store.recover_torn_write`) instead of the whole log.
  if ← storeIsFramed logPath then
    IO.println s!"h2coord-multi: durable store is the framed append-only format (torn-tail tolerant)"
  else
    storeWriteAll logPath events0
    IO.println s!"h2coord-multi: MIGRATED {logPath} to the framed append-only format ({events0.length} events, atomic rename)"
  for r in restored0.control.nodes do
    let ipNat := (r.node.addresses.head?).elim 0 (fun p => Control.Ipam.v4ToNat p.addr)
    IO.println s!"  known node key[0]={r.nodeKey.pub.headD 0} addr=100.64.0.{ipNat - Control.Ipam.cgnatPool.net} (recovered)"
  let paStore : Control.PreAuth.Store :=
    (Control.PreAuth.mint sha256Bytes testAuthSecret reusableAttrs)
      :: (Control.PreAuth.mint sha256Bytes (Control.H2Noise.s2b Control.H2Noise.demoSecretStr) reusableAttrs)
      :: restored0.preauth.map paRecordOf
  let some k ← mkKeys | do IO.eprintln "h2coord-multi: key derivation failed"; return 1
  IO.println s!"h2coord-multi: server Noise static pub (set DRORB_CONTROL_NOISE_PUB to this) : {toHex k.sPub}"
  -- ★OPERATOR POLICY: read `DRORB_POLICY` HuJSON, parse (proven) + compile; fail closed
  -- to deny-all. The served `PacketFilters["base"]` is THIS policy's `Acl.compile`, not
  -- `demoPolicy` (`servedFrom_filter_is_operator_compile`).
  let polPath? ← match policyPath? with
    | some p => pure (some p)
    | none   => IO.getEnv "DRORB_POLICY"
  let pol0 ← loadPolicy polPath?
  let pmtx ← Std.Mutex.new pol0
  let mtx ← Std.Mutex.new events0
  -- The cross-connection per-node DISCO + endpoints table (magicsock NAT state). Held in
  -- memory (re-reported by the client every poll; not durable — a node re-announces its
  -- disco/endpoints each session, exactly as tailscale's control keeps them ephemeral).
  let dmtx ← Std.Mutex.new ([] : Control.Join.NatTable)
  -- The tailnet GENERATION counter: bumped on every new-node registration and
  -- fresh disco/endpoint report; every OPEN map long-poll watches it and pushes a
  -- netmap delta when it advances (server-push, `pushLoop`).
  let gmtx ← Std.Mutex.new (0 : Nat)
  -- The per-tailnet CHANGELOG: an append-only list of the node keys that CHANGED
  -- (a new registration via `allocFor`, an endpoint report via `storeNat`). Each open
  -- `pushLoop` keeps a CURSOR into this log and pushes ONLY the suffix since it last
  -- delivered — scoped to the peers visible to its node (`scopedDelta` over the proven
  -- `servedNetMapWire`) — so a JOIN costs one delta per stream, not the whole peer set.
  let cmtx ← Std.Mutex.new ([] : List Control.NodeKey)
  -- ★Launch the policy-reload watcher (file-mtime admin trigger) when a policy file is
  -- configured, so an operator edit re-compiles + live-pushes the new ACL.
  match polPath? with
  | some p =>
      let stamp0 ← policyMtime p
      let _ ← IO.asTask (reloadWatcher pmtx gmtx p stamp0)
      IO.println s!"h2coord-multi: policy-reload watcher up on '{p}' (edit the file to hot-reload the served ACL)."
  | none => IO.println "h2coord-multi: no DRORB_POLICY — serving deny-all; no reload watcher."
  -- ★Launch the APPROVAL watcher: an out-of-band `drorb-ctl nodes approve` grows the
  -- durable log; adopt it live so a pending (interactive) node comes up without a coord
  -- restart. The coord's own writes keep disk==mem, so this fires only on operator approve.
  let _ ← IO.asTask (approvalWatcher mtx gmtx logPath)
  IO.println s!"h2coord-multi: approval watcher up on '{logPath}' (`drorb-ctl nodes approve <nonce>` to admit a pending node)."
  -- ★Read the ADVERTISED DERP addr ONCE, here, and thread it down to every served
  -- MapResponse: the relay binds `DRORB_DERP_LISTEN` but clients dial `DRORB_DERP_ADDR`.
  let derpAdv ← derpAdvMap
  announceDerp "h2coord-multi" derpAdv
  let lfd ← tcpListen port
  IO.println "h2coord-multi: listening; concurrent multi-node accept loop up (disco+endpoints served)."
  acceptLoop gmtx cmtx pmtx mtx dmtx derpAdv logPath paStore k lfd
  return 0

/-! ### Phase-3 GATE (my-hand): two REAL clients over the REAL composition → distinct
addrs + mutual peers

`control-live multidemo <port>` runs the `h2coordMulti` coord (in a task) and drives TWO
independent clients A and B — each doing the byte-exact ts2021 Noise-IK handshake (real
EverCrypt X25519/ChaCha20-Poly1305/BLAKE2s), then a REAL `POST /machine/register` and
`POST /machine/map` as HTTP/2 streams sealed into `controlbase` records — against the coord
over real localhost TCP. A and B carry DISTINCT overlay node keys. The coord IPAM-allocates
`100.64.0.1` to A and `100.64.0.2` to B (persisted durably), and serves each its stable
Self + the OTHER as a Peer. Each map client DECRYPTS its response records and we search the
plaintext for the address strings — so we witness, on the wire, that A received `100.64.0.1`
(self) + `100.64.0.2` (peer B) and B received the mirror. Finally we replay the persisted
log from empty (restart) and show the addresses are unchanged.

This is the gate at the drorb-native-client level: everything cryptographic/structural is
the proven Lean over real bytes. The ONE thing not exercised vs a literal `tailscale status`
is the stock client's HTTP `GET /key` + `POST /ts2021`-Upgrade (+TLS) bootstrap PREFIX,
which `tailnet-02b` §build item 3 assigns to the dataplane — the named residual. -/

/-- A client's h2 `POST /machine/register` request stream (preface+SETTINGS+HEADERS+DATA). -/
def mkRegStream (rr : Control.Tailcfg.RegisterRequest) : List UInt8 :=
  let reqJson := Control.TailcfgWire.renderStr (Control.Tailcfg.RegisterRequest.toJson rr)
  let reqBlock := H2.HpackEncode.encodeHeaders
    [ (Control.H2Noise.s2b ":method", Control.H2Noise.s2b "POST")
    , (Control.H2Noise.s2b ":path", Control.H2Noise.s2b "/machine/register")
    , (Control.H2Noise.s2b ":scheme", Control.H2Noise.s2b "http")
    , (Control.H2Noise.s2b ":authority", Control.H2Noise.s2b "drorb") ]
  H2.Conn.clientPreface ++ H2.Conn.frameHdr 0 0x4 0 0
    ++ H2.Conn.headersFrame 1 reqBlock ++ H2.Conn.dataFrame 1 true (Control.H2Noise.s2b reqJson)

/-- A client's h2 `POST /machine/map` request stream. -/
def mkMapStream (mr : Control.Tailcfg.MapRequest) : List UInt8 :=
  let reqJson := Control.TailcfgWire.renderStr (Control.Tailcfg.MapRequest.toJson mr)
  let reqBlock := H2.HpackEncode.encodeHeaders
    [ (Control.H2Noise.s2b ":method", Control.H2Noise.s2b "POST")
    , (Control.H2Noise.s2b ":path", Control.H2Noise.s2b "/machine/map")
    , (Control.H2Noise.s2b ":scheme", Control.H2Noise.s2b "http")
    , (Control.H2Noise.s2b ":authority", Control.H2Noise.s2b "drorb") ]
  H2.Conn.clientPreface ++ H2.Conn.frameHdr 0 0x4 0 0
    ++ H2.Conn.headersFrame 1 reqBlock ++ H2.Conn.dataFrame 1 true (Control.H2Noise.s2b reqJson)

/-- Is `needle` a contiguous sub-list of `hay`? (byte substring search) -/
def bytesInfix (needle hay : List UInt8) : Bool :=
  (List.range (hay.length + 1)).any (fun i => needle.isPrefixOf (hay.drop i))

/-- One REAL client RPC: connect, byte-exact Noise-IK handshake to `.up`, seal + send the
h2 stream as `controlbase` records, then read + DECRYPT the response records and return the
concatenated plaintext (the h2 response frames — for the map RPC these carry the served
netmap JSON verbatim in zstd raw blocks). -/
def runClientRPC (port : UInt16) (h2stream : List UInt8) : IO (List UInt8) := do
  let some k ← mkKeys | do IO.eprintln "client: key derivation failed"; return []
  let fd ← tcpConnect "127.0.0.1" port
  let nodeSess : Control.Channel.Ts2021.Session :=
    { role := .node, version := tsVersion, spriv := k.mpriv, spub := k.mpub,
      epriv := k.nEpriv, epub := k.nEpub, peerS := k.sPub }
  let (nodeP1, o1) := Control.Channel.Ts2021.step nodeSess .fresh .start
  let some initFrame := (match o1 with | .sendInit f => some f | _ => none)
    | do IO.eprintln "client: no init frame"; tcpClose fd; return []
  tcpSend fd (baOf initFrame)
  let some respFrame ← recvHandshakeFrame fd | do IO.eprintln "client: no resp frame"; tcpClose fd; return []
  let (nodeP, _) := Control.Channel.Ts2021.step nodeSess nodeP1 (.recvResp respFrame)
  let some nodeTx := (match nodeP with | .up tx => some tx | _ => none)
    | do IO.eprintln "client: handshake not up"; tcpClose fd; return []
  let _ ← sendH2Out fd nodeTx.send 0 h2stream
  -- read + decrypt up to 8 response records (bounded)
  let mut plain : List UInt8 := []
  let mut ctr : Nat := 0
  let mut go := true
  for _ in [0:8] do
    if go then
      match ← tcpRecvExact fd 3 5000 with
      | none => go := false
      | some hdr =>
        if hdr.get! 0 != 4 then go := false
        else
          let len := (hdr.get! 1).toNat * 256 + (hdr.get! 2).toNat
          match ← tcpRecvExact fd (UInt32.ofNat len) 5000 with
          | none => go := false
          | some sealed =>
            match Control.Ts2021Record.openRecordTs2021 ⟨nodeTx.recv, ctr⟩ (bytesOf hdr ++ bytesOf sealed) with
            | none => go := false
            | some (p, _) => plain := plain ++ p; ctr := ctr + 1
  tcpClose fd
  return plain

/-- A LONG-POLL client RPC for the server-push gate: like `runClientRPC` but it keeps
the map stream OPEN and PATIENT — after the initial netmap it waits out the idle gap
(server-push arrives asynchronously) within a wall-clock `budgetMs`, tolerating idle
read-timeouts (they do NOT desync the record counter), and early-exits as soon as the
decrypted plaintext contains `untilBytes` (the awaited delta marker). Returns the full
decrypted plaintext (initial netmap ++ any pushed deltas). -/
def runLongPollRPC (port : UInt16) (h2stream : List UInt8) (untilBytes : List UInt8)
    (budgetMs : Nat) : IO (List UInt8) := do
  let some k ← mkKeys | do IO.eprintln "client: key derivation failed"; return []
  let fd ← tcpConnect "127.0.0.1" port
  let nodeSess : Control.Channel.Ts2021.Session :=
    { role := .node, version := tsVersion, spriv := k.mpriv, spub := k.mpub,
      epriv := k.nEpriv, epub := k.nEpub, peerS := k.sPub }
  let (nodeP1, o1) := Control.Channel.Ts2021.step nodeSess .fresh .start
  let some initFrame := (match o1 with | .sendInit f => some f | _ => none)
    | do IO.eprintln "client: no init frame"; tcpClose fd; return []
  tcpSend fd (baOf initFrame)
  let some respFrame ← recvHandshakeFrame fd | do IO.eprintln "client: no resp frame"; tcpClose fd; return []
  let (nodeP, _) := Control.Channel.Ts2021.step nodeSess nodeP1 (.recvResp respFrame)
  let some nodeTx := (match nodeP with | .up tx => some tx | _ => none)
    | do IO.eprintln "client: handshake not up"; tcpClose fd; return []
  let _ ← sendH2Out fd nodeTx.send 0 h2stream
  let t0 ← IO.monoMsNow
  let mut plain : List UInt8 := []
  let mut ctr : Nat := 0
  let mut done := false
  for _ in [0:128] do
    if !done then
      let now ← IO.monoMsNow
      if now - t0 > budgetMs then done := true
      else
        match ← tcpRecvExact fd 3 1500 with
        | none => pure ()  -- idle within budget: keep waiting for the async push (no ctr change)
        | some hdr =>
          if hdr.get! 0 != 4 then done := true
          else
            let len := (hdr.get! 1).toNat * 256 + (hdr.get! 2).toNat
            match ← tcpRecvExact fd (UInt32.ofNat len) 1500 with
            | none => done := true
            | some sealed =>
              match Control.Ts2021Record.openRecordTs2021 ⟨nodeTx.recv, ctr⟩ (bytesOf hdr ++ bytesOf sealed) with
              | none => done := true
              | some (p, _) =>
                plain := plain ++ p; ctr := ctr + 1
                if (List.range (plain.length + 1)).any (fun i => untilBytes.isPrefixOf (plain.drop i)) then
                  done := true
  tcpClose fd
  return plain

/-- The demo's two distinct overlay node keys (valid `nodekey:<64hex>`). -/
def demoNkA : String := "nodekey:" ++ String.mk (List.replicate 64 'a')
def demoNkB : String := "nodekey:" ++ String.mk (List.replicate 64 'b')
/-- Two more distinct overlay node keys, for the 4-node targeted-push gate. -/
def demoNkC : String := "nodekey:" ++ String.mk (List.replicate 64 'c')
def demoNkD : String := "nodekey:" ++ String.mk (List.replicate 64 'e')

/-- The byte tail of `hay` AFTER the first occurrence of `needle` (or `[]` if
absent). Used to isolate the PUSHED delta region of a decrypted long-poll: the
initial full netmap uses the `"Peers"` JSON key, the pushed delta uses
`"PeersChanged"`, so the bytes after `"PeersChanged"` are the targeted delta. -/
def afterInfix (needle hay : List UInt8) : List UInt8 :=
  match (List.range (hay.length + 1)).find? (fun i => needle.isPrefixOf (hay.drop i)) with
  | some i => hay.drop (i + needle.length)
  | none => []

def multidemo (port : UInt16) : IO UInt32 := do
  IO.println "== control-live MULTIDEMO : two REAL clients, distinct addrs + mutual peers =="
  let logPath := "/tmp/drorb-multidemo.log"
  (try IO.FS.removeFile logPath catch _ => pure ())
  let coordTask ← IO.asTask (h2coordMulti port logPath)
  IO.sleep 700
  let rrA : Control.Tailcfg.RegisterRequest := { Control.H2Noise.demoRegReq with nodeKey := demoNkA }
  let rrB : Control.Tailcfg.RegisterRequest := { Control.H2Noise.demoRegReq with nodeKey := demoNkB }
  -- Each client reports its magicsock NAT state: a distinct DiscoKey + a direct endpoint,
  -- exactly as a stock client does in its MapRequest (`RealMapKat` pins these on real bytes).
  let discoA : String := "discokey:" ++ String.mk (List.replicate 64 'c')
  let discoB : String := "discokey:" ++ String.mk (List.replicate 64 'd')
  let epA : String := "192.168.1.10:41641"
  let epB : String := "192.168.1.20:51820"
  let mrA : Control.Tailcfg.MapRequest :=
    { version := 138, nodeKey := demoNkA, discoKey := some discoA, endpoints := some [epA], stream := true }
  let mrB : Control.Tailcfg.MapRequest :=
    { version := 138, nodeKey := demoNkB, discoKey := some discoB, endpoints := some [epB], stream := true }
  -- ── both nodes REGISTER (distinct node keys → distinct IPAM allocations) ──
  IO.println "\n-- A registers --"; let _ ← runClientRPC port (mkRegStream rrA)
  IO.println "-- B registers --";   let _ ← runClientRPC port (mkRegStream rrB)
  IO.sleep 500
  -- ── round 1 map-poll: each client REPORTS its disco+endpoints (stored coord-side) ──
  IO.println "\n-- A map-polls (reports disco+endpoints) --"; let _ ← runClientRPC port (mkMapStream mrA)
  IO.println "-- B map-polls (reports disco+endpoints) --";   let _ ← runClientRPC port (mkMapStream mrB)
  IO.sleep 300
  -- ── round 2 map-poll: the table has CONVERGED, so each now RECEIVES the other's
  --    disco key + endpoints (magicsock can path-build) alongside its address ──
  IO.println "\n-- A map-polls again (receives B's disco+endpoints) --"; let plainA ← runClientRPC port (mkMapStream mrA)
  IO.println "-- B map-polls again (receives A's disco+endpoints) --";   let plainB ← runClientRPC port (mkMapStream mrB)
  -- ── witness the addresses in the DECRYPTED, RECEIVED map responses ──
  let hasA1 := bytesInfix (Control.H2Noise.s2b "100.64.0.1") plainA
  let hasA2 := bytesInfix (Control.H2Noise.s2b "100.64.0.2") plainA
  let hasB1 := bytesInfix (Control.H2Noise.s2b "100.64.0.1") plainB
  let hasB2 := bytesInfix (Control.H2Noise.s2b "100.64.0.2") plainB
  -- ── witness the PEER's disco key + endpoint + DERP-home in each received netmap ──
  let aSeesBdisco := bytesInfix (Control.H2Noise.s2b discoB) plainA
  let aSeesBep    := bytesInfix (Control.H2Noise.s2b epB) plainA
  let bSeesAdisco := bytesInfix (Control.H2Noise.s2b discoA) plainB
  let bSeesAep    := bytesInfix (Control.H2Noise.s2b epA) plainB
  let aSeesDerp   := bytesInfix (Control.H2Noise.s2b "\"HomeDERP\":1") plainA
  let bSeesDerp   := bytesInfix (Control.H2Noise.s2b "\"HomeDERP\":1") plainB
  IO.println s!"\n-- A's received netmap ({plainA.length}B plaintext) --"
  IO.println s!"   self 100.64.0.1 present : {hasA1}    peer 100.64.0.2 present : {hasA2}"
  IO.println s!"   peer B disco key served : {aSeesBdisco}   peer B endpoint served : {aSeesBep}   peer HomeDERP=1 : {aSeesDerp}"
  IO.println s!"-- B's received netmap ({plainB.length}B plaintext) --"
  IO.println s!"   self 100.64.0.2 present : {hasB2}    peer 100.64.0.1 present : {hasB1}"
  IO.println s!"   peer A disco key served : {bSeesAdisco}   peer A endpoint served : {bSeesAep}   peer HomeDERP=1 : {bSeesDerp}"
  let discoServed := aSeesBdisco && aSeesBep && bSeesAdisco && bSeesAep && aSeesDerp && bSeesDerp
  -- ── read the coord's DURABLE log; show distinct+stable addrs + mutual peers coord-side ──
  IO.sleep 100
  let events ← loadLog logPath
  let inspectPol ← loadPolicy (← IO.getEnv "DRORB_POLICY")
  let ctrl := servedFrom inspectPol events
  let addrOf (nk : String) : String :=
    match Control.lookupReg ctrl.nodes (Control.H2Noise.coreKeyOf nk) with
    | some r => (r.node.addresses.head?).elim "(none)" (fun p => s!"100.64.0.{Control.Ipam.v4ToNat p.addr - Control.Ipam.cgnatPool.net}")
    | none => "(unregistered)"
  IO.println s!"\n-- coord durable state ({events.length} events, {ctrl.nodes.length} nodes) --"
  IO.println s!"   A (nodekey aa..) -> {addrOf demoNkA}"
  IO.println s!"   B (nodekey bb..) -> {addrOf demoNkB}"
  -- mutual peers, coord-side (the exact projection the client received)
  let peersOf (nk : String) : List String :=
    (Control.Join.servedNetMapWire ctrl (Control.H2Noise.coreKeyOf nk)).peers.getD [] |>.flatMap (·.addresses)
  IO.println s!"   A's served peers : {peersOf demoNkA}"
  IO.println s!"   B's served peers : {peersOf demoNkB}"
  -- ── restart: replay the durable log from empty → SAME addresses ──
  let restarted := servedFrom inspectPol events
  let stableA := addrOf demoNkA == (match Control.lookupReg restarted.nodes (Control.H2Noise.coreKeyOf demoNkA) with
    | some r => (r.node.addresses.head?).elim "(none)" (fun p => s!"100.64.0.{Control.Ipam.v4ToNat p.addr - Control.Ipam.cgnatPool.net}") | none => "x")
  IO.println s!"\n-- restart replay : A keeps its address : {stableA} --"
  let distinct := addrOf demoNkA == "100.64.0.1" && addrOf demoNkB == "100.64.0.2"
  let mutualOk := hasA1 && hasA2 && hasB1 && hasB2
  let _ := coordTask
  if distinct && mutualOk && discoServed then do
    IO.println "\nPASS — two REAL clients got DISTINCT stable addresses (A=100.64.0.1, B=100.64.0.2)"
    IO.println "       over the REAL ts2021 Noise + record + h2 + IPAM + Store composition, EACH"
    IO.println "       RECEIVED the OTHER as a peer in its decrypted netmap, carrying the peer's REAL"
    IO.println "       DiscoKey + Endpoints + DERP home (region 1) — magicsock can now attempt a path."
    IO.println "MULTI-NODE TAILNET + DISCO/ENDPOINTS DEMONSTRATED (drorb-native clients; stock-client HTTP /key+/ts2021 front = dataplane residual)."
    return 0
  else do
    IO.eprintln s!"\nFAIL — distinct={distinct} mutual={mutualOk} discoServed={discoServed} (A[{hasA1},{hasA2}] B[{hasB1},{hasB2}])"
    return 1

/-! ### Phase-4 GATE (my-hand): the coord serves the OPERATOR HuJSON file, live-reloaded

`control-live policydemo <port>` authors a REAL operator HuJSON ACL to a file, points the
`h2coordMulti` coord at it (as `DRORB_POLICY` would), registers two nodes, and witnesses on
the wire (DECRYPTED client netmap) that the served `PacketFilters["base"]` reflects the
FILE — a distinctive `dst …:2222` rule the operator wrote — and NOT `Acl.demoPolicy`'s
`10.0.0.0/8` shape. Then it REWRITES the file (`…:2222` → `…:4443`), the file-mtime reload
watcher re-parses (proven `parseHuPolicy`) + re-compiles + bumps the tailnet generation, and
the SERVER-PUSH loop pushes the new `PacketFilters` to the OPEN long-poll — witnessed by the
`4443` rule arriving in the decrypted pushed delta, with `2222` gone from a fresh poll.

Everything cryptographic/structural is the proven Lean over real bytes (same composition as
`multidemo`); the ACL served is `Acl.compile (parsePolicy file)` throughout
(`servedFrom_filter_is_operator_compile`). -/

/-- Operator ACL v1 (HuJSON): `group:admin` (host `adminbox` = 100.64.0.9) may reach the
CGNAT tailnet on tcp/**2222**. Distinctive vs `demoPolicy` (which opens `10.0.0.0/8:22`). -/
def operatorPolicyV1 : String :=
  "{ \"hosts\": { \"adminbox\": \"100.64.0.9/32\" }, \"groups\": { \"group:admin\": [\"adminbox\"] }, \"acls\": [ { \"action\": \"accept\", \"src\": [\"group:admin\"], \"dst\": [\"100.64.0.0/10:2222\"], \"proto\": \"tcp\" } ] }"

/-- Operator ACL v2 — the same policy with the SSH port changed to tcp/**4443** (the
operator's live edit; the reload must serve THIS to the open long-poll). -/
def operatorPolicyV2 : String :=
  "{ \"hosts\": { \"adminbox\": \"100.64.0.9/32\" }, \"groups\": { \"group:admin\": [\"adminbox\"] }, \"acls\": [ { \"action\": \"accept\", \"src\": [\"group:admin\"], \"dst\": [\"100.64.0.0/10:4443\"], \"proto\": \"tcp\" } ] }"

def policydemo (port : UInt16) : IO UInt32 := do
  IO.println "== control-live POLICYDEMO : the coord serves the OPERATOR HuJSON ACL, live-reloaded =="
  let logPath := "/tmp/drorb-policydemo.log"
  let polPath := "/tmp/drorb-policydemo.hujson"
  (try IO.FS.removeFile logPath catch _ => pure ())
  -- ── author the operator ACL file (v1) and point the coord at it ──
  IO.FS.writeFile polPath operatorPolicyV1
  IO.println s!"\n-- authored operator ACL v1 at {polPath} (group:admin -> tailnet:2222) --"
  let coordTask ← IO.asTask (h2coordMulti port logPath (some polPath))
  IO.sleep 800
  let rrA : Control.Tailcfg.RegisterRequest := { Control.H2Noise.demoRegReq with nodeKey := demoNkA }
  let rrB : Control.Tailcfg.RegisterRequest := { Control.H2Noise.demoRegReq with nodeKey := demoNkB }
  IO.println "-- A registers --"; let _ ← runClientRPC port (mkRegStream rrA)
  IO.println "-- B registers --"; let _ ← runClientRPC port (mkRegStream rrB)
  IO.sleep 400
  let mrA : Control.Tailcfg.MapRequest :=
    { version := 138, nodeKey := demoNkA, stream := true }
  -- ── round 1: A polls; its netmap must carry the OPERATOR filter (2222), not demo (10.0.0.0/8) ──
  IO.println "\n-- A map-polls; inspecting served PacketFilters --"
  let plain1 ← runClientRPC port (mkMapStream mrA)
  let v1present := bytesInfix (Control.H2Noise.s2b "2222") plain1
  let opSrcPresent := bytesInfix (Control.H2Noise.s2b "100.64.0.9/32") plain1
  let demoAbsent := ! bytesInfix (Control.H2Noise.s2b "10.0.0.0/8") plain1
  IO.println s!"   served filter has operator rule (dst :2222) : {v1present}"
  IO.println s!"   served filter has operator src 100.64.0.9/32 : {opSrcPresent}"
  IO.println s!"   served filter is NOT demoPolicy (no 10.0.0.0/8) : {demoAbsent}"
  -- ── open a LONG-POLL in a task to catch the pushed delta when we reload ──
  IO.println "\n-- A opens a long-poll (server-push); we will edit the ACL and watch the push --"
  let pushTask ← IO.asTask (runClientRPC port (mkMapStream mrA))
  IO.sleep 900
  -- ── RELOAD: operator edits the file (2222 -> 4443); the watcher re-compiles + pushes ──
  IO.FS.writeFile polPath operatorPolicyV2
  IO.println s!"-- REWROTE {polPath} to v2 (tailnet:4443); waiting for the reload watcher + push --"
  IO.sleep 2200
  -- ── fresh poll: the served filter now reflects v2 (4443), v1 (2222) gone ──
  let plain2 ← runClientRPC port (mkMapStream mrA)
  let v2present := bytesInfix (Control.H2Noise.s2b "4443") plain2
  let v1gone := ! bytesInfix (Control.H2Noise.s2b "2222") plain2
  IO.println s!"\n-- fresh poll after reload --"
  IO.println s!"   served filter has NEW rule (dst :4443) : {v2present}    old rule (:2222) gone : {v1gone}"
  -- ── the pushed delta on the OPEN long-poll carried the new filter ──
  let pushedE ← IO.wait pushTask
  let pushed := pushedE.toOption.getD []
  let pushHasV2 := bytesInfix (Control.H2Noise.s2b "4443") pushed
  IO.println s!"   OPEN long-poll received a PUSHED delta carrying the new filter (:4443) : {pushHasV2}"
  -- ── coord-side ground truth: the served filter IS Acl.compile(parsePolicy(file v2)) ──
  match Control.Policy.parseHuPolicy operatorPolicyV2 with
  | .ok polV2 =>
      let events ← loadLog logPath
      let ctrl := servedFrom polV2 events
      let wireFilter := (Control.Join.servedNetMapWire ctrl (Control.H2Noise.coreKeyOf demoNkA)).packetFilters
      let expected := some [("base", (Control.Join.compiledPacketFilter polV2).map Control.Join.filterRuleToWire)]
      let coordMatch := wireFilter == expected
      IO.println s!"   coord-side: servedNetMapWire.packetFilters == Acl.compile(parsePolicy(file)) : {coordMatch}"
      let _ := coordTask
      if v1present && opSrcPresent && demoAbsent && v2present && pushHasV2 && coordMatch then do
        IO.println "\nPASS — the coord serves the OPERATOR HuJSON ACL (parsePolicy→Acl.compile), NOT demoPolicy;"
        IO.println "       a file edit hot-RELOADS + SERVER-PUSHES the new filter to the open long-poll."
        IO.println "OPERATOR ACL SERVED + LIVE RELOAD DEMONSTRATED (drorb-native clients; served filter = Acl.compile(parsePolicy(file)))."
        return 0
      else do
        IO.eprintln s!"\nFAIL — v1[{v1present},{opSrcPresent},{demoAbsent}] v2[{v2present},{v1gone}] push={pushHasV2} coordMatch={coordMatch}"
        return 1
  | .error e => do IO.eprintln s!"\nFAIL — operator v2 policy did not parse: {e}"; return 1

/-! ### Phase-5 GATE (my-hand): TARGETED per-node server-push at SCALE

`control-live pushdemo <port>` registers THREE nodes A, B, C, each opening a map
LONG-POLL (kept OPEN for server-push). Then a FOURTH node D joins. Each of the three
already-open streams receives a PUSHED `PeersChanged` delta carrying ONLY D
(`scopedDelta` over the proven `servedNetMapWire`) — NOT the whole peer set. We
witness, in each decrypted long-poll, that D's address (`100.64.0.4`) arrived on the
ALREADY-OPEN stream (no re-poll) and that the delta did NOT re-list the OTHER peers'
addresses (the targeted-scoping evidence: 1 entry, not N). The coord log prints
`PUSHED netmap delta (1 peer(s), TARGETED)`. The compile-time `#guard`s above pin the
same fact structurally on the emitted `MapResponse`. -/
def pushdemo (port : UInt16) : IO UInt32 := do
  IO.println "== control-live PUSHDEMO : TARGETED per-node server-push — a JOIN pushes ONLY the new peer =="
  let logPath := "/tmp/drorb-pushdemo.log"
  (try IO.FS.removeFile logPath catch _ => pure ())
  let coordTask ← IO.asTask (h2coordMulti port logPath)
  IO.sleep 700
  let mkRR (nk : String) : Control.Tailcfg.RegisterRequest :=
    { Control.H2Noise.demoRegReq with nodeKey := nk }
  let mkMR (nk : String) : Control.Tailcfg.MapRequest :=
    { version := 138, nodeKey := nk, stream := true }
  -- ── A, B, C register (distinct keys → 100.64.0.1/2/3) ──
  IO.println "\n-- A, B, C register --"
  let _ ← runClientRPC port (mkRegStream (mkRR demoNkA))
  let _ ← runClientRPC port (mkRegStream (mkRR demoNkB))
  let _ ← runClientRPC port (mkRegStream (mkRR demoNkC))
  IO.sleep 400
  -- ── A, B, C each OPEN a map long-poll (kept open for server-push) in a task ──
  IO.println "-- A, B, C open map long-polls (server-push streams held OPEN, patient readers) --"
  let d := Control.H2Noise.s2b "100.64.0.4"
  let taskA ← IO.asTask (runLongPollRPC port (mkMapStream (mkMR demoNkA)) d 10000)
  let taskB ← IO.asTask (runLongPollRPC port (mkMapStream (mkMR demoNkB)) d 10000)
  let taskC ← IO.asTask (runLongPollRPC port (mkMapStream (mkMR demoNkC)) d 10000)
  IO.sleep 1400
  -- ── D JOINS as the 4th node: the three OPEN streams must each get a delta with ONLY D ──
  IO.println "\n-- D (4th node) joins — existing A/B/C streams must receive a delta carrying ONLY D --"
  let _ ← runClientRPC port (mkRegStream (mkRR demoNkD))
  let _ ← runClientRPC port (mkMapStream (mkMR demoNkD))
  IO.sleep 2500
  -- ── collect what the three OPEN streams received (decrypted plaintext) ──
  let plainA := (← IO.wait taskA).toOption.getD []
  let plainB := (← IO.wait taskB).toOption.getD []
  let plainC := (← IO.wait taskC).toOption.getD []
  -- The PUSHED delta is the frame body AFTER the `"PeersChanged"` key. It must carry
  -- D's address (100.64.0.4) and NOT the OTHER peers' addresses (targeted = 1 entry).
  let judge (nm : String) (plain : List UInt8) (other1 other2 : String) : IO Bool := do
    let delta := afterInfix (Control.H2Noise.s2b "PeersChanged") plain
    let hasD := bytesInfix d delta
    let noO1 := ! bytesInfix (Control.H2Noise.s2b other1) delta
    let noO2 := ! bytesInfix (Control.H2Noise.s2b other2) delta
    IO.println s!"   {nm} ({plain.length}B): pushed delta carries D (100.64.0.4)={hasD}  and does NOT re-list {other1}={noO1} / {other2}={noO2}"
    return hasD && noO1 && noO2
  IO.println "\n-- what each OPEN stream received on the wire (delta = bytes after \"PeersChanged\") --"
  let aOk ← judge "A" plainA "100.64.0.2" "100.64.0.3"
  let bOk ← judge "B" plainB "100.64.0.1" "100.64.0.3"
  let cOk ← judge "C" plainC "100.64.0.1" "100.64.0.2"
  let _ := coordTask
  if aOk && bOk && cOk then do
    IO.println "\nPASS — a 4th node's JOIN pushed a delta carrying ONLY that node (1 entry, not N)"
    IO.println "       to each of the three ALREADY-OPEN map streams, over the REAL ts2021 Noise +"
    IO.println "       record + h2 composition — each existing client converged on the newcomer"
    IO.println "       WITHOUT re-polling, and the delta is a sub-projection of the proven"
    IO.println "       servedNetMapWire (scopedDelta_peers_sublist)."
    IO.println "TARGETED PER-NODE SERVER-PUSH DEMONSTRATED (drorb-native clients; scoped delta = 1 peer)."
    return 0
  else do
    IO.eprintln s!"\nFAIL — targeted delta not witnessed: A={aOk} B={bOk} C={cOk}"
    return 1

/-! ### The h2-over-noise MY-HAND selftest (drives the REAL engine + REAL gate)

`control-live h2selftest` builds a synthetic HTTP/2 `POST /machine/register` request
(preface + SETTINGS + HEADERS + DATA) carrying a wire `RegisterRequest`, feeds it
through the VERIFIED `H2.Conn.feed` with `Control.H2Noise.mkHandler`, and checks the
h2 response body carries `"MachineAuthorized":true` for the valid pre-auth key and
`false` for a wrong one. This runs the whole composition — h2 engine, JSON codec,
`registerWithPreAuth` (EverCrypt SHA-256) — at RUNTIME (what `#guard` cannot, since the
gate calls `@[extern]` crypto). It realizes `Control.H2Noise.registerDecide_gate`. -/

def h2ClientRegisterStream (rr : Control.Tailcfg.RegisterRequest) : List UInt8 :=
  let reqJson := Control.TailcfgWire.renderStr (Control.Tailcfg.RegisterRequest.toJson rr)
  let reqBlock := H2.HpackEncode.encodeHeaders
    [ (Control.H2Noise.s2b ":method", Control.H2Noise.s2b "POST")
    , (Control.H2Noise.s2b ":path", Control.H2Noise.s2b "/machine/register")
    , (Control.H2Noise.s2b ":scheme", Control.H2Noise.s2b "http")
    , (Control.H2Noise.s2b ":authority", Control.H2Noise.s2b "drorb") ]
  H2.Conn.clientPreface
    ++ H2.Conn.frameHdr 0 0x4 0 0                    -- empty client SETTINGS
    ++ H2.Conn.headersFrame 1 reqBlock               -- HEADERS (END_HEADERS)
    ++ H2.Conn.dataFrame 1 true (Control.H2Noise.s2b reqJson)  -- DATA (END_STREAM)

def h2selftest : IO UInt32 := do
  IO.println "== control-live h2selftest : POST /machine/register over the VERIFIED h2 engine + PROVEN gate =="
  let cfg := Control.H2Noise.demoCfg
  let bytesInfix (needle hay : List UInt8) : Bool :=
    (List.range (hay.length + 1)).any (fun i => needle.isPrefixOf (hay.drop i))
  let run (rr : Control.Tailcfg.RegisterRequest) : Bool :=
    let (_, out, _) := Control.H2Noise.feedChunk cfg H2.Conn.initState (h2ClientRegisterStream rr)
    bytesInfix (Control.H2Noise.s2b "\"MachineAuthorized\":true") out
  let good := run Control.H2Noise.demoRegReq
  let bad  := run Control.H2Noise.demoBadReq
  IO.println s!"valid pre-auth key -> response body has MachineAuthorized:true : {good}"
  IO.println s!"WRONG   pre-auth key -> response body has MachineAuthorized:true : {bad} (must be false)"
  -- also witness the raw response is a well-formed h2 byte stream (server preface + settings ack present)
  let (_, out, _) := Control.H2Noise.feedChunk cfg H2.Conn.initState (h2ClientRegisterStream Control.H2Noise.demoRegReq)
  IO.println s!"h2 response octets emitted : {out.length}B (server SETTINGS + ACK + HEADERS + DATA)"
  if good && !bad then do
    IO.println "\nPASS - the register RPC roundtrips through the VERIFIED h2 engine and the PROVEN"
    IO.println "       registerWithPreAuth gate: valid key ADMITTED, wrong key REJECTED, over h2-over-noise."
    return 0
  else do IO.eprintln "\nFAIL - the h2-over-noise register composition did not cross-check."; return 1

/-- Default durable-log path for the coord when none is given on the command line. -/
def defaultLogPath : String := "/tmp/drorb-control-coord.log"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | ["h2selftest"] => h2selftest
  | ["h2coord", portS] =>
    match portS.toNat? with
    | some p => h2coord p.toUInt16 defaultLogPath
    | none => do IO.eprintln "control-live h2coord <port> [logfile]: bad port"; return 1
  | ["h2coord", portS, logPath] =>
    match portS.toNat? with
    | some p => h2coord p.toUInt16 logPath
    | none => do IO.eprintln "control-live h2coord <port> [logfile]: bad port"; return 1
  | ["h2coord-multi", portS] =>
    match portS.toNat? with
    | some p => h2coordMulti p.toUInt16 defaultLogPath
    | none => do IO.eprintln "control-live h2coord-multi <port> [logfile]: bad port"; return 1
  | ["h2coord-multi", portS, logPath] =>
    match portS.toNat? with
    | some p => h2coordMulti p.toUInt16 logPath
    | none => do IO.eprintln "control-live h2coord-multi <port> [logfile]: bad port"; return 1
  | ["multidemo", portS] =>
    match portS.toNat? with
    | some p => multidemo p.toUInt16
    | none => do IO.eprintln "control-live multidemo <port>: bad port"; return 1
  | ["policydemo", portS] =>
    match portS.toNat? with
    | some p => policydemo p.toUInt16
    | none => do IO.eprintln "control-live policydemo <port>: bad port"; return 1
  | ["pushdemo", portS] =>
    match portS.toNat? with
    | some p => pushdemo p.toUInt16
    | none => do IO.eprintln "control-live pushdemo <port>: bad port"; return 1
  | ["gate"] => gate "/tmp/drorb-control-gate.log"
  | ["gate", logPath] => gate logPath
  | ["coord", portS] =>
    match portS.toNat? with
    | some p => coord p.toUInt16 defaultLogPath
    | none => do IO.eprintln "control-live coord <port> [logfile]: bad port"; return 1
  | ["coord", portS, logPath] =>
    match portS.toNat? with
    | some p => coord p.toUInt16 logPath
    | none => do IO.eprintln "control-live coord <port> [logfile]: bad port"; return 1
  | ["node", host, portS] =>
    match portS.toNat? with
    | some p => node host p.toUInt16
    | none => do IO.eprintln "control-live node <host> <port>: bad port"; return 1
  | _ => do
    IO.eprintln "usage: control-live selftest | gate [logfile] | coord <port> [logfile] | node <host> <port>"
    return 1

end ControlLive

def main (args : List String) : IO UInt32 := ControlLive.main args
