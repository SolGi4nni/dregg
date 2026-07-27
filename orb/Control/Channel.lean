import Control
import Wireguard
import Crypto
import Control.Ts2021Core
import Control.Ts2021Transcript
import Hygiene
/-!
# Control.Channel — the ts2021 Noise-IK control channel

The `Control` foundation models the coordination server as an in-memory
transition system: a node registers, is authorized, and polls for its netmap.
But those `RegisterRequest` / `MapRequest` / `MapResponse` messages have to
*travel* between the node and the coordination server over a secure transport.
This module is that transport — the **ts2021** control protocol.

ts2021 is the public Tailscale control-plane protocol (`control/controlbase` and
`control/controlhttp` in github.com/tailscale/tailscale, BSD-3; the community
coordination server github.com/juanfont/headscale, BSD-3, speaks the responder
side). It is a **Noise IK** handshake — `Noise_IK_25519_ChaChaPoly_BLAKE2s` —
run over HTTP, after which the coordination messages ride as AEAD-sealed control
frames. Everything here is derived from that public specification and source; it
is an independent clean-room model.

## The two ends

  * The **node** (client) is the Noise **initiator**. Its static key is its
    **machine key** (`Control.MachineKey`) — the durable device identity. It
    learns the coordination server's static public key out of band (from the
    login server), so it can address the responder.
  * The **coordination server** is the Noise **responder**. Its static key is
    the fixed server key every node trusts.

The IK pattern is exactly right for this: the initiator already knows the
responder's static key (`I`nitiator-`K`nown), and the initiator transmits its own
static (machine) key *encrypted* inside the first message, so the machine
identity is never exposed on the wire and is authenticated to the server.

## What is reused, not re-derived (`Wireguard.Noise`)

drorb already has a verified Noise IK handshake — WireGuard's `Noise_IKpsk2`
variant in `Wireguard.Noise`, over the same primitives ts2021 uses (X25519 +
ChaCha20-Poly1305 + BLAKE2s). We **reuse** that machinery rather than re-derive
crypto:

  * `Wireguard.Noise.initiatorChainingKey` / `responderChainingKey` — the DH
    ratchet computed from opposite ends.
  * `Wireguard.Noise.transportKeys` — the 64-byte `KDF2` transport material.
  * `Wireguard.Noise.wg_transport_keys_agree` — **both peers derive identical
    transport keys** (the X25519 agreement, discharged by `Crypto`).
  * `Wireguard.Noise.sealStatic` / `wg_static_key_authenticated` /
    `wg_static_key_unforgeable` — the AEAD-sealed static (machine) key and its
    forgery-resistance.

ts2021 is Noise **IK** (no preshared key), where WireGuard is IK**psk2**. §1/§2
reuse the IKpsk2 ratchet with its `psk` slot instantiated at a fixed *public*
constant (`tsPsk`). A public post-mix of the chaining key does not weaken key
agreement — both peers apply the identical public step — so the reused
`wg_transport_keys_agree` transfers verbatim, and the security still rests
entirely on the DH chain of the static + ephemeral keys (one static being the
machine key). That model is retained here **unchanged**, with every theorem it
carries.

But IKpsk2's extra `KDF3` PSK step means its transcript and split keys are NOT
byte-identical to a stock ts2021 peer. So the channel the **live** control plane
runs is **§2b**: the same FSM shape over `Control.Ts2021Core`'s plain
`Noise_IK` — no PSK, the exact `handshake.go` mix order — with transitions that
consume and emit the real `controlbase` frames (101-byte initiation, 51-byte
response). §2b re-proves §2's safety theorems and feeds §3–§5's sealed-record
layer unchanged. The wire residual named below is closed by it.

## Trust surface

No new crypto axioms. The channel's guarantees compose the `Crypto` assumptions
(`x25519_dh_agree`, `chacha_open_seal_roundtrip`, `chacha_open_authentic`)
already discharged by HACL*/EverCrypt upstream, exactly as `Wireguard` and
`Disco` do. This module touches no serve / dataplane file; it composes with the
`Control` foundation types.
-/

namespace Control.Channel

open Wireguard

/-! ## §0  Byte-view helpers and protocol constants

The AEAD primitives operate on `ByteArray`; the codec algebra (`Control.Bytes =
List UInt8`) operates on lists. The two adapters `bytesOf` / `baOf` and their
round-trip lemmas `baOf_bytesOf` / `bytesOf_baOf` are declared in
`Control.Ts2021Core` — in THIS namespace, so every reference here and downstream
is unchanged. They live in that lower module because the byte-exact handshake
builders this FSM calls (§2b) need them, and those builders must sit below this
file. -/

/-- The ts2021 control-protocol version (`controlbase` protocol version). -/
def protocolVersion : Nat := 1

/-- The Noise handshake name for ts2021 — Noise IK, X25519, ChaCha20-Poly1305,
BLAKE2s (`control/controlbase`). -/
def protocolName : ByteArray := "Noise_IK_25519_ChaChaPoly_BLAKE2s".toUTF8

/-- The fixed public constant instantiating the reused IKpsk2 ratchet's `psk`
slot (ts2021 is psk-free — see the module header). 32 zero bytes: a public value
both peers mix identically, so it is inert to key agreement. -/
def tsPsk : ByteArray := ⟨Array.replicate 32 (0 : UInt8)⟩

/-! ## §1  The Noise-IK transport-key derivation (reused machinery)

Both ends run the reused `Wireguard.Noise` ratchet, differing only in which end
computes the four DH secrets. The 64-byte output splits into the two directional
transport keys. -/

/-- One direction's transport keys: this peer's send key and receive key. -/
structure TxKeys where
  send : ByteArray
  recv : ByteArray

/-- First 32 bytes of the 64-byte transport material (`T_send_i`). -/
def firstHalf (m : ByteArray) : ByteArray := m.extract 0 32
/-- Second 32 bytes of the 64-byte transport material (`T_recv_i`). -/
def secondHalf (m : ByteArray) : ByteArray := m.extract 32 64

/-- The **initiator** (node) uses the first half to send, the second to receive
(`controlbase` orientation). -/
def initiatorTx (m : ByteArray) : TxKeys := { send := firstHalf m, recv := secondHalf m }
/-- The **responder** (coordination server) uses the halves swapped, so its send
key is the initiator's receive key and vice versa. -/
def responderTx (m : ByteArray) : TxKeys := { send := secondHalf m, recv := firstHalf m }

/-- The node's (initiator's) 64-byte transport material: it holds its machine
static `mpriv` and ephemeral `epriv`, was told the server static `spubS`, and
learns the server ephemeral `epubS` from the response. -/
def nodeMaterial (mpriv epriv epub spubS epubS : ByteArray) : Option ByteArray :=
  Noise.transportKeys (Noise.initiatorChainingKey mpriv epriv epub spubS epubS tsPsk)

/-- The coordination server's (responder's) 64-byte transport material: it holds
its static `spriv` and ephemeral `epriv`, and learns the node's machine static
`mpub` (by decrypting the initiation) and ephemeral `epubN` (in the clear). -/
def serverMaterial (spriv epriv mpub epubN epubS : ByteArray) : Option ByteArray :=
  Noise.transportKeys (Noise.responderChainingKey spriv epriv mpub epubN epubS tsPsk)

/-- **The handshake key agreement.** Given well-formed keypairs (each public
point is its scalar's X25519 base multiple), the node and the coordination
server — computing their DH secrets from opposite ends — derive the *same*
64-byte transport material. Reuses `Wireguard.Noise.wg_transport_keys_agree`
(the X25519 agreement, discharged by `Crypto`); the ts2021 channel inherits the
verified WireGuard Noise guarantee directly. -/
theorem handshake_keys_agree
    (mpriv epriv spriv esPriv mpub epub spubS epubS : ByteArray)
    (hM : Crypto.x25519Base mpriv = some mpub)
    (hE : Crypto.x25519Base epriv = some epub)
    (hS : Crypto.x25519Base spriv = some spubS)
    (hES : Crypto.x25519Base esPriv = some epubS) :
    nodeMaterial mpriv epriv epub spubS epubS
      = serverMaterial spriv esPriv mpub epub epubS := by
  unfold nodeMaterial serverMaterial
  exact Noise.wg_transport_keys_agree mpriv epriv spriv esPriv mpub epub spubS epubS tsPsk
    hM hE hS hES

/-- **The directional keys agree.** From one shared 64-byte material, the node's
send key is the server's receive key and the node's receive key is the server's
send key — so each side can open what the other sealed. -/
theorem tx_directions_agree (m : ByteArray) :
    (initiatorTx m).send = (responderTx m).recv ∧
    (initiatorTx m).recv = (responderTx m).send :=
  ⟨rfl, rfl⟩

/-! ## §2  The handshake as a transition system

A compact transition system in the shape of `TlsHandshake.serverStep` and the
WireGuard handshake FSM: a `Phase`, a role-tagged `Session`, and a total `step`
that consumes handshake events and reaches `established` (`.up`) carrying the
derived transport keys. The safety facts mirror the WireGuard handshake's
`wg_no_transport_before_handshake` / `wg_established_needs_handshake`. -/

/-- Which end of the handshake this peer plays. -/
inductive Role where
  | node   -- the initiator (client), machine-key static identity
  | coord  -- the responder (coordination server)
deriving DecidableEq, Repr

/-- A peer's handshake session material. -/
structure Session where
  role  : Role
  /-- Own static private scalar (node: machine key; coord: server key). -/
  spriv : ByteArray
  /-- Own static public point. -/
  spub  : ByteArray
  /-- Own ephemeral private scalar. -/
  epriv : ByteArray
  /-- Own ephemeral public point. -/
  epub  : ByteArray
  /-- Known peer static public (node: the server key; unused by coord). -/
  peerS : ByteArray

/-- Handshake phase. `up` carries the derived directional transport keys. -/
inductive Phase where
  /-- No handshake in progress. -/
  | fresh
  /-- Node emitted the initiation, awaiting the server response. -/
  | awaitResp
  /-- Handshake complete; the channel is up with these transport keys. -/
  | up (tx : TxKeys)

/-- Events the environment can deliver to the handshake. -/
inductive Ev where
  /-- Begin (node only): emit the initiation. -/
  | start
  /-- The coordination server receives an initiation carrying the node's
  ephemeral public and its (decrypted) machine static public. -/
  | recvInit (epubN mpub : ByteArray)
  /-- The node receives the server's response carrying the server ephemeral. -/
  | recvResp (epubS : ByteArray)

/-- Handshake outputs (the wire sends). -/
inductive Out where
  /-- Node → server: the initiation carrying the node ephemeral public. -/
  | sendInit (epub : ByteArray)
  /-- Server → node: the response carrying the server ephemeral public. -/
  | sendResp (epub : ByteArray)
  /-- Nothing to emit. -/
  | idle

/-- **The handshake transition.** Total on phase × event. The node begins from
`.fresh` on `.start`; the coordination server completes from `.fresh` on
`.recvInit` (deriving responder transport keys and learning the machine key);
the node completes from `.awaitResp` on `.recvResp` (deriving initiator
transport keys). Any other pairing is inert. -/
def step (ss : Session) : Phase → Ev → Phase × Out
  | .fresh, .start =>
    match ss.role with
    | .node  => (.awaitResp, .sendInit ss.epub)
    | .coord => (.fresh, .idle)
  | .fresh, .recvInit epubN mpub =>
    match serverMaterial ss.spriv ss.epriv mpub epubN ss.epub with
    | some m => (.up (responderTx m), .sendResp ss.epub)
    | none   => (.fresh, .idle)
  | .awaitResp, .recvResp epubS =>
    match nodeMaterial ss.spriv ss.epriv ss.epub ss.peerS epubS with
    | some m => (.up (initiatorTx m), .idle)
    | none   => (.awaitResp, .idle)
  | p, _ => (p, .idle)

/-- States reachable under some event trace from `.fresh`. -/
inductive Reachable (ss : Session) : Phase → Prop where
  | fresh : Reachable ss .fresh
  | step {p : Phase} (h : Reachable ss p) (e : Ev) : Reachable ss (step ss p e).1

/-- **No channel before the handshake completes.** Starting the handshake from
`.fresh` never yields an established (`.up`) channel — `.start` only *emits* the
initiation; it derives no transport keys. (The WireGuard-handshake analog of
`wg_no_transport_before_handshake`.) -/
theorem channel_no_up_from_start (ss : Session) (tx : TxKeys) :
    (step ss .fresh .start).1 ≠ .up tx := by
  simp only [step]
  cases ss.role <;> simp

/-- **Entering the channel is a handshake completion.** If a step takes a
not-yet-established phase to `.up`, the event was a handshake message —
`recvInit` (server side) or `recvResp` (node side) — never `.start`. The
transport keys appear only on completing the Noise exchange. (The analog of
`wg_established_needs_handshake`.) -/
theorem channel_up_needs_handshake (ss : Session) (p : Phase) (e : Ev) (tx : TxKeys)
    (hp : ∀ tx0, p ≠ .up tx0)
    (h : (step ss p e).1 = .up tx) :
    (∃ epubN mpub, e = .recvInit epubN mpub) ∨ (∃ epubS, e = .recvResp epubS) := by
  cases p with
  | up tx0 => exact absurd rfl (hp tx0)
  | fresh =>
    cases e with
    | start =>
      exfalso; exact channel_no_up_from_start ss tx h
    | recvInit epubN mpub => exact Or.inl ⟨epubN, mpub, rfl⟩
    | recvResp epubS =>
      -- fresh + recvResp is inert (catch-all), stays fresh
      simp only [step] at h; exact Phase.noConfusion h
  | awaitResp =>
    cases e with
    | start => simp only [step] at h; exact Phase.noConfusion h
    | recvInit epubN mpub => simp only [step] at h; exact Phase.noConfusion h
    | recvResp epubS => exact Or.inr ⟨epubS, rfl⟩

/-- **The established transport keys agree across the two ends.** If the node
completes with the initiator keys derived from material `m`, and the server
completes with the responder keys derived from the *same* material (guaranteed by
`handshake_keys_agree` under well-formed keypairs), then the node's send key is
the server's receive key and vice versa — the channel is bidirectionally
keyed. -/
theorem channel_established_keys_agree
    (mpriv epriv spriv esPriv mpub epub spubS epubS m : ByteArray)
    (hM : Crypto.x25519Base mpriv = some mpub)
    (hE : Crypto.x25519Base epriv = some epub)
    (hS : Crypto.x25519Base spriv = some spubS)
    (hES : Crypto.x25519Base esPriv = some epubS)
    (hNode : nodeMaterial mpriv epriv epub spubS epubS = some m) :
    serverMaterial spriv esPriv mpub epub epubS = some m ∧
    (initiatorTx m).send = (responderTx m).recv ∧
    (initiatorTx m).recv = (responderTx m).send := by
  refine ⟨?_, tx_directions_agree m⟩
  rw [← handshake_keys_agree mpriv epriv spriv esPriv mpub epub spubS epubS hM hE hS hES]
  exact hNode

/-! ## §2b  The BYTE-EXACT ts2021 handshake FSM — the live control channel

§2's `step` reuses WireGuard's `Noise_IKpsk2` ratchet with a public all-zero PSK.
That is an honest **key-agreement** model (`handshake_keys_agree` is a real
theorem over the real X25519), but IKpsk2 mixes the PSK with an extra `KDF3`
step, so its transcript hash and its split keys are **not** byte-identical to a
stock ts2021 peer, and §2's `Ev` carries already-parsed public keys rather than
the bytes that actually traverse the wire.

This section is the handshake FSM the **live** channel runs. It is the same
transition-system shape — `Session` / `Phase` / `Ev` / `Out` / `step`, with the
same two safety theorems re-proven, nothing weakened — but every transition is
driven by, and emits, the **actual `controlbase` bytes**:

  * `.start` (node) emits the real **101-byte** initiation frame
    `[ver:u16BE][1][len:u16BE][e‖enc(s)‖tag]`;
  * `.recvInit` (coord) consumes that frame, parses it, replays the Noise
    transcript, and emits the real **51-byte** response frame
    `[2][len:u16BE][er‖tag]`;
  * `.recvResp` (node) consumes the response frame and completes.

The crypto is `Control.Ts2021Core`'s plain `Noise_IK_25519_ChaChaPoly_BLAKE2s`
— no PSK, `mix_hash(prologue) → mix_hash(rs) → e → es → s → ss → er → ee → se`,
exactly `control/controlbase/handshake.go`. The `Split()` orientation is §1's
`initiatorTx` / `responderTx` (client `tx=c1,rx=c2`, server `tx=c2,rx=c1`), so
the whole sealed-record layer of §3–§5 composes on top of these keys unchanged.

The Noise core these transitions call is the SAME code the `control-ts2021-kat`
known-answer test validates against the published `noise-c`
`Noise_IK_25519_ChaChaPoly_BLAKE2s` vector — one definitional home, so the KAT's
byte-exactness is the FSM's byte-exactness. `control-ts2021-channel-kat` drives
these transitions end to end and checks the emitted frames byte-for-byte. -/

namespace Ts2021

open Control.Ts2021Wire

/-- A peer's byte-exact ts2021 handshake session. Adds the `controlbase`
protocol `version` (which is bound into the Noise prologue as decimal ASCII,
`handshake.go` `protocolVersionPrologue`) to §2's `Session` shape. -/
structure Session where
  role    : Role
  /-- The `controlbase` protocol version carried in the initiation header and
  bound into the Noise prologue. -/
  version : Nat
  /-- Own static private scalar (node: machine key; coord: server key). -/
  spriv   : ByteArray
  /-- Own static public point. -/
  spub    : ByteArray
  /-- Own ephemeral private scalar. -/
  epriv   : ByteArray
  /-- Own ephemeral public point. -/
  epub    : ByteArray
  /-- Known peer static public (node: the server key `rs`; unused by coord). -/
  peerS   : ByteArray

/-- Handshake phase. `awaitResp` now carries the initiator's **post-initiation
Noise symmetric state** — the running transcript it must continue in order to
read the response; that state is exactly what makes the transcript byte-exact
rather than merely key-agreeing. -/
inductive Phase where
  /-- No handshake in progress. -/
  | fresh
  /-- Node emitted the initiation; carries its running Noise transcript. -/
  | awaitResp (st : Sym)
  /-- Handshake complete; the channel is up with these transport keys. -/
  | up (tx : TxKeys)

/-- Events the environment delivers — now the **raw wire frames**. -/
inductive Ev where
  /-- Begin (node only): build and emit the initiation frame. -/
  | start
  /-- The coordination server receives the 101-byte initiation frame. -/
  | recvInit (frame : Control.Bytes)
  /-- The node receives the 51-byte response frame. -/
  | recvResp (frame : Control.Bytes)

/-- Handshake outputs — the **bytes actually written to the wire**. -/
inductive Out where
  /-- Node → server: the byte-exact initiation frame. -/
  | sendInit (frame : Control.Bytes)
  /-- Server → node: the byte-exact response frame. -/
  | sendResp (frame : Control.Bytes)
  /-- Nothing to emit. -/
  | idle

/-! ### The three transitions

Each transition is its own definition, so `step` is a shallow dispatch. That
keeps the FSM readable AND keeps its equational reasoning cheap: a proof about
one transition unfolds only that transition, never the whole handshake. -/

/-- **Node, `.start`.** Build the byte-exact 101-byte initiation frame and keep
the running Noise transcript. The coordinator has nothing to start. -/
def initiate (ss : Session) : Phase × Out :=
  match ss.role with
  | .coord => (.fresh, .idle)
  | .node =>
    match mkTs2021Initiation ss.version ss.spriv ss.spub ss.epriv ss.epub ss.peerS with
    | none   => (.fresh, .idle)
    | some p => (.awaitResp p.2, .sendInit p.1)

/-- **Coordinator, `.recvInit`.** Parse the initiation frame, replay the Noise
transcript (recovering the node's ephemeral and its encrypted machine static),
emit the byte-exact 51-byte response, and land on the responder split of the
completed transcript. A node never answers an initiation. -/
def respond (ss : Session) (frame : Control.Bytes) : Phase × Out :=
  match ss.role with
  | .node => (.fresh, .idle)
  | .coord =>
    match parseInitiation frame with
    | none   => (.fresh, .idle)
    | some p =>
      match readInitiation (tsPrologue p.1) ss.spriv ss.spub (baOf p.2.1) with
      | none   => (.fresh, .idle)
      | some q =>
        match mkTs2021ResponseSt q.2.2.2 ss.epriv ss.epub q.1 q.2.1 with
        | none   => (.fresh, .idle)
        | some r => (.up (responderTx r.2.material), .sendResp r.1)

/-- **Node, `.recvResp`.** Parse the response frame, continue the running Noise
transcript through `ee`/`se`, and land on the initiator split. -/
def complete (ss : Session) (st : Sym) (frame : Control.Bytes) : Phase × Out :=
  match parseResponse frame with
  | none   => (.awaitResp st, .idle)
  | some p =>
    match readResponse st ss.epriv ss.spriv (baOf p.1) with
    | none   => (.awaitResp st, .idle)
    | some q => (.up (initiatorTx q.2.material), .idle)

/-- **The byte-exact handshake transition.** Total on phase × event; any pairing
other than the three handshake transitions is inert. -/
def step (ss : Session) : Phase → Ev → Phase × Out
  | .fresh,        .start        => initiate ss
  | .fresh,        .recvInit f   => respond ss f
  | .awaitResp st, .recvResp f   => complete ss st f
  | p,             _             => (p, .idle)

/-- States reachable under some event trace from `.fresh`. -/
inductive Reachable (ss : Session) : Phase → Prop where
  | fresh : Reachable ss .fresh
  | step {p : Phase} (h : Reachable ss p) (e : Ev) : Reachable ss (step ss p e).1

/-- **No channel before the handshake completes** (byte-exact FSM). Starting from
`.fresh` never yields an established channel — `.start` only *emits* the
initiation frame; no transport keys exist yet. The byte-exact analog of
`channel_no_up_from_start`, itself the analog of
`Wireguard.wg_no_transport_before_handshake`. -/
theorem no_up_from_start (ss : Session) (tx : TxKeys) :
    (step ss .fresh .start).1 ≠ .up tx := by
  intro h
  replace h : (initiate ss).1 = .up tx := h
  unfold initiate at h
  split at h
  · exact Phase.noConfusion h
  · split at h
    · exact Phase.noConfusion h
    · exact Phase.noConfusion h

/-- **Entering the channel is a handshake completion** (byte-exact FSM). If a step
takes a not-yet-established phase to `.up`, the event carried a handshake *frame*
— the initiation (server side) or the response (node side) — never `.start`.
The byte-exact analog of `channel_up_needs_handshake`. -/
theorem up_needs_handshake (ss : Session) (p : Phase) (e : Ev) (tx : TxKeys)
    (hp : ∀ tx0, p ≠ .up tx0)
    (h : (step ss p e).1 = .up tx) :
    (∃ f, e = .recvInit f) ∨ (∃ f, e = .recvResp f) := by
  cases p with
  | up tx0 => exact absurd rfl (hp tx0)
  | fresh =>
    cases e with
    | start => exact absurd h (no_up_from_start ss tx)
    | recvInit f => exact Or.inl ⟨f, rfl⟩
    | recvResp f =>
      replace h : (Phase.fresh, Out.idle).1 = Phase.up tx := h
      exact Phase.noConfusion h
  | awaitResp st =>
    cases e with
    | start =>
      replace h : (Phase.awaitResp st, Out.idle).1 = Phase.up tx := h
      exact Phase.noConfusion h
    | recvInit f =>
      replace h : (Phase.awaitResp st, Out.idle).1 = Phase.up tx := h
      exact Phase.noConfusion h
    | recvResp f => exact Or.inr ⟨f, rfl⟩

/-- **The node's established keys are the initiator split of its own completed
Noise transcript.** Reaching `.up` from `.awaitResp` means the response frame
parsed, the Noise transcript continued through `ee`/`se`, and the keys are
`initiatorTx` of that transcript's 64-byte material — `handshake.go`'s client
`tx = c1, rx = c2`. Nothing else can put the node in `.up`. -/
theorem node_up_material (ss : Session) (st : Sym) (frame : Control.Bytes) (tx : TxKeys)
    (h : (step ss (.awaitResp st) (.recvResp frame)).1 = .up tx) :
    ∃ p q,
      parseResponse frame = some p ∧
      readResponse st ss.epriv ss.spriv (baOf p.1) = some q ∧
      tx = initiatorTx q.2.material := by
  replace h : (complete ss st frame).1 = .up tx := h
  unfold complete at h
  split at h
  · exact Phase.noConfusion h
  · rename_i p heq
    split at h
    · exact Phase.noConfusion h
    · rename_i q heq2
      refine ⟨p, q, heq, heq2, ?_⟩
      replace h : Phase.up (initiatorTx q.2.material) = Phase.up tx := h
      rw [Phase.up.injEq] at h
      exact h.symm

/-- **The coordinator's established keys are the responder split of its own
completed Noise transcript.** Reaching `.up` from `.fresh` on an initiation frame
means the frame parsed, the initiation replayed (recovering the node's ephemeral
and its encrypted machine static), the response was built, and the keys are
`responderTx` of that transcript's material — `handshake.go`'s server
`tx = c2, rx = c1`. -/
theorem coord_up_material (ss : Session) (frame : Control.Bytes) (tx : TxKeys)
    (h : (step ss .fresh (.recvInit frame)).1 = .up tx) :
    ss.role = .coord ∧
    ∃ p q r,
      parseInitiation frame = some p ∧
      readInitiation (tsPrologue p.1) ss.spriv ss.spub (baOf p.2.1) = some q ∧
      mkTs2021ResponseSt q.2.2.2 ss.epriv ss.epub q.1 q.2.1 = some r ∧
      tx = responderTx r.2.material := by
  replace h : (respond ss frame).1 = .up tx := h
  unfold respond at h
  split at h
  · exact Phase.noConfusion h
  · rename_i hrole
    refine ⟨hrole, ?_⟩
    split at h
    · exact Phase.noConfusion h
    · rename_i p heq
      split at h
      · exact Phase.noConfusion h
      · rename_i q heq2
        split at h
        · exact Phase.noConfusion h
        · rename_i r heq3
          refine ⟨p, q, r, heq, heq2, heq3, ?_⟩
          replace h : Phase.up (responderTx r.2.material) = Phase.up tx := h
          rw [Phase.up.injEq] at h
          exact h.symm

/-- **The byte-exact channel is bidirectionally keyed.** When the two ends
complete on transcripts with the same 64-byte material — which is what "the
transcripts are byte-identical" means, and which the `control-ts2021-channel-kat`
run demonstrates on real crypto through these very transitions — the node's send
key IS the coordinator's receive key and vice versa. Composed with
`node_up_material` / `coord_up_material`, this is the FSM-level statement of
§1's `tx_directions_agree` for the byte-exact path, and it is exactly the
hypothesis §3–§5's `seal_open` / `*_channel_roundtrip` need (`hk : sk = rk`). -/
theorem keys_agree_of_material (txN txC : TxKeys) (m : ByteArray)
    (hN : txN = initiatorTx m) (hC : txC = responderTx m) :
    txN.send = txC.recv ∧ txN.recv = txC.send := by
  subst hN; subst hC; exact tx_directions_agree m

/-! ### Residual of §2b (named boundary) — CLOSED

What is proven here is the FSM shape: the byte-exact transitions are the ONLY
way into `.up`, the keys at `.up` are exactly the `Split()` of the peer's own
completed Noise transcript, and — given equal transcript material — the channel
is bidirectionally keyed and every `Control` message round-trips through it.

**Correction (this note previously said the opposite).** It used to read: "What
is not a Lean theorem is that the two ends' transcripts always coincide … proving
it needs a byte-level algebra for `ByteArray` `++`/`extract` that drorb does not
have yet." BOTH halves were wrong, and are retracted:

  * the theorem EXISTS — `Control.Ts2021Transcript.transcripts_coincide`, over
    this very byte-exact core, for ALL well-formed handshakes; and
  * the algebra was largely ALREADY THERE — Lean 4.30 core ships the
    `ByteArray` `++`/`extract` lemmas (`extract_append`, `extract_append_eq_left`
    /`_right`, `size_append`, `extract_eq_empty_iff`); `Util.ByteArrayAlg` only
    packages the field-split forms a parser wants on top of them.

§2c below CONSUMES that theorem at the FSM level (`handshake_refines`), so the
two ends' key agreement is a conclusion of the transitions rather than something
demonstrated on one set of keys. `control-ts2021-channel-kat` remains as the
byte-level witness on real crypto (real EverCrypt ChaCha20-Poly1305, real
X25519, RFC 7693 BLAKE2s) and as the tie to the published `noise-c` vector —
evidence, no longer the argument. -/

/-! ### §2c  The transcript coincidence, CONSUMED

`Control.Ts2021Transcript.transcripts_coincide` proves — over the SAME
byte-exact Noise core these transitions call — that the responder's read of the
initiation reproduces the initiator's post-initiation state exactly, and the
initiator's read of the response reproduces the responder's final state exactly.
This section feeds that theorem INTO the FSM: driving the three transitions on
the actual wire frames lands BOTH peers in `.up`, and the two peers' transport
keys are the two directional splits of ONE 64-byte material — so
`keys_agree_of_material`'s hypothesis is no longer supplied by a KAT run on one
set of keys, it is DISCHARGED for every well-formed handshake. -/

/-- `baOf` inverts `bytesOf`: the byte-list view of a `ByteArray` repacks to it.
The FSM crosses this boundary once per message (the frames are `Control.Bytes`,
the Noise core is `ByteArray`), so the crossing must not lose information. -/
@[simp] theorem baOf_bytesOf (b : ByteArray) : baOf (bytesOf b) = b := by
  simp [baOf, bytesOf]

/-- The byte-list view has the array's length. -/
@[simp] theorem length_bytesOf (b : ByteArray) : (bytesOf b).length = b.size := by
  simp only [bytesOf, Array.length_toList]; rfl

/-- **After a `MixKey` the AEAD key is present**, so `EncryptAndHash` really
seals and the ciphertext is the plaintext plus the 16-byte Poly1305 tag. (Before
the first `MixKey`, `encryptAndHash` is the identity — which is why this is
stated for the post-`MixKey` state, the only shape the Noise_IK messages use.) -/
theorem size_encryptAndHash_mixKey (aeadExpands : AeadExpands)
    {s s' : Sym} {ikm pt ct : ByteArray}
    (h : (s.mixKey ikm).encryptAndHash pt = some (ct, s')) :
    ct.size = pt.size + 16 := by
  unfold Sym.encryptAndHash at h
  split at h
  · rename_i hk; simp [Sym.mixKey] at hk
  · split at h
    · rename_i c hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact aeadExpands _ _ _ _ _ hc
    · exact absurd h (by simp)

/-- **The initiation Noise message is 96 bytes + payload**: `e` (32) ‖
`enc(s)` (32+16) ‖ `enc(payload)` (|payload|+16). With ts2021's empty handshake
payload that is exactly the 96 the 101-byte frame declares. -/
theorem size_noiseInitiation (aeadExpands : AeadExpands)
    {prologue siPriv siPub eiPriv eiPub rsPub payload noiseMsg : ByteArray} {sI : Sym}
    (hei : eiPub.size = 32) (hsi : siPub.size = 32)
    (hInit : noiseInitiation prologue siPriv siPub eiPriv eiPub rsPub payload
               = some (noiseMsg, sI)) :
    noiseMsg.size = 96 + payload.size := by
  unfold noiseInitiation at hInit
  dsimp only at hInit
  split at hInit
  · exact absurd hInit (by simp)
  · split at hInit
    · exact absurd hInit (by simp)
    · rename_i encS s2 hE1
      split at hInit
      · exact absurd hInit (by simp)
      · split at hInit
        · exact absurd hInit (by simp)
        · rename_i encP s4 hE2
          simp only [Option.some.injEq, Prod.mk.injEq] at hInit
          obtain ⟨rfl, rfl⟩ := hInit
          have h1 := size_encryptAndHash_mixKey aeadExpands hE1
          have h2 := size_encryptAndHash_mixKey aeadExpands hE2
          rw [ByteArray.size_append3, hei, h1, h2, hsi]
          omega

/-- **The response Noise message is 48 bytes + payload**: `er` (32) ‖
`enc(payload)` (|payload|+16) — the 48 the 51-byte frame declares. -/
theorem size_noiseResponse (aeadExpands : AeadExpands)
    {s0 sR : Sym} {erPriv erPub eiPub siPub payload respMsg : ByteArray}
    (her : erPub.size = 32)
    (hResp : noiseResponse s0 erPriv erPub eiPub siPub payload = some (respMsg, sR)) :
    respMsg.size = 48 + payload.size := by
  unfold noiseResponse at hResp
  dsimp only at hResp
  split at hResp
  · exact absurd hResp (by simp)
  · split at hResp
    · exact absurd hResp (by simp)
    · split at hResp
      · exact absurd hResp (by simp)
      · rename_i encP s4 hE
        simp only [Option.some.injEq, Prod.mk.injEq] at hResp
        obtain ⟨rfl, rfl⟩ := hResp
        have h1 := size_encryptAndHash_mixKey aeadExpands hE
        rw [ByteArray.size_append, her, h1]
        omega

/-- Taking the `.start` transition to `.awaitResp` MEANS the peer is the node and
its initiation builder succeeded on exactly the emitted frame and kept state. -/
theorem initiate_sendInit {ss : Session} {sI : Sym} {frame : Control.Bytes}
    (h : initiate ss = (.awaitResp sI, .sendInit frame)) :
    ss.role = .node ∧
      mkTs2021Initiation ss.version ss.spriv ss.spub ss.epriv ss.epub ss.peerS
        = some (frame, sI) := by
  unfold initiate at h
  split at h
  · exact absurd h (by simp)
  · rename_i hrole
    refine ⟨hrole, ?_⟩
    split at h
    · exact absurd h (by simp)
    · rename_i p hMk
      obtain ⟨f, st⟩ := p
      simp only [Prod.mk.injEq, Phase.awaitResp.injEq, Out.sendInit.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hMk

/-- The ts2021 initiation builder is `noiseInitiation` on the fixed prologue and
empty payload, framed. -/
theorem mkTs2021Initiation_eq {version : Nat} {siPriv siPub eiPriv eiPub rsPub : ByteArray}
    {frame : Control.Bytes} {s : Sym}
    (h : mkTs2021Initiation version siPriv siPub eiPriv eiPub rsPub = some (frame, s)) :
    ∃ np, noiseInitiation (tsPrologue version) siPriv siPub eiPriv eiPub rsPub ByteArray.empty
            = some (np, s) ∧ frame = frameInitiation version (bytesOf np) := by
  unfold mkTs2021Initiation at h
  split at h
  · rename_i np s' hNI
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨np, hNI, rfl⟩
  · exact absurd h (by simp)

/-- Conversely, a successful Noise response step IS the framed response builder. -/
theorem mkTs2021ResponseSt_of {s0 s : Sym} {erPriv erPub eiPub siPub rp : ByteArray}
    (h : noiseResponse s0 erPriv erPub eiPub siPub ByteArray.empty = some (rp, s)) :
    mkTs2021ResponseSt s0 erPriv erPub eiPub siPub = some (frameResponse (bytesOf rp), s) := by
  unfold mkTs2021ResponseSt; rw [h]

set_option maxHeartbeats 2000000 in
/-- **THE DEPLOYED HANDSHAKE IS BYTE-EXACT AND BOTH ENDS AGREE.**

Whenever the node takes the `.start` transition and puts `initFrame` on the wire:

  * `initFrame` is the `messages.go` initiation layout —
    `[ver:u16BE][type=1][len:u16BE]` over a **96-byte** Noise message, so 101 B
    total — and the coordinator's answer is the response layout,
    `[type=2][len:u16BE]` over a **48-byte** Noise message, so 51 B total. (This
    is what lets the socket loop read each frame off the stream header-first,
    trusting the length field rather than a hard-coded size.)
  * feeding *that frame* to the coordinator's `.recvInit` transition drives the
    coordinator to `.up`, and feeding *the frame it answers with* to the node's
    `.recvResp` transition drives the node to `.up` — on the **same** 64-byte
    Noise `Split()` material `m`, the node holding `initiatorTx m` and the
    coordinator `responderTx m`, hence `node.send = coord.recv` and
    `node.recv = coord.send`.

This is the theorem the §2b residual note used to say could not be stated. It is
now proven, by `Control.Ts2021Transcript.readInitiation_noiseInitiation` /
`readResponse_noiseResponse` — the transcript coincidence — over the byte-exact
core. The two ends' key agreement is a **conclusion**, never a hypothesis.

The hypotheses, all explicit and all discharged on the wire:
* `aeadExpands` — the ChaCha20-Poly1305 ciphertext-expansion law
  (`|ct| = |pt| + 16`), a true AEAD property deliberately kept OUT of
  `Crypto.Assumptions` so callers see the dependency (see `Ts2021Transcript`);
* `hRoleC` — the answering peer is configured as the coordinator;
* `hPeerS` — the node knows the coordinator's static public key (`rs`), which is
  what Noise_IK means and what `GET /key` supplies;
* `hVer` — the announced protocol version fits the `uint16` header field;
* `bEi`/`bSi`/`bSr`/`bEr` — each public key is its scalar's base-point image
  (X25519 keygen). From these the FOUR Diffie-Hellman agreements are DERIVED via
  the existing `Crypto.Assumptions.x25519_dh_agree`; they are not assumed;
* `hei`/`hsi`/`her` — X25519 public keys are 32 bytes;
* `hRespOk` — **liveness only**: the coordinator's Noise response step returns a
  result rather than failing. It asserts nothing about *which* result, and
  nothing about agreement; the state it produces is existentially bound and the
  conclusion holds for whichever one it is. This cannot be discharged from the
  present axioms because `Crypto.x25519` is `Option`-valued and
  `x25519_dh_agree` states only that the two DH computations are EQUAL, never
  that either is `some` — there is no totality axiom for X25519 or for
  `chachaSeal`, and adding one would enlarge the trust surface to buy a liveness
  fact the running handshake already exhibits. -/
theorem handshake_refines
    {nodeSess coordSess : Session} {sI : Sym} {initFrame : Control.Bytes}
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
    (hStart : step nodeSess .fresh .start = (.awaitResp sI, .sendInit initFrame)) :
    ∃ (respFrame niNoise nrNoise : Control.Bytes) (m : ByteArray),
      -- the bytes on the wire are the `messages.go` layouts
      initFrame = frameInitiation nodeSess.version niNoise ∧ niNoise.length = 96 ∧
      respFrame = frameResponse nrNoise ∧ nrNoise.length = 48 ∧
      -- both ends reach `.up` on the two directional splits of ONE material
      step coordSess .fresh (.recvInit initFrame)
          = (.up (responderTx m), .sendResp respFrame) ∧
      step nodeSess (.awaitResp sI) (.recvResp respFrame)
          = (.up (initiatorTx m), .idle) ∧
      (initiatorTx m).send = (responderTx m).recv ∧
      (initiatorTx m).recv = (responderTx m).send := by
  obtain ⟨rp, sR, hNR⟩ := hRespOk
  -- 1. what the node's `.start` transition actually built
  replace hStart : initiate nodeSess = (Phase.awaitResp sI, Out.sendInit initFrame) := hStart
  obtain ⟨_, hMk⟩ := initiate_sendInit hStart
  obtain ⟨np, hNI, hFrame⟩ := mkTs2021Initiation_eq hMk
  rw [hPeerS] at hNI
  -- 2. the Noise messages are the 96/48 the length fields declare
  have hNPsize : np.size = 96 := by
    have := size_noiseInitiation aeadExpands hei hsi hNI; simpa using this
  have hRPsize : rp.size = 48 := by
    have := size_noiseResponse aeadExpands her hNR; simpa using this
  -- 3. the coordinator's read of the initiation IS the node's own transcript
  have hRead : readInitiation (tsPrologue nodeSess.version) coordSess.spriv coordSess.spub np
      = some (nodeSess.epub, nodeSess.spub, ByteArray.empty, sI) :=
    readInitiation_noiseInitiation aeadExpands hei hsi (dh_es bEi bSr) (dh_ss bSi bSr) hNI
  -- 4. the node's read of the response IS the coordinator's own final transcript
  have hReadR : readResponse sI nodeSess.epriv nodeSess.spriv rp = some (ByteArray.empty, sR) :=
    readResponse_noiseResponse her
      (Crypto.Assumptions.x25519_dh_agree _ _ _ _ bEi bEr)
      (Crypto.Assumptions.x25519_dh_agree _ _ _ _ bSi bEr) hNR
  refine ⟨frameResponse (bytesOf rp), bytesOf np, bytesOf rp, sR.material,
    hFrame, by rw [length_bytesOf, hNPsize], rfl, by rw [length_bytesOf, hRPsize], ?_, ?_,
    (tx_directions_agree _).1, (tx_directions_agree _).2⟩
  · -- the coordinator transition
    show respond coordSess initFrame = _
    rw [respond, hRoleC, hFrame,
        parseInitiation_frame _ hVer _ (by rw [length_bytesOf, hNPsize]; omega)]
    dsimp only
    rw [baOf_bytesOf, hRead]
    dsimp only
    rw [mkTs2021ResponseSt_of hNR]
  · -- the node transition
    show complete nodeSess sI (frameResponse (bytesOf rp)) = _
    rw [complete, parseResponse_frame _ (by rw [length_bytesOf, hRPsize]; omega)]
    dsimp only
    rw [baOf_bytesOf, hReadR]

end Ts2021

/-! ## §3  The sealed control channel — frame codec + AEAD

Post-handshake, a control message is AEAD-sealed under a directional transport
key and framed as a ts2021 control **record**: a 1-byte record tag then the
length-prefixed ciphertext (`controlbase` frames each post-handshake message with
a type byte and a length). The frame codec reuses `Control`'s length-prefixed
byte-string codec (`putBytes` / `getBytes`), so its round-trip chains from the
already-proven `getBytes_putBytes`. -/

/-- The record message type in the ts2021 framing (`controlbase` `msgTypeRecord`). -/
def recordTag : UInt8 := 3

/-- Frame a ciphertext: record tag, then the length-prefixed ciphertext bytes. -/
def encodeFrame (ct : Control.Bytes) : Control.Bytes := recordTag :: Control.putBytes ct

/-- Parse a control frame: require the record tag, then read the length-prefixed
ciphertext. -/
def parseFrame (bs : Control.Bytes) : Option Control.Bytes :=
  match bs with
  | [] => none
  | t :: rest => if t == recordTag then (Control.getBytes rest).map (·.1) else none

/-- **Frame round-trip.** Parsing an encoded frame recovers the ciphertext
exactly. -/
theorem frame_roundtrip (ct : Control.Bytes) : parseFrame (encodeFrame ct) = some ct := by
  unfold parseFrame encodeFrame
  simp only [beq_self_eq_true, if_true]
  rw [show Control.putBytes ct = Control.putBytes ct ++ [] from (List.append_nil _).symm,
      Control.getBytes_putBytes]
  simp

/-- The all-zero 12-byte AEAD nonce (the record counter starts at 0 under each
transport key; the counter is carried in the first bytes on the real wire). -/
def nonce0 : ByteArray := ⟨Array.replicate 12 (0 : UInt8)⟩

/-- **Seal** a control payload under a directional transport key and nonce, and
frame it. `none` only on a bad key/nonce size (the AEAD's contract). -/
def sealFrame (key nonce : ByteArray) (payload : Control.Bytes) : Option Control.Bytes :=
  match Crypto.chachaSeal key nonce ByteArray.empty (baOf payload) with
  | some ct => some (encodeFrame (bytesOf ct))
  | none    => none

/-- **Open** a control frame under a directional transport key and nonce.
`none` on a malformed frame OR an authentication failure (indistinguishable, as
the AEAD requires). -/
def openFrame (key nonce : ByteArray) (frame : Control.Bytes) : Option Control.Bytes :=
  match parseFrame frame with
  | some ct =>
    match Crypto.chachaOpen key nonce ByteArray.empty (baOf ct) with
    | some pt => some (bytesOf pt)
    | none    => none
  | none => none

/-- **The channel round-trip.** A payload sealed by one side under its send key
opens, on the other side under the matching receive key (equal by
`channel_established_keys_agree`), to *exactly* the same payload. This is the
control-plane analog of `Disco.disco_seal_open`: the bytes one end puts on the
wire are precisely what the other decodes. -/
theorem seal_open (sk rk nonce : ByteArray) (payload : Control.Bytes)
    (hk : sk = rk) {frame : Control.Bytes}
    (hs : sealFrame sk nonce payload = some frame) :
    openFrame rk nonce frame = some payload := by
  subst hk
  unfold sealFrame at hs
  cases hseal : Crypto.chachaSeal sk nonce ByteArray.empty (baOf payload) with
  | none => rw [hseal] at hs; simp at hs
  | some ct =>
    rw [hseal] at hs
    simp only [Option.some.injEq] at hs
    subst hs
    have hopen : Crypto.chachaOpen sk nonce ByteArray.empty ct = some (baOf payload) :=
      Crypto.Assumptions.chacha_open_seal_roundtrip sk nonce ByteArray.empty
        (baOf payload) ct hseal
    simp only [openFrame, frame_roundtrip, baOf_bytesOf, hopen, bytesOf_baOf]

/-! ## §4  Carrying the `Control` messages

The channel carries the coordination messages: `RegisterRequest` and
`MapRequest` node→server, `RegisterResponse` and `MapResponse` server→node.
Each has a byte-level codec (`Control`'s for the requests/response; a codec built
here for `MapResponse`), so a message sealed on one end decodes on the other. -/

/-! ### A `MapResponse` codec

`Control` fixes `MapResponse` but not its codec (its `full` case carries a whole
`NetMap`, which does have a codec). We add the missing codec: a tag byte then the
constructor payload, with an `Option` field codec for `PeerChange`. -/

/-- Optional-field codec: a presence byte then the value's encoding. -/
def putOpt {α} (e : α → Control.Bytes) : Option α → Control.Bytes
  | none   => [0]
  | some a => 1 :: e a

def getOpt {α} (d : Control.Bytes → Option (α × Control.Bytes)) :
    Control.Bytes → Option (Option α × Control.Bytes)
  | []        => none
  | b :: rest => if b == 0 then some (none, rest) else (d rest).map (fun p => (some p.1, p.2))

theorem getOpt_put {α} (e : α → Control.Bytes) (d : Control.Bytes → Option (α × Control.Bytes))
    (hrt : ∀ a t, d (e a ++ t) = some (a, t)) (o : Option α) (tail : Control.Bytes) :
    getOpt d (putOpt e o ++ tail) = some (o, tail) := by
  cases o with
  | none => simp [putOpt, getOpt]
  | some a => simp only [putOpt, getOpt, List.cons_append]; rw [if_neg (by decide), hrt]; rfl

/-- A `PeerChange` codec (the field-level peer delta). -/
def putPeerChange (c : Control.PeerChange) : Control.Bytes :=
  Control.putNat c.nodeID ++ putOpt Control.putBool c.online ++
  putOpt (Control.putSeq Control.putEndpoint) c.endpoints ++
  putOpt Control.putNodeKey c.key

def getPeerChange (bs : Control.Bytes) : Option (Control.PeerChange × Control.Bytes) := do
  let (nodeID, r) ← Control.getNat bs
  let (online, r) ← getOpt Control.getBool r
  let (endpoints, r) ← getOpt (Control.getSeq Control.getEndpoint) r
  let (key, r) ← getOpt Control.getNodeKey r
  some (⟨nodeID, online, endpoints, key⟩, r)

theorem getPeerChange_put (c : Control.PeerChange) (t : Control.Bytes) :
    getPeerChange (putPeerChange c ++ t) = some (c, t) := by
  obtain ⟨nodeID, online, endpoints, key⟩ := c
  simp [putPeerChange, getPeerChange, List.append_assoc, Control.getNat_putNat,
    getOpt_put Control.putBool Control.getBool Control.getBool_putBool,
    getOpt_put (Control.putSeq Control.putEndpoint) (Control.getSeq Control.getEndpoint)
      (Control.getSeq_putSeq Control.putEndpoint Control.getEndpoint Control.getEndpoint_put),
    getOpt_put Control.putNodeKey Control.getNodeKey Control.getNodeKey_put]

/-- The `MapResponse` codec: `full` (tag 0) carries a `NetMap`; `delta` (tag 1)
carries changed nodes, removed ids, and peer patches; `keepAlive` (tag 2) is bare. -/
def putMapResp : Control.MapResponse → Control.Bytes
  | .full nm => 0 :: Control.putNetMap nm
  | .delta changed removed patch =>
      1 :: (Control.putSeq Control.putNode changed ++ Control.putSeq Control.putNat removed ++
            Control.putSeq putPeerChange patch)
  | .keepAlive => [2]

def getMapResp (bs : Control.Bytes) : Option (Control.MapResponse × Control.Bytes) :=
  match bs with
  | [] => none
  | t :: rest =>
    if t == 0 then
      (Control.getNetMap rest).map (fun p => (.full p.1, p.2))
    else if t == 1 then do
      let (changed, r) ← Control.getSeq Control.getNode rest
      let (removed, r) ← Control.getSeq Control.getNat r
      let (patch, r) ← Control.getSeq getPeerChange r
      some (.delta changed removed patch, r)
    else if t == 2 then some (.keepAlive, rest)
    else none

theorem getMapResp_put (m : Control.MapResponse) (t : Control.Bytes) :
    getMapResp (putMapResp m ++ t) = some (m, t) := by
  cases m with
  | full nm =>
    simp only [putMapResp, getMapResp, List.cons_append]
    rw [if_pos (by decide)]
    rw [Control.getNetMap_put]; rfl
  | delta changed removed patch =>
    simp only [putMapResp, getMapResp, List.cons_append, List.append_assoc]
    rw [if_neg (by decide), if_pos (by decide)]
    simp [Control.getSeq_putSeq Control.putNode Control.getNode Control.getNode_put,
      Control.getSeq_putSeq Control.putNat Control.getNat Control.getNat_putNat,
      Control.getSeq_putSeq putPeerChange getPeerChange getPeerChange_put]
  | keepAlive =>
    simp only [putMapResp, getMapResp, List.cons_append, List.nil_append]
    rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]

/-! ### Typed message channel round-trips

Each seals a `Control` message through the channel and recovers it on the peer,
composing `seal_open` with the message codec's round-trip. The `hk : sk = rk`
hypothesis is the directional key agreement discharged by
`channel_established_keys_agree`. -/

/-- Seal a `RegisterRequest` (node→server). -/
def sealRegReq (key nonce : ByteArray) (q : Control.RegisterRequest) : Option Control.Bytes :=
  sealFrame key nonce (Control.putRegReq q)
/-- Open a control frame as a `RegisterRequest`. -/
def openRegReq (key nonce : ByteArray) (frame : Control.Bytes) : Option Control.RegisterRequest :=
  (openFrame key nonce frame).bind (fun bs => (Control.getRegReq bs).map (·.1))

/-- **`RegisterRequest` round-trips through the channel.** -/
theorem regReq_channel_roundtrip (sk rk nonce : ByteArray) (q : Control.RegisterRequest)
    (hk : sk = rk) {frame : Control.Bytes} (hs : sealRegReq sk nonce q = some frame) :
    openRegReq rk nonce frame = some q := by
  unfold sealRegReq at hs
  have hof := seal_open sk rk nonce (Control.putRegReq q) hk hs
  have hg : Control.getRegReq (Control.putRegReq q) = some (q, []) := by
    have := Control.getRegReq_put q []; rwa [List.append_nil] at this
  simp [openRegReq, hof, hg]

/-- Seal a `MapRequest` (node→server). -/
def sealMapReq (key nonce : ByteArray) (q : Control.MapRequest) : Option Control.Bytes :=
  sealFrame key nonce (Control.putMapReq q)
/-- Open a control frame as a `MapRequest`. -/
def openMapReq (key nonce : ByteArray) (frame : Control.Bytes) : Option Control.MapRequest :=
  (openFrame key nonce frame).bind (fun bs => (Control.getMapReq bs).map (·.1))

/-- **`MapRequest` round-trips through the channel.** -/
theorem mapReq_channel_roundtrip (sk rk nonce : ByteArray) (q : Control.MapRequest)
    (hk : sk = rk) {frame : Control.Bytes} (hs : sealMapReq sk nonce q = some frame) :
    openMapReq rk nonce frame = some q := by
  unfold sealMapReq at hs
  have hof := seal_open sk rk nonce (Control.putMapReq q) hk hs
  have hg : Control.getMapReq (Control.putMapReq q) = some (q, []) := by
    have := Control.getMapReq_put q []; rwa [List.append_nil] at this
  simp [openMapReq, hof, hg]

/-- Seal a `RegisterResponse` (server→node). -/
def sealRegResp (key nonce : ByteArray) (r : Control.RegisterResponse) : Option Control.Bytes :=
  sealFrame key nonce (Control.putRegResp r)
/-- Open a control frame as a `RegisterResponse`. -/
def openRegResp (key nonce : ByteArray) (frame : Control.Bytes) : Option Control.RegisterResponse :=
  (openFrame key nonce frame).bind (fun bs => (Control.getRegResp bs).map (·.1))

/-- **`RegisterResponse` round-trips through the channel.** -/
theorem regResp_channel_roundtrip (sk rk nonce : ByteArray) (r : Control.RegisterResponse)
    (hk : sk = rk) {frame : Control.Bytes} (hs : sealRegResp sk nonce r = some frame) :
    openRegResp rk nonce frame = some r := by
  unfold sealRegResp at hs
  have hof := seal_open sk rk nonce (Control.putRegResp r) hk hs
  have hg : Control.getRegResp (Control.putRegResp r) = some (r, []) := by
    have := Control.getRegResp_put r []; rwa [List.append_nil] at this
  simp [openRegResp, hof, hg]

/-- Seal a `MapResponse` (server→node). -/
def sealMapResp (key nonce : ByteArray) (m : Control.MapResponse) : Option Control.Bytes :=
  sealFrame key nonce (putMapResp m)
/-- Open a control frame as a `MapResponse`. -/
def openMapResp (key nonce : ByteArray) (frame : Control.Bytes) : Option Control.MapResponse :=
  (openFrame key nonce frame).bind (fun bs => (getMapResp bs).map (·.1))

/-- **`MapResponse` round-trips through the channel** (the netmap the server
streams to the node arrives intact). -/
theorem mapResp_channel_roundtrip (sk rk nonce : ByteArray) (m : Control.MapResponse)
    (hk : sk = rk) {frame : Control.Bytes} (hs : sealMapResp sk nonce m = some frame) :
    openMapResp rk nonce frame = some m := by
  unfold sealMapResp at hs
  have hof := seal_open sk rk nonce (putMapResp m) hk hs
  have hg : getMapResp (putMapResp m) = some (m, []) := by
    have := getMapResp_put m []; rwa [List.append_nil] at this
  simp [openMapResp, hof, hg]

/-! ## §5  Authenticity — the wire anti-spoof

The confidentiality/authenticity core, the ts2021 analog of
`Disco.disco_authpongframe_genuine`: a control frame that *opens* under a
transport key was genuinely **sealed** under that key. Composed with the
handshake, only a party that completed the Noise IK exchange holding the machine
key ever derives that transport key — so no party lacking it can forge a frame
this channel accepts. -/

/-- **A frame that opens was genuinely sealed (anti-spoof).** If `openFrame`
under a transport key returns a payload, then the frame parsed to some ciphertext
that opened under the key AND was genuinely sealed under it — the functional
shadow of AEAD authenticity (INT-CTXT), via `chacha_open_authentic`. No party
lacking the transport key can fabricate a frame this accepts. -/
theorem channel_frame_genuine (key nonce : ByteArray) (frame payload : Control.Bytes)
    (h : openFrame key nonce frame = some payload) :
    ∃ ct,
      parseFrame frame = some ct ∧
      Crypto.chachaOpen key nonce ByteArray.empty (baOf ct) = some (baOf payload) ∧
      Crypto.chachaSeal key nonce ByteArray.empty (baOf payload) = some (baOf ct) := by
  unfold openFrame at h
  split at h
  · rename_i ct heq
    split at h
    · rename_i pt heq2
      simp only [Option.some.injEq] at h
      have hpt : baOf payload = pt := by rw [← h, baOf_bytesOf]
      refine ⟨ct, heq, ?_, ?_⟩
      · rw [hpt]; exact heq2
      · rw [hpt]
        exact Crypto.Assumptions.chacha_open_authentic key nonce ByteArray.empty (baOf ct) pt heq2
    · simp at h
  · simp at h

/-- **A control message the node accepts was genuinely sealed by the server.**
The typed anti-spoof: if `openRegResp` (server→node) yields a response, the frame
carried a ciphertext genuinely sealed under the node's receive transport key —
which, by the handshake, only the coordination server holding the derived key
could produce. A forged `RegisterResponse` is never accepted. -/
theorem regResp_frame_genuine (key nonce : ByteArray) (frame : Control.Bytes)
    (r : Control.RegisterResponse) (h : openRegResp key nonce frame = some r) :
    ∃ ct payload tail,
      parseFrame frame = some ct ∧
      Crypto.chachaOpen key nonce ByteArray.empty (baOf ct) = some (baOf payload) ∧
      Crypto.chachaSeal key nonce ByteArray.empty (baOf payload) = some (baOf ct) ∧
      Control.getRegResp payload = some (r, tail) := by
  unfold openRegResp at h
  cases ho : openFrame key nonce frame with
  | none => rw [ho] at h; simp at h
  | some payload =>
    rw [ho] at h
    simp only [Option.bind_some, Option.map_eq_some_iff] at h
    obtain ⟨pr, hgr, hpr⟩ := h
    obtain ⟨ct, hpf, hopen, hseal⟩ := channel_frame_genuine key nonce frame payload ho
    obtain ⟨v, tail⟩ := pr
    refine ⟨ct, payload, tail, hpf, hopen, hseal, ?_⟩
    simp only at hpr
    subst hpr
    exact hgr

/-! ## §6  Handshake-time machine-key authentication (reused)

The initiation seals the node's machine static key inside the first Noise
message (§5.4.2 shape); the coordination server, having derived the same step key
and transcript, recovers it — and no forged machine key is ever accepted. Reuses
`Wireguard.Noise.sealStatic` and its authenticity lemmas directly. -/

/-- Seal the node's machine static public key into the initiation
(`encrypted_static`), under a key derived from the chaining key and the running
transcript hash. Reuses `Wireguard.Noise.sealStatic`. -/
def sealMachineKey (k hash mpub : ByteArray) : Option ByteArray :=
  Noise.sealStatic k hash mpub

/-- **The coordination server recovers the node's genuine machine key.** With the
same derived key and transcript, opening `encrypted_static` yields exactly the
node's machine public key — the machine-key identity is authenticated to the
server. Reuses `Wireguard.Noise.wg_static_key_authenticated`. -/
theorem coord_recovers_machine_key (k hash mpub ct : ByteArray)
    (hseal : sealMachineKey k hash mpub = some ct) :
    Crypto.chachaOpen k Noise.nonce0 hash ct = some mpub :=
  Noise.wg_static_key_authenticated k hash mpub ct hseal

/-- **No forged machine key is accepted (handshake anti-spoof).** The only
ciphertext that opens to a given machine key under this step key/transcript is
the one the genuine node sealed — AEAD forgery-resistance. A server that admits
an initiation only on `chachaOpen … = some mpub` therefore only ever admits a
node that actually holds the shared key material bound to that machine key.
Reuses `Wireguard.Noise.wg_static_key_unforgeable`. -/
theorem machine_key_unforgeable (k hash mpub ct : ByteArray)
    (hopen : Crypto.chachaOpen k Noise.nonce0 hash ct = some mpub) :
    Crypto.chachaSeal k Noise.nonce0 hash mpub = some ct :=
  Noise.wg_static_key_unforgeable k hash mpub ct hopen

/-! ## §6b  The byte-exact ts2021 channel, end to end

The §2b FSM's keys carrying §3–§5's sealed records: what the byte-exact
handshake derives is exactly what the proven message round-trips consume. -/

namespace Ts2021

open Control.Ts2021Wire

/-- **End-to-end: a control message sealed by the node opens at the coordinator**,
over the byte-exact handshake. Chains `keys_agree_of_material` into §4's proven
`mapReq_channel_roundtrip`: whatever the node seals under the keys THIS FSM
derived, the coordinator — completing on a transcript with the same material —
decodes to exactly the message that was sent. -/
theorem mapReq_over_ts2021 (txN txC : TxKeys) (m : ByteArray) (nonce : ByteArray)
    (q : Control.MapRequest)
    (hN : txN = initiatorTx m) (hC : txC = responderTx m)
    {frame : Control.Bytes} (hs : sealMapReq txN.send nonce q = some frame) :
    openMapReq txC.recv nonce frame = some q :=
  mapReq_channel_roundtrip txN.send txC.recv nonce q
    (keys_agree_of_material txN txC m hN hC).1 hs

/-- **End-to-end the other way: the netmap the coordinator streams arrives intact.** -/
theorem mapResp_over_ts2021 (txN txC : TxKeys) (m : ByteArray) (nonce : ByteArray)
    (r : Control.MapResponse)
    (hN : txN = initiatorTx m) (hC : txC = responderTx m)
    {frame : Control.Bytes} (hs : sealMapResp txC.send nonce r = some frame) :
    openMapResp txN.recv nonce frame = some r :=
  mapResp_channel_roundtrip txC.send txN.recv nonce r
    (keys_agree_of_material txN txC m hN hC).2.symm hs

end Ts2021

/-! ## §7  Residual (named boundary)

What is proven here is the ts2021 **security core**: the Noise-IK handshake as a
transition system with key agreement (`handshake_keys_agree`), the sealed
control-frame round-trip carrying every `Control` message
(`{regReq,mapReq,regResp,mapResp}_channel_roundtrip`), and authenticity
(`channel_frame_genuine`, `regResp_frame_genuine`, `machine_key_unforgeable`) —
sorry-free, over the reused verified `Wireguard.Noise` machinery and the `Crypto`
assumptions.

The **byte-exact wire** residual that stood here is CLOSED by §2b + §6b: the
handshake FSM now speaks plain `Noise_IK` over the real `controlbase` frames
(`Control.Ts2021Core`, cross-verified line-by-line against the public
`control/controlbase/handshake.go` and `messages.go`), the emitted initiation is
the 101-byte layout and the response the 51-byte layout, and the record layer is
`Control.Ts2021Wire`'s proven `[type][u16 BE len][payload]`.

The transcript-coincidence statement this section used to carry as residual (a)
— "not yet a Lean theorem, for want of a `ByteArray` `++`/`extract` algebra" —
is CLOSED and that wording is retracted: it is
`Control.Ts2021Transcript.transcripts_coincide`, consumed at the FSM level by
§2c's `Ts2021.handshake_refines`, and the algebra was mostly Lean 4.30 core's
already. See the corrected note at the end of §2b.

What remains residual is **live-tailnet interop**: the `control/controlhttp` `/ts2021` `Upgrade` dance
over a real HTTP connection (host glue in the dataplane) and a cross-check
against a real stock client, which additionally needs a tailnet **auth key**
(operator-provided). Those are integration plumbing over this proven core, not
new proof obligations. -/

/-! ## §8  Axiom ledger — ASSERTED, not printed

Was `#print axioms` (info stream, cannot fail a build); now `#assert_axioms`
(see `Hygiene`), which throws on any dependency outside the declared set.

★ 13 of the 21 theorems here declare `cryptoSeam`: they are CONDITIONAL on the
`Crypto.Assumptions` axioms that shadow the `@[extern]` HACL*/EverCrypt
primitives (`chacha_open_seal_roundtrip`, `chacha_open_authentic`,
`x25519_dh_agree`). Those are discharged OUTSIDE Lean, by the HACL* F* proof —
so `seal_open`, `machine_key_unforgeable` and the TS2021 refinement hold exactly
as far as the C does. The remaining 8 are kernel-checked outright. -/

/-! ## §8  Axiom ledger -/

#assert_axioms handshake_keys_agree ⊆ [stdAxioms, cryptoSeam]
#assert_axioms channel_up_needs_handshake ⊆ [stdAxioms]
#assert_axioms channel_established_keys_agree ⊆ [stdAxioms, cryptoSeam]
#assert_axioms seal_open ⊆ [stdAxioms, cryptoSeam]
#assert_axioms regReq_channel_roundtrip ⊆ [stdAxioms, cryptoSeam]
#assert_axioms mapReq_channel_roundtrip ⊆ [stdAxioms, cryptoSeam]
#assert_axioms regResp_channel_roundtrip ⊆ [stdAxioms, cryptoSeam]
#assert_axioms mapResp_channel_roundtrip ⊆ [stdAxioms, cryptoSeam]
#assert_axioms channel_frame_genuine ⊆ [stdAxioms, cryptoSeam]
#assert_axioms regResp_frame_genuine ⊆ [stdAxioms, cryptoSeam]
#assert_axioms machine_key_unforgeable ⊆ [stdAxioms, cryptoSeam]
#assert_axioms Ts2021.no_up_from_start ⊆ [stdAxioms]
#assert_axioms Ts2021.up_needs_handshake ⊆ [stdAxioms]
#assert_axioms Ts2021.node_up_material ⊆ [stdAxioms]
#assert_axioms Ts2021.coord_up_material ⊆ [stdAxioms]
#assert_axioms Ts2021.keys_agree_of_material ⊆ [stdAxioms]
#assert_axioms Ts2021.size_noiseInitiation ⊆ [stdAxioms]
#assert_axioms Ts2021.size_noiseResponse ⊆ [stdAxioms]
#assert_axioms Ts2021.handshake_refines ⊆ [stdAxioms, cryptoSeam]
#assert_axioms Ts2021.mapReq_over_ts2021 ⊆ [stdAxioms, cryptoSeam]
#assert_axioms Ts2021.mapResp_over_ts2021 ⊆ [stdAxioms, cryptoSeam]

end Control.Channel
