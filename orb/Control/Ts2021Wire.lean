import Control.Ts2021Core
import Control.Channel
/-!
# Control.Ts2021Wire — the byte-exact ts2021 `controlbase` record framing

`Control.Channel` proves the ts2021 Noise-IK security core (handshake key
agreement, the sealed control-frame round-trip carrying every message,
authenticity) over a *drorb-native* frame codec — `encodeFrame` frames a
ciphertext as `recordTag :: putBytes ct`, where `putBytes` is drorb's
uvarint-length-prefixed byte string.

The public `control/controlbase` wire is more specific. As the control-plane
spec states, each post-handshake message is a **record** with a fixed 3-byte
header

    [ type : 1 byte ] [ length : uint16 big-endian ]

then the payload, and the handshake prologue carries the protocol version as a
big-endian `uint16`. This module pins that byte-exact framing — the residual
named in `Control/Channel.lean §7` ("the byte-exact `controlbase` header
offsets") — with proven round-trips, composed with the SAME real audited AEAD
(`Crypto.chachaSeal` / `chachaOpen`, EverCrypt ChaCha20-Poly1305) the channel
already uses.

It ADDS a codec. It changes no definition or proof in `Control`,
`Control.Channel`, `Control.Acl`, or `Control.Derp`; those theorems stay exactly
as proven and this module composes on top of them.

## Scope / honesty boundary

What is byte-exact and proven here is the **record framing** (`[type][u16 BE
len][payload]`) and the **version prologue** (`u16 BE`), which the spec fixes.
The full byte layout of the *handshake* initiation/response messages
(ephemeral ‖ encrypted-static offsets, the transcript-hash binding) is a wider
`controlbase` detail not fixed by the record framing and is NOT claimed
byte-exact here — it remains the named integration residual, to pin against a
running tailnet. The three message TYPE tags (`initiation`/`response`/`record`)
are named as the spec fixes them.
-/

namespace Control.Ts2021Wire

open Control (Bytes)
open Control.Channel (bytesOf baOf bytesOf_baOf baOf_bytesOf)

/-! ## §0-§1  Message type tags and `uint16` big-endian — see `Control.Ts2021Core`

The `controlbase` message type tags (`msgTypeInitiation`/`Response`/`Error`/
`Record`) and the big-endian `uint16` codec (`putU16BE`/`getU16BE`,
`getU16BE_putU16BE`) are defined in `Control.Ts2021Core`, in THIS namespace, so
every name below resolves unchanged. They were hoisted there because
`Control.Channel`'s handshake FSM — which sits below this module — calls the
byte-exact handshake builders that use them. One definitional home, no copy.
-/

/-! ## §2  The version prologue

`controlbase` binds the protocol version into the handshake prologue as a
big-endian `uint16`. -/

def protocolVersion : Nat := 1
def putVersion : Bytes := putU16BE protocolVersion
def getVersion (bs : Bytes) : Option (Nat × Bytes) := getU16BE bs

theorem version_roundtrip (t : Bytes) :
    getVersion (putVersion ++ t) = some (protocolVersion, t) :=
  getU16BE_putU16BE protocolVersion (by decide) t

/-! ## §3  The record frame — `[type : 1B][length : u16 BE][payload]`

The byte-exact `controlbase` post-handshake record. -/

/-- Frame a payload as a `controlbase` record: the record type byte, then the
big-endian `uint16` length, then the payload bytes. -/
def encodeRecord (payload : Bytes) : Bytes :=
  msgTypeRecord :: (putU16BE payload.length ++ payload)

/-- Parse one `controlbase` record off the front of a byte stream: require the
record type byte, read the big-endian `uint16` length, then split off exactly
that many payload bytes (returns the payload and the remaining stream). -/
def parseRecord (bs : Bytes) : Option (Bytes × Bytes) :=
  match bs with
  | []       => none
  | t :: rest =>
    if t == msgTypeRecord then
      match getU16BE rest with
      | some (len, body) =>
        if len ≤ body.length then some (body.take len, body.drop len) else none
      | none => none
    else none

/-- **Record round-trip.** A framed payload (whose length fits a `uint16`)
parses back to exactly that payload, with an empty remaining stream. -/
theorem parseRecord_encodeRecord (payload : Bytes) (h : payload.length < 65536) :
    parseRecord (encodeRecord payload) = some (payload, []) := by
  simp only [encodeRecord, parseRecord, beq_self_eq_true, if_true]
  rw [getU16BE_putU16BE payload.length h payload]
  simp only [Nat.le_refl, if_true, List.take_length, List.drop_length]

/-! ## §4  Sealing control messages into records (real EverCrypt AEAD)

The same AEAD the `Control.Channel` seal/open uses — `Crypto.chachaSeal` /
`chachaOpen`, `@[extern]`-bound to EverCrypt ChaCha20-Poly1305 — now under the
byte-exact record framing. The all-zero AEAD nonce mirrors `Control.Channel`
(§3): the per-key record counter starts at 0. -/

def nonce0 : ByteArray := Control.Channel.nonce0

/-- Seal a payload under a directional transport key and frame it as a record. -/
def sealRecord (key nonce : ByteArray) (payload : Bytes) : Option Bytes :=
  match Crypto.chachaSeal key nonce ByteArray.empty (baOf payload) with
  | some ct => some (encodeRecord (bytesOf ct))
  | none    => none

/-- Open a `controlbase` record under a directional transport key. `none` on a
malformed record OR an authentication failure (indistinguishable, per AEAD). -/
def openRecord (key nonce : ByteArray) (frame : Bytes) : Option Bytes :=
  match parseRecord frame with
  | some p =>
    match Crypto.chachaOpen key nonce ByteArray.empty (baOf p.1) with
    | some pt => some (bytesOf pt)
    | none    => none
  | none => none

/-- **The record channel round-trip.** A payload sealed by one side under its
send key opens, on the other side under the matching receive key (equal by
`Control.Channel.channel_established_keys_agree`), to *exactly* the same payload
— now over the byte-exact `controlbase` record framing. The side condition
`hlen` is that the sealed ciphertext fits a `uint16` length (records are
length-bounded on the wire); the AEAD round-trip itself is
`Crypto.Assumptions.chacha_open_seal_roundtrip`, the same assumption
`Control.Channel.seal_open` rests on. -/
theorem record_seal_open (sk rk nonce : ByteArray) (payload : Bytes)
    (hk : sk = rk) {frame : Bytes}
    (hs : sealRecord sk nonce payload = some frame)
    (hlen : ∀ ct, Crypto.chachaSeal sk nonce ByteArray.empty (baOf payload) = some ct →
              (bytesOf ct).length < 65536) :
    openRecord rk nonce frame = some payload := by
  subst hk
  unfold sealRecord at hs
  cases hseal : Crypto.chachaSeal sk nonce ByteArray.empty (baOf payload) with
  | none => rw [hseal] at hs; simp at hs
  | some ct =>
    rw [hseal] at hs
    simp only [Option.some.injEq] at hs
    subst hs
    have hb : (bytesOf ct).length < 65536 := hlen ct hseal
    have hopen : Crypto.chachaOpen sk nonce ByteArray.empty ct = some (baOf payload) :=
      Crypto.Assumptions.chacha_open_seal_roundtrip sk nonce ByteArray.empty (baOf payload) ct hseal
    unfold openRecord
    rw [parseRecord_encodeRecord (bytesOf ct) hb]
    simp only [baOf_bytesOf, hopen, bytesOf_baOf]

/-! ## §5  Authenticity — a record that opens was genuinely sealed

The byte-exact analog of `Control.Channel.channel_frame_genuine`: a record that
`openRecord` accepts carried a ciphertext that opened under the transport key
AND was genuinely sealed under it (AEAD INT-CTXT, via `chacha_open_authentic`).
Composed with the handshake, only a party that completed the Noise-IK exchange
holding the machine key derives that key — so no party lacking it can forge a
record this channel accepts. -/
theorem record_genuine (key nonce : ByteArray) (frame payload : Bytes)
    (h : openRecord key nonce frame = some payload) :
    ∃ ct rest,
      parseRecord frame = some (ct, rest) ∧
      Crypto.chachaOpen key nonce ByteArray.empty (baOf ct) = some (baOf payload) ∧
      Crypto.chachaSeal key nonce ByteArray.empty (baOf payload) = some (baOf ct) := by
  unfold openRecord at h
  split at h
  · rename_i p heq
    obtain ⟨ct, rest⟩ := p
    split at h
    · rename_i pt heq2
      simp only [Option.some.injEq] at h
      have hpt : baOf payload = pt := by rw [← h, baOf_bytesOf]
      refine ⟨ct, rest, heq, ?_, ?_⟩
      · rw [hpt]; exact heq2
      · rw [hpt]
        exact Crypto.Assumptions.chacha_open_authentic key nonce ByteArray.empty (baOf ct) pt heq2
    · simp at h
  · simp at h

/-! ## §6  A typed message through the exact record framing

The headline: the coordinator's `MapResponse` — the netmap it streams to a node
(peers, the compiled `packetFilter`, the DERPMap, MagicDNS) — round-trips
through the byte-exact `controlbase` record, reusing the proven
`Control.Channel` `MapResponse` byte codec (`putMapResp` / `getMapResp`,
round-trip `getMapResp_put`) inside the exact frame. -/

def sealMapRespRecord (key nonce : ByteArray) (m : Control.MapResponse) : Option Bytes :=
  sealRecord key nonce (Control.Channel.putMapResp m)

def openMapRespRecord (key nonce : ByteArray) (frame : Bytes) : Option Control.MapResponse :=
  (openRecord key nonce frame).bind (fun bs => (Control.Channel.getMapResp bs).map (·.1))

/-- **`MapResponse` round-trips through the byte-exact record framing.** -/
theorem mapResp_record_roundtrip (sk rk nonce : ByteArray) (m : Control.MapResponse)
    (hk : sk = rk) {frame : Bytes}
    (hs : sealMapRespRecord sk nonce m = some frame)
    (hlen : ∀ ct, Crypto.chachaSeal sk nonce ByteArray.empty (baOf (Control.Channel.putMapResp m))
              = some ct → (bytesOf ct).length < 65536) :
    openMapRespRecord rk nonce frame = some m := by
  unfold sealMapRespRecord at hs
  have hof := record_seal_open sk rk nonce (Control.Channel.putMapResp m) hk hs hlen
  have hg : Control.Channel.getMapResp (Control.Channel.putMapResp m) = some (m, []) := by
    have := Control.Channel.getMapResp_put m []; rwa [List.append_nil] at this
  simp only [openMapRespRecord, hof, Option.bind_some, hg, Option.map_some]

/-! ## §7  Executable sanity — the framing is really the u16-BE record

A ground demonstration (no proof content; a build-time cross-check that the
definitions compute the byte-exact header the spec fixes). For a 300-byte
payload the record header is `[4][0x01][0x2C]` = type 4 (record), length 0x012C = 300. -/

/-- The byte-exact record header for a payload of length `n` (< 65536). -/
def recordHeader (n : Nat) : Bytes := msgTypeRecord :: putU16BE n

-- header for a 300-byte payload: type=4 (record), len hi=1, len lo=44 (0x012C = 300)
#eval recordHeader 300                                 -- expect #[4, 1, 44]
-- round-trip on a sample payload
#eval (parseRecord (encodeRecord [10, 20, 30, 40, 50])).map (·.1)  -- expect some [10,20,30,40,50]
-- version prologue is u16 BE = 0x0001
#eval putVersion                                       -- expect [0, 1]

/-! ## §A  The byte-exact Noise_IK handshake — `Control.Ts2021Core`

The byte-exact `Noise_IK_25519_ChaChaPoly_BLAKE2s` handshake (the Noise
`SymmetricState`, `noiseInitiation`/`readInitiation`/`noiseResponse`/
`readResponse`, the 101-byte initiation and 51-byte response frames, and the
ts2021 specializations `mkTs2021Initiation`/`mkTs2021Response`) lives in
`Control.Ts2021Core`, in THIS namespace — `Control.Ts2021Kat` and every other
reference is unchanged.

It was hoisted BELOW `Control.Channel` for one reason: `Control.Channel`'s
handshake FSM now **calls** it (`Control.Channel.Ts2021.step`), so the live
control channel runs the byte-exact transcript rather than the WireGuard
IKpsk2-with-zero-PSK reuse. Since this module sits above `Control.Channel`
(it reuses the channel's `MapResponse` codec), the shared core had to move down.
There is exactly ONE implementation of the handshake: the one the noise-c KAT
(`control-ts2021-kat`) validates is the one the FSM runs.
-/

/-! ## §8  Axiom ledger -/

#print axioms getU16BE_putU16BE
#print axioms version_roundtrip
#print axioms parseRecord_encodeRecord
#print axioms record_seal_open
#print axioms record_genuine
#print axioms mapResp_record_roundtrip
#print axioms parseInitiation_frame
#print axioms parseResponse_frame

end Control.Ts2021Wire
