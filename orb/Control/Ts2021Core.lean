import Control
import Wireguard
import Crypto
/-!
# Control.Ts2021Core — the byte-exact `Noise_IK_25519_ChaChaPoly_BLAKE2s` core

This module is the **single definitional home** of the byte-exact ts2021
handshake: the Noise `SymmetricState`, the `Noise_IK` message cores, and the
`controlbase` handshake frames (initiation 101 B / response 51 B).

It exists as its own module purely for the *import order*. The byte-exact core
was originally authored inside `Control.Ts2021Wire`, which sits **above**
`Control.Channel` (it reuses the channel's `MapResponse` codec). But
`Control.Channel`'s handshake FSM has to **call** the byte-exact core — that is
the whole point of the ts2021 channel — so the core is hoisted here, *below*
`Control.Channel`, and both the channel FSM and `Control.Ts2021Wire` use it.
The declarations keep their original `Control.Ts2021Wire` namespace, so every
downstream reference (`Control.Ts2021Kat`, the record layer) is unchanged: there
is exactly ONE implementation of the handshake, and the KAT that validates it
validates the very code the live FSM runs.

Cross-verified against the public source (`github.com/tailscale/tailscale`,
BSD-3; fetched, cited file:line):

* `control/controlbase/handshake.go`
  * `protocolName = "Noise_IK_25519_ChaChaPoly_BLAKE2s"` → hash = BLAKE2s
  * `protocolVersionPrefix = "Tailscale Control Protocol v"`
  * `protocolVersionPrologue(v) = prefix ‖ strconv.AppendUint(v, 10)` (decimal
    ASCII — NOT a u16)
  * initiator order: `Initialize`; `MixHash(prologue)`; `MixHash(controlKey)`;
    `MixHash(machineEphemeralPub)`; `MixDH(machineEphemeral, controlKey)`;
    `EncryptAndHash(machineKeyPub)`; `MixDH(machineKey, controlKey)`;
    `EncryptAndHash(nil)`
  * responder order: the same first eight steps with `DecryptAndHash`, then
    `MixHash(controlEphemeralPub)`; `MixDH(controlEphemeral, machineEphemeralPub)`;
    `MixDH(controlEphemeral, machineKey)`; `EncryptAndHash(nil)`
  * `Split()` → `c1, c2`; client `tx = c1, rx = c2`; server `tx = c2, rx = c1`
    (exactly `Control.Channel.initiatorTx` / `responderTx` over the 64-byte
    `k1 ‖ k2` material)
* `control/controlbase/messages.go`
  * L7 `msgTypeInitiation = 1`, L9 `msgTypeResponse = 2`, L12 `msgTypeError = 3`,
    L14 `msgTypeRecord = 4`; L17 `headerLen = 3`, L19 `initiationHeaderLen = 5`
  * L22 `initiationMessage` (101 B): `[0:2]` Version u16BE · `[2]` Type=1 ·
    `[3:5]` Length u16BE (=96) · `[5:37]` EphemeralPub 32 · `[37:85]` MachinePub
    encrypted 48 · `[85:101]` Tag 16
  * L47 `responseMessage` (51 B): `[0]` Type=2 · `[1:3]` Length u16BE (=48) ·
    `[3:35]` EphemeralPub 32 · `[35:51]` Tag 16

Primitives: X25519 (`Crypto.x25519`, drorb-verified), ChaCha20-Poly1305
(`Crypto.chachaSeal`/`chachaOpen`, EverCrypt), BLAKE2s (`Wireguard.Blake2s`, the
pure-Lean RFC 7693 hash). The Noise HKDF is BLAKE2s-HMAC
(`Wireguard.Noise.kdf2`, exactly Noise's 2-output HKDF). No openssl.
-/

/-! ## §0  Byte-view helpers

`Control.Channel`'s adapters between `ByteArray` (what the AEAD speaks) and
`Control.Bytes = List UInt8` (what the codec algebra speaks). They live here,
in the lowest module, because the byte-exact frame builders below need them and
`Control.Channel` needs those builders. They keep their `Control.Channel`
namespace so every existing reference is unchanged. -/

namespace Control.Channel

/-- `List UInt8` view of a `ByteArray` (its backing array as a list). -/
def bytesOf (b : ByteArray) : Control.Bytes := b.data.toList

/-- Repack a byte list into a `ByteArray`. -/
def baOf (l : Control.Bytes) : ByteArray := ⟨l.toArray⟩

@[simp] theorem baOf_bytesOf (b : ByteArray) : baOf (bytesOf b) = b := by
  show (ByteArray.mk b.data.toList.toArray) = b
  simp

@[simp] theorem bytesOf_baOf (l : Control.Bytes) : bytesOf (baOf l) = l := by
  show (ByteArray.mk l.toArray).data.toList = l
  simp

end Control.Channel

namespace Control.Ts2021Wire

open Control (Bytes)
open Control.Channel (bytesOf baOf bytesOf_baOf baOf_bytesOf)

/-! ## §1  `controlbase` message type tags

The three record types on the ts2021 wire (`messages.go` L7-L14). Post-handshake
control messages all ride under `msgTypeRecord`; the two handshake messages use
the initiation / response tags. -/

def msgTypeInitiation : UInt8 := 1
def msgTypeResponse   : UInt8 := 2
def msgTypeError      : UInt8 := 3
def msgTypeRecord     : UInt8 := 4

/-! ## §2  `uint16` big-endian

The record length, the handshake payload length and the initiation's version
field are all big-endian `uint16`. Two bytes, most-significant first. -/

/-- Encode `n` as a big-endian `uint16` (high byte, low byte). For `n < 65536`
this is exact; larger `n` is truncated mod 65536 (records are length-bounded on
the wire, so the round-trip lemma carries that side condition). -/
def putU16BE (n : Nat) : Bytes := [UInt8.ofNat (n / 256), UInt8.ofNat (n % 256)]

/-- Decode a leading big-endian `uint16`, returning the value and the tail. -/
def getU16BE : Bytes → Option (Nat × Bytes)
  | hi :: lo :: rest => some (hi.toNat * 256 + lo.toNat, rest)
  | _ => none

theorem getU16BE_putU16BE (n : Nat) (h : n < 65536) (t : Bytes) :
    getU16BE (putU16BE n ++ t) = some (n, t) := by
  simp only [putU16BE, List.cons_append, List.nil_append, getU16BE]
  rw [UInt8.toNat_ofNat_of_lt' (show n / 256 < 256 by omega),
      UInt8.toNat_ofNat_of_lt' (show n % 256 < 256 by omega)]
  have hn : n / 256 * 256 + n % 256 = n := by omega
  rw [hn]

/-! ## §3  The Noise symmetric state

`Noise_IK_25519_ChaChaPoly_BLAKE2s`, matching `handshake.go`'s `symmetricState`. -/

/-- ChaChaPoly nonce for Noise counter `n`: 32 zero bits ‖ 64-bit **little-endian**
`n` (RFC 7539 / Noise). Every ts2021 handshake AEAD op runs at `n = 0` (each
`MixKey` resets the counter), so in practice this is the 12-zero nonce; the
general form keeps the model faithful.

★ **HANDSHAKE ONLY.** The post-handshake transport *record* layer uses a
**big-endian** counter — `recordNonce`, below. Never hand this to
`Control.Channel.sealFrame` / `openFrame`. -/
def noiseNonce (n : Nat) : ByteArray :=
  ⟨(#[0,0,0,0] : Array UInt8) ++
    ((List.range 8).map (fun i => UInt8.ofNat (n / 2 ^ (8 * i) % 256))).toArray⟩

/-! ### The two nonce encodings

★ ts2021 uses **two different counter encodings** and they are not
interchangeable:

* the **handshake** AEAD ops use the Noise/RFC-7539 nonce — 4 zero bytes ‖
  64-bit **little-endian** counter (`noiseNonce`);
* the post-handshake **transport record** layer uses `controlbase`'s nonce —
  4 zero bytes ‖ 64-bit **big-endian** counter (`recordNonce`).

They coincide at counter 0 (`recordNonce_zero_eq_noiseNonce_zero`) and diverge
from counter 1 on (`recordNonce_ne_noiseNonce`), so a record layer wired to the
handshake nonce interoperates for exactly one frame and then fails
authentication on every subsequent one. The names are deliberately distinct so
the wrong one cannot be selected by accident. -/

/-- One byte of `n` by weight: the byte of value `2 ^ (8 * i)`. The *order* in
which eight of these are laid down is the whole BE/LE difference below. -/
def ctrByte (n i : Nat) : UInt8 := UInt8.ofNat (n / 2 ^ (8 * i) % 256)

/-- ChaChaPoly nonce for the ts2021 **transport record** counter `n`:
4 zero bytes ‖ 64-bit **big-endian** `n`.

This is `controlbase`'s `type nonce [chp.NonceSize]byte`
(github.com/tailscale/tailscale, BSD-3, `control/controlbase/conn.go`, lines
385-396 at `main`):

```go
type nonce [chp.NonceSize]byte

func (n *nonce) Valid() bool {
	return binary.BigEndian.Uint32(n[:4]) == 0 && binary.BigEndian.Uint64(n[4:]) != invalidNonce
}

func (n *nonce) Increment() {
	if !n.Valid() {
		panic("increment of invalid nonce")
	}
	binary.BigEndian.PutUint64(n[4:], 1+binary.BigEndian.Uint64(n[4:]))
}
```

so bytes 0..3 are zero and bytes 4..11 are the counter **big-endian**. That whole
12-byte array is what the record AEAD receives — `conn.go` `encryptLocked`
(lines 162-175): `ret := c.tx.cipher.Seal(buf[:headerLen], c.tx.nonce[:], plaintext, nil)`
then `c.tx.nonce.Increment()`; and the read path (lines 142-147):
`c.rx.plaintext, err = c.rx.cipher.Open(ciphertext[:0], c.rx.nonce[:], ciphertext, nil)`
then `c.rx.nonce.Increment()`. The counter starts at 0 under each transport key
(Go zero value), is per-direction, and the AEAD runs with **no** additional
data (the trailing `nil`). -/
def recordNonce (n : Nat) : ByteArray :=
  ⟨#[0, 0, 0, 0,
     ctrByte n 7, ctrByte n 6, ctrByte n 5, ctrByte n 4,
     ctrByte n 3, ctrByte n 2, ctrByte n 1, ctrByte n 0]⟩

/-- Decode a 12-byte record nonce's counter field: `binary.BigEndian.Uint64(n[4:])`. -/
def recordNonceCounter (b : ByteArray) : Nat :=
  (b.get! 4).toNat * 2 ^ 56 + (b.get! 5).toNat * 2 ^ 48 +
  (b.get! 6).toNat * 2 ^ 40 + (b.get! 7).toNat * 2 ^ 32 +
  (b.get! 8).toNat * 2 ^ 24 + (b.get! 9).toNat * 2 ^ 16 +
  (b.get! 10).toNat * 2 ^ 8 + (b.get! 11).toNat

theorem recordNonce_size (n : Nat) : (recordNonce n).size = 12 := rfl

/-- The first four bytes of a record nonce are zero — `nonce.Valid()`'s
`binary.BigEndian.Uint32(n[:4]) == 0` clause, true by construction. -/
theorem recordNonce_prefix_zero (n : Nat) :
    (recordNonce n).get! 0 = 0 ∧ (recordNonce n).get! 1 = 0 ∧
    (recordNonce n).get! 2 = 0 ∧ (recordNonce n).get! 3 = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **The big-endian encoding round-trips.** For every counter in `uint64` range,
reading the field back with `BigEndian.Uint64` recovers it exactly. A
little-endian `recordNonce` does *not* satisfy this against this decoder — the
theorem pins the byte order, it does not merely assert a bijection. -/
theorem recordNonceCounter_recordNonce (n : Nat) (h : n < 2 ^ 64) :
    recordNonceCounter (recordNonce n) = n := by
  show (ctrByte n 7).toNat * 2 ^ 56 + (ctrByte n 6).toNat * 2 ^ 48 +
      (ctrByte n 5).toNat * 2 ^ 40 + (ctrByte n 4).toNat * 2 ^ 32 +
      (ctrByte n 3).toNat * 2 ^ 24 + (ctrByte n 2).toNat * 2 ^ 16 +
      (ctrByte n 1).toNat * 2 ^ 8 + (ctrByte n 0).toNat = n
  simp only [ctrByte]
  rw [UInt8.toNat_ofNat_of_lt' (show n / 2 ^ (8 * 7) % 256 < 256 by omega),
      UInt8.toNat_ofNat_of_lt' (show n / 2 ^ (8 * 6) % 256 < 256 by omega),
      UInt8.toNat_ofNat_of_lt' (show n / 2 ^ (8 * 5) % 256 < 256 by omega),
      UInt8.toNat_ofNat_of_lt' (show n / 2 ^ (8 * 4) % 256 < 256 by omega),
      UInt8.toNat_ofNat_of_lt' (show n / 2 ^ (8 * 3) % 256 < 256 by omega),
      UInt8.toNat_ofNat_of_lt' (show n / 2 ^ (8 * 2) % 256 < 256 by omega),
      UInt8.toNat_ofNat_of_lt' (show n / 2 ^ (8 * 1) % 256 < 256 by omega),
      UInt8.toNat_ofNat_of_lt' (show n / 2 ^ (8 * 0) % 256 < 256 by omega)]
  omega

/-- **Distinct counters give distinct nonces** (injectivity on the `uint64`
range): no two frames under one transport key can ever reuse a nonce, which is
the precondition the AEAD's security argument requires. -/
theorem recordNonce_injective {m n : Nat} (hm : m < 2 ^ 64) (hn : n < 2 ^ 64)
    (h : recordNonce m = recordNonce n) : m = n := by
  have hm' := recordNonceCounter_recordNonce m hm
  rw [h, recordNonceCounter_recordNonce n hn] at hm'
  exact hm'.symm

/-- At counter 0 the record and handshake nonces coincide (both all-zero) —
which is exactly why a little-endian record layer passes a one-frame smoke test. -/
theorem recordNonce_zero_eq_noiseNonce_zero : recordNonce 0 = noiseNonce 0 := rfl

/-- **…and from counter 1 on they differ.** Big-endian puts the 1 in byte 11,
little-endian in byte 4. This is the interop breaker, stated as a theorem. -/
theorem recordNonce_ne_noiseNonce : recordNonce 1 ≠ noiseNonce 1 := by
  intro h
  exact absurd (congrArg (fun b => b.get! 11) h) (by decide)

/-- `controlbase`'s `invalidNonce` (`conn.go`): the counter value at which the
cipher state is declared exhausted and the connection unusable. -/
def invalidNonce : Nat := 2 ^ 64 - 1

/-- `nonce.Valid()`: the top four bytes zero (always, `recordNonce_prefix_zero`)
**and** the counter not exhausted. -/
def recordNonceValid (n : Nat) : Bool := n != invalidNonce

/-- The ts2021 Noise protocol name (33 bytes, so `InitializeSymmetric` hashes it). -/
def noiseProtocolName : ByteArray := "Noise_IK_25519_ChaChaPoly_BLAKE2s".toUTF8

/-- `protocolVersionPrefix` (handshake.go). -/
def prologuePrefix : ByteArray := "Tailscale Control Protocol v".toUTF8

/-- `protocolVersionPrologue(v)` = prefix ‖ decimal-ASCII version (handshake.go). -/
def tsPrologue (version : Nat) : ByteArray := prologuePrefix ++ (toString version).toUTF8

/-- Noise `SymmetricState`: chaining key, transcript hash, current AEAD key
(`none` until the first `MixKey`), and the per-key nonce counter. -/
structure Sym where
  ck : ByteArray
  h  : ByteArray
  k  : Option ByteArray
  n  : Nat

/-- `InitializeSymmetric(protocolName)`: the 33-byte name > 32, so `h = HASH(name)`
and `ck = h` (Noise §5.2). -/
def initSym : Sym :=
  let h0 := Wireguard.Blake2s.hash noiseProtocolName
  { ck := h0, h := h0, k := none, n := 0 }

/-- `MixHash(data)`: `h ← HASH(h ‖ data)` (BLAKE2s, `Wireguard.Blake2s.hash`). -/
def Sym.mixHash (s : Sym) (data : ByteArray) : Sym :=
  { s with h := Wireguard.Blake2s.hash (s.h ++ data) }

/-- `MixKey(ikm)`: `(ck, k) ← HKDF(ck, ikm, 2)` (BLAKE2s-HMAC), reset `n`.
`Wireguard.Noise.kdf2` is exactly Noise's 2-output HKDF. -/
def Sym.mixKey (s : Sym) (ikm : ByteArray) : Sym :=
  let (ck', k') := Wireguard.Noise.kdf2 s.ck ikm
  { s with ck := ck', k := some k', n := 0 }

/-- `EncryptAndHash(pt)`: AEAD-seal under `k` with `ad = h`, then `MixHash(ct)`;
before the first `MixKey` (`k = none`) it is the identity, still mixing the bytes. -/
def Sym.encryptAndHash (s : Sym) (pt : ByteArray) : Option (ByteArray × Sym) :=
  match s.k with
  | none => some (pt, s.mixHash pt)
  | some k =>
    match Crypto.chachaSeal k (noiseNonce s.n) s.h pt with
    | some ct => some (ct, { s.mixHash ct with n := s.n + 1 })
    | none => none

/-- `DecryptAndHash(ct)`: AEAD-open under `k` with `ad = h`, then `MixHash(ct)`. -/
def Sym.decryptAndHash (s : Sym) (ct : ByteArray) : Option (ByteArray × Sym) :=
  match s.k with
  | none => some (ct, s.mixHash ct)
  | some k =>
    match Crypto.chachaOpen k (noiseNonce s.n) s.h ct with
    | some pt => some (pt, { s.mixHash ct with n := s.n + 1 })
    | none => none

/-- `Split()`: `(k1, k2) ← HKDF(ck, empty, 2)` — the two directional transport keys. -/
def Sym.split (s : Sym) : ByteArray × ByteArray :=
  Wireguard.Noise.kdf2 s.ck ByteArray.empty

/-- The 64-byte transport material `k1 ‖ k2`. Feeds `Control.Channel.initiatorTx`
/`responderTx`, which re-split it into per-direction send/recv keys — exactly
`handshake.go`'s client `tx=c1,rx=c2` / server `tx=c2,rx=c1`. -/
def Sym.material (s : Sym) : ByteArray := let (a, b) := s.split; a ++ b

/-! ## §4  The Noise_IK message cores

General over prologue and payload (so a published Noise test vector can drive
them); the ts2021 wrappers in §6 fix the prologue and the empty payloads. -/

/-- Noise_IK **initiation** (initiator) → the Noise message `e ‖ enc(s) ‖ enc(payload)`
and the post-message symmetric state. Initiator holds static `(siPriv,siPub)` and
ephemeral `(eiPriv,eiPub)`, and knows the responder static `rsPub`. -/
def noiseInitiation (prologue siPriv siPub eiPriv eiPub rsPub payload : ByteArray) :
    Option (ByteArray × Sym) :=
  let s0 := ((initSym.mixHash prologue).mixHash rsPub).mixHash eiPub
  match Crypto.x25519 eiPriv rsPub with
  | none => none
  | some dhes =>
    match (s0.mixKey dhes).encryptAndHash siPub with
    | none => none
    | some (encS, s2) =>
      match Crypto.x25519 siPriv rsPub with
      | none => none
      | some dhss =>
        match (s2.mixKey dhss).encryptAndHash payload with
        | none => none
        | some (encP, s4) => some (eiPub ++ encS ++ encP, s4)

/-- Noise_IK **initiation** read (responder): decrypt `e ‖ enc(s) ‖ enc(payload)`
→ `(eiPub, siPub, payload, state)`. Responder holds static `(srPriv, srPub)`
(its `srPub` is the initiator's known `rsPub`). -/
def readInitiation (prologue srPriv srPub noiseMsg : ByteArray) :
    Option (ByteArray × ByteArray × ByteArray × Sym) :=
  let eiPub := noiseMsg.extract 0 32
  let encS  := noiseMsg.extract 32 80
  let encP  := noiseMsg.extract 80 noiseMsg.size
  let s0 := ((initSym.mixHash prologue).mixHash srPub).mixHash eiPub
  match Crypto.x25519 srPriv eiPub with
  | none => none
  | some dhes =>
    match (s0.mixKey dhes).decryptAndHash encS with
    | none => none
    | some (siPub, s2) =>
      match Crypto.x25519 srPriv siPub with
      | none => none
      | some dhss =>
        match (s2.mixKey dhss).decryptAndHash encP with
        | none => none
        | some (pl, s4) => some (eiPub, siPub, pl, s4)

/-- Noise_IK **response** (responder) from the post-initiation state → the Noise
message `er ‖ enc(payload)` and the post-message state (its `split` is the
transport material). -/
def noiseResponse (s0 : Sym) (erPriv erPub eiPub siPub payload : ByteArray) :
    Option (ByteArray × Sym) :=
  let s1 := s0.mixHash erPub
  match Crypto.x25519 erPriv eiPub with
  | none => none
  | some dhee =>
    match Crypto.x25519 erPriv siPub with
    | none => none
    | some dhse =>
      match ((s1.mixKey dhee).mixKey dhse).encryptAndHash payload with
      | none => none
      | some (encP, s4) => some (erPub ++ encP, s4)

/-- Noise_IK **response** read (initiator) from the post-initiation state →
`(payload, state)`. Initiator holds `(siPriv, eiPriv)`. -/
def readResponse (s0 : Sym) (eiPriv siPriv respMsg : ByteArray) :
    Option (ByteArray × Sym) :=
  let erPub := respMsg.extract 0 32
  let encP  := respMsg.extract 32 respMsg.size
  let s1 := s0.mixHash erPub
  match Crypto.x25519 eiPriv erPub with
  | none => none
  | some dhee =>
    match Crypto.x25519 siPriv erPub with
    | none => none
    | some dhse =>
      match ((s1.mixKey dhee).mixKey dhse).decryptAndHash encP with
      | none => none
      | some (pl, s4) => some (pl, s4)

/-! ## §5  The byte-exact handshake frames (initiation 101 B, response 51 B)

`messages.go`: initiation = `[ver:u16BE][type=1][len:u16BE][noise]` (5-byte
header, L19 `initiationHeaderLen = 5`), response = `[type=2][len:u16BE][noise]`
(3-byte header, L17 `headerLen = 3`). -/

/-- Frame a Noise initiation payload: 5-byte header `[ver][type=1][len]`. -/
def frameInitiation (version : Nat) (noise : Bytes) : Bytes :=
  putU16BE version ++ (msgTypeInitiation :: (putU16BE noise.length ++ noise))

/-- Parse an initiation frame → `(version, noisePayload, rest)`. -/
def parseInitiation (bs : Bytes) : Option (Nat × Bytes × Bytes) :=
  match getU16BE bs with
  | some (version, r1) =>
    match r1 with
    | t :: r2 =>
      if t == msgTypeInitiation then
        match getU16BE r2 with
        | some (len, body) =>
          if len ≤ body.length then some (version, body.take len, body.drop len) else none
        | none => none
      else none
    | [] => none
  | none => none

/-- Frame a Noise response payload: 3-byte header `[type=2][len]`. -/
def frameResponse (noise : Bytes) : Bytes :=
  msgTypeResponse :: (putU16BE noise.length ++ noise)

/-- Parse a response frame → `(noisePayload, rest)`. -/
def parseResponse (bs : Bytes) : Option (Bytes × Bytes) :=
  match bs with
  | [] => none
  | t :: rest =>
    if t == msgTypeResponse then
      match getU16BE rest with
      | some (len, body) =>
        if len ≤ body.length then some (body.take len, body.drop len) else none
      | none => none
    else none

/-- **Initiation frame round-trips** (byte-exact `[ver:u16BE][1][len:u16BE][noise]`). -/
theorem parseInitiation_frame (version : Nat) (hv : version < 65536)
    (noise : Bytes) (hl : noise.length < 65536) :
    parseInitiation (frameInitiation version noise) = some (version, noise, []) := by
  simp only [frameInitiation, parseInitiation]
  rw [getU16BE_putU16BE version hv]
  simp only [beq_self_eq_true, if_true]
  rw [getU16BE_putU16BE noise.length hl]
  simp only [Nat.le_refl, if_true, List.take_length, List.drop_length]

/-- **Response frame round-trips** (byte-exact `[2][len:u16BE][noise]`). -/
theorem parseResponse_frame (noise : Bytes) (hl : noise.length < 65536) :
    parseResponse (frameResponse noise) = some (noise, []) := by
  simp only [frameResponse, parseResponse, beq_self_eq_true, if_true]
  rw [getU16BE_putU16BE noise.length hl]
  simp only [Nat.le_refl, if_true, List.take_length, List.drop_length]

/-! ## §6  ts2021 specializations (fixed prologue, empty handshake payload) -/

/-- Build the byte-exact ts2021 **initiation** frame + the initiator's post-message
symmetric state (empty Noise payload, `tsPrologue version`). -/
def mkTs2021Initiation (version : Nat) (siPriv siPub eiPriv eiPub rsPub : ByteArray) :
    Option (Bytes × Sym) :=
  match noiseInitiation (tsPrologue version) siPriv siPub eiPriv eiPub rsPub ByteArray.empty with
  | some (np, s) => some (frameInitiation version (bytesOf np), s)
  | none => none

/-- Build the byte-exact ts2021 **response** frame + the responder transport
material (empty Noise payload). -/
def mkTs2021Response (s0 : Sym) (erPriv erPub eiPub siPub : ByteArray) :
    Option (Bytes × ByteArray) :=
  match noiseResponse s0 erPriv erPub eiPub siPub ByteArray.empty with
  | some (rp, s) => some (frameResponse (bytesOf rp), s.material)
  | none => none

/-- The responder's post-response symmetric state (the transcript), alongside the
frame. `mkTs2021Response` returns only the material; the FSM wants the state too
so the two ends' transcripts can be compared. -/
def mkTs2021ResponseSt (s0 : Sym) (erPriv erPub eiPub siPub : ByteArray) :
    Option (Bytes × Sym) :=
  match noiseResponse s0 erPriv erPub eiPub siPub ByteArray.empty with
  | some (rp, s) => some (frameResponse (bytesOf rp), s)
  | none => none

/-- `mkTs2021Response` is `mkTs2021ResponseSt` followed by `Sym.material` — the
two agree by construction, so the FSM's use of the state-returning form derives
exactly the material the wire builder does. -/
theorem mkTs2021Response_eq (s0 : Sym) (erPriv erPub eiPub siPub : ByteArray) :
    mkTs2021Response s0 erPriv erPub eiPub siPub
      = (mkTs2021ResponseSt s0 erPriv erPub eiPub siPub).map
          (fun p => (p.1, p.2.material)) := by
  unfold mkTs2021Response mkTs2021ResponseSt
  cases noiseResponse s0 erPriv erPub eiPub siPub ByteArray.empty <;> rfl

/-! ## §7  Axiom ledger -/

#print axioms getU16BE_putU16BE
#print axioms parseInitiation_frame
#print axioms parseResponse_frame
#print axioms mkTs2021Response_eq

end Control.Ts2021Wire
