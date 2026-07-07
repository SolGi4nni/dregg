/-
# TlsHandshake — the TLS 1.3 server-side handshake MESSAGE layer

`TlsCrypto` supplied the real key schedule and record layer over EverCrypt, but
its `realConfig.hsFeed` was a shortcut: it "completed the handshake once any
ciphertext arrived", ignoring the bytes. The record layer was real; the message
layer that must *drive* it — parse the peer's ClientHello, agree a shared
secret, run the key schedule off the true transcript, and emit the server's
flight — was missing. This module supplies it.

A server-side TLS 1.3 handshake is, at the message layer:

1. **Parse ClientHello** (RFC 8446 §4.1.2). The record/handshake framing, the
   `key_share` extension (the client's X25519 public key), `supported_versions`
   (TLS 1.3 present), the `cipher_suites` (offer `TLS_CHACHA20_POLY1305_SHA256`),
   and the SNI.
2. **Agree the DHE secret** (`Crypto.x25519`: server ephemeral × client public)
   and hash the transcript (`Crypto.sha256` over the handshake messages), then
   drive `TlsCrypto.deriveSchedule` to the handshake- and application-traffic
   secrets — REAL crypto, over the REAL transcript.
3. **Emit the server flight** — ServerHello (server `key_share`), then, sealed
   under the server handshake key (`TlsCrypto.recordSeal`), EncryptedExtensions,
   Certificate, CertificateVerify (`Crypto.ed25519Sign` over the RFC 8446 §4.4.3
   signature content), and Finished (the RFC 8446 §4.4.4 HMAC, computed as
   `Crypto.hkdfExtract finished_key transcript_hash`, since HKDF-Extract *is*
   HMAC).
4. **Verify the client Finished** and establish: `waitCH → waitClientFinished →
   established`. No application data is delivered before establishment; a wrong
   client Finished is rejected.

The three theorems are structural (they do not evaluate the opaque EverCrypt
primitives, so they need no linked shim):

* `waitCH_not_established` / `serverStep_delivers_nothing` — the FSM reaches
  `established` only through the Finished round, and surfaces no application
  plaintext during the handshake (that is the record layer's job, afterward).
* `hs_transcript_drives_keys` — an `Established`'s secrets are exactly
  `TlsCrypto.deriveSchedule dhe thHS thSF`, a pure function of the DHE and the
  actual transcript hashes; composing `TlsCrypto.keyschedule_deterministic`,
  equal transcripts yield equal keys.
* `hs_finished_authenticates` — acceptance requires the presented client
  `verify_data` to equal the server-computed HMAC; a wrong Finished never
  establishes.

The self-test `tls-handshake-selftest` drives this against the RFC 8448 §3
ClientHello on the linked EverCrypt (deriving the RFC's handshake traffic
secrets), then runs a full self-consistent handshake to `established`.

Beyond the core handshake, this module carries the RFC 8446 depth features:
certificate selection over a multi-certificate pool (`chooseCert` — SNI per
RFC 6066 §3, then the client's `signature_algorithms`, serving the §9.1
MUST-support `rsa_pss_rsae_sha256` / `ecdsa_secp256r1_sha256` schemes through
per-entry signer seams), OCSP stapling (§4.4.2.1, `buildCertificateStapled`),
stateless resumption tickets carrying the issuing connection's suite and ALPN
(§4.6.1/§4.2.10, `TicketInfo`), and 0-RTT early data (§4.2.10/§4.5): accepted
only through `earlyGate` — behind the deployment's single-use anti-replay
register — surfaced on `ServerOut.earlyData` (a channel separate from
`delivered`, whose emptiness theorem is untouched), with EndOfEarlyData
extending the client-Finished transcript, and REJECTED offers' records
trial-skipped per §4.2.10 rather than fataled.
-/

import TlsCrypto

namespace TlsHandshake

open Crypto TlsCrypto

/-! ## Byte helpers -/

/-- List → ByteArray at the crypto boundary (shadowing `TlsCrypto.toBA` here). -/
def ofBytes (l : Tls.Bytes) : ByteArray := ByteArray.mk l.toArray

/-- A single big-endian `uint8` byte. -/
def u8 (n : Nat) : ByteArray := ByteArray.mk #[UInt8.ofNat n]

/-- Big-endian `uint16`. -/
def u16 (n : Nat) : ByteArray := ByteArray.mk #[UInt8.ofNat (n / 256), UInt8.ofNat n]

/-- Big-endian `uint24`. -/
def u24 (n : Nat) : ByteArray :=
  ByteArray.mk #[UInt8.ofNat (n / 65536), UInt8.ofNat (n / 256), UInt8.ofNat n]

/-- Big-endian `uint32`. -/
def u32 (n : Nat) : ByteArray :=
  ByteArray.mk #[UInt8.ofNat (n / 16777216), UInt8.ofNat (n / 65536),
                 UInt8.ofNat (n / 256), UInt8.ofNat n]

/-- A length-`len`-prefixed (`uint8` length) opaque vector. -/
def vec8 (b : ByteArray) : ByteArray := u8 b.size ++ b

/-- A length-`len`-prefixed (`uint16` length) opaque vector. -/
def vec16 (b : ByteArray) : ByteArray := u16 b.size ++ b

/-- A length-`len`-prefixed (`uint24` length) opaque vector. -/
def vec24 (b : ByteArray) : ByteArray := u24 b.size ++ b

/-- A handshake message: `msg_type(1) ‖ uint24 length ‖ body` (RFC 8446 §4). -/
def hsMsg (msgType : Nat) (body : ByteArray) : ByteArray :=
  u8 msgType ++ vec24 body

/-! ## Constants -/

/-- `TLS_CHACHA20_POLY1305_SHA256` (RFC 8446 §B.4). -/
def chachaSuite : Nat := 0x1303

/-- `TLS_AES_128_GCM_SHA256` (RFC 8446 §B.4) — the §9.1 mandatory-to-implement
suite. -/
def aes128Suite : Nat := 0x1301

/-- The suites this server implements, in preference order. Both hash with
SHA-256, so one key schedule serves both; the record AEAD is dispatched by
`TlsCrypto.Aead`. -/
def serverSuites : List Nat := [chachaSuite, aes128Suite]

/-- The record AEAD of a supported suite. -/
def suiteAead (suite : Nat) : TlsCrypto.Aead :=
  if suite == aes128Suite then .aes128gcm else .chacha20poly1305

/-- The `x25519` named group (RFC 8446 §4.2.7 / RFC 8422). -/
def x25519Group : Nat := 0x001d

/-- The `secp256r1` (NIST P-256) named group — the §9.1 MUST-support group.
The pure core reaches its group arithmetic through the `ServerParams.p256Dh`
seam (instantiated with the verified HACL* binding by the executables that
link it). -/
def p256Group : Nat := 0x0017

/-- The TLS 1.3 code point (`supported_versions`). -/
def tls13 : Nat := 0x0304

/-- `SignatureScheme.ed25519` (RFC 8446 §4.2.3) — the scheme this server's
default certificate key signs with. -/
def ed25519SigAlg : Nat := 0x0807

/-- `SignatureScheme.rsa_pss_rsae_sha256` (RFC 8446 §4.2.3) — a §9.1
MUST-support CertificateVerify algorithm, served when a deployment provides
an RSA certificate entry. -/
def rsaPssSigAlg : Nat := 0x0804

/-- `SignatureScheme.ecdsa_secp256r1_sha256` (RFC 8446 §4.2.3) — the other
§9.1 MUST-support algorithm, served when a deployment provides a P-256
certificate entry. -/
def ecdsaSigAlg : Nat := 0x0403

/-! ### Alert descriptions (RFC 8446 §6.2) -/

/-- `close_notify` (§6.1). -/
def closeNotifyDesc : Nat := 0
/-- `unexpected_message`. -/
def unexpectedMessageDesc : Nat := 10
/-- `bad_record_mac` — a record that fails AEAD deprotection. -/
def badRecordMacDesc : Nat := 20
/-- `handshake_failure` — no acceptable set of parameters. -/
def handshakeFailureDesc : Nat := 40
/-- `illegal_parameter` — a field violated the spec (e.g. a second ClientHello
that still omits the requested share). -/
def illegalParameterDesc : Nat := 47
/-- `decode_error` — a message that cannot be parsed. -/
def decodeErrorDesc : Nat := 50
/-- `decrypt_error` — a handshake cryptographic check (Finished) failed. -/
def decryptErrorDesc : Nat := 51
/-- `protocol_version` — the peer does not support TLS 1.3. -/
def protocolVersionDesc : Nat := 70
/-- `internal_error`. -/
def internalErrorDesc : Nat := 80
/-- `missing_extension` (§4.2 — a mandatory extension is absent). -/
def missingExtensionDesc : Nat := 109
/-- `no_application_protocol` (RFC 7301 §3.2). -/
def noApplicationProtocolDesc : Nat := 120

/-- A plaintext fatal alert record: `0x15 ‖ 0x0303 ‖ len=2 ‖ level=fatal(2) ‖
description` (RFC 8446 §5.1, §6). Sent for rejections that occur before any
record protection is established. -/
def plainAlert (desc : Nat) : ByteArray :=
  ByteArray.mk #[0x15, 0x03, 0x03, 0x00, 0x02, 0x02, UInt8.ofNat desc]

/-! ## ClientHello parsing (over `List UInt8`, total, `Option`-valued) -/

/-- Read a big-endian `uint16`, returning the value and the remaining bytes. -/
def rd16 : Tls.Bytes → Option (Nat × Tls.Bytes)
  | a :: b :: r => some (a.toNat * 256 + b.toNat, r)
  | _ => none

/-- Read a big-endian `uint24`. -/
def rd24 : Tls.Bytes → Option (Nat × Tls.Bytes)
  | a :: b :: c :: r => some (a.toNat * 65536 + b.toNat * 256 + c.toNat, r)
  | _ => none

/-- Take exactly `n` bytes, or `none` if fewer are present. -/
def takeN (n : Nat) (l : Tls.Bytes) : Option (Tls.Bytes × Tls.Bytes) :=
  if l.length < n then none else some (l.take n, l.drop n)

/-- Walk a byte block as a list of `(type, data)` extensions
(`uint16 type ‖ uint16 len ‖ data[len]`), collecting all that parse. `fuel`
bounds the iteration (each step consumes ≥ 4 bytes; pass the block length). -/
def walkExts : Nat → Tls.Bytes → List (Nat × Tls.Bytes)
  | 0, _ => []
  | fuel + 1, l =>
    match rd16 l with
    | none => []
    | some (ty, r1) =>
      match rd16 r1 with
      | none => []
      | some (len, r2) =>
        match takeN len r2 with
        | none => []
        | some (data, rest) => (ty, data) :: walkExts fuel rest

/-- Walk a byte block as a list of `uint16` values (used for `cipher_suites`
and the `supported_versions` version list). -/
def walkU16s : Nat → Tls.Bytes → List Nat
  | 0, _ => []
  | fuel + 1, l =>
    match rd16 l with
    | none => []
    | some (v, r) => v :: walkU16s fuel r

/-- Find the client share for named group `target` inside a `key_share`
extension body's entry list: `(group(2) ‖ key<uint16>)*`. Returns the raw
key-exchange bytes (32 for x25519, 65 for secp256r1's uncompressed point). -/
def findShare (target : Nat) : Nat → Tls.Bytes → Option Tls.Bytes
  | 0, _ => none
  | fuel + 1, l =>
    match rd16 l with
    | none => none
    | some (grp, r1) =>
      match rd16 r1 with
      | none => none
      | some (klen, r2) =>
        match takeN klen r2 with
        | none => none
        | some (key, rest) =>
          if grp == target then some key else findShare target fuel rest

/-- Walk an ALPN protocol-name list: `(uint8 len ‖ name)*` (RFC 7301 §3.1). -/
def walkAlpn : Nat → Tls.Bytes → List Tls.Bytes
  | 0, _ => []
  | fuel + 1, l =>
    match l with
    | len :: t =>
      match takeN len.toNat t with
      | some (name, rest) => name :: walkAlpn fuel rest
      | none => []
    | [] => []

/-- A `uint16`-length-prefixed list of `uint16` values (the shape of the
`supported_groups` and `signature_algorithms` extension bodies). -/
def u16ListBody (b : Tls.Bytes) : List Nat :=
  match rd16 b with
  | some (len, r) => let l := r.take len; walkU16s l.length l
  | none => []

/-- A `pre_shared_key` offer (RFC 8446 §4.2.11), reduced to the fields the
server acts on: the first identity (the ticket), the first binder, and how
many bytes the binders list occupies at the tail of the ClientHello (the
§4.2.11.2 transcript truncation point — `pre_shared_key` MUST be the last
extension, so the binders list ends the message). -/
structure OfferedPsk where
  /-- The first `PskIdentity.identity` — the ticket issued by NewSessionTicket. -/
  identity : Tls.Bytes
  /-- The first `PskBinderEntry` — the client's binder MAC. -/
  binder : Tls.Bytes
  /-- Encoded size of the whole binders list (its `uint16` length prefix
  included): the byte count `Truncate(ClientHello)` removes. -/
  bindersEncLen : Nat
  deriving Repr

/-- The parsed ClientHello fields the server acts on. -/
structure ClientHello where
  /-- The 32-byte client random. -/
  random : Tls.Bytes
  /-- The echoed legacy session id. -/
  sessionId : Tls.Bytes
  /-- Offered cipher suites (each a `uint16`). -/
  cipherSuites : List Nat
  /-- The client's X25519 public key from `key_share`, if offered. -/
  keyShare : Option Tls.Bytes
  /-- Whether `supported_versions` offered TLS 1.3. -/
  tls13Offered : Bool
  /-- The SNI host name, if present. -/
  sni : Option Tls.Bytes
  /-- The `supported_groups` (RFC 8446 §4.2.7) named-group list; `[]` when the
  extension is absent. Drives HelloRetryRequest when a supported group was
  offered without a matching share. -/
  groups : List Nat := []
  /-- The `signature_algorithms` (§4.2.3) list; `none` when the extension is
  absent (a §9.2 violation for a certificate-authenticated handshake). -/
  sigAlgs : Option (List Nat) := none
  /-- The ALPN (RFC 7301) protocol names; `none` when not offered. -/
  alpnOffered : Option (List Tls.Bytes) := none
  /-- The client's `secp256r1` share from `key_share` (a 65-byte uncompressed
  point), if offered. -/
  keyShareP256 : Option Tls.Bytes := none
  /-- Whether `psk_key_exchange_modes` (§4.2.9) offered `psk_dhe_ke` — the
  only PSK mode this server resumes with. -/
  pskDheKe : Bool := false
  /-- The `pre_shared_key` offer (§4.2.11), if present. -/
  psk : Option OfferedPsk := none
  /-- Whether a `status_request` extension (RFC 6066 §8 / RFC 8446 §4.4.2.1)
  asked for an OCSP staple (`status_type = ocsp`). -/
  statusRequested : Bool := false
  /-- Whether the `early_data` extension (§4.2.10) offered 0-RTT data. -/
  earlyData : Bool := false
  deriving Repr

/-- Strip a TLS record header (`type(1) ‖ legacy_version(2) ‖ uint16 len`) if the
first byte is `0x16` (handshake); otherwise return the input unchanged. So both a
bare ClientHello handshake message and a full record are accepted. -/
def stripRecord (l : Tls.Bytes) : Tls.Bytes :=
  match l with
  | 0x16 :: _v1 :: _v2 :: _l1 :: _l2 :: rest => rest
  | _ => l

/-- Extract the SNI host name from a `server_name` extension body. -/
def parseSni (body : Tls.Bytes) : Option Tls.Bytes :=
  match rd16 body with           -- server_name_list length
  | none => none
  | some (_, r0) =>
    match r0 with
    | _nameType :: r1 =>          -- name_type (0 = host_name)
      match rd16 r1 with
      | none => none
      | some (nlen, r2) =>
        match takeN nlen r2 with
        | some (name, _) => some name
        | none => none
    | [] => none

/-- Look up an extension body by type in the walked list. -/
def extBody (exts : List (Nat × Tls.Bytes)) (ty : Nat) : Option Tls.Bytes :=
  (exts.find? (fun p => p.1 == ty)).map (·.2)

/-- Parse a `pre_shared_key` extension body (RFC 8446 §4.2.11):
`identities<7..2^16-1> ‖ binders<33..2^16-1>` where each identity is
`opaque identity<1..2^16-1> ‖ uint32 obfuscated_ticket_age` and each binder is
`opaque PskBinderEntry<32..255>`. Extracts the FIRST identity and binder (the
only ones this server considers, `selected_identity` 0) and the encoded
binders-list size for the §4.2.11.2 transcript truncation. -/
def parsePskOffer (body : Tls.Bytes) : Option OfferedPsk := do
  let (idsLen, r1) ← rd16 body
  let (idsBlock, r2) ← takeN idsLen r1
  let (identLen, i1) ← rd16 idsBlock
  -- The obfuscated ticket age is not used for 0-RTT freshness: the single-use
  -- anti-replay register (`ServerParams.earlyDataOk`) is strictly stronger —
  -- each ticket identity is accepted for early data at most once, ever.
  let (ident, _) ← takeN identLen i1
  let (bindersLen, b1) ← rd16 r2
  let (bindersBlock, _) ← takeN bindersLen b1
  let (blen, bb) ← (match bindersBlock with | l :: t => some (l.toNat, t) | [] => none)
  let (binder, _) ← takeN blen bb
  some { identity := ident, binder := binder, bindersEncLen := 2 + bindersLen }

/-- **Parse a ClientHello.** Accepts either the bare handshake message or a full
record. Follows RFC 8446 §4.1.2: `msg_type(1)=0x01 ‖ uint24 len ‖
legacy_version(2) ‖ random(32) ‖ session_id<uint8> ‖ cipher_suites<uint16> ‖
legacy_compression<uint8> ‖ extensions<uint16>`. -/
def parseClientHello (input : Tls.Bytes) : Option ClientHello := do
  let hs := stripRecord input
  match hs with
  | 0x01 :: r0 =>                                   -- ClientHello handshake type
    let (_len, r1) ← rd24 r0                         -- handshake length
    let (rnd, r2) ← takeN 32 (r1.drop 2)             -- skip legacy_version, take random
    let (sidLen, r3) ← (match r2 with | b :: t => some (b.toNat, t) | [] => none)
    let (sid, r4) ← takeN sidLen r3
    let (csLen, r5) ← rd16 r4
    let (csBytes, r6) ← takeN csLen r5
    let (compLen, r7) ← (match r6 with | b :: t => some (b.toNat, t) | [] => none)
    let (_comp, r8) ← takeN compLen r7
    let (extLen, r9) ← rd16 r8
    let (extBytes, _) ← takeN extLen r9
    let exts := walkExts extBytes.length extBytes
    let shareOf := fun (grp : Nat) => (extBody exts 0x0033).bind (fun b =>
      match rd16 b with
      | some (_, entries) => findShare grp entries.length entries
      | none => none)
    let ks := shareOf x25519Group
    let ksP256 := shareOf p256Group
    let sv := (extBody exts 0x002b).map (fun b =>
      match b with
      | l :: t => (walkU16s t.length (t.take l.toNat)).contains tls13
      | [] => false)
    let sni := (extBody exts 0x0000).bind parseSni
    let groups := ((extBody exts 0x000a).map u16ListBody).getD []
    let sigAlgs := (extBody exts 0x000d).map u16ListBody
    let alpn := (extBody exts 0x0010).map (fun b =>
      match rd16 b with
      | some (len, r) => let l := r.take len; walkAlpn l.length l
      | none => [])
    let pskDheKe := ((extBody exts 0x002d).map (fun b =>
      match b with
      | l :: t => (t.take l.toNat).contains (1 : UInt8)
      | [] => false)).getD false
    let psk := (extBody exts 0x0029).bind parsePskOffer
    -- status_request (RFC 6066 §8): `status_type(1) ‖ responder_id_list ‖
    -- request_extensions`; a staple is requested when status_type is ocsp(1).
    let statusReq := ((extBody exts 0x0005).map (fun b => b.headD 0 == 1)).getD false
    some { random := rnd
           sessionId := sid
           cipherSuites := walkU16s csBytes.length csBytes
           keyShare := ks
           tls13Offered := sv.getD false
           sni := sni
           groups := groups
           sigAlgs := sigAlgs
           alpnOffered := alpn
           keyShareP256 := ksP256
           pskDheKe := pskDheKe
           psk := psk
           statusRequested := statusReq
           earlyData := (extBody exts 0x002a).isSome }
  | _ => none

/-! ## Negotiation (RFC 8446 §4.1.1) -/

/-- Select the cipher suite: the first server-preferred suite the client
offered. -/
def negotiateSuite (offered : List Nat) : Option Nat :=
  serverSuites.find? (fun s => offered.contains s)

/-- **Negotiation soundness.** A selected suite was both implemented by the
server and offered by the client — the negotiation cannot invent a suite. -/
theorem negotiateSuite_sound {offered : List Nat} {s : Nat}
    (h : negotiateSuite offered = some s) :
    s ∈ serverSuites ∧ s ∈ offered := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have hp := List.find?_some h
  simpa using hp

/-- The application protocols this server can actually speak, in preference
order (HTTP/1.1 only — what the byte-level responder implements). -/
def alpnHttp11 : Tls.Bytes := "http/1.1".toUTF8.toList

def serverAlpn : List Tls.Bytes := [alpnHttp11]

/-- Select the ALPN protocol: the first server-supported name the client
offered. -/
def negotiateAlpn (offered : List Tls.Bytes) : Option Tls.Bytes :=
  serverAlpn.find? (fun p => offered.contains p)

/-- **ALPN soundness**: a selected protocol was offered by the client and is
implemented by the server. -/
theorem negotiateAlpn_sound {offered : List Tls.Bytes} {p : Tls.Bytes}
    (h : negotiateAlpn offered = some p) :
    p ∈ serverAlpn ∧ p ∈ offered := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have hp := List.find?_some h
  simpa using hp

/-- The ALPN decision over an optional offer: no extension → proceed without
ALPN; an offer with a supported protocol → that protocol; an offer with no
overlap → reject (RFC 7301 §3.2 `no_application_protocol`). -/
inductive AlpnChoice where
  | ok (selected : Option Tls.Bytes)
  | reject
deriving Repr, DecidableEq

def chooseAlpn : Option (List Tls.Bytes) → AlpnChoice
  | none => .ok none
  | some offered =>
    match negotiateAlpn offered with
    | some p => .ok (some p)
    | none => .reject

/-! ## The server's message builders (RFC 8446 §4) -/

/-- The ServerHello `pre_shared_key` extension (RFC 8446 §4.2.11): the server
accepted the offered PSK at `selected_identity` 0. -/
def preSharedKeyExt : ByteArray := u16 0x0029 ++ vec16 (u16 0)

/-- **ServerHello** (RFC 8446 §4.1.3): `legacy_version(0x0303) ‖ random(32) ‖
legacy_session_id_echo<uint8> ‖ cipher_suite(2) ‖ legacy_compression(0) ‖
extensions<uint16>` with a `key_share` (server public, at named group `group`)
and `supported_versions` (0x0304) extension — plus `pre_shared_key` when the
handshake resumed from an accepted PSK. Returns the full handshake message. -/
def buildServerHello (suite : Nat) (random sessionIdEcho serverPub : ByteArray)
    (group : Nat := x25519Group) (pskSelected : Bool := false) : ByteArray :=
  let keyShareExt := u16 0x0033 ++ vec16 (u16 group ++ vec16 serverPub)
  let supVerExt := u16 0x002b ++ vec16 (u16 tls13)
  -- RFC 8448 §3 orders key_share before supported_versions; match it so the
  -- transcript hash reproduces the published trace.
  let exts := keyShareExt ++ supVerExt
                ++ (if pskSelected then preSharedKeyExt else ByteArray.empty)
  let body := u16 0x0303 ++ random ++ vec8 sessionIdEcho
                ++ u16 suite ++ u8 0 ++ vec16 exts
  hsMsg 2 body

/-- **EncryptedExtensions** (RFC 8446 §4.3.1): empty extension block. -/
def buildEncryptedExtensions : ByteArray := hsMsg 8 (u16 0)

/-- The ALPN extension (RFC 7301 §3.1) carrying the single selected protocol:
`type=16 ‖ ext_len ‖ protocol_name_list<uint16> = (uint8 len ‖ name)`. -/
def alpnExt (proto : Tls.Bytes) : ByteArray :=
  u16 0x0010 ++ vec16 (vec16 (vec8 (ofBytes proto)))

/-- **EncryptedExtensions** carrying the negotiated ALPN protocol (or the empty
block when none was negotiated). -/
def buildEncryptedExtensionsWith (alpn : Option Tls.Bytes) : ByteArray :=
  match alpn with
  | some proto => hsMsg 8 (vec16 (alpnExt proto))
  | none => buildEncryptedExtensions

/-- The empty `early_data` extension (RFC 8446 §4.2.10) — in
EncryptedExtensions it announces that the server ACCEPTED the 0-RTT offer. -/
def earlyDataExt : ByteArray := u16 0x002a ++ u16 0

/-- **EncryptedExtensions** with the negotiated ALPN and, when the 0-RTT offer
was accepted, the `early_data` extension. At `early = false` this is exactly
`buildEncryptedExtensionsWith`. -/
def buildEncryptedExtensionsFull (alpn : Option Tls.Bytes) (early : Bool) :
    ByteArray :=
  if early then
    hsMsg 8 (vec16 ((match alpn with
                     | some proto => alpnExt proto
                     | none => ByteArray.empty) ++ earlyDataExt))
  else buildEncryptedExtensionsWith alpn

theorem buildEE_no_early (alpn : Option Tls.Bytes) :
    buildEncryptedExtensionsFull alpn false = buildEncryptedExtensionsWith alpn := rfl

/-- **Certificate** (RFC 8446 §4.4.2): the certificate chain (end-entity first,
then the certifying authorities in order), each entry with no per-entry
extensions, and an empty `certificate_request_context`. -/
def buildCertificate (chain : List ByteArray) : ByteArray :=
  let entries := chain.foldl (fun acc c => acc ++ vec24 c ++ u16 0) ByteArray.empty
  hsMsg 11 (u8 0 ++ vec24 entries)            -- context<uint8> ‖ certificate_list<uint24>

/-- The `status_request` CertificateEntry extension (RFC 8446 §4.4.2.1): a
`CertificateStatus` carrying a DER `OCSPResponse` —
`status_type ocsp(1) ‖ response<uint24>` — as the leaf entry's extension. -/
def certStatusExt (ocsp : ByteArray) : ByteArray :=
  u16 0x0005 ++ vec16 (u8 1 ++ vec24 ocsp)

/-- **Certificate with an OCSP staple** (RFC 8446 §4.4.2.1): like
`buildCertificate`, with the staple attached as the end-entity entry's
`status_request` extension. With no staple this is exactly `buildCertificate`. -/
def buildCertificateStapled (chain : List ByteArray) (staple : Option ByteArray) :
    ByteArray :=
  match chain, staple with
  | leaf :: rest, some ocsp =>
    let entries := (vec24 leaf ++ vec16 (certStatusExt ocsp))
      ++ rest.foldl (fun acc c => acc ++ vec24 c ++ u16 0) ByteArray.empty
    hsMsg 11 (u8 0 ++ vec24 entries)
  | _, _ => buildCertificate chain

/-- **No staple, no change**: the stapled builder degenerates to the plain
Certificate exactly when there is nothing to staple. -/
theorem buildCertificateStapled_none (chain : List ByteArray) :
    buildCertificateStapled chain none = buildCertificate chain := by
  unfold buildCertificateStapled
  cases chain <;> rfl

/-! ### Servable certificates (RFC 8446 §4.4.2.2, §4.2.3, RFC 6066 §3)

A deployment serves a SET of certificates — differing in signature algorithm
(§9.1 requires `rsa_pss_rsae_sha256` and `ecdsa_secp256r1_sha256` alongside
this server's Ed25519 default) and possibly in SNI host name. The entry
carries its signer as a function seam, like `ServerParams.p256Dh`: the pure
core never links a signature backend; executables instantiate the seam with
the verified HACL* bindings (`TlsCrypto.Sig`, `Crypto.ed25519Sign`). -/

/-- One servable certificate: its CertificateVerify `SignatureScheme`, the
chain, the signing seam (§4.4.3 content → wire signature), the SNI host names
it serves (`[]` = any name), and an optional OCSP staple. -/
structure CertEntry where
  /-- The `SignatureScheme` code point CertificateVerify will carry. -/
  sigAlg : Nat := ed25519SigAlg
  /-- The end-entity certificate (DER). -/
  certData : ByteArray
  /-- The issuing authorities, in order. -/
  certChain : List ByteArray := []
  /-- The signing seam: §4.4.3 signature content → wire-form signature. -/
  sign : ByteArray → Option ByteArray := fun _ => none
  /-- SNI host names this entry serves; `[]` serves any name. -/
  names : List Tls.Bytes := []
  /-- A DER `OCSPResponse` to staple when the client requests one. -/
  ocspStaple : Option ByteArray := none

/-! ### HelloRetryRequest (RFC 8446 §4.1.4) -/

/-- The fixed "HelloRetryRequest" ServerHello random (RFC 8446 §4.1.3) —
SHA-256 of "HelloRetryRequest". -/
def hrrRandom : ByteArray := ByteArray.mk
  #[0xCF, 0x21, 0xAD, 0x74, 0xE5, 0x9A, 0x61, 0x11, 0xBE, 0x1D, 0x8C, 0x02,
    0x1E, 0x65, 0xB8, 0x91, 0xC2, 0xA2, 0x11, 0x16, 0x7A, 0xBB, 0x8C, 0x5E,
    0x07, 0x9E, 0x09, 0xE2, 0xC8, 0xA8, 0x33, 0x9C]

/-- **HelloRetryRequest**: a ServerHello whose random is `hrrRandom`, whose
`key_share` extension carries only the requested named group (no key), asking
the client to retry with a share for that group. -/
def buildHrr (suite : Nat) (sessionIdEcho : ByteArray)
    (group : Nat := x25519Group) : ByteArray :=
  let keyShareExt := u16 0x0033 ++ vec16 (u16 group)
  let supVerExt := u16 0x002b ++ vec16 (u16 tls13)
  let exts := keyShareExt ++ supVerExt
  hsMsg 2 (u16 0x0303 ++ hrrRandom ++ vec8 sessionIdEcho
            ++ u16 suite ++ u8 0 ++ vec16 exts)

/-- The §4.4.1 transcript substitution for a retried handshake: when the server
responds with HelloRetryRequest, `ClientHello1` is replaced in the transcript by
a synthetic `message_hash` handshake message over its hash. -/
def msgHash (chMsg : ByteArray) : ByteArray := hsMsg 254 (sha256 chMsg)

/-- Wrap a plaintext handshake message as a wire record (`0x16 ‖ 0x0303 ‖ len`). -/
def wrapPlainHs (m : ByteArray) : ByteArray :=
  ByteArray.mk #[0x16, 0x03, 0x03] ++ u16 m.size ++ m

/-- The RFC 8446 §4.4.3 CertificateVerify signature content: 64 `0x20` octets,
the ASCII context string `"TLS 1.3, server CertificateVerify"`, a single `0x00`
separator, then the transcript hash. -/
def certVerifyContent (thash : ByteArray) : ByteArray :=
  ByteArray.mk ((List.replicate 64 (0x20 : UInt8)).toArray)
    ++ "TLS 1.3, server CertificateVerify".toUTF8 ++ u8 0 ++ thash

/-- **CertificateVerify** (RFC 8446 §4.4.3): the Ed25519 signature
(`SignatureScheme ed25519 = 0x0807`) over `certVerifyContent thash`. `none` only
on a `Crypto.ed25519Sign` size error. -/
def buildCertificateVerify (certSeed thash : ByteArray) : Option ByteArray :=
  match ed25519Sign certSeed (certVerifyContent thash) with
  | some sig => some (hsMsg 15 (u16 0x0807 ++ vec16 sig))
  | none => none

/-- **CertificateVerify at a certificate entry's own scheme** (RFC 8446
§4.4.3): the entry's signing seam over `certVerifyContent thash`, carried
under the entry's `SignatureScheme` code point. -/
def buildCertificateVerifyWith (entry : CertEntry) (thash : ByteArray) :
    Option ByteArray :=
  match entry.sign (certVerifyContent thash) with
  | some sig => some (hsMsg 15 (u16 entry.sigAlg ++ vec16 sig))
  | none => none

/-- At an Ed25519 entry whose seam is `Crypto.ed25519Sign` of `certSeed`, the
generalized builder is exactly the classic one. -/
theorem buildCertificateVerifyWith_ed25519 (certSeed thash : ByteArray) :
    buildCertificateVerifyWith
      { sigAlg := ed25519SigAlg, certData := ByteArray.empty
        sign := fun content => ed25519Sign certSeed content } thash
      = buildCertificateVerify certSeed thash := by
  unfold buildCertificateVerifyWith buildCertificateVerify
  rfl

/-- The Finished key (RFC 8446 §4.4.4): `HKDF-Expand-Label(BaseKey, "finished",
"", Hash.length)`. -/
def finishedKey (baseKey : ByteArray) : Option ByteArray :=
  expandLabel baseKey "finished".toUTF8 ByteArray.empty hashLen

/-- The Finished `verify_data` (RFC 8446 §4.4.4): `HMAC(finished_key,
Transcript-Hash(...))`. HKDF-Extract *is* HMAC-Hash, so this is
`hkdfExtract finished_key thash`. -/
def verifyData (baseKey thash : ByteArray) : Option ByteArray :=
  match finishedKey baseKey with
  | some fk => hkdfExtract fk thash
  | none => none

/-- **Finished** (RFC 8446 §4.4.4): the handshake message carrying `verify_data`.
`none` on a derivation size error. -/
def buildFinished (baseKey thash : ByteArray) : Option ByteArray :=
  (verifyData baseKey thash).map (hsMsg 20)

/-! ## Session tickets and PSK resumption (RFC 8446 §4.6.1, §4.2.11)

The server issues **stateless, self-contained** tickets: the ticket bytes are
the resumption PSK sealed (ChaCha20-Poly1305) under a key derived from the
server's long-term signing seed, prefixed with the seal nonce. Any later
connection to the same server — with no shared state beyond the seed — can
open the ticket, recover the PSK, and verify the offer's binder. -/

/-- The ticket-sealing key: a deterministic, domain-separated derivation from
the server's long-term seed, so every connection (process) of one server opens
the tickets any other issued. -/
def ticketKey (seed : ByteArray) : ByteArray :=
  sha256 (seed ++ "tls ticket key v1".toUTF8)

/-- Seal a resumption PSK into an opaque ticket: `nonce(12) ‖ AEAD(psk)`. -/
def sealTicket (tkey nonce psk : ByteArray) : Option ByteArray :=
  (chachaSeal tkey nonce ByteArray.empty psk).map (fun ct => nonce ++ ct)

/-- Open a presented ticket (a `pre_shared_key` identity): split the seal
nonce, deprotect. `none` for tickets this server did not issue (the AEAD
also rejects any truncated ciphertext shorter than its tag). -/
def openTicket (tkey : ByteArray) (ticket : Tls.Bytes) : Option ByteArray :=
  if ticket.length < 12 then none    -- at least the seal nonce
  else chachaOpen tkey (ofBytes (ticket.take 12)) ByteArray.empty
         (ofBytes (ticket.drop 12))

/-- The §7.1 resumption PSK: `HKDF-Expand-Label(resumption_master_secret,
"resumption", ticket_nonce, Hash.length)` — the value the client derives from
its own resumption master secret, and the value this server seals into the
ticket. -/
def resumptionPskOf (rms tnonce : ByteArray) : Option ByteArray :=
  expandLabel rms "resumption".toUTF8 tnonce hashLen

/-- Advertised ticket lifetime (§4.6.1; MUST NOT exceed 604800). -/
def ticketLifetime : Nat := 7200

/-- What a sealed ticket certifies beyond the PSK itself: the cipher suite and
ALPN protocol of the issuing connection. RFC 8446 §4.2.10 requires a server
accepting 0-RTT to verify the resumed connection selected the same suite and
ALPN, so the ticket must carry them. -/
structure TicketInfo where
  /-- The §7.1 resumption PSK (`Hash.length` = 32 bytes). -/
  psk : ByteArray
  /-- The cipher suite of the issuing connection. -/
  suite : Nat := chachaSuite
  /-- The ALPN protocol of the issuing connection, if any. -/
  alpn : Option Tls.Bytes := none

/-- The sealed ticket payload: `psk(32) ‖ suite(2) ‖ alpn<uint8>` (an empty
ALPN vector encodes "none" — the empty protocol name is not a valid ALPN). -/
def encodeTicketInfo (i : TicketInfo) : ByteArray :=
  i.psk ++ u16 i.suite ++ (match i.alpn with
                           | some a => vec8 (ofBytes a)
                           | none => u8 0)

/-- Parse a sealed ticket payload back into its `TicketInfo`. -/
def parseTicketInfo (b : ByteArray) : Option TicketInfo := do
  let (psk, r1) ← takeN 32 b.toList
  let (suite, r2) ← rd16 r1
  match r2 with
  | 0 :: _ => some { psk := ofBytes psk, suite := suite, alpn := none }
  | len :: t => (takeN len.toNat t).map (fun p =>
      { psk := ofBytes psk, suite := suite, alpn := some p.1 })
  | [] => none

/-- **NewSessionTicket** (§4.6.1): `uint32 lifetime ‖ uint32 age_add ‖
ticket_nonce<uint8> ‖ ticket<uint16> ‖ extensions<uint16>`, carrying a sealed
self-contained ticket for this session's resumption PSK (ticket_nonce 0)
together with the connection's suite and ALPN (the §4.2.10 0-RTT match
context). When `maxEarly > 0` the ticket advertises the `early_data`
extension with that `max_early_data_size` — the deployment's 0-RTT opt-in. -/
def buildNewSessionTicket (tkey sealNonce rms : ByteArray) (ageAdd : Nat)
    (suite : Nat := chachaSuite) (alpn : Option Tls.Bytes := none)
    (maxEarly : Nat := 0) : Option ByteArray :=
  let tnonce := ByteArray.mk #[0]
  match resumptionPskOf rms tnonce with
  | none => none
  | some psk =>
    match sealTicket tkey sealNonce
            (encodeTicketInfo { psk := psk, suite := suite, alpn := alpn }) with
    | none => none
    | some ticket =>
      let exts := if maxEarly > 0
        then vec16 (u16 0x002a ++ vec16 (u32 maxEarly))
        else u16 0
      some (hsMsg 4 (u32 ticketLifetime ++ u32 ageAdd
                      ++ vec8 tnonce ++ vec16 ticket ++ exts))

/-- The §4.2.11.2 binder key: `Derive-Secret(HKDF-Extract(0, PSK),
"res binder", "")`. -/
def binderKeyOf (psk : ByteArray) : Option ByteArray :=
  (earlySecret psk).bind (fun es => deriveSecret es "res binder".toUTF8 emptyHash)

/-- The expected `PskBinderEntry` MAC: computed "in the same fashion as the
Finished message" (§4.2.11.2) with the binder key as base key, over the
transcript hash of the binder-truncated ClientHello. -/
def expectedBinder (psk thTrunc : ByteArray) : Option ByteArray :=
  (binderKeyOf psk).bind (fun bk => verifyData bk thTrunc)

/-! ## The server-side handshake state machine -/

/-- The established session material. It stores **only** the DHE secret and the
two transcript hashes; the key schedule and the per-direction record keys are
*derived* from them (below), so they are — by construction, not by convention —
a pure function of the transcript and the shared secret. -/
structure Established where
  /-- The X25519 shared secret. -/
  dhe : ByteArray
  /-- Transcript-Hash(ClientHello ‖ ServerHello). -/
  thHS : ByteArray
  /-- Transcript-Hash(ClientHello ‖ … ‖ server Finished). -/
  thSF : ByteArray
  /-- Negotiated application protocol. -/
  alpn : Tls.Alpn
  /-- The negotiated cipher suite (selects the record AEAD). -/
  suite : Nat := chachaSuite
  /-- The negotiated ALPN protocol name, when the client offered one. -/
  alpnProto : Option Tls.Bytes := none
  /-- The raw §4.4.1 transcript (the concatenated handshake messages this
  session hashed — through the server Finished at flight time, extended with
  the client Finished at establishment). Public handshake plaintext; kept so
  post-handshake secrets (resumption_master_secret) can extend the hash. -/
  transcript : ByteArray := ByteArray.empty
  /-- The pre-shared key this session resumed from — the §7.1 zero IKM
  (`zeros hashLen`) for a full handshake. -/
  psk : ByteArray := TlsCrypto.zeros TlsCrypto.hashLen
  /-- Whether the server accepted the client's 0-RTT offer (§4.2.10): early
  records are expected under the early traffic keys until EndOfEarlyData. -/
  earlyAccepted : Bool := false
  /-- `client_early_traffic_secret` (§7.1) when 0-RTT was accepted. -/
  clientEarlySecret : ByteArray := ByteArray.empty
  /-- Receive sequence within the early-data phase. -/
  earlySeq : Nat := 0
  /-- Trial-decryption budget (§4.2.10): with a REJECTED 0-RTT offer, this
  many client records that fail to open under the handshake keys are skipped
  (they are the client's early data, sealed under keys this server never
  derived) before a failure is fatal. -/
  skipEarly : Nat := 0
  /-- Transcript-Hash for the client Finished: `thSF` for a 1-RTT handshake,
  extended with EndOfEarlyData (§4.5) after an accepted 0-RTT phase. Empty
  means "not yet extended" — use `thSF`. -/
  thCF : ByteArray := ByteArray.empty

/-- The full `TlsCrypto` key schedule for this session — `deriveSchedulePsk` of
the PSK, the DHE, and the two transcript hashes (`deriveSchedule` exactly when
`psk` is the zero IKM, by `TlsCrypto.deriveSchedule_eq_psk_zero`). -/
def Established.schedule (e : Established) : TlsCrypto.Schedule :=
  TlsCrypto.deriveSchedulePsk e.psk e.dhe e.thHS e.thSF

/-- Server-direction handshake record keys (the server writes its flight with
these), derived from the server_handshake_traffic_secret at the negotiated
suite's AEAD. -/
def Established.tx (e : Established) : TlsCrypto.RecordKeys :=
  (trafficKeysA (suiteAead e.suite) (e.schedule.serverHs.getD (zeros hashLen))).getD defaultKeys

/-- Client-direction handshake record keys (the server reads the client Finished
with these), derived from the client_handshake_traffic_secret. -/
def Established.rx (e : Established) : TlsCrypto.RecordKeys :=
  (trafficKeysA (suiteAead e.suite) (e.schedule.clientHs.getD (zeros hashLen))).getD defaultKeys

/-- Early-data record keys (the client's 0-RTT records), derived from
`client_early_traffic_secret` at the negotiated suite's AEAD. -/
def Established.earlyRx (e : Established) : TlsCrypto.RecordKeys :=
  (trafficKeysA (suiteAead e.suite) e.clientEarlySecret).getD defaultKeys

/-- The transcript hash the client Finished is checked against: `thSF`
(through the server Finished) for 1-RTT, extended through EndOfEarlyData
after an accepted 0-RTT phase (§4.4.4 with §4.5 in the transcript). -/
def Established.clientFinHash (e : Established) : ByteArray :=
  if e.thCF.isEmpty then e.thSF else e.thCF

/-- The retained context of an emitted HelloRetryRequest: the §4.4.1 transcript
prefix (`message_hash(ClientHello1) ‖ HelloRetryRequest`), the suite the HRR
committed to, and the named group whose share it requested. -/
structure Retry where
  transcriptPrefix : ByteArray
  suite : Nat
  group : Nat := x25519Group

/-- The server handshake phase. -/
inductive HsState where
  /-- Awaiting the ClientHello. -/
  | waitCH
  /-- HelloRetryRequest sent; awaiting the second ClientHello (§4.1.4). -/
  | waitCH2 (retry : Retry)
  /-- Server flight sent; awaiting the client Finished. -/
  | waitClientFinished (est : Established)
  /-- Handshake complete. -/
  | established (est : Established)
  /-- Handshake failed (parse error, no shared group, bad Finished). -/
  | failed

/-- What one server step emits. -/
structure ServerOut where
  /-- Record-layer bytes to send (the server flight / alerts). Never plaintext. -/
  flight : ByteArray := ByteArray.empty
  /-- The **plaintext** handshake messages of the server flight this step
  emitted (ServerHello ‖ EncryptedExtensions ‖ Certificate ‖ CertificateVerify
  ‖ Finished — the bare `msg_type ‖ len ‖ body` messages, *not* the sealed
  record bytes in `flight`). This is the RFC 8446 §4.4.1 transcript
  contribution the record layer needs to accumulate; empty when no flight is
  sent. -/
  hsPlain : Tls.Bytes := []
  /-- Application plaintext delivered *by the handshake layer* — always empty;
  the record layer delivers application data only after establishment. -/
  delivered : Tls.Bytes := []
  /-- 0-RTT early-data plaintext (RFC 8446 §4.2.10), surfaced on its OWN
  channel — never through `delivered`. Nonempty only during an ACCEPTED early
  phase, which `earlyGate` opens solely behind the deployment's anti-replay
  check; consumers owe it the replay-tolerance discipline the safety layer
  models. -/
  earlyData : Tls.Bytes := []
  /-- Set when the handshake reaches `established` this step. -/
  done : Bool := false

/-- The server's static handshake parameters. -/
structure ServerParams where
  /-- Server ephemeral X25519 private key (32 bytes). -/
  ephemeralPriv : ByteArray
  /-- The 32-byte server random for ServerHello. -/
  serverRandom : ByteArray
  /-- Ed25519 signing seed (RFC 8032 §5.1.5) for CertificateVerify. -/
  certSeed : ByteArray
  /-- The end-entity certificate bytes to send. -/
  certData : ByteArray
  /-- The rest of the certificate chain (issuing authorities, in order). -/
  certChain : List ByteArray := []
  /-- The named groups this deployment's key exchange supports, in preference
  order. `secp256r1` belongs here only when `p256Dh` is instantiated. -/
  groupsSupported : List Nat := [x25519Group]
  /-- The secp256r1 key-exchange seam: from the server's 32-byte ephemeral
  scalar and the client's key-share bytes, the server's own share and the ECDH
  shared secret. Defaults to "unsupported"; executables that link the verified
  HACL* P-256 binding instantiate it with `TlsCrypto.P256.dhPair`, keeping the
  binding out of this module's import (and link) closure. -/
  p256Dh : ByteArray → Tls.Bytes → Option (ByteArray × ByteArray) := fun _ _ => none
  /-- Additional servable certificates (RSA / ECDSA / per-SNI entries), tried
  in order before the default Ed25519 entry built from `certSeed`/`certData`.
  Selection is by SNI host name and the client's `signature_algorithms`. -/
  certs : List CertEntry := []
  /-- A DER `OCSPResponse` to staple for the DEFAULT certificate when the
  client sends `status_request`. -/
  ocspStaple : Option ByteArray := none
  /-- The 0-RTT anti-replay gate (§8): given the offered ticket identity,
  `true` iff this offer is fresh — the deployment's single-use registry (the
  wire oracle marks each ticket on first use). Defaults to "reject all 0-RTT";
  early data is NEVER accepted without an instantiated gate. -/
  earlyDataOk : Tls.Bytes → Bool := fun _ => false
  /-- The `max_early_data_size` advertised on issued tickets when the
  deployment opts into 0-RTT. -/
  maxEarlyData : Nat := 16384

/-- The default certificate entry: the legacy Ed25519 `certSeed`/`certData`/
`certChain` fields as a `CertEntry` (name-agnostic, staple from
`ocspStaple`). -/
def ServerParams.defaultCert (p : ServerParams) : CertEntry :=
  { sigAlg := ed25519SigAlg
    certData := p.certData
    certChain := p.certChain
    sign := fun content => ed25519Sign p.certSeed content
    names := []
    ocspStaple := p.ocspStaple }

/-- Every certificate this deployment can serve, in preference order (the
extra entries first, the default Ed25519 entry last). -/
def ServerParams.certPool (p : ServerParams) : List CertEntry :=
  p.certs ++ [p.defaultCert]

/-- Does an entry serve this SNI name? -/
def sniMatches (e : CertEntry) (sni : Option Tls.Bytes) : Bool :=
  match sni with
  | some n => e.names.contains n
  | none => false

/-- The SNI-restricted certificate pool (RFC 6066 §3): the entries naming the
offered host when any do; otherwise the name-agnostic entries; otherwise (no
entry is name-agnostic and none matched) the whole pool. -/
def sniPool (p : ServerParams) (sni : Option Tls.Bytes) : List CertEntry :=
  match p.certPool.filter (fun e => sniMatches e sni) with
  | [] => match p.certPool.filter (fun e => e.names.isEmpty) with
          | [] => p.certPool
          | anyName => anyName
  | named => named

/-- **Certificate selection** (RFC 8446 §4.4.2.2, §4.2.3; RFC 6066 §3).
Restrict the pool to the entries naming the SNI host, then pick the first
whose `SignatureScheme` the client offered in `signature_algorithms`. When no
entry's scheme was offered, §4.4.3 lets the server proceed with a chain of its
choice rather than abort — the pool head. -/
def chooseCert (p : ServerParams) (ch : ClientHello) : CertEntry :=
  let pool := sniPool p ch.sni
  let offered := ch.sigAlgs.getD []
  (pool.find? (fun e => offered.contains e.sigAlg)).getD (pool.headD p.defaultCert)

/-- **Selection honors `signature_algorithms` whenever it can**: if the chosen
entry's scheme was NOT offered by the client, then NO entry in the SNI-
restricted pool had an offered scheme — the server falls back to a chain of
its choice (§4.4.3's escape) only when every alternative also fails §4.2.3. -/
theorem chooseCert_respects_sigalgs (p : ServerParams) (ch : ClientHello)
    (h : (ch.sigAlgs.getD []).contains (chooseCert p ch).sigAlg = false) :
    ∀ e ∈ sniPool p ch.sni, (ch.sigAlgs.getD []).contains e.sigAlg = false := by
  intro e he
  cases hoff : (ch.sigAlgs.getD []).contains e.sigAlg with
  | false => rfl
  | true =>
    have hsome : ((sniPool p ch.sni).find?
        (fun e => (ch.sigAlgs.getD []).contains e.sigAlg)).isSome :=
      List.find?_isSome.mpr ⟨e, he, hoff⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
    have hxs : (ch.sigAlgs.getD []).contains x.sigAlg = true := by
      simpa using List.find?_some hx
    simp only [chooseCert] at h
    rw [hx] at h
    simp only [Option.getD_some] at h
    rw [hxs] at h
    exact Bool.noConfusion h

/-- **A matching SNI name wins**: when some servable entry names the offered
host, the chosen certificate is one of the entries naming it. -/
theorem chooseCert_honors_sni (p : ServerParams) (ch : ClientHello)
    (hne : p.certPool.filter (fun e => sniMatches e ch.sni) ≠ []) :
    chooseCert p ch ∈ p.certPool.filter (fun e => sniMatches e ch.sni) := by
  have hpool : sniPool p ch.sni = p.certPool.filter (fun e => sniMatches e ch.sni) := by
    unfold sniPool
    split
    · next hemp => exact absurd hemp hne
    · rfl
  simp only [chooseCert, hpool]
  cases hfind : (p.certPool.filter (fun e => sniMatches e ch.sni)).find?
      (fun e => (ch.sigAlgs.getD []).contains e.sigAlg) with
  | some x =>
    simp only [Option.getD_some]
    exact List.mem_of_find?_eq_some hfind
  | none =>
    simp only [Option.getD_none]
    cases hl : p.certPool.filter (fun e => sniMatches e ch.sni) with
    | nil => exact absurd hl hne
    | cons a t => simp [List.headD]

/-- Wrap an AEAD `encrypted_record` as a wire TLSCiphertext: `0x17 0x03 0x03 ‖
uint16 len ‖ ct` (the additional data header is the same bytes). -/
def wrapRecord (ct : ByteArray) : ByteArray := recordAD ct.size ++ ct

/-- Split a TLS 1.3 inner plaintext (RFC 8446 §5.4): strip the zero padding,
then take the trailing content-type byte, returning `(type, content)`. `none`
on an all-zero (typeless) plaintext, which the RFC makes fatal. -/
def splitInner (pt : List UInt8) : Option (UInt8 × List UInt8) :=
  match pt.reverse.dropWhile (· == 0) with
  | t :: restRev => some (t, restRev.reverse)
  | [] => none

/-- **Inner-plaintext framing is correct**: for any content, nonzero content
type, and padding length, `splitInner` recovers exactly the content and type
(§5.4: padding is stripped up to the first nonzero trailing byte). -/
theorem splitInner_spec (content : List UInt8) (t : UInt8) (ht : t ≠ 0) (n : Nat) :
    splitInner (content ++ t :: List.replicate n 0) = some (t, content) := by
  have hbeq : (t == 0) = false := by
    simpa using ht
  have hrev : (content ++ t :: List.replicate n 0).reverse
      = List.replicate n 0 ++ t :: content.reverse := by
    simp [List.reverse_append, List.reverse_cons, List.reverse_replicate,
          List.append_assoc]
  have hdrop : ∀ m, List.dropWhile (· == (0 : UInt8))
      (List.replicate m 0 ++ t :: content.reverse) = t :: content.reverse := by
    intro m
    induction m with
    | zero => simp [List.dropWhile_cons, hbeq]
    | succ k ih => simpa [List.replicate_succ, List.dropWhile_cons] using ih
  simp [splitInner, hrev, hdrop n]

/-- Seal an inner plaintext (`content ‖ contentType`, §5.2/§5.4) into a wire
record under key `rk` at sequence `seq`. AD is the §5.2 header for the
ciphertext length. -/
def sealRecordAt (rk : TlsCrypto.RecordKeys) (seq : Nat) (ctype : Nat)
    (content : ByteArray) : Option ByteArray :=
  let pt := content ++ u8 ctype
  match recordSeal rk seq (recordAD (pt.size + 16)) pt with
  | some ct => some (wrapRecord ct)
  | none => none

/-- Seal a handshake-phase inner plaintext at sequence 0 (the server flight is
one record; content type `0x16` handshake). -/
def sealHsRecord (rk : TlsCrypto.RecordKeys) (inner : ByteArray) : Option ByteArray :=
  sealRecordAt rk 0 0x16 inner

/-- Open a wire record (`0x17 0x03 0x03 ‖ len ‖ ct`) under key `rk` at
sequence `seq`, strip the §5.4 padding, and return `(content type, content)`. -/
def openRecordAt (rk : TlsCrypto.RecordKeys) (seq : Nat) (wire : Tls.Bytes) :
    Option (UInt8 × ByteArray) :=
  match wire with
  | 0x17 :: _ :: _ :: l1 :: l2 :: rest =>
    let ctLen := l1.toNat * 256 + l2.toNat
    let ct := ofBytes (rest.take ctLen)
    match recordOpen rk seq (recordAD ct.size) ct with
    | some pt =>
      match splitInner pt.toList with
      | some (t, content) => some (t, ofBytes content)
      | none => none
    | none => none
  | _ => none

/-- Open a handshake-phase record at sequence 0, requiring the inner content
type to be `0x16` (handshake); returns the handshake message bytes. -/
def openHsRecord (rk : TlsCrypto.RecordKeys) (wire : Tls.Bytes) : Option ByteArray :=
  match openRecordAt rk 0 wire with
  | some (0x16, payload) => some payload
  | _ => none

/-- **Sealed content round-trips through the record layer and the §5.4 framing.**
Whatever `recordSeal` protected as an inner plaintext ending in a nonzero
content-type byte, `recordOpen` under the same key/sequence/AD followed by
`splitInner` recovers exactly `(type, content)` — the composition of the AEAD
round-trip (transported from the verified-crypto assumptions, uniformly over
both suites) with `splitInner_spec` at zero padding. -/
theorem sealed_content_roundtrip (rk : TlsCrypto.RecordKeys) (seq : Nat)
    (ad pt ct : ByteArray) (t : UInt8) (content : List UInt8) (ht : t ≠ 0)
    (hpt : pt.toList = content ++ [t])
    (h : recordSeal rk seq ad pt = some ct) :
    (recordOpen rk seq ad ct).bind (fun x => splitInner x.toList)
      = some (t, content) := by
  rw [record_roundtrip rk seq ad pt ct h]
  simpa [Option.bind, hpt] using splitInner_spec content t ht 0

/-- The EndOfEarlyData handshake message (RFC 8446 §4.5): type 5, empty body. -/
def endOfEarlyDataMsg : ByteArray := hsMsg 5 ByteArray.empty

/-- The client `verify_data` the server expects, given `est` — `HMAC` of the
client handshake finished key over Transcript-Hash(CH … server Finished),
extended through EndOfEarlyData after an accepted 0-RTT phase
(`Established.clientFinHash`). -/
def expectedClientVerifyData (est : Established) : Option ByteArray :=
  verifyData (est.schedule.clientHs.getD (zeros hashLen)) est.clientFinHash

/-- Decide whether an opened client Finished message carries the expected
`verify_data`. The client Finished is `0x14 ‖ uint24 32 ‖ verify_data(32)`, so the
`verify_data` is the message body after the 4-byte header. -/
def acceptClientFinished (est : Established) (openedFin : Option ByteArray) : Bool :=
  match openedFin, expectedClientVerifyData est with
  | some fin, some expected =>
    -- require the Finished handshake type, then compare the verify_data
    match fin.toList with
    | 0x14 :: _ :: _ :: _ :: vd => vd == expected.toList
    | _ => false
  | _, _ => false

/-- Derive the `Established` record from the negotiated parameters and the
server's ephemeral. `serverPub`/`dhe` are the already-computed X25519 outputs;
`transcript0` is the §4.4.1 transcript before the ServerHello (the ClientHello
message — or, after a retry, `message_hash(CH1) ‖ HRR ‖ CH2`). Returns the
established material, the sealed server flight wire bytes, **and** the plaintext
server flight handshake messages (`ServerHello ‖ EncryptedExtensions ‖
Certificate ‖ CertificateVerify ‖ Finished` — the same bytes `thSF` hashes), or
`none` on a derivation size error. -/
def buildFlight (params : ServerParams) (suite : Nat) (alpnSel : Option Tls.Bytes)
    (psk? : Option ByteArray) (group : Nat)
    (sessionIdEcho : Tls.Bytes) (serverPub dhe transcript0 : ByteArray)
    (entry : CertEntry := params.defaultCert) (statusReq : Bool := false)
    (early? : Option ByteArray := none) :
    Option (Established × ByteArray × Tls.Bytes) :=
  -- ServerHello (plaintext record) and the handshake transcript hashes.
  let sh := buildServerHello suite params.serverRandom (ofBytes sessionIdEcho)
              serverPub group psk?.isSome
  let thHS := sha256 (transcript0 ++ sh)
  let ee := buildEncryptedExtensionsFull alpnSel (psk?.isSome && early?.isSome)
  match (match psk? with | some p => earlySecret p | none => earlySecretNoPsk) with
  | none => none
  | some es =>
    match handshakeSecret es dhe with
    | none => none
    | some hs =>
      match serverHsTrafficSecret hs thHS with
      | none => none
      | some sHs =>
        match trafficKeysA (suiteAead suite) sHs with
        | none => none
        | some txHs =>
          match psk? with
          | some psk =>
            -- §4.2.11/§4.4: PSK authentication — the server flight carries no
            -- Certificate and no CertificateVerify; the session authenticates
            -- through the PSK-bound key schedule and Finished.
            match buildFinished sHs (sha256 (transcript0 ++ sh ++ ee)) with
            | none => none
            | some sFin =>
              match sealHsRecord txHs (ee ++ sFin) with
              | none => none
              | some innerRecord =>
                let thSF := sha256 (transcript0 ++ sh ++ ee ++ sFin)
                let est : Established :=
                  { dhe := dhe, thHS := thHS, thSF := thSF, alpn := .h1
                    suite := suite, alpnProto := alpnSel
                    transcript := transcript0 ++ sh ++ ee ++ sFin
                    psk := psk
                    earlyAccepted := early?.isSome
                    clientEarlySecret := early?.getD ByteArray.empty }
                some (est, wrapPlainHs sh ++ innerRecord,
                      (sh ++ ee ++ sFin).toList)
          | none =>
            let cert := buildCertificateStapled (entry.certData :: entry.certChain)
                          (if statusReq then entry.ocspStaple else none)
            match buildCertificateVerifyWith entry (sha256 (transcript0 ++ sh ++ ee ++ cert)) with
            | none => none
            | some cv =>
              match buildFinished sHs (sha256 (transcript0 ++ sh ++ ee ++ cert ++ cv)) with
              | none => none
              | some sFin =>
                match sealHsRecord txHs (ee ++ cert ++ cv ++ sFin) with
                | none => none
                | some innerRecord =>
                  let thSF := sha256 (transcript0 ++ sh ++ ee ++ cert ++ cv ++ sFin)
                  let shRecord := wrapPlainHs sh
                  let est : Established :=
                    { dhe := dhe, thHS := thHS, thSF := thSF, alpn := .h1
                      suite := suite, alpnProto := alpnSel
                      transcript := transcript0 ++ sh ++ ee ++ cert ++ cv ++ sFin }
                  -- The plaintext server flight: the bare handshake messages, in
                  -- order — exactly the bytes `thSF` hashes (after `transcript0`),
                  -- the RFC 8446 §4.4.1 transcript contribution the record layer
                  -- must accumulate.
                  let hsPlain : Tls.Bytes := (sh ++ ee ++ cert ++ cv ++ sFin).toList
                  some (est, shRecord ++ innerRecord, hsPlain)

/-- The rejection step: fail with a plaintext fatal alert (RFC 8446 §6.2). -/
def rejectWith (desc : Nat) : HsState × ServerOut :=
  (.failed, { flight := plainAlert desc })

/-- A fatal alert sealed under the server handshake keys at sequence 1 (the
flight consumed sequence 0) — the alert form for failures after the server
flight, per §6 ("alerts are ... encrypted as specified by the current
connection state"). Falls back to the plaintext form on a seal size error. -/
def encAlert (est : Established) (desc : Nat) : ByteArray :=
  (sealRecordAt est.tx 1 0x15 (ByteArray.mk #[0x02, UInt8.ofNat desc])).getD
    (plainAlert desc)

/-- The outcome of validating a `pre_shared_key` offer (§4.2.11). -/
inductive PskCheck where
  /-- No usable offer (absent, no `psk_dhe_ke` mode, or a ticket this server
  did not issue): proceed with a full handshake, ignoring the offer. -/
  | noPsk
  /-- The ticket opened and the binder MAC verified: resume with this PSK
  (and the issuing connection's suite/ALPN, for the §4.2.10 0-RTT match). -/
  | accepted (info : TicketInfo)
  /-- The ticket opened but the binder did NOT verify — §4.2.11.2 makes this
  fatal (`illegal_parameter`), never a silent fallback. -/
  | badBinder

/-- The accepted ticket, if any. -/
def PskCheck.acceptedInfo : PskCheck → Option TicketInfo
  | .accepted info => some info
  | _ => none

/-- The accepted PSK, if any. -/
def PskCheck.acceptedPsk : PskCheck → Option ByteArray
  | .accepted info => some info.psk
  | _ => none

/-- Validate a `pre_shared_key` offer against the §4.2.11.2 binder:
`transcript0` is the transcript prefix before this ClientHello (empty, or
`message_hash(CH1) ‖ HRR` after a retry) and `chMsg` the full ClientHello
message; the binder MAC is checked over
`Transcript-Hash(transcript0 ‖ Truncate(chMsg))`. -/
def checkPsk (params : ServerParams) (ch : ClientHello)
    (transcript0 chMsg : ByteArray) : PskCheck :=
  match ch.psk with
  | none => .noPsk
  | some op =>
    if !ch.pskDheKe then .noPsk       -- only psk_dhe_ke resumption is served
    else
      match (openTicket (ticketKey params.certSeed) op.identity).bind
              parseTicketInfo with
      | none => .noPsk                -- not our ticket: full handshake
      | some info =>
        let trunc := chMsg.extract 0 (chMsg.size - op.bindersEncLen)
        match expectedBinder info.psk (sha256 (transcript0 ++ trunc)) with
        | some b => if op.binder == b.toList then .accepted info else .badBinder
        | none => .badBinder

/-- `client_early_traffic_secret` (§7.1): `Derive-Secret(Early Secret,
"c e traffic", ClientHello)`. -/
def clientEarlySecretOf (psk thCH : ByteArray) : Option ByteArray :=
  (earlySecret psk).bind (fun es => deriveSecret es "c e traffic".toUTF8 thCH)

/-- **The 0-RTT acceptance gate** (RFC 8446 §4.2.10, §8): early data is
accepted only when the client offered it on a FIRST ClientHello (never after
a retry), the offer rode a binder-verified PSK whose issuing connection used
the SAME cipher suite and ALPN as this one, and the deployment's anti-replay
gate certifies the ticket identity as fresh. -/
def earlyGate (params : ServerParams) (retried : Option Retry)
    (ch : ClientHello) (suite : Nat) (alpnSel : Option Tls.Bytes)
    (info? : Option TicketInfo) : Bool :=
  ch.earlyData && retried.isNone
    && (match info? with
        | some info => (info.suite == suite) && (info.alpn == alpnSel)
        | none => false)
    && (match ch.psk with
        | some op => params.earlyDataOk op.identity
        | none => false)

/-- The gate never opens without the anti-replay check: an accepted 0-RTT
offer certifies `params.earlyDataOk` held on the offered ticket identity —
and the offer itself was present, on a first ClientHello. -/
theorem earlyGate_needs_antireplay (params : ServerParams)
    (retried : Option Retry) (ch : ClientHello) (suite : Nat)
    (alpnSel : Option Tls.Bytes) (info? : Option TicketInfo)
    (h : earlyGate params retried ch suite alpnSel info? = true) :
    ch.earlyData = true ∧ retried = none
      ∧ ∃ op, ch.psk = some op ∧ params.earlyDataOk op.identity = true := by
  unfold earlyGate at h
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨hearly, hretry⟩, -⟩, hgate⟩ := h
  refine ⟨hearly, hretry, ?_⟩
  cases hpsk : ch.psk with
  | none => rw [hpsk] at hgate; exact absurd hgate (by simp)
  | some op => rw [hpsk] at hgate; exact ⟨op, rfl, hgate⟩

/-- The gate never opens without a ticket whose suite and ALPN match this
connection's (§4.2.10's "the same cipher suite and ALPN" requirement). -/
theorem earlyGate_needs_matching_ticket (params : ServerParams)
    (retried : Option Retry) (ch : ClientHello) (suite : Nat)
    (alpnSel : Option Tls.Bytes) (info? : Option TicketInfo)
    (h : earlyGate params retried ch suite alpnSel info? = true) :
    ∃ info, info? = some info ∧ info.suite = suite ∧ info.alpn = alpnSel := by
  unfold earlyGate at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨-, hmatch⟩, -⟩ := h
  cases hinfo : info? with
  | none => rw [hinfo] at hmatch; exact absurd hmatch (by simp)
  | some info =>
    rw [hinfo] at hmatch
    simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
    exact ⟨info, rfl, hmatch.1, hmatch.2⟩

/-- The key-exchange tail of a hello step, after version/suite/sigalg/ALPN
negotiation succeeded: validate any PSK offer (§4.2.11), agree the ECDHE
secret over the client's share (x25519 preferred, secp256r1 through the
`p256Dh` seam), build the server flight, or ask for a §4.1.4 retry when the
client offered a supported group without a usable share. -/
def kexStep (params : ServerParams) (retried : Option Retry) (ch : ClientHello)
    (suite : Nat) (alpnSel : Option Tls.Bytes) (buf : Tls.Bytes) :
    HsState × ServerOut :=
  let chMsg := ofBytes (stripRecord buf)
  let t0 := (retried.map (·.transcriptPrefix)).getD ByteArray.empty
  match checkPsk params ch t0 chMsg with
  | .badBinder =>
    -- §4.2.11.2: a binder that does not validate MUST abort.
    rejectWith illegalParameterDesc
  | pskRes =>
    let psk? := pskRes.acceptedPsk
    let entry := chooseCert params ch
    -- §4.2.10: accept 0-RTT only through the gate; on a rejected offer the
    -- client's early records must be trial-skipped (`skipEarly`), not fataled.
    let early? :=
      if earlyGate params retried ch suite alpnSel pskRes.acceptedInfo then
        pskRes.acceptedPsk.bind
          (fun psk => clientEarlySecretOf psk (sha256 (t0 ++ chMsg)))
      else none
    let withEarly := fun (est : Established) =>
      { est with skipEarly :=
          if ch.earlyData && early?.isNone then 1024 else 0 }
    match ch.keyShare with
    | some cpub =>
      match x25519Base params.ephemeralPriv,
            x25519 params.ephemeralPriv (ofBytes cpub) with
      | some serverPub, some dhe =>
        match buildFlight params suite alpnSel psk? x25519Group
                ch.sessionId serverPub dhe (t0 ++ chMsg)
                entry ch.statusRequested early? with
        | some (est, flight, hsPlain) =>
          (.waitClientFinished (withEarly est),
           { flight := flight, hsPlain := hsPlain })
        | none => rejectWith internalErrorDesc
      | _, _ => rejectWith illegalParameterDesc
    | none =>
      -- No x25519 share; a secp256r1 share works when this deployment
      -- instantiated the P-256 seam.
      match (if params.groupsSupported.contains p256Group
             then ch.keyShareP256 else none) with
      | some cpub =>
        match params.p256Dh params.ephemeralPriv cpub with
        | some (serverPub, dhe) =>
          match buildFlight params suite alpnSel psk? p256Group
                  ch.sessionId serverPub dhe (t0 ++ chMsg)
                  entry ch.statusRequested early? with
          | some (est, flight, hsPlain) =>
            (.waitClientFinished (withEarly est),
             { flight := flight, hsPlain := hsPlain })
          | none => rejectWith internalErrorDesc
        | none =>
          -- §4.2.8.2: an off-curve/invalid point is fatal.
          rejectWith illegalParameterDesc
      | none =>
        match retried with
        | some _ =>
          -- A second ClientHello still without the requested share.
          rejectWith illegalParameterDesc
        | none =>
          match params.groupsSupported.find? (fun g => ch.groups.contains g) with
          | some g =>
            (.waitCH2 { transcriptPrefix :=
                          msgHash chMsg ++ buildHrr suite (ofBytes ch.sessionId) g
                        suite := suite
                        group := g },
             { flight := wrapPlainHs (buildHrr suite (ofBytes ch.sessionId) g)
               hsPlain := (buildHrr suite (ofBytes ch.sessionId) g).toList })
          | none => rejectWith handshakeFailureDesc

/-- Process one ClientHello (first or retried): negotiate version, suite,
signature algorithm, ALPN, PSK, and key-exchange group; then either build the
server flight (a usable key share is present — ECDHE alone, or PSK+ECDHE on a
validated resumption offer), ask for a retry (§4.1.4 — the client offered a
supported group but sent no usable share), or reject with the RFC's alert for
the failing check. `retried` carries the HRR context on the second ClientHello:
its transcript prefix, and the suite the HRR committed to (a change of suite
between the hellos is `illegal_parameter`). -/
def helloStep (params : ServerParams) (retried : Option Retry) (buf : Tls.Bytes) :
    HsState × ServerOut :=
  match parseClientHello buf with
  | none => rejectWith decodeErrorDesc
  | some ch =>
    if !ch.tls13Offered then rejectWith protocolVersionDesc
    else
      match negotiateSuite ch.cipherSuites with
      | none => rejectWith handshakeFailureDesc
      | some suite =>
        if (retried.map (·.suite)).getD suite ≠ suite then rejectWith illegalParameterDesc
        else
          match ch.sigAlgs with
          | none => rejectWith missingExtensionDesc
          | some _sa =>
            -- §4.4.3: the CertificateVerify algorithm MUST be one the client
            -- offered "unless no valid certificate chain can be produced
            -- without unsupported algorithms" — this server's only chain is
            -- Ed25519, so when ed25519 is not offered the handshake continues
            -- with the chain of the server's choice rather than aborting.
            -- The extension itself is mandatory (§9.2, `missing_extension`).
              match chooseAlpn ch.alpnOffered with
              | .reject => rejectWith noApplicationProtocolDesc
              | .ok alpnSel => kexStep params retried ch suite alpnSel buf

/-- **The server handshake step.** Total; drives the real key schedule and record
layer over EverCrypt when a ClientHello is processed. Every rejection emits the
RFC 8446 §6 fatal alert for its cause instead of silently failing. -/
def serverStep (params : ServerParams) : HsState → Tls.Bytes → HsState × ServerOut
  | .waitCH, buf => helloStep params none buf
  | .waitCH2 retry, buf => helloStep params (some retry) buf
  | .waitClientFinished est, buf =>
    if est.earlyAccepted then
      -- The accepted 0-RTT phase (§4.2.10): records open under the early
      -- traffic keys until EndOfEarlyData (§4.5) switches to the handshake
      -- keys and extends the client-Finished transcript.
      match openRecordAt est.earlyRx est.earlySeq buf with
      | some (0x17, content) =>
        (.waitClientFinished { est with earlySeq := est.earlySeq + 1 },
         { earlyData := content.toList })
      | some (0x16, msg) =>
        if msg.toList == endOfEarlyDataMsg.toList then
          (.waitClientFinished { est with
              earlyAccepted := false
              transcript := est.transcript ++ msg
              thCF := sha256 (est.transcript ++ msg)
              earlySeq := est.earlySeq + 1 }, {})
        else (.failed, { flight := encAlert est unexpectedMessageDesc })
      | some _ => (.failed, { flight := encAlert est unexpectedMessageDesc })
      | none => (.failed, { flight := encAlert est badRecordMacDesc })
    else
      match openHsRecord est.rx buf with
      | some fin =>
        if acceptClientFinished est (some fin) then
          (.established { est with transcript := est.transcript ++ fin }, { done := true })
        else (.failed, { flight := encAlert est decryptErrorDesc })
      | none =>
        if est.skipEarly > 0 then
          -- §4.2.10: a REJECTED 0-RTT offer's early records fail to open
          -- under the handshake keys; skip them (bounded), don't abort.
          (.waitClientFinished { est with skipEarly := est.skipEarly - 1 }, {})
        else (.failed, { flight := encAlert est badRecordMacDesc })
  | .established est, _ => (.established est, {})
  | .failed, _ => (.failed, {})

/-! ## Theorems -/

/-- The key-exchange tail delivers no application plaintext. -/
theorem kexStep_delivers_nothing (params : ServerParams) (retried : Option Retry)
    (ch : ClientHello) (suite : Nat) (alpnSel : Option Tls.Bytes)
    (buf : Tls.Bytes) :
    (kexStep params retried ch suite alpnSel buf).2.delivered = [] := by
  unfold kexStep
  dsimp only
  repeat' split
  all_goals rfl

/-- A hello step delivers no application plaintext (helper for
`serverStep_delivers_nothing`). -/
theorem helloStep_delivers_nothing (params : ServerParams) (retried : Option Retry)
    (buf : Tls.Bytes) : (helloStep params retried buf).2.delivered = [] := by
  unfold helloStep
  repeat' split
  all_goals first
    | rfl
    | apply kexStep_delivers_nothing

/-- **The handshake layer surfaces no application plaintext.** Every server step
delivers an empty application byte string — application data is the record
layer's job, only after establishment. -/
theorem serverStep_delivers_nothing (params : ServerParams) (st : HsState)
    (buf : Tls.Bytes) : (serverStep params st buf).2.delivered = [] := by
  cases st with
  | waitCH => exact helloStep_delivers_nothing params none buf
  | waitCH2 retry => exact helloStep_delivers_nothing params (some retry) buf
  | waitClientFinished est =>
    simp only [serverStep]
    repeat' split
    all_goals rfl
  | established est => rfl
  | failed => rfl

/-- The key-exchange tail never establishes. -/
theorem kexStep_not_established (params : ServerParams) (retried : Option Retry)
    (ch : ClientHello) (suite : Nat) (alpnSel : Option Tls.Bytes)
    (buf : Tls.Bytes) (est : Established) :
    (kexStep params retried ch suite alpnSel buf).1 ≠ .established est := by
  unfold kexStep
  dsimp only
  repeat' split
  all_goals exact fun h => HsState.noConfusion h

/-- A hello step never establishes (helper for `waitCH_not_established`). -/
theorem helloStep_not_established (params : ServerParams) (retried : Option Retry)
    (buf : Tls.Bytes) (est : Established) :
    (helloStep params retried buf).1 ≠ .established est := by
  unfold helloStep
  repeat' split
  all_goals first
    | exact fun h => HsState.noConfusion h
    | apply kexStep_not_established

/-- **No establishment without the Finished round.** A step from `waitCH` (or
from the retry wait) never reaches `established`: a ClientHello moves the
machine to `waitClientFinished`, `waitCH2`, or `failed`, so no application-data
phase is entered before the client Finished is verified. -/
theorem waitCH_not_established (params : ServerParams) (buf : Tls.Bytes)
    (est : Established) :
    (serverStep params .waitCH buf).1 ≠ .established est :=
  helloStep_not_established params none buf est

/-- The key-exchange tail fails only as a literal `rejectWith`. -/
theorem kexStep_failed_is_reject (params : ServerParams) (retried : Option Retry)
    (ch : ClientHello) (suite : Nat) (alpnSel : Option Tls.Bytes)
    (buf : Tls.Bytes) :
    (kexStep params retried ch suite alpnSel buf).1 ≠ .failed ∨
    ∃ desc, kexStep params retried ch suite alpnSel buf = rejectWith desc := by
  unfold kexStep
  dsimp only
  repeat' split
  all_goals first
    | exact .inr ⟨_, rfl⟩
    | exact .inl (fun h => HsState.noConfusion h)

/-- Every hello-step outcome is either a non-failure or literally a
`rejectWith` — i.e. a failure with the plaintext fatal alert for its cause. -/
theorem helloStep_failed_is_reject (params : ServerParams) (retried : Option Retry)
    (buf : Tls.Bytes) :
    (helloStep params retried buf).1 ≠ .failed ∨
    ∃ desc, helloStep params retried buf = rejectWith desc := by
  unfold helloStep
  repeat' split
  all_goals first
    | exact .inr ⟨_, rfl⟩
    | exact .inl (fun h => HsState.noConfusion h)
    | apply kexStep_failed_is_reject

/-- **Every hello rejection carries the fatal alert for its cause** (RFC 8446
§6.2): if a hello step fails, the emitted flight is a well-formed plaintext
fatal alert record — never a silent close. -/
theorem helloStep_alert_on_failure (params : ServerParams) (retried : Option Retry)
    (buf : Tls.Bytes) (h : (helloStep params retried buf).1 = .failed) :
    ∃ desc, (helloStep params retried buf).2.flight = plainAlert desc := by
  rcases helloStep_failed_is_reject params retried buf with hne | ⟨d, hd⟩
  · exact absurd h hne
  · exact ⟨d, by rw [hd]; rfl⟩

/-- The key-exchange tail asks for a retry only for a ClientHello without an
x25519 share, requesting the deployment's first supported group among the
client's `supported_groups` offers. -/
theorem kexStep_hrr (params : ServerParams) (retried : Option Retry)
    (ch : ClientHello) (suite : Nat) (alpnSel : Option Tls.Bytes)
    (buf : Tls.Bytes) (r : Retry)
    (h : (kexStep params retried ch suite alpnSel buf).1 = .waitCH2 r) :
    ch.keyShare = none
    ∧ params.groupsSupported.find? (fun g => ch.groups.contains g)
        = some r.group := by
  revert h
  unfold kexStep
  dsimp only
  repeat' split
  all_goals intro h
  all_goals
    simp only [rejectWith, reduceCtorEq, HsState.waitCH2.injEq] at h
  all_goals first
    | exact absurd h (by simp)
    | (subst h; exact ⟨by assumption, by assumption⟩)

/-- **A retry is requested only when it can help** (RFC 8446 §4.1.4): the first
step emits a HelloRetryRequest only for a ClientHello that parsed, offered no
x25519 share, and *did* offer (in `supported_groups`) a group this deployment
supports — the requested group `r.group` is the server's first preference among
the client's offers, so the requested share is one the client claims to
support. -/
theorem hrr_only_without_share (params : ServerParams) (buf : Tls.Bytes) (r : Retry)
    (h : (serverStep params .waitCH buf).1 = .waitCH2 r) :
    ∃ ch, parseClientHello buf = some ch
        ∧ ch.keyShare = none
        ∧ params.groupsSupported.find? (fun g => ch.groups.contains g)
            = some r.group := by
  simp only [serverStep] at h
  unfold helloStep at h
  repeat' split at h
  all_goals first
    | exact HsState.noConfusion h
    | exact ⟨_, by assumption,
             (kexStep_hrr params _ _ _ _ buf r h).1,
             (kexStep_hrr params _ _ _ _ buf r h).2⟩

/-- Corollary, via `List.find?`: the group an HRR requests is both supported by
this deployment and offered by the client — a retry is never requested for a
group that cannot complete the handshake. -/
theorem hrr_group_sound (params : ServerParams) (buf : Tls.Bytes) (r : Retry)
    (h : (serverStep params .waitCH buf).1 = .waitCH2 r) :
    r.group ∈ params.groupsSupported
    ∧ ∃ ch, parseClientHello buf = some ch ∧ ch.groups.contains r.group = true := by
  obtain ⟨ch, hch, -, hfind⟩ := hrr_only_without_share params buf r h
  exact ⟨List.mem_of_find?_eq_some hfind,
         ch, hch, by simpa using List.find?_some hfind⟩

/-- **The negotiated suite is the one the flight is built for**: the
`Established` a successful flight carries records exactly the suite the
negotiation chose (whose AEAD keys the record layer will derive). -/
theorem buildFlight_suite (params : ServerParams) (suite : Nat)
    (alpnSel : Option Tls.Bytes) (psk? : Option ByteArray) (group : Nat)
    (sid : Tls.Bytes) (pub dhe t0 : ByteArray)
    (est : Established) (fl : ByteArray) (hp : Tls.Bytes)
    (h : buildFlight params suite alpnSel psk? group sid pub dhe t0 = some (est, fl, hp)) :
    est.suite = suite := by
  simp only [buildFlight] at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨h1, -, -⟩ := h
       subst h1
       rfl)
    | cases h

/-- **The negotiated ALPN protocol is the one the flight commits to.** With
`negotiateAlpn_sound`, an `Established`'s protocol was offered by the client
and is implemented by the server. -/
theorem buildFlight_alpn (params : ServerParams) (suite : Nat)
    (alpnSel : Option Tls.Bytes) (psk? : Option ByteArray) (group : Nat)
    (sid : Tls.Bytes) (pub dhe t0 : ByteArray)
    (est : Established) (fl : ByteArray) (hp : Tls.Bytes)
    (h : buildFlight params suite alpnSel psk? group sid pub dhe t0 = some (est, fl, hp)) :
    est.alpnProto = alpnSel := by
  simp only [buildFlight] at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨h1, -, -⟩ := h
       subst h1
       rfl)
    | cases h

/-- **The accepted PSK is the one the flight's keys derive from** (and a full
handshake derives from the §7.1 zero IKM): the `Established` a successful
flight carries stores exactly `psk?.getD (zeros hashLen)`, the input
`Established.schedule` feeds to `deriveSchedulePsk` — an accepted resumption
offer cannot silently produce non-PSK keys, nor vice versa. -/
theorem buildFlight_psk (params : ServerParams) (suite : Nat)
    (alpnSel : Option Tls.Bytes) (psk? : Option ByteArray) (group : Nat)
    (sid : Tls.Bytes) (pub dhe t0 : ByteArray)
    (est : Established) (fl : ByteArray) (hp : Tls.Bytes)
    (h : buildFlight params suite alpnSel psk? group sid pub dhe t0 = some (est, fl, hp)) :
    est.psk = psk?.getD (zeros hashLen) := by
  simp only [buildFlight] at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨h1, -, -⟩ := h
       subst h1
       simp_all)
    | cases h

/-- **A flight accepts 0-RTT only on a resumption with an early secret**: the
`Established` a successful flight carries has `earlyAccepted = true` only when
the handshake resumed from a PSK (`psk?.isSome`) and the caller supplied the
accepted early-traffic secret — a full handshake can never enter the early
phase. With `earlyGate_needs_antireplay` (the only way `kexStep` supplies
`early?`), early data therefore rides solely behind the anti-replay gate. -/
theorem buildFlight_early (params : ServerParams) (suite : Nat)
    (alpnSel : Option Tls.Bytes) (psk? : Option ByteArray) (group : Nat)
    (sid : Tls.Bytes) (pub dhe t0 : ByteArray) (entry : CertEntry)
    (statusReq : Bool) (early? : Option ByteArray)
    (est : Established) (fl : ByteArray) (hp : Tls.Bytes)
    (h : buildFlight params suite alpnSel psk? group sid pub dhe t0
           entry statusReq early? = some (est, fl, hp))
    (he : est.earlyAccepted = true) :
    psk?.isSome ∧ early?.isSome := by
  simp only [buildFlight] at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨h1, -, -⟩ := h
       subst h1
       simp_all)
    | cases h

/-- **Early data surfaces only from an accepted early phase**: a `serverStep`
whose output carries early-data bytes was a step from `waitClientFinished` at
an `Established` with `earlyAccepted = true` — no hello step, no Finished
step, and no post-establishment step ever emits on the early channel. -/
theorem earlyData_only_when_accepted (params : ServerParams) (st : HsState)
    (buf : Tls.Bytes)
    (h : (serverStep params st buf).2.earlyData ≠ []) :
    ∃ est, st = .waitClientFinished est ∧ est.earlyAccepted = true := by
  cases st with
  | waitCH =>
    exfalso; apply h
    unfold serverStep helloStep kexStep
    dsimp only
    repeat' split
    all_goals rfl
  | waitCH2 retry =>
    exfalso; apply h
    unfold serverStep helloStep kexStep
    dsimp only
    repeat' split
    all_goals rfl
  | waitClientFinished est =>
    refine ⟨est, rfl, ?_⟩
    cases hacc : est.earlyAccepted with
    | true => rfl
    | false =>
      exfalso; apply h
      simp only [serverStep, hacc, Bool.false_eq_true, if_false]
      repeat' split
      all_goals rfl
  | established est => exact absurd rfl h
  | failed => exact absurd rfl h

/-- **The derived keys are a pure function of the PSK, the DHE secret, and the
transcript.** Every `Established`'s key schedule is exactly
`TlsCrypto.deriveSchedulePsk psk dhe thHS thSF` — there is no hidden input: the
schedule and both directions' record keys are *defined* as functions of the
stored PSK, DHE secret, and transcript hashes. -/
theorem hs_transcript_drives_keys (est : Established) :
    est.schedule = TlsCrypto.deriveSchedulePsk est.psk est.dhe est.thHS est.thSF := rfl

/-- A full (non-resumed) session's schedule is the classic no-PSK chain: at the
zero IKM, `deriveSchedulePsk` *is* `deriveSchedule`. -/
theorem hs_transcript_drives_keys_nopsk (est : Established)
    (h : est.psk = TlsCrypto.zeros TlsCrypto.hashLen) :
    est.schedule = TlsCrypto.deriveSchedule est.dhe est.thHS est.thSF := by
  rw [hs_transcript_drives_keys, h, TlsCrypto.deriveSchedule_eq_psk_zero]

/-- **The key schedule is deterministic**, transported: equal PSK, DHE, and
transcript hashes give equal derived schedules —
`TlsCrypto.keyschedule_psk_deterministic` composed with
`hs_transcript_drives_keys`. Two `Established`s built from the same inputs hold
the same keys. -/
theorem hs_keys_deterministic
    (e1 e2 : Established) (hp : e1.psk = e2.psk)
    (hd : e1.dhe = e2.dhe) (h1 : e1.thHS = e2.thHS) (h2 : e1.thSF = e2.thSF) :
    e1.schedule = e2.schedule := by
  rw [hs_transcript_drives_keys e1, hs_transcript_drives_keys e2]
  exact TlsCrypto.keyschedule_psk_deterministic hp hd h1 h2

/-- **A wrong client Finished is rejected.** From `waitClientFinished` in the
Finished-awaiting phase (no accepted-0-RTT records outstanding, no rejected-
0-RTT trial-skip budget), if the presented client Finished does not carry the
expected `verify_data` (`acceptClientFinished = false`), the machine goes to
`failed` — never `established`. Acceptance requires an exact MAC match, so no
forged or altered Finished completes the handshake. (The unconditional form —
NO path establishes without the MAC match, early phases included — is
`hs_established_needs_finished`.) -/
theorem hs_finished_authenticates (params : ServerParams) (est : Established)
    (buf : Tls.Bytes)
    (hearly : est.earlyAccepted = false) (hskip : est.skipEarly = 0)
    (h : acceptClientFinished est (openHsRecord est.rx buf) = false) :
    (serverStep params (.waitClientFinished est) buf).1 = .failed := by
  simp only [serverStep, hearly, Bool.false_eq_true, if_false]
  split
  · next fin heq =>
    rw [heq] at h
    simp only [h, Bool.false_eq_true, if_false]
  · simp only [hskip]
    rfl

/-! ### Resumption correctness -/

/-- `ByteArray` append concatenates the backing arrays (the `copySlice`
implementation, reduced). -/
theorem data_append (a b : ByteArray) : (a ++ b).data = a.data ++ b.data := by
  show (ByteArray.append a b).data = a.data ++ b.data
  simp [ByteArray.append, ByteArray.copySlice, ByteArray.size,
        Array.extract_empty_of_size_le_start a.data (Nat.le_add_right _ _)]

/-- **A ticket this server sealed opens to the PSK it sealed** — on the exact
wire bytes a resuming client presents as its `pre_shared_key` identity. The
AEAD roundtrip is transported from the verified-crypto assumptions; the
nonce/ciphertext split is the list algebra of the ticket layout. -/
theorem ticket_roundtrip (tkey nonce psk t : ByteArray) (hn : nonce.size = 12)
    (h : sealTicket tkey nonce psk = some t) :
    openTicket tkey t.data.toList = some psk := by
  unfold sealTicket at h
  cases hct : chachaSeal tkey nonce ByteArray.empty psk with
  | none => rw [hct] at h; cases h
  | some ct =>
    rw [hct] at h
    have ht : nonce ++ ct = t := by simpa using h
    subst ht
    have hlist : (nonce ++ ct).data.toList = nonce.data.toList ++ ct.data.toList := by
      rw [data_append, Array.toList_append]
    have hlen : nonce.data.toList.length = 12 := by
      simpa [ByteArray.size] using hn
    have htake : ((nonce ++ ct).data.toList).take 12 = nonce.data.toList := by
      rw [hlist, ← hlen, List.take_left]
    have hdrop : ((nonce ++ ct).data.toList).drop 12 = ct.data.toList := by
      rw [hlist, ← hlen, List.drop_left]
    have hofn : ofBytes nonce.data.toList = nonce := by
      show ByteArray.mk nonce.data.toList.toArray = nonce
      rw [Array.toArray_toList]
    have hofc : ofBytes ct.data.toList = ct := by
      show ByteArray.mk ct.data.toList.toArray = ct
      rw [Array.toArray_toList]
    have hlong : ¬ (nonce ++ ct).data.toList.length < 12 := by
      rw [hlist, List.length_append, hlen]
      omega
    unfold openTicket
    rw [if_neg hlong, htake, hdrop, hofn, hofc]
    exact Crypto.Assumptions.chacha_open_seal_roundtrip _ _ _ _ _ hct

/-- **A PSK is accepted only against a verified binder** (RFC 8446 §4.2.11.2):
`checkPsk` returns `.accepted psk` only when the client's offer carried a
ticket that opens to `psk` under this server's ticket key AND its binder MAC
equals the server-computed binder over the truncated transcript — resumption
cannot be entered with an unauthenticated offer. -/
theorem checkPsk_accepted_only_verified (params : ServerParams) (ch : ClientHello)
    (t0 chMsg : ByteArray) (info : TicketInfo)
    (h : checkPsk params ch t0 chMsg = .accepted info) :
    ∃ op b, ch.psk = some op
      ∧ ch.pskDheKe = true
      ∧ (openTicket (ticketKey params.certSeed) op.identity).bind parseTicketInfo
          = some info
      ∧ expectedBinder info.psk
          (sha256 (t0 ++ chMsg.extract 0 (chMsg.size - op.bindersEncLen))) = some b
      ∧ op.binder = b.toList := by
  unfold checkPsk at h
  repeat' (first | split at h | dsimp only at h)
  all_goals first
    | exact PskCheck.noConfusion h
    | (cases h
       exact ⟨_, _, by assumption, by simp_all, by assumption, by assumption,
              by simp_all⟩)

/-- Fallback is silent only for offers this server cannot even read: if the
offer's ticket opened but `checkPsk` did not accept, it flagged `.badBinder`
(which `helloStep` makes fatal, `illegal_parameter`) — an offer with a valid
ticket and a wrong binder is never quietly downgraded to a full handshake. -/
theorem checkPsk_no_silent_downgrade (params : ServerParams) (ch : ClientHello)
    (t0 chMsg : ByteArray) (op : OfferedPsk) (info : TicketInfo)
    (hop : ch.psk = some op) (hmode : ch.pskDheKe = true)
    (hticket : (openTicket (ticketKey params.certSeed) op.identity).bind
        parseTicketInfo = some info) :
    checkPsk params ch t0 chMsg = .accepted info
    ∨ checkPsk params ch t0 chMsg = .badBinder := by
  unfold checkPsk
  rw [hop]
  simp only [hmode, Bool.not_true, Bool.false_eq_true, if_false, hticket]
  split
  · next b _hb =>
    by_cases hbeq : (op.binder == b.toList) = true
    · left; simp [hbeq]
    · right; simp [hbeq]
  · right; rfl

/-- Corollary: acceptance is exactly the MAC match. If the machine reaches
`established` from `waitClientFinished`, then `acceptClientFinished` held. -/
theorem hs_established_needs_finished (params : ServerParams) (est est' : Established)
    (buf : Tls.Bytes)
    (h : (serverStep params (.waitClientFinished est) buf).1 = .established est') :
    acceptClientFinished est (openHsRecord est.rx buf) = true := by
  simp only [serverStep] at h
  split at h
  · -- accepted-0-RTT phase: early records / EndOfEarlyData / alerts — no
    -- branch establishes, so the hypothesis is absurd.
    repeat' split at h
    all_goals simp_all
  · -- Finished phase (1-RTT, post-EndOfEarlyData, or trial-skip).
    split at h
    · next fin heq =>
      rw [heq]
      by_cases hb : acceptClientFinished est (some fin) = true
      · exact hb
      · simp only [Bool.not_eq_true] at hb
        rw [hb] at h; simp at h
    · split at h <;> simp_all

/-! ## Wiring the real message layer into `Tls.Config`

`serverHsFeed` is the `Tls.Config.hsFeed`-shaped adapter that runs the REAL
handshake message layer: it parses the ClientHello, agrees the DHE, drives the
key schedule, and emits the sealed server flight. `handshakeConfig` installs it
over `TlsCrypto.realConfig`'s real EverCrypt record layer — replacing the
shortcut `hsFeed` (which ignored the bytes and "completed on first ciphertext").
-/

/-- **The real `hsFeed`.** On accumulated ciphertext, run the server handshake
from `waitCH`: a well-formed ClientHello yields `.done` with the real server
flight (ServerHello + sealed EncryptedExtensions/Certificate/CertificateVerify/
Finished); a malformed one yields `.fail`; an empty buffer is `.insufficient`.
Unlike the shortcut, this inspects the bytes and runs real crypto. -/
def serverHsFeed (params : ServerParams) : Tls.HsConn → Tls.Bytes → Tls.HsOut :=
  fun _hs buf =>
    if buf.isEmpty then .insufficient
    else
      match serverStep params .waitCH buf with
      | (.waitClientFinished _, out) =>
        -- Surface the server flight PLAINTEXT (`out.hsPlain`) as the `HsOut`
        -- transcript contribution, so `Tls.step` accumulates
        -- `ServerHello ‖ … ‖ server Finished` into `St.transcript` (RFC 8446
        -- §4.4.1) — not only the sealed record bytes on the wire.
        .done { id := 0 } buf.length out.flight.toList .h1 [] out.hsPlain
      | (.waitCH2 _, out) =>
        -- HelloRetryRequest: the handshake continues; surface the HRR both on
        -- the wire and as its §4.4.1 transcript contribution.
        .more { id := 0 } buf.length out.flight.toList [] out.hsPlain
      | _ => .fail

/-- A `Tls.Config` whose handshake message layer is the REAL server handshake and
whose record layer is `TlsCrypto`'s real EverCrypt seal/open. The `dhe`/`thHS`/
`thAP` seed the record-direction keys exactly as `realConfig` does; the change is
`hsFeed`, now the real parser instead of the shortcut. -/
def handshakeConfig (params : ServerParams) (dhe thHS thAP : ByteArray) : Tls.Config :=
  { TlsCrypto.realConfig dhe thHS thAP with hsFeed := serverHsFeed params }

/-- **The config's `hsFeed` is the real handshake layer** — not the shortcut. -/
theorem handshakeConfig_hsFeed (params : ServerParams) (dhe thHS thAP : ByteArray) :
    (handshakeConfig params dhe thHS thAP).hsFeed = serverHsFeed params := rfl

/-- **The real `hsFeed` inspects the bytes.** On an empty buffer it is
`.insufficient` — whereas `realConfig`'s shortcut is also `.insufficient` there,
but on any *nonempty* buffer the shortcut returns `.done` unconditionally while
`serverHsFeed` runs the parser and returns `.fail` on a non-ClientHello. This
witnesses that the two `hsFeed`s are different functions. -/
theorem serverHsFeed_rejects_non_clienthello (params : ServerParams)
    (hs : Tls.HsConn) :
    serverHsFeed params hs [0x00] = .fail := by
  simp only [serverHsFeed, serverStep, parseClientHello]
  rfl

/-- The shortcut `hsFeed` of `realConfig`, by contrast, "completes" on that same
byte — the exact behaviour this module replaces. -/
theorem realConfig_shortcut_completes (dhe thHS thAP : ByteArray) (hs : Tls.HsConn) :
    (TlsCrypto.realConfig dhe thHS thAP).hsFeed hs [0x00]
      = .done { id := 0 } 1 [] .h1 [] [] := rfl

end TlsHandshake
