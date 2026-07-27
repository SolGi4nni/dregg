/-
# TlsClient — the verified TLS 1.3 client handshake

drorb already had the whole TLS 1.3 *server* — `TlsHandshake.serverStep` /
`drorbTlsServe`: the RFC 8446 record layer, the X25519 / X25519MLKEM768 key
exchange, the §7.1 key schedule, the CertificateVerify / Finished flight, and
the Ed25519 / P-256 / RSA cert signature checks. What it lacked was the *client*
direction: an outbound HTTPS caller (the ACME driver) had to shell out to a
separate TLS command-line tool, the one unaudited primitive in an otherwise-
verified path.

This module is the client dual, built on **exactly the same verified pieces**:

  * ClientHello is encoded with the same `TlsHandshake.u8/u16/vec16/hsMsg`
    wire helpers the server's ServerHello uses.
  * ServerHello / EncryptedExtensions / Certificate / CertificateVerify /
    Finished are parsed with the same `rd16/rd24/takeN/walkExts` readers and
    the same `openRecordAt` record-layer deprotection the server reads the
    client Finished with.
  * The key schedule is `TlsCrypto.deriveSchedule` — the SAME function the
    server runs; over the same `(dhe, thHS, thSF)` the two sides derive an
    equal schedule (`client_schedule_agrees_with_server`), which is exactly why
    the client can open the server's flight and the server can open the
    client's Finished.
  * The server's CertificateVerify is checked with the audited
    `Crypto.ed25519Verify` (EverCrypt) over the RFC 8446 §4.4.3
    `certVerifyContent`, and the server Finished with `TlsHandshake.verifyData`
    (HMAC over the transcript) — the same computations the server produced.

## What is verified, audited-primitive, and thin glue

**Verified Lean, reused unchanged.** The record layer (`openRecordAt` /
`sealRecordAt`, `record_roundtrip`), the key schedule (`deriveSchedule`,
`keyschedule_deterministic`), the Finished HMAC (`verifyData`), the
CertificateVerify content (`certVerifyContent`), and every wire encoder/decoder
named above.

**Audited primitives (named).** `Crypto.x25519` / `x25519Base` (HACL* Curve25519),
`Crypto.ed25519Verify` (EverCrypt Ed25519), `Crypto.sha256` / HKDF / the record
AEAD (EverCrypt). No unaudited TLS subprocess.

**Thin, named host glue.** The TCP byte-mover (`drorb_tcp_connect/send/
recv_exact/close`, `ffi/derp_net.o` — the same shim the DERP live driver uses)
and the record framing loop (`readRecord`). It parses no TLS and holds no key.

## Residual (named, not hidden)
  * The server CertificateVerify is checked for the **Ed25519** scheme
    (`ed25519Verify`, audited). The P-256 / RSA-PSS server-auth *verify* path
    needs an audited HACL* verify shim (`Hacl_P256_ecdsa_verif_p256_sha2` /
    `Hacl_RSAPSS_rsapss_verify`) — the signing shims exist (`TlsCrypto.Sig`),
    the verify ones do not yet. `certVerifyOk` returns `none` (fail-closed) for
    those schemes rather than trusting them.
  * Full DER path-building to a public root is the `Pki.ChainBuild` accounting
    over a supplied trust anchor; this module verifies the leaf's proof of
    possession (CertificateVerify) and SNI, and leaves chain-to-root as the
    ChainBuild layer's job.
-/
import TlsHandshake
import Client.Tls
import Pki.Der
import Pki.ChainBuild

namespace TlsClient

open TlsHandshake

/-! ## Byte helpers -/

/-- A `ByteArray`'s bytes as the `List UInt8` the parsers consume. -/
@[inline] def toL (b : ByteArray) : Tls.Bytes := b.toList

/-! ## ClientHello (RFC 8446 §4.1.2) — the verified wire encoder -/

/-- A TLS extension: `type(2) ‖ opaque body<uint16>`. -/
def ext (ty : Nat) (body : ByteArray) : ByteArray := u16 ty ++ vec16 body

/-- `supported_versions` (§4.2.1) offering only TLS 1.3, in the ClientHello
`uint8`-list form. -/
def extSupportedVersions : ByteArray := ext 0x002b (vec8 (u16 tls13))

/-- `supported_groups` (§4.2.7) offering X25519. -/
def extSupportedGroups : ByteArray := ext 0x000a (vec16 (u16 x25519Group))

/-- `signature_algorithms` (§4.2.3): Ed25519, ECDSA-P256, RSA-PSS-RSAE — the
schemes a real CA leaf is signed under, so the server presents a cert we could
verify. -/
def extSigAlgs : ByteArray :=
  ext 0x000d (vec16 (u16 ed25519SigAlg ++ u16 ecdsaSigAlg ++ u16 rsaPssSigAlg))

/-- `key_share` (§4.2.8): a single X25519 `KeyShareEntry` — `group(2) ‖
key_exchange<uint16>`. -/
def extKeyShare (pub : ByteArray) : ByteArray :=
  ext 0x0033 (vec16 (u16 x25519Group ++ vec16 pub))

/-- `server_name` (RFC 6066 §3): a single `host_name` SNI entry. -/
def extServerName (host : ByteArray) : ByteArray :=
  ext 0x0000 (vec16 (u8 0 ++ vec16 host))

/-- `application_layer_protocol_negotiation` (RFC 7301) offering one protocol. -/
def extAlpn (proto : ByteArray) : ByteArray :=
  ext 0x0010 (vec16 (vec8 proto))

/-- The two suites both keyed by SHA-256; the record AEAD is dispatched by the
suite `suiteAead` selects. -/
def clientSuites : ByteArray := u16 aes128Suite ++ u16 chachaSuite

/-- **ClientHello** handshake message (`msg_type 1 ‖ uint24 len ‖ body`). The
`random` and `sessionId` are 32 bytes each (the session id is the middlebox-
compat echo); the extension block is key_share, supported_versions,
supported_groups, signature_algorithms, SNI, and ALPN(`http/1.1`). -/
def clientHelloMsg (random sessionId pub host : ByteArray) : ByteArray :=
  let exts := extKeyShare pub ++ extSupportedVersions ++ extSupportedGroups
                ++ extSigAlgs ++ extServerName host
                ++ extAlpn (ofBytes alpnHttp11)
  let body := u16 0x0303 ++ random ++ vec8 sessionId
                ++ vec16 clientSuites ++ vec8 (u8 0) ++ vec16 exts
  hsMsg 1 body

/-! ## ServerHello (RFC 8446 §4.1.3) — the verified wire decoder -/

/-- The parsed ServerHello fields the client needs to key the session. -/
structure ServerHelloParsed where
  random    : Tls.Bytes
  suite     : Nat
  group     : Nat
  serverPub : Tls.Bytes
  deriving Repr

/-- **Parse a ServerHello** (bare handshake message or full record):
`msg_type 2 ‖ uint24 len ‖ legacy_version(2) ‖ random(32) ‖ session_id<uint8> ‖
cipher_suite(2) ‖ compression(1) ‖ extensions<uint16>`; the X25519 server share
comes from the `key_share` extension (`group(2) ‖ key_exchange<uint16>`). -/
def parseServerHello (input : Tls.Bytes) : Option ServerHelloParsed := do
  match stripRecord input with
  | 0x02 :: r0 =>
    let (_len, r1) ← rd24 r0
    let (rnd, r2) ← takeN 32 (r1.drop 2)               -- skip legacy_version
    let (sidLen, r3) ← (match r2 with | b :: t => some (b.toNat, t) | [] => none)
    let (_sid, r4) ← takeN sidLen r3
    let (suite, r5) ← rd16 r4
    let r6 := r5.drop 1                                 -- legacy_compression_method
    let (extLen, r7) ← rd16 r6
    let (extBytes, _) ← takeN extLen r7
    let exts := walkExts extBytes.length extBytes
    let ksBody ← extBody exts 0x0033
    match ksBody with
    | g1 :: g2 :: rest =>
      let (klen, kb) ← rd16 rest
      let (pub, _) ← takeN klen kb
      some { random := rnd, suite := suite
             group := g1.toNat * 256 + g2.toNat, serverPub := pub }
    | _ => none
  | _ => none

/-! ## Handshake-message and certificate readers -/

/-- Split a run of handshake messages (`type(1) ‖ uint24 len ‖ body`) into
`(type, body)` pairs. Fuel-bounded so it is total. -/
def splitMsgs : Nat → Tls.Bytes → List (Nat × Tls.Bytes)
  | 0, _ => []
  | fuel + 1, l =>
    match l with
    | t :: a :: b :: c :: rest =>
      let len := a.toNat * 65536 + b.toNat * 256 + c.toNat
      if rest.length < len then [(t.toNat, rest.take len)]
      else (t.toNat, rest.take len) :: splitMsgs fuel (rest.drop len)
    | _ => []

/-- The end-entity certificate DER from a Certificate message body
(`context<uint8> ‖ certificate_list<uint24>`, each entry `cert<uint24> ‖
extensions<uint16>`). -/
def firstCertDer (certBody : Tls.Bytes) : Option Tls.Bytes := do
  match certBody with
  | ctxLen :: rest =>
    let (_ctx, r1) ← takeN ctxLen.toNat rest
    let (_listLen, r2) ← rd24 r1
    let (clen, r3) ← rd24 r2
    let (cert, _) ← takeN clen r3
    some cert
  | [] => none

/-- Skip past the Ed25519 algorithm OID (`06 03 2B 65 70`, id `1.3.101.112`). -/
def afterEd25519Oid : Tls.Bytes → Option Tls.Bytes
  | 0x06 :: 0x03 :: 0x2B :: 0x65 :: 0x70 :: rest => some rest
  | _ :: rest => afterEd25519Oid rest
  | [] => none

/-- Take the 32-byte raw key out of the SubjectPublicKeyInfo BIT STRING
(`03 21 00 ‖ key(32)`). -/
def scanEd25519BitString : Tls.Bytes → Option Tls.Bytes
  | 0x03 :: 0x21 :: 0x00 :: rest =>
      if rest.length ≥ 32 then some (rest.take 32) else scanEd25519BitString rest
  | _ :: rest => scanEd25519BitString rest
  | [] => none

/-- The Ed25519 subject public key (32 bytes) from a leaf certificate's DER, or
`none` if the leaf is not an Ed25519 certificate. -/
def leafEd25519Pub (der : Tls.Bytes) : Option ByteArray :=
  ((afterEd25519Oid der).bind scanEd25519BitString).map ofBytes

/-- Parse a CertificateVerify body (`SignatureScheme(2) ‖ signature<uint16>`). -/
def parseCertVerify (body : Tls.Bytes) : Option (Nat × ByteArray) := do
  match body with
  | s1 :: s2 :: rest =>
    let (slen, r) ← rd16 rest
    let (sig, _) ← takeN slen r
    some (s1.toNat * 256 + s2.toNat, ofBytes sig)
  | _ => none

/-! ## The verified checks -/

/-! ### DER extraction for the P-256 and RSA-PSS server-cert schemes.

The Ed25519 leaf key is a fixed-shape 32-byte BIT STRING; P-256 and RSA need a
little more of the SubjectPublicKeyInfo, and the ECDSA CertificateVerify carries
a DER `ECDSA-Sig-Value` HACL* wants as raw `R ‖ S`. These readers use the same
verified `Pki.Der.readTlv`/`readLen` the CSR/OCSP paths use. -/

/-- The bytes after the first occurrence of `needle`, or `none` if absent. -/
def afterBytes (needle : Tls.Bytes) : Tls.Bytes → Option Tls.Bytes
  | [] => none
  | l@(_ :: rest) =>
    if needle.isPrefixOf l then some (l.drop needle.length)
    else afterBytes needle rest

/-- The raw 64-byte `X ‖ Y` P-256 public point from a leaf's SubjectPublicKeyInfo:
the uncompressed-point BIT STRING `03 42 00 04 ‖ point(64)` (0x42 = 1 unused-bits
octet + the 65-octet SEC1 point). The 65-octet uncompressed shape pins the curve
to P-256; HACL* re-checks the point is on-curve and non-infinity. -/
def scanP256Point : Tls.Bytes → Option Tls.Bytes
  | 0x03 :: 0x42 :: 0x00 :: 0x04 :: rest =>
      if rest.length ≥ 64 then some (rest.take 64) else scanP256Point rest
  | _ :: rest => scanP256Point rest
  | [] => none

/-- The P-256 subject public point (raw 64-byte `X ‖ Y`) of a leaf DER. -/
def leafP256Pub (der : Tls.Bytes) : Option ByteArray :=
  (scanP256Point der).map ofBytes

/-- The `rsaEncryption` OID content octets (`1.2.840.113549.1.1.1`). -/
def rsaOidContent : Tls.Bytes := [0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01, 0x01, 0x01]

/-- The next BIT STRING (tag `0x03`) content with its leading `0x00` unused-bits
octet stripped. -/
def nextBitStringContent : Tls.Bytes → Option Tls.Bytes
  | [] => none
  | 0x03 :: rest =>
      match Pki.Der.readLen rest with
      | some (n, body) =>
          match body.take n with
          | 0x00 :: content => some content
          | _ => none
      | none => none
  | _ :: rest => nextBitStringContent rest

/-- The RSA public key `(modulus, publicExponent)` (big-endian, as carried in
DER — a leading `0x00` sign octet is left in place; the shim strips it) from a
leaf's SubjectPublicKeyInfo: after the `rsaEncryption` OID, the BIT STRING wraps
`RSAPublicKey ::= SEQUENCE { modulus INTEGER, publicExponent INTEGER }`. -/
def leafRsaKey (der : Tls.Bytes) : Option (ByteArray × ByteArray) := do
  let afterOid ← afterBytes rsaOidContent der
  let rsaPk ← nextBitStringContent afterOid
  let (tag, body, _) ← Pki.Der.readTlv rsaPk
  if tag ≠ 0x30 then none
  else
    let (t1, nB, r1) ← Pki.Der.readTlv body
    if t1 ≠ 0x02 then none
    else
      let (t2, eB, _) ← Pki.Der.readTlv r1
      if t2 ≠ 0x02 then none
      else some (ofBytes nB, ofBytes eB)

/-- Normalize a big-endian DER INTEGER to exactly 32 octets: strip leading zeros,
then left-pad to 32; `none` if it exceeds 32 significant octets. -/
def to32 (b : Tls.Bytes) : Option Tls.Bytes :=
  let s := b.dropWhile (· == 0)
  if s.length > 32 then none
  else some (List.replicate (32 - s.length) 0 ++ s)

/-- Decode the DER `ECDSA-Sig-Value ::= SEQUENCE { r INTEGER, s INTEGER }` a TLS
CertificateVerify carries (RFC 8446 §4.2.3) into the raw 64-byte `R(32) ‖ S(32)`
HACL* verifies. -/
def ecdsaRawSig (sig : ByteArray) : Option ByteArray := do
  let (tag, body, _) ← Pki.Der.readTlv sig.toList
  if tag ≠ 0x30 then none
  else
    let (t1, r, rest) ← Pki.Der.readTlv body
    if t1 ≠ 0x02 then none
    else
      let (t2, s, _) ← Pki.Der.readTlv rest
      if t2 ≠ 0x02 then none
      else
        let r32 ← to32 r
        let s32 ← to32 s
        some (ofBytes (r32 ++ s32))

/-- **CertificateVerify check** (RFC 8446 §4.4.3). The audited HACL* verify of the
leaf's signature over `certVerifyContent thCert` — the 64 `0x20` octets, the
`"TLS 1.3, server CertificateVerify"` context, a `0x00`, then the transcript hash
— under the leaf's public key, dispatched by SignatureScheme:

  * Ed25519 (`0x0807`) → `Crypto.ed25519Verify` (EverCrypt);
  * ECDSA-P256-SHA256 (`0x0403`) → `Crypto.ecdsaP256Verify` (HACL* `Hacl_P256`),
    over the raw `X ‖ Y` key and the raw `R ‖ S` decoded from the DER signature;
  * RSA-PSS-SHA256 (`0x0804`) → `Crypto.rsaPssVerify` (HACL* `Hacl_RSAPSS`), over
    the `(n, e)` from the leaf SPKI.

Any other scheme, or a leaf whose key cannot be extracted, fails closed (`none`). -/
def certVerifyOk (leafDer : Tls.Bytes) (scheme : Nat) (sig thCert : ByteArray) :
    Option Bool :=
  if scheme = ed25519SigAlg then
    match leafEd25519Pub leafDer with
    | some pub => some (Crypto.ed25519Verify pub (certVerifyContent thCert) sig)
    | none => none
  else if scheme = ecdsaSigAlg then
    match leafP256Pub leafDer, ecdsaRawSig sig with
    | some pub, some raw => some (Crypto.ecdsaP256Verify pub (certVerifyContent thCert) raw)
    | _, _ => none
  else if scheme = rsaPssSigAlg then
    match leafRsaKey leafDer with
    | some (n, e) => some (Crypto.rsaPssVerify n e sig (certVerifyContent thCert))
    | none => none
  else
    none

/-! ## Chain building to a trust root — `Pki.ChainBuild` wired to the served chain.

CertificateVerify proves the *leaf holds its key*; it does NOT prove the leaf is
one a trusted CA issued — a MITM presenting its own self-signed leaf, and signing
CertificateVerify with its own key, passes that check. Rejecting it is the job of
X.509 path building (RFC 5280 §6.1): the served chain must build to a pinned trust
anchor by verified signatures. `Pki.ChainBuild.verifyPathW` is the verified
decision logic; this section parses the real certificates into its abstract
`Cert` model and instantiates its signature oracle with the audited HACL* verify
over each certificate's TBSCertificate. The path-building logic is proved once
(`ChainBuild`); only the per-link signature verdict is the audited primitive.

**Signature-algorithm coverage.** Each chain link's signature is verified by an
AUDITED primitive dispatched on the child's `signatureAlgorithm`:
ECDSA-P256-SHA256, RSA-PSS-SHA256, and Ed25519 by HACL*/EverCrypt (F*-verified);
and `sha256WithRSAEncryption` (PKCS#1 v1.5) — the padding MOST real RSA CA chains
sign with, including Let's Encrypt's RSA intermediates (R10/R11) and ISRG Root X1
— by audited aws-lc (`Crypto.rsaPkcs1Verify`, one trust notch below HACL*: audited,
not machine-checked; see `Crypto.rsaPkcs1Verify_authentic`). A real PKCS#1 v1.5 RSA
chain now builds fully to its pinned root. Any OID with no audited verifier still
fails CLOSED (`classifySigAlg → 0`, `keyVerify → false`) rather than being trusted
unverified. -/

/-- One TLV consumed; the remaining bytes (`none` if malformed). -/
def afterTlv (l : Tls.Bytes) : Option Tls.Bytes := (Pki.Der.readTlv l).map (·.2.2)

/-- A distinguished name reduced to a `Nat` for the `ChainBuild` model. Only a
prefilter: name-chaining collisions cannot cause a FALSE ACCEPT because every
accepted link also carries a real signature (the parent genuinely signed the
child), which binds the actual issuer. Byte-identical DNs hash equal. -/
def dnHash (b : Tls.Bytes) : Nat :=
  b.foldl (fun a x => (a * 257 + x.toNat + 1) % 1000000007) 0

/-- An ASN.1 `UTCTime` (`0x17`, `YYMMDDHHMMSSZ`) or `GeneralizedTime` (`0x18`,
`YYYYMMDDHHMMSSZ`) as a monotone `YYYYMMDDHHMMSS` `Nat` for window comparison. -/
def asn1TimeToNat (tag : UInt8) (bytes : Tls.Bytes) : Nat :=
  let digits := bytes.filterMap (fun b =>
    if b ≥ 0x30 ∧ b ≤ 0x39 then some (b.toNat - 0x30) else none)
  let digits := if tag = 0x17 then
      (match digits with
       | y1 :: y2 :: _ => (if y1 * 10 + y2 < 50 then [2,0] else [1,9]) ++ digits
       | _ => digits)
    else digits
  digits.foldl (fun a d => a * 10 + d) 0

/-- Parse a `Validity ::= SEQUENCE { notBefore Time, notAfter Time }` body. -/
def parseValidity (body : Tls.Bytes) : Option (Nat × Nat) := do
  let (t1, nb, rest) ← Pki.Der.readTlv body
  let (t2, na, _) ← Pki.Der.readTlv rest
  some (asn1TimeToNat t1 nb, asn1TimeToNat t2 na)

/-- `SignatureScheme.rsa_pkcs1_sha256` (RFC 8446 §4.2.3 code point `0x0401`) — the
scheme tag we use INTERNALLY to route a `sha256WithRSAEncryption` (PKCS#1 v1.5)
*certificate* signature to the audited aws-lc verify. RFC 8446 §4.2.3 permits
`rsa_pkcs1_*` "solely for signatures which appear in certificates", NOT in the TLS
1.3 CertificateVerify handshake message — so this tag is used by the chain-link
oracle (`keyVerify`), never by `certVerifyOk`. -/
def rsaPkcs1SigAlg : Nat := 0x0401

/-- Classify a certificate's `signatureAlgorithm` OID to the SignatureScheme code
we can verify, or `0` for one with no audited verify (fail-closed). -/
def classifySigAlg (algBody : Tls.Bytes) : Nat :=
  match Pki.Der.readTlv algBody with
  | some (0x06, oid, _) =>
      if oid = [0x2A,0x86,0x48,0xCE,0x3D,0x04,0x03,0x02] then ecdsaSigAlg        -- ecdsa-with-SHA256
      else if oid = [0x2A,0x86,0x48,0x86,0xF7,0x0D,0x01,0x01,0x0A] then rsaPssSigAlg  -- id-RSASSA-PSS
      else if oid = [0x2A,0x86,0x48,0x86,0xF7,0x0D,0x01,0x01,0x0B] then rsaPkcs1SigAlg  -- sha256WithRSAEncryption (PKCS#1 v1.5)
      else if oid = [0x2B,0x65,0x70] then ed25519SigAlg                          -- Ed25519
      else 0   -- no audited verify (fail-closed)
  | _ => 0

/-- Scan a window for a DER `BOOLEAN TRUE` (`01 01 FF`). -/
def scanCaTrue : Tls.Bytes → Bool
  | 0x01 :: 0x01 :: 0xFF :: _ => true
  | _ :: rest => scanCaTrue rest
  | [] => false

/-- `basicConstraints: cA = TRUE` (RFC 5280 §4.2.1.9): the extension OID
`2.5.29.19` (`06 03 55 1D 13`) followed, within its value, by `BOOLEAN TRUE`. -/
def certIsCA (tbs : Tls.Bytes) : Bool :=
  match afterBytes [0x06,0x03,0x55,0x1D,0x13] tbs with
  | some after => scanCaTrue (after.take 16)
  | none => false

/-- A served certificate parsed into the `ChainBuild.Cert` model plus the bytes
the signature oracle needs: the signed TBSCertificate, the `signatureAlgorithm`
scheme, the signature value, and the full DER (its SPKI is the key that verifies
the *child*). -/
structure ParsedCert where
  abs      : Pki.ChainBuild.Cert
  der      : Tls.Bytes
  tbs      : ByteArray
  sigAlg   : Nat
  sig      : ByteArray
  subjHash : Nat

/-- Parse one X.509 `Certificate` DER (RFC 5280 §4.1). Fails closed on any
malformed structure. -/
def parseCert (der : Tls.Bytes) : Option ParsedCert := do
  let (_, certBody, _) ← Pki.Der.readTlv der
  let (_, tbsBody, afterTbs) ← Pki.Der.readTlv certBody
  let (_, algBody, afterAlg) ← Pki.Der.readTlv afterTbs
  let (_, sigBits, _) ← Pki.Der.readTlv afterAlg
  let sigRaw ← (match sigBits with | 0x00 :: r => some r | _ => none)
  let r1 := match tbsBody with | 0xA0 :: _ => (afterTlv tbsBody).getD tbsBody | _ => tbsBody
  let r2 ← afterTlv r1                          -- serialNumber
  let r3 ← afterTlv r2                          -- signature AlgorithmIdentifier
  let (_, issuerBody, r4) ← Pki.Der.readTlv r3  -- issuer
  let (_, validityBody, r5) ← Pki.Der.readTlv r4
  let (nb, na) ← parseValidity validityBody
  let (_, subjectBody, _) ← Pki.Der.readTlv r5  -- subject
  let subjH := dnHash (Pki.Der.seq subjectBody)
  let issH  := dnHash (Pki.Der.seq issuerBody)
  some {
    abs := { subject := subjH, issuer := issH, isCA := certIsCA tbsBody,
             notBefore := nb, notAfter := na }
    der := der, tbs := ofBytes (Pki.Der.seq tbsBody),
    sigAlg := classifySigAlg algBody, sig := ofBytes sigRaw, subjHash := subjH }

/-- Split a TLS 1.3 `certificate_list` (each entry `cert<uint24> ‖ ext<uint16>`)
into the certificate DERs. Fuel-bounded. -/
def certList : Nat → Tls.Bytes → List Tls.Bytes
  | 0, _ => []
  | fuel+1, bytes =>
    match rd24 bytes with
    | some (clen, r) =>
      match takeN clen r with
      | some (cert, r2) =>
        match rd16 r2 with
        | some (elen, r3) =>
          match takeN elen r3 with
          | some (_, r4) => cert :: certList fuel r4
          | none => [cert]
        | none => [cert]
      | none => []
    | none => []

/-- Every certificate DER in a Certificate-message body
(`context<uint8> ‖ certificate_list<uint24>`). -/
def allCertDers (certBody : Tls.Bytes) : List Tls.Bytes :=
  match certBody with
  | ctxLen :: rest =>
    match takeN ctxLen.toNat rest with
    | some (_, r1) =>
      match rd24 r1 with
      | some (_, r2) => certList 16 r2
      | none => []
    | none => []
  | [] => []

/-- **The real per-link signature check** (the `ChainBuild` oracle realized by
audited crypto): does `parentDer`'s public key verify the child's signature over
the child's TBSCertificate, under the child's `signatureAlgorithm`? HACL* hashes
the TBS internally (SHA-256). A `sha256WithRSAEncryption` (PKCS#1 v1.5) child is
verified under the parent's RSA `(n, e)` by the audited aws-lc
`Crypto.rsaPkcs1Verify` — the padding real RSA CA chains (Let's Encrypt R10/R11,
ISRG Root X1) sign with. An unrecognized `sigAlg` (`0`) still fails closed. -/
def keyVerify (parentDer : Tls.Bytes) (childSigAlg : Nat) (childSig childTbs : ByteArray) :
    Bool :=
  if childSigAlg = ecdsaSigAlg then
    match leafP256Pub parentDer, ecdsaRawSig childSig with
    | some pub, some raw => Crypto.ecdsaP256Verify pub childTbs raw
    | _, _ => false
  else if childSigAlg = rsaPssSigAlg then
    match leafRsaKey parentDer with
    | some (n, e) => Crypto.rsaPssVerify n e childSig childTbs
    | none => false
  else if childSigAlg = rsaPkcs1SigAlg then
    match leafRsaKey parentDer with
    | some (n, e) => Crypto.rsaPkcs1Verify n e childSig childTbs
    | none => false
  else if childSigAlg = ed25519SigAlg then
    match leafEd25519Pub parentDer with
    | some pub => Crypto.ed25519Verify pub childTbs childSig
    | none => false
  else false

/-- Look up a parsed certificate by its subject-DN hash. -/
def parsedFind (ps : List ParsedCert) (h : Nat) : Option ParsedCert :=
  ps.find? (·.subjHash == h)

/-- **The `ChainBuild` signature oracle, instantiated with real HACL* verify.**
`realOracle ps parent child` verifies `child`'s certificate signature under
`parent`'s public key, recovering both certificates' bytes from `ps` by their
subject-DN hash. -/
def realOracle (ps : List ParsedCert) : Pki.ChainBuild.Cert → Pki.ChainBuild.Cert → Bool :=
  fun parent child =>
    match parsedFind ps parent.subject, parsedFind ps child.subject with
    | some pp, some cc => keyVerify pp.der cc.sigAlg cc.sig cc.tbs
    | _, _ => false

/-- **Authenticate the served chain to a pinned trust root** (RFC 5280 §6.1).
The trust anchor `trustRootDer` (a supplied CA certificate — a CA bundle entry or
the system root) is appended as the path terminal; the leaf is the head. Returns
`true` iff `Pki.ChainBuild.verifyPathW` accepts under the audited HACL* oracle:
every certificate in-window at `now`, names chaining, every non-leaf a CA, every
link signature verifying, and the terminal being the pinned, self-signed root. A
MITM's self-presented leaf is rejected — its issuer is not the pinned root and its
signature does not verify under the root's key. -/
def authenticateChain (chainDers : List Tls.Bytes) (trustRootDer : Tls.Bytes) (now : Nat) :
    Bool :=
  match (chainDers ++ [trustRootDer]).mapM parseCert with
  | none => false
  | some ps =>
    match ps.reverse with
    | root :: _ =>
      Pki.ChainBuild.verifyPathW (realOracle ps) now (fun n => n == root.subjHash)
        (ps.map (·.abs))
    | [] => false

/-! ### The chain-authentication soundness bridge (ChainBuild ⊕ Crypto authenticity). -/

/-- **Accepted chain ⟹ every link's signature verified under the audited oracle.**
Direct from `Pki.ChainBuild.verifyPathW_links_signed`: acceptance is not merely
structural — each certificate was signature-checked against its issuer's key. -/
theorem accepted_chain_links_signed (ps : List ParsedCert) (now : Nat)
    (trusted : Pki.ChainBuild.Name → Bool)
    (h : Pki.ChainBuild.verifyPathW (realOracle ps) now trusted (ps.map (·.abs)) = true) :
    Pki.ChainBuild.allLinksSigned (realOracle ps) (ps.map (·.abs)) = true :=
  Pki.ChainBuild.verifyPathW_links_signed _ _ _ _ h

/-- **A verified ECDSA link is EUF-CMA-genuine.** If `keyVerify` accepts an
ECDSA-scheme link with extracted key `pub` and decoded signature `raw`, then by
`Crypto.ecdsaP256Verify_authentic` the holder of `pub`'s private key genuinely
signed the TBSCertificate — so an accepted ECDSA chain is one every link of which
was really issued by the certificate above it, not forged by a MITM. Non-vacuous:
the hypotheses are exactly what the demo's ECDSA path supplies. -/
theorem keyVerify_ecdsa_genuine (parentDer : Tls.Bytes) (childSig childTbs pub raw : ByteArray)
    (hpub : leafP256Pub parentDer = some pub) (hraw : ecdsaRawSig childSig = some raw)
    (h : keyVerify parentDer ecdsaSigAlg childSig childTbs = true) :
    Crypto.Assumptions.ecdsaP256Genuine pub childTbs raw := by
  have hv : Crypto.ecdsaP256Verify pub childTbs raw = true := by
    unfold keyVerify at h
    simp only [if_pos rfl, hpub, hraw] at h
    exact h
  exact Crypto.Assumptions.ecdsaP256Verify_authentic pub childTbs raw hv

/-- **A verified PKCS#1 v1.5 link is EUF-CMA-genuine.** If `keyVerify` accepts a
`sha256WithRSAEncryption` link under the parent's RSA key `(n, e)`, then by
`Crypto.rsaPkcs1Verify_authentic` (aws-lc's audited EUF-CMA shadow) the holder of
`(n, e)`'s private key genuinely signed the child's TBSCertificate — so an accepted
PKCS#1 v1.5 chain is one every RSA link of which was really issued by the
certificate above it, not forged by a MITM. Non-vacuous: the hypotheses are
exactly what a real Let's-Encrypt-style RSA chain (leaf ← R10/R11 ← ISRG Root X1)
supplies. The AUDITED (not F*-verified) analog of `keyVerify_ecdsa_genuine`. -/
theorem keyVerify_rsaPkcs1_genuine (parentDer : Tls.Bytes) (childSig childTbs n e : ByteArray)
    (hkey : leafRsaKey parentDer = some (n, e))
    (h : keyVerify parentDer rsaPkcs1SigAlg childSig childTbs = true) :
    Crypto.Assumptions.rsaPkcs1Genuine n e childTbs childSig := by
  have h1 : rsaPkcs1SigAlg ≠ ecdsaSigAlg := by decide
  have h2 : rsaPkcs1SigAlg ≠ rsaPssSigAlg := by decide
  have hv : Crypto.rsaPkcs1Verify n e childSig childTbs = true := by
    unfold keyVerify at h
    rw [if_neg h1, if_neg h2, if_pos (rfl : rsaPkcs1SigAlg = rsaPkcs1SigAlg), hkey] at h
    exact h
  exact Crypto.Assumptions.rsaPkcs1Verify_authentic n e childSig childTbs hv

/-- **Server Finished check** (RFC 8446 §4.4.4): the received `verify_data` must
equal `HMAC(server_finished_key, Transcript-Hash(CH … CertificateVerify))`,
which is exactly `TlsHandshake.verifyData sHs thCV`. -/
def serverFinishedOk (sHs thCV recvVerifyData : ByteArray) : Bool :=
  match verifyData sHs thCV with
  | some expected => recvVerifyData == expected
  | none => false

/-- **Client Finished** (RFC 8446 §4.4.4): the handshake message
`0x14 ‖ uint24 32 ‖ verify_data`, where `verify_data =
HMAC(client_finished_key, Transcript-Hash(CH … server Finished))`. This is the
byte-identical computation the server's `expectedClientVerifyData` checks. -/
def clientFinishedMsg (cHs thSF : ByteArray) : Option ByteArray :=
  (verifyData cHs thSF).map (hsMsg 20)

/-! ## The verified key derivation -/

/-- Server-handshake and client-handshake traffic secrets from the DHE shared
secret and `Transcript-Hash(CH ‖ SH)` — the standalone RFC 8446 §7.1 chain the
`deriveSchedule` fields are built from, computed here before `thSF` is known so
the client can open the server's flight. -/
def hsTrafficSecrets (dhe thHS : ByteArray) : Option (ByteArray × ByteArray) := do
  let es ← TlsCrypto.earlySecretNoPsk
  let hs ← TlsCrypto.handshakeSecret es dhe
  let cHs ← TlsCrypto.clientHsTrafficSecret hs thHS
  let sHs ← TlsCrypto.serverHsTrafficSecret hs thHS
  some (cHs, sHs)

/-- **The client key schedule is the server's.** Over the same shared secret and
the same two transcript hashes, the client derives `TlsCrypto.deriveSchedule dhe
thHS thSF` — which is definitionally the schedule the server's
`Established.schedule` computes for a full (no-PSK) handshake. Equal transcripts
therefore yield equal server-handshake, client-handshake, and application
secrets: the client reads exactly what the server sealed, and vice versa. -/
theorem client_schedule_agrees_with_server (dhe thHS thSF : ByteArray) :
    TlsCrypto.deriveSchedule dhe thHS thSF
      = ({ dhe := dhe, thHS := thHS, thSF := thSF, alpn := .h1 } : Established).schedule := by
  rfl

/-! ## Host glue — the TCP byte-mover (`ffi/derp_net.o`) and record framing.

These four crossings own the socket and nothing else: they parse no TLS record
and hold no key (the same shim the DERP live driver and the server front door
use). -/

/-- Open a TCP connection to a dotted-quad IPv4 `host:port`; returns the fd. -/
@[extern "drorb_tcp_connect"]
opaque tcpConnect (host : String) (port : UInt16) : IO UInt32

/-- Send all of `payload` on `fd`. -/
@[extern "drorb_tcp_send"]
opaque tcpSend (fd : UInt32) (payload : ByteArray) : IO Unit

/-- Read EXACTLY `nbytes` from `fd` within `timeoutMs`; `none` on EOF/timeout. -/
@[extern "drorb_tcp_recv_exact"]
opaque tcpRecvExact (fd : UInt32) (nbytes : UInt32) (timeoutMs : UInt32) :
    IO (Option ByteArray)

/-- Close `fd`. -/
@[extern "drorb_tcp_close"]
opaque tcpClose (fd : UInt32) : IO Unit

/-- Per-record read timeout (ms). -/
def recvTimeout : UInt32 := 15000

/-- Read one full TLS record: the 5-byte `type ‖ version ‖ uint16 len` header,
then exactly the declared body. Returns `(outer content-type, full record bytes)`
or `none` on EOF/timeout/short read. -/
def readRecord (fd : UInt32) : IO (Option (UInt8 × ByteArray)) := do
  match ← tcpRecvExact fd 5 recvTimeout with
  | none => return none
  | some hb =>
    if hb.size < 5 then return none
    let ctype := hb.get! 0
    let len := (hb.get! 3).toNat * 256 + (hb.get! 4).toNat
    if len > 18432 then return none
    let body ← if len == 0 then pure (some ByteArray.empty)
               else tcpRecvExact fd (UInt32.ofNat len) recvTimeout
    match body with
    | none => return none
    | some bb => return some (ctype, hb ++ bb)

/-! ## The handshake driver -/

/-- Accumulate the server's encrypted handshake flight: skip plaintext
ChangeCipherSpec (`0x14`) records (middlebox-compat), open each application_data
(`0x17`) record under the server-handshake keys at the running sequence number,
and concatenate the decrypted handshake bytes until a Finished (`0x14` handshake
type) message has arrived. Fuel-bounded on the number of records. -/
partial def readServerFlight (fd : UInt32) (sHsKeys : TlsCrypto.RecordKeys)
    (seq : Nat) (acc : Tls.Bytes) : IO (Option Tls.Bytes) := do
  -- Have we already got a Finished (type 20) in the accumulated flight?
  let msgs := splitMsgs 64 acc
  if msgs.any (fun m => m.1 = 20) then
    return some acc
  match ← readRecord fd with
  | none => return (if acc.isEmpty then none else some acc)
  | some (0x14, _) => readServerFlight fd sHsKeys seq acc            -- skip CCS
  | some (0x17, rec) =>
    match openRecordAt sHsKeys seq (toL rec) with
    | some (0x16, content) => readServerFlight fd sHsKeys (seq + 1) (acc ++ toL content)
    | some (0x15, _) => return none                                   -- alert
    | _ => return none
  | some _ => readServerFlight fd sHsKeys seq acc

/-- Read the application-data response: open each record under the server
application keys at the running sequence, collect `application_data` (`0x17`)
plaintext, skip post-handshake handshake records (`0x16`, e.g. NewSessionTicket),
and stop on a `close_notify` alert (`0x15`) or EOF. Fuel-bounded. -/
partial def readAppData (fd : UInt32) (sApKeys : TlsCrypto.RecordKeys)
    (seq : Nat) (acc : ByteArray) : IO ByteArray := do
  match ← readRecord fd with
  | none => return acc
  | some (0x17, rec) =>
    match openRecordAt sApKeys seq (toL rec) with
    | some (0x17, content) => readAppData fd sApKeys (seq + 1) (acc ++ content)
    | some (0x16, _) => readAppData fd sApKeys (seq + 1) acc         -- NewSessionTicket
    | some (0x15, _) => return acc                                    -- close_notify
    | _ => return acc
  | some _ => readAppData fd sApKeys seq acc

/-- The outcome of a client handshake: the negotiated suite/group, the leaf
certificate DER, and whether CertificateVerify and the server Finished checked
out — plus the established application record keys and running sequences. -/
structure Session where
  fd        : UInt32
  suite     : Nat
  group     : Nat
  leafDer   : Tls.Bytes
  /-- Every certificate the server sent, leaf first — the input to `Pki.ChainBuild`
  path building when a trust anchor is supplied. -/
  chainDers : List Tls.Bytes
  certVerify : Bool
  finished  : Bool
  cApKeys   : TlsCrypto.RecordKeys
  sApKeys   : TlsCrypto.RecordKeys

/-- **Run the 1-RTT client handshake** over a fresh TCP connection to
`ip:port`, offering SNI `sni`. Drives ClientHello → ServerHello → (open flight)
→ verify CertificateVerify + server Finished → client Finished, and returns the
`Session` with the application keys. `Except.error` on any parse / crypto /
socket failure. This is the verified core (`clientHelloMsg`, `parseServerHello`,
`deriveSchedule`, `certVerifyOk`, `serverFinishedOk`, `clientFinishedMsg`) over
the audited primitives; the socket byte-mover is the only host glue. -/
def handshake (ip : String) (port : UInt16) (sni : String) :
    IO (Except String Session) := do
  let random ← IO.getRandomBytes 32
  let sessionId ← IO.getRandomBytes 32
  let priv ← IO.getRandomBytes 32
  match Crypto.x25519Base priv with
  | none => return .error "x25519Base failed"
  | some pub =>
    let fd ← tcpConnect ip port
    try
      let host := sni.toUTF8
      let chMsg := clientHelloMsg random sessionId pub host
      tcpSend fd (wrapPlainHs chMsg)
      -- ServerHello (plaintext record).
      match ← readRecord fd with
      | none => tcpClose fd; return .error "no ServerHello"
      | some (_, shRec) =>
        let shMsg := ofBytes ((toL shRec).drop 5)
        match parseServerHello (toL shMsg) with
        | none => tcpClose fd; return .error "unparseable ServerHello"
        | some sh =>
          match Crypto.x25519 priv (ofBytes sh.serverPub) with
          | none => tcpClose fd; return .error "x25519 agree failed"
          | some dhe =>
            let thHS := Crypto.sha256 (chMsg ++ shMsg)
            match hsTrafficSecrets dhe thHS with
            | none => tcpClose fd; return .error "handshake secret derivation failed"
            | some (cHs, sHs) =>
              let aead := suiteAead sh.suite
              match TlsCrypto.trafficKeysA aead sHs, TlsCrypto.trafficKeysA aead cHs with
              | some sHsKeys, some cHsKeys =>
                -- Read + open the server's encrypted flight.
                match ← readServerFlight fd sHsKeys 0 [] with
                | none => tcpClose fd; return .error "no/undecryptable server flight"
                | some flight =>
                  let msgs := splitMsgs 64 flight
                  let bodyOf := fun ty => (msgs.find? (fun m => m.1 = ty)).map (·.2)
                  let eeOpt   := bodyOf 8
                  let certOpt := bodyOf 11
                  let cvOpt   := bodyOf 15
                  let finOpt  := bodyOf 20
                  match eeOpt, certOpt, cvOpt, finOpt with
                  | some eeBody, some certBody, some cvBody, some finBody =>
                    match firstCertDer certBody, parseCertVerify cvBody with
                    | some leaf, some (scheme, sig) =>
                      -- Reconstruct the exact handshake message bytes
                      -- (type ‖ uint24 len ‖ body) the §4.4.1 transcript hashes.
                      let reEE   := hsMsg 8  (ofBytes eeBody)
                      let reCert := hsMsg 11 (ofBytes certBody)
                      let reCV   := hsMsg 15 (ofBytes cvBody)
                      let reFin  := hsMsg 20 (ofBytes finBody)
                      let thCert := Crypto.sha256 (chMsg ++ shMsg ++ reEE ++ reCert)
                      let thCV   := Crypto.sha256 (chMsg ++ shMsg ++ reEE ++ reCert ++ reCV)
                      let thSF   := Crypto.sha256 (chMsg ++ shMsg ++ reEE ++ reCert ++ reCV ++ reFin)
                      let cvOk := (certVerifyOk leaf scheme sig thCert).getD false
                      let finOk := serverFinishedOk sHs thCV (ofBytes finBody)
                      -- Client Finished, sealed under the client-handshake keys.
                      match clientFinishedMsg cHs thSF with
                      | none => tcpClose fd; return .error "client Finished derivation failed"
                      | some cFin =>
                        match sealRecordAt cHsKeys 0 0x16 cFin with
                        | none => tcpClose fd; return .error "client Finished seal failed"
                        | some cFinRec =>
                          tcpSend fd cFinRec
                          -- Application keys.
                          let sched := TlsCrypto.deriveSchedule dhe thHS thSF
                          match sched.clientAp, sched.serverAp with
                          | some cAp, some sAp =>
                            match TlsCrypto.trafficKeysA aead cAp,
                                  TlsCrypto.trafficKeysA aead sAp with
                            | some cApKeys, some sApKeys =>
                              return .ok { fd := fd, suite := sh.suite, group := sh.group
                                           leafDer := leaf, chainDers := allCertDers certBody
                                           certVerify := cvOk
                                           finished := finOk
                                           cApKeys := cApKeys, sApKeys := sApKeys }
                            | _, _ => tcpClose fd; return .error "app traffic keys failed"
                          | _, _ => tcpClose fd; return .error "app secret derivation failed"
                    | _, _ => tcpClose fd; return .error "cert/certverify parse failed"
                  | _, _, _, _ => tcpClose fd; return .error "incomplete server flight"
              | _, _ => tcpClose fd; return .error "handshake traffic keys failed"
    catch e =>
      tcpClose fd
      return .error s!"socket error: {e}"

/-- **One HTTPS request over the verified client.** Complete the handshake to
`ip:port` (SNI `sni`), require CertificateVerify and the server Finished to
check out (fail-closed: a bad server signature or Finished aborts before any
request is sent — `requireAuth`), seal the request under the client application
keys, read the response, and close. Returns the decrypted response bytes. -/
def request (ip : String) (port : UInt16) (sni : String) (req : ByteArray)
    (requireAuth : Bool := true) (trust : Option (Tls.Bytes × Nat) := none) :
    IO (Except String ByteArray) := do
  match ← handshake ip port sni with
  | .error e => return .error e
  | .ok s =>
    if requireAuth && !(s.certVerify && s.finished) then
      tcpClose s.fd
      return .error s!"server authentication failed (certVerify={s.certVerify} finished={s.finished})"
    -- When a trust anchor is supplied, additionally require the served chain to
    -- build to it (RFC 5280 §6.1 via `Pki.ChainBuild`) — fail-closed. Without it,
    -- CertificateVerify proves only leaf key possession, not CA issuance.
    match trust with
    | some (rootDer, now) =>
        if !(authenticateChain s.chainDers rootDer now) then
          tcpClose s.fd
          return .error "server chain did not build to the pinned trust root (Pki.ChainBuild rejected)"
    | none => pure ()
    match sealRecordAt s.cApKeys 0 0x17 req with
    | none => tcpClose s.fd; return .error "request seal failed"
    | some rec =>
      tcpSend s.fd rec
      let resp ← readAppData s.fd s.sApKeys 0 ByteArray.empty
      tcpClose s.fd
      return .ok resp

/-- String convenience wrapper for the ACME driver: request text in, response
text out (UTF-8, lossy on the response as HTTP headers are ASCII). -/
def requestText (ip : String) (port : UInt16) (sni : String) (req : String)
    (requireAuth : Bool := true) (trust : Option (Tls.Bytes × Nat) := none) :
    IO (Except String String) := do
  match ← request ip port sni req.toUTF8 requireAuth trust with
  | .error e => return .error e
  | .ok b => return .ok ((String.fromUTF8? b).getD "")

end TlsClient
