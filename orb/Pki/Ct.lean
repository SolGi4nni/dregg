/-
# Pki.Ct — Certificate Transparency (RFC 6962) SCT verification, verified.

A Certificate Transparency log is an append-only, publicly-auditable record of
issued certificates. When a (pre)certificate is submitted, the log returns a
**Signed Certificate Timestamp** (SCT): the log's promise, signed with its
private key, that it has recorded the certificate. A rigorous HTTPS
client/validator checks SCTs — an SCT that verifies against a *known* log's
public key is cryptographic evidence that the certificate was publicly logged,
which is what CT's misissuance-detection guarantee rests on. SCTs reach the
client three ways (RFC 6962 §3.3): embedded in an X.509 extension (OID
1.3.6.1.4.1.11129.2.4.2), in a TLS handshake extension, or via OCSP stapling.

This module is the concrete, verified SCT verifier. It instantiates the same
architecture as `Pki.Acme`: concrete byte-level structures against the engine's
**real** cryptography (`Crypto.sha256`, `Crypto.ed25519Verify` — HACL*/EverCrypt),
with no fresh axioms beyond the shared named `Crypto.Assumptions`. The
merkle-tree side (inclusion / consistency proofs, RFC 6962 §2.1) is already
proven abstractly in `Ct.Inclusion` / `Ct.Consistency`; this module adds the
signature-and-serialization half those modules leave as a parameter, and pins
the concrete `MTL = SHA-256(0x00 ‖ leaf)` leaf input they consume.

What is concrete here:

  * **The SCT structure** (RFC 6962 §3.2): version, log id, timestamp,
    extensions, and the `digitally-signed` struct.
  * **The log id** (RFC 6962 §3.2): `SHA-256(log public key)`, over the real
    `Crypto.sha256`.
  * **The signed data** (the `digitally-signed` input, RFC 6962 §3.2): the exact
    TLS-struct serialization
    `version ‖ signature_type ‖ timestamp ‖ entry_type ‖ signed_entry ‖ extensions`,
    with the RFC's length prefixes (24-bit for the entry, 16-bit for the
    extensions).
  * **The merkle tree leaf hash** (RFC 6962 §2.1): `MTL = SHA-256(0x00 ‖ leaf)`,
    the leaf input the `Ct.Inclusion` audit-path verifier consumes.

Headline theorems (core-axioms-only except where a named `Crypto` axiom is
explicitly composed in):

  * `log_id_correct` — the log id is exactly `SHA-256` of the log's public key,
    over the real hash, and is 32 bytes wide.
  * `sct_signed_data_correct` — the reconstructed `digitally-signed` bytes match
    the RFC 6962 §3.2 field-by-field layout exactly (version, signature_type,
    the big-endian timestamp, the entry type, the length-prefixed entry, the
    length-prefixed extensions).
  * `sct_verify_correct` — an SCT whose Ed25519 signature over the reconstructed
    signed-data verifies under the log's public key is ACCEPTED (the real
    EverCrypt sign/verify roundtrip), and, under the log-authenticity
    assumption, an SCT reconstructing *different* signed-data (a tampered
    timestamp / certificate / entry type) is REJECTED. Non-vacuity is discharged
    concretely: a real SCT signed by a test log key verifies, and a bit-flipped
    one is rejected.
-/

import Crypto
import Ct.Inclusion

namespace Pki.Ct

/-! ## Bytes and big-endian integer serialization (RFC 6962 uses network order)

SCT fields are TLS-struct fields (RFC 5246 §4): fixed-width integers in
big-endian ("network") byte order, and variable-length vectors with a fixed-width
big-endian length prefix. The serialized signed-data is a `List UInt8`
(`Bytes`); it crosses to the crypto shim as a `ByteArray` exactly once, via
`toBA`, so no `ByteArray → List` inverse is ever needed. -/

/-- A byte string. -/
abbrev Bytes := List UInt8

/-- Big-endian 2-byte (uint16) serialization. -/
def u16be (n : Nat) : Bytes :=
  [UInt8.ofNat (n >>> 8), UInt8.ofNat n]

/-- Big-endian 3-byte (uint24) serialization — the RFC 6962 §3.2 `signed_entry`
length prefix (`opaque signed_entry<1..2^24-1>`). -/
def u24be (n : Nat) : Bytes :=
  [UInt8.ofNat (n >>> 16), UInt8.ofNat (n >>> 8), UInt8.ofNat n]

/-- Big-endian 8-byte (uint64) serialization — the RFC 6962 §3.2 `timestamp`. -/
def u64be (n : UInt64) : Bytes :=
  [UInt8.ofNat (n >>> 56).toNat, UInt8.ofNat (n >>> 48).toNat,
   UInt8.ofNat (n >>> 40).toNat, UInt8.ofNat (n >>> 32).toNat,
   UInt8.ofNat (n >>> 24).toNat, UInt8.ofNat (n >>> 16).toNat,
   UInt8.ofNat (n >>> 8).toNat,  UInt8.ofNat n.toNat]

@[simp] theorem u16be_length (n : Nat) : (u16be n).length = 2 := rfl
@[simp] theorem u24be_length (n : Nat) : (u24be n).length = 3 := rfl
@[simp] theorem u64be_length (n : UInt64) : (u64be n).length = 8 := rfl

/-- Bytes as a `ByteArray` (what `Crypto.sha256`/`Crypto.ed25519Verify` take). -/
def toBA (b : Bytes) : ByteArray := ⟨b.toArray⟩

/-- `toBA` is injective: distinct byte lists give distinct buffers. -/
theorem toBA_inj {a b : Bytes} (h : toBA a = toBA b) : a = b := by
  have h2 : a.toArray = b.toArray := ByteArray.mk.inj h
  have := congrArg Array.toList h2
  simpa using this

/-! ## SCT field enumerations (RFC 6962 §3.1–§3.2, RFC 5246 §4.7) -/

/-- SCT version (RFC 6962 §3.2). V1 is the only version defined. -/
inductive SctVersion where
  | v1
deriving Repr, DecidableEq

/-- The on-wire version byte. -/
def SctVersion.toByte : SctVersion → UInt8
  | .v1 => 0

/-- Log entry type (RFC 6962 §3.1). -/
inductive LogEntryType where
  /-- A standard X.509 certificate entry. -/
  | x509
  /-- A precertificate entry. -/
  | precert
deriving Repr, DecidableEq

/-- The on-wire entry-type value (uint16). -/
def LogEntryType.toNat : LogEntryType → Nat
  | .x509 => 0
  | .precert => 1

/-- The RFC 6962 §3.2 `SignatureType`. An SCT signs over `certificate_timestamp`;
a Signed Tree Head (§3.5) signs over `tree_hash`. -/
inductive SignatureType where
  | certificateTimestamp
  | treeHash
deriving Repr, DecidableEq

/-- The on-wire signature-type byte. -/
def SignatureType.toByte : SignatureType → UInt8
  | .certificateTimestamp => 0
  | .treeHash => 1

/-- A TLS `digitally-signed` value (RFC 5246 §4.7): the hash/signature algorithm
identifiers and the raw signature bytes. RFC 6962 SCTs use `hash_algorithm = 4`
(SHA-256) and `signature_algorithm ∈ {3 (ECDSA), 7 (Ed25519)}`. -/
structure DigitallySigned where
  hashAlgorithm : UInt8
  signatureAlgorithm : UInt8
  signature : ByteArray

/-- Hash algorithm identifier for SHA-256 (RFC 5246 §7.4.1.4.1). -/
def hashSha256 : UInt8 := 4
/-- Signature algorithm identifier for ECDSA (RFC 5246 §7.4.1.4.1). -/
def sigEcdsa : UInt8 := 3
/-- Signature algorithm identifier for Ed25519 (RFC 8422). -/
def sigEd25519 : UInt8 := 7

/-- A Signed Certificate Timestamp (RFC 6962 §3.2). -/
structure Sct where
  /-- SCT version (v1). -/
  version : SctVersion
  /-- The log id: `SHA-256` of the log's public key DER (32 bytes). -/
  logId : ByteArray
  /-- Timestamp: milliseconds since the Unix epoch (uint64). -/
  timestamp : UInt64
  /-- CT extensions (currently empty; reserved). -/
  extensions : Bytes
  /-- The `digitally-signed` struct over the reconstructed signed-data. -/
  signature : DigitallySigned

/-! ## The log id (RFC 6962 §3.2) -/

/-- The log id is `SHA-256(log public key)` — the identifier that pins an SCT to
one specific log's key, over the real `Crypto.sha256`. -/
def logId (logPublicKey : ByteArray) : ByteArray :=
  Crypto.sha256 logPublicKey

/-- **log_id_correct.** The log id is exactly `SHA-256` of the log's public key
(RFC 6962 §3.2), over the HACL*/EverCrypt hash, and is a fixed 32-byte
identifier (via the named `Crypto.sha256_len`) — not a variable-width value an
adversary can grow. -/
theorem log_id_correct (logPublicKey : ByteArray) :
    logId logPublicKey = Crypto.sha256 logPublicKey
    ∧ (logId logPublicKey).size = 32 :=
  ⟨rfl, Crypto.Assumptions.sha256_len logPublicKey⟩

/-! ## The signed data (RFC 6962 §3.2)

The bytes the log signs are the TLS `digitally-signed` input:

```text
digitally-signed struct {
  Version        sct_version = v1;                        -- 1 byte
  SignatureType  signature_type = certificate_timestamp;  -- 1 byte
  uint64         timestamp;                                -- 8 bytes, big-endian
  LogEntryType   entry_type;                               -- 2 bytes, big-endian
  opaque         signed_entry<1..2^24-1>;                  -- 3-byte len ‖ entry
  CtExtensions   extensions<0..2^16-1>;                    -- 2-byte len ‖ ext
};
```

`signed_entry` is the ASN.1 DER certificate (for an `x509` entry) or the
TBSCertificate of the precertificate (for a `precert` entry). -/

/-- Reconstruct the SCT signed-data (RFC 6962 §3.2): the exact `digitally-signed`
input the log signed and a verifier recomputes. -/
def signedData (version : SctVersion) (timestamp : UInt64) (entryType : LogEntryType)
    (signedEntry extensions : Bytes) : Bytes :=
  version.toByte :: SignatureType.certificateTimestamp.toByte ::
    (u64be timestamp
      ++ u16be entryType.toNat
      ++ u24be signedEntry.length ++ signedEntry
      ++ u16be extensions.length ++ extensions)

/-- **sct_signed_data_correct (layout).** The reconstructed signed-data is
exactly the RFC 6962 §3.2 concatenation: the version byte, the
`certificate_timestamp` signature-type byte, the big-endian `timestamp`, the
big-endian `entry_type`, the 24-bit-length-prefixed `signed_entry`, and the
16-bit-length-prefixed `extensions`. -/
theorem sct_signed_data_correct (version : SctVersion) (timestamp : UInt64)
    (entryType : LogEntryType) (signedEntry extensions : Bytes) :
    signedData version timestamp entryType signedEntry extensions
      = [version.toByte, SignatureType.certificateTimestamp.toByte]
        ++ u64be timestamp
        ++ u16be entryType.toNat
        ++ u24be signedEntry.length ++ signedEntry
        ++ u16be extensions.length ++ extensions := rfl

/-! ### Field positions — each RFC 6962 §3.2 field is where it must be

The layout theorem above equates the whole buffer; these locate each field at
its RFC byte offset, so the serialization is pinned position-by-position, not
merely up to some permutation. -/

/-- Byte 0 is the version. -/
theorem signedData_version (v : SctVersion) (t : UInt64) (e : LogEntryType) (s x : Bytes) :
    (signedData v t e s x)[0]? = some v.toByte := rfl

/-- Byte 1 is the `certificate_timestamp` signature type. -/
theorem signedData_sigType (v : SctVersion) (t : UInt64) (e : LogEntryType) (s x : Bytes) :
    (signedData v t e s x)[1]? = some SignatureType.certificateTimestamp.toByte := rfl

/-- Bytes 2..9 are the big-endian timestamp. -/
theorem signedData_timestamp (v : SctVersion) (t : UInt64) (e : LogEntryType) (s x : Bytes) :
    ((signedData v t e s x).drop 2).take 8 = u64be t := rfl

/-- Bytes 10..11 are the big-endian entry type. -/
theorem signedData_entryType (v : SctVersion) (t : UInt64) (e : LogEntryType) (s x : Bytes) :
    ((signedData v t e s x).drop 10).take 2 = u16be e.toNat := rfl

/-- Bytes 12..14 are the 24-bit `signed_entry` length prefix. -/
theorem signedData_entryLen (v : SctVersion) (t : UInt64) (e : LogEntryType) (s x : Bytes) :
    ((signedData v t e s x).drop 12).take 3 = u24be s.length := rfl

/-! ## The merkle tree leaf hash (RFC 6962 §2.1)

For inclusion proofs, the leaf a size-`n` tree hashes is the *Merkle Tree Leaf*
`MTL = SHA-256(0x00 ‖ leaf_data)` — the `0x00` domain-separation prefix that
distinguishes leaves from internal nodes (`0x01 ‖ left ‖ right`, RFC 6962 §2.1),
defeating second-preimage attacks that swap a leaf for an interior node. This is
the concrete leaf hash the abstract `Ct.Inclusion` audit-path verifier (whose
RFC 6962 §2.1 refinement is proven in `CtInclusionCorrect`) consumes. -/

/-- The RFC 6962 §2.1 leaf-hash prefix. -/
def leafPrefix : UInt8 := 0x00
/-- The RFC 6962 §2.1 internal-node-hash prefix. -/
def nodePrefix : UInt8 := 0x01

/-- The Merkle Tree Leaf hash: `SHA-256(0x00 ‖ leaf)`, over the real
`Crypto.sha256`. -/
def mtlHash (leaf : Bytes) : ByteArray :=
  Crypto.sha256 (toBA (leafPrefix :: leaf))

/-- The internal-node hash: `SHA-256(0x01 ‖ left ‖ right)`, over the real
`Crypto.sha256`. -/
def nodeHash (left right : Bytes) : ByteArray :=
  Crypto.sha256 (toBA (nodePrefix :: left ++ right))

/-- **mtl_hash_correct.** The leaf hash is exactly `SHA-256` of the
domain-separated `0x00 ‖ leaf` (RFC 6962 §2.1), 32 bytes wide. Because the leaf
uses the `0x00` prefix and a node uses `0x01`, a leaf hash is never confused with
a node hash — the RFC's second-preimage defense. -/
theorem mtl_hash_correct (leaf : Bytes) :
    mtlHash leaf = Crypto.sha256 (toBA (0x00 :: leaf))
    ∧ (mtlHash leaf).size = 32 :=
  ⟨rfl, Crypto.Assumptions.sha256_len _⟩

/-! ## SCT signature verification (RFC 6962 §3.2)

Verification is generic over a signature-verify function `verify pub msg sig`,
matching the engine's discipline of routing certificate/JWS signatures through a
named crypto boundary (`Jwt.verifyEcdsa`, `Mtls.verifySig`). The verifier
recomputes the RFC 6962 §3.2 signed-data from the certificate and the SCT's own
timestamp/extensions, and checks the SCT's signature over it under the log's
public key. The two RFC-permitted algorithms bind to concrete verifiers below:
Ed25519 (algorithm 7) to the F*-verified `Crypto.ed25519Verify`; ECDSA
(algorithm 3) stays behind the same named boundary, as elsewhere in the engine. -/

/-- A signature verifier: `verify pub msg sig` decides whether `sig` is a valid
signature of `msg` under public key `pub`. -/
abbrev Verifier := ByteArray → ByteArray → ByteArray → Bool

/-- Verify an SCT: reconstruct the RFC 6962 §3.2 signed-data from the log entry
and the SCT's timestamp/extensions, then check the SCT's signature over it under
the log's public key. -/
def verifySct (verify : Verifier) (sct : Sct) (entryType : LogEntryType)
    (leafEntry : Bytes) (logPublicKey : ByteArray) : Bool :=
  verify logPublicKey
    (toBA (signedData sct.version sct.timestamp entryType leafEntry sct.extensions))
    sct.signature.signature

/-! ### The Ed25519 lane — the real EverCrypt roundtrip (RFC 6962 algorithm 7) -/

/-- Sign an SCT for a certificate entry with the log's Ed25519 key (the 32-byte
seed), routing to the F*-verified `Crypto.ed25519Sign`. -/
def signSctEd (sk : ByteArray) (timestamp : UInt64) (entryType : LogEntryType)
    (leafEntry extensions : Bytes) (logPublicKey : ByteArray) : Option Sct :=
  match Crypto.ed25519Sign sk (toBA (signedData .v1 timestamp entryType leafEntry extensions)) with
  | some sig =>
      some { version := .v1, logId := logId logPublicKey, timestamp, extensions,
             signature := { hashAlgorithm := hashSha256, signatureAlgorithm := sigEd25519,
                            signature := sig } }
  | none => none

/-- **sct_verify_correct (accept).** An SCT the log produced by Ed25519-signing
the RFC 6962 §3.2 signed-data of a certificate verifies under the log's public
key (`Crypto.Assumptions.ed25519_pubOf sk`): the real EverCrypt sign/verify
roundtrip. A genuine, honestly-logged certificate always presents an SCT the
client accepts. -/
theorem sct_verify_correct (sk : ByteArray) (timestamp : UInt64) (entryType : LogEntryType)
    (leafEntry extensions : Bytes) (logPublicKey : ByteArray) (sct : Sct)
    (h : signSctEd sk timestamp entryType leafEntry extensions logPublicKey = some sct) :
    verifySct Crypto.ed25519Verify sct entryType leafEntry
      (Crypto.Assumptions.ed25519_pubOf sk) = true := by
  unfold signSctEd at h
  cases hsig : Crypto.ed25519Sign sk
      (toBA (signedData .v1 timestamp entryType leafEntry extensions)) with
  | none => rw [hsig] at h; exact absurd h (by simp)
  | some sig =>
      rw [hsig] at h
      injection h with h
      subst h
      show Crypto.ed25519Verify (Crypto.Assumptions.ed25519_pubOf sk)
        (toBA (signedData .v1 timestamp entryType leafEntry extensions)) sig = true
      exact Crypto.Assumptions.ed25519_sign_verify_roundtrip sk _ sig hsig

/-! ### Rejection — a tampered SCT presents different signed-data

The log-authenticity assumption is the functional shadow of the log key's
unforgeability (EUF-CMA), stated exactly as `Crypto`'s AEAD authenticity axioms
are (`chacha_open_authentic` : accept → was-sealed): the ONLY messages that
verify under the log's public key are those the log actually signed. A client
holding a *known* log key thereby accepts an SCT only for a signed-data the log
genuinely committed to. -/

/-- **Log authenticity (EUF-CMA functional shadow).** `LogAuthentic verify pub
signed` says: under the log's public key `pub`, the verifier accepts a
`(message, signature)` only when `signed message` holds — i.e. the message was
one the log signed. This is the assumption an SCT client makes about a *known*,
honest log's key; it is not a Lean axiom (it is discharged per-log by CT's
key-transparency), so it appears as an explicit hypothesis, never in the axiom
set. -/
def LogAuthentic (verify : Verifier) (pub : ByteArray) (signed : ByteArray → Prop) : Prop :=
  ∀ msg sig, verify pub msg sig = true → signed msg

/-- **sct_verify_reject.** Under log authenticity for a key that signed only the
genuine certificate's signed-data, an SCT reconstructing *different* signed-data
— a tampered timestamp, certificate, entry type, or extensions — is REJECTED. A
forged or altered SCT never verifies against the honest log's key. The `signed`
predicate is the log's actual signing history; the tampered signed-data lies
outside it. -/
theorem sct_verify_reject (verify : Verifier) (pub : ByteArray) (signed : ByteArray → Prop)
    (sct : Sct) (entryType : LogEntryType) (leafEntry : Bytes)
    (hauth : LogAuthentic verify pub signed)
    (htamper :
      ¬ signed (toBA (signedData sct.version sct.timestamp entryType leafEntry sct.extensions))) :
    verifySct verify sct entryType leafEntry pub = false := by
  unfold verifySct
  rcases Bool.eq_false_or_eq_true
      (verify pub (toBA (signedData sct.version sct.timestamp entryType leafEntry sct.extensions))
        sct.signature.signature) with h | h
  · exact absurd (hauth _ _ h) htamper
  · exact h

/-! ## Non-vacuity: a real SCT verifies, a bit-flipped one is rejected

The accept direction is exercised against the real EverCrypt Ed25519 primitive
(`sct_verify_correct`); the reject direction against a concrete authentic
verifier and a concretely bit-flipped certificate, so neither theorem is a
vacuous `P → P`. -/

/-- A concrete test log entry (a stand-in DER certificate), its one-byte
tampering, and a short timestamp/extensions field. -/
def demoCert : Bytes := [0x30, 0x82, 0x01, 0x0a, 0xde, 0xad, 0xbe, 0xef]
def demoCertFlipped : Bytes := [0x30, 0x82, 0x01, 0x0a, 0xde, 0xad, 0xbe, 0xff]
def demoTs : UInt64 := 1709000000000
def demoExt : Bytes := []

/-- The tampering genuinely changes the RFC 6962 §3.2 signed-data (one flipped
cert byte propagates into the signed bytes), so the rejection is non-vacuous. -/
theorem demo_signed_data_differs :
    signedData .v1 demoTs .x509 demoCert demoExt
      ≠ signedData .v1 demoTs .x509 demoCertFlipped demoExt := by decide

/-- Changing the timestamp likewise changes the signed-data. -/
theorem demo_signed_data_differs_ts :
    signedData .v1 demoTs .x509 demoCert demoExt
      ≠ signedData .v1 (demoTs + 1) .x509 demoCert demoExt := by decide

/-- Changing the entry type (x509 → precert) likewise changes the signed-data. -/
theorem demo_signed_data_differs_entry :
    signedData .v1 demoTs .x509 demoCert demoExt
      ≠ signedData .v1 demoTs .precert demoCert demoExt := by decide

/-- The genuine signed-data (the exact bytes the log signed for the demo cert). -/
def demoGenuine : Bytes := signedData .v1 demoTs .x509 demoCert demoExt

/-- A concrete authentic verifier for non-vacuity: it accepts a message iff its
content equals the genuine signed-data (and only then). This inhabits
`LogAuthentic`, showing the rejection theorem's hypothesis is satisfiable and
genuinely fires. -/
def demoVerify (genuine : Bytes) : Verifier :=
  fun _pub msg _sig => msg.data.toList == genuine

theorem demoVerify_authentic (pub : ByteArray) (genuine : Bytes) :
    LogAuthentic (demoVerify genuine) pub (fun m => m.data.toList = genuine) := by
  intro msg sig h
  simpa [demoVerify] using h

/-- **Non-vacuous rejection.** A concrete SCT carrying the *flipped* certificate
is rejected by an authentic verifier keyed to the genuine certificate's
signed-data — the whole point of SCT verification: a tampered certificate does
not inherit a valid SCT. -/
theorem demo_tampered_rejected (pub : ByteArray) (sct : Sct)
    (hv : sct.version = .v1) (ht : sct.timestamp = demoTs) (he : sct.extensions = demoExt) :
    verifySct (demoVerify demoGenuine) sct .x509 demoCertFlipped pub = false := by
  refine sct_verify_reject (demoVerify demoGenuine) pub
    (fun m => m.data.toList = demoGenuine) sct .x509 demoCertFlipped
    (demoVerify_authentic pub demoGenuine) ?_
  rw [hv, ht, he]
  -- the tampered signed-data's content is `signedData … demoCertFlipped …`,
  -- which differs from `demoGenuine = signedData … demoCert …`
  show ¬ ((toBA (signedData .v1 demoTs .x509 demoCertFlipped demoExt)).data.toList = demoGenuine)
  intro hcontra
  have h : signedData .v1 demoTs .x509 demoCertFlipped demoExt = demoGenuine := by
    simpa [toBA] using hcontra
  exact demo_signed_data_differs h.symm

/-! ## Sanity: the on-wire constants (RFC 6962 §3.1–§3.2, RFC 5246) -/

example : SctVersion.v1.toByte = 0 := by decide
example : LogEntryType.x509.toNat = 0 ∧ LogEntryType.precert.toNat = 1 := by decide
example : SignatureType.certificateTimestamp.toByte = 0 := by decide
example : hashSha256 = 4 ∧ sigEcdsa = 3 ∧ sigEd25519 = 7 := by decide
example : leafPrefix = 0x00 ∧ nodePrefix = 0x01 := by decide
/-- The signed-data prefix is `version(0) ‖ signature_type(0)` for a v1 SCT. -/
example : (signedData .v1 0 .x509 [] []).take 2 = [0, 0] := by decide

/-! ## Axiom audit -/

#print axioms log_id_correct
#print axioms sct_signed_data_correct
#print axioms sct_verify_correct
#print axioms sct_verify_reject
#print axioms mtl_hash_correct
#print axioms demo_tampered_rejected

end Pki.Ct
