/-
# Pki.Csr — the PKCS#10 `CertificationRequest` encoder (RFC 2986)

ACME `finalize` (RFC 8555 §7.4) carries a CSR: the CA reads the requested names
and the public key out of it and issues against exactly those. drorb modelled
the CSR as opaque bytes (`Pki.Acme.Csr` wraps a `List UInt8`); nothing built
one. This module builds it, over `Pki.Der`.

```
CertificationRequest ::= SEQUENCE {
  certificationRequestInfo CertificationRequestInfo,
  signatureAlgorithm       AlgorithmIdentifier,
  signature                BIT STRING }

CertificationRequestInfo ::= SEQUENCE {
  version       INTEGER (0),
  subject       Name,
  subjectPKInfo SubjectPublicKeyInfo,
  attributes    [0] IMPLICIT SET OF Attribute }
```

The requested names travel in the `extensionRequest` attribute
(PKCS#9, OID 1.2.840.113549.1.9.14) as an X.509 `subjectAltName` extension
(OID 2.5.29.17) whose value is a DER `GeneralNames`, each name a
`dNSName` — `[2] IMPLICIT IA5String`.

## What is proven

The property that matters is that **the CSR asks for the names we meant**: a CA
that parses the SAN bytes recovers exactly the domain list, in order, with no
name dropped, added, or merged. That is `san_names_roundtrip` — stated against
an independent decoder (`readDnsNames`) that knows only the octets, so it cannot
be satisfied by an encoder that agrees with itself. `csr_decodes` is the
structural counterpart: the three top-level components come back out whole.

The signature is a **seam** (`sign`), exactly as `TlsHandshake.CertEntry.sign`
is, so this module links everywhere; the executable instantiates it with the
HACL*-backed `TlsCrypto.Sig.ecdsaP256Sign` (ECDSA-P256-SHA256, DER
`ECDSA-Sig-Value`), matching the `ecdsa-with-SHA256` algorithm identifier
emitted here.
-/
import Pki.Der

namespace Pki.Csr

open Pki.Der

/-! ## Object identifiers (content octets, without the `06 len` header) -/

/-- `1.2.840.10045.2.1` — `ecPublicKey`. -/
def oidEcPublicKey : List UInt8 := [0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x02, 0x01]
/-- `1.2.840.10045.3.1.7` — `prime256v1` (NIST P-256). -/
def oidPrime256v1 : List UInt8 := [0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x03, 0x01, 0x07]
/-- `1.2.840.10045.4.3.2` — `ecdsa-with-SHA256`. -/
def oidEcdsaSha256 : List UInt8 := [0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x04, 0x03, 0x02]
/-- `1.2.840.113549.1.9.14` — PKCS#9 `extensionRequest`. -/
def oidExtensionRequest : List UInt8 :=
  [0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01, 0x09, 0x0E]
/-- `2.5.29.17` — `subjectAltName`. -/
def oidSubjectAltName : List UInt8 := [0x55, 0x1D, 0x11]
/-- `2.5.4.3` — `commonName`. -/
def oidCommonName : List UInt8 := [0x55, 0x04, 0x03]

/-! ## Subject alternative names -/

/-- `GeneralName ::= ... dNSName [2] IMPLICIT IA5String`. Implicit tagging
replaces the IA5String tag with `[2]` primitive (`0x82`) — it does not wrap. -/
def dnsName (d : List UInt8) : List UInt8 := ctxPrimitive 2 d

/-- `GeneralNames ::= SEQUENCE SIZE (1..MAX) OF GeneralName` — the body, i.e.
the concatenated names before the SEQUENCE header. -/
def generalNamesBody (ds : List (List UInt8)) : List UInt8 :=
  (ds.map dnsName).flatten

/-- The `subjectAltName` extension: `SEQUENCE { extnID, extnValue OCTET STRING }`
where the octet string wraps the DER `GeneralNames` (RFC 5280 §4.2). Not marked
critical — a SAN is non-critical when a subject is present, and CAs ignore the
requested criticality regardless. -/
def sanExtension (ds : List (List UInt8)) : List UInt8 :=
  seq (oid oidSubjectAltName ++ octetString (seq (generalNamesBody ds)))

/-- The `extensionRequest` attribute carrying exactly the SAN extension. -/
def extensionRequestAttr (ds : List (List UInt8)) : List UInt8 :=
  seq (oid oidExtensionRequest ++ set (seq (sanExtension ds)))

/-! ## Subject and public key -/

/-- `Name` — a single `CN=` RDN, or the empty `Name` when no common name is
given. RFC 8555 §7.4 lets the subject be empty (the identifiers live in the
SAN); Let's Encrypt reads the SAN and ignores a CN it does not need. -/
def subjectName : Option (List UInt8) → List UInt8
  | none => seq []
  | some cn => seq (set (seq (oid oidCommonName ++ utf8String cn)))

/-- `SubjectPublicKeyInfo` for a P-256 key: the `ecPublicKey` algorithm with the
`prime256v1` curve parameter, then the SEC1 uncompressed point `04 ‖ X ‖ Y` as a
BIT STRING with no unused bits. -/
def spkiP256 (point : List UInt8) : List UInt8 :=
  seq (seq (oid oidEcPublicKey ++ oid oidPrime256v1) ++ bitString point)

/-! ## The request -/

/-- `CertificationRequestInfo` — the bytes that get signed. -/
def certificationRequestInfo (cn : Option (List UInt8)) (point : List UInt8)
    (ds : List (List UInt8)) : List UInt8 :=
  seq (integerNat 0 ++ subjectName cn ++ spkiP256 point
        ++ ctxConstructed 0 (extensionRequestAttr ds))

/-- `AlgorithmIdentifier` for `ecdsa-with-SHA256`. RFC 5758 §3.2: the parameters
field is **absent**, not NULL. -/
def ecdsaSha256AlgId : List UInt8 := seq (oid oidEcdsaSha256)

/-- Assemble the signed request from the request info and the DER
`ECDSA-Sig-Value`. -/
def certificationRequest (cri sig : List UInt8) : List UInt8 :=
  seq (cri ++ ecdsaSha256AlgId ++ bitString sig)

/-- Build a complete CSR: encode the request info, hand it to the signing seam,
and assemble. `none` exactly when the signer fails. -/
def buildCsr (sign : List UInt8 → Option (List UInt8))
    (cn : Option (List UInt8)) (point : List UInt8) (ds : List (List UInt8)) :
    Option (List UInt8) :=
  (sign (certificationRequestInfo cn point ds)).map
    (certificationRequest (certificationRequestInfo cn point ds))

/-! ## The SAN round-trip

`readDnsNames` is the CA's reader: it walks the `GeneralNames` body, requiring
each item to carry the `dNSName` tag, and collects the values. It is defined
with a fuel parameter so it is structurally terminating without a
decreasing-measure argument on `readTlv`'s remainder. -/

/-- Decode a `GeneralNames` body into its `dNSName` values. -/
def readDnsNames : Nat → List UInt8 → Option (List (List UInt8))
  | _, [] => some []
  | 0, _ => none
  | fuel + 1, bs =>
    match readTlv bs with
    | some (t, body, rest) =>
        if t = 0x82 then (readDnsNames fuel rest).map (body :: ·) else none
    | none => none

/-- One step: the encoded body of `d :: ds` presents `d` under the `dNSName` tag
and leaves precisely the encoding of `ds` behind. -/
theorem generalNamesBody_cons (d : List UInt8) (ds : List (List UInt8))
    (h : Wf d) :
    readTlv (generalNamesBody (d :: ds)) = some (0x82, d, generalNamesBody ds) := by
  show readTlv (dnsName d ++ generalNamesBody ds) = _
  exact readTlv_tlv 0x82 d h (generalNamesBody ds)

/-- **san_names_roundtrip.** A reader that sees only the octets recovers exactly
the requested domain list — same names, same order, none lost or invented. This
is the property the whole CSR exists to carry: the certificate the CA issues
covers the names asked for here.

Non-vacuous: the hypothesis is just that each name is encodable (`Wf`, i.e.
under 64 KiB — every DNS name is), and the conclusion is equality with the
original list, recovered through an independent decoder. -/
theorem san_names_roundtrip (ds : List (List UInt8))
    (h : ∀ d ∈ ds, Wf d) :
    readDnsNames ds.length (generalNamesBody ds) = some ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    have hd : Wf d := h d (by simp)
    have hds : ∀ x ∈ ds, Wf x := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hne : generalNamesBody (d :: ds) ≠ [] := by
      show dnsName d ++ generalNamesBody ds ≠ []
      simp [dnsName, ctxPrimitive, tlv]
    -- unfold one step of the fuel recursion on a non-empty body
    match hb : generalNamesBody (d :: ds), hne with
    | b :: bs, _ =>
      show (match readTlv (b :: bs) with
            | some (t, body, rest) =>
                if t = 0x82 then (readDnsNames ds.length rest).map (body :: ·) else none
            | none => none) = some (d :: ds)
      rw [← hb, generalNamesBody_cons d ds hd]
      simp [ih hds]

/-! ## The structural round-trip

The three top-level components of the request come back out of the octets
whole — the request info the signature covers, the algorithm identifier, and the
signature itself. -/

theorem csr_decodes (cri sig : List UInt8) (h : Wf (cri ++ ecdsaSha256AlgId ++ bitString sig)) :
    readTlv (certificationRequest cri sig)
      = some (0x30, cri ++ ecdsaSha256AlgId ++ bitString sig, []) := by
  have hr := readTlv_tlv 0x30 (cri ++ ecdsaSha256AlgId ++ bitString sig) h []
  rw [List.append_nil] at hr
  exact hr

/-- `buildCsr` signs exactly the `CertificationRequestInfo` it emits — the bytes
under the signature are the bytes the CA will re-serialize and verify. Stated as:
whenever a CSR is produced, it is `certificationRequest cri s` for the `cri` this
module encoded and an `s` the seam returned on that same `cri`. -/
theorem buildCsr_signs_its_own_info
    (sign : List UInt8 → Option (List UInt8))
    (cn : Option (List UInt8)) (point : List UInt8) (ds : List (List UInt8))
    (out : List UInt8) (h : buildCsr sign cn point ds = some out) :
    ∃ s, sign (certificationRequestInfo cn point ds) = some s ∧
         out = certificationRequest (certificationRequestInfo cn point ds) s := by
  unfold buildCsr at h
  cases hs : sign (certificationRequestInfo cn point ds) with
  | none => rw [hs] at h; simp at h
  | some s => rw [hs] at h; simp at h; exact ⟨s, rfl, h.symm⟩

end Pki.Csr
