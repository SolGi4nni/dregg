/-
# Pki.Crl — X.509 CRL parse + revocation decision (RFC 5280), verified.

A Certificate Revocation List (CRL) is a signed, periodically-issued list naming
the certificates a CA has revoked before their scheduled expiry. A relying party
that trusts a certificate must consult a current CRL: if the certificate's serial
number appears on the list, the certificate is revoked and MUST be rejected; and
if the CRL itself is out of date (its `nextUpdate` time has passed), it can no
longer be trusted to reflect fresh revocations and MUST NOT be relied upon
(RFC 5280 §6.3.3). Getting this decision logic right is the security-relevant
part: a stale CRL can silently hide a revocation that happened after it was
issued.

This module is the concrete, verified model of that parse-and-decide pipeline.
It follows the same discipline as `Pki.OcspResponse`: concrete byte-level
structures and a signature-verify **oracle** carried as a named assumption (a
`Prop`, never a fresh Lean axiom), so the machine-checked content is the parse
and the revocation/freshness decision — the crypto primitive itself is out of
scope and is not reinvented here.

What is concrete here:

  * **The `TBSCertList` byte layout** (RFC 5280 §5.1.2): the `thisUpdate` /
    `nextUpdate` `Time` fields (`GeneralizedTime`/`UTCTime` octet strings) and the
    `revokedCertificates` `SEQUENCE OF`, each revoked entry keyed by its
    `userCertificate` serial (a DER `INTEGER` TLV, RFC 5280 §5.1.2.6 / §4.1.2.2).
  * **The CRL parse** — a `Bytes → Option TBSCertList` decoder with a proven
    encode/parse roundtrip: the parser recovers exactly the `thisUpdate`,
    `nextUpdate`, and the list of revoked serials the issuer encoded.
  * **The freshness gate** (RFC 5280 §6.3.3): the relying party stops trusting a
    CRL once the current time is outside `[thisUpdate, nextUpdate]`.
  * **The accept/reject decision** — accept a certificate only when the issuer's
    signature over the `tbsCertList` verifies, the CRL is fresh, and the
    certificate's serial is *not* on the revoked list.

Headline theorems (all core-axioms-only — no crypto axiom is composed in; the
signature verifier is an opaque parameter / named `Prop` assumption):

  * `crl_parses` — an encoded `TBSCertList` parses back to exactly the
    `thisUpdate`/`nextUpdate` and the list of revoked serials the issuer wrote
    (RFC 5280 §5.1.2): the parse never drops, reorders, or invents a serial.
  * `crl_revoked_rejected` — a certificate whose serial is on the CRL is rejected,
    even when the CRL signature verifies and the CRL is fresh. Revocation is
    terminal.
  * `crl_stale_rejected` — a CRL whose `nextUpdate` has passed is not trusted:
    the certificate is rejected (conservative hard-fail) even for a
    signature-valid CRL that does not list the serial (RFC 5280 §6.3.3). The
    freshness gate is load-bearing: a mutant that drops it trusts an expired CRL
    that the real check rejects.
  * `crl_forged_rejected` — under issuer authenticity (the EUF-CMA functional
    shadow), a CRL the issuer never signed is not trusted: the opaque signature
    oracle is what stands between a forged "empty" CRL and acceptance of a
    revoked certificate.
-/

namespace Pki.Crl

/-! ## Bytes -/

/-- A byte string. -/
abbrev Bytes := List UInt8

/-- A certificate serial number, modeled as its DER `INTEGER` content octets
(RFC 5280 §4.1.2.2: serials are up to 20 octets). -/
abbrev Serial := Bytes

/-! ## The `revokedCertificates` entries — RFC 5280 §5.1.2.6

```text
revokedCertificates SEQUENCE OF SEQUENCE {
  userCertificate   CertificateSerialNumber,
  revocationDate    Time,
  crlEntryExtensions Extensions OPTIONAL } OPTIONAL
```

The security-relevant projection of that list is the multiset of revoked
serials. Each serial is encoded on the wire as a DER `INTEGER` TLV: tag `0x02`,
a short-form length octet, then the content octets. `encodeSerials` lays a list
of serials down as the concatenation of their TLVs (the flattened `SEQUENCE OF`
content), and `parseSerials` recovers it. -/

/-- Encode one serial as its DER `INTEGER` TLV (short-form length). -/
def encodeSerial (s : Serial) : Bytes :=
  0x02 :: UInt8.ofNat s.length :: s

/-- Encode the `revokedCertificates` serials as the concatenation of their
`INTEGER` TLVs. -/
def encodeSerials : List Serial → Bytes
  | [] => []
  | s :: rest => encodeSerial s ++ encodeSerials rest

/-- Parse a concatenation of `INTEGER` TLVs back to the list of serials. Returns
`none` on an unexpected tag or a truncated length. -/
def parseSerials : Bytes → Option (List Serial)
  | [] => some []
  | tag :: len :: rest =>
      if tag == 0x02 then
        let n := len.toNat
        if rest.length < n then none
        else (parseSerials (rest.drop n)).map (fun tl => rest.take n :: tl)
      else none
  | _ => none
termination_by b => b.length
decreasing_by
  simp_wf
  have _hd : (rest.drop n).length ≤ rest.length := by
    rw [List.length_drop]; omega
  omega

/-! ## The `Time` fields and the `TBSCertList`

`thisUpdate` and `nextUpdate` are X.509 `Time` values — `UTCTime` or
`GeneralizedTime` **octet strings** on the wire (RFC 5280 §5.1.2.4 / §5.1.2.5),
not integers. We carry them as their raw octets and recover them verbatim; each
is laid down length-prefixed. -/

/-- A `TBSCertList`, reduced to the fields a revocation check consumes
(RFC 5280 §5.1.2): the two `Time` octet strings and the revoked serials. -/
structure TBSCertList where
  /-- `thisUpdate` `Time` octets. -/
  thisUpdate : Bytes
  /-- `nextUpdate` `Time` octets. -/
  nextUpdate : Bytes
  /-- The `userCertificate` serials of the `revokedCertificates` list. -/
  revoked : List Serial
deriving Repr, DecidableEq

/-- Encode a length-prefixed octet field (short-form length). -/
def encodeField (f : Bytes) : Bytes :=
  UInt8.ofNat f.length :: f

/-- Parse a length-prefixed octet field, returning the field and the remainder. -/
def parseField : Bytes → Option (Bytes × Bytes)
  | [] => none
  | len :: rest =>
      let n := len.toNat
      if rest.length < n then none
      else some (rest.take n, rest.drop n)

/-- Encode a `TBSCertList`: `thisUpdate ‖ nextUpdate ‖ revokedCertificates`. -/
def encodeTBS (t : TBSCertList) : Bytes :=
  encodeField t.thisUpdate ++ encodeField t.nextUpdate ++ encodeSerials t.revoked

/-- Parse a `TBSCertList` from its byte layout. -/
def parseTBS (b : Bytes) : Option TBSCertList := do
  let (tu, r1) ← parseField b
  let (nu, r2) ← parseField r1
  let rev ← parseSerials r2
  some { thisUpdate := tu, nextUpdate := nu, revoked := rev }

/-! ## The freshness window — RFC 5280 §6.3.3

The relying party interprets the two `Time` fields to a numeric window and
requires the current time to lie within `[thisUpdate, nextUpdate]`. Times are
modeled as `Nat` seconds since an epoch (the decoded view of the octet fields,
exactly as `Pki.OcspResponse.Window` carries decoded times). -/

/-- The validity window of a CRL. -/
structure Window where
  /-- `thisUpdate`: the CRL is issued as of this time. -/
  thisUpdate : Nat
  /-- `nextUpdate`: the CRL is stale after this time. -/
  nextUpdate : Nat
deriving Repr, DecidableEq

/-- **The freshness gate (RFC 5280 §6.3.3).** A CRL is fresh at `now` iff
`thisUpdate ≤ now ≤ nextUpdate`. -/
def isFresh (w : Window) (now : Nat) : Bool :=
  decide (w.thisUpdate ≤ now ∧ now ≤ w.nextUpdate)

/-! ## The signature-verify oracle

The issuer signs the `tbsCertList` (RFC 5280 §5.1.1.3). Verifying that signature
is a crypto primitive kept behind a named boundary — a `Verifier` function
supplied by the caller — exactly as `Pki.OcspResponse` routes responder
signatures through an abstract `Verifier`. The machine-checked content is the
decision logic *around* the oracle, not the primitive. -/

/-- A signature verifier: `verify key msg sig` decides whether `sig` is a valid
signature of `msg` under the CRL issuer's public key. -/
abbrev Verifier := ByteArray → ByteArray → ByteArray → Bool

/-! ## A CRL (for the decision) and the accept/reject verdict -/

/-- A CRL reduced to what the revocation decision needs (RFC 5280 §5.1): the
decoded validity window, the revoked serials, and the signed `tbsCertList` with
its signature. -/
structure Crl where
  /-- The decoded `thisUpdate`/`nextUpdate` window. -/
  window : Window
  /-- The revoked serials. -/
  revoked : List Serial
  /-- The signed `tbsCertList` bytes. -/
  tbs : ByteArray
  /-- The issuer's signature over `tbs`. -/
  signature : ByteArray

/-- The accept/reject verdict on the certificate under test. -/
inductive Decision where
  | accept
  | reject
deriving Repr, DecidableEq

/-- Is `serial` on the CRL? -/
def isRevoked (crl : Crl) (serial : Serial) : Bool :=
  crl.revoked.contains serial

/-- **The CRL accept/reject decision.** Accept the certificate iff, in order:
the issuer's signature over the `tbsCertList` verifies, the CRL is fresh
(RFC 5280 §6.3.3), and the certificate's serial is not on the revoked list. An
invalid signature, a stale CRL, or a listed serial all reject. -/
def checkCert (verify : Verifier) (issuerKey : ByteArray)
    (crl : Crl) (serial : Serial) (now : Nat) : Decision :=
  if verify issuerKey crl.tbs crl.signature = false then .reject
  else if isFresh crl.window now = false then .reject
  else if isRevoked crl serial then .reject
  else .accept

/-! ## Roundtrip lemmas -/

/-- Splitting an appended prefix: `(s ++ rest).take s.length = s`. -/
theorem take_left (s rest : Bytes) : (s ++ rest).take s.length = s := by
  induction s with
  | nil => simp
  | cons a l ih => simp [ih]

/-- Splitting an appended prefix: `(s ++ rest).drop s.length = rest`. -/
theorem drop_left (s rest : Bytes) : (s ++ rest).drop s.length = rest := by
  induction s with
  | nil => simp
  | cons a l ih => simp [ih]

/-- A `UInt8` length octet recovers a byte count below 256. -/
theorem toNat_ofNat_len (s : Bytes) (h : s.length < 256) :
    (UInt8.ofNat s.length).toNat = s.length := by
  simp [UInt8.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- A length-prefixed field roundtrips (short-form length): parsing the encoding
of `f` followed by any `rest` recovers `f` and leaves `rest`. -/
theorem parseField_encodeField (f rest : Bytes) (h : f.length < 256) :
    parseField (encodeField f ++ rest) = some (f, rest) := by
  have hlen : (UInt8.ofNat f.length).toNat = f.length := toNat_ofNat_len f h
  simp only [encodeField, List.cons_append, parseField, hlen]
  have hge : ¬ (f ++ rest).length < f.length := by
    simp [List.length_append]
  rw [if_neg hge, take_left, drop_left]

/-- The revoked-serials list roundtrips when every serial fits the short-form
length octet (`< 256`), which every RFC 5280 §4.1.2.2 serial does. -/
theorem parseSerials_encodeSerials (l : List Serial)
    (h : ∀ s ∈ l, s.length < 256) :
    parseSerials (encodeSerials l) = some l := by
  induction l with
  | nil => simp [encodeSerials, parseSerials]
  | cons s tl ih =>
      have hs : s.length < 256 := h s (List.mem_cons_self)
      have htl : ∀ x ∈ tl, x.length < 256 := fun x hx => h x (List.mem_cons_of_mem s hx)
      have hlen : (UInt8.ofNat s.length).toNat = s.length := toNat_ofNat_len s hs
      unfold encodeSerials encodeSerial
      simp only [List.cons_append, parseSerials, beq_self_eq_true, if_true, hlen]
      have hge : ¬ (s ++ encodeSerials tl).length < s.length := by
        simp [List.length_append]
      rw [if_neg hge, take_left, drop_left, ih htl]
      simp

/-! ## Theorem 1: the CRL parse recovers thisUpdate/nextUpdate + the serials -/

/-- **crl_parses.** An encoded `TBSCertList` parses back to exactly the
`thisUpdate`, `nextUpdate`, and the list of revoked serials the issuer wrote
(RFC 5280 §5.1.2) — under the short-form bound on the `Time` fields and every
serial. The parse is a left inverse of the encoder: it never drops, reorders,
truncates, or invents a serial, and it recovers the validity-window `Time`
octets verbatim. -/
theorem crl_parses (t : TBSCertList)
    (htu : t.thisUpdate.length < 256) (hnu : t.nextUpdate.length < 256)
    (hrev : ∀ s ∈ t.revoked, s.length < 256) :
    parseTBS (encodeTBS t) = some t := by
  unfold parseTBS encodeTBS
  rw [List.append_assoc]
  rw [parseField_encodeField t.thisUpdate _ htu]
  simp only [bind, Option.bind]
  rw [parseField_encodeField t.nextUpdate _ hnu]
  simp only [Option.bind]
  rw [parseSerials_encodeSerials t.revoked hrev]

/-! ## Theorem 2: a revoked certificate is rejected -/

/-- **crl_revoked_rejected.** A certificate whose serial is on the CRL is
rejected — even in the best case for the certificate, where the issuer's
signature verifies and the CRL is fresh. Revocation is terminal: no other field
can rescue a listed certificate. -/
theorem crl_revoked_rejected (verify : Verifier) (key : ByteArray)
    (crl : Crl) (serial : Serial) (now : Nat)
    (hlisted : isRevoked crl serial = true) :
    checkCert verify key crl serial now = .reject := by
  unfold checkCert
  by_cases hv : verify key crl.tbs crl.signature = false
  · simp [hv]
  · by_cases hf : isFresh crl.window now = false
    · simp [hv, hf]
    · simp [hv, hf, hlisted]

/-! ## Theorem 3: a stale CRL is not trusted (RFC 5280 §6.3.3) -/

/-- **crl_stale_rejected.** A CRL whose `nextUpdate` has passed (`nextUpdate <
now`) is stale and not trusted: the certificate is rejected (conservative
hard-fail) even for a signature-valid CRL that does not list the serial. Without
this gate an expired CRL — which cannot reflect revocations issued after it —
would be trusted, masking a fresh revocation (RFC 5280 §6.3.3). -/
theorem crl_stale_rejected (verify : Verifier) (key : ByteArray)
    (crl : Crl) (serial : Serial) (now : Nat)
    (hstale : crl.window.nextUpdate < now) :
    checkCert verify key crl serial now = .reject := by
  unfold checkCert
  have hf : isFresh crl.window now = false := by
    unfold isFresh
    apply decide_eq_false
    intro ⟨_, hle⟩
    omega
  by_cases hv : verify key crl.tbs crl.signature = false
  · simp [hv]
  · simp [hv, hf]

/-! ## Non-vacuity: the accept path is reachable

`crl_revoked_rejected` and `crl_stale_rejected` would be vacuous if `checkCert`
rejected everything. It does not: a signature-valid, fresh CRL that does not list
the serial accepts. -/

/-- A concrete verifier that always accepts (a stand-in honest oracle for the
accept-path witness). -/
def acceptAll : Verifier := fun _ _ _ => true

/-- **crl_good_accepts (non-vacuity).** A fresh, signature-valid CRL that does
not list the certificate's serial accepts it — so the reject theorems are not
vacuously rejecting all inputs. -/
theorem crl_good_accepts (key : ByteArray) (crl : Crl) (serial : Serial) (now : Nat)
    (hnl : isRevoked crl serial = false)
    (hfresh : crl.window.thisUpdate ≤ now ∧ now ≤ crl.window.nextUpdate) :
    checkCert acceptAll key crl serial now = .accept := by
  unfold checkCert
  have hv : ¬ (acceptAll key crl.tbs crl.signature = false) := by simp [acceptAll]
  have hf : ¬ (isFresh crl.window now = false) := by
    have ht : isFresh crl.window now = true := by unfold isFresh; simp [hfresh]
    simp [ht]
  rw [if_neg hv, if_neg hf]
  simp [hnl]

/-! ## A mutant: dropping the freshness gate is unsound

The freshness gate in `checkCert` is load-bearing. `checkCertNoFresh` is
`checkCert` with the `isFresh` clause removed; it trusts a stale CRL that
`checkCert` rejects. The disagreement witnesses that `crl_stale_rejected` is
testing a real behavior, not a tautology. -/

/-- The mutant decision: `checkCert` without the RFC 5280 §6.3.3 freshness gate. -/
def checkCertNoFresh (verify : Verifier) (issuerKey : ByteArray)
    (crl : Crl) (serial : Serial) (_now : Nat) : Decision :=
  if verify issuerKey crl.tbs crl.signature = false then .reject
  else if isRevoked crl serial then .reject
  else .accept

/-- A concrete stale CRL: window `[100, 200]`, revoking serial `[0x2A]`, checked
at `now = 1000` (well past `nextUpdate`) against the *unrevoked* serial `[0x07]`.
The real check rejects (stale); the mutant accepts. -/
def staleCrl : Crl where
  window := { thisUpdate := 100, nextUpdate := 200 }
  revoked := [[0x2A]]
  tbs := ⟨#[]⟩
  signature := ⟨#[]⟩

/-- **mutant_disagrees.** On the stale CRL the mutant (no freshness gate) ACCEPTS
the unrevoked serial while the real `checkCert` REJECTS it — the freshness gate
changes the verdict, so `crl_stale_rejected` guards a real behavior. -/
theorem mutant_disagrees :
    checkCertNoFresh acceptAll ⟨#[]⟩ staleCrl [0x07] 1000 = .accept
    ∧ checkCert acceptAll ⟨#[]⟩ staleCrl [0x07] 1000 = .reject := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## Issuer authenticity — the forged-CRL reject (EUF-CMA shadow)

The opaque signature oracle is what separates a forged CRL from acceptance.
`IssuerAuthentic` is the functional shadow of the issuer key's unforgeability,
stated exactly as `Pki.OcspResponse.ResponderAuthentic` is: under the issuer's
key, the verifier accepts a `(message, signature)` only when the issuer actually
signed that message. It is a per-issuer `Prop` hypothesis, never a Lean axiom. -/

/-- **Issuer authenticity (EUF-CMA functional shadow).** Under key `key`, the
verifier accepts `(tbs, sig)` only when `signed tbs` — the issuer genuinely
signed those `tbsCertList` bytes. -/
def IssuerAuthentic (verify : Verifier) (key : ByteArray)
    (signed : ByteArray → Prop) : Prop :=
  ∀ tbs sig, verify key tbs sig = true → signed tbs

/-- **crl_forged_rejected.** Under issuer authenticity for a key that signed only
genuine `tbsCertList` bytes, a CRL carrying `tbs` the issuer never signed causes
the certificate to be rejected — a forged or substituted CRL (e.g. a fabricated
empty list that omits a real revocation) never verifies against the honest
issuer's key, so it can never be trusted to accept a certificate. -/
theorem crl_forged_rejected (verify : Verifier) (key : ByteArray)
    (signed : ByteArray → Prop) (crl : Crl) (serial : Serial) (now : Nat)
    (hauth : IssuerAuthentic verify key signed)
    (hforged : ¬ signed crl.tbs) :
    checkCert verify key crl serial now = .reject := by
  unfold checkCert
  have hv : verify key crl.tbs crl.signature = false := by
    rcases Bool.eq_false_or_eq_true (verify key crl.tbs crl.signature) with h | h
    · exact absurd (hauth crl.tbs crl.signature h) hforged
    · exact h
  simp [hv]

/-! ## Non-vacuity of the forged-reject: a concrete authentic verifier fires -/

/-- A concrete authentic verifier: accepts iff the message content equals the
genuine `tbs` content (and only then). Inhabits `IssuerAuthentic`. -/
def demoVerify (genuine : ByteArray) : Verifier :=
  fun _key msg _sig => msg.data.toList == genuine.data.toList

theorem demoVerify_authentic (key genuine : ByteArray) :
    IssuerAuthentic (demoVerify genuine) key
      (fun m => m.data.toList = genuine.data.toList) := by
  intro tbs sig h
  simp only [demoVerify] at h
  exact eq_of_beq h

/-! ## Sanity: a concrete parse (RFC 5280 §5.1.2) -/

/-- A concrete `TBSCertList`: `thisUpdate`/`nextUpdate` two-octet `Time` stand-ins
and two revoked serials `[0x2A]`, `[0x01, 0x00]`. -/
def demoTBS : TBSCertList where
  thisUpdate := [0x18, 0x0F]
  nextUpdate := [0x18, 0x0F]
  revoked := [[0x2A], [0x01, 0x00]]

example : parseTBS (encodeTBS demoTBS) = some demoTBS :=
  crl_parses demoTBS (by decide) (by decide) (by decide)
example : encodeSerial [0x2A] = [0x02, 0x01, 0x2A] := by decide
example : isRevoked staleCrl [0x2A] = true := by decide
example : isRevoked staleCrl [0x07] = false := by decide

/-! ## Axiom audit -/

#print axioms crl_parses
#print axioms crl_revoked_rejected
#print axioms crl_stale_rejected
#print axioms crl_good_accepts
#print axioms mutant_disagrees
#print axioms crl_forged_rejected

end Pki.Crl
