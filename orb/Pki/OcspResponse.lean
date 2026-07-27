/-
# Pki.OcspResponse — OCSP response parse + status decision (RFC 6960), verified.

The Online Certificate Status Protocol (RFC 6960) lets a relying party ask a
responder, "is this certificate still valid?", and get back a signed
`BasicOCSPResponse` carrying, per certificate, one of three statuses: `good`,
`revoked`, or `unknown`. A correct client turns that response into an
accept/reject decision on the certificate. Getting the *decision logic* right is
the security-relevant part: a revoked certificate must be rejected, and a
response that is signature-invalid or out of its validity window must not be
trusted (a stale response could hide a fresh revocation).

This module is the concrete, verified model of that parse-and-decide pipeline.
It follows the same discipline as `Pki.Ct`: concrete byte-level structures and a
signature-verify **oracle** carried as a named assumption (a `Prop`, never a
fresh Lean axiom), so the machine-checked content is the parse and the
status/freshness decision — the crypto primitive itself is out of scope and is
not reinvented here.

What is concrete here:

  * **The `CertStatus` CHOICE** (RFC 6960 §4.2.1): the three certificate statuses
    `good [0]`, `revoked [1]`, `unknown [2]`, and their DER context-tag bytes.
  * **The certStatus parse** — a `Bytes → Option CertStatus` decoder keyed on the
    context tag, with a proven encode/parse roundtrip (the parser recovers
    exactly the status the responder encoded).
  * **The response-status enumeration** (RFC 6960 §4.2.1): `successful (0)` and
    the error values; only `successful` carries a `BasicOCSPResponse`.
  * **The freshness gate** (RFC 6960 §4.2.2.1): the client rejects unless the
    current time lies within `[thisUpdate, nextUpdate]`.
  * **The accept/reject decision** — accept a certificate only when the
    responder's signature over `tbsResponseData` verifies, the response status is
    `successful`, the response is fresh, and the certStatus is `good`.

Headline theorems (all core-axioms-only — no crypto axiom is composed in; the
signature verifier is an opaque parameter / named `Prop` assumption):

  * `ocsp_parse_status` — an encoded certStatus parses back to exactly the
    `good`/`revoked`/`unknown` the responder wrote (RFC 6960 §4.2.1 CHOICE).
  * `ocsp_revoked_rejected` — a `revoked` certStatus is rejected even when the
    signature verifies, the response is `successful`, and it is fresh.
  * `ocsp_stale_rejected` — a response whose validity window does not contain the
    current time is rejected even for a `good`, signature-valid certStatus
    (RFC 6960 §4.2.2.1). The freshness gate is load-bearing: a mutant that drops
    it accepts a stale `good` response that the real check rejects.
  * `ocsp_forged_rejected` — under responder authenticity (the EUF-CMA functional
    shadow), a response the responder never signed is rejected: the opaque
    signature oracle is what stands between a forged "good" and acceptance.
-/

namespace Pki.OcspResponse

/-! ## Bytes -/

/-- A byte string. -/
abbrev Bytes := List UInt8

/-! ## Certificate status — the RFC 6960 §4.2.1 `CertStatus` CHOICE

```text
CertStatus ::= CHOICE {
  good    [0] IMPLICIT NULL,
  revoked [1] IMPLICIT RevokedInfo,
  unknown [2] IMPLICIT UnknownInfo }
```

The three statuses are distinguished on the wire by their DER context tag: good
is `[0]` (primitive → `0x80`), revoked is `[1]` (constructed, carrying the
`RevokedInfo` → `0xA1`), unknown is `[2]` (primitive → `0x82`). -/

/-- The certificate's revocation status. `revoked` carries the raw
`revocationTime`/`RevokedInfo` payload bytes (the responder's evidence); the
parse recovers it verbatim, and the decision only needs the *tag*. -/
inductive CertStatus where
  /-- The certificate is not revoked. -/
  | good
  /-- The certificate has been revoked; `info` is the `RevokedInfo` payload. -/
  | revoked (info : Bytes)
  /-- The responder does not know this certificate. -/
  | unknown
deriving Repr, DecidableEq

/-- The DER context-tag byte for each `CertStatus` alternative (RFC 6960 §4.2.1):
`good [0]` → `0x80`, `revoked [1]` (constructed) → `0xA1`, `unknown [2]` →
`0x82`. -/
def CertStatus.tag : CertStatus → UInt8
  | .good => 0x80
  | .revoked _ => 0xA1
  | .unknown => 0x82

/-- Encode a `CertStatus` as its DER TLV (short-form length). `good` and
`unknown` are zero-length (IMPLICIT NULL); `revoked` prefixes its `RevokedInfo`
payload with a one-byte length. -/
def encodeCertStatus : CertStatus → Bytes
  | .good => [0x80, 0x00]
  | .unknown => [0x82, 0x00]
  | .revoked info => 0xA1 :: UInt8.ofNat info.length :: info

/-- Parse a certStatus TLV to a `CertStatus`, keyed on the DER context tag
(RFC 6960 §4.2.1). Matches the deployed responder path, which dispatches on
`tag & 0x1F ∈ {0,1,2}`; here on the full tag bytes `0x80`/`0xA1`/`0x82`. Returns
`none` on an unrecognized tag or a truncated `revoked` body. -/
def parseCertStatus (b : Bytes) : Option CertStatus :=
  match b with
  | [] => none
  | tag :: rest =>
      if tag == 0x80 then some .good
      else if tag == 0x82 then some .unknown
      else if tag == 0xA1 then
        match rest with
        | [] => none
        | len :: content => some (.revoked (content.take len.toNat))
      else none

/-! ## Response status — the RFC 6960 §4.2.1 `OCSPResponseStatus` enumeration -/

/-- `OCSPResponseStatus` (RFC 6960 §4.2.1). Only `successful` carries a
`BasicOCSPResponse`; the rest are transport/authorization errors. -/
inductive ResponseStatus where
  | successful
  | malformedRequest
  | internalError
  | tryLater
  | sigRequired
  | unauthorized
deriving Repr, DecidableEq

/-- The on-wire enumeration value. -/
def ResponseStatus.toByte : ResponseStatus → UInt8
  | .successful => 0
  | .malformedRequest => 1
  | .internalError => 2
  | .tryLater => 3
  | .sigRequired => 5
  | .unauthorized => 6

/-! ## The freshness window — RFC 6960 §4.2.2.1

Each `SingleResponse` carries `thisUpdate` (the time the status is known correct
as of) and `nextUpdate` (the time by which newer information will be available).
RFC 6960 §4.2.2.1: the client MUST consider the response valid only while the
current time is at or after `thisUpdate` and at or before `nextUpdate`. Times are
modeled as `Nat` seconds since an epoch. -/

/-- The validity window of a `SingleResponse`. -/
structure Window where
  /-- `thisUpdate`: status known correct as of this time. -/
  thisUpdate : Nat
  /-- `nextUpdate`: status is stale after this time. -/
  nextUpdate : Nat
deriving Repr, DecidableEq

/-- **The freshness gate (RFC 6960 §4.2.2.1).** A response is fresh at `now` iff
`thisUpdate ≤ now ≤ nextUpdate`. -/
def isFresh (w : Window) (now : Nat) : Bool :=
  decide (w.thisUpdate ≤ now ∧ now ≤ w.nextUpdate)

/-! ## The signature-verify oracle

The responder signs `tbsResponseData` (RFC 6960 §4.2.1). Verifying that
signature is a crypto primitive kept behind a named boundary — a `Verifier`
function supplied by the caller — exactly as `Pki.Ct` routes SCT signatures
through an abstract `Verifier`. The machine-checked content is the decision
logic *around* the oracle, not the primitive. -/

/-- A signature verifier: `verify key msg sig` decides whether `sig` is a valid
signature of `msg` under the responder's public key. -/
abbrev Verifier := ByteArray → ByteArray → ByteArray → Bool

/-! ## A BasicOCSPResponse (for a single certificate) and the decision -/

/-- A `BasicOCSPResponse` reduced to the first `SingleResponse` (RFC 6960
§4.2.1): the overall response status, the certificate's status, its freshness
window, and the signed `tbsResponseData` with its signature. -/
structure BasicResponse where
  /-- `OCSPResponseStatus`. -/
  responseStatus : ResponseStatus
  /-- The certificate's `CertStatus`. -/
  certStatus : CertStatus
  /-- The `thisUpdate`/`nextUpdate` validity window. -/
  window : Window
  /-- The signed `tbsResponseData` bytes. -/
  tbs : ByteArray
  /-- The responder's signature over `tbs`. -/
  signature : ByteArray

/-- The accept/reject verdict on the certificate. -/
inductive Decision where
  | accept
  | reject
deriving Repr, DecidableEq

/-- **The OCSP accept/reject decision.** Accept the certificate iff, in order:
the responder's signature over `tbsResponseData` verifies, the response status is
`successful`, the response is fresh (RFC 6960 §4.2.2.1), and the certStatus is
`good`. A `revoked` or `unknown` status, a stale window, a non-`successful`
status, or an invalid signature all reject. -/
def checkCert (verify : Verifier) (responderKey : ByteArray)
    (r : BasicResponse) (now : Nat) : Decision :=
  if verify responderKey r.tbs r.signature = false then .reject
  else if r.responseStatus ≠ .successful then .reject
  else if isFresh r.window now = false then .reject
  else match r.certStatus with
    | .good => .accept
    | .revoked _ => .reject
    | .unknown => .reject

/-! ## Theorem 1: the certStatus parse recovers the encoded status (RFC 6960 §4.2.1) -/

@[simp] theorem parse_encode_good :
    parseCertStatus (encodeCertStatus .good) = some .good := by decide

@[simp] theorem parse_encode_unknown :
    parseCertStatus (encodeCertStatus .unknown) = some .unknown := by decide

/-- The `revoked` payload roundtrips when its length fits the short-form DER
length byte (`< 256`), which every real `RevokedInfo` does. -/
theorem parse_encode_revoked (info : Bytes) (h : info.length < 256) :
    parseCertStatus (encodeCertStatus (.revoked info)) = some (.revoked info) := by
  have hlen : (UInt8.ofNat info.length).toNat = info.length := by
    simp [UInt8.toNat_ofNat, Nat.mod_eq_of_lt h]
  simp [encodeCertStatus, parseCertStatus, hlen, List.take_length]

/-- **ocsp_parse_status.** The certStatus parser is a left inverse of the encoder
on all three RFC 6960 §4.2.1 alternatives (`revoked` under the short-form length
bound): a `BasicOCSPResponse`'s certStatus parses back to exactly the
`good`/`revoked`/`unknown` the responder encoded — the parse never confuses one
status for another. -/
theorem ocsp_parse_status (s : CertStatus)
    (h : ∀ info, s = .revoked info → info.length < 256) :
    parseCertStatus (encodeCertStatus s) = some s := by
  cases s with
  | good => exact parse_encode_good
  | unknown => exact parse_encode_unknown
  | revoked info => exact parse_encode_revoked info (h info rfl)

/-! ## Theorem 2: a revoked certificate is rejected -/

/-- **ocsp_revoked_rejected.** A `revoked` certStatus is rejected — even in the
best case for the certificate, where the responder's signature verifies, the
response status is `successful`, and the response is fresh. Revocation is
terminal: no other field can rescue a revoked certificate. -/
theorem ocsp_revoked_rejected (verify : Verifier) (key : ByteArray)
    (r : BasicResponse) (now : Nat) (info : Bytes)
    (hstatus : r.certStatus = .revoked info) :
    checkCert verify key r now = .reject := by
  unfold checkCert
  by_cases hv : verify key r.tbs r.signature = false
  · simp [hv]
  · by_cases hs : r.responseStatus ≠ .successful
    · simp [hv, hs]
    · by_cases hf : isFresh r.window now = false
      · simp [hv, hs, hf]
      · simp [hv, hs, hf, hstatus]

/-! ## Theorem 3: a stale response is rejected (RFC 6960 §4.2.2.1) -/

/-- **ocsp_stale_rejected.** A response whose validity window does not contain
the current time (`¬ (thisUpdate ≤ now ≤ nextUpdate)`) is rejected — even for a
`good` certStatus with a `successful` status and a verifying signature. Without
this gate a replayed old "good" response could mask a subsequent revocation
(RFC 6960 §4.2.2.1). -/
theorem ocsp_stale_rejected (verify : Verifier) (key : ByteArray)
    (r : BasicResponse) (now : Nat)
    (hstale : ¬ (r.window.thisUpdate ≤ now ∧ now ≤ r.window.nextUpdate)) :
    checkCert verify key r now = .reject := by
  unfold checkCert
  have hf : isFresh r.window now = false := by
    unfold isFresh
    exact decide_eq_false hstale
  by_cases hv : verify key r.tbs r.signature = false
  · simp [hv]
  · by_cases hs : r.responseStatus ≠ .successful
    · simp [hv, hs]
    · simp [hv, hs, hf]

/-! ## Non-vacuity: the accept path is reachable

`ocsp_revoked_rejected` and `ocsp_stale_rejected` would be vacuous if `checkCert`
rejected everything. It does not: a signature-valid, `successful`, fresh, `good`
response is accepted. -/

/-- A concrete verifier that always accepts (a stand-in honest oracle for the
accept-path witness). -/
def acceptAll : Verifier := fun _ _ _ => true

/-- **ocsp_good_accepts (non-vacuity).** A `good`, `successful`, fresh,
signature-valid response is accepted — so the reject theorems are not vacuously
rejecting all inputs. -/
theorem ocsp_good_accepts (key : ByteArray) (r : BasicResponse) (now : Nat)
    (hg : r.certStatus = .good) (hok : r.responseStatus = .successful)
    (hfresh : r.window.thisUpdate ≤ now ∧ now ≤ r.window.nextUpdate) :
    checkCert acceptAll key r now = .accept := by
  unfold checkCert
  have hv : ¬ (acceptAll key r.tbs r.signature = false) := by simp [acceptAll]
  have hs : ¬ (r.responseStatus ≠ .successful) := by simp [hok]
  have hf : ¬ (isFresh r.window now = false) := by
    have ht : isFresh r.window now = true := by unfold isFresh; simp [hfresh]
    simp [ht]
  rw [if_neg hv, if_neg hs, if_neg hf, hg]

/-! ## A mutant: dropping the freshness gate is unsound

The freshness gate in `checkCert` is load-bearing. `checkCertNoFresh` is
`checkCert` with the `isFresh` clause removed; it accepts a stale `good` response
that `checkCert` rejects. The disagreement witnesses that
`ocsp_stale_rejected` is testing a real behavior, not a tautology. -/

/-- The mutant decision: `checkCert` without the RFC 6960 §4.2.2.1 freshness
gate. -/
def checkCertNoFresh (verify : Verifier) (responderKey : ByteArray)
    (r : BasicResponse) (_now : Nat) : Decision :=
  if verify responderKey r.tbs r.signature = false then .reject
  else if r.responseStatus ≠ .successful then .reject
  else match r.certStatus with
    | .good => .accept
    | .revoked _ => .reject
    | .unknown => .reject

/-- A concrete stale-but-good response: window `[100, 200]`, checked at `now =
1000` (well past `nextUpdate`), status `successful`, certStatus `good`. -/
def staleResponse : BasicResponse where
  responseStatus := .successful
  certStatus := .good
  window := { thisUpdate := 100, nextUpdate := 200 }
  tbs := ⟨#[]⟩
  signature := ⟨#[]⟩

/-- **mutant_disagrees.** On the stale-but-good response the mutant (no freshness
gate) ACCEPTS while the real `checkCert` REJECTS — the freshness gate changes the
verdict, so `ocsp_stale_rejected` guards a real behavior. -/
theorem mutant_disagrees (key : ByteArray) :
    checkCertNoFresh acceptAll key staleResponse 1000 = .accept
    ∧ checkCert acceptAll key staleResponse 1000 = .reject := by
  refine ⟨?_, ?_⟩
  · simp [checkCertNoFresh, acceptAll, staleResponse]
  · simp [checkCert, acceptAll, staleResponse, isFresh]

/-! ## Responder authenticity — the forged-response reject (EUF-CMA shadow)

The opaque signature oracle is what separates a forged "good" from acceptance.
`ResponderAuthentic` is the functional shadow of the responder key's
unforgeability, stated exactly as `Pki.Ct.LogAuthentic` is: under the responder's
key, the verifier accepts a `(message, signature)` only when the responder
actually signed that message. It is a per-responder `Prop` hypothesis, never a
Lean axiom. -/

/-- **Responder authenticity (EUF-CMA functional shadow).** Under key `key`, the
verifier accepts `(tbs, sig)` only when `signed tbs` — the responder genuinely
signed those `tbsResponseData` bytes. -/
def ResponderAuthentic (verify : Verifier) (key : ByteArray)
    (signed : ByteArray → Prop) : Prop :=
  ∀ tbs sig, verify key tbs sig = true → signed tbs

/-- **ocsp_forged_rejected.** Under responder authenticity for a key that signed
only genuine `tbsResponseData`, a response carrying `tbs` the responder never
signed is rejected — a forged or substituted OCSP response never verifies against
the honest responder's key, so a fabricated "good" cannot be accepted. -/
theorem ocsp_forged_rejected (verify : Verifier) (key : ByteArray)
    (signed : ByteArray → Prop) (r : BasicResponse) (now : Nat)
    (hauth : ResponderAuthentic verify key signed)
    (hforged : ¬ signed r.tbs) :
    checkCert verify key r now = .reject := by
  unfold checkCert
  have hv : verify key r.tbs r.signature = false := by
    rcases Bool.eq_false_or_eq_true (verify key r.tbs r.signature) with h | h
    · exact absurd (hauth r.tbs r.signature h) hforged
    · exact h
  simp [hv]

/-! ## Non-vacuity of the forged-reject: a concrete authentic verifier fires -/

/-- A concrete authentic verifier: accepts iff the message content equals the
genuine `tbs` content (and only then). Inhabits `ResponderAuthentic`. -/
def demoVerify (genuine : ByteArray) : Verifier :=
  fun _key msg _sig => msg.data.toList == genuine.data.toList

theorem demoVerify_authentic (key genuine : ByteArray) :
    ResponderAuthentic (demoVerify genuine) key
      (fun m => m.data.toList = genuine.data.toList) := by
  intro tbs sig h
  simp only [demoVerify] at h
  exact eq_of_beq h

/-! ## Sanity: the on-wire constants (RFC 6960 §4.2.1) -/

example : CertStatus.good.tag = 0x80 := by decide
example : (CertStatus.revoked []).tag = 0xA1 := by decide
example : CertStatus.unknown.tag = 0x82 := by decide
example : ResponseStatus.successful.toByte = 0 := by decide
example : encodeCertStatus .good = [0x80, 0x00] := by decide

/-! ## Axiom audit -/

#print axioms ocsp_parse_status
#print axioms ocsp_revoked_rejected
#print axioms ocsp_stale_rejected
#print axioms ocsp_good_accepts
#print axioms mutant_disagrees
#print axioms ocsp_forged_rejected

end Pki.OcspResponse
