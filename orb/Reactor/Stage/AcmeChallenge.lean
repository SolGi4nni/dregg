import Pki.Acme
import Reactor.Serialize
import Proto.Basic

/-!
# Reactor.Stage.AcmeChallenge — the HTTP-01 challenge route, landed on the serve

RFC 8555 §8.3 HTTP-01 validation: a certificate authority validating an
authorization for `<domain>` fetches

    GET http://<domain>/.well-known/acme-challenge/<token>

and accepts the authorization iff the responder returns exactly the **key
authorization** `token ‖ "." ‖ base64url(SHA-256(canonical-JWK(accountKey)))`
(RFC 8555 §8.1). The `Pki.Acme` library proves that value correct field-by-field
over the REAL `Crypto.sha256` (`Pki.Acme.keyAuthorization_correct`): the served
value passes CA validation, is exactly the §8.1 formula, and is never the bare
token (the classic HTTP-01 responder bug).

This module lands that proven value on the deployed serve as a request route.
`challengeResponse key req` answers a `GET /.well-known/acme-challenge/<token>`
with a `200` whose body IS `keyAuthorization <token> key` — computed at runtime
through the same verified-core hash the library reasons about — and passes every
other request through untouched (`challengeResponse … = none`, the wrapper then
routes to the inner serve). `Reactor.ServeConformant.conformantServe` consults
this route OUTERMOST, so the challenge fires on the live serve while every
non-challenge byte is unchanged.

Honest scope: `deployAcctKey` is a configured compile-time account key — the same
shape of residual as `Reactor.ServeConformant.deployNow` (the fixed `Date`
placeholder). The route serves the RFC §8.1 key authorization for *that* account
key; a CA that registered this account key accepts it (by
`keyAuthorization_correct` instantiated at the served token). Binding the account
key to a live ACME account object is a host-config seam, named here so the key is
not claimed to be loaded from a running registration.
-/

namespace Reactor.Stage.AcmeChallenge

open Proto (Bytes Request)
open Pki.Acme
  (AccountKey keyAuthorization clientServeHttp01 asciiBytes Http01Authz
   keyAuthorization_correct keyAuthorization_length keyAuthorization_formula
   keyAuthorization_ne_token http01_validate_iff thumbprint)

/-! ## Route constants -/

/-- ASCII `"GET"`. -/
def getBytes : Bytes := "GET".toUTF8.toList

/-- The HTTP-01 well-known path prefix (RFC 8555 §8.3). The route token is the
request target past this prefix. -/
def acmePrefix : Bytes := "/.well-known/acme-challenge/".toUTF8.toList

/-- ASCII `"Content-Type"`. -/
def ctName : Bytes := "Content-Type".toUTF8.toList

/-- ASCII `"text/plain"` — the media type RFC 8555 §8.3 expects for the responder
content. -/
def textPlain : Bytes := "text/plain".toUTF8.toList

/-- ASCII `"OK"`. -/
def okReason : Bytes := "OK".toUTF8.toList

/-! ## The deployed account key (configured constant — see residual) -/

/-- The deployed ACME account key. A fixed Ed25519 public key (JOSE `kty=OKP`,
`crv=Ed25519`); the served key authorization is keyed on its RFC 7638 JWK
thumbprint. Compile-time configured (residual): a live registration binds this to
an account object host-side; the route's correctness (`keyAuthorization_correct`)
holds of whatever key is deployed. -/
def deployAcctKey : AccountKey :=
  -- The deployed ACME account, as a P-256 (ES256) JWK — the SAME account the
  -- issuer registers via `DRORB_ACME_ACCOUNT_KEY` (thumbprint bmFxK…), so the
  -- served key authorization matches what the validating CA recomputes. ES256
  -- because Boulder/pebble reject EdDSA account keys. (Residual: still a
  -- compile-time constant; a runtime binding to the persisted account is future.)
  .p256
    [170, 233, 194, 155, 148, 251, 172, 187, 84, 135, 66, 12, 126, 97, 207, 137, 180, 188, 162, 57, 243, 98, 130, 167, 186, 126, 68, 202, 201, 222, 33, 56]
    [29, 121, 59, 39, 245, 197, 164, 17, 32, 243, 248, 38, 38, 37, 73, 232, 231, 29, 197, 60, 37, 137, 143, 197, 236, 221, 65, 167, 29, 68, 103, 16]

/-! ## The route -/

/-- The token carried in a challenge request target: the request-target bytes past
`acmePrefix`, read as ASCII characters (the CA's `<token>` is base64url, all ASCII). -/
def tokenOf (target : Bytes) : List Char :=
  (target.drop acmePrefix.length).map (fun b => Char.ofNat b.toNat)

/-- Whether a request is an HTTP-01 challenge fetch: method `GET`, target under the
well-known challenge prefix. -/
def inScope (req : Request) : Bool :=
  req.method == getBytes && acmePrefix.isPrefixOf req.target

/-- The `200` response the responder serves for a challenge token under `key`: body
is exactly the RFC §8.1 key authorization (`token ‖ "." ‖ base64url(thumbprint)`),
media type `text/plain`. -/
def challengeResp (token : List Char) (key : AccountKey) : Reactor.Response :=
  { status  := 200
  , reason  := okReason
  , headers := [(ctName, textPlain)]
  , body    := asciiBytes (keyAuthorization token key) }

/-- **The HTTP-01 challenge route.** A `GET /.well-known/acme-challenge/<token>`
is answered with the key authorization for `<token>` under `key`; every other
request yields `none` (the wrapper routes it to the inner serve untouched). -/
def challengeResponse (key : AccountKey) (req : Request) : Option Reactor.Response :=
  if inScope req then some (challengeResp (tokenOf req.target) key) else none

/-! ## What is proven -/

/-- **The route fires exactly on a challenge fetch.** A `GET` under the well-known
prefix is answered with `challengeResp (tokenOf target) key`. -/
theorem challenge_fires (key : AccountKey) (req : Request)
    (hm : req.method = getBytes)
    (hp : acmePrefix.isPrefixOf req.target = true) :
    challengeResponse key req = some (challengeResp (tokenOf req.target) key) := by
  simp [challengeResponse, inScope, hm, hp]

/-- **The route is identity off its scope.** A non-`GET` request, or a `GET` whose
target is not under the challenge prefix, yields `none` — the wrapper serves it
through the inner serve, byte-for-byte unchanged. -/
theorem challenge_none_off (key : AccountKey) (req : Request)
    (h : inScope req = false) :
    challengeResponse key req = none := by
  simp [challengeResponse, h]

/-- **The served body is the CA-accepted key authorization.** On a fired challenge,
the response body is `asciiBytes v` where `v = keyAuthorization (tokenOf target)
key` and, by `Pki.Acme.keyAuthorization_correct` instantiated at that token:

* `v` passes the CA's HTTP-01 validation (`Http01Authz.validate = true`) — it is
  the one value the CA holding `key` accepts;
* `v` is exactly the RFC §8.1 formula over the REAL SHA-256; and
* `v ≠ tokenOf target` — never the bare token (the classic responder bug is
  excluded).

Non-vacuous: `keyAuthorization_correct`'s validation is an `iff` with a single
accepting value, so this pins the served body to that unique CA-accepted string. -/
theorem challenge_body_ca_accepted (key : AccountKey) (token : List Char) :
    ∃ v : List Char,
      (challengeResp token key).body = asciiBytes v
      ∧ (Http01Authz.validate ⟨token, key⟩ v = true)
      ∧ v = token
          ++ ['.'] ++ Pki.Acme.base64url
                (Crypto.sha256 (Pki.Acme.asciiBA (Pki.Acme.canonicalJwk key))).toList
      ∧ v ≠ token := by
  refine ⟨keyAuthorization token key, rfl, ?_, ?_, ?_⟩
  · rw [http01_validate_iff]; rfl
  · exact keyAuthorization_formula token key
  · exact keyAuthorization_ne_token token key

/-- **The served body is strictly longer than the token** — a direct length
witness that the responder never serves just the token. -/
theorem challenge_body_gt_token (key : AccountKey) (token : List Char) :
    token.length < (asciiBytes (keyAuthorization token key)).length := by
  have : (asciiBytes (keyAuthorization token key)).length
      = (keyAuthorization token key).length := by
    simp [asciiBytes]
  rw [this, keyAuthorization_length]
  omega

/-! ## Non-vacuity — a concrete challenge path fires with a genuine key auth -/

/-- Any list is a prefix of itself appended with anything (byte-generic — no
concrete-list kernel reduction needed). -/
theorem isPrefixOf_self_append (p s : List UInt8) :
    p.isPrefixOf (p ++ s) = true := by
  induction p with
  | nil => rfl
  | cons a t ih => simp [ih]

/-- A concrete challenge request: `GET /.well-known/acme-challenge/tok0`. -/
def demoReq : Request :=
  { method := getBytes
  , target := acmePrefix ++ "tok0".toUTF8.toList
  , version := "HTTP/1.1".toUTF8.toList
  , headers := [] }

/-- The demo challenge fires and its body is the key authorization for its token. -/
theorem demo_fires :
    challengeResponse deployAcctKey demoReq
      = some (challengeResp (tokenOf demoReq.target) deployAcctKey) := by
  apply challenge_fires
  · rfl
  · exact isPrefixOf_self_append acmePrefix _

#print axioms challenge_fires
#print axioms challenge_none_off
#print axioms challenge_body_ca_accepted
#print axioms challenge_body_gt_token
#print axioms demo_fires

end Reactor.Stage.AcmeChallenge
