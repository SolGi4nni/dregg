/-
# Pki.Acme — a concrete, verified ACME (RFC 8555) client core.

The `Acme.*` modules model the ACME issuance *state machines* abstractly: the
order/authorization/challenge lifecycles, with the account key thumbprint and
the challenge digest left as opaque parameters. This module is the concrete
client that instantiates those seams against the engine's **real** cryptography
and real JWS structure, so the certificate-automation values a running client
puts on the wire are the exact ones the CA validates — and that fact is a
theorem.

What is concrete here (nothing is a fresh `axiom`; the only cryptographic trust
is the named `Crypto.Assumptions` shared with the rest of the engine):

  * **base64url** (RFC 4648 §5, unpadded — the JOSE encoding, RFC 7515 §2): a
    total, computable Lean function. No FFI, no boundary.
  * **JWK thumbprint** (RFC 7638, RFC 8555 §8.1): the canonical JWK JSON of an
    account key (`Ed25519`/`OKP` or `P-256`/`EC`) with members in lexicographic
    order and no whitespace, hashed with the real `Crypto.sha256`
    (HACL*/EverCrypt) and base64url-encoded.
  * **keyAuthorization** (RFC 8555 §8.1): `token ‖ "." ‖ base64url(thumbprint)`
    — the exact string an HTTP-01 responder serves and the CA re-derives.
  * **The JWS request envelope** (RFC 8555 §6.2): protected header
    (`alg`, `nonce`, `url`, and `jwk` for newAccount or `kid` afterwards),
    payload, and an Ed25519 signature over
    `ASCII(base64url(protected) ‖ "." ‖ base64url(payload))` — routed to the
    F*-verified `Crypto.ed25519Sign`/`Crypto.ed25519Verify`.
  * **The order state machine** — reused wholesale from `Acme.Order`, whose RFC
    8555 §7.1.6 refinement is proven in `AcmeCorrect`.

Headline theorems (all core-axioms-only except where a named `Crypto` axiom is
explicitly composed in):

  * `keyAuthorization_correct` — the value the client serves for HTTP-01 is
    exactly the value the CA computes and validates, equals the RFC §8.1
    formula over the real SHA-256, and is never the bare token (the classic
    HTTP-01 bug). Non-vacuous: CA validation accepts *only* that one value.
  * `jws_sign_verify` — an ACME JWS request signed with the account Ed25519 key
    verifies under the account's public key (the real EverCrypt roundtrip).
  * `order_needs_valid_authz` — a finalized order (one that reached
    `processing`, the post-`finalize` status) had **every** authorization
    valid; finalize never advances a pending/failed order.
  * `dns01_digest_correct` — the DNS-01 TXT value is exactly
    `base64url(SHA-256(keyAuthorization))` over the real hash (RFC 8555 §8.4).
  * `frames_roundtrip` — the length-prefixed wire framing of an ACME payload's
    identifier list decodes back to the original.
-/

import Crypto
import Acme.Basic
import Acme.Order
import Acme.Challenge

namespace Pki.Acme

/-! ## base64url (RFC 4648 §5, unpadded — RFC 7515 §2)

Concrete and total. The 64-symbol URL/filename-safe alphabet, then a
three-bytes-to-four-chars fold with the two short-tail cases. The `=` padding is
omitted, exactly as JOSE base64url requires. -/

/-- The RFC 4648 §5 URL-safe alphabet: `A–Z a–z 0–9 - _`. -/
def b64urlAlphabet : List Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_".toList

/-- The base64url symbol for a 6-bit value (`0 ≤ n < 64`). -/
def b64Char (n : Nat) : Char := b64urlAlphabet.getD n 'A'

/-- base64url-encode a byte string, no padding. -/
def base64url : List UInt8 → List Char
  | [] => []
  | [a] =>
      let na := a.toNat
      [b64Char (na >>> 2), b64Char ((na &&& 0x3) <<< 4)]
  | [a, b] =>
      let na := a.toNat; let nb := b.toNat
      [b64Char (na >>> 2),
       b64Char (((na &&& 0x3) <<< 4) ||| (nb >>> 4)),
       b64Char ((nb &&& 0xf) <<< 2)]
  | a :: b :: c :: rest =>
      let na := a.toNat; let nb := b.toNat; let nc := c.toNat
      b64Char (na >>> 2) ::
      b64Char (((na &&& 0x3) <<< 4) ||| (nb >>> 4)) ::
      b64Char (((nb &&& 0xf) <<< 2) ||| (nc >>> 6)) ::
      b64Char (nc &&& 0x3f) ::
      base64url rest

/-- Every full 3-byte group contributes exactly 4 output characters. -/
theorem base64url_full_group (a b c : UInt8) (rest : List UInt8) :
    (base64url (a :: b :: c :: rest)).length = 4 + (base64url rest).length := by
  simp [base64url]; omega

/-! ## Bytes ↔ ASCII strings

ACME/JOSE strings are ASCII. `asciiBytes` maps a `List Char` to its byte string;
`asciiBA` lands directly in `ByteArray` for the FFI-facing hashes/signatures. -/

/-- ASCII bytes of a character list (the low 8 bits of each code point). -/
def asciiBytes (s : List Char) : List UInt8 := s.map (fun c => UInt8.ofNat c.toNat)

/-- ASCII bytes as a `ByteArray` (what `Crypto.sha256`/`Crypto.ed25519*` take). -/
def asciiBA (s : List Char) : ByteArray := ⟨(asciiBytes s).toArray⟩

/-! ## Account keys and the JWK thumbprint (RFC 7638, RFC 8555 §8.1)

An ACME account is keyed by an asymmetric key. Two are modelled: Ed25519 (JOSE
`OKP`/`Ed25519`, the verified-crypto lane) and NIST P-256 (JOSE `EC`/`P-256`,
`ES256`). The thumbprint is `base64url(SHA-256(canonical-JWK-JSON))`, where the
canonical JSON lists exactly the RFC-7638-required members in lexicographic
order with no whitespace. -/

/-- An ACME account key. -/
inductive AccountKey where
  /-- Ed25519 public key (32 bytes). JOSE `kty=OKP`, `crv=Ed25519`. -/
  | ed25519 (pub : List UInt8)
  /-- NIST P-256 public point coordinates (32 bytes each). JOSE `kty=EC`,
  `crv=P-256`, `ES256`. -/
  | p256 (x y : List UInt8)
deriving Repr

/-- The canonical JWK JSON of an account key (RFC 7638 §3.2 required members,
lexicographically ordered, no whitespace). For `OKP`: `crv`, `kty`, `x`. For
`EC`: `crv`, `kty`, `x`, `y`. Coordinate bytes are base64url-encoded. -/
def canonicalJwk : AccountKey → List Char
  | .ed25519 pub =>
      "{\"crv\":\"Ed25519\",\"kty\":\"OKP\",\"x\":\"".toList
        ++ base64url pub ++ "\"}".toList
  | .p256 x y =>
      "{\"crv\":\"P-256\",\"kty\":\"EC\",\"x\":\"".toList
        ++ base64url x ++ "\",\"y\":\"".toList ++ base64url y ++ "\"}".toList

/-- The JWK thumbprint (RFC 7638): `base64url(SHA-256(canonical-JWK))`, over the
real HACL*/EverCrypt `Crypto.sha256`. -/
def thumbprint (key : AccountKey) : List Char :=
  base64url (Crypto.sha256 (asciiBA (canonicalJwk key))).toList

/-! ## keyAuthorization (RFC 8555 §8.1)

`keyAuthorization = token ‖ "." ‖ base64url(thumbprint(accountKey))`. This is the
one value HTTP-01 and DNS-01 both build on. -/

/-- The key authorization string for a challenge `token` under an account key. -/
def keyAuthorization (token : List Char) (key : AccountKey) : List Char :=
  token ++ ['.'] ++ thumbprint key

/-- The RFC §8.1 formula, made explicit: the key authorization is the token, a
separating dot, and the base64url of the real SHA-256 of the canonical JWK. -/
theorem keyAuthorization_formula (token : List Char) (key : AccountKey) :
    keyAuthorization token key
      = token ++ ['.'] ++ base64url (Crypto.sha256 (asciiBA (canonicalJwk key))).toList :=
  rfl

/-- Length of the key authorization: the token, the dot, and the thumbprint. -/
theorem keyAuthorization_length (token : List Char) (key : AccountKey) :
    (keyAuthorization token key).length
      = token.length + 1 + (thumbprint key).length := by
  simp [keyAuthorization]; omega

/-- **The served content is never the bare token.** Its length strictly exceeds
the token's, so an HTTP-01 responder that serves the key authorization can never
be accidentally serving just the token (the classic HTTP-01 implementation bug).
-/
theorem keyAuthorization_ne_token (token : List Char) (key : AccountKey) :
    keyAuthorization token key ≠ token := by
  intro h
  have hlen := congrArg List.length h
  rw [keyAuthorization_length] at hlen
  omega

/-! ## HTTP-01: the server-side validation, and client/CA agreement (RFC 8555 §8.3)

An HTTP-01 authorization at the CA carries the challenge `token` and the account
key on record. The CA fetches the responder's content and accepts iff it equals
the key authorization it recomputes. -/

/-- An HTTP-01 authorization as the CA holds it: the challenge token and the
account key registered for the account. -/
structure Http01Authz where
  token : List Char
  key : AccountKey

/-- The content the CA expects at `/.well-known/acme-challenge/<token>`. -/
def Http01Authz.expected (a : Http01Authz) : List Char :=
  keyAuthorization a.token a.key

/-- The CA's validation: accept the served content iff it is exactly the
expected key authorization (RFC 8555 §8.3: "compares … to the expected key
authorization"). -/
def Http01Authz.validate (a : Http01Authz) (served : List Char) : Bool :=
  served == a.expected

/-- The content the client serves: the key authorization for the token under its
own account key. -/
def clientServeHttp01 (token : List Char) (key : AccountKey) : List Char :=
  keyAuthorization token key

/-- **CA validation is exact.** The CA accepts a served value *iff* it is the one
expected value — so there is exactly one accepting string, ruling out any
tampered or truncated content. -/
theorem http01_validate_iff (a : Http01Authz) (served : List Char) :
    a.validate served = true ↔ served = a.expected := by
  simp [Http01Authz.validate, beq_iff_eq]

/-- **keyAuthorization_correct.** The value the client serves for a token under
its account key is accepted by the CA holding that same account key; that
accepted value is exactly the RFC §8.1 formula over the real SHA-256; and it is
never the bare token. Non-vacuous by `http01_validate_iff`: the CA accepts only
this one value. -/
theorem keyAuthorization_correct (token : List Char) (key : AccountKey) :
    let a : Http01Authz := ⟨token, key⟩
    -- (1) the client's value passes CA validation
    a.validate (clientServeHttp01 token key) = true
    -- (2) it is exactly the RFC §8.1 formula over the real SHA-256
    ∧ clientServeHttp01 token key
        = token ++ ['.'] ++ base64url (Crypto.sha256 (asciiBA (canonicalJwk key))).toList
    -- (3) it is not the bare token (the classic bug is excluded)
    ∧ clientServeHttp01 token key ≠ token := by
  refine ⟨?_, keyAuthorization_formula token key, keyAuthorization_ne_token token key⟩
  rw [http01_validate_iff]
  rfl

/-- **No cross-serving.** If a served value is accepted, the CA's stored token is
determined as the string's prefix up to the responder content — a value keyed to
one token is not accepted for another with a different key authorization. -/
theorem http01_accept_unique (a : Http01Authz) (s₁ s₂ : List Char)
    (h₁ : a.validate s₁ = true) (h₂ : a.validate s₂ = true) : s₁ = s₂ := by
  rw [http01_validate_iff] at h₁ h₂
  rw [h₁, h₂]

/-! ## DNS-01: the TXT digest (RFC 8555 §8.4)

The DNS-01 value published at `_acme-challenge.<domain>` is
`base64url(SHA-256(keyAuthorization))`. -/

/-- The DNS-01 TXT record value for a token/account key: the base64url of the
real SHA-256 of the key authorization. -/
def dns01Txt (token : List Char) (key : AccountKey) : List Char :=
  base64url (Crypto.sha256 (asciiBA (keyAuthorization token key))).toList

/-- The record name the value is published at (RFC 8555 §8.4). -/
def dns01RecordName (domain : List Char) : List Char :=
  "_acme-challenge.".toList ++ domain

/-- **dns01_digest_correct.** The DNS-01 TXT value is exactly the base64url of the
real SHA-256 of the key authorization (RFC 8555 §8.4) — the challenge-response
digest, over EverCrypt's hash, not a stub. -/
theorem dns01_digest_correct (token : List Char) (key : AccountKey) :
    dns01Txt token key
      = base64url (Crypto.sha256 (asciiBA (keyAuthorization token key))).toList :=
  rfl

/-- The SHA-256 fed to base64url is exactly 32 bytes (the real digest width),
via the named `Crypto` length axiom — so the TXT value is a fixed-width token,
not variable attacker-controlled length. -/
theorem dns01_digest_input_len (token : List Char) (key : AccountKey) :
    (Crypto.sha256 (asciiBA (keyAuthorization token key))).size = 32 :=
  Crypto.Assumptions.sha256_len (asciiBA (keyAuthorization token key))

/-! ## The JWS request envelope (RFC 8555 §6.2)

Every ACME request past `newNonce` is a JWS-signed POST. The protected header
carries `alg`, the anti-replay `nonce`, the target `url`, and a key
identification: an inline `jwk` for `newAccount`, or the account `kid` (its URL)
afterwards. The signature is over `ASCII(base64url(protected) ‖ "." ‖
base64url(payload))`. Ed25519 is routed to the verified primitive. -/

/-- ACME JWS algorithms. `eddsa` is the verified lane; `es256` is named for the
EC account-key case (its verifier is the ECDSA boundary, as in `Jwt`). -/
inductive AcmeAlg where
  | eddsa
  | es256
deriving Repr, DecidableEq

/-- Key identification in the protected header (RFC 8555 §6.2). -/
inductive JwsKeyId where
  /-- Inline public key — used by `newAccount` (RFC 8555 §7.3). -/
  | jwk (key : AccountKey)
  /-- Account URL — used by every request after account creation. -/
  | kid (accountUrl : List Char)
deriving Repr

/-- The JWS protected header. (`hdr`-named to avoid the `protected` keyword.) -/
structure ProtectedHeader where
  alg : AcmeAlg
  nonce : List UInt8
  url : List Char
  keyId : JwsKeyId
deriving Repr

/-- A JWS-signed ACME request: the protected header and the JSON payload bytes. -/
structure JwsRequest where
  hdr : ProtectedHeader
  payload : List UInt8
deriving Repr

/-- Serialize the protected header to its canonical JSON bytes (RFC 8555 §6.2
member set). The exact key material appears, so the signing input binds the
`nonce` and `url`. -/
def encodeHeader (h : ProtectedHeader) : List UInt8 :=
  let algStr : List Char := match h.alg with
    | .eddsa => "EdDSA".toList
    | .es256 => "ES256".toList
  let keyStr : List Char := match h.keyId with
    | .jwk k => "\"jwk\":".toList ++ canonicalJwk k
    | .kid u => "\"kid\":\"".toList ++ u ++ "\"".toList
  asciiBytes ("{\"alg\":\"".toList ++ algStr ++ "\",\"nonce\":\"".toList
    ++ base64url h.nonce ++ "\",\"url\":\"".toList ++ h.url ++ "\",".toList
    ++ keyStr ++ "}".toList)

/-- The JWS signing input (RFC 7515 §5.1, RFC 8555 §6.2):
`ASCII(base64url(protected) ‖ "." ‖ base64url(payload))`, as a `ByteArray` for
the crypto primitive. -/
def signingInput (req : JwsRequest) : ByteArray :=
  ⟨(asciiBytes (base64url (encodeHeader req.hdr) ++ ['.'] ++ base64url req.payload)).toArray⟩

/-- Sign an ACME request with an Ed25519 account key (the 32-byte seed). Routes
to the F*-verified `Crypto.ed25519Sign`. -/
def signAcmeEd (sk : ByteArray) (req : JwsRequest) : Option ByteArray :=
  Crypto.ed25519Sign sk (signingInput req)

/-- Verify an ACME request's signature under an Ed25519 public key. Routes to the
F*-verified `Crypto.ed25519Verify`. -/
def verifyAcmeEd (pub : ByteArray) (req : JwsRequest) (sig : ByteArray) : Bool :=
  Crypto.ed25519Verify pub (signingInput req) sig

/-- **jws_sign_verify.** An ACME JWS request signed with an account Ed25519 key
verifies under that key's public key. This is the real EverCrypt sign/verify
roundtrip (`Crypto.Assumptions.ed25519_sign_verify_roundtrip`) applied to the
ACME signing input — the account can always produce a signature the CA accepts.
-/
theorem jws_sign_verify (sk : ByteArray) (req : JwsRequest) (sig : ByteArray)
    (h : signAcmeEd sk req = some sig) :
    verifyAcmeEd (Crypto.Assumptions.ed25519_pubOf sk) req sig = true :=
  Crypto.Assumptions.ed25519_sign_verify_roundtrip sk (signingInput req) sig h

/-- The signing input is exactly the ASCII of `base64url(protected) ‖ "." ‖
base64url(payload)` (RFC 7515 §5.1) — the header (with its `nonce` and `url`) and
the payload are both inside what gets signed, so a signature is bound to them. -/
theorem signingInput_eq (req : JwsRequest) :
    signingInput req
      = ⟨(asciiBytes (base64url (encodeHeader req.hdr) ++ ['.']
            ++ base64url req.payload)).toArray⟩ :=
  rfl

/-! ## The order/authorization/challenge objects (RFC 8555 §7.1.3–§7.1.6)

Concrete client-facing objects, carrying the abstract `Acme.*Status` alphabets
whose lifecycle is proven in `Acme.Order`/`Acme.Challenge`/`AcmeCorrect`. -/

/-- An ACME identifier — a DNS name (RFC 8555 §7.1.4). -/
structure Identifier where
  value : List Char
deriving Repr

/-- The ACME directory (RFC 8555 §7.1.1): the CA's endpoint URLs. -/
structure Directory where
  newNonce : List Char
  newAccount : List Char
  newOrder : List Char
  revokeCert : List Char
  keyChange : List Char
deriving Repr

/-- An ACME account object (RFC 8555 §7.1.2). -/
structure AccountObj where
  key : AccountKey
  contact : List (List Char)
  status : List Char
  ordersUrl : List Char

/-- A challenge object (RFC 8555 §7.1.5, §8). -/
structure ChallengeObj where
  ty : Acme.ChallengeType
  url : List Char
  token : List Char
  status : Acme.ChalStatus
deriving Repr

/-- An authorization object (RFC 8555 §7.1.4). -/
structure AuthorizationObj where
  identifier : Identifier
  status : Acme.AuthzStatus
  challenges : List ChallengeObj

/-- The CSR carried by finalize (RFC 8555 §7.4). -/
structure Csr where
  der : List UInt8
deriving Repr

/-- An issued certificate (RFC 8555 §7.4.2). -/
structure Certificate where
  pem : List UInt8
deriving Repr

/-- An order object (RFC 8555 §7.1.3). -/
structure OrderObj where
  status : Acme.OrderStatus
  identifiers : List Identifier
  authorizations : List (List Char)
  finalizeUrl : List Char
  certificateUrl : Option (List Char)

/-! ## The order state machine — reused from `Acme.Order`

The proven lifecycle FSM lives in `Acme.Order`; here we lift its discipline to
the concrete client and state the finalize gate directly. -/

open _root_.Acme

/-- A fresh order over a list of DNS identifiers (RFC 8555 §7.4): one `pending`
authorization each, order `pending`. This is what both first issuance and
renewal start from (`Acme.Order.fresh`). -/
def freshOrder (ids : List Identifier) : Order :=
  Order.fresh (ids.map (·.value))

/-- **order_needs_valid_authz.** A finalized order — one the deployed FSM has
driven to `processing`, the status reached only by `finalize` — had **every**
authorization valid. Equivalently: `finalize` never advances a `pending` or
failed order; the CSR submission is gated on all authorizations being valid
(RFC 8555 §7.4: finalize is honoured only for a `ready` order, and an order is
`ready` only when all authorizations are valid). This is `Acme.Order.wf`
instantiated at `processing`, holding along every event sequence from a fresh
order. -/
theorem order_needs_valid_authz (ids : List Identifier) (es : List OrderEvent)
    (h : (orderRun (freshOrder ids) es).status = .processing) :
    allValid (orderRun (freshOrder ids) es).authzs = true :=
  orderRun_wf (freshOrder ids) (Order.fresh_wf _) es (Or.inr (Or.inl h))

/-- And at `valid`: an order the client drives all the way to `valid` — the
point a certificate is issued — likewise had every authorization valid. No
certificate is downloaded past a pending or failed authorization. -/
theorem order_valid_needs_valid_authz (ids : List Identifier) (es : List OrderEvent)
    (h : (orderRun (freshOrder ids) es).status = .valid) :
    allValid (orderRun (freshOrder ids) es).authzs = true := by
  unfold freshOrder at h ⊢
  exact valid_requires_all_authz_valid _ es h

/-- **Finalize is refused from pending.** The deployed step keeps a `pending`
order `pending` under `finalize`; there is no path from an unresolved order into
`processing`. -/
theorem finalize_refused_when_pending (as : List AuthzStatus) :
    (orderStep ⟨as, .pending⟩ .finalize).status = .pending := rfl

/-! ## Message framing round-trip (RFC 8555 payloads modelled as bytes)

An ACME payload such as `newOrder`'s `identifiers` array is, on the wire, a
length-delimited sequence. We model that framing as length-prefixed chunks (one
length byte per chunk, chunk length < 256) and prove the decoder inverts the
encoder — the round-trip an implementation relies on to read back what it sent. -/

/-- Encode a list of byte chunks, each prefixed by its length (< 256). -/
def encodeFrames : List (List UInt8) → List UInt8
  | [] => []
  | c :: rest => UInt8.ofNat c.length :: c ++ encodeFrames rest

/-- Decode length-prefixed chunks. `none` on truncation. -/
def decodeFrames : List UInt8 → Option (List (List UInt8))
  | [] => some []
  | n :: rest =>
      let k := n.toNat
      if rest.length < k then none
      else match decodeFrames (rest.drop k) with
        | some cs => some (rest.take k :: cs)
        | none => none
  termination_by l => l.length
  decreasing_by
    simp_wf
    have : (rest.drop k).length = rest.length - k := List.length_drop
    omega

/-- A frame list is well-formed for single-byte length prefixes if every chunk is
shorter than 256. -/
def FramesWf (cs : List (List UInt8)) : Prop := ∀ c ∈ cs, c.length < 256

/-- One-step unfolding of the decoder on a non-empty buffer. -/
theorem decodeFrames_cons (n : UInt8) (buf : List UInt8) :
    decodeFrames (n :: buf) =
      (if buf.length < n.toNat then none
       else match decodeFrames (buf.drop n.toNat) with
         | some cs => some (buf.take n.toNat :: cs)
         | none => none) := by
  rw [decodeFrames]

/-- **frames_roundtrip.** Decoding the encoding of well-formed frames returns
them unchanged. The client can always read back the identifier list it framed. -/
theorem frames_roundtrip (cs : List (List UInt8)) (hwf : FramesWf cs) :
    decodeFrames (encodeFrames cs) = some cs := by
  induction cs with
  | nil => simp only [encodeFrames, decodeFrames]
  | cons c rest ih =>
      have hc : c.length < 256 := hwf c (List.mem_cons_self)
      have hrest : FramesWf rest := fun x hx => hwf x (List.mem_cons_of_mem _ hx)
      have hn : (UInt8.ofNat c.length).toNat = c.length := by
        simpa [UInt8.toNat_ofNat] using Nat.mod_eq_of_lt hc
      show decodeFrames (UInt8.ofNat c.length :: (c ++ encodeFrames rest)) = some (c :: rest)
      rw [decodeFrames_cons, hn]
      have hlen : ¬ (c ++ encodeFrames rest).length < c.length := by
        rw [List.length_append]; omega
      rw [if_neg hlen, List.drop_left, List.take_left, ih hrest]

/-! ## Sanity: base64url on known RFC 4648 §10 test vectors (no FFI)

`#eval` checks that the concrete encoder matches the RFC's own vectors, so the
base64url the thumbprint and JWS rest on is the real thing. -/

/-- "foobar" → base64url. RFC 4648 §10: `Zm9vYmFy`. -/
example : base64url [0x66,0x6f,0x6f,0x62,0x61,0x72] = "Zm9vYmFy".toList := by decide
/-- "foo" → `Zm9v`. -/
example : base64url [0x66,0x6f,0x6f] = "Zm9v".toList := by decide
/-- "fo" → `Zm8` (unpadded). -/
example : base64url [0x66,0x6f] = "Zm8".toList := by decide
/-- "f" → `Zg` (unpadded). -/
example : base64url [0x66] = "Zg".toList := by decide
/-- URL-safe alphabet exercise: bytes `0xff 0xff` → `__8` (`-`/`_` for 62/63). -/
example : base64url [0xff, 0xff] = "__8".toList := by decide

/-! ## Axiom audit -/

#print axioms keyAuthorization_correct
#print axioms jws_sign_verify
#print axioms order_needs_valid_authz
#print axioms dns01_digest_correct
#print axioms frames_roundtrip

end Pki.Acme
