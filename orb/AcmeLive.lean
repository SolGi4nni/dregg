/-
# AcmeLive — driving the PROVEN ACME order lifecycle over the byte level

`Acme.Order`, `Acme.Challenge`, and `Acme.Basic` model automated certificate
issuance (RFC 8555) as sans-IO, proven Lean: the order FSM
(`pending → ready → processing → valid`, `orderStep`/`orderRun`), the challenge
FSM (`pending → processing → {valid,invalid}`, `Challenge.step`/`validateStep`),
the challenge → authorization bridge (`authzOfChalStatus`), and the two wire
encodings — HTTP-01 (`http01Path`, `keyAuthorization`) and DNS-01
(`dns01RecordName`, `dns01TxtValue`). The load-bearing safety theorems are all
proven there: `valid_requires_all_authz_valid` (no certificate is issued past a
pending or failed authorization), `validateStep_valid_needs_success` (a
challenge only becomes valid on a successful validation), `provision_http` /
`provision_dns` (the responder places exactly the right bytes at exactly the
right resource), `http01Path_injective` (no cross-serving between tokens).

None of that logic was wired into a running binary. This executable is that
wiring: a `selftest` that drives the WHOLE issuance pipeline over the byte
level in one process — provisioning challenges to real resource bytes, deriving
the DNS-01 TXT value with real SHA-256, fetching the served content back through
a byte-keyed responder table, driving both the challenge FSM and the order FSM
through the happy path (`newOrder → respond → validate → finalize → issued`),
and cross-checking every stage against the proven decisions.

## Faithfulness / realization boundary (the ControlLive discipline)

This is **drorb-native**: the responder, the CA validator, and the order client
are all our own spec-conformant participants speaking the modelled RFC 8555
objects — NOT interop against a live CA (a real public ACME directory service),
which additionally needs the JWS-signed HTTPS transport, nonce replay handling,
and account registration (the operator-provided directory URL + account key; the
named residual). Like ControlLive / DiscoLive this is a live cross-check, not
part of the trusted core: everything structural is the proven Lean. The gap the
selftest discharges by construction is that this exe faithfully CALLS the proven
Lean functions on real bytes; the faithfulness of the provision→fetch→validate
chain and the order-FSM safety guarantee are PROVEN below as
`acme_http01_provision_fetch_faithful` and `acme_order_faithful`.

Usage:
  acme-live selftest
-/
import Acme
import Crypto

namespace AcmeLive

open Acme

/-! ## Rendering helpers -/

/-- Render the model's `Bytes` (`List Char`) as text. -/
def text (b : Acme.Bytes) : String := String.mk b

/-- Lowercase hex of a `ByteArray` (for the SHA-256 digest bytes). -/
def toHex (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.toList.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

/-! ## The Phase-0 faithfulness theorems

Two obligations the running loop discharges. Neither is a `P → P`: each has a
non-trivial hypothesis, a distinct conclusion, and is inhabited by the selftest.

### (1) The byte-level HTTP-01 provision→fetch round-trip equals the model

When an HTTP-01 challenge is provisioned to a `(path, content)` pair and the CA
fetches the served content at the challenge's canonical well-known path, it
recovers PRECISELY the model key authorization `token ‖ "." ‖ thumbprint` — the
bytes on the wire realize the model, mediated only by the proven `provision_http`
(the responder places exactly `keyAuthorization` at exactly `http01Path token`).
This is the ACME analogue of `control_applies_netmap_faithfully`: fetch∘provision
= the proven model value. -/

/-- A byte-keyed HTTP responder table: `path ↦ content`. -/
def serveTable (table : List (Acme.Bytes × Acme.Bytes)) (path : Acme.Bytes) :
    Option Acme.Bytes :=
  (table.find? (fun kv => decide (kv.1 = path))).map Prod.snd

theorem acme_http01_provision_fetch_faithful
    (digest : Acme.Bytes → Acme.Bytes) (c : Acme.Challenge) (thumbprint : Acme.Bytes)
    (h : c.ty = .http01) :
    (match c.provision digest thumbprint with
     | .http path content => serveTable [(path, content)] (Acme.http01Path c.token)
     | .dns _ _ => none)
      = some (Acme.keyAuthorization c.token thumbprint) := by
  rw [Acme.provision_http h]
  simp [serveTable, Acme.http01Path, List.find?]

#print axioms acme_http01_provision_fetch_faithful

/-! ### (2) The order FSM never issues past an unfinished authorization

The headline. For ANY set of identifiers and ANY event sequence, if the order
driven from a fresh order reaches `valid` — the status at which a certificate is
issued — then EVERY one of its authorizations is `valid`. The live driver runs
exactly `orderRun` over the byte-driven events, so the property it must respect
is the proven `valid_requires_all_authz_valid`, lifted from the `allValid` Bool
to a per-element guarantee. Non-vacuous: the hypothesis (reaching `valid`) is
satisfiable — the selftest's happy path reaches it (`acme_happy_path_reaches_valid`
below) — and the conclusion is a distinct per-authorization fact, not the
hypothesis. -/
theorem acme_order_faithful (ids : List Acme.Bytes) (es : List Acme.OrderEvent)
    (h : (Acme.orderRun (Acme.Order.fresh ids) es).status = .valid) :
    ∀ a ∈ (Acme.orderRun (Acme.Order.fresh ids) es).authzs,
      a = Acme.AuthzStatus.valid := by
  have hall := Acme.valid_requires_all_authz_valid ids es h
  unfold Acme.allValid at hall
  rw [List.all_eq_true] at hall
  intro a ha
  exact (Acme.AuthzStatus.isValid_eq a).mp (hall a ha)

#print axioms acme_order_faithful

/-! ### The happy-path witness (inhabits the hypothesis of `acme_order_faithful`)

A concrete single-identifier order driven through the canonical issuance
sequence — validate the one authorization, finalize, issue — reaches `valid`.
This is what the selftest exercises; it also proves the hypothesis of
`acme_order_faithful` is satisfiable (so the headline is not vacuous). Kernel
`decide`, not `native_decide`. -/
def happyEvents : List Acme.OrderEvent :=
  [.authzResult 0 true, .finalize, .issued]

theorem acme_happy_path_reaches_valid :
    (Acme.orderRun (Acme.Order.fresh ["example.com".toList]) happyEvents).status
      = Acme.OrderStatus.valid := by decide

#print axioms acme_happy_path_reaches_valid

/-! ## The selftest — the whole issuance pipeline over the byte level -/

/-- Real DNS-01 digest: SHA-256 of the key authorization, rendered as hex chars.
This is the only cryptography in the pipeline (the model folds SHA-256/base64url
into the abstract `digest`); here we instantiate it with the verified
`Crypto.sha256`, so the DNS-01 TXT value on the wire is real bytes. -/
def realDigest (b : Acme.Bytes) : Acme.Bytes :=
  (toHex (Crypto.sha256 (String.mk b).toUTF8)).toList

def selftest : IO UInt32 := do
  IO.println "== acme-live selftest : RFC 8555 issuance, byte-level, order + challenge FSMs =="

  let thumbprint : Acme.Bytes := "acct-thumbprint-selftest".toList
  let domain : Acme.Bytes := "www.example.com".toList
  let token : Acme.Bytes := "tok-2f1e9c-selftest-http01".toList
  IO.println s!"account thumbprint : {text thumbprint}"
  IO.println s!"identifier (domain): {text domain}"
  IO.println s!"challenge token    : {text token}"

  -- ── 1. provision the HTTP-01 challenge to real resource bytes ──
  let httpChal : Challenge := { ty := .http01, token := token, domain := domain, status := .pending }
  let httpProv := httpChal.provision realDigest thumbprint
  IO.println "\n-- HTTP-01 provisioning --"
  let (httpPath, httpContent) ←
    match httpProv with
    | .http p ct => do
        IO.println s!"serve path    : {text p}"
        IO.println s!"serve content : {text ct}   (= key authorization)"
        pure (p, ct)
    | .dns _ _ => do IO.eprintln "HTTP-01 challenge did not provision as HTTP"; return 1

  -- the responder table, keyed by byte path; the CA fetches the content back
  let table : List (Acme.Bytes × Acme.Bytes) := [(httpPath, httpContent)]
  let fetched := serveTable table (Acme.http01Path token)
  let expected := some (Acme.keyAuthorization token thumbprint)
  let fetchOk := fetched == expected
  IO.println s!"CA fetch at http01Path(token) recovers key authorization : {fetchOk}"
  IO.println "  (realizes acme_http01_provision_fetch_faithful)"
  if !fetchOk then do IO.eprintln "HTTP-01 fetch did not round-trip"; return 1

  -- no cross-serving: a different token's path is not in the table
  let otherPath := Acme.http01Path "some-other-token".toList
  let crossServe := serveTable table otherPath
  let noCross := crossServe == none
  IO.println s!"different token's path is NOT served (http01Path_injective) : {noCross}"
  if !noCross then do IO.eprintln "cross-serving detected"; return 1

  -- ── 2. provision the DNS-01 challenge with real SHA-256 ──
  let dnsChal : Challenge := { ty := .dns01, token := token, domain := domain, status := .pending }
  let dnsProv := dnsChal.provision realDigest thumbprint
  IO.println "\n-- DNS-01 provisioning (real SHA-256) --"
  match dnsProv with
  | .dns name val => do
      IO.println s!"record name : {text name}"
      IO.println s!"TXT value   : {text val}   (= hex SHA-256 of key authorization)"
  | .http _ _ => do IO.eprintln "DNS-01 challenge did not provision as DNS"; return 1

  -- ── 3. drive the challenge FSM: respond → validate(true) → valid ──
  IO.println "\n-- challenge FSM --"
  let cResponded := httpChal.step .respond                 -- pending → processing
  let cValidated := cResponded.step (.validated true)      -- processing → valid
  let chalValid := cValidated.status == ChalStatus.valid
  IO.println s!"respond → processing → validated(true) → status = valid : {chalValid}"
  -- no-bypass: a failed validation of the SAME processing challenge lands invalid, not valid
  let cFailed := cResponded.step (.validated false)
  let failNotValid := cFailed.status != ChalStatus.valid
  IO.println s!"validated(false) does NOT reach valid (no bypass)        : {failNotValid}"
  if !(chalValid && failNotValid) then do IO.eprintln "challenge FSM cross-check failed"; return 1

  -- the challenge → authorization bridge
  let authz := authzOfChalStatus cValidated.status
  let authzValid := authz == AuthzStatus.valid
  IO.println s!"authzOfChalStatus(valid) = valid                          : {authzValid}"

  -- ── 4. drive the ORDER FSM over the byte-driven authorization result ──
  IO.println "\n-- order FSM (newOrder → authzResult → finalize → issued) --"
  let ids : List Acme.Bytes := [domain]
  let o0 := Order.fresh ids
  IO.println s!"fresh order : {o0.authzs.length} pending authz, status pending"
  -- the single authorization validated true (from the challenge FSM above), then finalize + issue
  let events : List OrderEvent := [.authzResult 0 (authz == AuthzStatus.valid), .finalize, .issued]
  let oFinal := orderRun o0 events
  let orderValid := oFinal.status == OrderStatus.valid
  let allAuthzValid := allValid oFinal.authzs
  IO.println s!"driven order status : {repr oFinal.status}"
  IO.println s!"order reached valid                                       : {orderValid}"
  IO.println s!"all authorizations valid (valid_requires_all_authz_valid) : {allAuthzValid}"
  if !(orderValid && allAuthzValid) then do IO.eprintln "order FSM did not reach valid with all authz valid"; return 1

  -- no-skip cross-check: an order that skips validation cannot reach valid
  let skipEvents : List OrderEvent := [.finalize, .issued]   -- finalize from pending stutters
  let oSkip := orderRun o0 skipEvents
  let skipNotValid := oSkip.status != OrderStatus.valid
  IO.println s!"finalize-before-validate does NOT reach valid (no skip)   : {skipNotValid}"
  if !skipNotValid then do IO.eprintln "order skipped authorization"; return 1

  -- ── 5. summary ──
  if fetchOk && noCross && chalValid && failNotValid && authzValid
      && orderValid && allAuthzValid && skipNotValid then do
    IO.println "\nPASS — challenge provisioned to real bytes, fetch round-tripped, both FSMs"
    IO.println "       driven to valid over the byte level; the order reaches valid ONLY with"
    IO.println "       every authorization valid (the proven safety guarantee, realized)."
    IO.println "FULL ACME ISSUANCE EXCHANGE COMPLETE (drorb-native, byte-level, real SHA-256)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the issuance pipeline did not cross-check."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do
    IO.eprintln "usage: acme-live selftest"
    return 1

end AcmeLive

def main (args : List String) : IO UInt32 := AcmeLive.main args
