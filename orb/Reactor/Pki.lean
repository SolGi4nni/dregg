import Reactor.Tls
import Resume.Ticket
import Resume.Ocsp
import Mtls.Verify
import Mtls.Theorems
import TlsHandshake

/-!
# Reactor.Pki — wiring the real PKI libraries into the TLS accept decision

`Reactor.Tls` drove the real `Tls` record/handshake machine through the FSM's
opaque `TlsConn` handle: `hsFeedReal` turns the handshake engine's phase into
the FSM's `HsOut` (`.more` while handshaking, `.done` on completion, `.fail` on
teardown), and `wireTls` installs it into `Config.hsFeed`. That is the function
the running reactor calls on every `.tlsHandshake` byte (`Proto.onBytes →
Proto.hsStep → cfg.hsFeed`).

This file gates that **accept decision** with two real PKI libraries, at the one
place the handshake completes:

* **Resume** (`Resume.Ticket`, `Resume.Ocsp`) — when a returning client presents
  a session-resumption ticket, the real validity-window logic (`Resume.accept`)
  decides whether resumption is honoured; a ticket outside `[issued, expiry)` (or
  under a rotated key epoch) is refused. If the server carries a stapled OCSP
  response, the real acceptance gate (`Resume.Staple.accepts`) refuses to complete
  the handshake unless the staple is `good`, fresh, and issued for the served
  certificate — a revoked, stale, or wrong-certificate staple is refused.

* **Mtls** (`Mtls.Verify`, `Mtls.Theorems`) — when a client presents a
  certificate chain (mutual TLS), the real decision (`Mtls.authenticate`, built
  on `Mtls.verifyFrom`) derives the single client identity only when the chain
  validates as an RFC 5280 path **and** the client's RFC 8446 §4.4.3
  `CertificateVerify` signature verifies under the leaf key over the surfaced
  transcript (proof of possession of the leaf private key), or yields none. When
  mTLS is required, the handshake completes only if that decision succeeds —
  there is no path from a failed chain, or a chain without a valid
  CertificateVerify, to an authenticated session.

Neither library is a dependency of the other or of `Tls`; each surfaces its
input (ticket, staple, chain) to this gate, which composes them *over* the real
TLS accept.

## The wiring

`pkiHsFeed base pcfg` wraps a base handshake feeder (the real
`TlsWire.hsFeedReal tcfg`): it runs the underlying TLS handshake unchanged and,
**only** on `.done` (the accept), applies the PKI gate `pkiOk`. If any gate
refuses, the accept is turned into `.fail` — the handshake does not complete.
`.more` (still handshaking) and `.fail` (already refused) pass through untouched.

`wirePki tcfg pcfg cfg` installs `pkiHsFeed (hsFeedReal tcfg) pcfg` into
`Config.hsFeed`, so the *running* reactor invokes it: `Proto.onBytes` on a
`.tlsHandshake` state calls `Proto.hsStep`, which calls `cfg.hsFeed` — now the
PKI-gated feeder. `wiredPkiConfig` is the concrete reactor config with the real
TLS engine and the PKI gate both plugged in over the arena-backed HTTP/1.1
`demoConfig`.

## The seam theorems

* `pki_resume_window` — if a session ticket is presented and the wired handshake
  accepts (`.done`), the current time lies inside the ticket's validity window
  per the real `Resume.accept_in_window`. Its reactor form
  (`pki_resume_window_reactor`) shows that on the running `Proto.onBytes` path a
  ticket outside its window can never carry the connection into an established
  protocol state — the reactor closes or stays in handshake.
* `mtls_no_auth_on_failure` — with mTLS required, a chain that fails the real
  `Mtls.verifyFrom` validation never lets the wired handshake reach `.done`
  (composing `Mtls.authenticate_unverified` with the gate);
  `mtls_identity_verified` shows any derived identity comes only from a validated
  chain (`Mtls.authenticate_eq_some`). The reactor form
  (`mtls_no_auth_on_failure_reactor`) transports this to `Proto.onBytes`: a
  failed chain yields no authenticated established state.
* `pki_ocsp_valid` — if the wired handshake accepts while a staple is configured,
  that staple was valid per the real `Resume.accepts_iff`: `good`, fresh
  (`thisUpdate ≤ now < nextUpdate`), and issued for the served certificate.
  `pki_ocsp_fresh`/`pki_ocsp_not_revoked` are its freshness / non-revocation
  projections.
-/

namespace Reactor
namespace PkiWire

open Proto (Bytes TlsConn Config HsOut)

/-! ## The client-authentication view and the real CertificateVerify parser

The residual the earlier mTLS refinement named — that `transcriptOf`/`cvSigOf`
were two *independent, opaque* `TlsConn → Bytes → ByteArray` functions (and, after
the first pass, a single but still *free* `clientAuthOf` field a caller could fill
with arbitrary bytes) — is closed here: the client-auth view is no longer a field
of `PkiCfg` at all. It is **derived** from the live TLS connection state
(`TlsWire.connHandshakeBytes` reads the connection's **accumulated handshake
transcript** — `Tls.St.transcript`, which `Tls.step` grows across every received
flight, RFC 8446 §4.4.1 — out of the deployed `Tls.St` the `TlsConn` carries) by
splitting the client's CertificateVerify message out of that transcript with the
real RFC 8446 §4 handshake framing (`scanCV`). Because the transcript retains the
**earlier received** flights (the `ClientHello`) **and** the interleaved plaintext
of the **emitted server flight** (`ServerHello ‖ EncryptedExtensions ‖ Certificate
‖ CertificateVerify ‖ Finished` — accumulated by `Tls.step` via
`HsOut.flightPlain` at the step that sends it, no longer dropped as sealed-only
record bytes), the handshake-context prefix the client CertificateVerify signs is
the full RFC 8446 §4.4.1 transcript up to and including the client `Certificate`
(`ClientHello ‖ server flight ‖ client Certificate`), not merely the retained
second-flight tail. `scanCV` walks past the server's own CertificateVerify (folding
it into the context, as that context requires) to locate the **client's**. Both the
transcript hash and the CertificateVerify signature the deployed decision uses are
therefore fixed functions of that one real, state-accumulated transcript: the
signature is the **real RFC 8446 §4.4.3 parse** of the located CertificateVerify
message, and the transcript hash is the real `Crypto.sha256` over the
handshake-context prefix that precedes it. Neither is a value any caller can
supply. -/

/-- The client's TLS 1.3 authentication material as the handshake/record layer
surfaces it after decrypting and de-framing the client's second flight
(RFC 8446 §4.4.2/§4.4.3). It is one value per connection, so the transcript hash
and the CertificateVerify signature can no longer be forged independently of each
other. -/
structure ClientAuth where
  /-- Transcript-Hash(Handshake Context … client Certificate) — the exact value
  the client's CertificateVerify signs (RFC 8446 §4.4.3). -/
  transcriptHash : ByteArray
  /-- The client's raw CertificateVerify **handshake message** bytes,
  `msg_type(0x0f) ‖ uint24 length ‖ SignatureScheme(2) ‖ signature<uint16>`
  (RFC 8446 §4 framing / §4.4.3), as the record layer decrypted them and the
  message layer split them out of the flight. -/
  certVerifyMsg : Bytes

/-- **The real CertificateVerify signature parser (RFC 8446 §4.4.3).** Extract the
raw signature octets out of a CertificateVerify handshake message
`msg_type(0x0f) ‖ uint24 length ‖ SignatureScheme(2) ‖ signature<uint16>`, reusing
the message layer's own `uint16`/`uint24`/take primitives (`TlsHandshake.rd16`/
`rd24`/`takeN`) so the framing cannot drift from the server's own
`buildCertificateVerify`. Any framing error — an absent, truncated, or
wrong-type CertificateVerify — yields `ByteArray.empty`, which the `cvVerify`
boundary rejects: exactly the closed proof-of-possession bypass. The signature the
deployed decision checks is therefore a **pure function of the message bytes**,
not an independently supplied value. -/
def parseCvSig (msg : Bytes) : ByteArray :=
  match msg with
  | 0x0f :: r0 =>
    match TlsHandshake.rd24 r0 with
    | none => ByteArray.empty
    | some (_len, r1) =>
      match TlsHandshake.rd16 r1 with            -- SignatureScheme
      | none => ByteArray.empty
      | some (_scheme, r2) =>
        match TlsHandshake.rd16 r2 with          -- signature<uint16> length
        | none => ByteArray.empty
        | some (slen, r3) =>
          match TlsHandshake.takeN slen r3 with
          | none => ByteArray.empty
          | some (sig, _rest) => ByteArray.mk sig.toArray
  | _ => ByteArray.empty

/-! ## Splitting the client's CertificateVerify out of the real handshake flight

`clientAuthOfConn` is the concrete client-auth view: it reads the real client
handshake bytes out of the deployed `Tls.St` (`TlsWire.connHandshakeBytes`) and
splits the client's CertificateVerify message from the handshake-context prefix
it signs, using the same RFC 8446 §4 `msg_type(1) ‖ uint24 len ‖ body` framing the
server's own message builders use. There is no free value anywhere on this
path. -/

/-- Read one RFC 8446 §4 handshake message `msg_type(1) ‖ uint24 length ‖ body`
off the front of a decrypted flight, returning the whole message (header +
body) and the remaining bytes. `none` on a truncated/absent header. Reuses the
message layer's own `rd24`/`takeN` so the framing cannot drift. -/
def readHsMsg : Bytes → Option (Bytes × Bytes)
  | ty :: r0 =>
    match TlsHandshake.rd24 r0 with
    | none => none
    | some (len, r1) =>
      match TlsHandshake.takeN len r1 with
      | none => none
      | some (_body, rest) => some (ty :: r0.take (3 + len), rest)
  | [] => none

/-- Walk the accumulated handshake transcript, accumulating each handshake
message into the transcript-context prefix `ctx`, and locate the **client's**
CertificateVerify (`msg_type = 0x0f`); return `(ctx, certVerifyMsg)` where `ctx`
is the handshake-context bytes that precede it — the exact bytes the client's
CertificateVerify signs (RFC 8446 §4.4.3) — and the second component is the raw
CertificateVerify handshake message `parseCvSig` then parses.

Because the transcript now carries the **full** RFC 8446 §4.4.1 sequence
(`ClientHello ‖ server flight ‖ client Certificate ‖ client CertificateVerify ‖
…`), it contains **two** CertificateVerify messages: the server's (inside the
server flight) and the client's (in the client's second flight). The client's is
the **last** one — the client flight is the final flight, and its
CertificateVerify is followed only by the client Finished (`0x14`). So this walks
past the server's CertificateVerify (folding it into `ctx`, exactly as the client
CV's transcript context requires) and returns the last `0x0f` it finds, with the
full preceding context. `fuel` bounds the walk (each step consumes a whole
message). A transcript with no CertificateVerify yields `(ctx, [])`, whose empty
signature `cvVerify` rejects. -/
def scanCV : Nat → Bytes → Bytes → Bytes × Bytes
  | 0, ctx, _ => (ctx, [])
  | fuel + 1, ctx, l =>
    match l with
    | [] => (ctx, [])
    | ty :: _ =>
      match readHsMsg l with
      | none => (ctx, [])
      | some (msg, rest) =>
        if ty == (0x0f : UInt8) then
          -- A CertificateVerify. Prefer a *later* one (the client's) if the
          -- rest of the transcript holds another; otherwise this is the last.
          let later := scanCV fuel (ctx ++ msg) rest
          if later.2.isEmpty then (ctx, msg) else later
        else scanCV fuel (ctx ++ msg) rest

/-- **The client-auth view, derived from the live TLS state.** Read the
connection's accumulated handshake transcript out of the deployed `Tls.St` the
`TlsConn` carries (`TlsWire.connHandshakeBytes` — `Tls.St.transcript ++ buf`, the
full RFC 8446 §4.4.1 sequence: **received** flights *and* the interleaved plaintext
of the **emitted server flight**), locate the client's CertificateVerify message
(`scanCV`, which walks past the server's CertificateVerify to the client's), and
bundle: the transcript hash is the real `Crypto.sha256` over the full
handshake-context prefix (`ClientHello ‖ server flight ‖ client Certificate`), the
CertificateVerify message is the located bytes. A pure function of `(tc, buf)` —
no caller value feeds it. -/
def clientAuthOfConn (tc : TlsConn) (buf : Bytes) : ClientAuth :=
  let flight := TlsWire.connHandshakeBytes tc buf
  let r := scanCV flight.length [] flight
  { transcriptHash := Crypto.sha256 (TlsHandshake.ofBytes r.1)
    certVerifyMsg := r.2 }

/-- Non-vacuity: a concrete client second flight `Certificate ‖ CertificateVerify
‖ Finished`. -/
def demoClientFlight : Bytes :=
  [0x0b, 0x00, 0x00, 0x01, 0xAA,                                 -- Certificate
   0x0f, 0x00, 0x00, 0x07, 0x08, 0x07, 0x00, 0x03, 1, 2, 3,      -- CertificateVerify
   0x14, 0x00, 0x00, 0x01, 0x99]                                 -- Finished

/-- `scanCV` locates the CertificateVerify message inside the real flight… -/
example : (scanCV demoClientFlight.length [] demoClientFlight).2
    = [0x0f, 0x00, 0x00, 0x07, 0x08, 0x07, 0x00, 0x03, 1, 2, 3] := by decide

/-- …and its transcript-context prefix is the preceding client Certificate
message (nonempty — the CertificateVerify really signs earlier bytes). -/
example : (scanCV demoClientFlight.length [] demoClientFlight).1
    = [0x0b, 0x00, 0x00, 0x01, 0xAA] := by decide

/-- …so `parseCvSig` of the located message recovers exactly the signature
octets: the whole path from the real flight to the checked signature is real
parsing, not a stub. -/
example : parseCvSig (scanCV demoClientFlight.length [] demoClientFlight).2
    = ByteArray.mk #[1, 2, 3] := by
  have h : (scanCV demoClientFlight.length [] demoClientFlight).2
      = [0x0f, 0x00, 0x00, 0x07, 0x08, 0x07, 0x00, 0x03, 1, 2, 3] := by decide
  rw [h]; rfl

/-! ### The residual, closed: the server flight is in the transcript

A concrete **full** RFC 8446 §4.4.1 transcript — `ClientHello ‖ server flight
(ServerHello ‖ EncryptedExtensions ‖ Certificate ‖ CertificateVerify ‖ Finished)
‖ client flight (Certificate ‖ CertificateVerify ‖ Finished)` — with **two**
CertificateVerify messages, the server's and the client's. The examples below
witness that the fix is real: with the server flight now present in the
transcript, `scanCV` walks *past* the server's CertificateVerify and checks the
**client's**, whose signed context is the full transcript prefix (server flight
included), not the client Certificate alone. -/

/-- A concrete server flight (plaintext handshake messages), including a server
CertificateVerify (`0x0f`) — the message that, before this fix, was absent from
the transcript. -/
def demoServerFlight : Bytes :=
  [0x02, 0x00, 0x00, 0x01, 0xBB,        -- ServerHello
   0x08, 0x00, 0x00, 0x00,              -- EncryptedExtensions
   0x0b, 0x00, 0x00, 0x01, 0xCC,        -- server Certificate
   0x0f, 0x00, 0x00, 0x02, 0xAA, 0xBB,  -- server CertificateVerify
   0x14, 0x00, 0x00, 0x01, 0xDD]        -- server Finished

/-- A concrete ClientHello handshake message. -/
def demoClientHello : Bytes := [0x01, 0x00, 0x00, 0x01, 0xEE]

/-- The full accumulated §4.4.1 transcript: ClientHello ‖ server flight ‖ client
flight — exactly what `Tls.St.transcript` now holds. -/
def demoFullTranscript : Bytes :=
  demoClientHello ++ demoServerFlight ++ demoClientFlight

/-- `scanCV` returns the **client's** CertificateVerify (the last `0x0f`), not the
server's — the proof-of-possession is checked against the client. -/
example : (scanCV demoFullTranscript.length [] demoFullTranscript).2
    = [0x0f, 0x00, 0x00, 0x07, 0x08, 0x07, 0x00, 0x03, 1, 2, 3] := by decide

/-- **The residual is closed.** The transcript context the client CertificateVerify
signs is the FULL §4.4.1 prefix — `ClientHello ‖ server flight ‖ client
Certificate` — so the server flight (previously dropped) is now covered. -/
example : (scanCV demoFullTranscript.length [] demoFullTranscript).1
    = demoClientHello ++ demoServerFlight ++ [0x0b, 0x00, 0x00, 0x01, 0xAA] := by decide

/-- …and the recovered signature is the client's (proof of possession of the
client leaf key), parsed from the client CertificateVerify located past the
server's. -/
example : parseCvSig (scanCV demoFullTranscript.length [] demoFullTranscript).2
    = ByteArray.mk #[1, 2, 3] := by
  have h : (scanCV demoFullTranscript.length [] demoFullTranscript).2
      = [0x0f, 0x00, 0x00, 0x07, 0x08, 0x07, 0x00, 0x03, 1, 2, 3] := by decide
  rw [h]; rfl

/-! ## The PKI accept context: the credentials surfaced to the gate -/

/-- The static PKI context threaded into the handshake accept decision. The
`ticketOf`/`chainOf` fields surface the client-presented credentials (session
ticket, certificate chain) out of the handshake handle and buffer — the sibling
libraries' *inputs* — the same shape by which `Tls.Config` surfaces the crypto
boundary. Every function-valued field is total, so the seam theorems hold
uniformly over every presentation behaviour. -/
structure PkiCfg where
  /-- The check time for every window/freshness decision. -/
  now : Nat
  /-- The current session-ticket key epoch (a rotated key advances it). -/
  resumeEpoch : Nat
  /-- The server's current stapled OCSP response, if it staples. -/
  staple : Option Resume.Staple
  /-- The `certID` of the certificate the server is serving on this connection —
  the identity the stapled OCSP response's `certID` must match (RFC 6960 §3.2 /
  §4.2.1). Surfaced into the accept gate the same way the ticket/chain inputs
  are, so `ocspOk` can reject a staple issued for a different certificate. -/
  servedCertId : Nat
  /-- The mTLS verification context: the named signature interface and the
  trust-anchor set. -/
  mtlsEnv : Mtls.Env
  /-- Whether client-certificate authentication is required to complete. -/
  mtlsRequired : Bool
  /-- The session-resumption ticket the client presented, if any. -/
  ticketOf : TlsConn → Bytes → Option Resume.Ticket
  /-- The client certificate chain the client presented (leaf first). -/
  chainOf : TlsConn → Bytes → Mtls.Chain

/-! ## The bound client-auth view and the transcript/CertificateVerify projections

The client-auth view is **not** a field of `PkiCfg`: it is `clientAuthOfConn`,
derived from the live TLS connection state, exposed here as `PkiCfg.clientAuthOf`
(ignoring `pcfg` — there is nothing a caller can vary). `transcriptOf`/`cvSigOf`
project from it, so the deployed decision uses a transcript hash and a
CertificateVerify signature that are both fixed functions of the one real
handshake buffer the `Tls.St` carries. -/

/-- The client's authentication material for this connection — the state-derived
view `clientAuthOfConn`, **not** a caller-supplied function. The `pcfg` argument
is ignored: the transcript hash and CertificateVerify message come only from the
live TLS connection state and the received bytes, so they cannot be forged. -/
def PkiCfg.clientAuthOf (_pcfg : PkiCfg) (tc : TlsConn) (buf : Bytes) : ClientAuth :=
  clientAuthOfConn tc buf

/-- The client-auth view is exactly the state extraction — independent of any
caller-varied `pcfg` data. -/
theorem clientAuthOf_eq_conn (pcfg : PkiCfg) (tc : TlsConn) (buf : Bytes) :
    pcfg.clientAuthOf tc buf = clientAuthOfConn tc buf := rfl

/-- The handshake transcript hash the client's CertificateVerify signs
(RFC 8446 §4.4.3): the `transcriptHash` of the state-derived view — the real
`Crypto.sha256` over the handshake-context prefix in the TLS state's buffer, not
an opaque supplied value. -/
def PkiCfg.transcriptOf (pcfg : PkiCfg) (tc : TlsConn) (buf : Bytes) : ByteArray :=
  (pcfg.clientAuthOf tc buf).transcriptHash

/-- The client's RFC 8446 §4.4.3 CertificateVerify signature: the **real parse**
(`parseCvSig`) of the surfaced CertificateVerify handshake message — a pure
function of the message bytes, not an independently supplied value. -/
def PkiCfg.cvSigOf (pcfg : PkiCfg) (tc : TlsConn) (buf : Bytes) : ByteArray :=
  parseCvSig (pcfg.clientAuthOf tc buf).certVerifyMsg

/-- **Binding, transcript.** The transcript hash the deployed decision uses is
exactly the state-derived view's value, not a caller-supplied one. -/
theorem transcriptOf_eq_view (pcfg : PkiCfg) (tc : TlsConn) (buf : Bytes) :
    pcfg.transcriptOf tc buf = (pcfg.clientAuthOf tc buf).transcriptHash := rfl

/-- **Binding, signature.** The signature the deployed decision checks is exactly
the RFC 8446 §4.4.3 parse of the surfaced CertificateVerify message bytes. -/
theorem cvSigOf_eq_parse (pcfg : PkiCfg) (tc : TlsConn) (buf : Bytes) :
    pcfg.cvSigOf tc buf = parseCvSig (pcfg.clientAuthOf tc buf).certVerifyMsg := rfl

/-- **Binding to the TLS state, transcript.** The transcript hash the deployed
decision uses is the real `Crypto.sha256` over the handshake-context prefix
`scanCV` peels off the client flight the **live `Tls.St`** carries
(`TlsWire.connHandshakeBytes tc buf`). No caller value appears. -/
theorem transcriptOf_from_state (pcfg : PkiCfg) (tc : TlsConn) (buf : Bytes) :
    pcfg.transcriptOf tc buf
      = Crypto.sha256 (TlsHandshake.ofBytes
          (scanCV (TlsWire.connHandshakeBytes tc buf).length
            [] (TlsWire.connHandshakeBytes tc buf)).1) := rfl

/-- **Binding to the TLS state, signature.** The signature the deployed decision
checks is the RFC 8446 §4.4.3 parse of the CertificateVerify message `scanCV`
locates in the client flight the **live `Tls.St`** carries
(`TlsWire.connHandshakeBytes tc buf`). No caller value appears. -/
theorem cvSigOf_from_state (pcfg : PkiCfg) (tc : TlsConn) (buf : Bytes) :
    pcfg.cvSigOf tc buf
      = parseCvSig (scanCV (TlsWire.connHandshakeBytes tc buf).length
          [] (TlsWire.connHandshakeBytes tc buf)).2 := rfl

/-- Non-vacuity of the parser: a concrete CertificateVerify message
(scheme `ed25519 = 0x0807`, signature `[1,2,3]`) parses back to exactly its
signature octets — `parseCvSig` reads real framing, it is not a stub. -/
example :
    parseCvSig [0x0f, 0x00, 0x00, 0x07, 0x08, 0x07, 0x00, 0x03, 1, 2, 3]
      = ByteArray.mk #[1, 2, 3] := by rfl

/-- …and a malformed CertificateVerify (wrong `msg_type`) parses to the empty
signature, which `cvVerify` rejects — the closed bypass, at the parser level. -/
example : parseCvSig [0x0b, 0x00, 0x00, 0x00] = ByteArray.empty := by rfl

/-! ## The individual gates, each a call into a real library -/

/-- The client identity the real `Mtls` validator derives from the presented
chain: `some subject` only when the chain validates as an RFC 5280 path **and**
the client's RFC 8446 §4.4.3 `CertificateVerify` verifies under the leaf key over
the surfaced transcript; `none` otherwise. This is literally `Mtls.authenticate`
on the surfaced chain, transcript hash and CertificateVerify signature. -/
def mtlsIdentity (pcfg : PkiCfg) (tc : TlsConn) (buf : Bytes) : Option Mtls.Name :=
  Mtls.authenticate pcfg.mtlsEnv pcfg.now (pcfg.chainOf tc buf)
    (pcfg.transcriptOf tc buf) (pcfg.cvSigOf tc buf)

/-- The resumption gate: with no ticket presented this is a full (non-resumed)
handshake and passes; with a ticket, the real `Resume.accept` decides it against
the validity window and key epoch. -/
def resumeOk (pcfg : PkiCfg) (tc : TlsConn) (buf : Bytes) : Bool :=
  match pcfg.ticketOf tc buf with
  | none => true
  | some t => Resume.accept t pcfg.now pcfg.resumeEpoch

/-- The OCSP gate: with no staple configured this passes; with a staple, the
real `Resume.Staple.accepts` decision applies — the staple is honoured only when
its certificate status is `good`, it is fresh, and its `certID` names the served
certificate (`pcfg.servedCertId`). A revoked staple, or one issued for a
different certificate, is refused even while fresh (RFC 6960 §2.2/§3.2/§4.2.1). -/
def ocspOk (pcfg : PkiCfg) : Bool :=
  match pcfg.staple with
  | none => true
  | some s => s.accepts pcfg.now pcfg.servedCertId

/-- The mTLS gate: when client-cert auth is required, an identity must have been
derived (i.e. the chain validated); otherwise it passes. -/
def mtlsOk (pcfg : PkiCfg) (tc : TlsConn) (buf : Bytes) : Bool :=
  if pcfg.mtlsRequired then (mtlsIdentity pcfg tc buf).isSome else true

/-- The composite accept gate: every PKI condition must hold to honour the
handshake. -/
def pkiOk (pcfg : PkiCfg) (tc : TlsConn) (buf : Bytes) : Bool :=
  resumeOk pcfg tc buf && ocspOk pcfg && mtlsOk pcfg tc buf

/-! ## The gated feeder and the config transformer -/

/-- Apply the accept gate to one `HsOut`: only `.done` (the accept) is gated;
`.more`/`.fail` pass through. A refused accept becomes `.fail`. -/
def gateDone (ok : Bool) : HsOut → HsOut
  | .done tc consumed toSend alpn ktls early =>
      if ok then .done tc consumed toSend alpn ktls early else .fail
  | out => out

/-- The PKI-gated handshake feeder: run the base (real TLS) handshake, then gate
its accept with `pkiOk`. This is the function installed on the reactor path. -/
def pkiHsFeed (base : TlsConn → Bytes → HsOut) (pcfg : PkiCfg)
    (tc : TlsConn) (buf : Bytes) : HsOut :=
  gateDone (pkiOk pcfg tc buf) (base tc buf)

/-- Install the PKI-gated feeder over the **real** TLS handshake adapter into a
base `Proto.Config`, leaving every other field (including the real `tlsRecv`/
`tlsSend`) untouched. -/
def wirePki (tcfg : Tls.Config) (pcfg : PkiCfg) (cfg : Config) : Config :=
  { cfg with hsFeed := pkiHsFeed (TlsWire.hsFeedReal tcfg) pcfg }

/-- The concrete reactor config with the real TLS engine and the PKI accept gate
both wired in over the arena-backed HTTP/1.1 `demoConfig`. -/
def wiredPkiConfig (tcfg : Tls.Config) (pcfg : PkiCfg) : Config :=
  wirePki tcfg pcfg (TlsWire.wireTls tcfg Reactor.Config.demoConfig)

/-- No drift: the wired `hsFeed` is exactly the PKI-gated feeder over the real
TLS handshake adapter. -/
theorem wirePki_hsFeed (tcfg : Tls.Config) (pcfg : PkiCfg) (cfg : Config) :
    (wirePki tcfg pcfg cfg).hsFeed = pkiHsFeed (TlsWire.hsFeedReal tcfg) pcfg := rfl

/-- The PKI gate leaves the real record layer wired: `tlsRecv`/`tlsSend` come
straight from the TLS engine. -/
theorem wiredPkiConfig_tlsRecv (tcfg : Tls.Config) (pcfg : PkiCfg) :
    (wiredPkiConfig tcfg pcfg).tlsRecv = TlsWire.tlsRecvReal tcfg := rfl

/-! ## The accept-gate discipline: `.done` implies `pkiOk` -/

/-- The gate only ever emits `.done` when `ok` holds. -/
theorem gateDone_done {ok : Bool} {o : HsOut}
    {tc' : TlsConn} {consumed : Nat} {toSend : Bytes} {alpn : Proto.Alpn}
    {ktls : Bool} {early : Bytes}
    (h : gateDone ok o = .done tc' consumed toSend alpn ktls early) : ok = true := by
  cases o with
  | more _ _ _ => simp [gateDone] at h
  | fail => simp [gateDone] at h
  | done _ _ _ _ _ _ =>
    simp only [gateDone] at h
    by_cases hok : ok = true
    · exact hok
    · rw [if_neg hok] at h; exact absurd h (by simp)

/-- **The accept discipline.** The wired feeder accepts (`.done`) only when the
composite PKI gate holds. -/
theorem pkiHsFeed_done_pkiOk (base : TlsConn → Bytes → HsOut) (pcfg : PkiCfg)
    (tc : TlsConn) (buf : Bytes)
    {tc' : TlsConn} {consumed : Nat} {toSend : Bytes} {alpn : Proto.Alpn}
    {ktls : Bool} {early : Bytes}
    (hd : pkiHsFeed base pcfg tc buf = .done tc' consumed toSend alpn ktls early) :
    pkiOk pcfg tc buf = true :=
  gateDone_done hd

/-! ### Projecting the composite gate onto its three conjuncts -/

theorem pkiOk_resume {pcfg : PkiCfg} {tc : TlsConn} {buf : Bytes}
    (h : pkiOk pcfg tc buf = true) : resumeOk pcfg tc buf = true := by
  unfold pkiOk at h
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1

theorem pkiOk_ocsp {pcfg : PkiCfg} {tc : TlsConn} {buf : Bytes}
    (h : pkiOk pcfg tc buf = true) : ocspOk pcfg = true := by
  unfold pkiOk at h
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2

theorem pkiOk_mtls {pcfg : PkiCfg} {tc : TlsConn} {buf : Bytes}
    (h : pkiOk pcfg tc buf = true) : mtlsOk pcfg tc buf = true := by
  unfold pkiOk at h
  exact (Bool.and_eq_true_iff.mp h).2

/-! ## Seam theorem 1 — resumption only inside the validity window -/

/-- **`pki_resume_window`.** If a session-resumption ticket is presented and the
wired handshake *accepts* it (surfaces `.done`), then the current time lies
inside the ticket's half-open validity window `[issued, expiry)`. This composes
the real `Resume.accept_in_window` with the TLS accept: the accept could only
have fired because `resumeOk` held, and with a ticket present `resumeOk` *is*
`Resume.accept`, whose window theorem transfers verbatim. -/
theorem pki_resume_window (base : TlsConn → Bytes → HsOut) (pcfg : PkiCfg)
    (tc : TlsConn) (buf : Bytes) (t : Resume.Ticket)
    (ht : pcfg.ticketOf tc buf = some t)
    {tc' : TlsConn} {consumed : Nat} {toSend : Bytes} {alpn : Proto.Alpn}
    {ktls : Bool} {early : Bytes}
    (hd : pkiHsFeed base pcfg tc buf = .done tc' consumed toSend alpn ktls early) :
    t.issued ≤ pcfg.now ∧ pcfg.now < t.expiry := by
  have hres := pkiOk_resume (pkiHsFeed_done_pkiOk base pcfg tc buf hd)
  simp only [resumeOk, ht] at hres
  exact Resume.accept_in_window hres

/-! ## Seam theorem 2 — no client identity / no accept on chain failure -/

/-- Any client identity the gate derives comes only from a chain the real
validator accepted — the no-bypass property (`Mtls.authenticate_eq_some`)
transported to the reactor's `mtlsIdentity`. -/
theorem mtls_identity_verified (pcfg : PkiCfg) (tc : TlsConn) (buf : Bytes)
    {id : Mtls.Name} (h : mtlsIdentity pcfg tc buf = some id) :
    Mtls.verifyFrom pcfg.mtlsEnv pcfg.now (pcfg.chainOf tc buf) = true := by
  obtain ⟨_, _, _, _, hver, _⟩ := Mtls.authenticate_eq_some h
  exact hver

/-- **`mtls_no_auth_on_failure`.** With mTLS required, a client chain that fails
the real `Mtls.verifyFrom` validation never lets the wired handshake reach
`.done`: no authenticated session is established on a failed chain. This composes
`Mtls.authenticate_unverified` (a failed chain yields no identity) with the
accept gate (a required-but-absent identity refuses the accept). -/
theorem mtls_no_auth_on_failure (base : TlsConn → Bytes → HsOut) (pcfg : PkiCfg)
    (tc : TlsConn) (buf : Bytes)
    (hreq : pcfg.mtlsRequired = true)
    (hfail : Mtls.verifyFrom pcfg.mtlsEnv pcfg.now (pcfg.chainOf tc buf) = false)
    {tc' : TlsConn} {consumed : Nat} {toSend : Bytes} {alpn : Proto.Alpn}
    {ktls : Bool} {early : Bytes} :
    pkiHsFeed base pcfg tc buf ≠ .done tc' consumed toSend alpn ktls early := by
  intro hd
  have hm := pkiOk_mtls (pkiHsFeed_done_pkiOk base pcfg tc buf hd)
  have hnone : mtlsIdentity pcfg tc buf = none := by
    unfold mtlsIdentity; exact Mtls.authenticate_unverified hfail
  unfold mtlsOk at hm
  rw [if_pos hreq, hnone] at hm
  simp at hm

/-! ## Seam theorem 3 — no accept on a revoked, stale, or wrong-cert OCSP staple -/

/-- **`pki_ocsp_valid`.** If the wired handshake accepts while the server carries
a stapled OCSP response, that staple was *valid* at the check time per the real
`Resume.accepts_iff`: its certificate status was `good`, it was fresh
(`thisUpdate ≤ now < nextUpdate`), and its `certID` named the served certificate
(`pcfg.servedCertId`). A revoked, stale, or wrong-certificate staple can never
ride out on an accepted handshake. -/
theorem pki_ocsp_valid (base : TlsConn → Bytes → HsOut) (pcfg : PkiCfg)
    (tc : TlsConn) (buf : Bytes) (s : Resume.Staple)
    (hs : pcfg.staple = some s)
    {tc' : TlsConn} {consumed : Nat} {toSend : Bytes} {alpn : Proto.Alpn}
    {ktls : Bool} {early : Bytes}
    (hd : pkiHsFeed base pcfg tc buf = .done tc' consumed toSend alpn ktls early) :
    s.certStatus = Resume.CertStatus.good
      ∧ (s.thisUpdate ≤ pcfg.now ∧ pcfg.now < s.nextUpdate)
      ∧ s.certId = pcfg.servedCertId := by
  have hoc := pkiOk_ocsp (pkiHsFeed_done_pkiOk base pcfg tc buf hd)
  simp only [ocspOk, hs] at hoc
  exact (Resume.accepts_iff s pcfg.now pcfg.servedCertId).mp hoc

/-- **`pki_ocsp_fresh`.** The freshness projection of `pki_ocsp_valid`: an
accepted handshake carrying a staple implies that staple was fresh. -/
theorem pki_ocsp_fresh (base : TlsConn → Bytes → HsOut) (pcfg : PkiCfg)
    (tc : TlsConn) (buf : Bytes) (s : Resume.Staple)
    (hs : pcfg.staple = some s)
    {tc' : TlsConn} {consumed : Nat} {toSend : Bytes} {alpn : Proto.Alpn}
    {ktls : Bool} {early : Bytes}
    (hd : pkiHsFeed base pcfg tc buf = .done tc' consumed toSend alpn ktls early) :
    s.thisUpdate ≤ pcfg.now ∧ pcfg.now < s.nextUpdate :=
  (pki_ocsp_valid base pcfg tc buf s hs hd).2.1

/-- **`pki_ocsp_not_revoked`.** No accepted handshake carries a *revoked* (or
`unknown`) staple: OCSP stapling's purpose — proof of non-revocation — holds at
the deployed gate. -/
theorem pki_ocsp_not_revoked (base : TlsConn → Bytes → HsOut) (pcfg : PkiCfg)
    (tc : TlsConn) (buf : Bytes) (s : Resume.Staple)
    (hs : pcfg.staple = some s)
    {tc' : TlsConn} {consumed : Nat} {toSend : Bytes} {alpn : Proto.Alpn}
    {ktls : Bool} {early : Bytes}
    (hd : pkiHsFeed base pcfg tc buf = .done tc' consumed toSend alpn ktls early) :
    s.certStatus = Resume.CertStatus.good :=
  (pki_ocsp_valid base pcfg tc buf s hs hd).1

/-! ## The reactor seam: the gate is invoked on the running `onBytes` path

`Proto.onBytes` on a `.tlsHandshake` state calls `Proto.hsStep`, which calls
`cfg.hsFeed`. With `wirePki`, that field is `pkiHsFeed`. A gate that never emits
`.done` therefore cannot carry `hsStep` into an established protocol state:
`hsStep` enters `runH1`/`runH2` (an established state) only on `.done`, so on
`.more` it stays in `.tlsHandshake` and on `.fail` it closes. -/

/-- A handshake feeder that never accepts keeps the running `hsStep` off the
established path: it either closes the connection or stays in the handshake. -/
theorem hsStep_no_done (cfg : Config) (stay : Proto.ProtoState)
    (tc : TlsConn) (buf : Bytes)
    (hnd : ∀ tc' consumed toSend alpn ktls early,
      cfg.hsFeed tc buf ≠ .done tc' consumed toSend alpn ktls early) :
    (Proto.hsStep cfg none stay tc buf).closeNow = true ∨
    ∃ tc' rest, (Proto.hsStep cfg none stay tc buf).proto = .tlsHandshake tc' rest := by
  unfold Proto.hsStep
  cases hh : cfg.hsFeed tc buf with
  | more a b c => exact Or.inr ⟨a, buf.drop b, rfl⟩
  | fail => exact Or.inl rfl
  | done a b c d e f => exact absurd hh (hnd a b c d e f)

/-- **`mtls_no_auth_on_failure_reactor`.** On the running reactor path, an mTLS
handshake whose presented chain fails the real validation never reaches an
established protocol state: `Proto.onBytes` on the `.tlsHandshake` state either
closes the connection or leaves it still handshaking. Composes
`mtls_no_auth_on_failure` with `Proto.onBytes`/`Proto.hsStep`. -/
theorem mtls_no_auth_on_failure_reactor (tcfg : Tls.Config) (pcfg : PkiCfg)
    (cfg : Config) (tc : TlsConn) (tlsBuf data : Bytes)
    (hreq : pcfg.mtlsRequired = true)
    (hfail : Mtls.verifyFrom pcfg.mtlsEnv pcfg.now
              (pcfg.chainOf tc (tlsBuf ++ data)) = false) :
    (Proto.onBytes (wirePki tcfg pcfg cfg) (.tlsHandshake tc tlsBuf) data).closeNow = true ∨
    ∃ tc' rest, (Proto.onBytes (wirePki tcfg pcfg cfg) (.tlsHandshake tc tlsBuf) data).proto
        = .tlsHandshake tc' rest := by
  have hnd : ∀ tc' consumed toSend alpn ktls early,
      (wirePki tcfg pcfg cfg).hsFeed tc (tlsBuf ++ data)
        ≠ .done tc' consumed toSend alpn ktls early := by
    intro tc' consumed toSend alpn ktls early
    rw [wirePki_hsFeed]
    exact mtls_no_auth_on_failure _ pcfg tc (tlsBuf ++ data) hreq hfail
  simpa only [Proto.onBytes] using
    hsStep_no_done (wirePki tcfg pcfg cfg) (.tlsHandshake tc tlsBuf) tc (tlsBuf ++ data) hnd

/-- **`pki_resume_window_reactor`.** On the running reactor path, a resumption
ticket presented outside its validity window never carries the connection into
an established protocol state: `Proto.onBytes` closes or stays in handshake.
Composes `pki_resume_window` with `Proto.onBytes`/`Proto.hsStep`. -/
theorem pki_resume_window_reactor (tcfg : Tls.Config) (pcfg : PkiCfg)
    (cfg : Config) (tc : TlsConn) (tlsBuf data : Bytes) (t : Resume.Ticket)
    (ht : pcfg.ticketOf tc (tlsBuf ++ data) = some t)
    (hbad : ¬ (t.issued ≤ pcfg.now ∧ pcfg.now < t.expiry)) :
    (Proto.onBytes (wirePki tcfg pcfg cfg) (.tlsHandshake tc tlsBuf) data).closeNow = true ∨
    ∃ tc' rest, (Proto.onBytes (wirePki tcfg pcfg cfg) (.tlsHandshake tc tlsBuf) data).proto
        = .tlsHandshake tc' rest := by
  have hnd : ∀ tc' consumed toSend alpn ktls early,
      (wirePki tcfg pcfg cfg).hsFeed tc (tlsBuf ++ data)
        ≠ .done tc' consumed toSend alpn ktls early := by
    intro tc' consumed toSend alpn ktls early
    rw [wirePki_hsFeed]
    intro hd
    exact hbad (pki_resume_window _ pcfg tc (tlsBuf ++ data) t ht hd)
  simpa only [Proto.onBytes] using
    hsStep_no_done (wirePki tcfg pcfg cfg) (.tlsHandshake tc tlsBuf) tc (tlsBuf ++ data) hnd

end PkiWire
end Reactor
