/-
# AcmeIssue — the RFC 8555 protocol driver: a real certificate from a real CA

The ACME pieces drorb already had were all *sans-IO*: the order and challenge
FSMs (`Acme.Order`, `Acme.Challenge`) with their safety theorems, the JWS
protected-header/signing-input encoding and the key authorization (`Pki.Acme`),
and the HTTP-01 responder stage (`Reactor.Stage.AcmeChallenge`). Nothing ever
spoke to a CA — `AcmeLive`/`AcmeOrderLive` name that exactly as their residual
("real interop against a public CA — the JWS-signed HTTPS transport, nonce
handling, account registration").

This executable is that residual, discharged: it drives the full RFC 8555 flow
against a live ACME server and lands a CA-issued certificate on disk in the
form drorb's TLS cert pool loads.

    directory → newNonce → newAccount → newOrder → authz
      → HTTP-01 (served by drorb) → challenge ready → poll
      → finalize (a real PKCS#10 CSR) → poll → download chain

## What is verified, and what is glue — plainly

**Verified Lean, reused unchanged.** The JWS protected header and signing input
(`Pki.Acme.encodeHeader`, `signingInput`) — so every request binds its nonce,
its URL, and its account key. The account thumbprint and key authorization
(`Pki.Acme.thumbprint`, `keyAuthorization`, proven `keyAuthorization_correct`).
The ECDSA-P256 signature over the JWS signing input
(`Pki.AcmeEs256.signAcmeEs256`, `es256_signs_the_signing_input`) and over the
CSR, both on HACL*'s F*-verified P-256 with the deterministic nonce chain.
SHA-256 is EverCrypt. The CSR encoding (`Pki.Csr`, with `san_names_roundtrip`
and the DER round-trip `Pki.Der.readTlv_tlv`).

**Lean, total, unproven plumbing.** `Pki.AcmeDriver`'s JSON member extractor and
HTTP/1.1 response splitter — targeted readers, not general parsers; their limits
are documented there, and `jsonString_of_member` pins the string case.

**Host glue, thin and named.** Two things, both stated so they are not mistaken
for verified drorb:

1. **The TLS transport is drorb's OWN verified TLS 1.3 client** (`TlsClient`),
   not a shelled-out TLS subprocess. Each request rides `TlsClient.request`: the verified ClientHello
   / ServerHello / record layer / §7.1 key schedule, with the CA authenticated
   by CertificateVerify + Finished (fail-closed). The audited primitives are
   HACL* X25519 and EverCrypt Ed25519 / SHA-256 / AEAD; the only host glue is the
   TCP byte-mover (`ffi/derp_net.o`). No external TLS tool, no subprocess in the path.
2. Base64 decoding of the returned PEM, and file I/O.

Usage:
  acme-issue <directoryUrl> <domain> <staticRoot> <outDir> [contactEmail]
-/
import Pki.AcmeDriver
import Pki.AcmeEs256
import Pki.Csr
import Crypto
import Pki.AcmeAccount
import TlsClient

namespace AcmeIssue

open Pki.Acme
open Pki.AcmeDriver

/-! ## Rendering -/

def str (l : Str) : String := String.mk l
def L (s : String) : Str := s.toList

def toHex (b : List UInt8) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.foldl (fun acc x => acc ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

/-! ## Host glue #1 — the TLS transport (drorb's verified `TlsClient`)

The request is handshaked and served over drorb's own verified TLS 1.3 client;
see the header. The old note about handing the request to the
subprocess on stdin and the whole response read back from stdout. -/

/-- Is `h` a dotted-quad IPv4 literal (the `inet_pton` input the verified
client's `tcpConnect` needs)? -/
def dottedQuad (h : String) : Bool :=
  let parts := h.splitOn "."
  parts.length == 4 && parts.all (fun p => !p.isEmpty && p.length ≤ 3 && p.all Char.isDigit)

/-- Resolve an ACME host to the dotted-quad IPv4 the verified TLS client dials.
`localhost` maps to `127.0.0.1`; a literal IPv4 passes through. A name needing
DNS is a NAMED residual (a resolver shim), rejected rather than shelled out —
there is no shelled-out TLS tool and no unaudited fallback. -/
def resolveIp (host : String) : IO String :=
  if host == "localhost" then pure "127.0.0.1"
  else if dottedQuad host then pure host
  else throw (IO.userError s!"acme: verified client needs a dotted-quad IPv4 (or localhost) for {host}; DNS resolver is a named residual")

/-- **The ACME TLS transport — drorb's OWN verified TLS 1.3 client, no external TLS subprocess.**
The request is handshaked and served over `TlsClient.request`: ClientHello, the
verified record layer, the §7.1 key schedule, and CertificateVerify + Finished
authentication of the CA (fail-closed — `requireAuth`). The host glue is the TCP
byte-mover only; no subprocess, no external TLS tool in the path. -/
def httpsRaw (host : String) (port : Nat) (req : String) : IO String := do
  let ip ← resolveIp host
  match ← TlsClient.requestText ip (UInt16.ofNat port) host req with
  | .ok resp => return resp
  | .error e => throw (IO.userError s!"acme: drorb verified TLS client failed for {host}:{port}: {e}")

/-- Assemble an HTTP/1.1 request. `Connection: close` makes the server end the
stream, which is what terminates the subprocess read. -/
def buildReq (method : String) (u : Url) (body : Option String) : String :=
  let hostHdr := if u.port == 443 then str u.host else s!"{str u.host}:{u.port}"
  let base :=
    s!"{method} {str u.path} HTTP/1.1\r\nHost: {hostHdr}\r\n\
       User-Agent: drorb-acme/0.1\r\nAccept: */*\r\nConnection: close\r\n"
  match body with
  | none => base ++ "\r\n"
  | some b =>
    base ++ s!"Content-Type: application/jose+json\r\nContent-Length: {b.length}\r\n\r\n{b}"

def request (method : String) (url : Str) (body : Option String) : IO Resp := do
  match parseUrl url with
  | none => throw (IO.userError s!"bad URL: {str url}")
  | some u =>
    let raw ← httpsRaw (str u.host) u.port (buildReq method u body)
    match parseResp raw.toList with
    | none => throw (IO.userError s!"unparseable response from {str url}:\n{raw}")
    | some r => return r

/-! ## base64url decoding (host glue #2)

The CA's nonce is base64url text; `Pki.Acme.encodeHeader` re-encodes the nonce
member from bytes, so the text must be decoded to the bytes it stands for. -/

def b64urlVal (c : Char) : Nat :=
  (b64urlAlphabet.findIdx? (· == c)).getD 0

def b64urlDecodeGo : Str → List UInt8
  | a :: b :: c :: d :: rest =>
    let n := b64urlVal a * 262144 + b64urlVal b * 4096 + b64urlVal c * 64 + b64urlVal d
    UInt8.ofNat (n / 65536) :: UInt8.ofNat ((n / 256) % 256) :: UInt8.ofNat (n % 256)
      :: b64urlDecodeGo rest
  | [a, b, c] =>
    let n := b64urlVal a * 4096 + b64urlVal b * 64 + b64urlVal c
    [UInt8.ofNat (n / 1024), UInt8.ofNat ((n / 4) % 256)]
  | [a, b] =>
    let n := b64urlVal a * 64 + b64urlVal b
    [UInt8.ofNat (n / 16)]
  | _ => []

def b64urlDecode (s : Str) : List UInt8 := b64urlDecodeGo s

/-! ## JWS envelopes (RFC 8555 §6.2) -/

/-- The flattened JWS JSON the CA expects. The three members are exactly the
base64url of what `Pki.Acme` encoded and signed. -/
def jwsEnvelope (hdr : List UInt8) (payload : List UInt8) (sig : List UInt8) : String :=
  s!"\{\"protected\":\"{str (base64url hdr)}\",\
      \"payload\":\"{str (base64url payload)}\",\
      \"signature\":\"{str (base64url sig)}\"}"

structure Ctx where
  priv : ByteArray
  acct : AccountKey
  kid : IO.Ref (Option Str)
  nonce : IO.Ref Str

/-- Record the `Replay-Nonce` the CA returned; every response carries one. -/
def takeNonce (ctx : Ctx) (r : Resp) : IO Unit := do
  match r.header (L "replay-nonce") with
  | some n => ctx.nonce.set n
  | none => pure ()

/-- One JWS-signed POST. The header is built and signed by the verified Lean;
this function only moves bytes. On `badNonce` (RFC 8555 §6.5 — pebble rejects a
share of good nonces deliberately) the request is re-signed with the fresh nonce
the error response carried, which is why the nonce is read on every reply. -/
partial def postJws (ctx : Ctx) (url : Str) (payload : Str) (tries : Nat := 3) :
    IO Resp := do
  let nonce ← ctx.nonce.get
  let kid ← ctx.kid.get
  let keyId := match kid with
    | some k => JwsKeyId.kid k
    | none => JwsKeyId.jwk ctx.acct
  -- `encodeHeader` base64url-ENCODES the nonce member, and the CA hands the
  -- nonce out already in base64url text, so it is decoded back to the bytes it
  -- denotes before being placed in the header.
  let hdr : ProtectedHeader :=
    { alg := .es256, nonce := b64urlDecode nonce, url := url, keyId := keyId }
  let req : JwsRequest := { hdr := hdr, payload := asciiBytes payload }
  match Pki.AcmeEs256.signAcmeEs256 ctx.priv req with
  | none => throw (IO.userError "ES256 signing failed")
  | some sig =>
    let env := jwsEnvelope (encodeHeader hdr) (asciiBytes payload) sig.toList
    let r ← request "POST" url (some env)
    takeNonce ctx r
    if r.status == 400 && tries > 0 then
      if (afterSub (L "badNonce") r.body).isSome then
        postJws ctx url payload (tries - 1)
      else return r
    else return r

/-! ## PEM -/

def b64StdAlphabet : Str :=
  (L "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/")

def b64StdVal (c : Char) : Nat := (b64StdAlphabet.findIdx? (· == c)).getD 0

def b64StdDecode : Str → List UInt8
  | a :: b :: c :: d :: rest =>
    let n := b64StdVal a * 262144 + b64StdVal b * 4096
      + (if c == '=' then 0 else b64StdVal c) * 64
      + (if d == '=' then 0 else b64StdVal d)
    let b1 := UInt8.ofNat (n / 65536)
    let b2 := UInt8.ofNat ((n / 256) % 256)
    let b3 := UInt8.ofNat (n % 256)
    if c == '=' then [b1]
    else if d == '=' then [b1, b2]
    else b1 :: b2 :: b3 :: b64StdDecode rest
  | _ => []

/-- Split a PEM bundle into its DER certificates, in order (leaf first). -/
partial def pemCerts (s : Str) : List (List UInt8) :=
  match afterSub (L "-----BEGIN CERTIFICATE-----") s with
  | none => []
  | some rest =>
    match splitOnSub (L "-----END CERTIFICATE-----") rest with
    | none => []
    | some (b64, tail) =>
      let clean := b64.filter (fun c => !isWs c)
      b64StdDecode clean :: pemCerts tail

/-! ## The flow -/

def expectOk (what : String) (r : Resp) : IO Unit := do
  if r.status < 200 || r.status >= 300 then
    throw (IO.userError s!"{what}: HTTP {r.status}\n{str r.body}")

def jsonStr (key : String) (body : Str) : IO Str := do
  match jsonString (L key) body with
  | some v => return v
  | none => throw (IO.userError s!"missing JSON member {key} in:\n{str body}")

/-- Generate a P-256 scalar HACL* accepts. -/
partial def freshScalar : IO ByteArray := do
  let b ← IO.getRandomBytes 32
  match TlsCrypto.P256.pub b with
  | some _ => return b
  | none => freshScalar

def run (dirUrl domain staticRoot outDir : String) (contact : Option String) :
    IO UInt32 := do
  IO.println "== drorb acme-issue : RFC 8555 issuance against a live CA =="
  IO.println s!"directory : {dirUrl}"
  IO.println s!"identifier: {domain}"

  -- ── account key (ES256; Boulder/pebble reject EdDSA account keys) ──
  -- Persisted when DRORB_ACME_ACCOUNT_KEY is set, so a re-run (a renewal) reuses
  -- the SAME account and never trips the CA new-account rate limit; otherwise a
  -- fresh key per run (the old behaviour). Pki.AcmeAccount owns the store.
  let priv ← match ← IO.getEnv "DRORB_ACME_ACCOUNT_KEY" with
    | some kp => Pki.AcmeAccount.loadOrCreateScalar kp
    | none => freshScalar
  let acct ← match Pki.AcmeEs256.accountKeyOfScalar priv with
    | some k => pure k
    | none => throw (IO.userError "could not derive account JWK")
  IO.println s!"account key: ES256 (P-256), thumbprint {str (thumbprint acct)}"

  let kid ← IO.mkRef none
  let nonceRef ← IO.mkRef ([] : Str)
  let ctx : Ctx := { priv := priv, acct := acct, kid := kid, nonce := nonceRef }

  -- ── 1. directory ──
  let dir ← request "GET" (L dirUrl) none
  expectOk "directory" dir
  let newNonceU ← jsonStr "newNonce" dir.body
  let newAccountU ← jsonStr "newAccount" dir.body
  let newOrderU ← jsonStr "newOrder" dir.body
  IO.println s!"directory OK — newOrder {str newOrderU}"

  -- ── 2. newNonce ──
  let nr ← request "HEAD" newNonceU none
  takeNonce ctx nr
  let n0 ← nonceRef.get
  if n0.isEmpty then throw (IO.userError "no Replay-Nonce from newNonce")
  IO.println s!"nonce acquired ({n0.length} chars)"

  -- ── 3. newAccount (JWS with inline jwk) ──
  let ar ← postJws ctx newAccountU (newAccountPayload (contact.map L))
  expectOk "newAccount" ar
  let acctUrl ← match ar.header (L "location") with
    | some u => pure u
    | none => throw (IO.userError "newAccount returned no Location")
  kid.set (some acctUrl)
  IO.println s!"account registered — kid {str acctUrl}"
  match ← IO.getEnv "DRORB_ACME_ACCOUNT_KEY" with
    | some kp => Pki.AcmeAccount.saveAccountUrl kp (str acctUrl)
    | none => pure ()

  -- ── 4. newOrder ──
  let or_ ← postJws ctx newOrderU (newOrderPayload [L domain])
  expectOk "newOrder" or_
  let orderUrl ← match or_.header (L "location") with
    | some u => pure u
    | none => throw (IO.userError "newOrder returned no Location")
  let authzUrls := jsonStringArray (L "authorizations") or_.body
  let finalizeU ← jsonStr "finalize" or_.body
  IO.println s!"order created — {authzUrls.length} authorization(s)"

  -- ── 5. authorization → the HTTP-01 challenge ──
  let authzU ← match authzUrls with
    | a :: _ => pure a
    | [] => throw (IO.userError "order carried no authorizations")
  let az ← postJws ctx authzU postAsGetPayload
  expectOk "authz" az
  let chals := jsonObjectArray (L "challenges") az.body
  let http01 ← match chals.find? (fun c => jsonString (L "type") c == some (L "http-01")) with
    | some c => pure c
    | none => throw (IO.userError s!"no http-01 challenge offered:\n{str az.body}")
  let token ← jsonStr "token" http01
  let chalUrl ← jsonStr "url" http01

  -- ── 6. provision the response through drorb's own serve path ──
  -- The served bytes are the PROVEN `keyAuthorization` (RFC 8555 §8.1) over the
  -- verified SHA-256 thumbprint — `Pki.Acme.keyAuthorization_correct`.
  let keyAuth := keyAuthorization token acct
  let chalDir := s!"{staticRoot}/.well-known/acme-challenge"
  IO.FS.createDirAll chalDir
  IO.FS.writeFile s!"{chalDir}/{str token}" (str keyAuth)
  IO.println s!"HTTP-01 provisioned: /.well-known/acme-challenge/{str token}"
  IO.println s!"  key authorization = {str keyAuth}"

  -- ── 7. tell the CA we are ready, then poll the authorization ──
  let cr ← postJws ctx chalUrl challengeReadyPayload
  expectOk "challenge ready" cr

  let mut authzStatus : Str := L "pending"
  for _ in [0:40] do
    let a ← postJws ctx authzU postAsGetPayload
    match jsonString (L "status") a.body with
    | some st => authzStatus := st
    | none => pure ()
    if authzStatus == L "valid" || authzStatus == L "invalid" then break
    IO.sleep 400
  IO.println s!"authorization status: {str authzStatus}"
  if authzStatus != L "valid" then
    throw (IO.userError s!"authorization did not validate: {str authzStatus}")

  -- ── 8. the CSR (Pki.Csr) over a fresh certificate key ──
  let certPriv ← freshScalar
  let point ← match Pki.AcmeEs256.publicPoint certPriv with
    | some p => pure p
    | none => throw (IO.userError "could not derive certificate public point")
  let signer := fun (cri : List UInt8) =>
    (TlsCrypto.Sig.ecdsaP256Sign certPriv ⟨cri.toArray⟩).map ByteArray.toList
  let csrDer ← match Pki.Csr.buildCsr signer (some (asciiBytes (L domain))) point
                      [asciiBytes (L domain)] with
    | some d => pure d
    | none => throw (IO.userError "CSR signing failed")
  IO.println s!"CSR built: {csrDer.length} bytes DER, SAN dNSName={domain}"

  -- ── 9. finalize ──
  let fr ← postJws ctx finalizeU (finalizePayload (base64url csrDer))
  expectOk "finalize" fr

  let mut orderStatus : Str := L "processing"
  let mut certUrl : Option Str := none
  for _ in [0:40] do
    let o ← postJws ctx orderUrl postAsGetPayload
    match jsonString (L "status") o.body with
    | some st => orderStatus := st
    | none => pure ()
    certUrl := jsonString (L "certificate") o.body
    if certUrl.isSome || orderStatus == L "invalid" then break
    IO.sleep 400
  IO.println s!"order status: {str orderStatus}"

  let certU ← match certUrl with
    | some u => pure u
    | none => throw (IO.userError s!"order never produced a certificate: {str orderStatus}")

  -- ── 10. download the chain and land it where the TLS pool loads it ──
  let dl ← postJws ctx certU postAsGetPayload
  expectOk "certificate download" dl
  let certs := pemCerts dl.body
  if certs.isEmpty then throw (IO.userError "no certificates in the returned PEM")
  IO.FS.createDirAll outDir
  IO.FS.writeFile s!"{outDir}/chain.pem" (str dl.body)
  match certs with
  | leaf :: issuers =>
    IO.FS.writeBinFile s!"{outDir}/ecdsa-cert.der" ⟨leaf.toArray⟩
    IO.FS.writeBinFile s!"{outDir}/ecdsa-key.bin" certPriv
    let mut i := 0
    for iss in issuers do
      IO.FS.writeBinFile s!"{outDir}/ecdsa-chain-{i}.der" ⟨iss.toArray⟩
      i := i + 1
    IO.println s!"\nISSUED — leaf {leaf.length} B DER, {issuers.length} issuer(s)"
    IO.println s!"  {outDir}/ecdsa-cert.der   (DRORB_TLS_ECDSA_CERT)"
    IO.println s!"  {outDir}/ecdsa-key.bin    (DRORB_TLS_ECDSA_KEY, 32-byte scalar)"
    IO.println s!"  {outDir}/chain.pem"
  | [] => pure ()
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [d, dom, root, out] => run d dom root out none
  | [d, dom, root, out, c] => run d dom root out (some c)
  | _ => do
    IO.eprintln "usage: acme-issue <directoryUrl> <domain> <staticRoot> <outDir> [contactEmail]"
    return 1

end AcmeIssue

def main (args : List String) : IO UInt32 := AcmeIssue.main args
