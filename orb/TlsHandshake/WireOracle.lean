/-
TlsHandshake.WireOracle — the server handshake + record layer exposed to an
external conformance battery.

A line-oriented stdio oracle around `TlsHandshake.serverStep` and the
established-phase `TlsHandshake.Post` driver: an untrusted TCP front
(conformance/tls/front.py) accepts the socket and splits the byte stream into
TLS records — nothing else — and feeds each record here in hex. Every protocol
decision (ClientHello parse, negotiation, HelloRetryRequest, key schedule,
flight construction, Finished verification, post-handshake KeyUpdate/close,
and the application-data record layer that serves HTTP over TLS) and all crypto
(EverCrypt via `Crypto`) happen in this process, in the same `serverStep` /
`appStep` the theorems are about.

Protocol (one request line, one response line, hex = lowercase, no spaces):

  `CH <hex>`   — a full handshake record (or bare ClientHello message).
                 Reply is one of:
                   `FLIGHT <hex>`  — the server flight (send, await Finished).
                   `HRR <hex>`     — HelloRetryRequest (send, await 2nd CH).
                   `ALERT <hex>`   — a fatal alert record (send, then close).
  `FIN <hex>`  — the client's encrypted-handshake record carrying Finished.
                 Reply `ESTABLISHED` or `ALERT <hex>`.
  `APP <hex>`  — a post-handshake application_data (or alert) record. Reply:
                   `SEND <hex>`  — records to write back (e.g. the HTTP reply).
                   `CLOSE <hex>` — reciprocal close_notify; then the front closes.
                   `ALERT <hex>` — a fatal alert; then the front closes.
                   `NONE`        — nothing to send (e.g. an unfinished request).

Arguments: `<cert.der> <seed.bin> [chain.der ...] [flags]` — the DER
end-entity certificate to present, the 32-byte Ed25519 signing seed (RFC 8032
§5.1.5) matching its public key, and the rest of the certificate chain
(issuing authorities, in order). The X25519/P-256 ephemeral and the
ServerHello random are drawn fresh per process from the OS entropy source, so
each connection gets its own DHE.

Flags (each adds a `TlsHandshake.CertEntry` or deployment option):

  `--rsa <cert.der> <n.bin> <e.bin> <d.bin> [chain.der]`
      An RSA certificate served with `rsa_pss_rsae_sha256` (RFC 8446 §9.1
      MUST) — the key given as big-endian modulus/exponents, signed through
      the verified HACL* `Hacl_RSAPSS` binding (`TlsCrypto.Sig`).
  `--ecdsa <cert.der> <priv.bin> [chain.der]`
      A P-256 certificate served with `ecdsa_secp256r1_sha256` (§9.1 MUST),
      signed through the verified HACL* `Hacl_P256` binding.
  `--sni <hostname> <cert.der> <seed.bin>`
      An additional Ed25519 certificate served ONLY for that SNI host name
      (RFC 6066 §3) — exercises SNI-based certificate selection.
  `--staple <ocsp.der>`
      A DER OCSPResponse stapled on the DEFAULT certificate when the client
      sends `status_request` (RFC 8446 §4.4.2.1).
  `--rsa-staple <ocsp.der>` / `--ecdsa-staple <ocsp.der>`
      Staples for the RSA / ECDSA entries.
  `--early <replay-dir>`
      Opt into 0-RTT (§4.2.10): issued tickets advertise `early_data`, and an
      offered ticket is accepted for early data only if its identity hash is
      NOT yet marked in `<replay-dir>` — a single-use, filesystem-backed
      anti-replay register (§8). The mark is written before the handshake
      proceeds, so a replayed ticket finds it and is refused early data
      (the connection still resumes, 1-RTT).

This executable instantiates the `ServerParams.p256Dh` and `CertEntry.sign`
seams with the verified HACL* bindings (`TlsCrypto.P256`, `TlsCrypto.Sig`,
`Crypto.ed25519Sign`) and links `ffi/tls_p256_shim.o`, so secp256r1 and both
§9.1 MUST-support signature schemes are served here.

On establishment the oracle issues a NewSessionTicket (RFC 8446 §4.6.1): the
`FIN` reply is `ESTABLISHED <hex>` where the hex is the sealed ticket record
for the front to write (followed, when the client's accepted 0-RTT data
already carried a complete HTTP request, by the response record). Tickets are
stateless (sealed under a key derived from the signing seed) and carry the
issuing connection's suite and ALPN, so a later connection — a different
oracle process — can resume from them (§4.2.11, PSK + ECDHE) and offer early
data against them (§4.2.10).

During an accepted 0-RTT phase the front keeps feeding the client's records
as `FIN <hex>` lines; the oracle answers `CONT` for each consumed early-data
record (and for EndOfEarlyData / trial-skipped records) until the client
Finished establishes.

Run: `lake exe tls-wire-oracle cert.der seed.bin [chain.der] [flags]` (one
process per connection).
-/
import TlsHandshake.Post
import TlsCrypto.P256
import TlsCrypto.Sig
import Dsl.Deployment

namespace TlsHandshake.WireOracle

open TlsHandshake

/-- Parse a hex string into a `ByteArray` (stops at the first non-hex pair). -/
def ofHex (s : String) : ByteArray := Id.run do
  let cs := s.toList.filter (fun c => c ≠ ' ' ∧ c ≠ '\n')
  let hexVal : Char → Option UInt8 := fun c =>
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
    else none
  let rec go : List Char → ByteArray → ByteArray
    | hi :: lo :: rest, acc =>
      match hexVal hi, hexVal lo with
      | some h, some l => go rest (acc.push (h * 16 + l))
      | _, _ => acc
    | _, acc => acc
  go cs (ByteArray.mk #[])

def toHex (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.toList.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

/-- One reply line, flushed so the front sees it immediately. -/
def reply (stdout : IO.FS.Stream) (s : String) : IO Unit := do
  stdout.putStr (s ++ "\n")
  stdout.flush

/-- The oracle's own view of the connection between requests. `earlyBuf`
accumulates accepted 0-RTT plaintext so the request it carries is answered
right after establishment. -/
inductive OStage where
  | handshake (st : HsState) (earlyBuf : List UInt8 := [])
  | established (app : AppConn) (reqBuf : List UInt8)
  | dead

/-- Mark a ticket identity as used in the single-use anti-replay register
(one file per identity hash under `dir`): `true` iff this is the FIRST use.
The existence check and the mark are two filesystem steps, not one atomic
operation — the register is the conformance deployment's gate, honest about
that seam; a production register would use an atomic create. -/
def markTicketOnce (dir : String) (identity : Tls.Bytes) : IO Bool := do
  let path := System.FilePath.mk dir / toHex (Crypto.sha256 (ofBytes identity))
  if (← path.pathExists) then
    return false
  IO.FS.writeFile path "used"
  return true

/-- **The config TLS-profile read.** Resolve the deployment's named TLS profile
against the base handshake terminator through
`Dsl.DeploymentConfig.serverParamsFor` (`Reactor.Deploy.altDeployment`'s TLS
matrix), so the running `serverStep` reads the config profile's 0-RTT / OCSP
policy. `none` (no `--tls-profile`) is the identity — the base terminator, byte
unchanged. A 0-RTT-off profile (`public-web`) pins the anti-replay gate shut and
zeroes the advertised early-data window; a 0-RTT-on profile (`internal-mtls`)
keeps the deployment's own register gate and advertises the profile's window. -/
def profileTransform (name : Option String) (params : ServerParams) : ServerParams :=
  match name with
  | none   => params
  | some n =>
    -- Exactly `Dsl.DeploymentConfig.serverParamsFor` over the deployment's TLS
    -- dimension (`altDeployment.tls = Dsl.Cfg.dualStackTls`): resolve the
    -- well-formed named profile, then override the base handshake policy.
    match Dsl.Cfg.dualStackTls.resolveWF n with
    | some p => p.applyServerParams params
    | none   => params

/-- The per-ClientHello anti-replay gate: when 0-RTT is enabled (`replayDir`)
and the ClientHello offers a PSK with early data, consult-and-mark the
register, and instantiate `ServerParams.earlyDataOk` with the verdict for
exactly that identity. Without `--early` the default gate (reject all 0-RTT)
stands. The config TLS profile is applied LAST, so a 0-RTT-off profile stays shut
regardless of the register. -/
def gateParams (profile : Option String) (params : ServerParams) (replayDir : Option String)
    (chBytes : Tls.Bytes) : IO ServerParams := do
  let gated ← match replayDir with
    | none => pure params
    | some dir =>
      match parseClientHello chBytes with
      | some ch =>
        match ch.psk, ch.earlyData with
        | some op, true =>
          let fresh ← markTicketOnce dir op.identity
          pure { params with earlyDataOk := fun id => fresh && (id == op.identity) }
        | _, _ => pure params
      | none => pure params
  return profileTransform profile gated

/-- Build the response to one post-handshake application record: open it,
serve HTTP once the request headers are complete, or handle the control
messages `appStep` recognizes. Returns the next stage and the reply line. -/
def handleApp (app : AppConn) (reqBuf : List UInt8) (record : ByteArray) :
    OStage × String :=
  match appStep app record.toList with
  | (app', .deliver content, _) =>
    let reqBuf := reqBuf ++ content
    if hasCrlfCrlf reqBuf then
      -- A complete HTTP request head: serve the fixed 200 as an app record,
      -- then reset the accumulator for a possible next pipelined request.
      match sealRecordAt app'.txKeys app'.txSeq 0x17 httpResponse with
      | some wire =>
        (.established { app' with txSeq := app'.txSeq + 1 } [], s!"SEND {toHex wire}")
      | none => (.dead, "ALERT " ++ toHex (plainAlert internalErrorDesc))
    else
      (.established app' reqBuf, "NONE")
  | (_app', .close, reply) => (.dead, s!"CLOSE {toHex reply}")
  | (app', .keyUpdated, reply) =>
    if reply.isEmpty then (.established app' reqBuf, "NONE")
    else (.established app' reqBuf, s!"SEND {toHex reply}")
  | (_, .fatal _, alert) => (.dead, s!"ALERT {toHex alert}")

/-- The request loop: drive `serverStep` (handshake, including an accepted or
trial-skipped 0-RTT phase) then `appStep` (established) over the fed records. -/
partial def loop (params : ServerParams) (replayDir : Option String) (profile : Option String)
    (stage : OStage) (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return   -- EOF: the front closed the connection
  let stage' ←
    match line.trim.splitOn " ", stage with
    | ["CH", h], .handshake hst _ =>
      -- Accept a first (waitCH) or retried (waitCH2) ClientHello.
      let st0 := match hst with
        | .waitCH => HsState.waitCH
        | .waitCH2 r => HsState.waitCH2 r
        | _ => HsState.waitCH
      -- Instantiate the 0-RTT anti-replay gate for THIS offer (§8).
      let params ← gateParams profile params replayDir (ofHex h).toList
      match serverStep params st0 (ofHex h).toList with
      | (.waitClientFinished est, out) => do
        reply stdout s!"FLIGHT {toHex out.flight}"
        pure (.handshake (.waitClientFinished est))
      | (.waitCH2 r, out) => do
        reply stdout s!"HRR {toHex out.flight}"
        pure (.handshake (.waitCH2 r))
      | (_, out) => do
        reply stdout s!"ALERT {toHex out.flight}"
        pure .dead
    | ["FIN", h], .handshake (.waitClientFinished est) earlyBuf =>
      match serverStep params (.waitClientFinished est) (ofHex h).toList with
      | (.waitClientFinished est', out) => do
        -- An accepted early-data record, EndOfEarlyData, or a trial-skipped
        -- rejected-0-RTT record: the handshake continues.
        reply stdout "CONT"
        pure (.handshake (.waitClientFinished est') (earlyBuf ++ out.earlyData))
      | (.established est', _) => do
        -- Issue a NewSessionTicket (RFC 8446 §4.6.1) as the first
        -- application-phase record: a stateless sealed ticket for this
        -- session's resumption PSK — carrying the connection's suite and
        -- ALPN (§4.2.10) and, when 0-RTT is enabled, the early_data
        -- advertisement — under the server application keys. When the
        -- accepted 0-RTT data already carried a complete HTTP request,
        -- answer it in the same reply.
        let app := mkAppConn est'
        let sealNonce ← IO.getRandomBytes 12
        let ageAddBytes ← IO.getRandomBytes 4
        let ageAdd := ageAddBytes.toList.foldl (fun a b => a * 256 + b.toNat) 0
        let (app, wire) :=
          match buildNewSessionTicket (ticketKey params.certSeed) sealNonce
                  app.resumptionMaster ageAdd est'.suite est'.alpnProto
                  (if replayDir.isSome then params.maxEarlyData else 0) with
          | some nst =>
            match sealRecordAt app.txKeys app.txSeq 0x16 nst with
            | some w => ({ app with txSeq := app.txSeq + 1 }, w)
            | none => (app, ByteArray.empty)
          | none => (app, ByteArray.empty)
        let (app, wire, reqBuf) :=
          if hasCrlfCrlf earlyBuf then
            match sealRecordAt app.txKeys app.txSeq 0x17 httpResponse with
            | some w => ({ app with txSeq := app.txSeq + 1 }, wire ++ w, [])
            | none => (app, wire, earlyBuf)
          else (app, wire, earlyBuf)
        if wire.isEmpty then do
          reply stdout "ESTABLISHED"
          pure (.established app reqBuf)
        else do
          reply stdout s!"ESTABLISHED {toHex wire}"
          pure (.established app reqBuf)
      | (_, out) => do
        reply stdout s!"ALERT {toHex out.flight}"
        pure .dead
    | ["APP", h], .established app reqBuf =>
      let (stage', line) := handleApp app reqBuf (ofHex h)
      reply stdout line
      pure stage'
    | _, _ => do
      reply stdout "FAIL input"
      pure .dead
  match stage' with
  | .dead => return
  | _ => loop params replayDir profile stage' stdin stdout

/-- Everything the flag walk accumulates. -/
structure Flags where
  chain : List ByteArray := []
  certs : List CertEntry := []
  staple : Option ByteArray := none
  replayDir : Option String := none
  /-- The deployment TLS profile name (`--tls-profile <name>`) the running
  terminator reads its 0-RTT / OCSP policy from (`Dsl.DeploymentConfig.serverParamsFor`).
  `none` is the base terminator, byte-unchanged. -/
  tlsProfile : Option String := none

/-- Walk the argument tail: positional arguments are chain certificates, and
each `--flag` consumes its operands (see the module docstring). -/
partial def parseFlags : List String → Flags → IO (Option Flags)
  | [], acc => return some acc
  | "--rsa" :: certP :: nP :: eP :: dP :: rest, acc => do
    let certData ← IO.FS.readBinFile certP
    let key : TlsCrypto.Sig.RsaKey :=
      { n := ← IO.FS.readBinFile nP
        e := ← IO.FS.readBinFile eP
        d := ← IO.FS.readBinFile dP }
    let (chain, rest) ← takeChain rest
    parseFlags rest { acc with certs := acc.certs ++
      [{ sigAlg := rsaPssSigAlg, certData := certData, certChain := chain
         sign := fun content => TlsCrypto.Sig.rsaPssSign key content }] }
  | "--ecdsa" :: certP :: privP :: rest, acc => do
    let certData ← IO.FS.readBinFile certP
    let priv ← IO.FS.readBinFile privP
    let (chain, rest) ← takeChain rest
    parseFlags rest { acc with certs := acc.certs ++
      [{ sigAlg := ecdsaSigAlg, certData := certData, certChain := chain
         sign := fun content => TlsCrypto.Sig.ecdsaP256Sign priv content }] }
  | "--sni" :: host :: certP :: seedP :: rest, acc => do
    let certData ← IO.FS.readBinFile certP
    let sniSeed ← IO.FS.readBinFile seedP
    parseFlags rest { acc with certs := acc.certs ++
      [{ sigAlg := ed25519SigAlg, certData := certData
         sign := fun content => Crypto.ed25519Sign sniSeed content
         names := [host.toUTF8.toList] }] }
  | "--staple" :: p :: rest, acc => do
    parseFlags rest { acc with staple := some (← IO.FS.readBinFile p) }
  | "--rsa-staple" :: p :: rest, acc => do
    let ocsp ← IO.FS.readBinFile p
    parseFlags rest { acc with certs := acc.certs.map (fun e =>
      if e.sigAlg == rsaPssSigAlg then { e with ocspStaple := some ocsp } else e) }
  | "--ecdsa-staple" :: p :: rest, acc => do
    let ocsp ← IO.FS.readBinFile p
    parseFlags rest { acc with certs := acc.certs.map (fun e =>
      if e.sigAlg == ecdsaSigAlg then { e with ocspStaple := some ocsp } else e) }
  | "--early" :: dir :: rest, acc => do
    IO.FS.createDirAll dir
    parseFlags rest { acc with replayDir := some dir }
  | "--tls-profile" :: name :: rest, acc =>
    parseFlags rest { acc with tlsProfile := some name }
  | p :: rest, acc =>
    if p.startsWith "--" then do
      IO.eprintln s!"unknown or incomplete flag: {p}"
      return none
    else do
      parseFlags rest { acc with chain := acc.chain ++ [← IO.FS.readBinFile p] }
where
  /-- Leading non-flag arguments after `--rsa`/`--ecdsa`: that entry's chain. -/
  takeChain : List String → IO (List ByteArray × List String)
    | p :: rest =>
      if p.startsWith "--" then return ([], p :: rest)
      else do
        let (more, rest') ← takeChain rest
        return ((← IO.FS.readBinFile p) :: more, rest')
    | [] => return ([], [])

def main (args : List String) : IO UInt32 := do
  match args with
  | certPath :: seedPath :: rest =>
    let cert ← IO.FS.readBinFile certPath
    let seed ← IO.FS.readBinFile seedPath
    if seed.size ≠ 32 then
      IO.eprintln "seed must be exactly 32 bytes (RFC 8032 §5.1.5)"
      return 2
    let some flags ← parseFlags rest {} | return 2
    let priv ← IO.getRandomBytes 32
    let rnd ← IO.getRandomBytes 32
    let baseParams : ServerParams :=
      { ephemeralPriv := priv, serverRandom := rnd
        certSeed := seed, certData := cert, certChain := flags.chain
        groupsSupported := [x25519Group, p256Group]
        p256Dh := TlsCrypto.P256.dhPair
        certs := flags.certs
        ocspStaple := flags.staple }
    -- Read the deployment TLS profile: the 0-RTT window / OCSP policy the running
    -- terminator advertises follows the config profile (`--tls-profile`).
    let params := profileTransform flags.tlsProfile baseParams
    if flags.tlsProfile.isSome then
      IO.eprintln s!"tls-wire-oracle: TLS profile {flags.tlsProfile.get!} -> advertised max_early_data = {params.maxEarlyData}"
    loop params flags.replayDir flags.tlsProfile (.handshake .waitCH)
      (← IO.getStdin) (← IO.getStdout)
    return 0
  | _ =>
    IO.eprintln "usage: tls-wire-oracle <cert.der> <seed.bin> [chain.der ...] [flags]"
    return 2

end TlsHandshake.WireOracle

def main (args : List String) : IO UInt32 := TlsHandshake.WireOracle.main args
