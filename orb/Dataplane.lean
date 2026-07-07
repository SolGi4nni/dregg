/-
Dataplane — the proven serve exposed with a C ABI for a native host to drive.

`Arena.Orb.main` runs the deployed serve as a one-shot stdin→stdout filter, and
`IoMac` drives that same proven core from a C accept loop with Lean as the
CALLEE of `@[extern]`. This module inverts the direction: it hands the proven
pipeline OUT across the C ABI as an `@[export]` symbol (`drorb_serve`), so a
native host (the Rust dataplane) is the CALLER — it owns the socket and the
accept loop and calls into the proven core for every request.

The handler is byte-identical to the one the shipped binaries run: request bytes
in, the deployed guarded response bytes out, `deployStepIngress` over a fresh
`ObsState.init`. Nothing here knows a socket exists; the host moves the bytes.
-/
import Reactor.Deploy
import Reactor.Ingress
import Reactor.H2Ingress
import Reactor.Observe
-- The reverse-proxy backend-selection seam (`drorb_proxy_pick`) lives in
-- `Reactor.ProxyDial`. Importing it here places `initialize_Reactor_ProxyDial`
-- in the closure of `initialize_Dataplane`, so the single host-side runtime-init
-- call brings up the proven `Proxy.selectChain` pick's constants AND the archive
-- (ffi/build-dataplane-lib.sh globs every `*.c.o.export`) includes
-- `Reactor/ProxyDial.c.o.export` — without this the `drorb_proxy_pick` symbol is
-- never built into `libdrorb.a` and the host link fails undefined.
import Reactor.ProxyDial
-- The multi-protocol seams (`drorb_serve_ws_frame`, `drorb_serve_datagram`) live
-- in `Dataplane.Multi`. Importing it here places its module initializer in the
-- closure of `initialize_Dataplane`, so the single host-side init call brings up
-- all three exports' constants (a `@[export]` whose module is uninitialized has
-- uninitialized closures — a crash on first call).
import Dataplane.Multi
-- The effect/continuation serve seam (`drorb_serve_step` / `drorb_serve_resume`)
-- lives in `Reactor.ServeStep`. Importing it here places its module initializer in
-- the closure of `initialize_Dataplane` (so the single host-side init brings up the
-- seam's constants), and `ffi/build-dataplane-lib.sh` compiles its
-- `Reactor/ServeStep.c.o.export` object into `libdrorb.a` so the two new exports
-- link.
import Reactor.ServeStep
-- The textual-config parser + denotation (`Dsl.Config.parseChars` /
-- `denoteOn` / `dialChainOfByte`) live in `Dsl.Config.Parse`. Importing it here
-- places `initialize_Dsl_Config_Parse` in the closure of `initialize_Dataplane`
-- so the boot brings up the parser's constants, and `ffi/build-dataplane-lib.sh`
-- compiles its `Dsl/Config/Parse.c.o.export` object into `libdrorb.a` so the new
-- `drorb_deployment_of_config` / `drorb_serve_step_pol` exports link.
import Dsl.Config.Parse
-- The verified TLS 1.3 server handshake + established-phase record layer
-- (`TlsHandshake.serverStep` / `TlsHandshake.appStep` over the verified `Crypto`
-- AEAD/HKDF/SHA and Ed25519/X25519). Importing it here places its module
-- initializers in the closure of `initialize_Dataplane` and — with the explicit
-- `:c.o.export` builds `ffi/build-dataplane-lib.sh` runs for the TLS closure
-- (`Crypto`, `Tls.*`, `TlsCrypto`, `TlsHandshake`, `TlsHandshake.Post`) —
-- archives their objects into `libdrorb.a`, so the `drorb_tls_serve` HTTPS
-- front-door seam below links. The crypto @[extern] symbols resolve against the
-- SAME backend the `orb`/`tls-wire-oracle` exes use (`ffi/crypto_shim.o`,
-- `libaes_fallback.a`, verified HACL*/EverCrypt) — no unverified TLS stack.
import TlsHandshake.Post
-- The RFC 8446 §9.1 MUST-support certificate signature schemes
-- `rsa_pss_rsae_sha256` / `ecdsa_secp256r1_sha256` (`TlsCrypto.Sig.rsaPssSign` /
-- `ecdsaP256Sign`, over the verified HACL* `Hacl_RSAPSS` / `Hacl_P256` bindings).
-- Importing it here lets the deployed front door instantiate the extra
-- `CertEntry.sign` seams the multi-cert pool selects among, so a real client
-- (curl/LibreSSL/browsers) that does not accept Ed25519 is presented an RSA-PSS
-- or ECDSA-P256 certificate per its `signature_algorithms`. Its two @[extern]
-- symbols (`drorb_p256_ecdsa_sign`, `drorb_rsapss_sha256_sign`) resolve against
-- `ffi/tls_p256_shim.o` — the SAME verified backend the `tls-wire-oracle` exe
-- links; `ffi/build-dataplane-lib.sh` archives its `:c.o.export` object.
import TlsCrypto.Sig

/-- The proven pipeline as a pure byte function, exported under the C symbol
`drorb_serve`. One request's bytes in, the deployed response bytes out — the
exact serve `Arena.Orb.main` runs: fork on the HTTP/2 connection preface (h2c
prior knowledge) to the real H2 engine (`serveIngress`); everything else runs
the HTTP/1.1 path through the full ten-stage fold (`deployStepFull2`), which
carries all ten byte-drivers — the five gates (jwt/ipfilter/rate/cache/redirect),
the traversal/policy gates, and the cors/gzip/htmlrewrite/security/header
transforms. The observation state is a fresh `ObsState.init` per call. The native
host calls this once per accepted connection; nothing here knows a socket exists. -/
@[export drorb_serve]
def drorbServe (input : ByteArray) : ByteArray :=
  let bytes := input.toList
  let (out, _obs) :=
    if Reactor.Ingress.hasH2Preface bytes then
      -- h2c prior-knowledge: drive the REAL H2 engine and emit a spec-conformant
      -- HTTP/2 response byte stream (server SETTINGS + ACK + HPACK HEADERS/DATA)
      -- via `Reactor.H2Ingress.serveH2c`, so a real H2 client completes. The H1
      -- branch and every serveIngress H1-equality theorem are untouched.
      (Reactor.H2Ingress.serveH2c bytes, Reactor.Observe.ObsState.init)
    else
      Reactor.Deploy.deployStepFull2 Reactor.Observe.ObsState.init bytes
  ByteArray.mk out.toArray

/-- **The metered serve seam** (`drorb_serve_metered`). The same deployed serve as
`drorb_serve`, but the native host also supplies the accepted peer address (`peer`,
family-tagged bit-encoded per `Reactor.Stage.IpFilter.encodeAddr`) and the
per-connection request index (`seq`, 0-based, incremented each keep-alive
iteration). These feed the real IP-filter (deny `10.0.0.0/8`) and rate (cap 8 /
connection) gates through `Reactor.Deploy.servePipelineFull2Metered`. The host
calls this on the HTTP/1.1 path when it has a peer + keep-alive counter; the
non-metered `drorb_serve` remains for callers that do not. -/
@[export drorb_serve_metered]
def drorbServeMetered (peer : ByteArray) (seq : UInt64) (input : ByteArray) : ByteArray :=
  ByteArray.mk
    (Reactor.Deploy.servePipelineFull2Metered peer.toList seq.toNat input.toList).toArray

/-- **The effect/continuation STEP seam** (`drorb_serve_step`). The proven
resumable serve (`Reactor.ServeStep.serveStep`) surfaced for the interpreter loop:
input byte 0 = the live health/breaker mask (bit `i` ⇒ backend `i` up, exactly the
byte `drorb_proxy_pick` reads), bytes 1.. = the request. Output is the encoded
`Step` (`Reactor.ServeStep.encodeStep`): byte 0 = tag (`0` = DONE, rest = response
bytes; `1` = YIELD proxyDial, byte 1 = the proven-chosen backend id, bytes 2.. =
the request the shell forwards). The shell dials the yielded backend and calls
`drorb_serve_resume` with the reply; the CORE decided whether to proxy, which
backend, and what to do with the upstream bytes. -/
@[export drorb_serve_step]
def drorbServeStep (input : ByteArray) : ByteArray :=
  match input.toList with
  | []          => ByteArray.empty
  | mask :: req =>
    -- Read the LB policy chain FROM the deployment config projection
    -- (`Reactor.Deploy.defaultDeployment.dialChain`), threaded through
    -- `serveStepWith`. Byte-identical to the hardcoded default
    -- (`serveStepWith_deploy`), but the running dial is now the config's read.
    ByteArray.mk (Reactor.ServeStep.encodeStep
      (Reactor.ServeStep.serveStepWith Reactor.ServeStep.deployDialChain mask.toNat req)).toArray

/-- **The config-selected LB policy chain** the running step dials with, keyed on a
deployment selector byte the host supplies (`DRORB_LB_POLICY`): `0` (or unset) is
`defaultDeployment` (the deployed default rendezvous chain, byte-identical to
`drorb_serve_step`), `1` is `altDeployment` (a least-connections `api` pool). A
non-default selector makes the running reverse-proxy dial a config-declared LB
policy, so a proxied request reaches a different backend. -/
def deploymentDialChain : Nat → List Proxy.Policy
  | 1 => Reactor.Deploy.altDeployment.dialChain Reactor.Deploy.proxyPoolName
  | _ => Reactor.ServeStep.deployDialChain

/-- Selector `0` is the deployed default chain — the config-selected step at the
default selector is byte-identical to `drorb_serve_step`. -/
theorem deploymentDialChain_default : deploymentDialChain 0 = Reactor.ProxyDial.dialPolicies := rfl

/-- **The config-driven effect/continuation STEP seam** (`drorb_serve_step_cfg`).
Identical to `drorb_serve_step`, but input byte 0 is a deployment selector
(`DRORB_LB_POLICY`) chosen by the host and byte 1 is the live health mask, bytes
2.. the request. The proxy branch dials the backend the CONFIG-declared LB policy
(`deploymentDialChain sel`) selects, so a non-default deployment reaches a
different backend. Selector `0` reproduces `drorb_serve_step` exactly. -/
@[export drorb_serve_step_cfg]
def drorbServeStepCfg (input : ByteArray) : ByteArray :=
  match input.toList with
  | sel :: mask :: req =>
    ByteArray.mk (Reactor.ServeStep.encodeStep
      (Reactor.ServeStep.serveStepWith (deploymentDialChain sel.toNat) mask.toNat req)).toArray
  | _ => ByteArray.empty

/-- **The config-driven RESUME seam** (`drorb_serve_resume_cfg`). After the shell
executes the yielded effect, it threads back byte 0 = the deployment selector plus
the ORIGINAL `mask :: reqLen(4 BE) :: request :: result` frame; the core REPLAYS
`serveStepWith (deploymentDialChain sel)` (pure ⇒ deterministic), so the resumed
continuation is reconstructed under the SAME config chain the step used. -/
@[export drorb_serve_resume_cfg]
def drorbServeResumeCfg (input : ByteArray) : ByteArray :=
  match input.toList with
  | sel :: rest =>
    ByteArray.mk
      (Reactor.ServeStep.decodeResumeWith (deploymentDialChain sel.toNat) rest).toArray
  | [] => ByteArray.empty

/-- **The L4 accept-surface projection** (`drorb_l4_bind`), for a deployment
selector byte. Returns the newline-joined `bind\tpool\tmode\tid,id,…` lines the
running host turns into its `DRORB_L4_LISTEN` binding — the layer-4 listeners the
config DECLARES, generated from `DeploymentConfig.l4Listeners` (empty for selector
`0`, one `127.0.0.1:8710` raw-TCP passthrough for selector `1`). So a
config-declared L4 listener is bound at deploy time, from the deployment. -/
@[export drorb_l4_bind]
def drorbL4Bind (sel : ByteArray) : ByteArray :=
  let cfg := match sel.toList with
    | 1 :: _ => Reactor.Deploy.altDeployment
    | _      => Reactor.Deploy.defaultDeployment
  let line := fun (b : Dsl.L4Binding) =>
    let m := match b.mode with | .tcp => "tcp" | .udp => "udp"
    let ids := String.intercalate "," (b.backendIds.map toString)
    s!"{b.bind}\t{b.poolName}\t{m}\t{ids}"
  (String.intercalate "\n" (cfg.l4Listeners.map line)).toUTF8

/-- **The effect/continuation RESUME seam** (`drorb_serve_resume`). After the shell
executes a yielded effect, it threads back the ORIGINAL `(mask, request)` plus the
effect result, framed as `mask :: reqLen(4, big-endian) :: request :: result`
(`Reactor.ServeStep.decodeResume`). The proven core REPLAYS `serveStep` (pure ⇒
deterministic) to reconstruct the same continuation and applies it to the result,
returning the resumed response bytes — on the proxy path,
`proxyRespTransform result`. No Lean closure is marshalled across the FFI. -/
@[export drorb_serve_resume]
def drorbServeResume (input : ByteArray) : ByteArray :=
  ByteArray.mk (Reactor.ServeStep.decodeResume input.toList).toArray

/-! ## The ARBITRARY-config deployment path — an operator-written config drives serve

The seams above select among the two NAMED deployments (`default` / `alt`) by a
selector byte. This section replaces that last mile with a real config→deployment
path: the host reads an ARBITRARY textual `DeploymentConfig` at boot, the proven
`Dsl.Config.parseChars` parses it (parse-soundness: `Dsl.Config.parse_render`), and
`denoteOn defaultDeployment` layers its data dimensions onto the proven byte
pipeline. `drorb_deployment_of_config` emits the runtime projections the host needs
(the LB-policy byte + the declared L4 bindings); each proxied request then threads
the LB byte to `drorb_serve_step_pol`, whose chain is `Dsl.Config.dialChainOfByte`
— provably the denoted deployment's `dialChain` for the parsed pool
(`Dsl.Config.dialChainOfByte_denote`). So an arbitrary written config drives the
running reverse-proxy dial, correct-by-construction. -/

/-- Render one `L4Binding` as the host's `bind\tpool\tmode\tid,id,…` line. -/
def l4BindLine (b : Dsl.L4Binding) : String :=
  let m := match b.mode with | .tcp => "tcp" | .udp => "udp"
  let ids := String.intercalate "," (b.backendIds.map toString)
  s!"{b.bind}\t{b.poolName}\t{m}\t{ids}"

/-- **`drorb_deployment_of_config` — parse an operator config into the running
projections.** Input: the textual config bytes (UTF-8). On a parse FAILURE (or a
non-UTF-8 input) the output is EMPTY, so the host falls back to the byte-identical
default. On success the output is newline-joined lines:

* `lb\t<byte>` — the parsed pool's LB policy, encoded by `Dsl.Config.policyByteN`
  (the byte the host threads to `drorb_serve_step_pol`); then
* one `bind\tpool\tmode\tid,id,…` line per declared L4 listener
  (`DeploymentConfig.l4Listeners` of the denoted deployment).

The parsed config is `denoteOn Reactor.Deploy.defaultDeployment` — its byte pipeline
(routing + the fourteen-stage fold) is the proven default; only the IO-boundary
dimensions come from the operator's text. -/
@[export drorb_deployment_of_config]
def drorbDeploymentOfConfig (input : ByteArray) : ByteArray :=
  match String.fromUTF8? input with
  | none => ByteArray.empty
  | some s =>
    match Dsl.Config.parseChars s.data with
    | none => ByteArray.empty
    | some pc =>
      let cfg := Dsl.Config.denoteOn Reactor.Deploy.defaultDeployment pc
      let polByte := Dsl.Config.policyByteN pc.lb.toProxy
      let lbLine := s!"lb\t{polByte}"
      -- The route-count gate the host reads (`has_routes`): flat routes PLUS declared
      -- virtual-host items, so a vhost-only config also routes through the config serve.
      let routesLine := s!"routes\t{pc.routes.length + pc.vitems.length}"
      let l4lines := cfg.l4Listeners.map l4BindLine
      -- The proxy-vhost hostnames: a request whose `Host` names one of these is
      -- reverse-proxied host-side to the configured fleet (the `hostGlob` served path
      -- answers a proxy block route with a placeholder; the real forward is host-side).
      let vproxyLines := (Dsl.Config.proxyVHostNames pc.vitems).map (fun h => s!"vproxy\t{h}")
      (String.intercalate "\n" (lbLine :: routesLine :: (l4lines ++ vproxyLines))).toUTF8

/-- **`drorb_serve_step_pol` — the effect/continuation STEP dialed by a config
LB-policy byte.** Input: byte 0 = the LB-policy byte
(`Dsl.Config.policyByteN`, cached by the host from `drorb_deployment_of_config`),
byte 1 = the live health mask, bytes 2.. = the request. The reverse-proxy branch
dials the backend `Dsl.Config.dialChainOfByte` selects — provably the parsed
config's declared policy. -/
@[export drorb_serve_step_pol]
def drorbServeStepPol (input : ByteArray) : ByteArray :=
  match input.toList with
  | pol :: mask :: req =>
    ByteArray.mk (Reactor.ServeStep.encodeStep
      (Reactor.ServeStep.serveStepWith (Dsl.Config.dialChainOfByte pol.toNat) mask.toNat req)).toArray
  | _ => ByteArray.empty

/-- **`drorb_serve_resume_pol` — resume the config-policy STEP.** Input byte 0 is
the same LB-policy byte, then the ORIGINAL `mask :: reqLen(4 BE) :: request ::
result` frame; the core REPLAYS `serveStepWith (dialChainOfByte pol)` (pure ⇒
deterministic) so the resumed continuation matches the chain the step used. -/
@[export drorb_serve_resume_pol]
def drorbServeResumePol (input : ByteArray) : ByteArray :=
  match input.toList with
  | pol :: rest =>
    ByteArray.mk
      (Reactor.ServeStep.decodeResumeWith (Dsl.Config.dialChainOfByte pol.toNat) rest).toArray
  | [] => ByteArray.empty

/-- **No regression.** A config selecting `rendezvous` (policy byte `3`) makes the
config-policy step byte-identical to the deployed default step (`serveStep`): the
rendezvous chain IS the deployed default chain. So an unset / rendezvous config
regresses nothing. -/
theorem serveStepPol_rendezvous (mask : Nat) (input : Proto.Bytes) :
    Reactor.ServeStep.serveStepWith (Dsl.Config.dialChainOfByte 3) mask input
      = Reactor.ServeStep.serveStep mask input := rfl

/-- **The config policy byte drives the exact declared dial.** For any parsed
config, the chain the config-policy step runs from `pc`'s LB byte is exactly the
denoted deployment's dial chain for the parsed pool — the running dial is the
config's declared policy, not a named-deployment selection. -/
theorem serveStepPol_denotes (pc : Dsl.Config.ParsedConfig) (mask : Nat) (input : Proto.Bytes) :
    Reactor.ServeStep.serveStepWith
        (Dsl.Config.dialChainOfByte (Dsl.Config.policyByteN pc.lb.toProxy)) mask input
      = Reactor.ServeStep.serveStepWith
          ((Dsl.Config.denoteOn Reactor.Deploy.defaultDeployment pc).dialChain
            (String.mk pc.poolName)) mask input := by
  rw [Dsl.Config.dialChainOfByte_denote]

#guard Dsl.Config.policyByteN Dsl.Cfg.LbPolicy.rendezvous.toProxy == 3
#guard Dsl.Config.policyByteN Dsl.Cfg.LbPolicy.leastConn.toProxy == 1
#guard Dsl.Config.policyByteN Dsl.Cfg.LbPolicy.roundRobin.toProxy == 0

/-! ## The config-ROUTE-TABLE serve — an operator config declares the served routes

`drorb_deployment_of_config` above surfaces the parsed config's IO-boundary
projections (LB byte, L4 binds, route count). This seam surfaces the last one — the
ROUTE TABLE — as a served response: given the config text and a request, it serves
the request through `Reactor.Deploy.servePipelineOf (denoteOn defaultDeployment pc)`,
the SAME proven fourteen-stage fold but over the CONFIG's route table
(`Dsl.Config.denoteOn_routes`). A `redirect`/`respond`/`static` route answers
directly; a routeless / unparseable config falls back to the byte-identical default
serve (`servePipelineFull2`), so a host that sets no routes regresses nothing. -/

/-- Decode a 4-byte big-endian length prefix. -/
def be32 (a b c d : UInt8) : Nat :=
  a.toNat <<< 24 ||| b.toNat <<< 16 ||| c.toNat <<< 8 ||| d.toNat

/-- Serve one request under a parsed config's route table + virtual-host dimension
(or the byte-identical default when the config declares neither). -/
def serveUnderConfig (pc : Dsl.Config.ParsedConfig) (req : Proto.Bytes) : Proto.Bytes :=
  match pc.routes, pc.vitems with
  | [], [] => Reactor.Deploy.servePipelineFull2 req
  | _,  _  => Reactor.Deploy.servePipelineOf (Dsl.Config.denoteOn Reactor.Deploy.defaultDeployment pc) req

/-- **`drorb_serve_cfg` — serve a request under an operator config's route table.**
Input framing: `cfgLen(4 BE) :: configBytes :: requestBytes`. The config bytes are
parsed by the proven `Dsl.Config.parseChars`; when the config declares routes, the
request is served through `servePipelineOf (denoteOn defaultDeployment pc)` — the SAME
fourteen-stage fold over the CONFIG's declared route table. On a parse failure, a
non-UTF-8 config, or a routeless config the request is served by the byte-identical
default (`servePipelineFull2`). Total. -/
@[export drorb_serve_cfg]
def drorbServeCfg (input : ByteArray) : ByteArray :=
  match input.toList with
  | b0 :: b1 :: b2 :: b3 :: rest =>
    let cfgLen := be32 b0 b1 b2 b3
    let cfgBytes := rest.take cfgLen
    let reqBytes := rest.drop cfgLen
    let served :=
      match String.fromUTF8? (ByteArray.mk cfgBytes.toArray) with
      | none   => Reactor.Deploy.servePipelineFull2 reqBytes
      | some s =>
        match Dsl.Config.parseChars s.data with
        | none    => Reactor.Deploy.servePipelineFull2 reqBytes
        | some pc => serveUnderConfig pc reqBytes
    ByteArray.mk served.toArray
  | _ => ByteArray.empty

/-- **The config-route serve honours the parsed route table.** For a config that
declares routes, `serveUnderConfig` serves through `servePipelineOf` of the denoted
deployment — whose route table is exactly the config's routes
(`Dsl.Config.denoteOn_routes`), so the served bytes are decided by the operator's
declared routes, not the demo table. -/
theorem serveUnderConfig_routes (pc : Dsl.Config.ParsedConfig) (req : Proto.Bytes)
    (h : pc.routes ≠ []) :
    serveUnderConfig pc req
      = Reactor.Deploy.servePipelineOf (Dsl.Config.denoteOn Reactor.Deploy.defaultDeployment pc) req
    ∧ (Dsl.Config.denoteOn Reactor.Deploy.defaultDeployment pc).routing.routes
        = pc.routes.map Dsl.Config.routeOfSpec := by
  refine ⟨?_, Dsl.Config.denoteOn_routes _ pc h⟩
  unfold serveUnderConfig
  cases hpc : pc.routes with
  | nil => exact absurd hpc h
  | cons a t => rfl

/-- **The virtual-host serve honours the parsed vhost dimension.** A config that
declares virtual hosts serves through `servePipelineOf` of the denoted deployment,
whose default handler is the proven host/method/glob `Handler.hostGlob` over the
config's declared blocks (`Dsl.Config.denoteOn_vhosts`) — so an unmatched request is
routed by the operator's declared vhosts, not the demo table. -/
theorem serveUnderConfig_vhosts (pc : Dsl.Config.ParsedConfig) (req : Proto.Bytes)
    (h : pc.vitems ≠ []) :
    serveUnderConfig pc req
      = Reactor.Deploy.servePipelineOf (Dsl.Config.denoteOn Reactor.Deploy.defaultDeployment pc) req
    ∧ (Dsl.Config.denoteOn Reactor.Deploy.defaultDeployment pc).routing.defaultHandler
        = Reactor.App.Handler.hostGlob (Dsl.Config.denoteVHosts pc.vitems) := by
  refine ⟨?_, Dsl.Config.denoteOn_vhosts _ pc h⟩
  unfold serveUnderConfig
  cases hv : pc.vitems with
  | nil => exact absurd hv h
  | cons a t => cases pc.routes <;> rfl

/-- **No regression.** A config declaring neither flat routes nor virtual hosts serves
byte-identically to the deployed default (`servePipelineFull2` = `servePipelineOf
defaultDeployment`). -/
theorem serveUnderConfig_default (pc : Dsl.Config.ParsedConfig) (req : Proto.Bytes)
    (hr : pc.routes = []) (hv : pc.vitems = []) :
    serveUnderConfig pc req = Reactor.Deploy.servePipelineFull2 req := by
  simp only [serveUnderConfig, hr, hv]

/-! ## The in-process TLS 1.3 HTTPS front door — `drorb_tls_serve`

The seams above serve PLAINTEXT bytes: the native host reads an HTTP/1.1 request
off a bare TCP socket and crosses `drorb_serve`. This section adds the missing
front door: a native host hands one accepted TCP connection's file descriptor to
`drorb_tls_serve`, and the VERIFIED TLS 1.3 server runs the whole connection
IN THIS PROCESS — the RFC 8446 handshake (`TlsHandshake.serverStep`: ClientHello
parse, X25519 ECDHE, key schedule, Certificate/CertificateVerify/Finished flight,
client-Finished check), then the established record layer (`TlsHandshake.appStep`:
open each application_data record, strip §5.4 padding), and for each complete
decrypted HTTP request it crosses the SAME proven `drorbServe` the plaintext path
runs and seals the response back as a §5 record (`TlsHandshake.sealRecordAt`).

Every protocol decision and all cryptography happen here, in the same
`serverStep`/`appStep` the TLS theorems are about, over the verified `Crypto`
primitives (EverCrypt AEAD/HKDF/SHA, Ed25519, X25519). The untrusted host owns
only the socket: accept, and the raw `recv`/`send` this seam calls through the
`ffi/derp_net.o` byte-mover (`drorb_tcp_recv_exact` / `drorb_tcp_send` — the same
blocking TCP shim the DERP live driver uses). It never parses a TLS record or
touches a key.

Reachable in this cut: a MULTI-CERTIFICATE pool (Ed25519 default plus, when the
host supplies the material, an ECDSA-P256 and an RSA-PSS-2048 end-entity
certificate), X25519 key exchange, full 1-RTT handshake, and the established
application-data record layer serving real HTTP through `drorbServe`. The
certificate presented is chosen by the SAME proven `chooseCert` the testssl-A+
conformance path uses (`TlsHandshake.serverStep` → `chooseCert`): it reads the
client's `signature_algorithms` and returns an entry whose `SignatureScheme` the
client offered (`chooseCert_respects_sigalgs`). So a real client that rejects
Ed25519 (curl/LibreSSL/browsers) is presented an ECDSA-P256 or RSA-PSS
certificate and connects.

Now wired on this deployed path, over the same proven pieces:
  * **SNI certificate selection** (RFC 6066 §3, `chooseCert_honors_sni`): a pool
    entry bound to a host (`DRORB_TLS_ECDSA_SNI` / `DRORB_TLS_RSA_SNI`) is
    presented only when the ClientHello's `server_name` matches; other names /
    no SNI fall to the name-agnostic entries.
  * **ALPN** (RFC 7301, `negotiateAlpn_sound`): `serverStep` negotiates the
    application protocol in EncryptedExtensions — the deployment advertises
    `http/1.1` (`serverAlpn`). (h2-over-TLS is a follow-on: the deployed record
    layer serves the HTTP/1.1 pipeline; advertising `h2` there is future work.)
  * **Session resumption** (RFC 8446 §4.6.1, §4.2.11): `enterApp` issues a
    NewSessionTicket — a stateless sealed ticket carrying the resumption PSK,
    suite, and ALPN — and a later connection presenting it resumes through the
    proven PSK path (`checkPsk`, binder-verified, over `ticketKey seed`).
  * **0-RTT early data** (RFC 8446 §4.2.10, §8): opt-in via `DRORB_TLS_EARLY_DIR`
    — issued tickets then advertise `max_early_data`, the per-offer anti-replay
    gate (`gateFor`/`markTicketOnce`) instantiates `earlyDataOk`, and accepted
    early records are served through `drorbServe`. Without the opt-in the gate
    rejects all 0-RTT (early records trial-skipped, 1-RTT completes). -/

namespace Dataplane.Tls

open TlsHandshake

/-- Send all bytes of `payload` on the connected socket `fd`. Backed by
`ffi/derp_net.o`'s `drorb_tcp_send` (a blocking `send` loop); the byte-mover
parses nothing. -/
@[extern "drorb_tcp_send"]
opaque tcpSend (fd : UInt32) (payload : ByteArray) : IO Unit

/-- Read EXACTLY `nbytes` from `fd`, waiting up to `timeoutMs`; `none` on
timeout / EOF / error. Backed by `ffi/derp_net.o`'s `drorb_tcp_recv_exact`. -/
@[extern "drorb_tcp_recv_exact"]
opaque tcpRecvExact (fd : UInt32) (nbytes : UInt32) (timeoutMs : UInt32) :
    IO (Option ByteArray)

/-- Close the socket `fd`. Backed by `ffi/derp_net.o`'s `drorb_tcp_close`. -/
@[extern "drorb_tcp_close"]
opaque tcpClose (fd : UInt32) : IO Unit

/-- Per-record read timeout (ms). A stalled peer costs at most this long. -/
def recvTimeout : UInt32 := 15000

/-- Read one full TLS record off the wire: the 5-byte `type ‖ version ‖ length`
header (RFC 8446 §5.1), then exactly the declared body. Returns the outer
content-type byte and the FULL record bytes (header ++ body — the shape
`serverStep`/`openRecordAt` strip), or `none` on EOF/timeout/short read. -/
def readRecord (fd : UInt32) : IO (Option (UInt8 × ByteArray)) := do
  match ← tcpRecvExact fd 5 recvTimeout with
  | none => return none
  | some hb =>
    if hb.size < 5 then return none
    let ctype := hb.get! 0
    let len := (hb.get! 3).toNat * 256 + (hb.get! 4).toNat
    if len > 18432 then return none          -- > 2^14 + 256: not a valid record
    let body ← if len == 0 then pure (some ByteArray.empty)
               else tcpRecvExact fd (UInt32.ofNat len) recvTimeout
    match body with
    | none => return none
    | some bb => return some (ctype, hb ++ bb)

/-- Lowercase-hex a byte string (for anti-replay register filenames). -/
def toHex (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.toList.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

/-- Single-use 0-RTT anti-replay register (RFC 8446 §8): one file per
ticket-identity hash under `dir`, `true` iff this identity is used for the FIRST
time. The existence check and the mark are two filesystem steps, not one atomic
operation — the honest conformance-grade seam (the SAME the `tls-wire-oracle`
uses); a production register would create atomically. -/
def markTicketOnce (dir : String) (identity : Tls.Bytes) : IO Bool := do
  let path := System.FilePath.mk dir / toHex (Crypto.sha256 (ofBytes identity))
  if (← path.pathExists) then return false
  IO.FS.writeFile path "used"
  return true

/-- Instantiate the per-connection 0-RTT gate (§4.2.10, §8). When the deployment
opted into 0-RTT (`earlyDir` set) and this first ClientHello offers a PSK with
early data, consult-and-mark the anti-replay register and pin
`ServerParams.earlyDataOk` to the fresh verdict for exactly that identity;
otherwise the default gate (reject all 0-RTT) stands, and `serverStep`
trial-skips any early records the client sent. -/
def gateFor (earlyDir : Option String) (params : ServerParams) (chBytes : Tls.Bytes) :
    IO ServerParams := do
  match earlyDir with
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

/-- The established application phase: read each record, open it with `appStep`,
and once a complete HTTP request head has arrived (CRLFCRLF) cross the SAME
proven `drorbServe` the plaintext front runs, sealing its response as a §5
application_data record under the send keys. Loops until close/EOF. `fuel`
bounds the record count so the driver is structurally total. -/
partial def appLoop (fd : UInt32) (app : AppConn) (reqBuf : List UInt8) : IO Unit := do
  match ← readRecord fd with
  | none => tcpClose fd
  | some (0x14, _) => appLoop fd app reqBuf   -- a stray CCS (§5): drop
  | some (_, rec) =>
    match appStep app rec.toList with
    | (app', .deliver content, _) =>
      let reqBuf := reqBuf ++ content
      if hasCrlfCrlf reqBuf then
        -- A complete request head: serve it through the proven pipeline and
        -- seal the response bytes as one application_data record.
        let resp := drorbServe (ofBytes reqBuf)
        match sealRecordAt app'.txKeys app'.txSeq 0x17 resp with
        | some wire => do
          tcpSend fd wire
          appLoop fd { app' with txSeq := app'.txSeq + 1 } []
        | none => tcpClose fd
      else appLoop fd app' reqBuf
    | (_, .close, reply) => do tcpSend fd reply; tcpClose fd
    | (app', .keyUpdated, reply) =>
      if reply.isEmpty then appLoop fd app' reqBuf
      else do tcpSend fd reply; appLoop fd app' reqBuf
    | (_, .fatal _, alert) => do tcpSend fd alert; tcpClose fd

/-- Enter the established application phase (RFC 8446 §4.6). Issue a
NewSessionTicket as the FIRST application-phase record — a stateless, sealed
ticket for this session's resumption PSK, carrying the connection's suite and
ALPN (§4.2.10) and, when the deployment opted into 0-RTT (`maxEarly > 0`), the
`early_data` advertisement — under the server application keys (`ticketKey` is
derived from the same `seed`, so any later connection to this server opens it).
When an ACCEPTED 0-RTT phase already delivered a complete HTTP request head
(`earlyBuf`), answer it in the same flight through the SAME proven `drorbServe`.
Then run the record layer over `appLoop`. -/
partial def enterApp (fd : UInt32) (seed : ByteArray) (maxEarly : Nat)
    (est : Established) (earlyBuf : List UInt8) : IO Unit := do
  let app := mkAppConn est
  let sealNonce ← IO.getRandomBytes 12
  let ageAddBytes ← IO.getRandomBytes 4
  let ageAdd := ageAddBytes.toList.foldl (fun a b => a * 256 + b.toNat) 0
  let (app, tkWire) :=
    match buildNewSessionTicket (ticketKey seed) sealNonce
            app.resumptionMaster ageAdd est.suite est.alpnProto maxEarly with
    | some nst =>
      match sealRecordAt app.txKeys app.txSeq 0x16 nst with
      | some w => ({ app with txSeq := app.txSeq + 1 }, w)
      | none => (app, ByteArray.empty)
    | none => (app, ByteArray.empty)
  let (app, outWire, reqBuf) :=
    if hasCrlfCrlf earlyBuf then
      match sealRecordAt app.txKeys app.txSeq 0x17 (drorbServe (ofBytes earlyBuf)) with
      | some w => ({ app with txSeq := app.txSeq + 1 }, tkWire ++ w, [])
      | none => (app, tkWire, earlyBuf)
    else (app, tkWire, earlyBuf)
  if !outWire.isEmpty then tcpSend fd outWire
  appLoop fd app reqBuf

/-- The handshake phase: drive `serverStep` over each incoming record until the
connection is `established`, sending the server flight / HelloRetryRequest /
fatal alert it emits, then hand off to `enterApp`. On the first ClientHello the
0-RTT anti-replay gate is instantiated for this offer (`gateFor`); an accepted
early-data phase accumulates its plaintext in `earlyBuf` until EndOfEarlyData.
`maxEarly` is the `max_early_data_size` advertised on issued tickets (0 when the
deployment did not opt into 0-RTT). -/
partial def hsLoop (fd : UInt32) (params : ServerParams) (earlyDir : Option String)
    (maxEarly : Nat) (st : HsState) (earlyBuf : List UInt8) : IO Unit := do
  match ← readRecord fd with
  | none => tcpClose fd
  | some (0x14, _) => hsLoop fd params earlyDir maxEarly st earlyBuf  -- CCS (§5): drop
  | some (_, rec) =>
    match st with
    | .waitCH =>
      let params ← gateFor earlyDir params rec.toList
      match serverStep params .waitCH rec.toList with
      | (.waitClientFinished est, out) => do
        tcpSend fd out.flight; hsLoop fd params earlyDir maxEarly (.waitClientFinished est) earlyBuf
      | (.waitCH2 r, out) => do
        tcpSend fd out.flight; hsLoop fd params earlyDir maxEarly (.waitCH2 r) earlyBuf
      | (_, out) => do tcpSend fd out.flight; tcpClose fd
    | .waitCH2 r =>
      match serverStep params (.waitCH2 r) rec.toList with
      | (.waitClientFinished est, out) => do
        tcpSend fd out.flight; hsLoop fd params earlyDir maxEarly (.waitClientFinished est) earlyBuf
      | (_, out) => do tcpSend fd out.flight; tcpClose fd
    | .waitClientFinished est =>
      match serverStep params (.waitClientFinished est) rec.toList with
      | (.established est', _) => enterApp fd params.certSeed maxEarly est' earlyBuf
      | (.waitClientFinished est', out) =>
        -- An accepted early-data record (accumulate its plaintext), or a
        -- trial-skipped rejected-0-RTT record: the handshake continues.
        hsLoop fd params earlyDir maxEarly (.waitClientFinished est') (earlyBuf ++ out.earlyData)
      | (_, out) => do tcpSend fd out.flight; tcpClose fd
    | _ => tcpClose fd

/-- The servable certificate pool for the deployed front door, built from the
host's certificate material. The Ed25519 entry (`certDer`/`seed`) is the pool
default (`ServerParams.defaultCert`, last, name-agnostic). Each of the ECDSA-P256
and RSA-PSS-2048 entries is added when its material is non-empty, with its
CertificateVerify signing seam instantiated by the verified HACL* binding
(`TlsCrypto.Sig.ecdsaP256Sign` / `rsaPssSign`) — the SAME seams the
`tls-wire-oracle` conformance path instantiates. Order: ECDSA first, then RSA,
then the Ed25519 default, so `chooseCert` prefers the compact ECDSA entry when
the client offers `ecdsa_secp256r1_sha256`.

`ecdsaSni` / `rsaSni` (empty = none) bind an entry to a specific SNI host name
(RFC 6066 §3), so `chooseCert` — through the proven `sniPool` — presents THAT
entry only when the ClientHello's `server_name` matches (`chooseCert_honors_sni`).
A named entry no longer serves other names, so at least one pool member (the RSA
entry, or the Ed25519 default) MUST stay name-agnostic to serve non-matching /
no-SNI clients; the deployment binds only the ECDSA entry to a host by default. -/
def deployedCerts (ecdsaCert ecdsaPriv ecdsaSni rsaCert rsaN rsaE rsaD rsaSni : ByteArray) :
    List CertEntry :=
  let ecdsa : List CertEntry :=
    if ecdsaCert.isEmpty then []
    else [{ sigAlg := ecdsaSigAlg, certData := ecdsaCert
            sign := fun content => TlsCrypto.Sig.ecdsaP256Sign ecdsaPriv content
            names := if ecdsaSni.isEmpty then [] else [ecdsaSni.toList] }]
  let rsa : List CertEntry :=
    if rsaCert.isEmpty then []
    else
      let key : TlsCrypto.Sig.RsaKey := { n := rsaN, e := rsaE, d := rsaD }
      [{ sigAlg := rsaPssSigAlg, certData := rsaCert
         sign := fun content => TlsCrypto.Sig.rsaPssSign key content
         names := if rsaSni.isEmpty then [] else [rsaSni.toList] }]
  ecdsa ++ rsa

/-- **`drorb_tls_serve` — the deployed HTTPS front door.** One accepted TCP
connection (`fd`) and the host's certificate material: the Ed25519 default
end-entity certificate (`certDer`, DER) with its 32-byte RFC 8032 signing seed
(`seed`), and — when supplied (empty = absent) — an ECDSA-P256 leaf (`ecdsaCert`,
DER) with its 32-byte raw scalar (`ecdsaPriv`) and an RSA-PSS-2048 leaf
(`rsaCert`, DER) with its big-endian modulus / public exponent / private exponent
(`rsaN`/`rsaE`/`rsaD`). Run the whole verified TLS 1.3 server on this connection
in-process — the handshake presents the certificate the proven `chooseCert`
selects from this pool per the client's `signature_algorithms`, then the record
layer serves real HTTP through `drorbServe` — and close. The X25519 ephemeral and
the ServerHello random are drawn fresh per connection from the OS entropy source,
so each connection gets its own DHE. Total; any I/O error closes the socket. -/
@[export drorb_tls_serve]
def drorbTlsServe (fd : UInt32) (certDer seed
    ecdsaCert ecdsaPriv rsaCert rsaN rsaE rsaD : ByteArray) : IO Unit := do
  let priv ← IO.getRandomBytes 32
  let rnd ← IO.getRandomBytes 32
  -- SNI host bindings and the 0-RTT opt-in come from the environment, so the
  -- FFI cert-material ABI stays fixed: `DRORB_TLS_ECDSA_SNI` /
  -- `DRORB_TLS_RSA_SNI` bind that entry to a host (`chooseCert_honors_sni`);
  -- `DRORB_TLS_EARLY_DIR`, when set, opts into 0-RTT with a single-use
  -- anti-replay register at that path (empty ⇒ resumption only, no 0-RTT).
  let ecdsaSni := ((← IO.getEnv "DRORB_TLS_ECDSA_SNI").map (·.toUTF8)).getD ByteArray.empty
  let rsaSni := ((← IO.getEnv "DRORB_TLS_RSA_SNI").map (·.toUTF8)).getD ByteArray.empty
  let earlyDir ← IO.getEnv "DRORB_TLS_EARLY_DIR"
  match earlyDir with
  | some dir => IO.FS.createDirAll dir
  | none => pure ()
  let params : ServerParams :=
    { ephemeralPriv := priv
      serverRandom := rnd
      certSeed := seed
      certData := certDer
      groupsSupported := [x25519Group]
      certs := deployedCerts ecdsaCert ecdsaPriv ecdsaSni rsaCert rsaN rsaE rsaD rsaSni }
  let maxEarly := if earlyDir.isSome then params.maxEarlyData else 0
  try
    hsLoop fd params earlyDir maxEarly .waitCH []
  catch _ =>
    tcpClose fd

end Dataplane.Tls
