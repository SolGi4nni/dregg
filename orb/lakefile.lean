import Lake
open Lake DSL

require «dregg-serve-spec» from "../dregg-serve-spec"

/-- Per-OS link args for the FFI/crypto-linking executables.
    macOS: keep the data segment writable with `-Wl,-no_data_const` (ld64/__DATA_CONST
    workaround; rejected by GNU/lld on Linux, so dropped there).
    Linux: supply the glibc>=2.38 C23 symbols (__isoc23_sscanf/__isoc23_strtol) that
    aws-lc in libaes_fallback.a references but the Lean toolchain glibc lacks, via the
    ABI-identical aliases in ffi/glibc_isoc23_compat.o, inserted before that archive.
    HACL/EverCrypt (-levercrypt) is resolved via LIBRARY_PATH (=$HACL_DIST, the project
    convention) rather than a hard-coded -L path, so it is machine-independent. -/
def osLink (coreIn : Array String) : Array String :=
  -- Every standalone Lean serve exe that links the crypto shim needs the
  -- post-quantum seam symbols (drorb_pq_ml_dsa_verify / drorb_pq_ml_kem_*),
  -- which the pure-Lean exes cannot get from the dregg-pq Rust crate (a
  -- dataplane-only path-dep). ffi/pq_stub.o gives fail-closed definitions so
  -- the link is total; the deployed dataplane binary links the REAL dregg wire.
  let core := #["ffi/pq_stub.o"] ++ coreIn
  if System.Platform.isOSX then
    #["-Wl,-no_data_const"] ++ core
  else
    core.foldl (init := #[]) fun acc a =>
      if a == "target/release/libaes_fallback.a" then
        (acc.push "ffi/glibc_isoc23_compat.o").push a
      else acc.push a

package drorb where
  version := v!"0.1.0"
  -- Heartbeat headroom: several `Reactor.Deploy` braid proofs (braided8_off_eq /
  -- servePipelineBraided8_off_eq &c.) elaborate large composed terms that exceed the
  -- default 200000-heartbeat cap from scratch. Raise the package-wide cap so the tree
  -- builds from scratch. (A cap, not a target — modules that finish sooner are unaffected.)
  leanOptions := #[⟨`maxHeartbeats, .ofNat 4000000⟩]

-- Hygiene: the axiom-footprint / vacuity assertions that CAN fail a build
-- (`#assert_axioms`, `#assert_axioms_exact`, `#assert_nonvacuous`) plus their
-- self-test, which demonstrates each assertion CATCHING a violation.

/-! ## Verified libraries — DIRECTORY GLOBS (a bare `lake build` reaches the whole tree)

Every module under a source directory below is a `@[default_target]`, so the
from-scratch `lake build` that `scripts/ci.sh` runs typechecks ALL of it.

Why this shape: Lake defaults `globs := roots.map Glob.one`. The previous lakefile
had 206 stanzas of the form

    @[default_target] lean_lib Foo where
      srcDir := "."
      roots := #[`Some.Module]

so `lean_lib Reactor` compiled ONLY `Reactor.lean` — never `Reactor/**` — and a
module was gated only if someone remembered to write a stanza for it. The result
was 33 modules with no Lake target at all and 102 modules the full CI gate never
typechecked. Directory globs make gating the DEFAULT: drop a file under any
directory below and it is gated. Only a NEW top-level `Foo.lean` needs an entry
(in `DrorbRoot`).

`Glob.andSubmodules X` = the `X.lean` facade plus everything under `X/`;
`Glob.submodules X` = everything under `X/` for the directories with no facade.
-/

@[default_target] lean_lib Acme where globs := #[Glob.andSubmodules `Acme]
@[default_target] lean_lib Admin where globs := #[Glob.andSubmodules `Admin]
@[default_target] lean_lib Arena where globs := #[Glob.andSubmodules `Arena]
@[default_target] lean_lib Body where globs := #[Glob.andSubmodules `Body]
@[default_target] lean_lib Cache where globs := #[Glob.andSubmodules `Cache]
@[default_target] lean_lib Captp where globs := #[Glob.andSubmodules `Captp]
@[default_target] lean_lib Cgi where globs := #[Glob.andSubmodules `Cgi]
@[default_target] lean_lib Client where globs := #[Glob.submodules `Client]
@[default_target] lean_lib Control where globs := #[Glob.andSubmodules `Control]
@[default_target] lean_lib Crypto where globs := #[Glob.andSubmodules `Crypto]
@[default_target] lean_lib Ct where globs := #[Glob.andSubmodules `Ct]
@[default_target] lean_lib Datapath where globs := #[Glob.andSubmodules `Datapath]
-- (`Dataplane` is also the archive target: `ffi/build-dataplane-lib.sh` runs
--  `lake build Dataplane:static` and archives THIS library's objects. Its member
--  set must stay exactly `Dataplane` + `Dataplane.Multi`, which is what this glob
--  yields — `Dataplane/` contains only `Multi.lean`.)
@[default_target] lean_lib Dataplane where globs := #[Glob.andSubmodules `Dataplane]
@[default_target] lean_lib Derp where globs := #[Glob.andSubmodules `Derp]
@[default_target] lean_lib Dns where globs := #[Glob.andSubmodules `Dns]
@[default_target] lean_lib DownloadMgr where globs := #[Glob.andSubmodules `DownloadMgr]
@[default_target] lean_lib Drain where globs := #[Glob.andSubmodules `Drain]
@[default_target] lean_lib Dsl where globs := #[Glob.andSubmodules `Dsl]
@[default_target] lean_lib EarlyHints where globs := #[Glob.andSubmodules `EarlyHints]
@[default_target] lean_lib Fallback where globs := #[Glob.andSubmodules `Fallback]
@[default_target] lean_lib Flow where globs := #[Glob.andSubmodules `Flow]
@[default_target] lean_lib H2 where globs := #[Glob.andSubmodules `H2]
@[default_target] lean_lib H3 where globs := #[Glob.andSubmodules `H3]
@[default_target] lean_lib Har where globs := #[Glob.andSubmodules `Har]
@[default_target] lean_lib Header where globs := #[Glob.andSubmodules `Header]
@[default_target] lean_lib HtmlRewrite where globs := #[Glob.andSubmodules `HtmlRewrite]
@[default_target] lean_lib Hygiene where globs := #[Glob.andSubmodules `Hygiene]
@[default_target] lean_lib Iocore where globs := #[Glob.andSubmodules `Iocore]
@[default_target] lean_lib Isolation where globs := #[Glob.andSubmodules `Isolation]
@[default_target] lean_lib L4 where globs := #[Glob.submodules `L4]
@[default_target] lean_lib Mesh where globs := #[Glob.submodules `Mesh]
@[default_target] lean_lib Metrics where globs := #[Glob.andSubmodules `Metrics]
@[default_target] lean_lib Mtls where globs := #[Glob.andSubmodules `Mtls]
@[default_target] lean_lib Mux where globs := #[Glob.andSubmodules `Mux]
@[default_target] lean_lib O11y where globs := #[Glob.andSubmodules `O11y]
@[default_target] lean_lib Pki where globs := #[Glob.submodules `Pki]
@[default_target] lean_lib Policy where globs := #[Glob.andSubmodules `Policy]
@[default_target] lean_lib Pool where globs := #[Glob.andSubmodules `Pool]
@[default_target] lean_lib Proto where globs := #[Glob.andSubmodules `Proto]
@[default_target] lean_lib Proxy where globs := #[Glob.andSubmodules `Proxy]
@[default_target] lean_lib Quic where globs := #[Glob.andSubmodules `Quic]
@[default_target] lean_lib Range where globs := #[Glob.submodules `Range]
@[default_target] lean_lib Rate where globs := #[Glob.andSubmodules `Rate]
@[default_target] lean_lib Reactor where globs := #[Glob.andSubmodules `Reactor]
@[default_target] lean_lib Resume where globs := #[Glob.andSubmodules `Resume]
@[default_target] lean_lib Route where globs := #[Glob.andSubmodules `Route]
@[default_target] lean_lib Safety where globs := #[Glob.andSubmodules `Safety]
@[default_target] lean_lib Slab where globs := #[Glob.andSubmodules `Slab]
@[default_target] lean_lib Socks where globs := #[Glob.andSubmodules `Socks]
@[default_target] lean_lib Sse where globs := #[Glob.andSubmodules `Sse]
@[default_target] lean_lib StickTable where globs := #[Glob.andSubmodules `StickTable]
@[default_target] lean_lib Sticky where globs := #[Glob.andSubmodules `Sticky]
@[default_target] lean_lib Tap where globs := #[Glob.andSubmodules `Tap]
@[default_target] lean_lib Tls where globs := #[Glob.andSubmodules `Tls]
@[default_target] lean_lib TlsCrypto where globs := #[Glob.andSubmodules `TlsCrypto]
@[default_target] lean_lib TlsHandshake where globs := #[Glob.andSubmodules `TlsHandshake]
@[default_target] lean_lib Trace where globs := #[Glob.andSubmodules `Trace]
@[default_target] lean_lib Turn where globs := #[Glob.andSubmodules `Turn]
@[default_target] lean_lib Udp where globs := #[Glob.andSubmodules `Udp]
@[default_target] lean_lib Uring where globs := #[Glob.andSubmodules `Uring]
@[default_target] lean_lib Util where globs := #[Glob.submodules `Util]
@[default_target] lean_lib Wireguard where globs := #[Glob.andSubmodules `Wireguard]
@[default_target] lean_lib Ws where globs := #[Glob.andSubmodules `Ws]

-- Top-level modules that are not the facade of a source directory. This is the one
-- list that still needs hand-maintenance; every other module is globbed in above.
@[default_target] lean_lib DrorbRoot where
  globs := #[
    Glob.one `AccessControlProxy,
    Glob.one `AcmeAccountTool,
    Glob.one `AcmeCorrect,
    Glob.one `AcmeIssue,
    Glob.one `AcmeLive,
    Glob.one `AcmeOrderLive,
    Glob.one `ArenaSound,
    Glob.one `BasicAuth,
    Glob.one `BasicAuthCorrect,
    Glob.one `BodyClCorrect,
    Glob.one `CacheCoalesceCorrect,
    Glob.one `CacheDiskLive,
    Glob.one `CacheFreshCorrect,
    Glob.one `CgiCorrect,
    Glob.one `ChunkedCorrect,
    Glob.one `ControlLive,
    Glob.one `Cors,
    Glob.one `CorsCorrect,
    Glob.one `CorsDeployedCorrect,
    Glob.one `CtInclusionCorrect,
    Glob.one `CtLive,
    Glob.one `DateConditionCorrect,
    Glob.one `Dcep,
    Glob.one `Deflate,
    Glob.one `DerpLive,
    Glob.one `DerpMeshLive,
    Glob.one `DerpRelayLive,
    Glob.one `Disco,
    Glob.one `DiscoLive,
    Glob.one `DiscoMeshLive,
    Glob.one `DnsMessageCorrect,
    Glob.one `DnsNameCorrect,
    Glob.one `DnsRecordsLive,
    Glob.one `DnsResolveLive,
    Glob.one `DohLive,
    Glob.one `DrainCorrect,
    Glob.one `DrorbCtl,
    Glob.one `EarlyHintsCorrect,
    Glob.one `FabricLive,
    Glob.one `FlowTokenCorrect,
    Glob.one `ForwardProxy,
    Glob.one `ForwardProxyCorrect,
    Glob.one `Gzip,
    Glob.one `H2EngineLive,
    Glob.one `H2FlowCorrect,
    Glob.one `H2Sound,
    Glob.one `H2StreamCorrect,
    Glob.one `H3FrameCorrect,
    Glob.one `HarCorrect,
    Glob.one `HeaderHopCorrect,
    Glob.one `HeaderSound,
    Glob.one `HpackDynCorrect,
    Glob.one `HtmlRewriteCorrect,
    Glob.one `HuffmanCorrect,
    Glob.one `Ice,
    Glob.one `IoLinux,
    Glob.one `IoMac,
    Glob.one `IoMacMulti,
    Glob.one `IoQuic,
    Glob.one `IoSel4,
    Glob.one `IoWin,
    Glob.one `IpFilter,
    Glob.one `IpFilterCorrect,
    Glob.one `IpFilterDeployedProven,
    Glob.one `IsolationCorrect,
    Glob.one `Jwt,
    Glob.one `JwtValidCorrect,
    Glob.one `MetricsCorrect,
    Glob.one `Middleware,
    Glob.one `MtlsHybridCorrect,
    Glob.one `MtlsVerifyCorrect,
    Glob.one `MuxPriorityCorrect,
    Glob.one `NetmapLive,
    Glob.one `NotAcceptableCorrect,
    Glob.one `PbkdfHashTool,
    Glob.one `PreAuthMintTool,
    Glob.one `ProxyBreakerCorrect,
    Glob.one `ProxyConnectTunnel,
    Glob.one `ProxyHealthCorrect,
    Glob.one `ProxyLbLive,
    Glob.one `ProxyTimeoutCorrect,
    Glob.one `QpackDynCorrect,
    Glob.one `QpackSound,
    Glob.one `QuicHeaderProt,
    Glob.one `QuicReplayCorrect,
    Glob.one `QuicServer,
    Glob.one `QuicTransport,
    Glob.one `RangeUnveilCorrect,
    Glob.one `ReactorStepCorrect,
    Glob.one `Redirect,
    Glob.one `RedirectCorrect,
    Glob.one `ResumeCorrect,
    Glob.one `RouteAdvanced,
    Glob.one `RouteCorrect,
    Glob.one `SecurityHeaders,
    Glob.one `SecurityHeadersCorrect,
    Glob.one `SocksCorrect,
    Glob.one `SseFrameCorrect,
    Glob.one `StaticEtagCorrect,
    Glob.one `StaticFile,
    Glob.one `StaticRangeCorrect,
    Glob.one `StickTableLive,
    Glob.one `StickyCorrect,
    Glob.one `Stun,
    Glob.one `StunLive,
    Glob.one `StunTailscaleKat,
    Glob.one `TapNoLeakCorrect,
    Glob.one `TlsAuthDemo,
    Glob.one `TlsClient,
    Glob.one `TlsFsmCorrect,
    Glob.one `TraceW3cCorrect,
    Glob.one `TurnLive,
    Glob.one `TurnPermLive,
    Glob.one `WebrtcLive,
    Glob.one `WebrtcTransport,
    Glob.one `WgLive,
    Glob.one `WgResponder,
    Glob.one `WsCloseCorrect,
    Glob.one `WsFrameCorrect,
    Glob.one `WsFrameLive
    -- NOTE: never list a module that is not IN THE REPOSITORY. `ZH2AxiomCheck`
    -- was listed here because an UNTRACKED scratch file (ZH2AxiomCheck.lean, left
    -- in the hbox worktree on 2026-07-18) happened to be on disk when this list
    -- was enumerated. On a clean checkout Lake aborts job computation with
    -- "no such file or directory", so scripts/ci.sh's from-scratch
    -- `rm -rf .lake/build && lake build` could not run AT ALL. Enumerate this
    -- list from `git ls-files`, never from the working tree.
  ]

-- Conformance-harness Lean sources (lower-case module names under `conformance/`).
@[default_target] lean_lib ConformanceHarness where
  globs := #[
    Glob.one `conformance.dns.DnsCheck,
    Glob.one `conformance.stun.harness,
    Glob.one `conformance.stun.vectors
  ]

/-! ## Executables -/

lean_exe «arena-check» where
  root := `Arena.Check
  moreLinkArgs := osLink #[]

lean_exe «h1-client» where
  root := `Client.Main
  moreLinkArgs := osLink #[]

lean_exe orb where
  root := `Arena.Orb
  moreLinkArgs := osLink #["ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «orb-mac» where
  root := `IoMac
  moreLinkArgs := osLink #["ffi/mac_io.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «crypto-selftest» where
  root := `Crypto.SelfTest
  moreLinkArgs := osLink #["ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «control-ts2021-kat» where
  root := `Control.Ts2021Kat
  moreLinkArgs := osLink #["ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «control-ts2021-record-kat» where
  root := `Control.Ts2021RecordKat
  moreLinkArgs := osLink #["ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «control-ts2021-channel-kat» where
  root := `Control.Ts2021ChannelKat
  moreLinkArgs := osLink #["ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «basicauth-demo» where
  root := `Reactor.BasicAuthDemo
  moreLinkArgs := osLink #["ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «pbkdf2-hash» where
  root := `PbkdfHashTool
  moreLinkArgs := osLink #["ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «preauth-mint» where
  root := `PreAuthMintTool
  moreLinkArgs := osLink #["ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «drorb-ctl» where
  root := `DrorbCtl
  moreLinkArgs := osLink #["ffi/durable.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «orb-linux» where
  root := `IoLinux
  moreLinkArgs := osLink #["ffi/linux_io.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «orb-win» where
  root := `IoWin
  moreLinkArgs := osLink #["ffi/win_io.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «tls-keyschedule-selftest» where
  root := `TlsCrypto.SelfTest
  moreLinkArgs := osLink #["ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «tls-handshake-selftest» where
  root := `TlsHandshake.SelfTest
  moreLinkArgs := osLink #["ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «tls-wire-oracle» where
  root := `TlsHandshake.WireOracle
  moreLinkArgs := osLink #["ffi/cgi_exec.o", "ffi/crypto_shim.o", "ffi/tls_p256_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «orb-mac-multi» where
  root := `IoMacMulti
  moreLinkArgs := osLink #["ffi/mac_io.o", "ffi/mac_udp.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «quic-transport-selftest» where
  root := `QuicTransport
  moreLinkArgs := osLink #["ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «orb-quic» where
  root := `IoQuic
  moreLinkArgs := osLink #["ffi/mac_udp.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «wg-live» where
  root := `WgLive
  moreLinkArgs := osLink #["ffi/wg_udp.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «derp-live» where
  root := `DerpLive
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «derp-relay» where
  root := `DerpRelayLive
  moreLinkArgs := osLink #["ffi/derp_relay_net.o", "ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «wg-responder» where
  root := `WgResponder
  moreLinkArgs := osLink #["ffi/wg_udp.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «disco-live» where
  root := `DiscoLive
  moreLinkArgs := osLink #["ffi/wg_udp.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «stun-live» where
  root := `StunLive
  moreLinkArgs := osLink #["ffi/wg_udp.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «webrtc-live» where
  root := `WebrtcLive
  moreLinkArgs := osLink #["ffi/webrtc_udp.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "ffi/tls_p256_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «fetch-client» where
  root := `Client.FetchMain
  moreLinkArgs := osLink #[]

lean_exe «control-live» where
  root := `ControlLive
  moreLinkArgs := osLink #["ffi/control_net.o", "ffi/derp_net.o", "ffi/durable.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «turn-live» where
  root := `TurnLive
  moreLinkArgs := osLink #["ffi/crypto_shim.o", "ffi/cgi_exec.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «acme-live» where
  root := `AcmeLive
  moreLinkArgs := osLink #["ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «dns-resolve-live» where
  root := `DnsResolveLive
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «derp-mesh» where
  root := `DerpMeshLive
  moreLinkArgs := osLink #["ffi/derp_relay_net.o", "ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «ct-live» where
  root := `CtLive
  moreLinkArgs := osLink #["ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «turn-perm-live» where
  root := `TurnPermLive
  supportInterpreter := true
  moreLinkArgs := osLink #["ffi/crypto_shim.o", "ffi/cgi_exec.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «acme-order-live» where
  root := `AcmeOrderLive
  supportInterpreter := true
  moreLinkArgs := osLink #[]

lean_exe «doh-live» where
  root := `DohLive
  supportInterpreter := true
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «disco-mesh-live» where
  root := `DiscoMeshLive
  supportInterpreter := true
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «netmap-live» where
  root := `NetmapLive
  supportInterpreter := true
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «fabric-live» where
  root := `FabricLive
  supportInterpreter := true
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «h2-engine-live» where
  root := `H2EngineLive
  supportInterpreter := true
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «sticktable-live» where
  root := `StickTableLive
  supportInterpreter := true
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «dns-records-live» where
  root := `DnsRecordsLive
  supportInterpreter := true
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/crypto_shim.o", "ffi/cgi_exec.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «proxy-lb-live» where
  root := `ProxyLbLive
  supportInterpreter := true
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «cache-disk-live» where
  root := `CacheDiskLive
  supportInterpreter := true
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «ws-frame-live» where
  root := `WsFrameLive
  supportInterpreter := true
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «relay-mesh-live» where
  root := `Mesh.RelayMeshLive
  supportInterpreter := true
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

-- NOTE: this lane is PURE / no-crypto and is verified via `lake env lean --run`
-- (no FFI symbol is referenced by the file — it calls zero @[extern] opaques).
-- The moreLinkArgs are the shared-executable link line only (matching netmap-live/
-- fabric-live); they satisfy `lake build`'s linker but are never CALLED at runtime,
-- so the selftest also runs green under the pure interpreter. If a crypto-free
-- link line is preferred, `moreLinkArgs` may be dropped entirely for this exe.
lean_exe «dns-forward-resolve-live» where
  root := `Dns.ForwardResolve
  supportInterpreter := true

lean_exe «hedged-request-live» where
  root := `Proxy.HedgedRequest
  supportInterpreter := true

lean_exe «introspect-live» where
  root := `Admin.IntrospectLive
  supportInterpreter := true
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

-- Verified run path is the pure interpreter (`lake env lean --run Admin/IntrospectLive.lean selftest`);
-- the selftest calls NO crypto FFI. The osLink args only satisfy a compiled link line, mirroring the
-- sibling *Live exes; they are never invoked at runtime.
lean_exe «svcb-live» where
  root := `Dns.SvcbLive
  supportInterpreter := true

lean_exe «peer-discovery-live» where
  root := `Mesh.PeerDiscoveryLive
  supportInterpreter := true

lean_exe «drain-live» where
  root := `Admin.DrainLive
  supportInterpreter := true

lean_exe «mirror-live» where
  root := `Proxy.MirrorLive
  supportInterpreter := true

lean_exe «outlier-live» where
  root := `Proxy.OutlierLive
  supportInterpreter := true
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «channeldata-live» where
  root := `Turn.ChannelDataLive
  supportInterpreter := true

lean_exe «derp-region-live» where
  root := `Mesh.DerpRegionLive
  supportInterpreter := true

lean_exe «key-rotate-live» where
  root := `Mesh.KeyRotateLive
  supportInterpreter := true

lean_exe «weighted-least-req-live» where
  root := `Proxy.WeightedLeastReqLive
  supportInterpreter := true
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «alloc-refresh-live» where
  root := `Turn.AllocRefreshLive
  supportInterpreter := true

lean_exe route_static_serve where
  root := `Route.StaticServe
  supportInterpreter := true

lean_exe «acme-issue» where
  root := `AcmeIssue
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/crypto_shim.o", "ffi/tls_p256_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «acme-account» where
  root := `AcmeAccountTool
  moreLinkArgs := osLink #["ffi/crypto_shim.o", "ffi/tls_p256_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

-- Real-CA authentication gate for the verified TLS client (TlsClient + Pki.ChainBuild).
lean_exe «tls-auth-demo» where
  root := `TlsAuthDemo
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/crypto_shim.o", "ffi/tls_p256_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

