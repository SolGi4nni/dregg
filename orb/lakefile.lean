import Lake
open Lake DSL

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

@[default_target] lean_lib Arena
@[default_target] lean_lib Datapath
@[default_target] lean_lib Refinement where
  srcDir := "."
  roots := #[`Datapath.Refinement]
@[default_target] lean_lib ByteRefine where
  srcDir := "."
  roots := #[`Datapath.ByteRefine]
@[default_target] lean_lib Uring
@[default_target] lean_lib Iocore
@[default_target] lean_lib Proto
@[default_target] lean_lib ProtoClient where
  srcDir := "."
  roots := #[`Proto.Decimal, `Proto.ResponseParse, `Proto.RequestSerialize, `Client.H1]
@[default_target] lean_lib Slab
@[default_target] lean_lib Pool
@[default_target] lean_lib Flow
@[default_target] lean_lib Quic
@[default_target] lean_lib H3
@[default_target] lean_lib Tls
@[default_target] lean_lib Proxy
@[default_target] lean_lib Policy
@[default_target] lean_lib Route
@[default_target] lean_lib H2
@[default_target] lean_lib H2FrameEncode where
  srcDir := "."
  roots := #[`H2.FrameEncode]
@[default_target] lean_lib H2HpackEncode where
  srcDir := "."
  roots := #[`H2.HpackEncode]
@[default_target] lean_lib ClientH2 where
  srcDir := "."
  roots := #[`Client.H2]
@[default_target] lean_lib ClientH2Receive where
  srcDir := "."
  roots := #[`Client.H2Receive]
@[default_target] lean_lib Ext where
  srcDir := "."
  roots := #[`H2.Ext]
@[default_target] lean_lib Ws
@[default_target] lean_lib Dns
@[default_target] lean_lib DnsDoh where
  srcDir := "."
  roots := #[`Dns.Doh]
@[default_target] lean_lib DnsDot where
  srcDir := "."
  roots := #[`Dns.Dot]
@[default_target] lean_lib Rate
@[default_target] lean_lib Captp
@[default_target] lean_lib Safety
@[default_target] lean_lib Drain
@[default_target] lean_lib Admin
@[default_target] lean_lib Body
@[default_target] lean_lib Header
@[default_target] lean_lib Sticky
@[default_target] lean_lib Resume
@[default_target] lean_lib Trace
@[default_target] lean_lib Fallback
@[default_target] lean_lib Mux
@[default_target] lean_lib Sse
@[default_target] lean_lib StickTable
@[default_target] lean_lib Socks
@[default_target] lean_lib Udp
@[default_target] lean_lib Mtls
@[default_target] lean_lib Acme
lean_lib Pki where
  srcDir := "."
  roots := #[`Pki.Acme]
@[default_target] lean_lib PkiCt where
  srcDir := "."
  roots := #[`Pki.Ct]
@[default_target] lean_lib Ct
@[default_target] lean_lib EarlyHints
@[default_target] lean_lib HtmlRewrite
@[default_target] lean_lib Metrics
@[default_target] lean_lib O11y
@[default_target] lean_lib Tap
@[default_target] lean_lib Har
@[default_target] lean_lib DownloadMgr
@[default_target] lean_lib Isolation
@[default_target] lean_lib Dsl
@[default_target] lean_lib Reactor
@[default_target] lean_lib BraidCalculus where
  srcDir := "."
  roots := #[`Reactor.BraidCalculus]
lean_lib BraidCalculusDemo where
  srcDir := "."
  roots := #[`Reactor.BraidCalculusDemo]
lean_lib ReactorStageConnLimit where
  srcDir := "."
  roots := #[`Reactor.Stage.ConnLimit]
lean_lib ReactorStandingCounters where
  srcDir := "."
  roots := #[`Reactor.StandingCounters]
lean_lib ReactorStageSlowloris where
  srcDir := "."
  roots := #[`Reactor.Stage.Slowloris]
lean_lib ReactorStageStickTable where
  srcDir := "."
  roots := #[`Reactor.Stage.StickTable]
lean_lib ReactorStageRequestId where
  srcDir := "."
  roots := #[`Reactor.Stage.RequestId]
lean_lib ReactorStageAuthRequest where
  srcDir := "."
  roots := #[`Reactor.Stage.AuthRequest]
lean_lib ReactorStageErrorPage where
  srcDir := "."
  roots := #[`Reactor.Stage.ErrorPage]
lean_lib ReactorStageCompress where
  srcDir := "."
  roots := #[`Reactor.Stage.Compress]
@[default_target] lean_lib ReactorSerializeFast where
  srcDir := "."
  roots := #[`Reactor.SerializeFast]
@[default_target] lean_lib ServeStream where
  globs := #[Glob.one `Reactor.ServeStream]
@[default_target] lean_lib DriveCache where
  srcDir := "."
  roots := #[`Reactor.DriveCache]
@[default_target] lean_lib DriveProxy where
  srcDir := "."
  roots := #[`Reactor.DriveProxy]
lean_lib Dataplane where
  globs := #[Glob.one `Dataplane, Glob.one `Dataplane.Multi]
@[default_target] lean_lib StaticFile
@[default_target] lean_lib Redirect
@[default_target] lean_lib Cgi
@[default_target] lean_lib Cache
@[default_target] lean_lib CacheDisk where
  srcDir := "."
  roots := #[`Cache.Disk]
@[default_target] lean_lib CacheZones where
  srcDir := "."
  roots := #[`Cache.Zones]
@[default_target] lean_lib Middleware
@[default_target] lean_lib Cors
@[default_target] lean_lib SecurityHeaders
@[default_target] lean_lib IpFilter
@[default_target] lean_lib Jwt
@[default_target] lean_lib BasicAuth
@[default_target] lean_lib Stun
lean_lib Turn
@[default_target] lean_lib Ice
@[default_target] lean_lib Dcep
@[default_target] lean_lib Wireguard
@[default_target] lean_lib Derp
@[default_target] lean_lib DerpRelay where
  srcDir := "."
  roots := #[`Derp.Relay]
@[default_target] lean_lib DerpMesh where
  srcDir := "."
  roots := #[`Derp.Mesh]
@[default_target] lean_lib Disco
@[default_target] lean_lib Control
@[default_target] lean_lib ForwardProxy
@[default_target] lean_lib AccessControlProxy
@[default_target] lean_lib RouteAdvanced
@[default_target] lean_lib WebrtcTransport
lean_lib IoSel4
lean_lib Crypto
lean_lib TlsCrypto
lean_lib TlsHandshake
@[default_target] lean_lib TlsServe where
  roots := #[`Dsl.Cfg.TlsServe]
lean_lib Deflate
lean_lib Gzip
lean_lib WireMore where
  roots := #[`Reactor.WireMore]
lean_lib WsDeployLane where
  roots := #[`Reactor.WsDeploy]
lean_lib ReactorH2Response where
  srcDir := "."
  roots := #[`Reactor.H2Response]
@[default_target] lean_lib ReactorL4 where
  srcDir := "."
  roots := #[`Reactor.L4]
lean_lib ArenaSound where
  srcDir := "."
  roots := #[`ArenaSound]
lean_lib HeaderSound where
  srcDir := "."
  roots := #[`HeaderSound]
lean_lib WireRest where
  srcDir := "."
  roots := #[`Reactor.WireRest]
@[default_target] lean_lib ControlAcl where
  srcDir := "."
  roots := #[`Control.Acl]
@[default_target] lean_lib ControlDistribute where
  srcDir := "."
  roots := #[`Control.Distribute]
@[default_target] lean_lib ControlRegister where
  srcDir := "."
  roots := #[`Control.Register]
@[default_target] lean_lib ControlDns where
  srcDir := "."
  roots := #[`Control.Dns]
@[default_target] lean_lib ControlDerp where
  srcDir := "."
  roots := #[`Control.Derp]
@[default_target] lean_lib ControlRoutes where
  srcDir := "."
  roots := #[`Control.Routes]
@[default_target] lean_lib ControlChannel where
  srcDir := "."
  roots := #[`Control.Channel]
@[default_target] lean_lib H2Sound
@[default_target] lean_lib QpackSound
@[default_target] lean_lib QuicTransport
@[default_target] lean_lib QuicHeaderProt
lean_lib QuicServer
@[default_target] lean_lib RouteCorrect
@[default_target] lean_lib HpackDynCorrect
@[default_target] lean_lib HuffmanCorrect
@[default_target] lean_lib QpackDynCorrect
@[default_target] lean_lib H3Priority where
  srcDir := "."
  roots := #[`H3.Priority]
@[default_target] lean_lib H3QpackEncode where
  srcDir := "."
  roots := #[`H3.QpackEncode]
@[default_target] lean_lib H3Stream where
  srcDir := "."
  roots := #[`H3.Stream]
@[default_target] lean_lib H3Client where
  srcDir := "."
  roots := #[`H3.Client]
@[default_target] lean_lib ClientH3 where
  srcDir := "."
  roots := #[`Client.H3]
@[default_target] lean_lib ClientH3Receive where
  srcDir := "."
  roots := #[`Client.H3Receive]
@[default_target] lean_lib QuicStrike where
  srcDir := "."
  roots := #[`Quic.Strike]
@[default_target] lean_lib ChunkedCorrect
@[default_target] lean_lib ReactorStepCorrect
@[default_target] lean_lib TlsFsmCorrect
@[default_target] lean_lib H2FlowCorrect
@[default_target] lean_lib CacheFreshCorrect
@[default_target] lean_lib StaticRangeCorrect
@[default_target] lean_lib CorsCorrect
@[default_target] lean_lib JwtValidCorrect
@[default_target] lean_lib DnsNameCorrect
@[default_target] lean_lib SseFrameCorrect
@[default_target] lean_lib ProxyHealthCorrect
@[default_target] lean_lib H3FrameCorrect
@[default_target] lean_lib QuicReplayCorrect
@[default_target] lean_lib DrainCorrect
@[default_target] lean_lib WsFrameCorrect
@[default_target] lean_lib MtlsVerifyCorrect
@[default_target] lean_lib MtlsHybridCorrect
@[default_target] lean_lib SocksCorrect
@[default_target] lean_lib H2StreamCorrect
@[default_target] lean_lib BodyClCorrect
@[default_target] lean_lib IpFilterCorrect
@[default_target] lean_lib RedirectCorrect
@[default_target] lean_lib CtInclusionCorrect
@[default_target] lean_lib TraceW3cCorrect
@[default_target] lean_lib MuxPriorityCorrect
@[default_target] lean_lib HeaderHopCorrect
@[default_target] lean_lib StickyCorrect
@[default_target] lean_lib ProxyBreakerCorrect
@[default_target] lean_lib BasicAuthCorrect
@[default_target] lean_lib StaticEtagCorrect
@[default_target] lean_lib CgiCorrect
@[default_target] lean_lib CacheCoalesceCorrect
@[default_target] lean_lib TapNoLeakCorrect
@[default_target] lean_lib WsCloseCorrect
@[default_target] lean_lib ProxyTimeoutCorrect
@[default_target] lean_lib ForwardProxyCorrect
@[default_target] lean_lib IsolationCorrect
@[default_target] lean_lib MetricsCorrect
@[default_target] lean_lib SecurityHeadersCorrect
@[default_target] lean_lib ResumeCorrect
@[default_target] lean_lib FlowTokenCorrect
@[default_target] lean_lib EarlyHintsCorrect
@[default_target] lean_lib HarCorrect
@[default_target] lean_lib AcmeCorrect
@[default_target] lean_lib DnsMessageCorrect
@[default_target] lean_lib HtmlRewriteCorrect
@[default_target] lean_lib ClientTls where
  srcDir := "."
  roots := #[`Client.Tls]
@[default_target] lean_lib Autoindex where
  srcDir := "."
  roots := #[`Reactor.Stage.Autoindex]
@[default_target] lean_lib ReactorStageCompressExt where
  srcDir := "."
  roots := #[`Reactor.Stage.CompressExt]
@[default_target] lean_lib ClientRedirect where
  srcDir := "."
  roots := #[`Client.Redirect]
@[default_target] lean_lib GrpcHealthCorrect where
  srcDir := "."
  roots := #[`Proxy.GrpcHealth]
@[default_target] lean_lib L4Passthrough where
  srcDir := "."
  roots := #[`L4.Passthrough]
@[default_target] lean_lib Deadline where
  srcDir := "."
  roots := #[`Iocore.Deadline]
@[default_target] lean_lib CacheTee where
  srcDir := "."
  roots := #[`Cache.Tee]
@[default_target] lean_lib ClientSession where
  srcDir := "."
  roots := #[`Client.Session]
@[default_target] lean_lib WsClient where
  srcDir := "."
  roots := #[`Ws.Client]
@[default_target] lean_lib ReactorStageVariants where
  srcDir := "."
  roots := #[`Reactor.Stage.Variants]
@[default_target] lean_lib ProxyGrpcWeb where
  srcDir := "."
  roots := #[`Proxy.GrpcWeb]
@[default_target] lean_lib CompletionHandlerCorrect where
  srcDir := "."
  roots := #[`Iocore.CompletionHandler]
@[default_target] lean_lib FastCgi where
  srcDir := "."
  roots := #[`Cgi.FastCgi]
@[default_target] lean_lib Smuggling where
  srcDir := "."
  roots := #[`Body.Smuggling]
@[default_target] lean_lib Framing where
  srcDir := "."
  roots := #[`Body.Framing]
@[default_target] lean_lib FrameRaw where
  srcDir := "."
  roots := #[`Body.FrameRaw]
@[default_target] lean_lib WsDecode where
  srcDir := "."
  roots := #[`Ws.Decode]
@[default_target] lean_lib WsEncode where
  srcDir := "."
  roots := #[`Ws.Encode]
@[default_target] lean_lib H2PseudoHeader where
  srcDir := "."
  roots := #[`H2.PseudoHeader]
@[default_target] lean_lib H3QpackDynEncode where
  srcDir := "."
  roots := #[`H3.QpackDynEncode]
@[default_target] lean_lib WsProxyRelay where
  srcDir := "."
  roots := #[`Ws.ProxyRelay]
@[default_target] lean_lib ReactorStageForwardAuth where
  srcDir := "."
  roots := #[`Reactor.Stage.ForwardAuth]
@[default_target] lean_lib ProxyRetryBudgetCorrect where
  srcDir := "."
  roots := #[`Proxy.RetryBudget]
@[default_target] lean_lib ProxyLeastConn where
  srcDir := "."
  roots := #[`Proxy.LeastConn]
@[default_target] lean_lib ClientCookieExpiry where
  srcDir := "."
  roots := #[`Client.CookieExpiry]
@[default_target] lean_lib IocoreWake where
  srcDir := "."
  roots := #[`Iocore.Wake]
@[default_target] lean_lib ReactorStageCompressBody where
  srcDir := "."
  roots := #[`Reactor.Stage.CompressBody]
@[default_target] lean_lib MtlsChainDepth where
  srcDir := "."
  roots := #[`Mtls.ChainDepth]
@[default_target] lean_lib L4Splice where
  srcDir := "."
  roots := #[`L4.Splice]
@[default_target] lean_lib H3Datagram where
  srcDir := "."
  roots := #[`H3.Datagram]
@[default_target] lean_lib Continue where
  srcDir := "."
  roots := #[`Body.Continue]
@[default_target] lean_lib Http10 where
  srcDir := "."
  roots := #[`Proto.Http10]
@[default_target] lean_lib ReactorStageEarlyHints where
  srcDir := "."
  roots := #[`Reactor.Stage.EarlyHints]
@[default_target] lean_lib H2FlowWindow where
  srcDir := "."
  roots := #[`H2.FlowWindow]
@[default_target] lean_lib H2RespTrailers where
  srcDir := "."
  roots := #[`H2.RespTrailers]
@[default_target] lean_lib ProxyUnixUpstream where
  srcDir := "."
  roots := #[`Proxy.UnixUpstream]
@[default_target] lean_lib CacheConditional where
  srcDir := "."
  roots := #[`Cache.Conditional]
@[default_target] lean_lib DnsSvcb where
  srcDir := "."
  roots := #[`Dns.Svcb]
lean_lib ClientFetch where
  srcDir := "."
  roots := #[`Client.Fetch]
lean_lib ClientFetchExport where
  srcDir := "."
  roots := #[`Client.FetchExport]
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
lean_exe «webrtc-live» where
  root := `WebrtcLive
  moreLinkArgs := osLink #["ffi/webrtc_udp.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "ffi/tls_p256_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]
lean_exe «fetch-client» where
  root := `Client.FetchMain
  moreLinkArgs := osLink #[]

lean_exe «control-live» where
  root := `ControlLive
  moreLinkArgs := osLink #["ffi/control_net.o", "ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «turn-live» where
  root := `TurnLive
  moreLinkArgs := osLink #["ffi/crypto_shim.o", "ffi/cgi_exec.o", "target/release/libaes_fallback.a", "-levercrypt"]

@[default_target] lean_lib AcmeDns01 where
  srcDir := "."
  roots := #[`Acme.Dns01]

@[default_target] lean_lib ProxyConnectTunnel where
  roots := #[`ProxyConnectTunnel]

lean_exe «acme-live» where
  root := `AcmeLive
  moreLinkArgs := osLink #["ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

@[default_target] lean_lib OtelTrace where
  srcDir := "."
  roots := #[`O11y.OtelTrace]

lean_exe «dns-resolve-live» where
  root := `DnsResolveLive
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «derp-mesh» where
  root := `DerpMeshLive
  moreLinkArgs := osLink #["ffi/derp_relay_net.o", "ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

@[default_target] lean_lib ProxyProtocol where
  srcDir := "."
  roots := #[`Proxy.ProxyProtocol]

lean_exe «ct-live» where
  root := `CtLive
  moreLinkArgs := osLink #["ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «turn-perm-live» where
  root := `TurnPermLive
  supportInterpreter := true
  moreLinkArgs := osLink #["ffi/crypto_shim.o", "ffi/cgi_exec.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_lib ReactorStageSpaFallback where
  srcDir := "."
  roots := #[`Reactor.Stage.SpaFallback]

lean_exe «acme-order-live» where
  root := `AcmeOrderLive
  supportInterpreter := true
  moreLinkArgs := osLink #[]

@[default_target] lean_lib RangePartial where
  srcDir := "."
  roots := #[`Range.Partial]

lean_exe «doh-live» where
  root := `DohLive
  supportInterpreter := true
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

@[default_target] lean_lib AccessLog where
  srcDir := "."
  roots := #[`O11y.AccessLog]

@[default_target] lean_lib ProxyRetryReplay where
  srcDir := "."
  roots := #[`Proxy.RetryReplay]

lean_exe «disco-mesh-live» where
  root := `DiscoMeshLive
  supportInterpreter := true
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

@[default_target] lean_lib ProxyConnectMitm where
  roots := #[`Proxy.ConnectMitm]

@[default_target] lean_lib DnsSystemFallback where
  srcDir := "."
  roots := #[`Dns.SystemFallback]

@[default_target] lean_lib GrpcFraming where
  srcDir := "."
  roots := #[`Proxy.GrpcFraming]

lean_exe «netmap-live» where
  root := `NetmapLive
  supportInterpreter := true
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_exe «fabric-live» where
  root := `FabricLive
  supportInterpreter := true
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

lean_lib UdpRelay where
  srcDir := "."
  roots := #[`L4.UdpRelay]

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

@[default_target] lean_lib HealthProbe where
  srcDir := "."
  roots := #[`Admin.HealthProbe]

-- (Alternatively, and cleaner: add `import Admin.HealthProbe` to the shared
--  Admin.lean so the existing `lean_lib Admin` picks it up transitively.
--  I did NOT edit Admin.lean — it is shared. The file is import-free and builds
--  standalone: `lake env lean Admin/HealthProbe.lean` EXIT=0.)

@[default_target] lean_lib ProtoContentLength where
  srcDir := "."
  roots := #[`Proto.ContentLength]

@[default_target] lean_lib PromExposition where
  roots := #[`O11y.PromExposition]

@[default_target] lean_lib ChunkedFraming where
  srcDir := "."
  roots := #[`Proto.ChunkedFraming]

@[default_target] lean_lib AdminMetricsFormat where
  srcDir := "."
  roots := #[`Admin.MetricsFormat]

-- (Alternatively, add `import Admin.MetricsFormat` to the existing Admin.lean
--  root so it rides the existing `lean_lib Admin`; I did NOT edit Admin.lean.)
-- Deps already present as their own libs: `import O11y.Prometheus`, `import Proto.Decimal`.

@[default_target] lean_lib ClientRedirectFollow where
  srcDir := "."
  roots := #[`Client.RedirectFollow]

@[default_target] lean_lib CacheZonePartition where
  srcDir := "."
  roots := #[`Cache.ZonePartition]

@[default_target] lean_lib GrpcBidiStream where
  srcDir := "."
  roots := #[`Proxy.GrpcBidiStream]

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

-- (No moreLinkArgs: this lane is PURE / no-crypto. The exe imports only
-- `Control` (varint codec algebra) and `Proxy.RetryBudget` (pure FSM); it links
-- with no crypto/FFI objects and runs under `lake env lean --run`. Do NOT add
-- the crypto link line — the selftest calls no crypto FFI by design.)

@[default_target] lean_lib PkiCtInclusion where
  srcDir := "."
  roots := #[`Pki.CtInclusion]

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

@[default_target] lean_lib ClientCookieJar where
  srcDir := "."
  roots := #[`Client.CookieJar]

lean_exe «peer-discovery-live» where
  root := `Mesh.PeerDiscoveryLive
  supportInterpreter := true

lean_exe «drain-live» where
  root := `Admin.DrainLive
  supportInterpreter := true

@[default_target] lean_lib PkiChainBuild where
  srcDir := "."
  roots := #[`Pki.ChainBuild]

@[default_target] lean_lib PkiOcsp where
  srcDir := "."
  roots := #[`Pki.OcspResponse]

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

@[default_target] lean_lib CacheStreamTee where
  srcDir := "."
  roots := #[`Cache.StreamTee]

@[default_target] lean_lib L4TProxy where
  srcDir := "."
  roots := #[`L4.TProxy]

@[default_target] lean_lib RouteUrlRewrite where
  srcDir := "."
  roots := #[`Route.UrlRewrite]

@[default_target] lean_lib H2Priority where
  srcDir := "."
  roots := #[`H2.Priority]

@[default_target] lean_lib AccessLogFormat where
  srcDir := "."
  roots := #[`O11y.AccessLogFormat]

@[default_target] lean_lib MetricsCounters where
  roots := #[`O11y.MetricsCounters]

@[default_target] lean_lib WsCloseHandshake where
  roots := #[`Ws.CloseHandshake]

lean_exe «derp-region-live» where
  root := `Mesh.DerpRegionLive
  supportInterpreter := true

@[default_target] lean_lib RouteRegexMatch where
  srcDir := "."
  roots := #[`Route.RegexMatch]

@[default_target] lean_lib CanaryRoute where
  srcDir := "."
  roots := #[`Proxy.CanaryRoute]

lean_exe «key-rotate-live» where
  root := `Mesh.KeyRotateLive
  supportInterpreter := true

@[default_target] lean_lib RouteHostRoute where
  srcDir := "."
  roots := #[`Route.HostRoute]

@[default_target] lean_lib CacheVaryKey where
  srcDir := "."
  roots := #[`Cache.VaryKey]

@[default_target] lean_lib CachePurge where
  roots := #[`Cache.Purge]

@[default_target] lean_lib PkiCtConsistency where
  srcDir := "."
  roots := #[`Pki.CtConsistency]

lean_exe «weighted-least-req-live» where
  root := `Proxy.WeightedLeastReqLive
  supportInterpreter := true
  moreLinkArgs := osLink #["ffi/derp_net.o", "ffi/cgi_exec.o", "ffi/crypto_shim.o", "target/release/libaes_fallback.a", "-levercrypt"]

@[default_target] lean_lib H2RstStream where
  srcDir := "."
  roots := #[`H2.RstStream]
  supportInterpreter := true

@[default_target] lean_lib PkiCrl where
  srcDir := "."
  roots := #[`Pki.Crl]

@[default_target] lean_lib H3QpackDynamic where
  srcDir := "."
  roots := #[`H3.QpackDynamic]

lean_exe «alloc-refresh-live» where
  root := `Turn.AllocRefreshLive
  supportInterpreter := true

lean_exe route_static_serve where
  root := `Route.StaticServe
  supportInterpreter := true

@[default_target] lean_lib EtagProven where
  globs := #[Glob.one `Proto.EtagProven]

@[default_target] lean_lib CompressProven where
  srcDir := "."
  roots := #[`O11y.CompressProven]

@[default_target] lean_lib KeepAliveProven where
  srcDir := "."
  roots := #[`Proto.KeepAliveProven]

@[default_target] lean_lib CacheHitProven where
  srcDir := "."
  roots := #[`Cache.HitProven]

@[default_target] lean_lib ForwardProven where
  srcDir := "."
  roots := #[`Proxy.ForwardProven]

@[default_target] lean_lib H2cProven where
  srcDir := "."
  roots := #[`H2.H2cProven]

@[default_target] lean_lib SerializeSanitize where
  roots := #[`Reactor.SerializeSanitize]

@[default_target] lean_lib H2FlowProven where
  srcDir := "."
  roots := #[`H2.FlowProven]

@[default_target] lean_lib HeadProven where
  srcDir := "."
  roots := #[`Proto.HeadProven]

@[default_target] lean_lib ChunkedProven where
  srcDir := "."
  roots := #[`Proto.ChunkedProven]

@[default_target] lean_lib OptionsProven where
  srcDir := "."
  roots := #[`Proto.OptionsProven]

lean_lib QueryRouteProven where
  srcDir := "."
  roots := #[`Route.QueryRouteProven]

@[default_target] lean_lib Expect100Proven where
  srcDir := "."
  roots := #[`Proto.Expect100Proven]

@[default_target] lean_lib RangeProven where
  srcDir := "."
  roots := #[`Proto.RangeProven]

@[default_target] lean_lib BulkProven where
  srcDir := "."
  roots := #[`Proto.BulkProven]

@[default_target] lean_lib GzipProven where
  srcDir := "."
  roots := #[`Proto.GzipProven]

@[default_target] lean_lib ZeroCopyBodyProven where
  srcDir := "."
  roots := #[`Proto.ZeroCopyBodyProven]

@[default_target] lean_lib CtGateProven where
  srcDir := "."
  roots := #[`Proto.CtGateProven]

@[default_target] lean_lib GzipLargeProven where
  srcDir := "."
  roots := #[`Proto.GzipLargeProven]

@[default_target] lean_lib ContentTypeProven where
  srcDir := "."
  roots := #[`Proto.ContentTypeProven]

@[default_target] lean_lib ServerHeaderProven where
  srcDir := "."
  roots := #[`Proto.ServerHeaderProven]

@[default_target] lean_lib NoSniffProven where
  srcDir := "."
  roots := #[`Proto.NoSniffProven]

@[default_target] lean_lib RetryAfterProven where
  srcDir := "."
  roots := #[`Proto.RetryAfterProven]

@[default_target] lean_lib ContentLanguageProven where
  srcDir := "."
  roots := #[`Proto.ContentLanguageProven]

@[default_target] lean_lib ContentRange416Proven where
  srcDir := "."
  roots := #[`Proto.ContentRange416Proven]

@[default_target] lean_lib BadVersionProven where
  srcDir := "."
  roots := #[`Proto.BadVersionProven]

@[default_target] lean_lib NotImplementedProven where
  srcDir := "."
  roots := #[`Proto.NotImplementedProven]

@[default_target] lean_lib TraceMaxForwardsProven where
  srcDir := "."
  roots := #[`Proto.TraceMaxForwardsProven]

@[default_target] lean_lib HstsProven where
  srcDir := "."
  roots := #[`Proto.HstsProven]

@[default_target] lean_lib StaticServeProven where
  srcDir := "."
  roots := #[`Proto.StaticServeProven]

@[default_target] lean_lib XUpstreamProven where
  srcDir := "."
  roots := #[`Proto.XUpstreamProven]

@[default_target] lean_lib XCorrProven where
  srcDir := "."
  roots := #[`Proto.XCorrProven]

@[default_target] lean_lib CorsAcaoProven where
  srcDir := "."
  roots := #[`Proto.CorsAcaoProven]

@[default_target] lean_lib NotFoundProven where
  srcDir := "."
  roots := #[`Proto.NotFoundProven]

@[default_target] lean_lib StatusLine200Proven where
  srcDir := "."
  roots := #[`Proto.StatusLine200Proven]

@[default_target] lean_lib ContentLengthProven where
  srcDir := "."
  roots := #[`Proto.ContentLengthProven]

@[default_target] lean_lib IpFilterDeployedProven where
  srcDir := "."
  roots := #[`Proto.IpFilterDeployedProven]

@[default_target] lean_lib RateDeployedProven where
  srcDir := "."
  roots := #[`Proto.RateDeployedProven]

@[default_target] lean_lib VaryProven where
  srcDir := "."
  roots := #[`Proto.VaryProven]

@[default_target] lean_lib AgeProven where
  srcDir := "."
  roots := #[`Proto.AgeProven]

@[default_target] lean_lib ContentDispositionProven where
  srcDir := "."
  roots := #[`Proto.ContentDispositionProven]


@[default_target] lean_lib ReactorStageProxyProtocol where
  srcDir := "."
  roots := #[`Reactor.Stage.ProxyProtocol]

@[default_target] lean_lib ReactorStageCookieSecure where
  srcDir := "."
  roots := #[`Reactor.Stage.CookieSecure]

@[default_target] lean_lib KernelShortcuts where
  srcDir := "."
  roots := #[`Proto.Kernel.Shortcuts]

@[default_target] lean_lib ReactorStageLinkPreload where
  srcDir := "."
  roots := #[`Reactor.Stage.LinkPreload]

@[default_target] lean_lib ReactorStageWarningTransform where
  srcDir := "."
  roots := #[`Reactor.Stage.WarningTransform]

@[default_target] lean_lib ReactorStageCacheStatus where
  srcDir := "."
  roots := #[`Reactor.Stage.CacheStatus]

@[default_target] lean_lib ReactorStageCrossOriginResource where
  srcDir := "."
  roots := #[`Reactor.Stage.CrossOriginResource]

@[default_target] lean_lib ReactorStagePermissionsPolicy where
  srcDir := "."
  roots := #[`Reactor.Stage.PermissionsPolicy]

@[default_target] lean_lib ReactorStageAltSvc where
  srcDir := "."
  roots := #[`Reactor.Stage.AltSvc]

@[default_target] lean_lib WsUtf8 where
  srcDir := "."
  roots := #[`Ws.Utf8]

@[default_target] lean_lib WsReassemblyAdmit where
  srcDir := "."
  roots := #[`Ws.ReassemblyAdmit]

@[default_target] lean_lib WsReassemblyClose where
  srcDir := "."
  roots := #[`Ws.ReassemblyClose]
