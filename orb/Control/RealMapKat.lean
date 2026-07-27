import Control.Tailcfg
import Control.TailcfgWire

/-!
# Real stock-client MapRequest / MapResponse capture (ground truth)

Every literal in this file was **captured from a stock `tailscale` client (1.98.8)
talking to a real `headscale` control server**, not hand-written.

## Provenance

* Client: `tailscale` / `tailscaled` **1.98.8** (`1.98.8-t1241b225b-g0520dfda5`,
  go1.26.3), the distro binary, run as an **isolated** second daemon
  (`--tun=userspace-networking`, own socket/state/port).
* Control server: **headscale v0.29.2** (`headscale/headscale:latest`), a
  throwaway container on loopback, seeded with one user and a reusable preauth key.
* Method: a **ts2021 MITM** sat between them. It terminated the client's
  `Noise_IK_25519_ChaChaPoly_BLAKE2s` session with its own machine key,
  re-originated a second real Noise session to headscale with headscale's real
  machine key, and relayed the inner HTTP/2 plaintext **verbatim** in both
  directions, teeing it to disk. The only bytes the MITM authored were the two
  Noise handshakes it was a legitimate party to; every application byte is the
  real client's or the real server's. `tailscale up` **completed registration**
  (the node received `100.64.0.1`), so the full
  `RegisterRequest -> MapRequest{Stream} -> MapResponse` exchange really flowed.
* MapRequest bodies are cleartext HTTP/2 DATA frames. The MapResponse was carried
  as `[u32LE len][zstd frame]` (the client advertised `Compress:"zstd"`) and was
  decompressed with stock `zstd -d`; the JSON below is that decompressed body.
* Raw artifacts: `Control/testdata/{map_request_stream,map_request_poll,
  map_response_full}.json`.

## What these KATs pin

drorb's codec previously **REJECTED every one of these** — it modeled the Go
`omitzero`/`omitempty` scalars (`Stream`, `OmitPeers`, `ReadOnly`, `KeepAlive`,
`Node.HomeDERP`) and the legacy `PacketFilter` array as *required*, and did not
model the newer `PacketFilters` map the server actually sends. The theorems below
witness that drorb now decodes the real bytes and lands the omitted scalars at
Go's zero value.
-/

namespace Control.RealMapKat

open Control.TailcfgWire

def realMapRequestStream : String :=
  "{\"Version\":138,\"Compress\":\"zstd\",\"KeepAlive\":true,\"NodeKey\":\"nodekey:39833dd99f4e33f3"
  ++ "1e0f43d8902b971367387151803dcfbedac1a275c8823c64\",\"DiscoKey\":\"discokey:b10f6ec363ffbbfbe5771"
  ++ "283545ec6cecb7819ec483d92697a27f1674c93e555\",\"Stream\":true,\"Hostinfo\":{\"IPNVersion\":\"1.9"
  ++ "8.8-t1241b225b-g0520dfda5\",\"BackendLogID\":\"b623891acb2bf89bb4bd027bb6230967bdd80ee04990b1581"
  ++ "6570876c69ad9ab\",\"OS\":\"linux\",\"OSVersion\":\"6.11.0-29-generic\",\"Container\":false,\"Dis"
  ++ "tro\":\"ubuntu\",\"DistroVersion\":\"24.10\",\"DistroCodeName\":\"oracular\",\"Desktop\":true,\""
  ++ "Hostname\":\"mapcaptest\",\"Machine\":\"x86_64\",\"GoArch\":\"amd64\",\"GoArchVar\":\"v1\",\"GoV"
  ++ "ersion\":\"go1.26.3\",\"Services\":[{\"Proto\":\"peerapi-dns-proxy\",\"Port\":1}],\"Userspace\":"
  ++ "true,\"UserspaceRouter\":true,\"AppConnector\":false,\"StateEncrypted\":false},\"DebugFlags\":["
  ++ "\"netstack\"]}"

def realMapRequestPoll : String :=
  "{\"Version\":138,\"Compress\":\"zstd\",\"KeepAlive\":true,\"NodeKey\":\"nodekey:39833dd99f4e33f3"
  ++ "1e0f43d8902b971367387151803dcfbedac1a275c8823c64\",\"DiscoKey\":\"discokey:b10f6ec363ffbbfbe5771"
  ++ "283545ec6cecb7819ec483d92697a27f1674c93e555\",\"Hostinfo\":{\"IPNVersion\":\"1.98.8-t1241b225b-g"
  ++ "0520dfda5\",\"BackendLogID\":\"b623891acb2bf89bb4bd027bb6230967bdd80ee04990b15816570876c69ad9ab"
  ++ "\",\"OS\":\"linux\",\"OSVersion\":\"6.11.0-29-generic\",\"Container\":false,\"Distro\":\"ubuntu"
  ++ "\",\"DistroVersion\":\"24.10\",\"DistroCodeName\":\"oracular\",\"Desktop\":true,\"Hostname\":\"m"
  ++ "apcaptest\",\"Machine\":\"x86_64\",\"GoArch\":\"amd64\",\"GoArchVar\":\"v1\",\"GoVersion\":\"go1"
  ++ ".26.3\",\"Services\":[{\"Proto\":\"peerapi4\",\"Port\":58436},{\"Proto\":\"peerapi6\",\"Port\":5"
  ++ "8436},{\"Proto\":\"peerapi-dns-proxy\",\"Port\":1}],\"NetInfo\":{\"WorkingIPv6\":false,\"OSHasIP"
  ++ "v6\":true,\"WorkingUDP\":false,\"WorkingICMPv4\":false,\"HavePortMap\":true,\"UPnP\":true,\"PMP"
  ++ "\":true,\"PCP\":true,\"PreferredDERP\":900},\"Userspace\":true,\"UserspaceRouter\":true,\"AppCon"
  ++ "nector\":false,\"StateEncrypted\":false},\"Endpoints\":[\"73.4.118.165:41999\",\"172.17.0.1:4199"
  ++ "9\",\"192.168.50.39:41999\"],\"EndpointTypes\":[3,1,1],\"OmitPeers\":true,\"DebugFlags\":[\"nets"
  ++ "tack\"]}"

def realMapResponseFull : String :=
  "{\"Node\":{\"ID\":1,\"StableID\":\"1\",\"Name\":\"mapcaptest.capnet.internal.\",\"User\":1,\"Key"
  ++ "\":\"nodekey:39833dd99f4e33f31e0f43d8902b971367387151803dcfbedac1a275c8823c64\",\"Machine\":\"mk"
  ++ "ey:bce9614e6b4973b19e8891cfadcc0dca5f8810c7dcc82ea2930e1abcb183d52c\",\"DiscoKey\":\"discokey:b1"
  ++ "0f6ec363ffbbfbe5771283545ec6cecb7819ec483d92697a27f1674c93e555\",\"Addresses\":[\"100.64.0.1/32"
  ++ "\",\"fd7a:115c:a1e0::1/128\"],\"AllowedIPs\":[\"100.64.0.1/32\",\"fd7a:115c:a1e0::1/128\"],\"Hos"
  ++ "tinfo\":{\"IPNVersion\":\"1.98.8-t1241b225b-g0520dfda5\",\"BackendLogID\":\"b623891acb2bf89bb4bd"
  ++ "027bb6230967bdd80ee04990b15816570876c69ad9ab\",\"OS\":\"linux\",\"OSVersion\":\"6.11.0-29-generi"
  ++ "c\",\"Container\":false,\"Distro\":\"ubuntu\",\"DistroVersion\":\"24.10\",\"DistroCodeName\":\"o"
  ++ "racular\",\"Desktop\":true,\"Hostname\":\"mapcaptest\",\"Machine\":\"x86_64\",\"GoArch\":\"amd64"
  ++ "\",\"GoArchVar\":\"v1\",\"GoVersion\":\"go1.26.3\",\"Services\":[{\"Proto\":\"peerapi-dns-proxy"
  ++ "\",\"Port\":1}],\"Userspace\":true,\"UserspaceRouter\":true,\"AppConnector\":false,\"StateEncryp"
  ++ "ted\":false},\"Created\":\"2026-07-19T15:56:02.003653982Z\",\"Cap\":138,\"Online\":true,\"Machin"
  ++ "eAuthorized\":true,\"CapMap\":{\"default-auto-update\":[false],\"https://tailscale.com/cap/file-"
  ++ "sharing\":[],\"https://tailscale.com/cap/is-admin\":[],\"https://tailscale.com/cap/ssh\":[]}},\""
  ++ "DERPMap\":{\"Regions\":{\"900\":{\"RegionID\":900,\"RegionCode\":\"cap\",\"RegionName\":\"Captur"
  ++ "eRegion\",\"Nodes\":[{\"Name\":\"900a\",\"RegionID\":900,\"HostName\":\"derp.capnet.internal\","
  ++ "\"IPv4\":\"127.0.0.1\",\"STUNPort\":3478,\"DERPPort\":3340}]}}},\"DNSConfig\":{\"Resolvers\":[{"
  ++ "\"Addr\":\"1.1.1.1\"}],\"Routes\":{\"0.e.1.a.c.5.1.1.a.7.d.f.ip6.arpa\":[],\"100.100.in-addr.arp"
  ++ "a\":[],\"101.100.in-addr.arpa\":[],\"102.100.in-addr.arpa\":[],\"103.100.in-addr.arpa\":[],\"104"
  ++ ".100.in-addr.arpa\":[],\"105.100.in-addr.arpa\":[],\"106.100.in-addr.arpa\":[],\"107.100.in-addr"
  ++ ".arpa\":[],\"108.100.in-addr.arpa\":[],\"109.100.in-addr.arpa\":[],\"110.100.in-addr.arpa\":[],"
  ++ "\"111.100.in-addr.arpa\":[],\"112.100.in-addr.arpa\":[],\"113.100.in-addr.arpa\":[],\"114.100.in"
  ++ "-addr.arpa\":[],\"115.100.in-addr.arpa\":[],\"116.100.in-addr.arpa\":[],\"117.100.in-addr.arpa\""
  ++ ":[],\"118.100.in-addr.arpa\":[],\"119.100.in-addr.arpa\":[],\"120.100.in-addr.arpa\":[],\"121.10"
  ++ "0.in-addr.arpa\":[],\"122.100.in-addr.arpa\":[],\"123.100.in-addr.arpa\":[],\"124.100.in-addr.ar"
  ++ "pa\":[],\"125.100.in-addr.arpa\":[],\"126.100.in-addr.arpa\":[],\"127.100.in-addr.arpa\":[],\"64"
  ++ ".100.in-addr.arpa\":[],\"65.100.in-addr.arpa\":[],\"66.100.in-addr.arpa\":[],\"67.100.in-addr.ar"
  ++ "pa\":[],\"68.100.in-addr.arpa\":[],\"69.100.in-addr.arpa\":[],\"70.100.in-addr.arpa\":[],\"71.10"
  ++ "0.in-addr.arpa\":[],\"72.100.in-addr.arpa\":[],\"73.100.in-addr.arpa\":[],\"74.100.in-addr.arpa"
  ++ "\":[],\"75.100.in-addr.arpa\":[],\"76.100.in-addr.arpa\":[],\"77.100.in-addr.arpa\":[],\"78.100."
  ++ "in-addr.arpa\":[],\"79.100.in-addr.arpa\":[],\"80.100.in-addr.arpa\":[],\"81.100.in-addr.arpa\":"
  ++ "[],\"82.100.in-addr.arpa\":[],\"83.100.in-addr.arpa\":[],\"84.100.in-addr.arpa\":[],\"85.100.in-"
  ++ "addr.arpa\":[],\"86.100.in-addr.arpa\":[],\"87.100.in-addr.arpa\":[],\"88.100.in-addr.arpa\":[],"
  ++ "\"89.100.in-addr.arpa\":[],\"90.100.in-addr.arpa\":[],\"91.100.in-addr.arpa\":[],\"92.100.in-add"
  ++ "r.arpa\":[],\"93.100.in-addr.arpa\":[],\"94.100.in-addr.arpa\":[],\"95.100.in-addr.arpa\":[],\"9"
  ++ "6.100.in-addr.arpa\":[],\"97.100.in-addr.arpa\":[],\"98.100.in-addr.arpa\":[],\"99.100.in-addr.a"
  ++ "rpa\":[]},\"Domains\":[\"capnet.internal\"],\"Proxied\":true},\"Domain\":\"127.0.0.1\",\"PacketF"
  ++ "ilters\":{\"base\":[{\"SrcIPs\":[\"*\"],\"DstPorts\":[{\"IP\":\"*\",\"Ports\":{\"First\":0,\"Las"
  ++ "t\":65535}}]}]},\"UserProfiles\":[{\"ID\":1,\"LoginName\":\"captureuser\",\"DisplayName\":\"capt"
  ++ "ureuser\"}],\"ControlTime\":\"2026-07-19T15:56:03.880112602Z\"}"


/-! ## §1  Real MapRequest with `Stream:true` (streaming poll opened) -/

-- Fields present: Version, Compress, KeepAlive, NodeKey, DiscoKey, Stream,
-- Hostinfo, DebugFlags. ABSENT (Go omitzero): OmitPeers, ReadOnly.
#eval (MapRequest.wireDecode realMapRequestStream).isSome              -- expect: true
#eval (MapRequest.wireDecode realMapRequestStream).map (·.stream)     -- some true
#eval (MapRequest.wireDecode realMapRequestStream).map (·.omitPeers)  -- some false
#eval (MapRequest.wireDecode realMapRequestStream).map (·.readOnly)   -- some false

/-- **drorb decodes the real streaming MapRequest.** -/
theorem mapRequestStream_isSome :
    (MapRequest.wireDecode realMapRequestStream).isSome = true := by native_decide

/-- `Stream` (Go `bool,omitzero`) is present and true. -/
theorem mapRequestStream_stream :
    (MapRequest.wireDecode realMapRequestStream).map (·.stream) = some true := by
  native_decide

/-- `OmitPeers` and `ReadOnly` are ABSENT on the wire; the fixed codec defaults
them to Go's zero value `false` instead of rejecting the message. -/
theorem mapRequestStream_omitempty_defaults :
    (MapRequest.wireDecode realMapRequestStream).map (fun m => (m.omitPeers, m.readOnly))
      = some (false, false) := by native_decide

/-! ## §2  Real MapRequest poll (`OmitPeers`, `Endpoints`, `NetInfo`) -/

-- Fields present: OmitPeers:true, Endpoints, EndpointTypes, NetInfo (in Hostinfo).
-- ABSENT (Go omitzero): Stream, ReadOnly.
#eval (MapRequest.wireDecode realMapRequestPoll).isSome                -- expect: true
#eval (MapRequest.wireDecode realMapRequestPoll).map (·.omitPeers)     -- some true
#eval (MapRequest.wireDecode realMapRequestPoll).map (·.stream)        -- some false
#eval (MapRequest.wireDecode realMapRequestPoll).bind (·.endpoints)

/-- **drorb decodes the real poll MapRequest.** -/
theorem mapRequestPoll_isSome :
    (MapRequest.wireDecode realMapRequestPoll).isSome = true := by native_decide

/-- `OmitPeers` present/true while `Stream` is ABSENT (defaults false). -/
theorem mapRequestPoll_omitPeers_stream :
    (MapRequest.wireDecode realMapRequestPoll).map (fun m => (m.omitPeers, m.stream))
      = some (true, false) := by native_decide

/-- The three real client `Endpoints` land as the exact address strings. -/
theorem mapRequestPoll_endpoints :
    (MapRequest.wireDecode realMapRequestPoll).bind (·.endpoints)
      = some ["73.4.118.165:41999", "172.17.0.1:41999", "192.168.50.39:41999"] := by
  native_decide

/-- **The real client `DiscoKey` lands as the exact `"discokey:<hex>"` string.** This is
the disco key magicsock seals its NAT-probe boxes to; the coordinator must store it and
serve it to peers (`Control.Join.withNat_disco_served`). Pinned on the REAL captured poll
bytes — the same `DiscoKey` the streaming MapRequest also carries. -/
theorem mapRequestPoll_discoKey :
    (MapRequest.wireDecode realMapRequestPoll).bind (·.discoKey)
      = some "discokey:b10f6ec363ffbbfbe5771283545ec6cecb7819ec483d92697a27f1674c93e555" := by
  native_decide

theorem mapRequestStream_discoKey :
    (MapRequest.wireDecode realMapRequestStream).bind (·.discoKey)
      = some "discokey:b10f6ec363ffbbfbe5771283545ec6cecb7819ec483d92697a27f1674c93e555" := by
  native_decide

/-! ## §3  Real MapResponse (Node + DERPMap + DNSConfig + `PacketFilters` map) -/

-- Present: Node (no HomeDERP), DERPMap, DNSConfig, Domain, PacketFilters (map),
-- UserProfiles, ControlTime. ABSENT (Go omitempty): legacy PacketFilter, KeepAlive.
#eval (MapResponse.wireDecode realMapResponseFull).isSome              -- expect: true
#eval (MapResponse.wireDecode realMapResponseFull).bind (·.node) |>.map (·.homeDERP)  -- some 0
#eval (MapResponse.wireDecode realMapResponseFull).map (·.keepAlive)  -- some false
#eval (MapResponse.wireDecode realMapResponseFull).map (·.packetFilter.isEmpty)  -- some true
#eval (MapResponse.wireDecode realMapResponseFull).bind (·.packetFilters)
        |>.map (fun kvs => kvs.map (·.1))                             -- some ["base"]

/-- **drorb decodes the real MapResponse** — the message that every prior codec
version rejected. -/
theorem mapResponse_isSome :
    (MapResponse.wireDecode realMapResponseFull).isSome = true := by native_decide

/-- The real `Node` omits `HomeDERP` (Go `int,omitzero`); the fixed codec lands
it at Go's zero value `0` rather than rejecting the whole MapResponse. -/
theorem mapResponse_node_homeDERP_default :
    ((MapResponse.wireDecode realMapResponseFull).bind (·.node)).map (·.homeDERP)
      = some 0 := by native_decide

/-- The real MapResponse omits `KeepAlive` and the legacy `PacketFilter` array;
both land at Go's zero value (`false` / the empty list). -/
theorem mapResponse_omitempty_defaults :
    (MapResponse.wireDecode realMapResponseFull).map (fun m => (m.keepAlive, m.packetFilter.isEmpty))
      = some (false, true) := by native_decide

/-- The real ACL is carried in the newer **`PacketFilters` map** (keyed `"base"`),
which drorb now models and decodes. -/
theorem mapResponse_packetFilters_base :
    ((MapResponse.wireDecode realMapResponseFull).bind (·.packetFilters)).map
        (fun kvs => kvs.map (·.1))
      = some ["base"] := by native_decide

#print axioms mapRequestStream_isSome
#print axioms mapRequestStream_omitempty_defaults
#print axioms mapRequestPoll_endpoints
#print axioms mapRequestPoll_discoKey
#print axioms mapRequestStream_discoKey
#print axioms mapResponse_isSome
#print axioms mapResponse_node_homeDERP_default
#print axioms mapResponse_packetFilters_base

/-! ## §4  ★ The endpoint-report poll, VERBATIM — the one drorb silently dropped

Captured 2026-07-25 on hbox from stock `tailscale` 1.98.8 enrolled against **drorb's own**
coordinator (`scripts/run-tailnet.sh`), dumped by `ControlLive.dumpBodies`
(`DRORB_DEBUG_MAPREQ=1`) straight off the verified h2 engine's assembled stream body.

This is the request that carries `Endpoints` — the ONLY place a client tells the
coordinator where peers may reach it directly. The §2 poll above was captured against
headscale and happens to carry **no `NetInfo`**; this one does, and `NetInfo.DERPLatency`
holds a REAL number:

    "DERPLatency":{"1-v4":0.00040243}

drorb's `pNum` parsed integers only, so this single field made the WHOLE request
unparseable, `ControlLive.natReportsOf` returned nothing, the NAT table never learned an
endpoint, every served peer went out with `Endpoints: null`, and no client on the tailnet
could attempt a direct path. Nothing logged an error — the endpoint report was simply the
only thing the tailnet lost. `Control.TailcfgWire.numTail` implements the RFC 8259 §6
number grammar; these KATs are the regression gate. -/

/-- The endpoint-report poll, byte-for-byte. -/
def realMapRequestEndpoints : String :=
  "{\"Version\":138,\"Compress\":\"zstd\",\"KeepAlive\":true,\"NodeKey\":\"nodekey:287e5107"
  ++ "5b4bdf1489fa5154921f2227d8231d9e41857bb9147faec8c833987c\",\"DiscoKey\":\"discokey:95191"
  ++ "962eb74b6738e8ced9bb9c3df57f50250478ebc763138b897374021e858\",\"Hostinfo\":{\"IPNVersion"
  ++ "\":\"1.98.8-t1241b225b-g0520dfda5\",\"BackendLogID\":\"b623891acb2bf89bb4bd027bb6230967b"
  ++ "dd80ee04990b15816570876c69ad9ab\",\"OS\":\"linux\",\"OSVersion\":\"6.11.0-29-generic\","
  ++ "\"Container\":false,\"Distro\":\"ubuntu\",\"DistroVersion\":\"24.10\",\"DistroCodeName\":"
  ++ "\"oracular\",\"Desktop\":true,\"Hostname\":\"node-1\",\"Machine\":\"x86_64\",\"GoArch\":"
  ++ "\"amd64\",\"GoArchVar\":\"v1\",\"GoVersion\":\"go1.26.3\",\"Services\":[{\"Proto\":\"pee"
  ++ "rapi4\",\"Port\":58436},{\"Proto\":\"peerapi-dns-proxy\",\"Port\":1}],\"NetInfo\":{\"Wor"
  ++ "kingIPv6\":false,\"OSHasIPv6\":true,\"WorkingUDP\":true,\"WorkingICMPv4\":false,\"HavePo"
  ++ "rtMap\":true,\"UPnP\":true,\"PMP\":true,\"PCP\":true,\"PreferredDERP\":1,\"DERPLatency\""
  ++ ":{\"1-v4\":0.00040243}},\"Userspace\":true,\"UserspaceRouter\":true,\"AppConnector\":fal"
  ++ "se,\"StateEncrypted\":false},\"Endpoints\":[\"73.4.118.165:45991\",\"192.168.50.39:45991"
  ++ "\",\"172.17.0.1:45991\"],\"EndpointTypes\":[3,2,1],\"OmitPeers\":true,\"DebugFlags\":[\""
  ++ "netstack\"]}"

/-- **It parses at all.** The float in `NetInfo.DERPLatency` no longer kills the request. -/
theorem mapRequestEndpoints_isSome :
    (MapRequest.wireDecode realMapRequestEndpoints).isSome = true := by native_decide

/-- **★ The three real endpoints are decoded, in order.** These are exactly the candidates
`magicsock` reported (`endpoints changed: 73.4.118.165:45991 (portmap),
192.168.50.39:45991 (stun), 172.17.0.1:45991 (local)`), and exactly what
`Control.Join.applyNatState` then serves to this node's peers. -/
theorem mapRequestEndpoints_endpoints :
    (MapRequest.wireDecode realMapRequestEndpoints).bind (·.endpoints)
      = some ["73.4.118.165:45991", "192.168.50.39:45991", "172.17.0.1:45991"] := by
  native_decide

/-- The disco key rides the same request, so one report gives the coordinator both halves
of what magicsock needs to path-build. -/
theorem mapRequestEndpoints_discoKey :
    (MapRequest.wireDecode realMapRequestEndpoints).bind (·.discoKey)
      = some "discokey:95191962eb74b6738e8ced9bb9c3df57f50250478ebc763138b897374021e858" := by
  native_decide

/-- It is the short `OmitPeers` poll, not the streaming long-poll — the shape
`ControlLive.pushLoop` must DRAIN off the already-open h2 connection to see it at all. -/
theorem mapRequestEndpoints_omitPeers :
    (MapRequest.wireDecode realMapRequestEndpoints).map (fun m => (m.omitPeers, m.stream))
      = some (true, false) := by native_decide

#print axioms mapRequestEndpoints_isSome
#print axioms mapRequestEndpoints_endpoints
#print axioms mapRequestEndpoints_discoKey
#print axioms mapRequestEndpoints_omitPeers

end Control.RealMapKat
