/-
# DiscoMeshLive — driving the PROVEN DISCO/STUN path-discovery + ICE pairing over the byte level

The mesh dataplane learns *where a peer can be reached* before it commits a path.
Three proven, sans-IO layers do that, and this executable is the wiring that drives
them end to end over real bytes in one process:

  * **STUN server-reflexive discovery (RFC 5389 §15.2).** A client sends a Binding
    request; the reflector answers with `Stun.respond`, packing the observed source
    transport address into an XOR-MAPPED-ADDRESS. The client parses the reply and
    recovers its own public endpoint with `Disco.reflexiveEndpoint` — the exact
    Tailscale DISCO STUN→candidate bridge (`Disco.endpointOfStun`). This is the
    *path* the mesh discovers: the reflexive candidate address.

  * **DISCO CallMeMaybe rendezvous (Tailscale `disco`, TypeCallMeMaybe `0x03`).**
    The relayed message that seeds a peer's candidate endpoints, `ip(16) ‖ port(2)`
    each. `Disco.encodeCallMeMaybe` / `Disco.decodeDiscoMessage` are the wire codec,
    pinned by `Disco.disco_callmemaybe_roundtrip`. No crypto — a plain byte codec.

  * **ICE candidate pairing (RFC 8445 §6.1.2).** The discovered candidates are
    formed into pairs (`Ice.formPairs`), each pair driven through the connectivity
    checklist FSM (`Ice.step` : frozen → waiting → inProgress → succeeded), then
    nominated (`Ice.nominate`) so the send gate `Ice.mayDeliver` opens — and never
    before, by `Ice.ice_no_send_before_succeeded`. The §7.2.2 connectivity-check
    Binding request itself (`Ice.checkRequest`, MESSAGE-INTEGRITY + FINGERPRINT
    over pure-Lean HMAC-SHA1 / CRC-32) is exercised too.

## The faithfulness theorem

`disco_path_faithful` (below) proves the running loop's discovery step is faithful:
parsing the reflector's Binding-success bytes and running `Disco.reflexiveEndpoint`
on them recovers PRECISELY `Disco.endpointOfStun src` — the endpoint the reflector
observed — for every well-formed source address. It composes the FINGERPRINT parse
round-trip with the XOR-MAPPED-ADDRESS codec round-trip; the hypotheses are the
satisfiable well-formedness of a real transport address (the selftest's `src`
satisfies them), the conclusion a real equation over the byte-driven discovery
pipeline. `disco_path_faithful_v4` discharges it fully for a concrete IPv4 endpoint.

## Honesty / realization boundary (the DiscoLive / DnsResolveLive discipline)

The `selftest` is **drorb-native**: the reflector, the CallMeMaybe seeder, and the
ICE checker are our own spec-conformant peers speaking the modelled RFC 5389 /
RFC 8445 / DISCO wire formats, driven byte-to-byte in one process (no sockets).
Everything structural/codec is the proven Lean; the gap the selftest discharges by
construction (not proof) is that this exe faithfully CALLS the proven functions on
real bytes — the decode→discover chain's own faithfulness is `disco_path_faithful`.
The DISCO Ping/Pong crypto verify (X25519 + XSalsa20-Poly1305) is NOT exercised
here — that is `disco-live`'s job and needs the crypto FFI, out of the pure-Lean
interpreter. The `probe <server> <port>` mode is REAL STUN-over-TCP interop against
an external reflector — a named residual (needs a reachable STUN server).

Usage:
  disco-mesh-live selftest
  disco-mesh-live probe <server> <port>
-/
import Disco
import Ice

namespace DiscoMeshLive

/-! ## The Phase-0 faithfulness theorem

The running discovery loop holds only the reflector's reply bytes; it parses them
and calls `Disco.reflexiveEndpoint` to recover its reflexive candidate. This theorem
says that chain, applied to the bytes a spec-conformant reflector produces for a
source endpoint `src`, recovers exactly the DISCO candidate `endpointOfStun src`.
It composes `Stun.withFingerprint_parses` (the reply parses to the XOR-MAPPED +
FINGERPRINT attribute list) with `Stun.xorMapped_roundtrip` (the address codec).
Not a `P → P`: the hypotheses are the satisfiable field bounds of a transport
address, the conclusion a real equation over the discovery pipeline. -/
theorem disco_path_faithful (txid : Stun.Bytes) (src : Stun.Endpoint)
    (htx : txid.length = 12) (hport : src.port < 65536)
    (hfam : (src.family = 1 ∧ src.addr.length = 4) ∨
            (src.family = 2 ∧ src.addr.length = 16)) :
    ∃ m, Stun.parse (Stun.bindingSuccess txid src) = some m ∧
      Disco.reflexiveEndpoint m = some (Disco.endpointOfStun src) := by
  have haddr16 : src.addr.length ≤ 16 := by
    rcases hfam with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have hxlen : (Stun.xorMappedValue txid src).length = 4 + src.addr.length := by
    simp only [Stun.xorMappedValue, List.length_append, List.length_cons,
      List.length_nil, Stun.enc16, Stun.xorBytes, List.length_zipWith,
      Stun.magicCookie, htx]
    omega
  have hwf1 : ∀ a ∈ [(⟨Stun.attrXorMappedAddress,
      Stun.xorMappedValue txid src⟩ : Stun.Attr)],
      a.type < 65536 ∧ a.value.length < 65536 := by
    intro a ha
    simp only [List.mem_singleton] at ha
    subst ha
    exact ⟨by simp [Stun.attrXorMappedAddress], by simp only [hxlen]; omega⟩
  have hblen1 : (Stun.encodeAttrs
      [(⟨Stun.attrXorMappedAddress, Stun.xorMappedValue txid src⟩ : Stun.Attr)]).length
      + 8 < 65536 := by
    have hpx := Stun.padLen_lt (4 + src.addr.length)
    simp only [Stun.encodeAttrs, Stun.encodeAttr_length, Stun.attrSize,
      List.length_append, List.length_nil, hxlen]
    omega
  obtain ⟨fpv, hfpv⟩ : ∃ v, Stun.u32Bytes (Stun.crc32
      (Stun.enc16 Stun.bindingSuccessType ++
        Stun.enc16 ((Stun.encodeAttrs
          [(⟨Stun.attrXorMappedAddress,
            Stun.xorMappedValue txid src⟩ : Stun.Attr)]).length + 8) ++
        Stun.magicCookie ++ txid ++
        Stun.encodeAttrs [(⟨Stun.attrXorMappedAddress,
          Stun.xorMappedValue txid src⟩ : Stun.Attr)]) ^^^
      Stun.fingerprintMask) = v := ⟨_, rfl⟩
  have hpe := Stun.withFingerprint_parses Stun.bindingSuccessType txid
    [(⟨Stun.attrXorMappedAddress, Stun.xorMappedValue txid src⟩ : Stun.Attr)] fpv hfpv
    (by simp [Stun.bindingSuccessType]) htx hblen1 hwf1
  have hattr : Stun.findAttr Stun.attrXorMappedAddress
      ([(⟨Stun.attrXorMappedAddress, Stun.xorMappedValue txid src⟩ : Stun.Attr)] ++
        [⟨Stun.attrFingerprint, fpv⟩])
      = some ⟨Stun.attrXorMappedAddress, Stun.xorMappedValue txid src⟩ := by
    simp [Stun.findAttr, List.find?]
  refine ⟨_, hpe, ?_⟩
  unfold Disco.reflexiveEndpoint
  simp only [hattr, Stun.xorMapped_roundtrip txid src htx hport hfam,
    Option.map_some]

/-- The concrete IPv4 reflexive endpoint the selftest discovers: `203.0.113.7:51820`
(TEST-NET-3), transaction id twelve fixed bytes. -/
def demoTxid : Stun.Bytes :=
  [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3a, 0x3b, 0x3c]
def demoSrc : Stun.Endpoint :=
  { family := 1, port := 51820, addr := [203, 0, 113, 7] }

/-- **Discovery is faithful, closed for a concrete IPv4 reflexive endpoint.**
The reflector's Binding-success bytes for `203.0.113.7:51820`, parsed and run through
`Disco.reflexiveEndpoint`, recover exactly `Disco.endpointOfStun demoSrc` — the
discovery pipeline realizes the model, no hypotheses left open. -/
theorem disco_path_faithful_v4 :
    ∃ m, Stun.parse (Stun.bindingSuccess demoTxid demoSrc) = some m ∧
      Disco.reflexiveEndpoint m = some (Disco.endpointOfStun demoSrc) :=
  disco_path_faithful demoTxid demoSrc (by decide) (by decide) (by decide)

/-! ## The ICE §7.2.2 connectivity-check request, closed

`Ice.checkRequest` builds the actual integrity-protected Binding request an agent
sends on a candidate pair; `Ice.checkRequest_correct` proves it verifies and parses.
Instantiated here at the selftest's concrete parameters (no HMAC is evaluated — the
proof is the abstract sign/verify round-trip), a fully closed correctness statement
for the wire the `perform`/`checkSucceeded` FSM events are driven by. -/
def demoPwd : Stun.Bytes :=
  [0x73, 0x65, 0x63, 0x72, 0x65, 0x74, 0x70, 0x77, 0x64]      -- "secretpwd"
def demoUser : Stun.Bytes :=
  [0x52, 0x46, 0x52, 0x47, 0x3a, 0x4c, 0x46, 0x52, 0x47]      -- "RFRG:LFRG"
def demoPrio : UInt32 := 0x7effffff
def demoTie : Nat := 0x1122334455667788

theorem ice_check_verifies :
    Stun.messageIntegrityOk demoPwd
        (Ice.checkRequest demoPwd demoTxid demoUser demoPrio true demoTie true) = true ∧
    Stun.fingerprintOk
        (Ice.checkRequest demoPwd demoTxid demoUser demoPrio true demoTie true) = true ∧
    ∃ m, Stun.parse
        (Ice.checkRequest demoPwd demoTxid demoUser demoPrio true demoTie true) = some m ∧
      m.typ = Stun.bindingRequest ∧ m.txid = demoTxid ∧
      (⟨Stun.attrUsername, demoUser⟩ : Stun.Attr) ∈ m.attrs :=
  Ice.checkRequest_correct demoPwd demoTxid demoUser demoPrio true demoTie true
    (by decide) (by decide)

/-! ## The untrusted TCP socket seam (reused from ffi/derp_net.c)

Client half only (STUN is a pure client here). These are the untrusted
environment — they move bytes and hold no protocol state. -/

@[extern "drorb_tcp_connect"]
opaque tcpConnect (host : String) (port : UInt16) : IO UInt32
@[extern "drorb_tcp_send"]
opaque tcpSend (fd : UInt32) (payload : ByteArray) : IO Unit
@[extern "drorb_tcp_recv_exact"]
opaque tcpRecvExact (fd : UInt32) (nbytes : UInt32) (timeoutMs : UInt32) :
    IO (Option ByteArray)
@[extern "drorb_tcp_close"]
opaque tcpClose (fd : UInt32) : IO Unit

/-! ## Byte helpers -/

def baOfBytes (b : Stun.Bytes) : ByteArray := ⟨b.toArray⟩
def bytesOfBa (b : ByteArray) : Stun.Bytes := b.toList

def toHex (b : Stun.Bytes) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

def dot4 (a : Stun.Bytes) : String :=
  String.intercalate "." (a.map (fun b => toString b.toNat))

/-- A client Binding request, FINGERPRINT-protected (RFC 5389 §7.2.1). -/
def bindingReq (txid : Stun.Bytes) : Stun.Bytes :=
  Stun.withFingerprint Stun.bindingRequest txid []

/-! ## The selftest — the whole discovery + pairing pipeline over the byte level -/

def selftest : IO UInt32 := do
  IO.println "== disco-mesh-live selftest : STUN reflexive discovery + DISCO CallMeMaybe + ICE pairing, byte-level =="

  -- 1. STUN server-reflexive discovery over real bytes ----------------------
  let txid := demoTxid
  let src := demoSrc
  let reqBytes := bindingReq txid
  IO.println s!"\n-- STUN Binding request (client) --"
  IO.println s!"txid                     : {toHex txid}"
  IO.println s!"request ({reqBytes.length}B)             : {toHex reqBytes}"

  -- reflector observes src and responds with XOR-MAPPED-ADDRESS
  let some respBytes := Stun.respond reqBytes src
    | do IO.eprintln "reflector: respond produced no reply"; return 1
  IO.println s!"\n-- STUN Binding success (reflector saw {dot4 src.addr}:{src.port}) --"
  IO.println s!"response ({respBytes.length}B)            : {toHex respBytes}"

  -- client parses + runs the PROVEN DISCO STUN->candidate bridge
  let some m := Stun.parse respBytes
    | do IO.eprintln "client: response did not parse"; return 1
  let discovered := Disco.reflexiveEndpoint m
  let expected := some (Disco.endpointOfStun src)
  IO.println s!"\n-- reflexiveEndpoint (Disco.reflexiveEndpoint over the wire bytes) --"
  IO.println s!"discovered candidate     : {repr discovered}"
  IO.println s!"endpointOfStun src       : {repr expected}"
  let discoveryFaithful := discovered == expected
  IO.println s!"reflexiveEndpoint == endpointOfStun src (realizes disco_path_faithful) : {discoveryFaithful}"

  -- negative: a request carrying an unknown comprehension-required attr -> 420,
  -- and 420 carries no XOR-MAPPED so reflexiveEndpoint refuses it.
  let badReq := Stun.encode Stun.bindingRequest txid [⟨0x0099, [0xaa, 0xbb]⟩]
  let some errBytes := Stun.respond badReq src
    | do IO.eprintln "reflector: no reply to unknown-attr request"; return 1
  let errRefl := (Stun.parse errBytes).bind Disco.reflexiveEndpoint
  IO.println s!"\n-- negative: unknown comprehension-required attr -> 420, no reflexive addr --"
  IO.println s!"reflexiveEndpoint on 420 : {repr errRefl}  (must be none)"
  let errRefused := errRefl == none

  -- 2. DISCO CallMeMaybe rendezvous: the relayed candidate list -------------
  let cand1 : Stun.Bytes := (List.replicate 10 0) ++ [0xff, 0xff, 203, 0, 113, 7]  -- ::ffff:203.0.113.7
  let cand2 : Stun.Bytes := (List.replicate 10 0) ++ [0xff, 0xff, 198, 51, 100, 9] -- ::ffff:198.51.100.9
  let eps : List (Stun.Bytes × Nat) := [(cand1, 51820), (cand2, 3478)]
  let cmm := Disco.encodeCallMeMaybe eps
  let decoded := Disco.decodeDiscoMessage cmm
  IO.println s!"\n-- DISCO CallMeMaybe (candidate rendezvous, byte-level) --"
  IO.println s!"encodeCallMeMaybe ({cmm.length}B)   : {toHex cmm}"
  let cmmOk := decoded == some (.callMeMaybe eps)
  IO.println s!"decodeDiscoMessage == callMeMaybe eps (realizes disco_callmemaybe_roundtrip) : {cmmOk}"

  -- 3. DISCO endpoint FSM: a STUN-discovered candidate seeds `unprobed`,
  --    and is NOT yet a usable path (anti-spoof: needs a Pong).
  let cfg : Disco.Config := { authPong := fun _ _ => false }
  let some ep := discovered
    | do IO.eprintln "no discovered endpoint to seed"; return 1
  let seeded := (Disco.step cfg Disco.init (.addCandidate ep)).1
  let seededState := Disco.lookup seeded.eps ep
  let usePathOut := (Disco.step cfg seeded .selectPath).2
  IO.println s!"\n-- DISCO endpoint FSM (path still needs a Pong) --"
  IO.println s!"lookup after addCandidate: {repr seededState}  (expect unprobed)"
  IO.println s!"selectPath outputs       : {repr usePathOut}  (expect [] — not yet usable)"
  let seededUnprobed := seededState == some Disco.EpState.unprobed
  let notYetUsable := usePathOut.isEmpty

  -- 4. ICE candidate pairing (RFC 8445) -------------------------------------
  let hostCand : Ice.Cand := { type := .host, localPref := 65535, component := 1 }
  let srflxCand : Ice.Cand := { type := .serverReflexive, localPref := 65535, component := 1 }
  let pairs := Ice.formPairs [hostCand] [srflxCand]
  IO.println s!"\n-- ICE candidate pairing (RFC 8445 §6.1.2) --"
  IO.println s!"formPairs                : {pairs.length} pair(s), all frozen/un-nominated"
  IO.println s!"host priority > srflx    : {decide (srflxCand.priority < hostCand.priority)}  (priority_type_dominates)"
  let prioOrdered := decide (srflxCand.priority < hostCand.priority)

  -- drive one pair through the connectivity checklist FSM
  let p0 : Ice.Pair := { state := .frozen, nominated := false }
  let p1 := Ice.stepPair p0 .unfreeze        -- waiting
  let p2 := Ice.stepPair p1 .perform          -- inProgress
  let p3 := Ice.stepPair p2 .checkSucceeded   -- succeeded
  let p4 := Ice.nominate p3                    -- nominated succeeded
  IO.println s!"pair FSM frozen -> {repr p1.state} -> {repr p2.state} -> {repr p3.state}"
  IO.println s!"mayDeliver inProgress    : {Ice.mayDeliver p2}  (must be false — no send before succeeded)"
  IO.println s!"mayDeliver succeeded+nom : {Ice.mayDeliver p4}  (send gate open)"
  IO.println s!"classify [p4]            : {repr (Ice.classify [p4])}  (expect completed)"
  let gateClosedEarly := Ice.mayDeliver p2 == false
  let gateOpen := Ice.mayDeliver p4 == true
  let completed := Ice.classify [p4] == Ice.Checklist.completed

  -- 5. ICE §7.2.2 connectivity-check request wire (pure-Lean HMAC-SHA1 / CRC-32)
  let check := Ice.checkRequest demoPwd txid demoUser demoPrio true demoTie true
  let miOk := Stun.messageIntegrityOk demoPwd check
  let fpOk := Stun.fingerprintOk check
  IO.println s!"\n-- ICE connectivity-check Binding request (RFC 8445 §7.2.2) --"
  IO.println s!"checkRequest ({check.length}B)       : {toHex check}"
  IO.println s!"messageIntegrityOk       : {miOk}  (realizes ice_check_verifies)"
  IO.println s!"fingerprintOk            : {fpOk}"

  let allOk := discoveryFaithful && errRefused && cmmOk && seededUnprobed
    && notYetUsable && prioOrdered && gateClosedEarly && gateOpen && completed
    && miOk && fpOk
  if allOk then do
    IO.println "\nPASS — reflexive path discovered from real STUN bytes and it equals the model;"
    IO.println "       CallMeMaybe candidates round-trip; the DISCO candidate is seeded but gated;"
    IO.println "       ICE pairs form, the checklist FSM opens the send gate only after success,"
    IO.println "       and the connectivity-check request is integrity/fingerprint sound."
    IO.println "FULL MESH PATH-DISCOVERY COMPLETE (drorb-native, byte-level, verified codec+FSM)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the discovery/pairing pipeline did not cross-check."
    return 1

/-! ## Real interop: STUN-over-TCP to an external reflector (named residual)

RFC 5389 §7.2.2 permits STUN over TCP; the message self-delimits via its length
field. This drives the SAME proven `bindingReq` builder and `Disco.reflexiveEndpoint`
against a real reflector over `ffi/derp_net.c`. Residual: needs a reachable STUN
server that speaks STUN-over-TCP. -/

def recvTimeout : UInt32 := 10000

def probe (server : String) (port : UInt16) : IO UInt32 := do
  let txid := demoTxid
  let reqBytes := bindingReq txid
  IO.println s!"== disco-mesh-live probe : STUN Binding to {server}:{port} over TCP =="
  let fd ← tcpConnect server port
  IO.println "connected (real TCP)."
  tcpSend fd (baOfBytes reqBytes)
  IO.println s!"sent Binding request ({reqBytes.length}B)."
  -- STUN header is 20 bytes: 2 type, 2 length, 4 cookie, 12 txid.
  let some hdr ← tcpRecvExact fd 20 recvTimeout
    | do IO.eprintln "no STUN header from reflector"; tcpClose fd; return 1
  let bodyLen := (hdr.get! 2).toNat * 256 + (hdr.get! 3).toNat
  let some body ← tcpRecvExact fd (UInt32.ofNat bodyLen) recvTimeout
    | do IO.eprintln "short STUN body from reflector"; tcpClose fd; return 1
  tcpClose fd
  let respBytes := bytesOfBa hdr ++ bytesOfBa body
  IO.println s!"received response ({respBytes.length}B): {toHex respBytes}"
  match (Stun.parse respBytes).bind Disco.reflexiveEndpoint with
  | some ep =>
    IO.println s!"reflexive candidate      : {repr ep}"
    IO.println "DONE — real reflector reply decoded by the proven discovery pipeline."
    return 0
  | none => do
    IO.eprintln "no reflexive address extracted (parse/decode refused — see model soundness)"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | ["probe", server, portS] =>
    match portS.toNat? with
    | some p => probe server p.toUInt16
    | none => do IO.eprintln "probe <server> <port>: bad port"; return 1
  | _ => do
    IO.eprintln "usage: disco-mesh-live selftest | probe <server> <port>"
    return 1

end DiscoMeshLive

def main (args : List String) : IO UInt32 := DiscoMeshLive.main args
