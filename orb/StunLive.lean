/-
# StunLive — driving the PROVEN STUN Binding server over a real UDP socket

`Stun.respond` is sans-IO: given the request bytes and the source transport address it
computes the exact reply bytes as a pure function, and `Stun.respond_success_correct`
proves that reply parses as a Binding success, echoes the transaction id, verifies its
FINGERPRINT, and carries an XOR-MAPPED-ADDRESS that decodes back to **exactly** that
source. `Stun.respond_malformed` / `Stun.respond_only_requests` prove the two silence
cases. `StunTailscaleKat.real_netcheck_reflected` instantiates all of it on the 40 bytes
a stock `tailscale` 1.98.8 `netcheck` really sends.

This executable takes those decisions to a real socket. It does exactly three untrusted
things, and no more:

  * bind a UDP port and read one datagram (`drorb_udp_listen_addr` / `drorb_udp_recv`),
  * copy out the kernel's source address for that datagram (`drorb_udp_last_src`),
  * send back whatever `Stun.respond` returned (`drorb_udp_reply`).

It parses nothing, builds no STUN message, and holds no protocol state. Every byte a
client receives is `Stun.respond`'s output — including the decision to stay SILENT, which
is the proven behaviour on a malformed datagram or on anything that is not a Binding
request.

## Why a homelab tailnet needs this

A stock client cannot attempt a **direct** path unless it knows its own reflexive
transport address, and it learns that only by STUNning the DERP regions in the netmap the
coordinator served it. Absent a STUN service, `netcheck` reports `udp=false` and the
client's candidate set holds only local-interface addresses — so direct paths exist only
between peers that already share a link, and everything else falls back to the relay.
`Control.Join.derpMapToWireAtPortStun_stunPort` is the theorem that the served netmap
NAMES the port this binary binds.

Usage:
  stun-live server [port] [bindHost]   run the Binding server (default 3478, 0.0.0.0)
  stun-live selftest                   answer the REAL captured netcheck datagram, no sockets
-/
import Stun
import StunTailscaleKat

namespace StunLive

/-! ## The socket seam (untrusted FFI, ffi/wg_udp.c) -/

@[extern "drorb_udp_listen_addr"]
opaque udpListenAddr (host : String) (port : UInt16) : IO UInt32

@[extern "drorb_udp_recv"]
opaque udpRecv (fd : UInt32) (timeoutMs : UInt32) : IO (Option ByteArray)

/-- The source transport address of the last datagram received, as 4 address bytes then
the port big-endian. Pure copy-out of `recvfrom`'s source — it is `Stun.xorMappedValue`
that reflects it into the reply, never this shim. -/
@[extern "drorb_udp_last_src"]
opaque udpLastSrc (u : Unit) : IO (Option ByteArray)

@[extern "drorb_udp_reply"]
opaque udpReply (fd : UInt32) (payload : ByteArray) : IO Unit

@[extern "drorb_udp_close"]
opaque udpClose (fd : UInt32) : IO Unit

/-! ## Byte plumbing -/

def baOf (bs : Stun.Bytes) : ByteArray := ⟨bs.toArray⟩

/-- The 6 bytes `drorb_udp_last_src` hands back → the `Stun.Endpoint` the proven server
reflects. IPv4 only (`family = 1` is RFC 5389 §15.1's IPv4 family), which is what the
`drorb_udp_listen_addr` socket can ever receive. -/
def endpointOfSrc (b : ByteArray) : Option Stun.Endpoint :=
  if b.size = 6 then
    some { family := 1
         , port := (b.get! 4).toNat * 256 + (b.get! 5).toNat
         , addr := [b.get! 0, b.get! 1, b.get! 2, b.get! 3] }
  else none

def renderEp (e : Stun.Endpoint) : String :=
  match e.addr with
  | [a, b, c, d] => s!"{a.toNat}.{b.toNat}.{c.toNat}.{d.toNat}:{e.port}"
  | _ => s!"<{e.addr.length}-byte addr>:{e.port}"

/-! ## The server loop -/

def recvTimeout : UInt32 := 30000

/-- One service step: read a datagram, learn its source, and send back exactly what the
PROVEN `Stun.respond` returns — or nothing at all, which is `respond`'s proven answer to
a malformed datagram or a non-request (`Stun.respond_malformed`,
`Stun.respond_only_requests`). Returns the number of replies sent (0 or 1). -/
def serveOne (fd : UInt32) (verbose : Bool) : IO Nat := do
  match ← udpRecv fd recvTimeout with
  | none => return 0
  | some dg =>
    match ← udpLastSrc () with
    | none => do IO.eprintln "[stun] datagram with no recoverable IPv4 source; dropped"; return 0
    | some srcBytes =>
      match endpointOfSrc srcBytes with
      | none => do IO.eprintln "[stun] source address seam returned a bad shape; dropped"; return 0
      | some src =>
        -- ★ THE PROVEN DECISION. Nothing below computes a STUN byte.
        match Stun.respond dg.toList src with
        | none =>
            if verbose then
              IO.println s!"[stun] {dg.size}B from {renderEp src}: not a Binding request — SILENCE (respond_only_requests / respond_malformed)"
            return 0
        | some out =>
            udpReply fd (baOf out)
            if verbose then
              IO.println s!"[stun] {dg.size}B from {renderEp src} -> {out.length}B Binding response reflecting {renderEp src}"
            return 1

partial def serveLoop (fd : UInt32) (served : Nat) : IO Unit := do
  let n ← serveOne fd true
  serveLoop fd (served + n)

def server (bindHost : String) (port : UInt16) : IO UInt32 := do
  let fd ← udpListenAddr bindHost port
  IO.println s!"[stun] PERSISTENT STUN Binding server on {bindHost}:{port} (UDP)"
  IO.println "[stun] every reply is Stun.respond's output (respond_success_correct: the"
  IO.println "[stun] XOR-MAPPED-ADDRESS decodes back to exactly the request's source)"
  serveLoop fd 0
  udpClose fd
  return 0

/-! ## Selftest — the real captured netcheck datagram, no sockets -/

def selftest : IO UInt32 := do
  let src : Stun.Endpoint := { family := 1, port := 45992, addr := [192, 168, 50, 39] }
  IO.println "[stun] selftest: the REAL tailscale 1.98.8 netcheck Binding request"
  IO.println s!"[stun]   request : {StunTailscaleKat.realBindingRequest.length}B, source {renderEp src}"
  match Stun.respond StunTailscaleKat.realBindingRequest src with
  | none => do IO.eprintln "[stun] FAIL: proven server declined the real request"; return 1
  | some out =>
    match Stun.parse out with
    | none => do IO.eprintln "[stun] FAIL: reply does not parse"; return 1
    | some m =>
      let fpOk := Stun.fingerprintOk out
      let reflected :=
        (m.attrs.find? (fun a => a.type == Stun.attrXorMappedAddress)).bind
          (fun a => Stun.decodeXorMapped StunTailscaleKat.realTxid a.value)
      IO.println s!"[stun]   reply   : {out.length}B, type {m.typ} (0x101 = Binding success), txid echoed {m.txid == StunTailscaleKat.realTxid}, FINGERPRINT ok {fpOk}"
      match reflected with
      | some e =>
          IO.println s!"[stun]   reflected XOR-MAPPED-ADDRESS: {renderEp e}"
          if e == src && fpOk && m.typ == Stun.bindingSuccessType then
            IO.println "[stun] OK — matches StunTailscaleKat.real_netcheck_reflected"
            return 0
          else
            IO.eprintln "[stun] FAIL: reflection/type/fingerprint mismatch"; return 1
      | none => do IO.eprintln "[stun] FAIL: no XOR-MAPPED-ADDRESS in the reply"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["selftest"] => selftest
  | ["server"] => server "0.0.0.0" 3478
  | ["server", p] =>
      match p.toNat? with
      | some n => server "0.0.0.0" (UInt16.ofNat n)
      | none => do IO.eprintln "usage: stun-live server [port] [bindHost]"; return 2
  | ["server", p, h] =>
      match p.toNat? with
      | some n => server h (UInt16.ofNat n)
      | none => do IO.eprintln "usage: stun-live server [port] [bindHost]"; return 2
  | _ => do
      IO.eprintln "usage: stun-live selftest | stun-live server [port] [bindHost]"
      return 2

end StunLive

def main (args : List String) : IO UInt32 := StunLive.main args
