import Reactor.Pipeline
import Proxy.ProxyProtocol

/-!
# Reactor.Stage.ProxyProtocol — real-client-address recovery, as a pipeline stage (pk.18)

A load balancer that terminates the client TCP connection and dials a fresh backend
connection hides the real client behind its own address. The PROXY protocol restores
it: the balancer prepends a small header — the FIRST bytes on the backend connection,
ahead of any HTTP — carrying the original `(source, destination)` socket addresses.

The proven codec `Proxy.ProxyProtocol` (v1 text + v2 binary parsers, with the
address-recovery theorems `proxy_proto_v1_parse` / `proxy_proto_v2_parse` /
`proxy_proto_recovers_client`) was a MISSING-row leaf: the parser was proven but no
served path reached it (`[proven leaf, inert: proxy_proto_v1/v2_parse]`). This module
WIRES it as a byte-driving `Stage` for the deployed serve fold.

Behaviour: the request phase reads the raw input bytes (`Ctx.input`, the first bytes on
the connection), tries the v1 then the v2 parser, and — when a header is present and
carries an IPv4 client source — stashes the recovered dotted-quad address under
`clientKey` for upstream propagation. The response phase stamps it as
`X-Forwarded-For: <client-ip>` so a downstream proxy pass / access log keys on the REAL
client, not the balancer's peer address. A request with no PROXY preamble (or a
non-IPv4 source) is a pure pass-through — no header is added (default-safe: the stage
never invents a client identity).

## What is proved

* `recover_sampleV1` — the canonical on-the-wire v1 line
  `PROXY TCP4 192.168.1.1 10.0.0.1 12345 80\r\n` recovers exactly the dotted-quad
  `192.168.1.1` (kernel-decided over the real parser + renderer).
* `proxyProtoStage_stamps` — for ANY tail/handler, when the raw input recovers a client
  IP the FINALIZED response the serializer renders carries `(X-Forwarded-For, ip)`. The
  recovered address genuinely reaches the wire.
* `proxyProtoStage_passthrough` — with no recoverable client, the request phase passes
  the context through UNCHANGED and the response phase is the identity (no header
  invented).
* `demo_stamps` — the assembled single-stage pipeline on the canonical v1 vector emits
  `X-Forwarded-For: 192.168.1.1` (a concrete, non-vacuous end-to-end witness).

## Boundary

Only IPv4 sources are rendered (v1 `TCP4` and v2 IPv4 — the parser's fully-modeled
cases); a v6 source is recovered by the codec but not stamped here (`renderClient`
returns `none`), the same boundary the codec draws. Textual `TCP6` v1 is already
`unsupportedV1Family` upstream.
-/

namespace Reactor.Stage.ProxyProtocol

open Reactor.Pipeline
open Proto (Bytes Request)
open Proxy.ProxyProtocol (IpAddr SockAddr Header ParseResult parseV1 parseV2 clientAddr)

/-! ## Rendering a recovered IPv4 address as a dotted-quad ASCII string -/

/-- A single ASCII decimal digit for `n % 10`. -/
def digit (n : Nat) : UInt8 := (48 + n % 10).toUInt8

/-- Render a byte value (`0`–`255`) as its ASCII decimal, no leading zeros. -/
def decByte (n : Nat) : Bytes :=
  if n < 10 then [digit n]
  else if n < 100 then [digit (n / 10), digit n]
  else [digit (n / 100), digit (n / 10 % 10), digit n]

/-- ASCII `'.'`. -/
def dot : UInt8 := 46

/-- Render an IPv4 address as a dotted-quad ASCII byte string. -/
def renderV4 (a b c d : UInt8) : Bytes :=
  decByte a.toNat ++ [dot] ++ decByte b.toNat ++ [dot]
    ++ decByte c.toNat ++ [dot] ++ decByte d.toNat

/-- Render a recovered socket address' IP to an ASCII string — IPv4 only (a v6
source is recovered by the codec but not rendered here, the codec's own boundary). -/
def renderClient (s : SockAddr) : Option Bytes :=
  match s.ip with
  | .v4 a b c d => some (renderV4 a b c d)
  | .v6 _       => none

/-! ## Recovering the client address off the raw input -/

/-- The parsed PROXY header at the head of the input, trying v1 (text) then v2
(binary). `none` when neither parser completes. -/
def parseHeader (input : Bytes) : Option Header :=
  match parseV1 input with
  | .complete h _ => some h
  | _ =>
    match parseV2 input with
    | .complete h _ => some h
    | _ => none

/-- The recovered client IP as an ASCII dotted-quad, if the input carries a PROXY
header with an IPv4 source. -/
def recoverClient (input : Bytes) : Option Bytes :=
  match parseHeader input with
  | some h =>
    match clientAddr h with
    | some sa => renderClient sa
    | none    => none
  | none => none

/-! ## The stage -/

/-- The attribute key the recovered client IP is stashed under for upstream
propagation. -/
def clientKey : String := "proxyproto.client"

/-- The response header name carrying the recovered client (`X-Forwarded-For`). -/
def xffName : Bytes := "X-Forwarded-For".toUTF8.toList

/-- **The PROXY-protocol stage.** Request phase: recover the client IP from the raw
input and stash it under `clientKey` (so an upstream proxy pass / access log keys on
it); a request with no recoverable client passes through unchanged. Response phase:
stamp the stashed IP as `(xffName, ip)`. Default-safe — it never gates and never
invents a client identity. -/
def proxyProtoStage : Stage where
  name := "proxy-protocol"
  onRequest := fun c =>
    match recoverClient c.input with
    | some ip => .continue { c with attrs := (clientKey, ip) :: c.attrs }
    | none    => .continue c
  onResponse := fun c b =>
    match c.attrs.find? (fun p => p.1 == clientKey) with
    | some p => b.addHeader (xffName, p.2)
    | none   => b

/-! ## Concrete recovery — the canonical v1 vector -/

/-- The ASCII dotted-quad `"192.168.1.1"` as explicit bytes (a `decide`-reducible RHS —
`String.toUTF8` is `@[extern]` and does not reduce in the kernel). -/
def expectedIp : Bytes := [49, 57, 50, 46, 49, 54, 56, 46, 49, 46, 49]

/-- The canonical v1 line recovers exactly `192.168.1.1` (kernel-decided over the real
parser + renderer). Non-vacuous: an on-the-wire byte vector yields the dotted-quad. -/
theorem recover_sampleV1 :
    recoverClient Proxy.ProxyProtocol.sampleV1 = some expectedIp := by
  decide

/-! ## The byte-effect — the recovered client reaches the wire -/

/-- The enriched context after the request phase stashes the recovered IP. -/
def enriched (c : Ctx) (ip : Bytes) : Ctx := { c with attrs := (clientKey, ip) :: c.attrs }

/-- When the input recovers `ip`, the request phase continues to the enriched context. -/
theorem onReq_enriched (c : Ctx) (ip : Bytes) (h : recoverClient c.input = some ip) :
    proxyProtoStage.onRequest c = .continue (enriched c ip) := by
  have hu : proxyProtoStage.onRequest c
      = (match recoverClient c.input with
         | some ip => StageStep.continue { c with attrs := (clientKey, ip) :: c.attrs }
         | none    => .continue c) := rfl
  simp only [hu, h, enriched]

/-- On the enriched context, the response phase finds the stashed IP and stamps it. -/
theorem onResp_enriched (c : Ctx) (ip : Bytes) (b : ResponseBuilder) :
    proxyProtoStage.onResponse (enriched c ip) b = b.addHeader (xffName, ip) := by
  have hu : proxyProtoStage.onResponse (enriched c ip) b
      = (match ((clientKey, ip) :: c.attrs).find? (fun p => p.1 == clientKey) with
         | some p => b.addHeader (xffName, p.2)
         | none   => b) := rfl
  rw [hu]; simp [List.find?]

/-- **The byte-effect.** For ANY tail and handler, when the raw input recovers a client
IP the FINALIZED response the serializer renders carries `(X-Forwarded-For, ip)` — the
recovered address genuinely reaches the wire. -/
theorem proxyProtoStage_stamps (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (ip : Bytes) (hrec : recoverClient c.input = some ip) :
    (xffName, ip) ∈ ((runPipeline (proxyProtoStage :: rest) h c).build).headers := by
  rw [pipeline_stage_effect proxyProtoStage rest h c (enriched c ip) (onReq_enriched c ip hrec),
      onResp_enriched, build_addHeader]
  simp

/-- **Default-safe pass-through (request phase).** With no recoverable client, the
request phase passes the context through UNCHANGED. -/
theorem proxyProtoStage_passthrough (c : Ctx) (h : recoverClient c.input = none) :
    proxyProtoStage.onRequest c = .continue c := by
  have hu : proxyProtoStage.onRequest c
      = (match recoverClient c.input with
         | some ip => StageStep.continue { c with attrs := (clientKey, ip) :: c.attrs }
         | none    => .continue c) := rfl
  rw [hu, h]

/-- **Default-safe pass-through (response phase).** With no stashed client key, the
response phase is the identity — no header is invented. -/
theorem proxyProtoStage_no_invent (c : Ctx) (b : ResponseBuilder)
    (h : c.attrs.find? (fun p => p.1 == clientKey) = none) :
    proxyProtoStage.onResponse c b = b := by
  have hu : proxyProtoStage.onResponse c b
      = (match c.attrs.find? (fun p => p.1 == clientKey) with
         | some p => b.addHeader (xffName, p.2)
         | none   => b) := rfl
  rw [hu, h]

/-! ## End-to-end witness -/

/-- A context whose raw input is the canonical v1 line. -/
def demoCtx : Ctx := { input := Proxy.ProxyProtocol.sampleV1, req := {}, attrs := [] }

/-- A trivial `200` handler. -/
def okHandler : Ctx → Response := fun _ => { status := 200, reason := [], headers := [], body := [] }

/-- **End-to-end.** The assembled single-stage pipeline on the canonical v1 vector emits
`X-Forwarded-For: 192.168.1.1` in the finalized response — a concrete, non-vacuous
witness that the recovered client reaches the served bytes. -/
theorem demo_stamps :
    (xffName, expectedIp)
      ∈ ((runPipeline [proxyProtoStage] okHandler demoCtx).build).headers :=
  proxyProtoStage_stamps [] okHandler demoCtx _ recover_sampleV1

end Reactor.Stage.ProxyProtocol
