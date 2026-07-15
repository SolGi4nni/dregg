import Reactor.Pipeline

/-!
# Reactor.Stage.AltSvc — RFC 7838 `Alt-Svc` (the HTTP/3 alternative-service
advertisement response header — a genuine serve gap)

RFC 7838 (`Alt-Svc`): an origin advertises that the SAME resources are reachable
over an alternative protocol/authority, so a client that arrived over HTTP/1.1 or
HTTP/2 can transparently upgrade its next requests to HTTP/3 (QUIC).
`Alt-Svc: h3=":443"; ma=86400` says "an HTTP/3 endpoint is available on UDP port
443; cache this for 86400 s". This is exactly the header nginx/Caddy/Cloudflare
emit over the TCP listener to steer clients onto the co-located QUIC listener — the
ONLY standards-track way an h3 endpoint gets discovered (there is no h3 without it,
absent DNS HTTPS/SVCB).

## Ground truth — the deployed serve emits no Alt-Svc

drorb's dataplane binds a UDP `HOST:PORT` for the QUIC/HTTP-3 datagram path
alongside the TCP listener (`crates/dataplane/src/main.rs`: `--udp` / `DRORB_UDP`,
default = same HOST:PORT as the TCP bind), but the TCP responses carry NO `Alt-Svc`,
so no client is ever told the h3 endpoint exists. This module adds the missing
advertisement as a response-phase `Stage`.

## Behaviour

Append `Alt-Svc: h3=":443"; ma=86400` unless an `Alt-Svc` header is already present
(case-insensitive) — an upstream's own advertisement is never overridden or
duplicated.

## What is proved (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound})

* `stampAlt_has` — after stamping, an `Alt-Svc` field is present, for ANY header list.
* `stampAlt_noop` — a list already carrying `Alt-Svc` is returned UNCHANGED.
* `stampAlt_prefix` — stamping only appends (original headers preserved as a prefix).
* `stampAlt_idem` — idempotent (no double-decoration on re-entry).
* `altVal_shape` — the value is the h3 alt-service `h3=":443"` with a `; ma=86400`
  max-age parameter (the RFC 7838 `alt-value ; parameter` grammar), structurally.
* `altStage_effect` — the stage maps `stampAlt` over the finalized headers.
* `altStage_response_has_alt` — every response through the stage carries `Alt-Svc`.
* `altStage_statusStable` — never touches the status (safe to braid).
* `demo_stamps` / `demo_no_double` — concrete non-vacuous witnesses.

Residual (named): wire into `deployStagesFull2` + curl (dataplane rebuild deferred);
the advertisement is honest ONLY when the co-located UDP/QUIC listener is actually
up (deployment-configured) — this stage emits the header; whether h3 is reachable
is the UDP-bind's concern. Also: the `Alt-Svc: clear` retraction form, and
per-connection `ma` tuning (this stage takes the fixed `h3=":443"; ma=86400` form).
-/

namespace Reactor.Stage.AltSvc

open Reactor.Pipeline
open Proto (Bytes Request)

/-! ## Case-insensitive field-name match -/

/-- ASCII-lowercase one byte. -/
def lowerByte (b : UInt8) : UInt8 := if 65 ≤ b && b ≤ 90 then b + 32 else b

/-- ASCII-lowercase a byte string. -/
def lower (bs : Bytes) : Bytes := bs.map lowerByte

/-- Lowercase field-name token `"alt-svc"`. -/
def altTok : Bytes := [97, 108, 116, 45, 115, 118, 99]

/-- Is this field name `Alt-Svc` (case-insensitive)? -/
def isAlt (name : Bytes) : Bool := lower name == altTok

/-! ## The emitted field -/

/-- The emitted field name `"Alt-Svc"`. -/
def altName : Bytes := [65, 108, 116, 45, 83, 118, 99]

/-- The advertised alt-service value `h3=":443"` (protocol-id `h3`, authority
`:443` = same host, UDP port 443). -/
def altService : Bytes := [104, 51, 61, 34, 58, 52, 52, 51, 34]

/-- The `; ` parameter separator. -/
def paramSep : Bytes := [59, 32]

/-- The max-age parameter `ma=86400` (cache the advertisement one day). -/
def maParam : Bytes := [109, 97, 61, 56, 54, 52, 48, 48]

/-- The emitted value `"h3=":443"; ma=86400"`. -/
def altVal : Bytes := altService ++ paramSep ++ maParam

/-- **RFC 7838 grammar.** The emitted value is an `alt-value` (`h3=":443"`) followed
by a `; ` and the `ma` (max-age) parameter — `alt-value *( OWS ";" OWS parameter )`. -/
theorem altVal_shape : altVal = altService ++ paramSep ++ maParam := rfl

/-- The emitted name matches its own detector (self-recognizing; kernel-decided). -/
theorem altName_isAlt : isAlt altName = true := by decide

/-! ## The stamp -/

/-- Does the header list already carry an `Alt-Svc` field (case-insensitive)? -/
def hasAlt (hs : List (Bytes × Bytes)) : Bool := hs.any (fun nv => isAlt nv.1)

/-- **Stamp `Alt-Svc`.** Append `Alt-Svc: h3=":443"; ma=86400` unless one is present. -/
def stampAlt (hs : List (Bytes × Bytes)) : List (Bytes × Bytes) :=
  if hasAlt hs then hs else hs ++ [(altName, altVal)]

/-- The appended entry is seen by the detector, whatever precedes it. -/
theorem hasAlt_append (hs : List (Bytes × Bytes)) :
    hasAlt (hs ++ [(altName, altVal)]) = true := by
  unfold hasAlt
  rw [List.any_append]
  have hlast : List.any [(altName, altVal)] (fun nv => isAlt nv.1) = true := by decide
  rw [hlast, Bool.or_true]

/-- **Presence.** After stamping, an `Alt-Svc` field is present — for ANY header list. -/
theorem stampAlt_has (hs : List (Bytes × Bytes)) : hasAlt (stampAlt hs) = true := by
  unfold stampAlt
  by_cases h : hasAlt hs = true
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact hasAlt_append hs

/-- **No duplication.** A list already carrying `Alt-Svc` is returned UNCHANGED. -/
theorem stampAlt_noop (hs : List (Bytes × Bytes)) (h : hasAlt hs = true) :
    stampAlt hs = hs := by
  unfold stampAlt; rw [if_pos h]

/-- **Append-only.** The original headers are a prefix of the stamped list. -/
theorem stampAlt_prefix (hs : List (Bytes × Bytes)) : hs <+: stampAlt hs := by
  unfold stampAlt
  by_cases h : hasAlt hs = true
  · rw [if_pos h]; exact List.prefix_refl hs
  · rw [if_neg h]; exact List.prefix_append hs _

/-- **Idempotence.** Stamping a stamped list changes nothing. -/
theorem stampAlt_idem (hs : List (Bytes × Bytes)) :
    stampAlt (stampAlt hs) = stampAlt hs :=
  stampAlt_noop _ (stampAlt_has hs)

/-! ## The stage -/

/-- **The `Alt-Svc` stage.** Request phase: pass through. Response phase: advertise
the h3 endpoint on the finalized headers. Never gates. -/
def altStage : Stage where
  name := "alt-svc"
  onRequest := fun c => .continue c
  onResponse := fun _ b => b.mapResp (fun r => { r with headers := stampAlt r.headers })

/-- **The byte-effect.** The stage maps `stampAlt` over the finalized response's
headers, for ANY tail and handler. -/
theorem altStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    ((runPipeline (altStage :: rest) h c).build).headers
      = stampAlt ((runPipeline rest h c).build).headers := by
  rw [pipeline_stage_effect altStage rest h c c rfl]
  rfl

/-- Every response through the stage carries `Alt-Svc` — for ANY tail and handler. -/
theorem altStage_response_has_alt (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    hasAlt ((runPipeline (altStage :: rest) h c).build).headers = true := by
  rw [altStage_effect]; exact stampAlt_has _

/-- The stage never changes the status — safe to braid into a status-stable onion. -/
theorem altStage_statusStable : altStage.statusStable := fun _ _ => rfl

/-! ## End-to-end witnesses (non-vacuous) -/

/-- A bare 200 with one unrelated header (`X: Y`). -/
def bareHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [], headers := [([88], [89])], body := [] }

/-- A response already carrying an upstream `Alt-Svc` (lowercase name, value
`h2=":443"`). -/
def upstreamAltHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [],
             headers := [(altTok, [104, 50, 61, 34, 58, 52, 52, 51, 34])], body := [] }

/-- An empty request context. -/
def demoCtx : Ctx := { input := [], req := {}, attrs := [] }

/-- **End-to-end.** The single-stage pipeline serves the bare 200 with EXACTLY the
original header followed by `Alt-Svc: h3=":443"; ma=86400`. -/
theorem demo_stamps :
    ((runPipeline [altStage] bareHandler demoCtx).build).headers
      = [([88], [89]), (altName, altVal)] := by decide

/-- **End-to-end, no duplication.** A response already carrying `Alt-Svc` passes
through byte-identical. -/
theorem demo_no_double :
    ((runPipeline [altStage] upstreamAltHandler demoCtx).build).headers
      = [(altTok, [104, 50, 61, 34, 58, 52, 52, 51, 34])] := by decide

#print axioms Reactor.Stage.AltSvc.stampAlt_has
#print axioms Reactor.Stage.AltSvc.stampAlt_noop
#print axioms Reactor.Stage.AltSvc.stampAlt_prefix
#print axioms Reactor.Stage.AltSvc.stampAlt_idem
#print axioms Reactor.Stage.AltSvc.altVal_shape
#print axioms Reactor.Stage.AltSvc.altStage_effect
#print axioms Reactor.Stage.AltSvc.altStage_response_has_alt
#print axioms Reactor.Stage.AltSvc.altStage_statusStable
#print axioms Reactor.Stage.AltSvc.demo_stamps
#print axioms Reactor.Stage.AltSvc.demo_no_double

end Reactor.Stage.AltSvc
