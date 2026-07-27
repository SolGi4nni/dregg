import Reactor.Pipeline

/-!
# Reactor.Stage.VaryEncoding — RFC 9110 §12.5.5 `Vary: Accept-Encoding`
(the content-negotiation cache key the deployed serve never names — a genuine gap)

The deployed serve NEGOTIATES on `Accept-Encoding`: the gzip stage rewrites a
`200` body into a coded representation exactly when the request advertises
`gzip`. Two requests for the same target can therefore receive DIFFERENT
representations keyed on a request header — which is precisely the situation
RFC 9110 §12.5.5 obliges the origin to declare: a response subject to proactive
negotiation SHOULD carry `Vary` naming the request fields that selected the
representation, or a shared cache serving both clients will hand the gzip bytes
to a client that never accepted them (response corruption at the cache, not at
this origin).

## Ground truth — the deployed serve emits no `Vary`

curl against the running default serve (2026-07-12): `GET /static/app.js`
answers `200` with `ETag`/`Accept-Ranges`/`Content-Type` and — with
`Accept-Encoding: gzip` — a `Content-Encoding: gzip` rewrite, but NO `Vary` on
either response. This module adds the missing declaration as a response-phase
`Stage`.

## Behaviour

Append `Vary: Accept-Encoding` unless a `Vary` header is already present
(case-insensitive) — an upstream's own (possibly wider) `Vary` is never
overridden or duplicated.

## What is proved (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound})

* `stampVary_has` — after stamping, a `Vary` field is present, for ANY header list.
* `stampVary_noop` — a list already carrying `Vary` is returned UNCHANGED.
* `stampVary_prefix` — stamping only appends (original headers preserved as a prefix).
* `stampVary_idem` — idempotent (no double-decoration on re-entry).
* `varyStage_effect` — the stage maps `stampVary` over the finalized headers.
* `varyStage_response_has_vary` — every response through the stage carries `Vary`.
* `varyStage_statusStable` — never touches the status (safe to braid).
* `demo_stamps` / `demo_no_double` — concrete non-vacuous witnesses.

Residual (named): the emitted field names only `Accept-Encoding` (the one field
the deployed fold genuinely negotiates on); a route that later negotiates on
`Accept-Language`/`Accept` needs the wider list, and the deployed variants stage's
own selections are its concern.
-/

namespace Reactor.Stage.VaryEncoding

open Reactor.Pipeline
open Proto (Bytes Request)

/-! ## Case-insensitive field-name match -/

/-- ASCII-lowercase one byte. -/
def lowerByte (b : UInt8) : UInt8 := if 65 ≤ b && b ≤ 90 then b + 32 else b

/-- ASCII-lowercase a byte string. -/
def lower (bs : Bytes) : Bytes := bs.map lowerByte

/-- Lowercase field-name token `"vary"`. -/
def varyTok : Bytes := [118, 97, 114, 121]

/-- Is this field name `Vary` (case-insensitive)? -/
def isVary (name : Bytes) : Bool := lower name == varyTok

/-! ## The emitted field -/

/-- The emitted field name `"Vary"`. -/
def varyName : Bytes := [86, 97, 114, 121]

/-- The emitted value `"Accept-Encoding"` — the request field the deployed gzip
negotiation genuinely selects the representation on. -/
def aeVal : Bytes :=
  [65, 99, 99, 101, 112, 116, 45, 69, 110, 99, 111, 100, 105, 110, 103]

/-- The emitted name matches its own detector (self-recognizing; kernel-decided). -/
theorem varyName_isVary : isVary varyName = true := by decide

/-! ## The stamp -/

/-- Does the header list already carry a `Vary` field (case-insensitive)? -/
def hasVary (hs : List (Bytes × Bytes)) : Bool := hs.any (fun nv => isVary nv.1)

/-- **Stamp `Vary`.** Append `Vary: Accept-Encoding` unless one is present. -/
def stampVary (hs : List (Bytes × Bytes)) : List (Bytes × Bytes) :=
  if hasVary hs then hs else hs ++ [(varyName, aeVal)]

/-- The appended entry is seen by the detector, whatever precedes it. -/
theorem hasVary_append (hs : List (Bytes × Bytes)) :
    hasVary (hs ++ [(varyName, aeVal)]) = true := by
  unfold hasVary
  rw [List.any_append]
  have hlast : List.any [(varyName, aeVal)] (fun nv => isVary nv.1) = true := by decide
  rw [hlast, Bool.or_true]

/-- **Presence.** After stamping, a `Vary` field is present — for ANY header list. -/
theorem stampVary_has (hs : List (Bytes × Bytes)) : hasVary (stampVary hs) = true := by
  unfold stampVary
  by_cases h : hasVary hs = true
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact hasVary_append hs

/-- **No duplication.** A list already carrying `Vary` is returned UNCHANGED. -/
theorem stampVary_noop (hs : List (Bytes × Bytes)) (h : hasVary hs = true) :
    stampVary hs = hs := by
  unfold stampVary; rw [if_pos h]

/-- **Append-only.** The original headers are a prefix of the stamped list. -/
theorem stampVary_prefix (hs : List (Bytes × Bytes)) : hs <+: stampVary hs := by
  unfold stampVary
  by_cases h : hasVary hs = true
  · rw [if_pos h]; exact List.prefix_refl hs
  · rw [if_neg h]; exact List.prefix_append hs _

/-- **Idempotence.** Stamping a stamped list changes nothing. -/
theorem stampVary_idem (hs : List (Bytes × Bytes)) :
    stampVary (stampVary hs) = stampVary hs :=
  stampVary_noop _ (stampVary_has hs)

/-! ## The stage -/

/-- **The `Vary` stage.** Request phase: pass through. Response phase: declare the
negotiated request field on the finalized headers. Never gates. -/
def varyStage : Stage where
  name := "vary-encoding"
  onRequest := fun c => .continue c
  onResponse := fun _ b => b.mapResp (fun r => { r with headers := stampVary r.headers })

/-- **The byte-effect.** The stage maps `stampVary` over the finalized response's
headers, for ANY tail and handler. -/
theorem varyStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    ((runPipeline (varyStage :: rest) h c).build).headers
      = stampVary ((runPipeline rest h c).build).headers := by
  rw [pipeline_stage_effect varyStage rest h c c rfl]
  rfl

/-- Every response through the stage carries `Vary` — for ANY tail and handler. -/
theorem varyStage_response_has_vary (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    hasVary ((runPipeline (varyStage :: rest) h c).build).headers = true := by
  rw [varyStage_effect]; exact stampVary_has _

/-- The stage never changes the status — safe to braid into a status-stable onion. -/
theorem varyStage_statusStable : varyStage.statusStable := fun _ _ => rfl

/-! ## End-to-end witnesses (non-vacuous) -/

/-- A bare 200 with one unrelated header (`X: Y`). -/
def bareHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [], headers := [([88], [89])], body := [] }

/-- A response already carrying an upstream `Vary` (lowercase name, value `*`). -/
def upstreamVaryHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [],
             headers := [(varyTok, [42])], body := [] }

/-- An empty request context. -/
def demoCtx : Ctx := { input := [], req := {}, attrs := [] }

/-- **End-to-end.** The single-stage pipeline serves the bare 200 with EXACTLY the
original header followed by `Vary: Accept-Encoding`. -/
theorem demo_stamps :
    ((runPipeline [varyStage] bareHandler demoCtx).build).headers
      = [([88], [89]), (varyName, aeVal)] := by decide

/-- **End-to-end, no duplication.** A response already carrying `Vary` passes
through byte-identical. -/
theorem demo_no_double :
    ((runPipeline [varyStage] upstreamVaryHandler demoCtx).build).headers
      = [(varyTok, [42])] := by decide

#print axioms Reactor.Stage.VaryEncoding.stampVary_has
#print axioms Reactor.Stage.VaryEncoding.stampVary_noop
#print axioms Reactor.Stage.VaryEncoding.stampVary_prefix
#print axioms Reactor.Stage.VaryEncoding.stampVary_idem
#print axioms Reactor.Stage.VaryEncoding.varyStage_effect
#print axioms Reactor.Stage.VaryEncoding.varyStage_response_has_vary
#print axioms Reactor.Stage.VaryEncoding.varyStage_statusStable
#print axioms Reactor.Stage.VaryEncoding.demo_stamps
#print axioms Reactor.Stage.VaryEncoding.demo_no_double

end Reactor.Stage.VaryEncoding
