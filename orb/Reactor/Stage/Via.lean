import Reactor.Pipeline

/-!
# Reactor.Stage.Via — RFC 9110 §7.6.3 `Via` stamping, as a pipeline stage (px.1 residual)

RFC 9110 §7.6.3: an intermediary (gateway/proxy) MUST send a `Via` field in forwarded
messages, naming the protocol version it received the message with and a pseudonym —
the loop-detection / capability-discovery field every gateway in the reference class
stamps. The deployed drorb serve stamps `Server`, `x-upstream` and the security trio
but NO `Via` on ANY response.

## Ground truth — curl against the running dataplane (io_uring, port 8144, 2026-07-11)

```
$ curl -s -D - -o /dev/null http://127.0.0.1:8144/static/app.js
HTTP/1.1 200 OK
…
Server: drorb
x-upstream: 1572395042
Content-Length: 35            ← no Via, on the 200, the 206, and the 404 alike
```

This module adds the missing field as a response-phase `Stage`: append
`Via: 1.1 drorb` (received-protocol version + pseudonym) unless a `Via` is already
present (case-insensitive) — an upstream's own `Via` is never duplicated or rewritten.

## What is proved (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound})

* `stampVia_has` — after stamping, a `Via` field is present, for ANY header list.
* `stampVia_noop` — a header list that already carries a `Via` (case-insensitive) is
  returned UNCHANGED: an upstream `Via` is never duplicated.
* `stampVia_prefix` — stamping only appends: the original headers are a prefix of the
  result (no header is dropped, reordered, or rewritten).
* `stampVia_idem` — stamping is idempotent (no double-decoration on re-entry).
* `viaVal_shape` — the emitted value is exactly `received-protocol SP pseudonym`
  (`"1.1" ++ " " ++ "drorb"`), the RFC 9110 §7.6.3 grammar.
* `viaStage_effect` — the stage's response phase maps `stampVia` over the finalized
  response headers, for ANY tail/handler (via `pipeline_stage_effect`).
* `viaStage_statusStable` — the stage never touches the status (safe to braid).
* `demo_stamps` / `demo_no_double` — concrete non-vacuous witnesses through the real
  `runPipeline` fold: a bare 200 gains exactly `Via: 1.1 drorb`; a response already
  carrying an upstream `Via: 1.0 up` passes through byte-identical.

Residual (named): wire into `deployStagesFull2` + curl through the running socket
(dataplane rebuild deferred — box-safety this session); the multi-hop comma-append
form (RFC permits either a new field line or appending to an existing one; this stage
takes the new-line form, so an upstream `Via` is preserved verbatim).
-/

namespace Reactor.Stage.Via

open Reactor.Pipeline
open Proto (Bytes Request)

/-! ## Case-insensitive field-name match -/

/-- ASCII-lowercase one byte. -/
def lowerByte (b : UInt8) : UInt8 := if 65 ≤ b && b ≤ 90 then b + 32 else b

/-- ASCII-lowercase a byte string. -/
def lower (bs : Bytes) : Bytes := bs.map lowerByte

/-- Lowercase field-name token `"via"`. -/
def viaTok : Bytes := [118, 105, 97]

/-- Is this field name `Via` (case-insensitive)? -/
def isVia (name : Bytes) : Bool := lower name == viaTok

/-! ## The emitted field -/

/-- The emitted field name `"Via"`. -/
def viaName : Bytes := [86, 105, 97]

/-- The received-protocol version this gateway forwards: `"1.1"`. -/
def protoVer : Bytes := [49, 46, 49]

/-- The gateway pseudonym: `"drorb"`. -/
def pseudonym : Bytes := [100, 114, 111, 114, 98]

/-- The emitted value `"1.1 drorb"`. -/
def viaVal : Bytes := [49, 46, 49, 32, 100, 114, 111, 114, 98]

/-- **RFC 9110 §7.6.3 grammar.** The emitted value is exactly
`received-protocol SP pseudonym`. -/
theorem viaVal_shape : viaVal = protoVer ++ [32] ++ pseudonym := rfl

/-- The emitted name matches its own detector (stamping is self-recognizing —
what `stampVia` adds, `hasVia` sees; kernel-decided). -/
theorem viaName_isVia : isVia viaName = true := by decide

/-! ## The stamp -/

/-- Does the header list already carry a `Via` (case-insensitive)? -/
def hasVia (hs : List (Bytes × Bytes)) : Bool := hs.any (fun nv => isVia nv.1)

/-- **Stamp `Via`.** Append `Via: 1.1 drorb` unless a `Via` is already present. -/
def stampVia (hs : List (Bytes × Bytes)) : List (Bytes × Bytes) :=
  if hasVia hs then hs else hs ++ [(viaName, viaVal)]

/-- The appended entry is seen by the detector, whatever precedes it. -/
theorem hasVia_append (hs : List (Bytes × Bytes)) :
    hasVia (hs ++ [(viaName, viaVal)]) = true := by
  unfold hasVia
  rw [List.any_append]
  have hlast : List.any [(viaName, viaVal)] (fun nv => isVia nv.1) = true := by decide
  rw [hlast, Bool.or_true]

/-- **Presence.** After stamping, a `Via` field is present — for ANY header list. -/
theorem stampVia_has (hs : List (Bytes × Bytes)) : hasVia (stampVia hs) = true := by
  unfold stampVia
  by_cases h : hasVia hs = true
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact hasVia_append hs

/-- **No duplication.** A header list already carrying a `Via` is returned
UNCHANGED — an upstream's `Via` is never doubled or rewritten. -/
theorem stampVia_noop (hs : List (Bytes × Bytes)) (h : hasVia hs = true) :
    stampVia hs = hs := by
  unfold stampVia; rw [if_pos h]

/-- **Append-only.** The original headers are a prefix of the stamped list:
nothing is dropped, reordered, or rewritten. -/
theorem stampVia_prefix (hs : List (Bytes × Bytes)) : hs <+: stampVia hs := by
  unfold stampVia
  by_cases h : hasVia hs = true
  · rw [if_pos h]
    exact List.prefix_refl hs
  · rw [if_neg h]
    exact List.prefix_append hs _

/-- **Idempotence.** Stamping a stamped list changes nothing. -/
theorem stampVia_idem (hs : List (Bytes × Bytes)) :
    stampVia (stampVia hs) = stampVia hs :=
  stampVia_noop _ (stampVia_has hs)

/-! ## The stage -/

/-- **The `Via` stage.** Request phase: pass through. Response phase: stamp
`Via: 1.1 drorb` onto the finalized headers (one affine `mapResp`). Never gates. -/
def viaStage : Stage where
  name := "via"
  onRequest := fun c => .continue c
  onResponse := fun _ b => b.mapResp (fun r => { r with headers := stampVia r.headers })

/-- **The byte-effect.** The stage maps `stampVia` over the finalized response's
headers, for ANY tail and handler. -/
theorem viaStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    ((runPipeline (viaStage :: rest) h c).build).headers
      = stampVia ((runPipeline rest h c).build).headers := by
  rw [pipeline_stage_effect viaStage rest h c c rfl]
  rfl

/-- Every response through the stage carries a `Via` — the RFC 9110 §7.6.3
obligation, discharged for ANY tail and handler. -/
theorem viaStage_response_has_via (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    hasVia ((runPipeline (viaStage :: rest) h c).build).headers = true := by
  rw [viaStage_effect]; exact stampVia_has _

/-- The stage never changes the status — safe to braid into a status-stable onion. -/
theorem viaStage_statusStable : viaStage.statusStable := fun _ _ => rfl

/-! ## End-to-end witnesses (non-vacuous) -/

/-- A bare 200 with one unrelated header (`X: Y`). -/
def bareHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [], headers := [([88], [89])], body := [] }

/-- A response already carrying an upstream `Via: 1.0 up` (value `"1.0 up"`). -/
def upstreamViaHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [],
             headers := [(viaName, [49, 46, 48, 32, 117, 112])], body := [] }

/-- An empty request context. -/
def demoCtx : Ctx := { input := [], req := {}, attrs := [] }

/-- **End-to-end.** The single-stage pipeline serves the bare 200 with EXACTLY the
original header followed by `Via: 1.1 drorb` — appended, nothing else touched. -/
theorem demo_stamps :
    ((runPipeline [viaStage] bareHandler demoCtx).build).headers
      = [([88], [89]), (viaName, viaVal)] := by decide

/-- **End-to-end, no duplication.** A response already carrying an upstream `Via`
passes through byte-identical (the upstream entry preserved verbatim, no second
`Via` added). -/
theorem demo_no_double :
    ((runPipeline [viaStage] upstreamViaHandler demoCtx).build).headers
      = [(viaName, [49, 46, 48, 32, 117, 112])] := by decide

#print axioms Reactor.Stage.Via.stampVia_has
#print axioms Reactor.Stage.Via.stampVia_noop
#print axioms Reactor.Stage.Via.stampVia_prefix
#print axioms Reactor.Stage.Via.stampVia_idem
#print axioms Reactor.Stage.Via.viaStage_effect
#print axioms Reactor.Stage.Via.viaStage_response_has_via
#print axioms Reactor.Stage.Via.viaStage_statusStable
#print axioms Reactor.Stage.Via.demo_stamps
#print axioms Reactor.Stage.Via.demo_no_double

end Reactor.Stage.Via
