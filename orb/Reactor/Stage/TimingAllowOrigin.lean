import Reactor.Pipeline

/-!
# Reactor.Stage.TimingAllowOrigin — `Timing-Allow-Origin` (W3C Resource Timing —
the cross-origin timing-visibility response header, a genuine serve gap)

W3C Resource Timing (Level 2, §4.9 `Timing-Allow-Origin`): a cross-origin
resource's detailed timing attributes (DNS/TCP/TLS/request/response phases) are
REDACTED by the browser — `PerformanceResourceTiming` collapses to a bare
`startTime`/`responseEnd` — unless the response opts in with a
`Timing-Allow-Origin` header naming the requesting origin (or `*`). This is the
standard header CDNs and static-asset origins emit so their consumers' RUM
telemetry can see real network phase timings for third-party fetches.

## Ground truth — the deployed serve emits no Timing-Allow-Origin

No stage in the deployed fold (nor any inert leaf under `Reactor/Stage/`) names
this field: a cross-origin consumer of a drorb-served asset gets a redacted
timing entry today. This module supplies the opt-in as a response-phase `Stage`.

## Behaviour

Append `Timing-Allow-Origin: *` unless a `Timing-Allow-Origin` header is already
present (case-insensitive) — an origin's own (possibly narrower) policy is never
overridden or duplicated. `*` is the deliberate policy for this serve's public
assets: timing visibility is not an authenticated-content channel.

## What is proved (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound})

* `stampTAO_has` — after stamping, a `Timing-Allow-Origin` field is present, for
  ANY header list.
* `stampTAO_noop` — a list already carrying `Timing-Allow-Origin` is returned
  UNCHANGED.
* `stampTAO_prefix` — stamping only appends (original headers preserved as a prefix).
* `stampTAO_idem` — idempotent (no double-decoration on re-entry).
* `taoStage_effect` — the stage maps `stampTAO` over the finalized headers.
* `taoStage_response_has_tao` — every response through the stage carries the field.
* `taoStage_statusStable` — never touches the status (safe to braid).
* `demo_stamps` / `demo_no_double` — concrete non-vacuous witnesses.

Deployment: prepended to the deployed default fold by `Reactor.DeployPlus4`
(`deployStagesPlus4` — head placement, outermost `onResponse`, so EVERY deployed
response carries the opt-in, gate refusals included).
-/

namespace Reactor.Stage.TimingAllowOrigin

open Reactor.Pipeline
open Proto (Bytes Request)

/-! ## Case-insensitive field-name match -/

/-- ASCII-lowercase one byte. -/
def lowerByte (b : UInt8) : UInt8 := if 65 ≤ b && b ≤ 90 then b + 32 else b

/-- ASCII-lowercase a byte string. -/
def lower (bs : Bytes) : Bytes := bs.map lowerByte

/-- Lowercase field-name token `"timing-allow-origin"`. -/
def taoTok : Bytes :=
  [116, 105, 109, 105, 110, 103, 45, 97, 108, 108, 111, 119, 45,
   111, 114, 105, 103, 105, 110]

/-- Is this field name `Timing-Allow-Origin` (case-insensitive)? -/
def isTAO (name : Bytes) : Bool := lower name == taoTok

/-! ## The emitted field -/

/-- The emitted field name `"Timing-Allow-Origin"`. -/
def taoName : Bytes :=
  [84, 105, 109, 105, 110, 103, 45, 65, 108, 108, 111, 119, 45,
   79, 114, 105, 103, 105, 110]

/-- The emitted value `"*"` — every requesting origin may see full timing
attributes (the public-asset policy). -/
def taoVal : Bytes := [42]

/-- The emitted name matches its own detector (self-recognizing; kernel-decided). -/
theorem taoName_isTAO : isTAO taoName = true := by decide

/-! ## The stamp -/

/-- Does the header list already carry a `Timing-Allow-Origin` field
(case-insensitive)? -/
def hasTAO (hs : List (Bytes × Bytes)) : Bool := hs.any (fun nv => isTAO nv.1)

/-- **Stamp `Timing-Allow-Origin`.** Append `Timing-Allow-Origin: *` unless one is
present. -/
def stampTAO (hs : List (Bytes × Bytes)) : List (Bytes × Bytes) :=
  if hasTAO hs then hs else hs ++ [(taoName, taoVal)]

/-- The appended entry is seen by the detector, whatever precedes it. -/
theorem hasTAO_append (hs : List (Bytes × Bytes)) :
    hasTAO (hs ++ [(taoName, taoVal)]) = true := by
  unfold hasTAO
  rw [List.any_append]
  have hlast : List.any [(taoName, taoVal)] (fun nv => isTAO nv.1) = true := by decide
  rw [hlast, Bool.or_true]

/-- **Presence.** After stamping, a `Timing-Allow-Origin` field is present — for
ANY header list. -/
theorem stampTAO_has (hs : List (Bytes × Bytes)) : hasTAO (stampTAO hs) = true := by
  unfold stampTAO
  by_cases h : hasTAO hs = true
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact hasTAO_append hs

/-- **No duplication.** A list already carrying the field is returned UNCHANGED —
an origin's own narrower policy survives. -/
theorem stampTAO_noop (hs : List (Bytes × Bytes)) (h : hasTAO hs = true) :
    stampTAO hs = hs := by
  unfold stampTAO; rw [if_pos h]

/-- **Append-only.** The original headers are a prefix of the stamped list. -/
theorem stampTAO_prefix (hs : List (Bytes × Bytes)) : hs <+: stampTAO hs := by
  unfold stampTAO
  by_cases h : hasTAO hs = true
  · rw [if_pos h]; exact List.prefix_refl hs
  · rw [if_neg h]; exact List.prefix_append hs _

/-- **Idempotence.** Stamping a stamped list changes nothing. -/
theorem stampTAO_idem (hs : List (Bytes × Bytes)) :
    stampTAO (stampTAO hs) = stampTAO hs :=
  stampTAO_noop _ (stampTAO_has hs)

/-! ## The stage -/

/-- **The `Timing-Allow-Origin` stage.** Request phase: pass through. Response
phase: stamp the timing opt-in onto the finalized headers. Never gates. -/
def taoStage : Stage where
  name := "timing-allow-origin"
  onRequest := fun c => .continue c
  onResponse := fun _ b => b.mapResp (fun r => { r with headers := stampTAO r.headers })

/-- **The byte-effect.** The stage maps `stampTAO` over the finalized response's
headers, for ANY tail and handler. -/
theorem taoStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    ((runPipeline (taoStage :: rest) h c).build).headers
      = stampTAO ((runPipeline rest h c).build).headers := by
  rw [pipeline_stage_effect taoStage rest h c c rfl]
  rfl

/-- Every response through the stage carries `Timing-Allow-Origin` — for ANY tail
and handler. -/
theorem taoStage_response_has_tao (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    hasTAO ((runPipeline (taoStage :: rest) h c).build).headers = true := by
  rw [taoStage_effect]; exact stampTAO_has _

/-- The stage never changes the status — safe to braid into a status-stable onion. -/
theorem taoStage_statusStable : taoStage.statusStable := fun _ _ => rfl

/-! ## End-to-end witnesses (non-vacuous) -/

/-- A bare 200 with one unrelated header (`X: Y`). -/
def bareHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [], headers := [([88], [89])], body := [] }

/-- A response already carrying an upstream `Timing-Allow-Origin` (lowercase name,
value `https://a` — a narrower origin policy). -/
def upstreamTaoHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [],
             headers := [(taoTok, [104, 116, 116, 112, 115, 58, 47, 47, 97])],
             body := [] }

/-- An empty request context. -/
def demoCtx : Ctx := { input := [], req := {}, attrs := [] }

/-- **End-to-end.** The single-stage pipeline serves the bare 200 with EXACTLY the
original header followed by `Timing-Allow-Origin: *`. -/
theorem demo_stamps :
    ((runPipeline [taoStage] bareHandler demoCtx).build).headers
      = [([88], [89]), (taoName, taoVal)] := by decide

/-- **End-to-end, no duplication.** A response already carrying the field passes
through byte-identical. -/
theorem demo_no_double :
    ((runPipeline [taoStage] upstreamTaoHandler demoCtx).build).headers
      = [(taoTok, [104, 116, 116, 112, 115, 58, 47, 47, 97])] := by decide

#print axioms Reactor.Stage.TimingAllowOrigin.stampTAO_has
#print axioms Reactor.Stage.TimingAllowOrigin.stampTAO_noop
#print axioms Reactor.Stage.TimingAllowOrigin.stampTAO_prefix
#print axioms Reactor.Stage.TimingAllowOrigin.stampTAO_idem
#print axioms Reactor.Stage.TimingAllowOrigin.taoStage_effect
#print axioms Reactor.Stage.TimingAllowOrigin.taoStage_response_has_tao
#print axioms Reactor.Stage.TimingAllowOrigin.taoStage_statusStable
#print axioms Reactor.Stage.TimingAllowOrigin.demo_stamps
#print axioms Reactor.Stage.TimingAllowOrigin.demo_no_double

end Reactor.Stage.TimingAllowOrigin
