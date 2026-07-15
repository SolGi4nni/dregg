import Reactor.Pipeline

/-!
# Reactor.Stage.CrossOriginResource — WHATWG Fetch `Cross-Origin-Resource-Policy`
(the CORP cross-origin resource-isolation response header — a genuine serve gap)

WHATWG Fetch §3.5 (`Cross-Origin-Resource-Policy` fetch metadata): a resource
server declares who may EMBED it cross-origin. `Cross-Origin-Resource-Policy:
same-origin` instructs the browser to BLOCK a `no-cors` cross-origin load of the
resource — the Spectre-era side-channel mitigation that lets a server opt its
bytes out of another origin's process. It is DISTINCT from CORS
(`Access-Control-Allow-Origin`, request-driven read permission handled by
`Reactor.Stage.Cors`) and from the classic security trio
(HSTS / X-Frame-Options / nosniff / Referrer-Policy handled by
`Reactor.Stage.SecurityHeaders`): CORP gates cross-origin *embedding* of the
response body, a policy neither of those stages emits.

## Ground truth — the deployed serve emits no CORP

The deployed drorb serve stamps `Server`, `x-upstream`, the security trio and (via
the sibling stages) `Via` — but NO `Cross-Origin-Resource-Policy` on ANY response.
A cross-origin `<img>`/`<script>` `no-cors` load of a static asset is therefore
NOT isolated. This module adds the missing field as a response-phase `Stage`.

## Behaviour

Append `Cross-Origin-Resource-Policy: same-origin` unless a CORP header is already
present (case-insensitive) — an upstream/handler that already declared a policy is
never overridden or duplicated.

## What is proved (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound})

* `stampCorp_has` — after stamping, a CORP field is present, for ANY header list.
* `stampCorp_noop` — a list already carrying a CORP field is returned UNCHANGED.
* `stampCorp_prefix` — stamping only appends (original headers preserved as a prefix).
* `stampCorp_idem` — idempotent (no double-decoration on re-entry).
* `corpVal_shape` — the emitted value is exactly `same-origin`.
* `corpStage_effect` — the stage maps `stampCorp` over the finalized headers.
* `corpStage_response_has_corp` — every response through the stage carries CORP.
* `corpStage_statusStable` — never touches the status (safe to braid).
* `demo_stamps` / `demo_no_double` — concrete non-vacuous witnesses through the
  real `runPipeline` fold.

Residual (named): wire into `deployStagesFull2` + curl through the running socket
(dataplane rebuild deferred — box-safety this session); the report-only /
`credentialless` COEP-coupled variants (this stage takes the `same-origin` form).
-/

namespace Reactor.Stage.CrossOriginResource

open Reactor.Pipeline
open Proto (Bytes Request)

/-! ## Case-insensitive field-name match -/

/-- ASCII-lowercase one byte. -/
def lowerByte (b : UInt8) : UInt8 := if 65 ≤ b && b ≤ 90 then b + 32 else b

/-- ASCII-lowercase a byte string. -/
def lower (bs : Bytes) : Bytes := bs.map lowerByte

/-- Lowercase field-name token `"cross-origin-resource-policy"`. -/
def corpTok : Bytes :=
  [99, 114, 111, 115, 115, 45, 111, 114, 105, 103, 105, 110, 45,
   114, 101, 115, 111, 117, 114, 99, 101, 45, 112, 111, 108, 105, 99, 121]

/-- Is this field name `Cross-Origin-Resource-Policy` (case-insensitive)? -/
def isCorp (name : Bytes) : Bool := lower name == corpTok

/-! ## The emitted field -/

/-- The emitted field name `"Cross-Origin-Resource-Policy"`. -/
def corpName : Bytes :=
  [67, 114, 111, 115, 115, 45, 79, 114, 105, 103, 105, 110, 45,
   82, 101, 115, 111, 117, 114, 99, 101, 45, 80, 111, 108, 105, 99, 121]

/-- The emitted value `"same-origin"`. -/
def corpVal : Bytes := [115, 97, 109, 101, 45, 111, 114, 105, 103, 105, 110]

/-- **WHATWG Fetch §3.5 grammar.** The emitted value is exactly the `same-origin`
policy token. -/
theorem corpVal_shape : corpVal = [115, 97, 109, 101, 45, 111, 114, 105, 103, 105, 110] := rfl

/-- The emitted name matches its own detector (self-recognizing; kernel-decided). -/
theorem corpName_isCorp : isCorp corpName = true := by decide

/-! ## The stamp -/

/-- Does the header list already carry a CORP field (case-insensitive)? -/
def hasCorp (hs : List (Bytes × Bytes)) : Bool := hs.any (fun nv => isCorp nv.1)

/-- **Stamp CORP.** Append `Cross-Origin-Resource-Policy: same-origin` unless one is
already present. -/
def stampCorp (hs : List (Bytes × Bytes)) : List (Bytes × Bytes) :=
  if hasCorp hs then hs else hs ++ [(corpName, corpVal)]

/-- The appended entry is seen by the detector, whatever precedes it. -/
theorem hasCorp_append (hs : List (Bytes × Bytes)) :
    hasCorp (hs ++ [(corpName, corpVal)]) = true := by
  unfold hasCorp
  rw [List.any_append]
  have hlast : List.any [(corpName, corpVal)] (fun nv => isCorp nv.1) = true := by decide
  rw [hlast, Bool.or_true]

/-- **Presence.** After stamping, a CORP field is present — for ANY header list. -/
theorem stampCorp_has (hs : List (Bytes × Bytes)) : hasCorp (stampCorp hs) = true := by
  unfold stampCorp
  by_cases h : hasCorp hs = true
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact hasCorp_append hs

/-- **No duplication.** A list already carrying a CORP field is returned UNCHANGED. -/
theorem stampCorp_noop (hs : List (Bytes × Bytes)) (h : hasCorp hs = true) :
    stampCorp hs = hs := by
  unfold stampCorp; rw [if_pos h]

/-- **Append-only.** The original headers are a prefix of the stamped list. -/
theorem stampCorp_prefix (hs : List (Bytes × Bytes)) : hs <+: stampCorp hs := by
  unfold stampCorp
  by_cases h : hasCorp hs = true
  · rw [if_pos h]; exact List.prefix_refl hs
  · rw [if_neg h]; exact List.prefix_append hs _

/-- **Idempotence.** Stamping a stamped list changes nothing. -/
theorem stampCorp_idem (hs : List (Bytes × Bytes)) :
    stampCorp (stampCorp hs) = stampCorp hs :=
  stampCorp_noop _ (stampCorp_has hs)

/-! ## The stage -/

/-- **The CORP stage.** Request phase: pass through. Response phase: stamp
`Cross-Origin-Resource-Policy: same-origin` onto the finalized headers. Never gates. -/
def corpStage : Stage where
  name := "cross-origin-resource-policy"
  onRequest := fun c => .continue c
  onResponse := fun _ b => b.mapResp (fun r => { r with headers := stampCorp r.headers })

/-- **The byte-effect.** The stage maps `stampCorp` over the finalized response's
headers, for ANY tail and handler. -/
theorem corpStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    ((runPipeline (corpStage :: rest) h c).build).headers
      = stampCorp ((runPipeline rest h c).build).headers := by
  rw [pipeline_stage_effect corpStage rest h c c rfl]
  rfl

/-- Every response through the stage carries CORP — for ANY tail and handler. -/
theorem corpStage_response_has_corp (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    hasCorp ((runPipeline (corpStage :: rest) h c).build).headers = true := by
  rw [corpStage_effect]; exact stampCorp_has _

/-- The stage never changes the status — safe to braid into a status-stable onion. -/
theorem corpStage_statusStable : corpStage.statusStable := fun _ _ => rfl

/-! ## End-to-end witnesses (non-vacuous) -/

/-- A bare 200 with one unrelated header (`X: Y`). -/
def bareHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [], headers := [([88], [89])], body := [] }

/-- A response already carrying an upstream CORP (`cross-origin`, lowercase name). -/
def upstreamCorpHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [],
             headers := [(corpTok, [99, 114, 111, 115, 115, 45, 111, 114, 105, 103, 105, 110])],
             body := [] }

/-- An empty request context. -/
def demoCtx : Ctx := { input := [], req := {}, attrs := [] }

/-- **End-to-end.** The single-stage pipeline serves the bare 200 with EXACTLY the
original header followed by `Cross-Origin-Resource-Policy: same-origin`. -/
theorem demo_stamps :
    ((runPipeline [corpStage] bareHandler demoCtx).build).headers
      = [([88], [89]), (corpName, corpVal)] := by decide

/-- **End-to-end, no duplication.** A response already carrying a CORP field passes
through byte-identical. -/
theorem demo_no_double :
    ((runPipeline [corpStage] upstreamCorpHandler demoCtx).build).headers
      = [(corpTok, [99, 114, 111, 115, 115, 45, 111, 114, 105, 103, 105, 110])] := by decide

#print axioms Reactor.Stage.CrossOriginResource.stampCorp_has
#print axioms Reactor.Stage.CrossOriginResource.stampCorp_noop
#print axioms Reactor.Stage.CrossOriginResource.stampCorp_prefix
#print axioms Reactor.Stage.CrossOriginResource.stampCorp_idem
#print axioms Reactor.Stage.CrossOriginResource.corpVal_shape
#print axioms Reactor.Stage.CrossOriginResource.corpStage_effect
#print axioms Reactor.Stage.CrossOriginResource.corpStage_response_has_corp
#print axioms Reactor.Stage.CrossOriginResource.corpStage_statusStable
#print axioms Reactor.Stage.CrossOriginResource.demo_stamps
#print axioms Reactor.Stage.CrossOriginResource.demo_no_double

end Reactor.Stage.CrossOriginResource
