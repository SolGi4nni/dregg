import Reactor.Pipeline

/-!
# Reactor.Stage.PermissionsPolicy — W3C `Permissions-Policy` (the powerful-feature
gating response header — a genuine serve gap)

W3C Permissions Policy (the successor to `Feature-Policy`): a document declares
which powerful browser features (geolocation, camera, microphone, payment, …) it
and its embedded frames may use. `Permissions-Policy: geolocation=(), camera=(),
microphone=(), payment=()` DENIES each named feature to the document and every
`<iframe>` it hosts — the standard hardening a static edge applies so an injected
or third-party script can never silently reach for the camera/mic/geolocation.

It is DISTINCT from the classic security trio
(HSTS / X-Frame-Options / nosniff / Referrer-Policy — `Reactor.Stage.SecurityHeaders`)
and from CORS/CORP: none of those emit a feature-permission policy.

## Ground truth — the deployed serve emits no Permissions-Policy

The deployed drorb serve stamps the security trio, `Server`, `x-upstream` — but NO
`Permissions-Policy` on ANY response, so a served document leaves every powerful
feature at the browser default. This module adds the missing field as a
response-phase `Stage`.

## Behaviour

Append `Permissions-Policy: geolocation=(), camera=(), microphone=(), payment=()`
unless a Permissions-Policy header is already present (case-insensitive) — an
upstream/handler that already declared a policy is never overridden or duplicated.

## What is proved (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound})

* `stampPP_has` — after stamping, a Permissions-Policy field is present, for ANY list.
* `stampPP_noop` — a list already carrying the field is returned UNCHANGED.
* `stampPP_prefix` — stamping only appends (original headers preserved as a prefix).
* `stampPP_idem` — idempotent (no double-decoration on re-entry).
* `ppVal_denies_all` — the emitted value's allow-lists are ALL empty `()`
  (`geolocation`, `camera`, `microphone`, `payment` each denied), structurally.
* `ppStage_effect` — the stage maps `stampPP` over the finalized headers.
* `ppStage_response_has_pp` — every response through the stage carries the field.
* `ppStage_statusStable` — never touches the status (safe to braid).
* `demo_stamps` / `demo_no_double` — concrete non-vacuous witnesses.

Residual (named): wire into `deployStagesFull2` + curl (dataplane rebuild deferred);
per-route feature relaxation (this stage takes the deny-all posture).
-/

namespace Reactor.Stage.PermissionsPolicy

open Reactor.Pipeline
open Proto (Bytes Request)

/-! ## Case-insensitive field-name match -/

/-- ASCII-lowercase one byte. -/
def lowerByte (b : UInt8) : UInt8 := if 65 ≤ b && b ≤ 90 then b + 32 else b

/-- ASCII-lowercase a byte string. -/
def lower (bs : Bytes) : Bytes := bs.map lowerByte

/-- Lowercase field-name token `"permissions-policy"`. -/
def ppTok : Bytes :=
  [112, 101, 114, 109, 105, 115, 115, 105, 111, 110, 115, 45, 112, 111, 108, 105, 99, 121]

/-- Is this field name `Permissions-Policy` (case-insensitive)? -/
def isPP (name : Bytes) : Bool := lower name == ppTok

/-! ## The emitted field -/

/-- The emitted field name `"Permissions-Policy"`. -/
def ppName : Bytes :=
  [80, 101, 114, 109, 105, 115, 115, 105, 111, 110, 115, 45, 80, 111, 108, 105, 99, 121]

/-- One directive `feature=()` (a denied feature — empty allow-list). The name bytes
are the ASCII feature token; the value is the empty-allow-list suffix `=()`. -/
def denyDirective (feature : Bytes) : Bytes := feature ++ [61, 40, 41]

/-- `geolocation` (ASCII). -/
def fGeo : Bytes := [103, 101, 111, 108, 111, 99, 97, 116, 105, 111, 110]
/-- `camera` (ASCII). -/
def fCam : Bytes := [99, 97, 109, 101, 114, 97]
/-- `microphone` (ASCII). -/
def fMic : Bytes := [109, 105, 99, 114, 111, 112, 104, 111, 110, 101]
/-- `payment` (ASCII). -/
def fPay : Bytes := [112, 97, 121, 109, 101, 110, 116]

/-- The `", "` directive separator. -/
def sep : Bytes := [44, 32]

/-- The emitted value: the four powerful features each denied, comma-joined —
`geolocation=(), camera=(), microphone=(), payment=()`. -/
def ppVal : Bytes :=
  denyDirective fGeo ++ sep ++ denyDirective fCam ++ sep ++
  denyDirective fMic ++ sep ++ denyDirective fPay

/-- **Deny-all shape.** The value is exactly the four `feature=()` deny directives,
`", "`-joined — each allow-list is the empty `()`, so every named feature is denied
to the document and its frames. -/
theorem ppVal_denies_all :
    ppVal = denyDirective fGeo ++ sep ++ denyDirective fCam ++ sep ++
            denyDirective fMic ++ sep ++ denyDirective fPay := rfl

/-- Each directive ends in the empty allow-list `=()` — the deny token. -/
theorem denyDirective_empty (feature : Bytes) :
    denyDirective feature = feature ++ [61, 40, 41] := rfl

/-- The emitted name matches its own detector (self-recognizing; kernel-decided). -/
theorem ppName_isPP : isPP ppName = true := by decide

/-! ## The stamp -/

/-- Does the header list already carry a Permissions-Policy field (case-insensitive)? -/
def hasPP (hs : List (Bytes × Bytes)) : Bool := hs.any (fun nv => isPP nv.1)

/-- **Stamp Permissions-Policy.** Append the deny-all policy unless one is present. -/
def stampPP (hs : List (Bytes × Bytes)) : List (Bytes × Bytes) :=
  if hasPP hs then hs else hs ++ [(ppName, ppVal)]

/-- The appended entry is seen by the detector, whatever precedes it. -/
theorem hasPP_append (hs : List (Bytes × Bytes)) :
    hasPP (hs ++ [(ppName, ppVal)]) = true := by
  unfold hasPP
  rw [List.any_append]
  have hlast : List.any [(ppName, ppVal)] (fun nv => isPP nv.1) = true := by decide
  rw [hlast, Bool.or_true]

/-- **Presence.** After stamping, the field is present — for ANY header list. -/
theorem stampPP_has (hs : List (Bytes × Bytes)) : hasPP (stampPP hs) = true := by
  unfold stampPP
  by_cases h : hasPP hs = true
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact hasPP_append hs

/-- **No duplication.** A list already carrying the field is returned UNCHANGED. -/
theorem stampPP_noop (hs : List (Bytes × Bytes)) (h : hasPP hs = true) :
    stampPP hs = hs := by
  unfold stampPP; rw [if_pos h]

/-- **Append-only.** The original headers are a prefix of the stamped list. -/
theorem stampPP_prefix (hs : List (Bytes × Bytes)) : hs <+: stampPP hs := by
  unfold stampPP
  by_cases h : hasPP hs = true
  · rw [if_pos h]; exact List.prefix_refl hs
  · rw [if_neg h]; exact List.prefix_append hs _

/-- **Idempotence.** Stamping a stamped list changes nothing. -/
theorem stampPP_idem (hs : List (Bytes × Bytes)) :
    stampPP (stampPP hs) = stampPP hs :=
  stampPP_noop _ (stampPP_has hs)

/-! ## The stage -/

/-- **The Permissions-Policy stage.** Request phase: pass through. Response phase:
stamp the deny-all policy onto the finalized headers. Never gates. -/
def ppStage : Stage where
  name := "permissions-policy"
  onRequest := fun c => .continue c
  onResponse := fun _ b => b.mapResp (fun r => { r with headers := stampPP r.headers })

/-- **The byte-effect.** The stage maps `stampPP` over the finalized response's
headers, for ANY tail and handler. -/
theorem ppStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    ((runPipeline (ppStage :: rest) h c).build).headers
      = stampPP ((runPipeline rest h c).build).headers := by
  rw [pipeline_stage_effect ppStage rest h c c rfl]
  rfl

/-- Every response through the stage carries the field — for ANY tail and handler. -/
theorem ppStage_response_has_pp (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    hasPP ((runPipeline (ppStage :: rest) h c).build).headers = true := by
  rw [ppStage_effect]; exact stampPP_has _

/-- The stage never changes the status — safe to braid into a status-stable onion. -/
theorem ppStage_statusStable : ppStage.statusStable := fun _ _ => rfl

/-! ## End-to-end witnesses (non-vacuous) -/

/-- A bare 200 with one unrelated header (`X: Y`). -/
def bareHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [], headers := [([88], [89])], body := [] }

/-- A response already carrying an upstream Permissions-Policy (lowercase name,
value `camera=()`). -/
def upstreamPPHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [],
             headers := [(ppTok, denyDirective fCam)], body := [] }

/-- An empty request context. -/
def demoCtx : Ctx := { input := [], req := {}, attrs := [] }

/-- **End-to-end.** The single-stage pipeline serves the bare 200 with EXACTLY the
original header followed by the `Permissions-Policy` deny-all field. -/
theorem demo_stamps :
    ((runPipeline [ppStage] bareHandler demoCtx).build).headers
      = [([88], [89]), (ppName, ppVal)] := by decide

/-- **End-to-end, no duplication.** A response already carrying a Permissions-Policy
field passes through byte-identical. -/
theorem demo_no_double :
    ((runPipeline [ppStage] upstreamPPHandler demoCtx).build).headers
      = [(ppTok, denyDirective fCam)] := by decide

#print axioms Reactor.Stage.PermissionsPolicy.stampPP_has
#print axioms Reactor.Stage.PermissionsPolicy.stampPP_noop
#print axioms Reactor.Stage.PermissionsPolicy.stampPP_prefix
#print axioms Reactor.Stage.PermissionsPolicy.stampPP_idem
#print axioms Reactor.Stage.PermissionsPolicy.ppVal_denies_all
#print axioms Reactor.Stage.PermissionsPolicy.ppStage_effect
#print axioms Reactor.Stage.PermissionsPolicy.ppStage_response_has_pp
#print axioms Reactor.Stage.PermissionsPolicy.ppStage_statusStable
#print axioms Reactor.Stage.PermissionsPolicy.demo_stamps
#print axioms Reactor.Stage.PermissionsPolicy.demo_no_double

end Reactor.Stage.PermissionsPolicy
