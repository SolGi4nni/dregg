import Reactor.Pipeline

/-!
# Reactor.Stage.UriTooLong — the `414 (URI Too Long)` gate (RFC 9110 §15.5.13)

A byte-driving request GATE closing a refusal-shape gap: RFC 9110 §15.5.13
directs a server to answer `414` when a request target is "longer than the
server is willing to interpret". The deployed serve had NO such refusal — a
several-kilobyte request-target was parsed, dispatched, and answered a
mis-routed `404` (wire capture 2026-07-13: a 3000-octet path is `404 Not
Found`), silently accepting unbounded targets up to the whole-head cap and
misclassifying the refusal.

The budget is `targetCap = 2048` octets — the classic interoperable ceiling
(RFC 9110 §4.1 recommends supporting "at least 8000 octets" for the whole
request LINE; a 2048-octet target is the widely-deployed conservative bound,
far under both the head cap and the parse cap, so this gate genuinely FIRES on
this host, unlike a declared-size budget the upstream caps shadow).

DISPATCH SCOPE: the fold's reject path (over-cap, unparsable) carries a default
request context whose target is EMPTY, so this gate passes it through and the
deployed reject responses stay owned by the handler (`overCap_empty`).

## What is proven here (pure kernel; no `native_decide`, no `ofReduceBool`)

* `uriGate_fires` / `uriGate_passes` — the exact firing condition.
* `overCap_empty` — the reject path (empty target) is never gated.
* `uriTooLong_status` / `uriGate_statusStable`; non-vacuous witnesses by
  `decide` (a 2049-octet target fires; a 2048-octet one passes).
-/

namespace Reactor.Stage.UriTooLong

open Reactor.Pipeline
open Reactor (Response)
open Proto (Bytes)

/-- The target budget in octets: the widely-deployed conservative bound. -/
def targetCap : Nat := 2048

/-- The `414 (URI Too Long)` refusal (RFC 9110 §15.5.13). -/
def uriTooLongResp : Response :=
  { status := 414
    reason := "URI Too Long".toUTF8.toList
    headers := []
    body := "uri too long\n".toUTF8.toList }

/-- Is the request target over budget? -/
def overCap (req : Proto.Request) : Bool :=
  decide (targetCap < req.target.length)

/-- **The `414` gate.** An over-budget target is refused; everything else
passes through UNTOUCHED. -/
def uriTooLongStage : Stage where
  name := "uri-too-long-414"
  onRequest := fun c => if overCap c.req then .respond uriTooLongResp else .continue c
  onResponse := fun _ b => b

theorem uriGate_fires (c : Ctx) (h : overCap c.req = true) :
    uriTooLongStage.onRequest c = .respond uriTooLongResp := by
  show (if overCap c.req then StageStep.respond uriTooLongResp
        else StageStep.continue c) = _
  rw [h]
  rfl

theorem uriGate_passes (c : Ctx) (h : overCap c.req = false) :
    uriTooLongStage.onRequest c = .continue c := by
  show (if overCap c.req then StageStep.respond uriTooLongResp
        else StageStep.continue c) = _
  rw [h]
  rfl

/-- The gate's response phase is the identity. -/
theorem uriGate_onResponse_id (c : Ctx) (b : ResponseBuilder) :
    uriTooLongStage.onResponse c b = b := rfl

theorem uriGate_statusStable : Stage.statusStable uriTooLongStage :=
  fun _ _ => rfl

theorem uriTooLong_status : uriTooLongResp.status = 414 := rfl

/-- **The reject path is never gated**: an empty target (the fold's default
request context on an input the deployed parse refuses) passes. -/
theorem overCap_empty (req : Proto.Request) (h : req.target = []) :
    overCap req = false := by
  unfold overCap
  rw [h]
  rfl

/-! ## Non-vacuity (kernel `decide` on concrete lengths) -/

/-- The firing condition in arithmetic form (rewrite, do not whole-list
`decide` — a multi-thousand-element list exceeds the kernel recursion budget). -/
theorem overCap_replicate (n : Nat) :
    overCap { target := List.replicate n (97 : UInt8) }
      = decide (targetCap < n) := by
  unfold overCap
  rw [show ({ target := List.replicate n (97 : UInt8) }
      : Proto.Request).target = List.replicate n (97 : UInt8) from rfl,
    List.length_replicate]

/-- A 2049-octet target fires the gate. -/
example : overCap { target := List.replicate 2049 (97 : UInt8) } = true := by
  rw [overCap_replicate]
  rfl

/-- A 2048-octet target passes (the budget is inclusive). -/
example : overCap { target := List.replicate 2048 (97 : UInt8) } = false := by
  rw [overCap_replicate]
  rfl

/-- The deployed routes are far under budget (`/static/app.js`). -/
example : overCap { target := [47, 115, 116, 97, 116, 105, 99, 47, 97, 112,
    112, 46, 106, 115] } = false := by
  decide

end Reactor.Stage.UriTooLong

#print axioms Reactor.Stage.UriTooLong.uriGate_fires
#print axioms Reactor.Stage.UriTooLong.overCap_empty
