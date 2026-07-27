import Datapath.FlatHeaders
import Datapath.ByteRefine
import Reactor.Stage.Redirect

/-!
# Datapath.FlatStage_redirect — the deployed `redirect` GATE stage proven flat,
its decision matched to the real stage, and its emitted 3xx response byte-identical
to the deployed serialize.

The representative gate is `redirect`
(`Reactor.Stage.Redirect.redirectStage`, position 5 of the deploy chain in
`Reactor.Deploy`, `Reactor.Stage.Redirect.redirectStage` used verbatim). Unlike a
header-transform stage (`securityheaders`, the `Datapath.FlatStage` exemplar), a
GATE has two halves the flat form must reproduce, both grounded in the REAL stage:

* **the DECISION on the request** — `redirectStage.onRequest` short-circuits with
  `.respond` exactly when `c.req.target = ruleTarget` (`/old`), else `.continue`;
* **the RESPONSE** — the emitted 3xx (`308 Permanent Redirect`) carrying the single
  `Location` header the REAL `Redirect.redirect` library renders, which the flat
  form builds on the flat `HdrBlock` and serializes byte-identically.

## What is proven here (equality-transfer / byte-identity, NOT a re-spec)

* `flatRedirectGate` + `flatRedirectGate_true_iff` — the flat decision is
  `c.req.target == ruleTarget` (flat `BEq`), proven equivalent to the deployed
  stage's propositional gate `c.req.target = ruleTarget`.
* `flatRedirect_respond` / `flatRedirect_pass` — the DECISION matched to the REAL
  stage: `redirectStage.onRequest c` is `.respond (flatRedirectResp c.req)` exactly
  when the flat gate fires, else `.continue c`. The response is the flat-built form,
  proven equal to the deployed `redirectFor` (`flatRedirectResp_eq`).
* `flatRedirectResp` + `flatRedirectResp_eq` — the flat response builds the single
  `Location` header on the flat `HdrBlock` (`HdrBlock.addHeader`, an `Array.push`,
  no cons cell), and is proven EQUAL to the deployed `redirectFor` response — via
  the header push-fold denotation (`HdrBlock.denote_addHeader`), not by definition.
* `flatRedirect_serialize_refines` — the WHOLE serialized 3xx response of the flat
  stage is byte-identical to `Reactor.serialize` of the deployed `redirectFor`
  response, chaining `flatRedirectResp_eq` into the derived flat serializer
  `Datapath.Refinement.flatSerialize` (`flatSerialize_refines`, the byte-grain
  serialize equality).
* `flatRedirect_pipeline_gate` — the end-to-end grounding: a matched request makes
  the REAL deployed pipeline `runPipeline (redirectStage :: rest)` short-circuit to
  exactly the flat-built response, for ANY tail/handler (rides on the deployed
  `redirectStage_gate`).
* `flatRedirect_status_is_redirect` — the emitted status is one of the four §15.4
  redirect codes (301/302/307/308), via the REAL `Redirect.status_is_redirect`.

This is the GATE shape the scope named (a decision on the request + a fixed/computed
byte-identical status response), the sibling of the exemplar's header-transform shape.
-/

namespace Datapath.FlatStage_redirect

open Proto (Bytes Request)
open Reactor (Response)
open Reactor.Pipeline (Ctx Stage StageStep ResponseBuilder runPipeline runResp)
open Reactor.Stage.Redirect
  (redirectStage redirectFor toResponse ruleCode ruleTemplate ruleTarget
   locationName redirectReason decodeTarget redirectStage_gate)
open Datapath.FlatHeaders (HdrBlock)
open Datapath.Refinement (flatSerialize flatSerialize_refines)

/-! ## 1. The flat gate decision, matched to the REAL stage's propositional gate -/

/-- **The flat `redirect` gate decision.** A request is redirected exactly when its
target equals the configured rule target (`/old`), decided flat by `BEq` on the
target byte-window — the flat sibling of the deployed stage's propositional
`c.req.target = ruleTarget`. -/
def flatRedirectGate (req : Request) : Bool := req.target == ruleTarget

/-- The flat `BEq` gate agrees with the deployed stage's propositional gate
(`List UInt8` is `LawfulBEq`). -/
theorem flatRedirectGate_true_iff (req : Request) :
    flatRedirectGate req = true ↔ req.target = ruleTarget := by
  unfold flatRedirectGate
  exact beq_iff_eq

/-! ## 2. The flat 3xx response — built on the flat `HdrBlock`, grounded in the REAL
`redirectFor` -/

/-- **The flat `redirect` response.** Run the REAL `Redirect.redirect` (status +
`Location` template render, RFC 9110 §15.4) against the configured code/template and
the request's own decoded target, then build the single `Location` header on the
flat `HdrBlock` (`HdrBlock.addHeader`, an amortized-`O(1)` `Array.push`, no per-header
cons cell). The flat sibling of the deployed `redirectFor`; `flatRedirectResp_eq`
proves the two responses EQUAL. -/
def flatRedirectResp (req : Request) : Response :=
  { status  := (_root_.Redirect.redirect ruleCode ruleTemplate (decodeTarget req.target) "").status
    reason  := redirectReason
    headers := (HdrBlock.empty.addHeader
                  (locationName,
                    (_root_.Redirect.redirect ruleCode ruleTemplate (decodeTarget req.target) "").location.toUTF8.toList)).denote
    body    := [] }

/-- **The flat response IS the deployed `redirectFor` response** — PROVEN via the
flat header push denotation (`HdrBlock.denote_addHeader`: pushing `nv` onto the empty
flat block denotes to `[] ++ [nv] = [nv]`, the deployed single-`Location` header
list), not by definition. Grounds the flat form in the ACTUAL deployed stage output. -/
theorem flatRedirectResp_eq (req : Request) : flatRedirectResp req = redirectFor req := by
  unfold flatRedirectResp redirectFor toResponse
  simp [HdrBlock.denote_addHeader, HdrBlock.denote_empty]

/-! ## 3. The DECISION, matched to the REAL stage (respond ⇔ gate fires) -/

/-- **Gate fires ⇒ the REAL stage responds with the flat-built response.** When the
flat gate fires, the deployed `redirectStage.onRequest` short-circuits with exactly
`flatRedirectResp c.req` (`= redirectFor c.req`). The decision AND the emitted
response are the flat form's, read off the real stage. -/
theorem flatRedirect_respond (c : Ctx) (hm : flatRedirectGate c.req = true) :
    redirectStage.onRequest c = StageStep.respond (flatRedirectResp c.req) := by
  have ht : c.req.target = ruleTarget := (flatRedirectGate_true_iff c.req).mp hm
  show (if c.req.target = ruleTarget then StageStep.respond (redirectFor c.req)
        else StageStep.continue c) = StageStep.respond (flatRedirectResp c.req)
  rw [if_pos ht, flatRedirectResp_eq]

/-- **Gate does not fire ⇒ the REAL stage passes through.** When the flat gate is
`false`, the deployed `redirectStage.onRequest` is `.continue c` — the gate decision
matched to the real stage on the pass path too. -/
theorem flatRedirect_pass (c : Ctx) (hm : flatRedirectGate c.req = false) :
    redirectStage.onRequest c = StageStep.continue c := by
  have ht : c.req.target ≠ ruleTarget := by
    intro h
    have h2 : flatRedirectGate c.req = true := (flatRedirectGate_true_iff c.req).mpr h
    rw [h2] at hm
    exact Bool.noConfusion hm
  show (if c.req.target = ruleTarget then StageStep.respond (redirectFor c.req)
        else StageStep.continue c) = StageStep.continue c
  rw [if_neg ht]

/-! ## 4. Byte-identity: the flat 3xx response serialized = the deployed serialize -/

/-- **THE FULL BYTE-IDENTITY.** The flat redirect stage's whole serialized 3xx
response (flat `Location`-header build ⟶ `Datapath.Refinement.flatSerialize`, the
derived flat serializer) is byte-identical to `Reactor.serialize` of the DEPLOYED
`redirectFor` response. Chains the response equality (`flatRedirectResp_eq`) into the
byte-grain serialize equality (`flatSerialize_refines`). No deployed byte changes;
the header block is built flat with `Array.push` in place of the cons cell. -/
theorem flatRedirect_serialize_refines (req : Request) :
    Datapath.Refinement.Refines (Reactor.serialize (redirectFor req)) (flatSerialize (flatRedirectResp req)) := by
  rw [flatRedirectResp_eq]
  exact flatSerialize_refines (redirectFor req)

/-! ## 5. End-to-end: the deployed pipeline short-circuits to the flat response -/

/-- **The deployed pipeline gate, grounded in the flat form.** A request whose flat
gate fires makes the REAL deployed pipeline `runPipeline (redirectStage :: rest)`
short-circuit to exactly `flatRedirectResp c.req` — the handler and every stage in
`rest` skipped, for ANY tail/handler. Rides on the deployed `redirectStage_gate`;
the response is the flat-built one (`flatRedirectResp_eq`). -/
theorem flatRedirect_pipeline_gate (rest : List Stage) (handler : Ctx → Response) (c : Ctx)
    (hm : flatRedirectGate c.req = true) :
    runPipeline (redirectStage :: rest) handler c
      = runResp rest c (ResponseBuilder.ofResponse (flatRedirectResp c.req)) := by
  rw [flatRedirectResp_eq]
  exact redirectStage_gate rest handler c ((flatRedirectGate_true_iff c.req).mp hm)

/-- **Byte-effect (status).** The status the flat response genuinely emits is one of
the four §15.4 redirect codes — a real 3xx — via the REAL `Redirect.status_is_redirect`
on the flat-built response (`= redirectFor`). -/
theorem flatRedirect_status_is_redirect (req : Request) :
    (flatRedirectResp req).status ∈ _root_.Redirect.redirectStatuses := by
  rw [flatRedirectResp_eq]
  show (_root_.Redirect.redirect ruleCode ruleTemplate (decodeTarget req.target) "").status
      ∈ _root_.Redirect.redirectStatuses
  exact _root_.Redirect.status_is_redirect ruleCode ruleTemplate (decodeTarget req.target) ""

/-! ## Non-vacuity — the flat gate/response genuinely compute, witnessed on real inputs -/

-- The full flat serialized 3xx response is byte-identical to the deployed serialize —
-- evaluated by the kernel on the real `/old` witness (not just proven).
#guard (flatSerialize (flatRedirectResp { target := ruleTarget })).data.toList
        == Reactor.serialize (redirectFor { target := ruleTarget })

-- The flat gate genuinely fires on the rule target and passes off it.
#guard flatRedirectGate { target := ruleTarget } == true
#guard flatRedirectGate { target := "/other".toUTF8.toList } == false

-- The emitted status is exactly the configured `308 Permanent Redirect`.
#guard (flatRedirectResp { target := ruleTarget }).status == 308

-- The flat response carries exactly one header, and it is the `Location` header.
#guard (flatRedirectResp { target := ruleTarget }).headers.map (·.1) == [locationName]

-- The flat op genuinely depends on the request target: different targets render
-- different `Location` bytes, hence different serialized responses (not a constant).
#guard (flatSerialize (flatRedirectResp { target := "/a".toUTF8.toList })).data.toList
        != (flatSerialize (flatRedirectResp { target := "/bb".toUTF8.toList })).data.toList

end Datapath.FlatStage_redirect
