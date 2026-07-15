/-
# Proto.NoSniffProven — `X-Content-Type-Options: nosniff` on the DEPLOYED serve

PROVE-WHAT-RUNS for the MIME-sniffing-protection header the running dataplane stamps on
every response. Curl-confirmed against the deployed `dataplane` binary:

    $ curl -s -D - -o /dev/null http://127.0.0.1:8097/static/app.js
    HTTP/1.1 200 OK
    …
    X-Content-Type-Options: nosniff               ← proven here
    …

The deployed pipeline's `Reactor.Stage.SecurityHeaders.securityheadersStage` folds the
REAL `SecurityHeaders.render` output for the deployed policy onto the response builder.
The deployed policy sets `noSniff := true`, so `render` emits
`("X-Content-Type-Options", "nosniff")` — the RFC-defined directive that forbids the
browser from MIME-sniffing the body and forces it to honour the declared `Content-Type`
(the `application/javascript` proven in `Proto.ContentTypeProven`).

The existing `Reactor.Stage.SecurityHeaders.securityheadersStage_hsts_present` proves the
`Strict-Transport-Security` member reaches the BUILT output; this file proves the same
byte-effect for the `X-Content-Type-Options: nosniff` member.

Theorems:

  * `nosniff_in_wireHeaders` — `(X-Content-Type-Options, nosniff)` is a member of the wire
    header set the deployed policy renders.
  * `securityheaders_nosniff_present` — for ANY pipeline tail and handler, the
    `X-Content-Type-Options: nosniff` header genuinely appears in the BUILT pipeline
    output of `securityheadersStage :: rest` (rides `pipeline_stage_effect` +
    `build_addHeaders`, exactly as the deployed HSTS byte-effect does).
  * `nosniff_wire_bytes` — the name/value are exactly the bytes of
    `"X-Content-Type-Options"` / `"nosniff"` (pinned via the `Shortcuts.ba_toList_eq` bridge —
    pure-kernel `decide`, no `native_decide`).
-/

import Reactor.Stage.SecurityHeaders
import SecurityHeaders
import Proto.Kernel.Shortcuts

namespace Proto.NoSniffProven

open Reactor.Pipeline
open Reactor.Stage.SecurityHeaders
open Proto (Bytes)
open Proto.Kernel

/-- The `X-Content-Type-Options` header name on the wire. -/
def nosniffName : Bytes := "X-Content-Type-Options".toUTF8.toList

/-- The `nosniff` header value on the wire. -/
def nosniffVal : Bytes := "nosniff".toUTF8.toList

/-! ## The `nosniff` member is in the rendered wire header set -/

/-- The deployed policy's rendered `SecurityHeaders` set contains the
`("X-Content-Type-Options", "nosniff")` pair — the policy sets `noSniff := true`, so the
`render` disjunct fires. -/
theorem nosniff_in_render :
    ("X-Content-Type-Options", "nosniff") ∈ _root_.SecurityHeaders.render policy := by
  simp only [_root_.SecurityHeaders.render, policy]
  -- render = [HSTS] ++ [] ++ [X-Frame] ++ [nosniff] ++ [Referrer]; the nosniff pair is present.
  simp

/-- **`nosniff_in_wireHeaders`.** The wire header set the deployed policy renders contains
the `X-Content-Type-Options: nosniff` pair (the `toWireHeader` image of the rendered
member). -/
theorem nosniff_in_wireHeaders :
    (nosniffName, nosniffVal) ∈ wireHeaders policy := by
  show (nosniffName, nosniffVal)
    ∈ (_root_.SecurityHeaders.render policy).map toWireHeader
  have : (nosniffName, nosniffVal)
      = toWireHeader ("X-Content-Type-Options", "nosniff") := rfl
  rw [this]
  exact List.mem_map_of_mem _ nosniff_in_render

/-! ## The deployed byte-effect: `nosniff` reaches the BUILT pipeline output -/

/-- **`securityheaders_nosniff_present`.** The real `X-Content-Type-Options: nosniff`
header genuinely appears in the BUILT pipeline output, for ANY tail and handler — a true
byte-driver: `build_addHeaders` carries the affine security-header fold into the finalized
`Response` the serializer renders. Mirrors the deployed HSTS byte-effect
(`securityheadersStage_hsts_present`); with `rest = [Reactor.Stage.Header.headerStage]`
this is exactly the deployed `deployStagesFull2` tail (the terminal header rewrite strips
only hop-by-hop fields, so `nosniff` survives to the wire — curl-confirmed). -/
theorem securityheaders_nosniff_present (rest : List Stage) (h : Ctx → Reactor.Response)
    (c : Ctx) :
    (nosniffName, nosniffVal)
      ∈ ((runPipeline (securityheadersStage :: rest) h c).build).headers := by
  rw [securityheadersStage_effect, build_addHeaders]
  exact List.mem_append.mpr (Or.inr nosniff_in_wireHeaders)

/-! ## The exact wire bytes -/

/-- **`nosniff_wire_bytes`.** The header name/value the deployed stage emits are exactly
the bytes of `"X-Content-Type-Options"` / `"nosniff"` — pinned to explicit literals
through the `Shortcuts.ba_toList_eq` bridge (pure-kernel `decide`, no `native_decide`), matching the
curl `X-Content-Type-Options: nosniff`. -/
theorem nosniff_wire_bytes :
    nosniffName = [88, 45, 67, 111, 110, 116, 101, 110, 116, 45, 84, 121, 112, 101,
                   45, 79, 112, 116, 105, 111, 110, 115]
  ∧ nosniffVal = [110, 111, 115, 110, 105, 102, 102] := by
  refine ⟨?_, ?_⟩ <;> simp only [nosniffName, nosniffVal, Shortcuts.ba_toList_eq] <;> decide

end Proto.NoSniffProven

#print axioms Proto.NoSniffProven.nosniff_in_render
#print axioms Proto.NoSniffProven.nosniff_in_wireHeaders
#print axioms Proto.NoSniffProven.securityheaders_nosniff_present
#print axioms Proto.NoSniffProven.nosniff_wire_bytes
