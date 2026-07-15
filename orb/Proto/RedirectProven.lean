import Reactor.Deploy
import Reactor.Stage.Redirect
import Redirect
import Proto.Kernel.Shortcuts

/-!
# Proto.RedirectProven — the DEPLOYED `Location:` redirect (ledger row `h1.redirect`)

PROVE-WHAT-RUNS for `Location`/3xx redirect. The redirect gate
`Reactor.Stage.Redirect.redirectStage` is WIRED into the deployed HTTP/1.1 fold
`Reactor.Deploy.deployStagesFull2` (it is element #5), so a request whose target
matches the configured rule (`/old`) short-circuits the whole pipeline with a
`308 Moved` carrying a `Location` header rendered by the REAL `Redirect.redirect`
library (RFC 9110 §15.4).

## Ground truth — curl against the running dataplane (io_uring, port 8080)

```
$ curl -sS -i http://127.0.0.1:8080/old
HTTP/1.1 308 Moved
Connection: keep-alive
Location: https://new.example/old
Server: drorb
Content-Length: 0
```

The status is `308`, the `Location` value is `https://new.example` prepended to
the request's decoded path (`/old`), and the body is empty (`Content-Length: 0`)
— exactly what the theorems below fix.

## What is proven here (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound})

* `redirect_deployed` — `redirectStage` really is in `deployStagesFull2` (the
  redirect logic is on the default request path, not a side model).
* `location_name_bytes` — the emitted header name is exactly the ASCII bytes of
  `"Location"` (the `.toUTF8.toList` constant kernel-reduced via `Shortcuts.ba_toList_eq`).
* `ruleTarget_bytes` — the configured redirect target is exactly the bytes of
  `"/old"` (the curl's path).
* `redirect_status_308` — for ANY request the gate's response status is `308`.
* `redirect_location_prefix` — the rendered `Location` string is
  `"https://new.example" ++ <decoded path>`; for `/old` this is the wire's
  `https://new.example/old`.
* `redirect_response_shape` — the built redirect `Response` carries a single
  header whose name is `locationName` and whose value is the rendered location
  bytes, with an empty body (the `Content-Length: 0` on the wire).
* `redirect_gate_fires` — for the concrete `/old` request the gate short-circuits
  (handler + later stages skipped), riding the real `redirectStage_gate`.

The `Location` VALUE's exact bytes cross the extern `String.fromUTF8!`/`toUTF8`
boundary (the request path is decoded with `String.fromUTF8!`); its concrete
octets are established by the curl. The IN-kernel facts are the header NAME
bytes, the status, the response shape, and the render structure.
-/

namespace Proto.RedirectProven

open Reactor.Pipeline (Ctx Stage ResponseBuilder runPipeline)
open Reactor (Response)

open Reactor.Stage.Redirect
open Proto.Kernel

/-! ## The redirect gate is on the DEPLOYED path -/

/-- **`redirect_deployed`.** The redirect gate `redirectStage` really is an
element of the deployed HTTP/1.1 fold `deployStagesFull2` — so the `Location`
redirect logic runs on the default request path, not in a side model. Proved by
walking the concrete stage list (no `DecidableEq Stage` needed). -/
theorem redirect_deployed : redirectStage ∈ Reactor.Deploy.deployStagesFull2 := by
  unfold Reactor.Deploy.deployStagesFull2
  repeat first
    | exact List.mem_cons_self _ _
    | apply List.mem_cons_of_mem

/-! ## Byte-exact header name and configured target (pure kernel via `Shortcuts.ba_toList_eq`) -/

/-- **`location_name_bytes`.** The redirect gate's `Location` header NAME is
exactly the ASCII bytes of `"Location"`. The `.toUTF8.toList` constant is
kernel-reduced with `Shortcuts.ba_toList_eq`, so this closes by `decide` in the pure
kernel. -/
theorem location_name_bytes :
    locationName = [76, 111, 99, 97, 116, 105, 111, 110] := by
  show "Location".toUTF8.toList = _
  rw [Shortcuts.ba_toList_eq]; decide

/-- **`ruleTarget_bytes`.** The configured redirect target is exactly the bytes of
`"/old"` — the path the curl requests. -/
theorem ruleTarget_bytes : ruleTarget = [47, 111, 108, 100] := by
  show "/old".toUTF8.toList = _
  rw [Shortcuts.ba_toList_eq]; decide

/-! ## Status, location string, and response shape -/

/-- **`redirect_status_308`.** For ANY request the redirect gate's response status
is `308` — the wire's `HTTP/1.1 308`. The status is the configured code's status
and does not depend on the (extern-decoded) request path, so it closes by `rfl`. -/
theorem redirect_status_308 (req : Proto.Request) :
    (redirectFor req).status = 308 := rfl

/-- **`redirect_location_prefix`.** The `Location` value the REAL `Redirect.render`
produces for the deployed template (`[.lit "https://new.example", .path]`) is
exactly `"https://new.example"` prepended to the decoded request path. Rendering
is independent of the query argument (the template has no `{query}` token). For
`/old` this is the wire's `https://new.example/old`. -/
theorem redirect_location_prefix (path query : String) :
    _root_.Redirect.render ruleTemplate path query = "https://new.example" ++ path := by
  simp [ruleTemplate, _root_.Redirect.render, _root_.Redirect.Tok.value]

/-- **`redirect_response_shape`.** The built redirect `Response` for a matched
request carries EXACTLY one header — the `Location` header, whose name is
`locationName` (byte-exact `"Location"` by `location_name_bytes`) and whose value
is the rendered location bytes — and an EMPTY body (the wire's
`Content-Length: 0`). Definitional in the gate's `toResponse`. -/
theorem redirect_response_shape (req : Proto.Request) :
    (redirectFor req).headers
      = [(locationName,
          (_root_.Redirect.redirect ruleCode ruleTemplate (decodeTarget req.target) "").location.toUTF8.toList)]
  ∧ (redirectFor req).body = [] := ⟨rfl, rfl⟩

/-! ## The concrete `/old` request the curl issues -/

/-- `GET /old` — target exactly the configured rule target `/old`. -/
def oldReq : Proto.Request :=
  { method := [71, 69, 84], target := ruleTarget, version := [], headers := [] }

/-- **`redirect_gate_fires`.** For the concrete `/old` request the gate
short-circuits: the pipeline output is exactly `ofResponse (redirectFor oldReq)`
for ANY tail and handler — the handler and every later stage are skipped. Rides
the real `redirectStage_gate`. -/
theorem redirect_gate_fires (rest : List Stage) (handler : Ctx → Response) :
    runPipeline (redirectStage :: rest) handler { input := [], req := oldReq, attrs := [] }
      = Reactor.Pipeline.runResp rest { input := [], req := oldReq, attrs := [] }
          (ResponseBuilder.ofResponse (redirectFor oldReq)) :=
  redirectStage_gate rest handler { input := [], req := oldReq, attrs := [] } rfl

/-- **`old_status_308`.** The concrete `/old` redirect carries status `308`. -/
theorem old_status_308 : (redirectFor oldReq).status = 308 := rfl

end Proto.RedirectProven

#print axioms Proto.RedirectProven.redirect_deployed
#print axioms Proto.RedirectProven.location_name_bytes
#print axioms Proto.RedirectProven.ruleTarget_bytes
#print axioms Proto.RedirectProven.redirect_status_308
#print axioms Proto.RedirectProven.redirect_location_prefix
#print axioms Proto.RedirectProven.redirect_response_shape
#print axioms Proto.RedirectProven.redirect_gate_fires
#print axioms Proto.RedirectProven.old_status_308
