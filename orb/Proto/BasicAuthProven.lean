import Reactor.Deploy
import Reactor.Stage.BasicAuth
import BasicAuth
import Proto.Kernel.Shortcuts

/-!
# Proto.BasicAuthProven — the DEPLOYED `WWW-Authenticate`/`401` (ledger row `h1.basicauth`)

PROVE-WHAT-RUNS for the RFC 7617 Basic-auth challenge. The Basic-auth gate
`Reactor.Stage.BasicAuth.basicStage` is WIRED into the deployed HTTP/1.1 fold
`Reactor.Deploy.deployStagesFull2` (element #1), so a request under `/private`
that carries no (or bad) credentials short-circuits the whole pipeline with a
`401 Unauthorized` carrying the `WWW-Authenticate: Basic realm="orb"` challenge
produced by the REAL `BasicAuth.authenticate` machine.

## Ground truth — curl against the running dataplane (io_uring, port 8080)

```
$ curl -sS -i http://127.0.0.1:8080/private
HTTP/1.1 401 Unauthorized
Connection: keep-alive
WWW-Authenticate: Basic realm="orb"
Server: drorb
Content-Length: 23

authentication required
```

Status `401`, the RFC 7235 §4.1 `WWW-Authenticate` header with value
`Basic realm="orb"`, and the 23-byte diagnostic body `authentication required`.

## What is proven here (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound})

* `basicauth_deployed` — `basicStage` really is in `deployStagesFull2`.
* `www_auth_name_bytes` — the challenge header name is exactly the ASCII bytes of
  `"WWW-Authenticate"` (`.toUTF8.toList` kernel-reduced via `Shortcuts.ba_toList_eq`).
* `unauthorized_body_bytes` — the emitted body is exactly the bytes of
  `"authentication required"` (the wire's 23-byte body).
* `basic_401_shape` — the gate's short-circuit `Response` has status `401`, a
  single header named `wwwAuthName` carrying the challenge value bytes, and the
  diagnostic body.
* `deployed_challenge_value` — the challenge value the REAL machine emits for the
  deployed config is `"Basic realm=\"" ++ "orb" ++ "\""` (i.e. `Basic realm="orb"`).
* `privateNoAuth_fires_401` — for the credential-less `GET /private` request the
  REAL `BasicAuth.authenticate` challenges and the gate emits the `401` (any tail,
  any handler), riding `basicStage_no_creds_bytes`.

The challenge value's exact BYTES (`String.toUTF8`) and the base64/verify FSM over
a *credentialed* request cross the extern boundary; the wire establishes those
octets. The in-kernel facts are the header/body byte constants, the status, the
response shape, and the challenge string structure over the real machine.
-/

namespace Proto.BasicAuthProven

open Reactor.Pipeline (Ctx Stage ResponseBuilder runPipeline)
open Reactor (Response)

open Reactor.Stage.BasicAuth
open Proto.Kernel

/-! ## The Basic-auth gate is on the DEPLOYED path -/

/-- **`basicauth_deployed`.** The Basic-auth gate `basicStage` really is an element
of the deployed HTTP/1.1 fold `deployStagesFull2` — so the `401`/`WWW-Authenticate`
challenge runs on the default request path, not in a side model. -/
theorem basicauth_deployed : basicStage ∈ Reactor.Deploy.deployStagesFull2 := by
  unfold Reactor.Deploy.deployStagesFull2
  repeat first
    | exact List.mem_cons_self _ _
    | apply List.mem_cons_of_mem

/-! ## Byte-exact challenge header name and body (pure kernel via `Shortcuts.ba_toList_eq`) -/

/-- **`www_auth_name_bytes`.** The challenge header NAME is exactly the ASCII bytes
of `"WWW-Authenticate"` (RFC 7235 §4.1). -/
theorem www_auth_name_bytes :
    wwwAuthName = [87, 87, 87, 45, 65, 117, 116, 104, 101, 110, 116, 105, 99, 97, 116, 101] := by
  show "WWW-Authenticate".toUTF8.toList = _
  rw [Shortcuts.ba_toList_eq]; decide

/-- **`unauthorized_body_bytes`.** The `401` diagnostic body is exactly the bytes
of `"authentication required"` — the wire's 23-byte body. -/
theorem unauthorized_body_bytes :
    unauthorizedBody =
      [97, 117, 116, 104, 101, 110, 116, 105, 99, 97, 116, 105, 111, 110,
       32, 114, 101, 113, 117, 105, 114, 101, 100] := by
  show "authentication required".toUTF8.toList = _
  rw [Shortcuts.ba_toList_eq]; decide

/-! ## The `401` response shape and the real challenge value -/

/-- **`basic_401_shape`.** The gate's short-circuit response `basicUnauthorized www`
has status `401`, a single header named `wwwAuthName` carrying the challenge value
bytes, and the diagnostic body. Definitional. -/
theorem basic_401_shape (www : String) :
    (basicUnauthorized www).status = 401
  ∧ (basicUnauthorized www).headers = [(wwwAuthName, strBytes www)]
  ∧ (basicUnauthorized www).body = unauthorizedBody := ⟨rfl, rfl, rfl⟩

/-- **`deployed_challenge_value`.** The challenge value the REAL `BasicAuth`
machine emits for the deployed config (`realm = "orb"`, no `charset`) is
`"Basic realm=\"" ++ "orb" ++ "\""` — the wire's `Basic realm="orb"` (RFC 7617
§2). Discharged by the library's own `challengeHeader_names_realm`. -/
theorem deployed_challenge_value :
    BasicAuth.challengeHeader stageConfig = "Basic realm=\"" ++ "orb" ++ "\"" :=
  BasicAuth.challengeHeader_names_realm stageConfig rfl

/-! ## The credential-less `/private` request fires the `401` over the REAL machine -/

/-- **`privateNoAuth_fires_401`.** For the credential-less `GET /private` request
the REAL `BasicAuth.authenticate` challenges (computed, `privateNoAuth_challenges`)
and the gate emits the `401` carrying the realm challenge header — for ANY tail and
ANY handler, the handler body never contributing. Rides `basicStage_no_creds_bytes`. -/
theorem privateNoAuth_fires_401 (rest : List Stage) (handler : Ctx → Response) :
    runPipeline (basicStage :: rest) handler privateNoAuthCtx
      = Reactor.Pipeline.runResp rest privateNoAuthCtx
          (ResponseBuilder.ofResponse
            (basicUnauthorized (BasicAuth.challengeHeader stageConfig))) :=
  basicStage_no_creds_bytes rest handler

/-- **`privateNoAuth_status_401`.** And that short-circuit's status is `401`
through a status-stable inner onion (RFC 7617 §2 maps `challenge` to `401`). -/
theorem privateNoAuth_status_401 (rest : List Stage) (handler : Ctx → Response)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (basicStage :: rest) handler privateNoAuthCtx).build).status = 401 :=
  basicStage_no_creds_status rest handler hst

end Proto.BasicAuthProven

#print axioms Proto.BasicAuthProven.basicauth_deployed
#print axioms Proto.BasicAuthProven.www_auth_name_bytes
#print axioms Proto.BasicAuthProven.unauthorized_body_bytes
#print axioms Proto.BasicAuthProven.basic_401_shape
#print axioms Proto.BasicAuthProven.deployed_challenge_value
#print axioms Proto.BasicAuthProven.privateNoAuth_fires_401
#print axioms Proto.BasicAuthProven.privateNoAuth_status_401
