/-
# Proto.CorsAcaoProven — `Access-Control-Allow-Origin` on the DEPLOYED serve

PROVE-WHAT-RUNS for the CORS grant the running dataplane stamps when a request carries a
permitted `Origin`. The deployed `Reactor.Deploy.deployCorsStage` runs the REAL
`Cors.acaoValue` decision over the deployed `Reactor.Stage.Cors.corsPolicy` (one allowed
origin `https://app.example.com`, no wildcard, no credentials) on the request's canonical
lowercase `origin`, and — iff the origin is permitted — pushes `Access-Control-Allow-Origin`
onto the affine builder. Curl-confirmed against the deployed `dataplane` binary:

    $ curl -sS -i -H 'Origin: https://app.example.com' http://127.0.0.1:9147/
    HTTP/1.1 404 Not Found
    …
    Access-Control-Allow-Origin: https://app.example.com     ← proven here

    $ curl -sS -i -H 'Origin: https://evil.example.com' http://127.0.0.1:9147/
    HTTP/1.1 404 Not Found
    …
    (no Access-Control-Allow-Origin — the no-leak boundary)

The existing `Reactor.Deploy.full2_cors_acao_inner` proves the ACAO value lands in the
BUILT inner fold (`full2InnerStages` — the five deployed response transforms) whenever the
REAL `Cors.acaoValue` admits the request's origin. This file specializes it to the deployed
policy's concrete allowed origin, decides the real policy branch, and pins the wire name.

Theorems:

  * `cors_acao_value_deployed` — the REAL `Cors.acaoValue` on the deployed policy admits
    `https://app.example.com` and echoes it (no wildcard, no credentials) — pure-kernel
    `decide` over the genuine policy, NOT a stub.
  * `acao_name_wire_bytes` — the header name is exactly the 27 bytes of
    `"Access-Control-Allow-Origin"` (pure-kernel `decide` via the `Shortcuts.ba_toList_eq` bridge,
    no `native_decide`, no `Lean.ofReduceBool`).
  * `deployed_cors_acao_present` — for ANY deployed ctx whose canonical `origin` is the
    permitted `https://app.example.com`, the `(Access-Control-Allow-Origin,
    https://app.example.com)` pair genuinely appears in the BUILT deployed inner fold
    (rides `full2_cors_acao_inner` + `cors_acao_value_deployed`).
-/

import Reactor.Deploy
import Reactor.Stage.Cors
import Cors
import Proto.Kernel.Shortcuts

namespace Proto.CorsAcaoProven

open Proto (Bytes)
open Reactor.Pipeline (Ctx)
open Proto.Kernel

/-- The deployed policy's single permitted origin. -/
def deployedOrigin : String := "https://app.example.com"

/-! ## The REAL policy admits the deployed origin -/

/-- **`cors_acao_value_deployed`.** The REAL `Cors.acaoValue` over the deployed
`Reactor.Stage.Cors.corsPolicy` admits the origin `https://app.example.com` and echoes it
back (the policy has no wildcard and no credentials, so the specific origin is emitted).
Pure-kernel `decide` over the genuine policy — a stub would not agree with the real
allowlist. -/
theorem cors_acao_value_deployed :
    Cors.acaoValue Reactor.Stage.Cors.corsPolicy deployedOrigin = some deployedOrigin := by
  decide

/-! ## The exact wire name -/

/-- **`acao_name_wire_bytes`.** The deployed CORS header name is exactly the 27 bytes of
`"Access-Control-Allow-Origin"` — pinned to an explicit literal through the `Shortcuts.ba_toList_eq`
bridge (pure-kernel `decide`, no `native_decide`), matching the curl. -/
theorem acao_name_wire_bytes :
    Reactor.Stage.Cors.acaoName
      = [65, 99, 99, 101, 115, 115, 45, 67, 111, 110, 116, 114, 111, 108, 45,
         65, 108, 108, 111, 119, 45, 79, 114, 105, 103, 105, 110] := by
  simp only [Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes, Shortcuts.ba_toList_eq]; decide

/-! ## The deployed byte-effect: ACAO reaches the BUILT deployed inner fold -/

/-- **`deployed_cors_acao_present`.** For any deployed ctx whose canonical lowercase
`origin` is the permitted `https://app.example.com`, the CORS grant fires and the
`(Access-Control-Allow-Origin, https://app.example.com)` pair genuinely appears in the
BUILT deployed inner fold (`full2InnerStages` — the five deployed response transforms the
outer header rewrite wraps). Rides `Reactor.Deploy.full2_cors_acao_inner` (the composed
deployed CORS byte-effect) fed by `cors_acao_value_deployed` (the real policy branch). The
outer deploy rewrite's only header drop is the hop-by-hop strip, which keeps this non-hop
field — curl-confirmed on the wire. -/
theorem deployed_cors_acao_present (c : Ctx)
    (horigin : Reactor.Deploy.corsOriginOf c = deployedOrigin) :
    (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes deployedOrigin)
      ∈ ((Reactor.Pipeline.runPipeline Reactor.Deploy.full2InnerStages
            Reactor.Deploy.appHandler c).build).headers := by
  apply Reactor.Deploy.full2_cors_acao_inner c deployedOrigin
  rw [horigin]
  exact cors_acao_value_deployed

end Proto.CorsAcaoProven

#print axioms Proto.CorsAcaoProven.cors_acao_value_deployed
#print axioms Proto.CorsAcaoProven.acao_name_wire_bytes
#print axioms Proto.CorsAcaoProven.deployed_cors_acao_present
