/-
# Proto.XUpstreamProven — `x-upstream: 1572395042` on the DEPLOYED serve

PROVE-WHAT-RUNS for the reverse-proxy evidence header the running dataplane stamps on
every dispatched response. Curl-confirmed against the deployed `dataplane` binary (the
wire dump recorded in `Proto.ServerHeaderProven` / `Proto.OptionsProven`, re-run by the
verifier):

    $ curl -s -D - -o /dev/null http://127.0.0.1:8097/static/app.js
    HTTP/1.1 200 OK
    …
    Server: drorb
    x-upstream: 1572395042                        ← proven here
    x-corr: …

The deployed pipeline's `Reactor.Deploy.headerRewriteStage` applies the REAL `Header.run`
program `Reactor.Deploy.deployProg` (= `Reactor.Lifecycle.stdRewrite ++ [set upstream,
set corr]`) to the response headers. The `set upstreamName (upstreamVal plan)` op installs
`x-upstream` carrying the address the REAL reverse-proxy load balancer chose and the REAL
DNS parser resolved (`Proxy.targetedUpstream` of the deploy plan). It is the second-to-last
op, so the later `x-corr` set does not clobber it (`corrName ≠ upstreamName`).

`Proto.ServerHeaderProven` pins the sibling `Server: drorb` install; this file pins the
`x-upstream` header — its wire name, its survival past the `x-corr` set, and the exact
decimal bytes of the deployed value.

Theorems:

  * `deployed_upstream_present` — for ANY DNS/proxy plan, input, and base headers, a
    `Header.get x-upstream` on the deployed rewrite output is `some (upstreamVal plan)`
    (re-states `Reactor.Deploy.deployProg_upstream`; not clobbered by the later `x-corr`).
  * `upstream_name_wire_bytes` — the header name is exactly the 10 ASCII bytes of
    `"x-upstream"` (`upstreamName` is already an explicit literal — pure `rfl`).
  * `deployed_upstream_value` — on a real deployed dispatch the emitted value is
    `natBytes 1572395042` (re-states `Reactor.Deploy.deploy_emits_upstream`, the LB/DNS
    evidence), pinned through `upstream_value_wire_bytes` to the exact decimal ASCII.
  * `upstream_value_wire_bytes` — `natBytes 1572395042` is exactly the 10 bytes of
    `"1572395042"` (pure-kernel `decide` via the `Shortcuts.ba_toList_eq` bridge, no `native_decide`,
    no `Lean.ofReduceBool`), matching the curl `x-upstream: 1572395042`.
-/

import Reactor.Deploy
import Reactor.Lifecycle
import Proto.Kernel.Shortcuts

namespace Proto.XUpstreamProven

open Proto (Bytes)
open Reactor (RingSubmission)
open Proto.Kernel

/-! ## The deployed `x-upstream` install survives the later `x-corr` stamp -/

/-- **`deployed_upstream_present`.** On the deployed header rewrite (`deployProg` =
`stdRewrite ++ [set upstream, set corr]`), a `Header.get x-upstream` returns the
LB/DNS-chosen `upstreamVal plan` for ANY plan, any input bytes, any base headers — the
`x-upstream` install is not clobbered by the later `x-corr` set (`corrName ≠ upstreamName`,
`Header.get_set` locality). Re-states the deployed `Reactor.Deploy.deployProg_upstream`;
this is the header the wire carries. -/
theorem deployed_upstream_present (plan : List RingSubmission) (input : Bytes)
    (h : Header.Headers) :
    Header.get Reactor.Deploy.upstreamName
        (Header.run (Reactor.Deploy.deployProg plan input) h)
      = some (Reactor.Deploy.upstreamVal plan) :=
  Reactor.Deploy.deployProg_upstream plan input h

/-! ## The exact wire bytes -/

/-- **`upstream_name_wire_bytes`.** The deployed `x-upstream` header name is exactly the
10 ASCII bytes of `"x-upstream"` (`upstreamName` is an explicit byte literal). -/
theorem upstream_name_wire_bytes :
    Reactor.Deploy.upstreamName = [120, 45, 117, 112, 115, 116, 114, 101, 97, 109] := rfl

/-- **`upstream_value_wire_bytes`.** The deployed value `natBytes 1572395042` is exactly
the 10 bytes of `"1572395042"` — pinned to an explicit literal through the `Shortcuts.ba_toList_eq`
bridge (pure-kernel `decide`, no `native_decide`), matching the curl `x-upstream:
1572395042`. -/
theorem upstream_value_wire_bytes :
    Reactor.Deploy.natBytes 1572395042
      = [49, 53, 55, 50, 51, 57, 53, 48, 52, 50] := by
  simp only [Reactor.Deploy.natBytes, Shortcuts.ba_toList_eq]; decide

/-- **`deployed_upstream_value`.** On a real deployed dispatch (`deploySubs input =
.dispatch req :: rest`), the emitted `x-upstream` header value is exactly the 10 bytes of
`"1572395042"` — the address the REAL reverse-proxy LB chose and the REAL DNS parser
resolved. Composes `Reactor.Deploy.deploy_emits_upstream` (the LB/DNS evidence in the
served bytes) with `upstream_value_wire_bytes` (the exact decimal ASCII). -/
theorem deployed_upstream_value (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsub : Reactor.Deploy.deploySubs input = .dispatch req :: rest) :
    Header.get Reactor.Deploy.upstreamName
      (Header.run (Reactor.Deploy.deployProg
          (Reactor.Deploy.deployPlan (Reactor.Deploy.deploySubs input)) input)
        (Reactor.Lifecycle.toHeaders
          (Reactor.demoResp (Reactor.Deploy.deploySubs input)).headers))
      = some [49, 53, 55, 50, 51, 57, 53, 48, 52, 50] := by
  rw [Reactor.Deploy.deploy_emits_upstream input req rest hsub, upstream_value_wire_bytes]

end Proto.XUpstreamProven

#print axioms Proto.XUpstreamProven.deployed_upstream_present
#print axioms Proto.XUpstreamProven.upstream_name_wire_bytes
#print axioms Proto.XUpstreamProven.upstream_value_wire_bytes
#print axioms Proto.XUpstreamProven.deployed_upstream_value
