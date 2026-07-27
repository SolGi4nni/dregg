/-
# Proto.XCorrProven — `x-corr: …` (the REAL Trace id) on the DEPLOYED serve

PROVE-WHAT-RUNS for the request-correlation header the running dataplane stamps on every
dispatched response. Curl-confirmed against the deployed `dataplane` binary (the wire dump
recorded in `Proto.OptionsProven` / `Proto.ServerHeaderProven`, re-run by the verifier):

    $ curl -sS -i http://127.0.0.1:9147/
    HTTP/1.1 404 Not Found
    …
    Server: drorb
    x-upstream: 1572395042
    x-corr: 79.80.84.73.79.78.83.32.47.…          ← proven here (decimal echo of the request)

The deployed pipeline's `Reactor.Deploy.headerRewriteStage` applies the REAL `Header.run`
program `Reactor.Deploy.deployProg` (= `Reactor.Lifecycle.stdRewrite ++ [set upstream,
set corr]`). The `set corrName (corrVal input)` op installs `x-corr` carrying the id the
REAL `Trace.process` assigned to this request (`Observe.corrOf` over the deployed
generator/trust). It is the LAST op, so the emitted value is exactly `corrVal input` — no
later op can clobber it.

`Proto.ServerHeaderProven` pins the sibling `Server` install and `Proto.XUpstreamProven`
the `x-upstream` install; this file pins the `x-corr` header — its wire name, the fact
that it is the outermost (last) set, and its distinctness from the two other deployed sets.

Theorems:

  * `deployed_corr_present` — for ANY plan, input, and base headers, a `Header.get x-corr`
    on the deployed rewrite output is `some (corrBytes … input)`: the REAL `Trace`-assigned
    id (re-states `Reactor.Deploy.deploy_emits_corr`; `Header.get_set_eq` on the last op).
  * `corr_name_wire_bytes` — the header name is exactly the 6 ASCII bytes of `"x-corr"`
    (`corrName` is an explicit literal — pure `rfl`).
  * `corr_distinct` — the three deployed `set` names (`Server`, `x-upstream`, `x-corr`) are
    pairwise distinct, so the outermost `x-corr` set neither is nor clobbers the others —
    non-vacuous (the names are provably unequal, pure-kernel `decide`).
-/

import Reactor.Deploy
import Reactor.Lifecycle

namespace Proto.XCorrProven

open Proto (Bytes)
open Reactor (RingSubmission)

/-! ## The deployed `x-corr` install is the outermost set — it is the served value -/

/-- **`deployed_corr_present`.** On the deployed header rewrite (`deployProg` =
`stdRewrite ++ [set upstream, set corr]`), a `Header.get x-corr` returns exactly
`Reactor.Deploy.corrVal input` — the `corrBytes` of the id the REAL `Trace.process`
assigned (`Observe.corrOf` over the deployed generator/trust) — for ANY plan, input bytes,
and base headers. `x-corr` is the LAST `set` op of `deployProg`, so `Header.get_set_eq`
reads its installed value directly, past the earlier `Server`/`x-upstream` sets and the
hop-by-hop strip. This is the correlation id the wire carries (cf. the deployed
`Reactor.Deploy.deploy_emits_corr`). -/
theorem deployed_corr_present (plan : List RingSubmission) (input : Bytes)
    (h : Header.Headers) :
    Header.get Reactor.Deploy.corrName
        (Header.run (Reactor.Deploy.deployProg plan input) h)
      = some (Reactor.Deploy.corrVal input) := by
  unfold Reactor.Deploy.deployProg Reactor.Lifecycle.stdRewrite
  rw [Header.run_append]
  simp only [Header.run_cons, Header.run_nil, Header.applyOp]
  exact Header.get_set_eq _ _ _

/-! ## The exact wire bytes -/

/-- **`corr_name_wire_bytes`.** The deployed `x-corr` header name is exactly the 6 ASCII
bytes of `"x-corr"` (`corrName` is an explicit byte literal). -/
theorem corr_name_wire_bytes :
    Reactor.Deploy.corrName = [120, 45, 99, 111, 114, 114] := rfl

/-! ## The three deployed sets are pairwise distinct (the outermost `x-corr` is faithful) -/

/-- **`corr_distinct`.** The three header names the deployed rewrite `set`s —
`Reactor.Lifecycle.serverName` (`Server`), `Reactor.Deploy.upstreamName` (`x-upstream`) and
`Reactor.Deploy.corrName` (`x-corr`) — are pairwise distinct. So the outermost `x-corr` set
is a genuine third field: it does not alias, and is not clobbered by, the `Server`/`x-upstream`
installs (`deployed_corr_present` reads it directly). Non-vacuous: the names are provably
unequal (pure-kernel `decide`). -/
theorem corr_distinct :
    Reactor.Deploy.corrName ≠ Reactor.Deploy.upstreamName
  ∧ Reactor.Deploy.corrName ≠ Reactor.Lifecycle.serverName
  ∧ Reactor.Deploy.upstreamName ≠ Reactor.Lifecycle.serverName := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Reactor.Deploy.corrName, Reactor.Deploy.upstreamName,
      Reactor.Lifecycle.serverName] <;> decide

end Proto.XCorrProven

#print axioms Proto.XCorrProven.deployed_corr_present
#print axioms Proto.XCorrProven.corr_name_wire_bytes
#print axioms Proto.XCorrProven.corr_distinct
