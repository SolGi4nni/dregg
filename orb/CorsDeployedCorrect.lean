import Reactor.Deploy

/-!
# Reactor.Deploy.CorsDeployedCorrect — the deployed CORS stage response phase, proven GENERAL

`Reactor.Deploy.deployCorsStage` re-wires the REAL `Cors.acaoValue` decision over the
operator policy `Reactor.Stage.Cors.corsPolicy` and, iff the request origin is permitted,
stamps `Access-Control-Allow-Origin` onto the affine response builder.

The GRANT direction — a permitted origin lands its `ACAO` pair — is exercised inside the
full deployed fold. The two response-phase laws of the stage in ISOLATION, GENERAL over
EVERY context and threaded builder, live here:

* `deployCorsStage_grant` — a permitted origin (`acaoValue … = some v`) makes the response
  phase add exactly the `ACAO` header carrying `v`.
* `deployCorsStage_deny` — the SECURITY-load-bearing arm: a DISALLOWED origin
  (`acaoValue … = none`) leaves the built response byte-IDENTICAL — NO
  `Access-Control-Allow-Origin` is emitted, for EVERY context and builder. This was only
  ever established inline, with the `none` hypothesis baked into a specific dense-fold
  proof; here it is a named `∀`.
-/

namespace Reactor.Deploy

open Reactor.Pipeline (Ctx Stage ResponseBuilder)

/-- **CORS grant, general.** When the REAL `Cors.acaoValue` admits the request's origin
under the operator policy, the deployed stage's response phase stamps exactly the
`Access-Control-Allow-Origin` pair carrying that value — for EVERY context and builder. -/
theorem deployCorsStage_grant (c : Ctx) (b : ResponseBuilder) (v : String)
    (h : _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) = some v) :
    deployCorsStage.onResponse c b
      = b.addHeader (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v) := by
  show (match _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) with
        | some v => b.addHeader (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v)
        | none   => b) = _
  rw [h]

/-- **CORS deny, general (the DENY arm).** When the REAL `Cors.acaoValue` does NOT admit
the request's origin, the deployed stage's response phase is the IDENTITY: the built
response is byte-identical and carries NO `Access-Control-Allow-Origin` header — for EVERY
context and builder. The always-safe direction: an unlisted origin is never granted. -/
theorem deployCorsStage_deny (c : Ctx) (b : ResponseBuilder)
    (h : _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) = none) :
    deployCorsStage.onResponse c b = b := by
  show (match _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) with
        | some v => b.addHeader (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v)
        | none   => b) = b
  rw [h]

end Reactor.Deploy

#print axioms Reactor.Deploy.deployCorsStage_grant
#print axioms Reactor.Deploy.deployCorsStage_deny
