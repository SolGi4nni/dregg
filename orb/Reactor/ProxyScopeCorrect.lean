import Reactor.ServeStep

/-!
# Reactor.ProxyScopeCorrect — the DEPLOYED reverse proxy is confined to `/api`

The deployed effect-seam serve is `drorb_serve_step`
(`Reactor.ServeStep.serveStep`). Its reverse-proxy branch is taken **only** when
`isApiPath input` — the `/api` surface. `Reactor.ServeStep` already proves what the
proxy branch does (yields the health-checked backend, runs the response transform,
`503` on no backend). This module proves the complementary CONFINEMENT boundary of
the same deployed decision: a request that is **not** on the `/api` surface can
never cause a `proxyDial` effect — the serve cannot be tricked into forwarding an
off-route request upstream. No behaviour change — a pure proof of `serveStep`'s
existing routing.
-/

namespace Reactor.ProxyScopeCorrect

open Reactor.ServeStep

/-- **The deployed reverse proxy never forwards an off-`/api` request.** For a
request whose target is not on the `/api` surface, `serveStep` (the deployed
`drorb_serve_step`) never yields a `.proxyDial` effect — it takes the cache/`done`
branch instead. So no upstream connection is ever opened for a non-`/api` request:
the proxy is confined to its declared surface. -/
theorem serveStep_non_api_no_proxy (mask : Nat) (input : Proto.Bytes)
    (hapi : isApiPath input = false) :
    ∀ (id : BackendId) (req : Proto.Bytes) (k : Proto.Bytes → Step),
      serveStep mask input ≠ .yield (.proxyDial id req) k := by
  intro id req k
  unfold serveStep
  rw [hapi]
  cases cacheableKey input with
  | none => intro h; exact Step.noConfusion h
  | some key =>
    cases gateAdmits input with
    | false => intro h; exact Step.noConfusion h
    | true =>
      intro h
      exact Step.noConfusion h (fun he _ => Effect.noConfusion he)

/-! ## Non-vacuity — the routing predicate on real targets -/

/-- `"/health"` as ASCII bytes — an ordinary, non-proxied route. -/
def healthTarget : Proto.Bytes := [47, 104, 101, 97, 108, 116, 104]

/-- A `/health` target is NOT on the proxy surface — so it is never forwarded. -/
theorem health_not_api : isApiTarget healthTarget = false := by decide
/-- The exact `/api` route IS on the proxy surface. -/
theorem apiExact_is_api : isApiTarget apiExact = true := by decide
/-- A path under `/api/` IS on the proxy surface. -/
theorem apiSlash_is_api : isApiTarget apiSlash = true := by decide

/-- **The routing predicate genuinely discriminates.** `/health` is off-surface and
`/api/` is on-surface: the proxy confinement is a real routing boundary, not a
vacuous statement. -/
theorem proxy_scope_discriminates : isApiTarget healthTarget ≠ isApiTarget apiSlash := by decide

#print axioms serveStep_non_api_no_proxy
#print axioms health_not_api
#print axioms apiSlash_is_api

end Reactor.ProxyScopeCorrect
