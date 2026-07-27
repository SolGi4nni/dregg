import Reactor.App

/-!
# Dsl.Cfg.Route — the routing dimension of a deployment

A deployment declares a **route table**: an ordered list of `(pattern, handler)`
routes, a catch-all default handler, and the adapter that maps a matched route to
the opaque `Policy.RouteKey` the admission layer keys on. This file owns ONLY that
dimension, as a standalone structure, so a grow lane adding route kinds (new
`Handler` variants, richer patterns) or admission-key policy edits this file
alone.

The three fields are exactly the author-facing surface of `Reactor.App.AppConfig`
(`routes`, `defaultHandler`, `routeKeyOf`); the listener-derived `lid`/`policy`
come from the listener dimension (`Dsl.Cfg.Listener`). `instantiate`
(`Dsl.Deployment`) folds the two dimensions into the single `AppConfig` the proven
`Reactor.App.handle` router runs — so the routing surface is authored here and the
real `Route.Match.bestMatch` selection is preserved with no re-proof.
-/

namespace Dsl.Cfg

open Reactor.App (Handler)

/-- The routing dimension: an author route table, a catch-all handler, and the
route→admission-key adapter. Mirrors the author-facing fields of
`Reactor.App.AppConfig`; the listener dimension supplies the rest. -/
structure RouteCfg where
  /-- The author's route table (handlers of type `Reactor.App.Handler`). -/
  routes : List (Route.Match.Route Handler)
  /-- The catch-all handler, applied when no author route matches. -/
  defaultHandler : Handler
  /-- The adapter mapping a matched route to its `Policy` admission key. -/
  routeKeyOf : Route.Match.Route Handler → Policy.RouteKey

end Dsl.Cfg
