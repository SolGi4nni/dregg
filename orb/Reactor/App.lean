import Proto.Basic
import Reactor.Serialize
import Reactor.Proxy
import Route.Match
import Route.Path
import Policy.Model
import StaticFile
import Cgi
import Reactor.RouteMiddleware

/-!
# Reactor.App — the application layer: a dispatched request becomes a response

This is the interface seed the other lanes build against. It turns the reactor's
dispatch hand-off (`Proto.Request`, the payload of `Proto.Output.dispatch`) into a
`Reactor.Response` (the value the proven serializer renders) by driving the *real*
`Route.Match` library — not a stub.

The wiring:

  * `Handler` — the per-route payload (a static response for this slice: a status
    and a body). Instantiating `Route.Match.Route Handler` is what lets a route
    table carry application handlers.
  * `AppConfig` — a route table plus a default handler, the Policy admission
    state, and the adapters the policy lane fills. The default handler is folded
    into the effective table (`AppConfig.table`) so the table ALWAYS contains a
    `default` route by construction.
  * `targetSegments` — the request target bytes become path segments: drop the
    query, slash-split, then `Route.Path.normalize` (which percent-decodes once
    and runs the RFC 3986 dot-segment walk — the traversal-safe boundary).
  * `handle` — normalize the target, `Route.Match.bestMatch` over the table, and
    build a `Response` from the chosen handler.

The seam theorem is `app_routes_total`: for *any* AppConfig and request, `handle`
always produces a response (never stuck) AND that response is exactly
`responseOfHandler` of the route that the REAL `Route.Match.bestMatch` chose. A
handle that ignored `bestMatch` (a stubbed router) would fail the second
conjunct; `app_chosen_route_matches` strengthens it — the chosen route actually
matches the request (`bestMatch_sound`).

Policy is wired as a real, driven composition (`admitDecision` calls the actual
`Policy.serveDecision`), with the route→`RouteKey` adapter left as the documented
field the policy lane fills. `admit_refuses_undeclared` exercises the real
admission logic, so `Policy` is driven here, not islanded.
-/

namespace Reactor.App

open Proto (Bytes Request)

/-! ## Handlers and responses -/

/-- **The config-representable virtual-host block answer.** A `hostGlob` block route
selects one of these (via the proven `RouteAdvanced.dispatch`); it is the widened
answer type that replaces the original status+body pair, so a virtual host can
reverse-proxy / redirect / respond / serve-static PER HOST — the homelab multi-service
case. Every variant is data-parameterized (config-denotable):

  * `respond status body` — answer locally with a fixed status + body (the original
    `(Nat × Bytes)` case);
  * `proxy pool` — reverse-proxy this host's request to the named upstream pool. The
    Response projection is the `502` placeholder used off the submission path; the real
    forward is driven host-side (the deployment surfaces the proxy-vhost hostnames);
  * `redirect status location` — a `3xx` + `Location` redirect;
  * `static` — the embedded request-aware static-file handler. -/
inductive VHandler where
  | respond (status : Nat) (body : Bytes)
  | proxy (pool : Reactor.Proxy.ProxyPool)
  | redirect (status : Nat) (location : Bytes)
  | static
  /-- **A middleware-guarded route answer.** An ordered `mws` chain runs BEFORE the
    inner answer (`Reactor.RouteMw.runChain`): the first middleware that
    short-circuits (e.g. `bearerAuth`'s 401 on a rejected token) is served in place of
    `inner`; if all pass, `inner`'s response is served. This is how a config route's
    `middleware <name>` clause composes onto its handler — the effective answer is
    `middleware >>> handler`, reusing the proven `Jwt.authenticate` gate. -/
  | guarded (mws : List Reactor.RouteMw.RouteMw) (inner : VHandler)

/-- The per-route application payload. Two variants:

  * `static status body` — answer locally with a fixed response (the original
    seed case: a status and a body).
  * `proxy pool` — this route is a **reverse-proxy route**; a request matching it
    is forwarded to an upstream chosen by the REAL load balancer over `pool`
    (the `Reactor.Proxy.ProxyPool` health-filtered selection algebra). The
    submission-emitting side (a `connectUpstream` to the LB-chosen backend) is
    driven on the reactor path by `Reactor.ProxyServe`; `responseOfHandler`'s
    projection of a proxy route is only the `502` placeholder used when the
    Response path (not the proxy submission path) is taken. -/
inductive Handler where
  | static (status : Nat) (body : Bytes)
  | proxy (pool : Reactor.Proxy.ProxyPool)
  /-- A **real static-file route.** The answer is served request-aware by
    `responseOfReq`/`handle` through the proven `StaticFile.serveDeployed` (real
    bytes, content-hash ETag, conditional `304`, `Range` `206`). This constructor
    carries no payload — the file selection is driven by the request target
    segments and headers at dispatch. `responseOfHandler`'s projection is only the
    `200` totality placeholder used when the (request-blind) `Handler → Response`
    view is taken; the real answer flows through `responseOfReq`. -/
  | staticFile
  /-- A **CGI/1.1 route** (RFC 3875): the request is answered by running `script`
    as a real child process and framing its stdout (`Cgi.serveCgi`). The app layer
    coerces a `< 200` script status to `502` so the deployed final stays non-1xx
    (RFC 9110 §15.4). -/
  | cgi (script : String)
  /-- A **host/glob virtual-host route** (RFC 9110 §7.2 authority selection + `*`/`**`
    globs). The answer is served **request-aware** by `responseOfReq`/`handle` through
    the proven `RouteAdvanced.dispatch` over `blocks`: the request's `Host` authority
    selects a virtual-host block, then that block's first matching route (glob included)
    supplies the `(status, body)` answer. This wires the proven host/glob matcher
    (`Route.Match.dispatchHandler`'s engine, `RouteAdvanced.dispatch`) into the served
    path while keeping the route itself a member of the flat effective table — so
    `bestMatch_mem` (the tenant-isolation exposure argument) is preserved by
    construction: the served exposure is this one declared route, and the host/glob
    dispatch happens *within* its handler, exactly as `staticFile` selects a file.
    `responseOfHandler`'s projection is a `200` totality placeholder (the request-blind
    view); the real answer flows through `responseOfReq`, which reads the `Host` header
    and target path. -/
  | hostGlob (blocks : List (RouteAdvanced.ServerBlock VHandler))
  /-- A **redirect route** (RFC 9110 §15.4): answer with a `3xx` status and a
    `Location` header pointing at `location`. Fully data-parameterized (a status
    code + a target byte string), so it is config-representable — an operator
    declares `route /old redirect 308 https://new/` and the served response is
    exactly this handler's `status` + `Location`. `responseOfHandler` builds the
    `Location`-carrying response directly (no request data is consulted), so
    `responseOfReq` is definitionally `responseOfHandler` on this variant. -/
  | redirect (status : Nat) (location : Bytes)

/-- Reason phrase bytes for a status code (a small fixed table; the seed only
needs the codes it emits, plus the common `3xx` redirect phrases a config
`redirect` route declares). -/
def reasonFor (status : Nat) : Bytes :=
  (if status = 200 then "OK"
   else if status = 404 then "Not Found"
   else if status = 403 then "Forbidden"
   else if status = 301 then "Moved Permanently"
   else if status = 302 then "Found"
   else if status = 307 then "Temporary Redirect"
   else if status = 308 then "Permanent Redirect"
   else "").toUTF8.toList

/-- The `Location` response-header name (lower-case ASCII), carried by a
`redirect` handler's response. -/
def locationName : Bytes := "location".toUTF8.toList

/-- Build the serializer's `Response` from a handler. A `static` handler's status
and body are rendered with a derived reason phrase and no caller headers (the
serializer adds `Content-Length` by construction). A `proxy` handler has no local
Response — the real answer flows on the reactor's submission path
(`Reactor.ProxyServe`); its Response projection is a `502 Bad Gateway` placeholder
so `handle` stays total. -/
def responseOfHandler : Handler → Response
  | .static status body => { status := status, reason := reasonFor status, headers := [], body := body }
  | .proxy _ => { status := 502, reason := "Bad Gateway".toUTF8.toList, headers := [], body := "no upstream".toUTF8.toList }
  | .staticFile => { status := 200, reason := reasonFor 200, headers := [], body := "static".toUTF8.toList }
  | .cgi script =>
    -- Run the real CGI script, then uphold the deployed non-1xx (RFC 9110 §15.4)
    -- final-status invariant: a script that emits an interim `1xx` Status is
    -- coerced to `502 Bad Gateway` (a gateway rejecting an invalid upstream final).
    let r := Cgi.serveCgi script
    if 200 ≤ r.status then r
    else { status := 502, reason := "Bad Gateway".toUTF8.toList, headers := [],
           body := "cgi: invalid (interim) script status".toUTF8.toList }
  | .hostGlob _ =>
    -- Request-blind projection (the `Host`/path are unavailable here): a `200`
    -- totality placeholder. The real, host/glob-dispatched answer flows through
    -- `responseOfReq`.
    { status := 200, reason := reasonFor 200, headers := [], body := "vhost".toUTF8.toList }
  | .redirect status location =>
    -- A genuine redirect: the declared `3xx` status and a `Location` header at the
    -- declared target. No request data is consulted, so `responseOfReq` reuses this.
    { status := status, reason := reasonFor status, headers := [(locationName, location)], body := [] }

/-- The clamped `cgi` handler's status is always a genuine final (non-1xx): the
`< 200` branch forces `502`, and the pass-through branch is `≥ 200` by its guard.
The deployed §15.4 discharge rides on this even though the script output is opaque. -/
theorem cgi_status_final (script : String) : 200 ≤ (responseOfHandler (.cgi script)).status := by
  simp only [responseOfHandler]
  split
  · assumption
  · decide

/-! ## Application configuration -/

/-- The application configuration.

`routes` is the author's route table; `defaultHandler` is the catch-all folded in
as an explicit `default` route by `table`, so the effective table is total. `lid`,
`policy`, and `routeKeyOf` are the Policy admission seam: `admitDecision` drives
the real `Policy.serveDecision` with `routeKeyOf` mapping a matched route to the
opaque `Policy.RouteKey` identity the policy lane keys on. -/
structure AppConfig where
  /-- The author's route table (handlers of type `Handler`). -/
  routes : List (Route.Match.Route Handler)
  /-- The catch-all handler, applied when no author route matches. -/
  defaultHandler : Handler
  /-- The listener id this app is served on (Policy admission attribution). -/
  lid : Nat
  /-- The live Policy admission state. -/
  policy : Policy.Running
  /-- Adapter the policy lane fills: a matched route's admission key. -/
  routeKeyOf : Route.Match.Route Handler → Policy.RouteKey

/-- The effective route table: the author's routes followed by an explicit
`default` route carrying `defaultHandler`. This makes "the table contains a
default route" true by construction — `handle` is total without a side
condition. -/
def AppConfig.table (ac : AppConfig) : List (Route.Match.Route Handler) :=
  ac.routes ++ [⟨Route.Match.Pat.default, ac.defaultHandler⟩]

/-- The effective table always contains a matching default route. -/
theorem table_has_default (ac : AppConfig) :
    ∃ r ∈ ac.table, Route.Match.matchesDefault r = true := by
  refine ⟨⟨Route.Match.Pat.default, ac.defaultHandler⟩, ?_, rfl⟩
  simp [AppConfig.table]

/-! ## Target → path segments -/

/-- Interpret the target bytes as characters (one byte → one code point). Used
only to split on the structural ASCII delimiters `?` and `/`; the segment bytes
themselves are percent-decoded downstream by `Route.Path.normalize`. -/
def bytesToString (b : Bytes) : String := String.mk (b.map (fun x => Char.ofNat x.toNat))

/-- Split a request target (bytes) into normalized path segments: drop the query
(`?...`), slash-split, drop empty segments (leading `/`, doubled `//`), then run
`Route.Path.normalize` — percent-decode once and remove dot-segments (the
traversal-safe boundary). The result is exactly what `Route.Match.bestMatch`
matches against. -/
def targetSegments (target : Bytes) : List String :=
  let s := bytesToString target
  let path := (s.splitOn "?").headD ""
  let raw := (path.splitOn "/").filter (fun seg => seg != "")
  Route.Path.normalize raw

/-- The request's authoritative host as split labels: the `Host` header value split
on `.` (e.g. `a.example` → `["a","example"]`). Empty when no `Host` header is present.
Header names are canonical lowercase on the deployed path (`Reactor.Config.protoReqOf`),
so the name is matched literally as `"host"`. -/
def hostLabelsOf (req : Request) : List String :=
  match req.headers.find? (fun h => h.1 == "host".toUTF8.toList) with
  | some (_, v) => (bytesToString v).splitOn "."
  | none => []

/-- Lower-case an ASCII string (RFC 9110 §5.1 field-name case-insensitivity). Header
names are matched against a guard's declared name case-insensitively by lower-casing
both sides. -/
def lowerAscii (s : String) : String := String.mk (s.data.map Char.toLower)

/-- The request headers as `(lower-name, value)` string pairs, for guard evaluation.
Deployed header names are already canonical lowercase (`Reactor.Config.protoReqOf`);
lower-casing here makes the header-required guard robust whatever the arrival casing. -/
def headerPairsOf (req : Request) : List (String × String) :=
  req.headers.map (fun h => (lowerAscii (bytesToString h.1), bytesToString h.2))

/-- The request's query string as `(key, value)` pairs (RFC 3986 §3.4): take the
target's `?`-suffix, split on `&`, then each field on its first `=`. Empty keys are
dropped; query keys are case-sensitive. -/
def queryPairsOf (req : Request) : List (String × String) :=
  let s := bytesToString req.target
  match s.splitOn "?" with
  | _ :: rest =>
    let qs := String.intercalate "?" rest
    (qs.splitOn "&").filterMap (fun kv =>
      match kv.splitOn "=" with
      | []      => none
      | k :: vs => if k = "" then none else some (k, String.intercalate "=" vs))
  | [] => []

/-- Build a `RouteAdvanced.Req` from a `Proto.Request` for host/glob dispatch: the
`Host`-derived authority labels, the method bytes as a token, the normalized target
segments (the same traversal-safe segments `bestMatch` matches on), and now the request
headers (lower-cased names) and parsed query pairs — so the proven header-required /
query-required guards (`RouteAdvanced.headerPresent` / `queryPresent`) are consulted on
the deployed virtual-host table. -/
def hostReqOf (req : Request) : RouteAdvanced.Req :=
  { host := hostLabelsOf req
    method := bytesToString req.method
    segs := targetSegments req.target
    headers := headerPairsOf req
    query := queryPairsOf req }

/-! ## The application handler -/

/-- **Build a virtual-host block route's `Response` from its widened answer,
request-aware.** Each config-representable `VHandler` variant projects to a genuine
final (non-1xx) response:

  * `respond status body` — the fixed status + body, with a `< 200` status clamped to
    `502` (upholding the deployed non-1xx final invariant, RFC 9110 §15.4);
  * `redirect status location` — a `3xx` + `Location` redirect (a `< 200` status
    clamped to `502` the same way);
  * `static` — the embedded request-aware static-file answer
    (`StaticFile.serveDeployed` over this request's target segments + headers);
  * `proxy pool` — the `502 Bad Gateway` placeholder taken off the reverse-proxy
    submission path (the real forward is driven host-side from the surfaced
    proxy-vhost hostnames), exactly as the flat `Handler.proxy` projection. -/
def vhandlerResponse (req : Request) : VHandler → Response
  | .respond status body =>
    if 200 ≤ status then { status := status, reason := reasonFor status, headers := [], body := body }
    else { status := 502, reason := "Bad Gateway".toUTF8.toList, headers := [],
           body := "vh: invalid (interim) route status".toUTF8.toList }
  | .redirect status location =>
    if 200 ≤ status then { status := status, reason := reasonFor status,
                           headers := [(locationName, location)], body := [] }
    else { status := 502, reason := "Bad Gateway".toUTF8.toList, headers := [],
           body := "vh: invalid (interim) redirect status".toUTF8.toList }
  | .static => StaticFile.serveDeployed (targetSegments req.target) req.headers
  | .proxy _ => { status := 502, reason := "Bad Gateway".toUTF8.toList, headers := [],
                  body := "no upstream".toUTF8.toList }
  | .guarded mws inner => Reactor.RouteMw.runChain req mws (vhandlerResponse req inner)

/-- Every widened virtual-host answer is a genuine final (non-1xx): `respond`/`redirect`
clamp a `< 200` status to `502`, `static` emits only literal `200/206/304/416/404`, and
`proxy` is the `502` placeholder. -/
theorem vhandlerResponse_status_final (req : Request) (vh : VHandler) :
    200 ≤ (vhandlerResponse req vh).status := by
  induction vh with
  | respond s b => simp only [vhandlerResponse]; split
                   · assumption
                   · decide
  | redirect s l => simp only [vhandlerResponse]; split
                    · assumption
                    · decide
  | proxy p => simp only [vhandlerResponse]; decide
  | static =>
    show 200 ≤ (StaticFile.toResponse
        (StaticFile.serveConditional StaticFile.deployedConfig
          (StaticFile.reqOfHeaders req.headers) (targetSegments req.target))).status
    cases StaticFile.serveConditional StaticFile.deployedConfig
        (StaticFile.reqOfHeaders req.headers) (targetSegments req.target) <;>
      simp only [StaticFile.toResponse] <;> decide
  | guarded mws inner ih =>
    show 200 ≤ (Reactor.RouteMw.runChain req mws (vhandlerResponse req inner)).status
    exact Reactor.RouteMw.runChain_status_final req mws _ ih

/-- **Request-aware response of a chosen handler.** The `staticFile` route is
served request-aware — through the proven `StaticFile.serveDeployed` over the
request's target segments and headers (real bytes, content-hash ETag, conditional
`304`, `Range` `206`); the `hostGlob` route is served through the proven
`RouteAdvanced.dispatch` over the widened block table (the `Host` authority selects a
block, then that block's first matching route supplies a `VHandler`, built by
`vhandlerResponse`); every other handler is exactly `responseOfHandler`. This is
the projection `handle` uses, so the deployed serve answers `/static/<file>` with
real file bytes rather than the request-blind placeholder. -/
def responseOfReq (req : Request) : Handler → Response
  | .staticFile => StaticFile.serveDeployed (targetSegments req.target) req.headers
  | .hostGlob blocks =>
    match RouteAdvanced.dispatch blocks (hostReqOf req) with
    | some rt => vhandlerResponse req rt.handler
    | none    => vhandlerResponse req (.respond 404 "not found".toUTF8.toList)
  | h => responseOfHandler h

/-- Off the request-aware routes (`staticFile`, `hostGlob`), `responseOfReq` is exactly
`responseOfHandler` — the request-aware projection only differs on the handlers that
consult the request (the real static-file handler and the host/glob virtual-host
handler). -/
theorem responseOfReq_eq {req : Request} {h : Handler}
    (hne : h ≠ .staticFile) (hng : ∀ b, h ≠ .hostGlob b) :
    responseOfReq req h = responseOfHandler h := by
  cases h with
  | staticFile => exact absurd rfl hne
  | static s b => rfl
  | proxy p => rfl
  | cgi s => rfl
  | redirect s l => rfl
  | hostGlob b => exact absurd rfl (hng b)

/-- **The request-aware host/glob response is a genuine final (non-1xx).** Whatever
virtual-host block / glob route the request selects (or the `404` no-match default), the
answer is built by `vhandlerResponse`, which is `≥ 200` on every widened variant. This
feeds the deployed RFC 9110 §15.4 discharge for the `hostGlob` handler, whose
status/body are otherwise opaque to the kernel (they come from the block table). -/
theorem hostGlob_status_final (req : Request)
    (blocks : List (RouteAdvanced.ServerBlock VHandler)) :
    200 ≤ (responseOfReq req (.hostGlob blocks)).status := by
  show 200 ≤ (match RouteAdvanced.dispatch blocks (hostReqOf req) with
    | some rt => vhandlerResponse req rt.handler
    | none    => vhandlerResponse req (.respond 404 "not found".toUTF8.toList)).status
  cases RouteAdvanced.dispatch blocks (hostReqOf req) with
  | some rt => exact vhandlerResponse_status_final req rt.handler
  | none    => exact vhandlerResponse_status_final req _

/-- **The request-aware static-file response is a genuine final (non-1xx).** The
`StaticFile.toResponse` adapter emits only literal `200/206/304/416/404` statuses,
so the served `/static/<file>` response — whatever conditional/range branch fires —
is always `≥ 200`. This feeds the deployed RFC 9110 §15.4 discharge for the
`staticFile` route, whose body/status are otherwise opaque to the kernel. -/
theorem staticFile_status_final (req : Request) :
    200 ≤ (responseOfReq req .staticFile).status := by
  show 200 ≤ (StaticFile.toResponse
      (StaticFile.serveConditional StaticFile.deployedConfig
        (StaticFile.reqOfHeaders req.headers) (targetSegments req.target))).status
  cases StaticFile.serveConditional StaticFile.deployedConfig
      (StaticFile.reqOfHeaders req.headers) (targetSegments req.target) <;>
    simp only [StaticFile.toResponse] <;> decide

/-- **The application layer.** Normalize the target to segments, select a route
with the real `Route.Match.bestMatch` over the effective table, and build the
response from the chosen handler — **request-aware** (`responseOfReq`), so a
`staticFile` route serves the real conditioned file bytes for THIS request. The
`none` arm is unreachable (the table always has a default) but is spelled with the
default handler so `handle` is a plain total `def`. -/
def handle (ac : AppConfig) (req : Request) : Response :=
  match Route.Match.bestMatch ac.table (targetSegments req.target) with
  | some r => responseOfReq req r.handler
  | none   => responseOfHandler ac.defaultHandler

/-! ## The Policy admission seam (real `Policy.serveDecision`, driven)

The shapes do not line up on their own: `bestMatch` yields a `Route Handler`,
while `Policy.serveDecision` keys on an opaque `Policy.RouteKey`. `routeKeyOf` is
the adapter the policy lane fills; `admitDecision` is the genuine composition
onto the real admission function, and `admit_refuses_undeclared` drives it. The
policy lane completes the wiring by gating `handle` on `admitDecision` (see
`APP-README`). -/

/-- The admission decision for a matched route: the REAL `Policy.serveDecision`,
composed through the `routeKeyOf` adapter. -/
def admitDecision (ac : AppConfig) (r : Route.Match.Route Handler) (plaintext : Bool) :
    Option Policy.Served :=
  Policy.serveDecision ac.lid (ac.routeKeyOf r) plaintext ac.policy

/-- `admitDecision` is definitionally the real `Policy.serveDecision` — not a
stub reimplementation. -/
theorem admitDecision_is_serveDecision (ac : AppConfig) (r : Route.Match.Route Handler)
    (plaintext : Bool) :
    admitDecision ac r plaintext
      = Policy.serveDecision ac.lid (ac.routeKeyOf r) plaintext ac.policy := rfl

/-- Driving the real admission logic: an undeclared listener admits nothing. This
exercises `Policy.serveDecision`'s first gate through `admitDecision`, so `Policy`
is genuinely wired here, not islanded. -/
theorem admit_refuses_undeclared (ac : AppConfig) (r : Route.Match.Route Handler)
    (plaintext : Bool) (h : ac.policy.cfg.listener? ac.lid = none) :
    admitDecision ac r plaintext = none := by
  unfold admitDecision Policy.serveDecision
  rw [h]

/-! ## The seam theorem -/

/-- **`app_routes_total` — the anti-island seam.** For any `AppConfig` and
request, `handle` always produces a response (there is always such an `r`; the
request is never stuck), and that response is exactly `responseOfHandler` of the
route the REAL `Route.Match.bestMatch` selected over the effective table. The
totality half rides on `Route.Match.bestMatch_total` (the table always carries a
default); the correspondence half ties `handle`'s output to `bestMatch`'s choice,
so a `handle` that ignored `bestMatch` would fail it. -/
theorem app_routes_total (ac : AppConfig) (req : Request) :
    ∃ r, Route.Match.bestMatch ac.table (targetSegments req.target) = some r
       ∧ handle ac req = responseOfReq req r.handler := by
  have hsome := Route.Match.bestMatch_total (rt := ac.table)
      (req := targetSegments req.target) (table_has_default ac)
  obtain ⟨r, hr⟩ :
      ∃ r, Route.Match.bestMatch ac.table (targetSegments req.target) = some r := by
    cases hb : Route.Match.bestMatch ac.table (targetSegments req.target) with
    | none => rw [hb] at hsome; simp at hsome
    | some r => exact ⟨r, rfl⟩
  exact ⟨r, hr, by simp only [handle, hr]⟩

/-- **`app_chosen_route_matches`** — the strengthened seam: the route whose
handler produced the response actually matches the request target
(`Route.Match.bestMatch_sound`). The response is decided by a route that really
matches, not a fallback slipped in behind `bestMatch`. -/
theorem app_chosen_route_matches (ac : AppConfig) (req : Request) :
    ∃ r, Route.Match.bestMatch ac.table (targetSegments req.target) = some r
       ∧ Route.Match.matchesAny (targetSegments req.target) r = true
       ∧ handle ac req = responseOfReq req r.handler := by
  obtain ⟨r, hb, hresp⟩ := app_routes_total ac req
  exact ⟨r, hb, Route.Match.bestMatch_sound hb, hresp⟩

/-! ## A concrete instantiation (the seed, driven by real data) -/

/-- A minimal Policy config: no listeners, no routes. Enough to carry a
`Policy.Running` snapshot; the policy lane supplies the real declared surface. -/
def demoPolicyConfig : Policy.Config := { listeners := [], routes := [] }

/-! ### The `/bulk` large-body download route — a real homelab throughput endpoint

A verified server fronting real services needs a way for an operator to measure its
own throughput on a large 2xx body (a bandwidth/download probe — the LibreSpeed
`garbage.php` / Cloudflare `/__down` pattern). `bulkBody` is a genuinely large
(1 MiB) generated response, and `bulkRoute` serves it from the `anyHost` block so a
plain `GET /bulk` to the deployed listener flows a large 2xx response through the
whole `deployStagesFull2` fold. -/

/-- The size in bytes of the `/bulk` download payload: 1 MiB. A fixed, sizeable
constant so the deployed serve is measurable on a large 2xx body. -/
def bulkSize : Nat := 1048576

/-- The generated large download body: `bulkSize` copies of `'a'` (`0x61`), built by
`List.replicate` — NOT a source literal, so the module stays small while the served
body is genuinely 1 MiB. This is the `VHandler.respond 200` payload the `/bulk` route
answers with: a real, sizeable 2xx body flowing the full deployed pipeline. -/
def bulkBody : Bytes := List.replicate bulkSize (0x61 : UInt8)

/-- The served `/bulk` body is genuinely large (1 MiB) — not a placeholder. -/
theorem bulkBody_length : bulkBody.length = bulkSize := by
  simp [bulkBody]

/-- The `/bulk` route: any method, exact single-segment path `["bulk"]`, no guards,
answering `200` with the 1 MiB `bulkBody`. Lives in the `anyHost` block, so it is
served for any authority that is not one of the exact virtual hosts. -/
def bulkRoute : RouteAdvanced.Route VHandler :=
  { method := .anyMethod,
    path := { segs := [RouteAdvanced.SegPat.lit "bulk"], globstar := false },
    guards := [], handler := VHandler.respond 200 bulkBody }

/-- The deployed virtual-host / glob table the default route dispatches over
(`Route.Match.dispatchHandler`'s engine, `RouteAdvanced.dispatch`). Two exact-host
blocks discriminate authority — `a.example` and `b.example` answer with DIFFERENT bodies
for the same path — and the fallback `anyHost` block carries a `**`-glob route
(`/…/assets/**`), the large-body `/bulk` download route, and a catch-all `404`. This is
what makes host-based and glob routing observable on the wire: the request's `Host`
selects the block, then the block's first matching route (glob/bulk included) supplies
the answer. -/
def demoVhBlocks : List (RouteAdvanced.ServerBlock VHandler) :=
  [ { host := .exact ["a", "example"],
      routes := [ RouteAdvanced.catchAllRoute (VHandler.respond 200 "vhost-a".toUTF8.toList) ] },
    { host := .exact ["b", "example"],
      routes := [ RouteAdvanced.catchAllRoute (VHandler.respond 200 "vhost-b".toUTF8.toList) ] },
    { host := .anyHost,
      routes :=
        [ { method := .anyMethod,
            path := { segs := [RouteAdvanced.SegPat.lit "health", RouteAdvanced.SegPat.lit "assets"],
                      globstar := true },
            guards := [], handler := VHandler.respond 200 "glob-hit".toUTF8.toList },
          bulkRoute,
          RouteAdvanced.catchAllRoute (VHandler.respond 404 "not found".toUTF8.toList) ] } ]

/-- A concrete `AppConfig`: an exact route for `/health`, a prefix route under
`/static`, a `/cgi-bin` prefix, and a host/glob-dispatching default (`demoVhBlocks`).
The default handler routes host- and glob-aware via the proven `RouteAdvanced.dispatch`,
so an admitted-but-unmatched path (e.g. `/health/…`) is answered by the virtual-host
table: `Host: a.example` vs `b.example` return DIFFERENT bodies, and a `/health/assets/**`
glob matches. This is the seed the other lanes drive against. -/
def demoApp : AppConfig where
  routes :=
    [ ⟨Route.Match.Pat.exact ["health"], .static 200 "ok".toUTF8.toList⟩,
      ⟨Route.Match.Pat.«prefix» ["static"], .staticFile⟩,
      ⟨Route.Match.Pat.«prefix» ["cgi-bin"], .cgi "conformance/cgi-bin/hello"⟩ ]
  defaultHandler := .hostGlob demoVhBlocks
  lid := 0
  policy := Policy.init demoPolicyConfig
  routeKeyOf := fun _ => ⟨0, 0⟩

/-- The seam theorem instantiated at the concrete demo app: real routing decides
every response. -/
theorem demoApp_routes_total (req : Request) :
    ∃ r, Route.Match.bestMatch demoApp.table (targetSegments req.target) = some r
       ∧ handle demoApp req = responseOfReq req r.handler :=
  app_routes_total demoApp req

/-! ## The `/bulk` large-body route on the deployed app -/

/-- A `RouteAdvanced.Req` for `GET /bulk` under a non-vhost authority (`localhost`) —
the shape `hostReqOf` builds for a curl to the plaintext listener, whose `Host` is
neither `a.example` nor `b.example`, so the `anyHost` block is selected. -/
def bulkReq : RouteAdvanced.Req :=
  { host := ["localhost"], method := "GET", segs := ["bulk"], headers := [], query := [] }

/-- **The `/bulk` route dispatches to the large-body handler.** The REAL
`RouteAdvanced.dispatch` over the deployed `demoVhBlocks` — the exact matcher the
deployed default handler runs — selects `bulkRoute` for a `GET /bulk` under a
non-vhost authority, and its handler is exactly `respond 200 bulkBody` (the 1 MiB
body). Non-vacuous: it computes host-block selection then first-match routing. -/
theorem bulk_dispatches :
    RouteAdvanced.dispatch demoVhBlocks bulkReq = some bulkRoute := rfl

/-- **The non-vhost-authority `selectBlock` non-match: any host that is neither
`a.example` nor `b.example` selects the `anyHost` block.** The deployed `demoVhBlocks`
discriminates authority with two EXACT-host blocks (`a.example`, `b.example`) ahead of
the fallback `anyHost` block. `RouteAdvanced.selectBlock` is a first-match `find?` over
`hostMatch`; an exact block never matches a different host (`hostMatch_exact_ne`), so a
request whose authority is neither exact vhost falls through both and selects the
`anyHost` block (which `hostMatch`es every authority). This is the authority half of the
`/bulk`-any-host result: the `/bulk` route lives in `anyHost`, so it is reachable from
EVERY non-vhost host, not only `localhost`. -/
theorem demoVhBlocks_selectBlock_anyHost (req : Request)
    (hna : hostLabelsOf req ≠ ["a", "example"])
    (hnb : hostLabelsOf req ≠ ["b", "example"]) :
    RouteAdvanced.selectBlock demoVhBlocks (hostReqOf req)
      = some { host := RouteAdvanced.HostPat.anyHost,
               routes :=
                 [ { method := RouteAdvanced.MethodPat.anyMethod,
                     path := { segs := [RouteAdvanced.SegPat.lit "health",
                                        RouteAdvanced.SegPat.lit "assets"],
                               globstar := true },
                     guards := [], handler := VHandler.respond 200 "glob-hit".toUTF8.toList },
                   bulkRoute,
                   RouteAdvanced.catchAllRoute (VHandler.respond 404 "not found".toUTF8.toList) ] } := by
  unfold RouteAdvanced.selectBlock
  have e0 : RouteAdvanced.hostMatch (RouteAdvanced.HostPat.exact ["a", "example"])
      (hostReqOf req).host = false := by
    show RouteAdvanced.hostMatch (RouteAdvanced.HostPat.exact ["a", "example"])
        (hostLabelsOf req) = false
    exact RouteAdvanced.hostMatch_exact_ne hna
  have e1 : RouteAdvanced.hostMatch (RouteAdvanced.HostPat.exact ["b", "example"])
      (hostReqOf req).host = false := by
    show RouteAdvanced.hostMatch (RouteAdvanced.HostPat.exact ["b", "example"])
        (hostLabelsOf req) = false
    exact RouteAdvanced.hostMatch_exact_ne hnb
  simp only [demoVhBlocks, List.find?, e0, e1, RouteAdvanced.anyHost_matches]

/-- **The deployed app answers `/bulk` with the 1 MiB body, request-aware — for ANY
non-vhost authority.** For a request whose target normalizes to `["bulk"]` under an
authority that is neither of the exact virtual hosts `a.example`/`b.example` (any
method, any headers/query — the `/bulk` route is `anyMethod` and unguarded),
`App.handle demoApp` returns a `200` whose body is exactly `bulkBody`. The whole
deployed decision: `bestMatch` falls through the author routes to the host/glob default,
`RouteAdvanced.selectBlock` picks the `anyHost` block (`demoVhBlocks_selectBlock_anyHost`
— NOT pinned to `localhost`), its first matching route is `bulkRoute`, and
`vhandlerResponse` builds the `200` + large body. -/
theorem bulk_serves_large_body_any (req : Request)
    (htarget : targetSegments req.target = ["bulk"])
    (hna : hostLabelsOf req ≠ ["a", "example"])
    (hnb : hostLabelsOf req ≠ ["b", "example"]) :
    handle demoApp req
      = { status := 200, reason := reasonFor 200, headers := [], body := bulkBody } := by
  have hseg : (hostReqOf req).segs = ["bulk"] := by unfold hostReqOf; exact htarget
  have hb : RouteAdvanced.dispatch demoVhBlocks (hostReqOf req) = some bulkRoute := by
    unfold RouteAdvanced.dispatch RouteAdvanced.routeMatches
    rw [demoVhBlocks_selectBlock_anyHost req hna hnb, hseg]
    rfl
  unfold handle
  rw [htarget]
  show (match RouteAdvanced.dispatch demoVhBlocks (hostReqOf req) with
        | some rt => vhandlerResponse req rt.handler
        | none => vhandlerResponse req (VHandler.respond 404 "not found".toUTF8.toList)) = _
  rw [hb]
  show vhandlerResponse req (VHandler.respond 200 bulkBody) = _
  rfl

/-- **The deployed app answers `/bulk` with the 1 MiB body under a `localhost`
authority.** The `localhost` specialization of `bulk_serves_large_body_any` (`localhost`
is neither exact vhost), kept for the downstream consumers that pin the plaintext
listener's authority. -/
theorem bulk_serves_large_body (req : Request)
    (htarget : targetSegments req.target = ["bulk"])
    (hhost : hostLabelsOf req = ["localhost"]) :
    handle demoApp req
      = { status := 200, reason := reasonFor 200, headers := [], body := bulkBody } :=
  bulk_serves_large_body_any req htarget (by rw [hhost]; decide) (by rw [hhost]; decide)

/-- **The demo `/health` route is UNCHANGED by the `/bulk` addition.** `App.handle`
still answers a `/health` request with exactly `200 "ok"` — the `/bulk` route lives in
the host/glob default (`demoVhBlocks`), which `/health` never reaches (it matches the
exact author route first). Adding the download route did not perturb the existing
route surface. -/
theorem health_unchanged (req : Request) (h : targetSegments req.target = ["health"]) :
    handle demoApp req
      = { status := 200, reason := reasonFor 200, headers := [], body := "ok".toUTF8.toList } := by
  unfold handle
  rw [h]
  rfl

/-! ## The widened per-host answer is real (isolation intact over `VHandler`)

The homelab core: `host jelly.home` reverse-proxies while `host blog.home` responds —
DIFFERENT widened answers under different authorities. These witnesses execute the
proven `RouteAdvanced.dispatch` over a `VHandler` block table so per-host proxy vs
respond is not vacuous, and instantiate the proven `route_host_isolation` at the widened
type — tenant isolation is preserved, not weakened, by the wider answer. -/

/-- A `proxy`-shaped widened answer (a decidable projection, so the discrimination
witness can `decide` without comparing the opaque `ProxyPool`). -/
def isProxyVH : VHandler → Bool
  | .proxy _ => true
  | _        => false

/-- Build a `RouteAdvanced.Req` at an authority + path (any method). -/
def reqVH (host segs : List String) : RouteAdvanced.Req :=
  { host := host, method := "GET", segs := segs, headers := [], query := [] }

/-- A two-block widened vhost table: `jelly.home` reverse-proxies (the real
`demoPool`), `blog.home` responds `200 BLOG`. -/
def demoVhWiden : List (RouteAdvanced.ServerBlock VHandler) :=
  [ { host := .exact ["jelly", "home"],
      routes := [ RouteAdvanced.catchAllRoute (VHandler.proxy Reactor.Proxy.demoPool) ] },
    { host := .exact ["blog", "home"],
      routes := [ RouteAdvanced.catchAllRoute (VHandler.respond 200 "BLOG".toUTF8.toList) ] } ]

/-- **Per-host widened dispatch discriminates.** The SAME path under `jelly.home`
selects a `proxy` answer, under `blog.home` a non-proxy (`respond`) answer — host
routing over the widened `VHandler` table is real. -/
theorem demoVhWiden_discriminates :
    (RouteAdvanced.dispatch demoVhWiden (reqVH ["jelly", "home"] [])).map
        (fun r => isProxyVH r.handler) = some true
      ∧ (RouteAdvanced.dispatch demoVhWiden (reqVH ["blog", "home"] [])).map
        (fun r => isProxyVH r.handler) = some false := by
  constructor <;> rfl

/-- **Host isolation is intact over `VHandler`.** A request whose authority is not
`jelly.home` is never served by the `jelly.home` proxy block — the proven
`route_host_isolation` at the widened answer type. Widening the block answer did not
weaken tenant isolation. -/
theorem demoVhWiden_host_isolation {req : RouteAdvanced.Req}
    (hne : req.host ≠ ["jelly", "home"]) :
    RouteAdvanced.selectBlock demoVhWiden req
      ≠ some { host := .exact ["jelly", "home"],
               routes := [ RouteAdvanced.catchAllRoute (VHandler.proxy Reactor.Proxy.demoPool) ] } :=
  RouteAdvanced.route_host_isolation rfl hne

/-! ## Axiom audit for the generalized `/bulk`-any-host result -/

#print axioms demoVhBlocks_selectBlock_anyHost
#print axioms bulk_serves_large_body_any
#print axioms bulk_serves_large_body

end Reactor.App
