import Reactor.Deploy
import Reactor.ProxyDial
import Reactor.ServeConformant
import Reactor.DeployPipeline
import Cache

/-!
# Reactor.ServeStep — the effect / continuation serve seam (proxy + CACHE)

`Reactor.step` already yields OUTPUTS the untrusted shell forwards. This module
GENERALIZES that yielded type from a *send* to an `Effect`, and turns the shell's
forward-loop into a RESUME loop. The proven serve becomes a resumable state
machine: it runs pure until it needs an I/O result the sans-IO core cannot
produce (dial a backend, look up a cache), at which point it YIELDS an `Effect`
carrying everything the shell needs to perform that one I/O, plus a CONTINUATION
that takes the I/O result bytes and keeps computing — proven. The shell executes
the yielded effect (the only thing it does) and resumes the continuation.

The payoff: the whole fabric decision — *whether* to proxy, *which* backend,
*whether* to cache, *which* key, *what* lifetime, *what* to do with the reply —
moves into proven code. The shell only moves bytes over sockets and holds the
byte-for-byte store.

## The two effect families

* **proxyDial** — the reverse-proxy forward. The proven `Reactor.ProxyDial.pick`
  chooses the backend; the shell dials it and returns the upstream reply; the
  continuation runs the FULL response-transform fold (cors / gzip /
  security-headers / header) over the reply, so a proxied response carries
  HSTS / `Server` / CORS like a normal one.
* **cacheLookup / cacheStore** — the RFC 9111 shared cache. The proven core runs
  the GATES first; only for a gate-admitted, cacheable GET does it yield
  `.cacheLookup`. On a HIT the continuation `.done`s the stored bytes WITHOUT
  running the handler — REVALIDATED against the request's preconditions (RFC
  7232: `If-None-Match` match ⇒ the proven `304`, verbatim for a plain GET); on
  a MISS it runs the fold (preconditions stripped, so the store holds the plain
  `200`), yields `.cacheStore` with the PROVEN key + lifetime, then `.done`s the
  revalidated fold bytes. Because the gate check runs BEFORE the
  lookup, a cache HIT is gate-admitted: a request the gate refuses (e.g. a
  `/admin` path with no valid credential) never reaches the store — it is the
  gate response, not a cached hit. This is the sans-IO cache done correctly, the
  reason the effect seam was chosen over a shallow dataplane cache that would
  bypass auth / rate on a hit.

## Faithfulness to the deployed serve

* On a **non-cacheable, non-proxy** request, `serveStep` `.done`-s the
  consolidated deployed serve bytes (`seamInner input` — the full deployed stage
  registry `Reactor.DeployPipeline.deployPipelineStages`) crossed by the
  `revalidate` finisher (`Date` + the conditional rewrites), the same closing
  stages the bare `conformantServe` default applies — `serveStep_noncacheable`.
* On a **gate-refused cacheable** request, `serveStep` `.done`-s the deployed
  fold (the gate response) and yields NO cache effect (`serveStep_gate_rejects`).
* On a **gate-admitted cacheable** request, `serveStep` yields `.cacheLookup key`
  with the proven key, then (on a miss) `.cacheStore key resp lifetime` with the
  proven lifetime (`serveStep_cacheable`, `cacheResume_miss`); on a hit the
  continuation `.done`s the stored bytes REVALIDATED against the request's
  preconditions (`cacheResume_hit` — `Date`-spliced for a plain GET,
  `cacheResume_hit_plain`; the proven `304`/`412` for a conditional one,
  `cacheResume_hit_notModified`/`_preconditionFailed`, RFC 7232 in the core).
* On a **proxy** request, `serveStep` `.yield`s a `proxyDial` to the proven-picked
  backend (`serveStep_proxy_yields`, `serveStep_backend_up`); the continuation
  runs the full response-transform fold over the reply (`serveStep_proxy_resume`,
  `proxyRespTransform_hsts`).
-/

namespace Reactor.ServeStep

open Proto (Bytes)
open Reactor (str serialize error4xx reasonOK Response)

/-- A backend id, matching the ids of `Reactor.ProxyDial.fleet` (0, 1, 2, …). -/
abbrev BackendId := Nat

/-- **The yielded effects.** The one I/O the shell may be asked to perform.

* `proxyDial backend req` — open a connection to `backend` (the id the proven
  pick chose) and forward `req`; the effect result is the upstream response bytes.
* `cacheLookup key` — probe the untrusted store at the PROVEN `key`; the effect
  result is the stored (gate-admitted) response bytes on a hit, EMPTY on a miss.
* `cacheStore key resp lifetime` — store `resp` under the PROVEN `key` with the
  PROVEN `lifetime` (seconds); the effect result is ignored. -/
inductive Effect where
  | proxyDial (backend : BackendId) (req : Bytes)
  | cacheLookup (key : Bytes)
  | cacheStore (key : Bytes) (resp : Bytes) (lifetime : Nat)
  deriving Repr, DecidableEq

/-- **A resumable serve step.** Either the serve is `.done` (its final response
bytes), or it `.yield`s an `Effect` and a CONTINUATION `resume` that takes the
effect's result bytes and produces the next `Step`. A multi-step fabric
(cache-lookup, then cache-store, then done) is a chain of `.yield`s ending in
`.done`. -/
inductive Step where
  | done  (resp : Bytes)
  | yield (eff : Effect) (resume : Bytes → Step)

/-! ## The proxy-route decision (proven, in the core) -/

/-- `"/api"` as ASCII bytes — the reverse-proxy route prefix. -/
def apiExact : Bytes := [47, 97, 112, 105]
/-- `"/api/"` — a path under the proxy route. -/
def apiSlash : Bytes := [47, 97, 112, 105, 47]
/-- `"/api?"` — the proxy route with a query string. -/
def apiQuery : Bytes := [47, 97, 112, 105, 63]

/-- Is a request target one the reverse proxy forwards? -/
def isApiTarget (t : Bytes) : Bool :=
  t == apiExact || Reactor.Deploy.isPrefixB apiSlash t || Reactor.Deploy.isPrefixB apiQuery t

/-- The request the deployed reactor dispatched for these input bytes. -/
def reqOf (input : Bytes) : Proto.Request :=
  (Reactor.Deploy.dispatchReqOf (Reactor.Deploy.deploySubs input)).getD ({} : Proto.Request)

/-- Does this request take the reverse-proxy path? -/
def isApiPath (input : Bytes) : Bool := isApiTarget (reqOf input).target

/-- The session-affinity key the proven pick keys on. -/
def stickyKey (input : Bytes) : Nat := Reactor.ProxyDial.keyOf (reqOf input).target

/-- **The 503 the core emits when no backend is eligible.** -/
def serviceUnavailable503 : Response :=
  error4xx 503 (str "Service Unavailable") (str "no healthy upstream\n")

/-! ## The proven cache decision (key + cacheability + lifetime, in the core) -/

/-- `"GET"` as ASCII bytes. -/
def getMethod : Bytes := [71, 69, 84]
/-- `"/static"` as ASCII bytes — a cacheable static-asset route prefix. -/
def staticPrefix : Bytes := [47, 115, 116, 97, 116, 105, 99]

/-- Is the request a `GET`? Only GETs are cacheable (§4). -/
def isGet (req : Proto.Request) : Bool := req.method == getMethod

/-- Is this target a cacheable route? The static-asset prefix (a genuine 200 to
cache) OR the `/admin` prefix (a GATED route — included precisely so the
gate-before-cache ordering is exercised: an `/admin` request is cacheable-shaped,
yet the gate refuses it before any lookup). -/
def isCacheableTarget (t : Bytes) : Bool :=
  Reactor.Deploy.isPrefixB staticPrefix t || Reactor.Deploy.isPrefixB Reactor.Deploy.adminPrefix t

/-- **The proven cache KEY**: `method ++ " " ++ target` (§4.1 exact-key match over
method + request-target). The shell stores/loads under exactly these bytes — it
never derives a key of its own. -/
def cacheKeyOf (req : Proto.Request) : Bytes := req.method ++ [32] ++ req.target

/-- `range` (lowercase) — the RFC 7233 request header field-name. -/
def rangeNameLower : Bytes := [114, 97, 110, 103, 101]

/-- Does the request carry a `Range` header (RFC 7233)? A Range request is NOT
admitted to the cache path: the store holds the FULL `200` representation and the
`206`/`416` materialization is the fold's (the app's) job — so the core DECLINES
the lookup and `serveStep` serves the deployed fold directly
(`serveStep_noncacheable`), which genuinely answers the range. The decision is in
the proven core, not a host prefilter. -/
def hasRange (req : Proto.Request) : Bool :=
  (Reactor.Stage.ConditionalRequest.headerVal rangeNameLower req.headers).isSome

/-- **The proven cacheability decision (request phase).** `some key` iff the
request is a cacheable, range-free GET; `none` otherwise. Request-only, so a HIT
can skip the handler entirely. -/
def cacheableKey (input : Bytes) : Option Bytes :=
  let req := reqOf input
  if isGet req && isCacheableTarget req.target && !hasRange req then some (cacheKeyOf req)
  else none

/-- The freshness directives the deployed cache resolves for a cacheable route:
`max-age=60` (no `s-maxage`, no `Expires`). -/
def cacheDirectives : _root_.Cache.Directives :=
  { sMaxAge := none, maxAge := some 60, expiresMinusDate := none }

/-- **The proven freshness LIFETIME** (seconds), via the real §4.2.1
`Cache.selectLifetime` over `cacheDirectives`. This is the lifetime the shell
stores under — the proven core decides it, the shell never invents a TTL. -/
def cacheLifetime : Nat := (_root_.Cache.selectLifetime cacheDirectives).getD 0

/-- The proven lifetime is exactly `Cache.selectLifetime`'s `max-age` selection. -/
theorem cacheLifetime_is_selectLifetime :
    _root_.Cache.selectLifetime cacheDirectives = some cacheLifetime := rfl

/-- The concrete resolved lifetime is 60s. -/
theorem cacheLifetime_eq : cacheLifetime = 60 := rfl

/-! ## The GATE check (proven, runs BEFORE the cache lookup)

A cacheable request is admitted to the cache only if it passes the deployed
credential gate. `gateAdmits` runs the REAL `Reactor.Deploy.jwtAdminStage`
request phase (the genuine `Jwt.authenticate` FSM, scoped to `/admin*`): off
`/admin` it always admits; on `/admin*` a request the FSM refuses does NOT
admit. Because `serveStep` consults `gateAdmits` before yielding `.cacheLookup`,
a gate-refused request never touches the store — a cache HIT is gate-admitted. -/
def gateAdmits (input : Bytes) : Bool :=
  match Reactor.Deploy.jwtAdminStage.onRequest (Reactor.Deploy.ctxOf input) with
  | .continue _ => true
  | .respond _  => false

/-! ## The full response-transform fold over an upstream reply (proxy)

The seed's proxy resume ran only the (identity) HTML transform. This runs the
FULL response-phase fold — the SAME cors / gzip / security-headers / header
stages the deployed serve applies — over the upstream reply, so a proxied
response gets HSTS / `Server` / CORS / gzip. The reply bytes are parsed into a
`Response`, run through the transform stages, and re-serialized. -/

/-- Split response bytes at the first CRLF-CRLF into `(head, body)`. -/
def splitHeadBody : Bytes → Bytes × Bytes
  | 13 :: 10 :: 13 :: 10 :: rest => ([], rest)
  | b :: rest => let (h, body) := splitHeadBody rest; (b :: h, body)
  | [] => ([], [])

/-- Split head bytes into CRLF-separated lines. -/
def splitCRLFLines : Bytes → List Bytes
  | [] => [[]]
  | 13 :: 10 :: rest => [] :: splitCRLFLines rest
  | b :: rest =>
    match splitCRLFLines rest with
    | [] => [[b]]
    | l :: ls => (b :: l) :: ls

/-- The bytes after the first space. -/
def afterFirstSpace : Bytes → Bytes
  | [] => []
  | 32 :: rest => rest
  | _ :: rest => afterFirstSpace rest

/-- The bytes up to the first space. -/
def beforeFirstSpace : Bytes → Bytes
  | [] => []
  | 32 :: _ => []
  | b :: rest => b :: beforeFirstSpace rest

/-- The bytes up to the first colon (the header name). -/
def beforeColon : Bytes → Bytes
  | [] => []
  | 58 :: _ => []
  | b :: rest => b :: beforeColon rest

/-- The bytes after the first colon (the raw header value). -/
def afterColon : Bytes → Bytes
  | [] => []
  | 58 :: rest => rest
  | _ :: rest => afterColon rest

/-- Does the line contain a colon (a `name: value` header)? -/
def hasColon : Bytes → Bool
  | [] => false
  | 58 :: _ => true
  | _ :: rest => hasColon rest

/-- Drop leading ASCII spaces. -/
def trimLeadingSpace : Bytes → Bytes
  | 32 :: rest => trimLeadingSpace rest
  | bs => bs

/-- Parse a decimal ASCII byte run into a `Nat` (non-digits skipped). -/
def parseNat (bs : Bytes) : Nat :=
  bs.foldl (fun a b => if 48 ≤ b.toNat ∧ b.toNat ≤ 57 then a * 10 + (b.toNat - 48) else a) 0

/-- Lowercase one ASCII byte. -/
def lowerByte (b : UInt8) : UInt8 :=
  if 65 ≤ b.toNat ∧ b.toNat ≤ 90 then UInt8.ofNat (b.toNat + 32) else b

/-- `"content-length"` (lowercase) — the framing header the serializer re-derives,
so it is dropped from the parsed upstream headers to avoid a duplicate. -/
def contentLengthLower : Bytes := [99, 111, 110, 116, 101, 110, 116, 45, 108,
  101, 110, 103, 116, 104]

/-- Is this header name `Content-Length` (case-insensitive)? -/
def isContentLength (name : Bytes) : Bool := name.map lowerByte == contentLengthLower

/-- **Parse an upstream HTTP/1.1 reply into a `Response`.** Status code + reason
from the status line, the header block (dropping `Content-Length`, which the
serializer re-derives), and the body after the blank line. Total. -/
def parseUpstream (bs : Bytes) : Response :=
  let (head, body) := splitHeadBody bs
  match splitCRLFLines head with
  | [] => { status := 200, reason := reasonOK, headers := [], body := bs }
  | statusLine :: hlines =>
    let afterVer := afterFirstSpace statusLine
    let status := parseNat (beforeFirstSpace afterVer)
    let reason := afterFirstSpace afterVer
    let headers := hlines.filterMap (fun line =>
      if hasColon line then
        let name := beforeColon line
        if isContentLength name then none
        else some (name, trimLeadingSpace (afterColon line))
      else none)
    { status := status, reason := reason, headers := headers, body := body }

open Reactor.Pipeline (Stage runPipeline ResponseBuilder pipeline_stage_effect)

/-- The response-transform stages a proxied reply runs through — the SAME
cors / gzip / security-headers / header response phase the deployed fold applies. -/
def proxyRespStages : List Stage :=
  [ Reactor.Deploy.deployCorsStage
  , Reactor.Stage.Gzip.gzipStage
  , Reactor.Stage.SecurityHeaders.securityheadersStage
  , Reactor.Stage.Header.headerStage ]

/-- **The proven response transform over the upstream reply.** Parse the reply,
run the full response-transform fold (keyed on the ORIGINAL request context so
CORS/gzip see the client's `Origin`/`Accept-Encoding`), and re-serialize. A
proxied response now carries HSTS / `Server` / CORS / gzip like a normal one. -/
def proxyRespTransform (input upstream : Bytes) : Bytes :=
  serialize ((runPipeline proxyRespStages
    (fun _ => parseUpstream upstream) (Reactor.Deploy.ctxOf input)).build)

/-! ## Conditional revalidation on the cache path (RFC 7232, IN the core)

A cache HIT serves STORED bytes without the handler — so the precondition
decision (`If-None-Match` match ⇒ `304`, `If-Match` mismatch ⇒ `412`, RFC 7232
§3.1/§3.2) must be made HERE, in the proven core, over the stored
representation. Previously the HIT arm returned the stored full `200` verbatim
and an unproven Rust prefilter excluded conditional requests from the seam;
that correctness decision now lives in the core.

The rewrite REUSED is the proven `Reactor.Stage.ConditionalRequest.
conditionalRewrite` (H1/H2/H3/H5 of the extended conformance probe), applied to
the parsed stored response (`Proto.ResponseParse.parse`, the proven inverse of
`serialize` — `parse_serialize`). A precondition-free request takes the
identity branch and serves the stored bytes VERBATIM (no parse, no re-cons —
byte-identical to the old behavior; justified against the rewrite by
`conditionalRewrite_noCond`).

On a MISS the fold runs on the request with its precondition headers STRIPPED
(`ServeConformant.stripCondReq` — the same discipline the conformant wrapper
uses, because the deployed app's own direction-blind precondition answer must
not decide the STORED representation): the store then always holds the plain
`200`, and the miss continuation revalidates the fold bytes the same way, so a
conditional request is answered correctly even on a cold cache and can never
poison the store with a `304`. -/

open Reactor.Stage.ConditionalRequest (conditionalRewrite respETag ifNoneMatchMatches
  ifMatchFails notModifiedOf preconditionFailedOf headerVal ifNoneMatchNameLower
  ifMatchNameLower)
open Reactor.ServeConformant (hasConditional stripCondReq injectDate addDate dateFinish)
open Reactor.Stage.DateCondition (hasDateCond)

/-- Drop any parsed `Content-Length` header — the serializer re-derives framing
from the (possibly `304`-stripped) body, the same discipline as `parseUpstream`.
Without this a `304`'s re-serialization would carry the stored `200`'s stale
length next to the derived one. -/
def dropCL (resp : Response) : Response :=
  { resp with headers := resp.headers.filter (fun kv => !isContentLength kv.1) }

/-- **The RFC finisher the cache-path response bytes cross — the SAME accepted-path
finisher the bare `conformantServe` default applies** (`Reactor.ServeConformant.
condRewriteBytes` / `injectDate`), so the effect seam closes a cacheable route
through the deployed default's closing stages rather than a divergent shortcut.
Always splices `Date` (F1). For a request carrying a precondition it parses the
stored representation and applies, over the CL-dropped record, the entity-tag
`conditionalRewrite` (RFC 7232 — `If-None-Match` match ⇒ `304`, `If-Match`
mismatch ⇒ `412`) THEN the date-conditional `dateFinish` (RFC 9110 §13.1.3 /
§13.1.4, with §13.2.2 precedence: the entity-tag verdict runs first), then
re-serializes with `Date`. A precondition-free request takes the plain `Date`
splice, byte-identical to the default's non-conditional accept. Total. -/
def revalidate (req : Proto.Request) (bytes : Bytes) : Bytes :=
  if hasConditional req then
    match Proto.ResponseParse.parse bytes with
    | some resp => serialize (addDate (dateFinish req (conditionalRewrite req (dropCL resp))))
    | none => injectDate bytes
  else injectDate bytes

/-- The input the MISS fold runs on: for a conditional request, the request with
its precondition headers stripped and re-serialized
(`Proto.RequestSerialize.parse_serialize`-faithful, the `ServeConformant.
condInnerInput` discipline) so the STORED representation is the plain `200`;
for everything else, `input` VERBATIM. -/
def cacheFoldInput (input : Bytes) : Bytes :=
  if hasConditional (reqOf input) then
    Proto.RequestSerialize.serialize (stripCondReq (reqOf input))
  else input

/-- A precondition-free request's fold input is `input` verbatim. -/
theorem cacheFoldInput_plain (input : Bytes)
    (h : hasConditional (reqOf input) = false) : cacheFoldInput input = input := by
  simp [cacheFoldInput, h]

/-- A precondition-free request's revalidation is the plain `Date` splice — the
same non-conditional accept the `conformantServe` default produces (`injectDate`
the inner fold bytes). -/
theorem revalidate_plain (req : Proto.Request) (bytes : Bytes)
    (h : hasConditional req = false) : revalidate req bytes = injectDate bytes := by
  simp [revalidate, h]

/-- `dateFinish` is the identity on a request carrying no date conditional
(`If-Modified-Since` / `If-Unmodified-Since`): an entity-tag-only precondition
leaves the date-conditional finisher inert. -/
theorem dateFinish_noDate (req : Proto.Request) (resp : Response)
    (h : hasDateCond req = false) : dateFinish req resp = resp := by
  simp [dateFinish, h]

/-- A conditional request's revalidation IS the proven entity-tag
`conditionalRewrite` THEN the date-conditional `dateFinish` over the parse
(CL-dropped), re-serialized with `Date` — the default's `condRewriteBytes`. -/
theorem revalidate_conditional (req : Proto.Request) (bytes : Bytes) (resp : Response)
    (hc : hasConditional req = true) (hp : Proto.ResponseParse.parse bytes = some resp) :
    revalidate req bytes
      = serialize (addDate (dateFinish req (conditionalRewrite req (dropCL resp)))) := by
  simp [revalidate, hc, hp]

/-- **The identity branch loses nothing:** with no precondition header the proven
rewrite is itself the identity, on ANY response — so serving the stored bytes
verbatim on the plain path EQUALS applying `conditionalRewrite` to the parse.
(This is the byte-level shortcut's faithfulness obligation.) -/
theorem conditionalRewrite_noCond (req : Proto.Request) (resp : Response)
    (h : hasConditional req = false) : conditionalRewrite req resp = resp := by
  have hn : headerVal ifNoneMatchNameLower req.headers = none := by
    cases ho : headerVal ifNoneMatchNameLower req.headers with
    | none => rfl
    | some v =>
      unfold Reactor.ServeConformant.hasConditional at h
      rw [ho] at h; simp at h
  have hm : headerVal ifMatchNameLower req.headers = none := by
    cases ho : headerVal ifMatchNameLower req.headers with
    | none => rfl
    | some v =>
      unfold Reactor.ServeConformant.hasConditional at h
      rw [ho] at h; simp at h
  have him : ∀ etag, ifMatchFails req etag = false := fun etag => by
    unfold Reactor.Stage.ConditionalRequest.ifMatchFails; rw [hm]
  have hinm : ∀ etag, ifNoneMatchMatches req etag = false := fun etag => by
    unfold Reactor.Stage.ConditionalRequest.ifNoneMatchMatches; rw [hn]
  cases h200 : (resp.status == 200) with
  | false => exact Reactor.Stage.ConditionalRequest.conditionalRewrite_not200 req resp h200
  | true =>
    cases hres : respETag resp with
    | none => exact Reactor.Stage.ConditionalRequest.conditionalRewrite_noEtag req resp h200 hres
    | some etag =>
      exact Reactor.Stage.ConditionalRequest.conditionalRewrite_passes req resp etag
        h200 hres (him etag) (hinm etag)

/-- `dropCL` recovers the pre-serialization record: the wire form is the record
plus the ONE derived `Content-Length`, so dropping CL from the parse of
`serialize resp` gives back `resp` (for a record carrying no CL of its own —
every built fold response). -/
theorem dropCL_wireForm (resp : Response)
    (hcl : ∀ kv ∈ resp.headers, isContentLength kv.1 = false) :
    dropCL (Proto.ResponseParse.wireForm resp) = resp := by
  unfold dropCL Proto.ResponseParse.wireForm
  have hkeep : resp.headers.filter (fun kv => !isContentLength kv.1) = resp.headers :=
    List.filter_eq_self.mpr (fun kv hkv => by rw [hcl kv hkv]; rfl)
  have hclname : isContentLength Reactor.clName = true := by decide
  simp [List.filter_append, hkeep, hclname]

/-- **THE revalidation spec, on serialize-shaped stored bytes.** For a
precondition-bearing request and ANY stored representation `serialize R`
(well-formed, CL-free — every built fold response), the byte-level revalidation IS
the default's conditional finisher: the entity-tag `conditionalRewrite` THEN the
date-conditional `dateFinish`, re-serialized with `Date`. The parse round-trip
(`parse_serialize` + `dropCL_wireForm`) recovers `R` from the stored bytes. -/
theorem revalidate_stored (req : Proto.Request) (R : Response)
    (hwf : Proto.ResponseParse.WF R)
    (hcl : ∀ kv ∈ R.headers, isContentLength kv.1 = false)
    (hc : hasConditional req = true) :
    revalidate req (serialize R)
      = serialize (addDate (dateFinish req (conditionalRewrite req R))) := by
  rw [revalidate_conditional req _ _ hc (Proto.ResponseParse.parse_serialize R hwf),
    dropCL_wireForm R hcl]

/-! ## The resumable serve -/

/-- **The consolidated deployed fold the effect seam runs.** The SAME ordered stage
registry the bare host default folds (`Reactor.DeployPipeline.deployPipelineStages`),
over the non-metered request context (`Reactor.Deploy.ctxOf`): the metered
IP-filter / rate gates are keyed on accept-path attributes this context omits, so
they are the identity here — exactly as the seam's own `gateAdmits` is the
admission authority, and byte-identical to the default serve for any request the
gates would admit.

This REPLACES the seam's former divergent fourteen-stage fold
(`Reactor.Deploy.servePipelineFull2`). The stages the default carries but the old
seam fold did not — `Content-Location` canonicalization (RFC 9110 §8.7),
`Cache-Control` freshness, `Vary`, the range / revalidation stages — now reach
every effect-seam route; the `x-corr` scrub is applied at the single `encodeStep`
DONE exit, and `revalidate` adds `Date` + the conditional rewrites over these
bytes. So the seam's served bytes ARE the default's `conformantServe`
accepted-path bytes, and a fix to a pipeline stage or the conditional finisher
now reaches BOTH serve paths. -/
def seamInner (input : Bytes) : Bytes :=
  serialize (Reactor.DeployPipeline.deployPipelineRespOf (Reactor.Deploy.ctxOf input))

/-- Continuation of the cache lookup: on a HIT (non-empty stored bytes) `.done`
the stored bytes REVALIDATED against the request's preconditions — a plain GET
serves them `Date`-spliced, an `If-None-Match` match serves the proven `304` — the
handler still never runs; on a MISS ([]) run the deployed fold on the
precondition-STRIPPED input (so the STORED representation is the plain `200`),
yield `.cacheStore` with the PROVEN key + lifetime, then `.done` the revalidated
fold bytes. -/
def cacheResume (key input : Bytes) : Bytes → Step := fun hit =>
  match hit with
  | [] =>
    let resp := seamInner (cacheFoldInput input)
    .yield (.cacheStore key resp cacheLifetime)
      (fun _ => .done (revalidate (reqOf input) resp))
  | _ => .done (revalidate (reqOf input) hit)

/-- **The resumable deployed serve.**

* a **proxy** request whose proven pick finds an eligible backend `.yield`s a
  `proxyDial`, with a continuation that runs the full response-transform fold
  over the reply; no eligible backend ⇒ the core's 503;
* a **gate-admitted cacheable** request `.yield`s `.cacheLookup key` (the proven
  key), with `cacheResume` as its continuation;
* a **gate-refused cacheable** request, and every **non-cacheable, non-proxy**
  request, `.done`s the consolidated deployed serve bytes — the `seamInner` fold
  crossed by the same `revalidate` finisher (`Date` + the conditional rewrites)
  the cache path uses, so a non-cached route is served through the deployed
  default's closing stages.

Total. `mask` is the shell's one live input (the health/breaker bitmask). -/
def serveStep (mask : Nat) (input : Bytes) : Step :=
  match isApiPath input with
  | true =>
    match Reactor.ProxyDial.pick mask (stickyKey input) with
    | some id => .yield (.proxyDial id input) (fun up => .done (proxyRespTransform input up))
    | none    => .done (serialize serviceUnavailable503)
  | false =>
    match cacheableKey input with
    | none => .done (revalidate (reqOf input) (seamInner input))
    | some key =>
      if gateAdmits input then
        .yield (.cacheLookup key) (cacheResume key input)
      else
        .done (revalidate (reqOf input) (seamInner input))

/-- **The config-driven deployed serve.** Identical to `serveStep`, except the
reverse-proxy branch dials with a CONFIG-supplied LB policy chain
(`Reactor.ProxyDial.pickWith policies`) — the chain the DSL's
`Dsl.Cfg.UpstreamCfg.dialChain` produces from the deployment's declared
`LbPolicy`. So a deployment selecting round-robin vs least-connections routes a
proxied request to a different backend. `serveStep` is the `policies =
dialPolicies` instance (`serveStepWith_default`). -/
def serveStepWith (policies : List Proxy.Policy) (mask : Nat) (input : Bytes) : Step :=
  match isApiPath input with
  | true =>
    match Reactor.ProxyDial.pickWith policies mask (stickyKey input) with
    | some id => .yield (.proxyDial id input) (fun up => .done (proxyRespTransform input up))
    | none    => .done (serialize serviceUnavailable503)
  | false =>
    match cacheableKey input with
    | none => .done (revalidate (reqOf input) (seamInner input))
    | some key =>
      if gateAdmits input then
        .yield (.cacheLookup key) (cacheResume key input)
      else
        .done (revalidate (reqOf input) (seamInner input))

/-- **No regression.** The config-driven serve at the deployed default chain is
the original serve, byte-for-byte — the config knob defaults to today's behavior. -/
theorem serveStepWith_default (mask : Nat) (input : Bytes) :
    serveStepWith Reactor.ProxyDial.dialPolicies mask input = serveStep mask input := rfl

/-- **The deployed default dial chain, READ from the config.** The LB projection
`Reactor.Deploy.defaultDeployment.dialChain` produces for the deployed `api` pool —
the value the deployed step (`drorb_serve_step`) threads through `serveStepWith`.
Proven equal to the hardcoded default chain, so the deployed serve now reads the
config projection while emitting byte-identical bytes. -/
def deployDialChain : List Proxy.Policy :=
  Reactor.Deploy.defaultDeployment.dialChain Reactor.Deploy.proxyPoolName

/-- The deployed config's default dial chain IS the hardcoded default. -/
theorem deployDialChain_eq : deployDialChain = Reactor.ProxyDial.dialPolicies := rfl

/-- **The deployed serve, config-read, is byte-identical.** Threading the config
projection `deployDialChain` through `serveStepWith` reproduces `serveStep` exactly
— so `drorb_serve_step` reading the config regresses nothing. -/
theorem serveStepWith_deploy (mask : Nat) (input : Bytes) :
    serveStepWith deployDialChain mask input = serveStep mask input := rfl

/-! ## The resume loop (multi-effect replay), and the FFI framing

The shell drives `serveStep` as a loop: cross `drorb_serve_step` → inspect the
`Step` → execute the yielded effect → cross `drorb_serve_resume` with the ORIGINAL
`(mask, input)` and the GROWING list of effect results. No Lean closure crosses
the FFI. `stepFeed` REPLAYS `serveStep` (pure ⇒ deterministic) and feeds each
recorded result into successive continuations, returning the next `Step` — which
the shell re-encodes and either writes (`.done`) or drives one more effect. -/

/-- Feed a list of effect results into a step's continuations, in order. -/
def stepFeed : Step → List Bytes → Step
  | s, [] => s
  | .done b, _ => .done b
  | .yield _ k, r :: rs => stepFeed (k r) rs

/-- Feeding no results leaves the step unchanged. -/
@[simp] theorem stepFeed_nil (s : Step) : stepFeed s [] = s := by
  cases s <;> rfl

/-- Feeding into a `.done` step is a no-op (nothing to resume). -/
@[simp] theorem stepFeed_done (b : Bytes) (rs : List Bytes) :
    stepFeed (.done b) rs = .done b := by
  cases rs <;> rfl

/-- Feeding one result into a `.yield` steps its continuation. -/
@[simp] theorem stepFeed_yield (e : Effect) (k : Bytes → Step) (r : Bytes) (rs : List Bytes) :
    stepFeed (.yield e k) (r :: rs) = stepFeed (k r) rs := rfl

/-- Extract the final bytes of a `.done` step (`[]` if still `.yield`ing). -/
def stepDone : Step → Bytes
  | .done b    => b
  | .yield _ _ => []

/-- **Resume.** Replay `serveStep mask input` and feed the recorded `results`. -/
def resumeStep (mask : Nat) (input : Bytes) (results : List Bytes) : Step :=
  stepFeed (serveStep mask input) results

/-! ### Byte framing for the two `ByteArray → ByteArray` exports -/

/-- Tag byte of a `.done` step. -/
def tagDone : UInt8 := 0
/-- Tag byte of a `.yield (proxyDial …)` step. -/
def tagYieldProxy : UInt8 := 1
/-- Tag byte of a `.yield (cacheLookup …)` step. -/
def tagYieldCacheLookup : UInt8 := 2
/-- Tag byte of a `.yield (cacheStore …)` step. -/
def tagYieldCacheStore : UInt8 := 3

/-- Big-endian `Nat` from four bytes. -/
def be32 (a b c d : UInt8) : Nat :=
  a.toNat <<< 24 ||| b.toNat <<< 16 ||| c.toNat <<< 8 ||| d.toNat

/-- Four big-endian bytes of a `Nat` (low 32 bits; `UInt8.ofNat` truncates). -/
def be32enc (n : Nat) : Bytes :=
  [UInt8.ofNat (n >>> 24), UInt8.ofNat (n >>> 16), UInt8.ofNat (n >>> 8), UInt8.ofNat n]

/-- **Encode a `Step` for the shell.**

* `.done`            → `tagDone :: resp`
* `proxyDial id req` → `tagYieldProxy :: id :: req`
* `cacheLookup key`  → `tagYieldCacheLookup :: key` (rest is the key)
* `cacheStore …`     → `tagYieldCacheStore :: lifetime(4 BE) :: keyLen(4 BE) :: key :: resp`
-/
def encodeStep : Step → Bytes
  -- The effect-seam serve (`drorb_serve_step` / `drorb_serve_resume`) is NOT wrapped
  -- by `conformantServe`, so — unlike the metered path — its DONE response would
  -- otherwise reach the wire carrying the deployed fold's internal `x-corr` /
  -- `x-upstream` head lines (the cacheable `/static` · `/admin` routes cross here).
  -- Scrub them at the single DONE exit both the step and the resume replay funnel
  -- through, so every effect-seam route is scrubbed exactly as the metered path is.
  | .done b => tagDone :: Reactor.ServeConformant.scrubCorr b
  | .yield (.proxyDial id req) _ => tagYieldProxy :: UInt8.ofNat id :: req
  | .yield (.cacheLookup key) _ => tagYieldCacheLookup :: key
  | .yield (.cacheStore key resp lifetime) _ =>
      tagYieldCacheStore :: (be32enc lifetime ++ be32enc key.length ++ key ++ resp)

/-- Decode `count` length-prefixed (4-byte BE) results from a byte run, returning
the results and the unconsumed tail. Structural on `count`. -/
def decodeResults : Nat → Bytes → List Bytes × Bytes
  | 0, rest => ([], rest)
  | Nat.succ k, l0 :: l1 :: l2 :: l3 :: rest =>
      let n := be32 l0 l1 l2 l3
      let r := rest.take n
      let (rs, tail) := decodeResults k (rest.drop n)
      (r :: rs, tail)
  | Nat.succ _, _ => ([], [])

/-- **Decode + run the `drorb_serve_resume` frame.** The shell frames the resume
input as `mask :: reqLen(4 BE) :: request(reqLen) :: count :: (resultLen(4 BE) ::
result)*`, so the pure core recovers `(mask, input)` to replay plus the recorded
effect results. Returns the RE-ENCODED next `Step` (the shell drives to `.done`). -/
def decodeResume : Bytes → Bytes
  | mask :: l0 :: l1 :: l2 :: l3 :: rest =>
    let n   := be32 l0 l1 l2 l3
    let req := rest.take n
    match rest.drop n with
    | cnt :: body => encodeStep (resumeStep mask.toNat req (decodeResults cnt.toNat body).1)
    | [] => encodeStep (resumeStep mask.toNat req [])
  | _ => []

/-! ### The config-driven resume (the LB chain threaded through the replay)

`drorb_serve_resume` replays the DEFAULT `serveStep`. When the shell drove the
STEP with a config LB chain (`serveStepWith`), the resume must replay the SAME
config serve so the reconstructed continuation matches — otherwise the proxy
backend the step chose and the backend the resume replays could diverge.
`resumeStepWith` / `decodeResumeWith` replay `serveStepWith policies`, and default
to `resumeStep` / `decodeResume` at the deployed default chain (no regression). -/

/-- Replay the config-driven serve `serveStepWith policies` and feed the recorded
`results` — the config sibling of `resumeStep`. -/
def resumeStepWith (policies : List Proxy.Policy) (mask : Nat) (input : Bytes)
    (results : List Bytes) : Step :=
  stepFeed (serveStepWith policies mask input) results

/-- At the deployed default chain the config replay IS the default replay. -/
theorem resumeStepWith_default (mask : Nat) (input : Bytes) (results : List Bytes) :
    resumeStepWith Reactor.ProxyDial.dialPolicies mask input results
      = resumeStep mask input results := rfl

/-- **Decode + run the config-driven `drorb_serve_resume_cfg` frame.** Identical
framing to `decodeResume`, replaying `serveStepWith policies` instead of the
default `serveStep`. -/
def decodeResumeWith (policies : List Proxy.Policy) : Bytes → Bytes
  | mask :: l0 :: l1 :: l2 :: l3 :: rest =>
    let n   := be32 l0 l1 l2 l3
    let req := rest.take n
    match rest.drop n with
    | cnt :: body =>
        encodeStep (resumeStepWith policies mask.toNat req (decodeResults cnt.toNat body).1)
    | [] => encodeStep (resumeStepWith policies mask.toNat req [])
  | _ => []

/-- At the deployed default chain the config-driven decode IS the default decode. -/
theorem decodeResumeWith_default :
    decodeResumeWith Reactor.ProxyDial.dialPolicies = decodeResume := rfl

/-! ## Seam theorems — zero sorries

### Behavior preservation (non-cacheable, non-proxy) -/

/-- On a non-cacheable, non-proxy request, `serveStep` `.done`-s the consolidated
deployed serve bytes: the `seamInner` fold (the full deployed stage registry)
crossed by the `revalidate` finisher (`Date` + the conditional rewrites) — the
same closing stages the bare `conformantServe` default applies. -/
theorem serveStep_noncacheable (mask : Nat) (input : Bytes)
    (hapi : isApiPath input = false) (hc : cacheableKey input = none) :
    serveStep mask input = .done (revalidate (reqOf input) (seamInner input)) := by
  unfold serveStep; rw [hapi, hc]

/-! ### The cache path (gate → lookup → store, proven key + lifetime) -/

/-- **A gate-admitted cacheable request yields `.cacheLookup` with the proven
key.** The lookup fires with the PROVEN key `key`, and the continuation is
`cacheResume`. -/
theorem serveStep_cacheable (mask : Nat) (input key : Bytes)
    (hapi : isApiPath input = false) (hc : cacheableKey input = some key)
    (hg : gateAdmits input = true) :
    serveStep mask input = .yield (.cacheLookup key) (cacheResume key input) := by
  unfold serveStep; rw [hapi, hc]; simp [hg]

/-- **On a HIT the stored bytes are served WITHOUT the handler**, revalidated
against the request's preconditions. For any non-empty lookup result,
`cacheResume` `.done`s `revalidate (reqOf input) hit` — the deployed fold
(`seamInner`) is never evaluated. -/
theorem cacheResume_hit (key input : Bytes) (hit : Bytes) (h : hit ≠ []) :
    cacheResume key input hit = .done (revalidate (reqOf input) hit) := by
  unfold cacheResume
  cases hit with
  | nil => exact absurd rfl h
  | cons a as => rfl

/-- **The plain HIT is the `Date`-spliced stored bytes** — a precondition-free
request's HIT serves the stored representation through the default's non-conditional
accept (`injectDate`), the handler still not run. -/
theorem cacheResume_hit_plain (key input : Bytes) (hit : Bytes) (h : hit ≠ [])
    (hp : hasConditional (reqOf input) = false) :
    cacheResume key input hit = .done (injectDate hit) := by
  rw [cacheResume_hit key input hit h, revalidate_plain _ _ hp]

/-- **The conditional HIT is the proven `304`, cache-fast.** For a stored
representation `serialize R` (well-formed, CL-free) whose `200` carries the
`ETag` the request's `If-None-Match` matches (and whose `If-Match`, if any, is
satisfied) — an entity-tag-only precondition (`hnd`: no date conditional, so the
date finisher is inert) — the HIT arm `.done`s `serialize (addDate (notModifiedOf R))`
— status `304` (`addDate_status`/`notModifiedOf_status`), body stripped — WITHOUT
running the handler. H1+H2+H3 of the extended probe, on the cache path, in the core. -/
theorem cacheResume_hit_notModified (key input : Bytes) (R : Response) (etag : Bytes)
    (hne : serialize R ≠ [])
    (hwf : Proto.ResponseParse.WF R)
    (hcl : ∀ kv ∈ R.headers, isContentLength kv.1 = false)
    (hcond : hasConditional (reqOf input) = true)
    (hnd : hasDateCond (reqOf input) = false)
    (h200 : (R.status == 200) = true) (he : respETag R = some etag)
    (him : ifMatchFails (reqOf input) etag = false)
    (hinm : ifNoneMatchMatches (reqOf input) etag = true) :
    cacheResume key input (serialize R) = .done (serialize (addDate (notModifiedOf R))) := by
  rw [cacheResume_hit key input _ hne, revalidate_stored (reqOf input) R hwf hcl hcond,
    Reactor.Stage.ConditionalRequest.conditionalRewrite_ifNoneMatch (reqOf input) R etag
      h200 he him hinm, dateFinish_noDate (reqOf input) _ hnd]

/-- **The failing `If-Match` HIT is the proven `412`.** RFC 7232 §3.1 (H5), on
the cache path, in the core. -/
theorem cacheResume_hit_preconditionFailed (key input : Bytes) (R : Response) (etag : Bytes)
    (hne : serialize R ≠ [])
    (hwf : Proto.ResponseParse.WF R)
    (hcl : ∀ kv ∈ R.headers, isContentLength kv.1 = false)
    (hcond : hasConditional (reqOf input) = true)
    (hnd : hasDateCond (reqOf input) = false)
    (h200 : (R.status == 200) = true) (he : respETag R = some etag)
    (him : ifMatchFails (reqOf input) etag = true) :
    cacheResume key input (serialize R) = .done (serialize (addDate (preconditionFailedOf R))) := by
  rw [cacheResume_hit key input _ hne, revalidate_stored (reqOf input) R hwf hcl hcond,
    Reactor.Stage.ConditionalRequest.conditionalRewrite_ifMatchFails (reqOf input) R etag
      h200 he him, dateFinish_noDate (reqOf input) _ hnd]

/-- **On a MISS the fold runs (preconditions stripped), then `.cacheStore` fires
with the proven key + lifetime, then `.done` the revalidated fold bytes.** The
store carries the PROVEN key `key`, the PROVEN `cacheLifetime`, and the PLAIN
representation (`cacheFoldInput` strips `If-*` before the fold) — the shell only
stores what the core told it, and never a `304`. -/
theorem cacheResume_miss (key input : Bytes) :
    cacheResume key input [] =
      .yield (.cacheStore key (seamInner (cacheFoldInput input))
          cacheLifetime)
        (fun _ => .done (revalidate (reqOf input)
          (seamInner (cacheFoldInput input)))) := rfl

/-- **The plain MISS runs the fold on `input`, stores it, and `.done`s it
`Date`-spliced** — a precondition-free request's MISS serves the stored plain `200`
through the default's non-conditional accept (`injectDate`). -/
theorem cacheResume_miss_plain (key input : Bytes)
    (hp : hasConditional (reqOf input) = false) :
    cacheResume key input [] =
      .yield (.cacheStore key (seamInner input) cacheLifetime)
        (fun _ => .done (injectDate (seamInner input))) := by
  rw [cacheResume_miss, cacheFoldInput_plain input hp]
  congr 1
  funext r
  rw [revalidate_plain _ _ hp]

/-- **The stored lifetime is the proven `Cache.selectLifetime`.** The `.cacheStore`
the miss path yields carries `Cache.selectLifetime cacheDirectives`, not a
host-invented TTL. -/
theorem cacheResume_miss_lifetime :
    _root_.Cache.selectLifetime cacheDirectives = some cacheLifetime :=
  cacheLifetime_is_selectLifetime

/-- **A gate-REFUSED cacheable request `.done`s the deployed fold and yields NO
cache effect.** So even a cacheable-shaped request the credential gate refuses
(e.g. `/admin` without a valid token) is served the gate response — the store is
never consulted. This is the gate-before-cache guarantee at the seam. -/
theorem serveStep_gate_rejects (mask : Nat) (input key : Bytes)
    (hapi : isApiPath input = false) (hc : cacheableKey input = some key)
    (hg : gateAdmits input = false) :
    serveStep mask input = .done (revalidate (reqOf input) (seamInner input)) := by
  unfold serveStep; rw [hapi, hc]; simp [hg]

/-- The full cache-miss drive, at the byte level: replaying with the recorded
`[miss, store-ack]` results ends `.done`-ing the revalidated deployed fold bytes
(the STORED bytes are the plain fold on the precondition-stripped input). -/
theorem resumeStep_cache_miss (mask : Nat) (input key : Bytes) (ack : Bytes)
    (hapi : isApiPath input = false) (hc : cacheableKey input = some key)
    (hg : gateAdmits input = true) :
    resumeStep mask input [[], ack]
      = .done (revalidate (reqOf input)
          (seamInner (cacheFoldInput input))) := by
  unfold resumeStep
  rw [serveStep_cacheable mask input key hapi hc hg, stepFeed_yield, cacheResume_miss,
    stepFeed_yield, stepFeed_nil]

/-- The plain (precondition-free) cache-miss drive `.done`s the consolidated fold
bytes on `input`, `Date`-spliced (`injectDate`) — the default's non-conditional accept. -/
theorem resumeStep_cache_miss_plain (mask : Nat) (input key : Bytes) (ack : Bytes)
    (hapi : isApiPath input = false) (hc : cacheableKey input = some key)
    (hg : gateAdmits input = true) (hp : hasConditional (reqOf input) = false) :
    resumeStep mask input [[], ack] = .done (injectDate (seamInner input)) := by
  rw [resumeStep_cache_miss mask input key ack hapi hc hg,
    cacheFoldInput_plain input hp, revalidate_plain _ _ hp]

/-- The full cache-hit drive, at the byte level: replaying with the recorded
`[hit]` result ends `.done`-ing the revalidated stored bytes, WITHOUT the handler. -/
theorem resumeStep_cache_hit (mask : Nat) (input key hit : Bytes)
    (hapi : isApiPath input = false) (hc : cacheableKey input = some key)
    (hg : gateAdmits input = true) (hne : hit ≠ []) :
    resumeStep mask input [hit] = .done (revalidate (reqOf input) hit) := by
  unfold resumeStep
  rw [serveStep_cacheable mask input key hapi hc hg, stepFeed_yield, stepFeed_nil,
    cacheResume_hit key input hit hne]

/-- The plain (precondition-free) cache-hit drive `.done`s the stored bytes
`Date`-spliced (`injectDate`) — the default's non-conditional accept. -/
theorem resumeStep_cache_hit_plain (mask : Nat) (input key hit : Bytes)
    (hapi : isApiPath input = false) (hc : cacheableKey input = some key)
    (hg : gateAdmits input = true) (hne : hit ≠ [])
    (hp : hasConditional (reqOf input) = false) :
    resumeStep mask input [hit] = .done (injectDate hit) := by
  rw [resumeStep_cache_hit mask input key hit hapi hc hg hne, revalidate_plain _ _ hp]

/-! ### The proxy path -/

/-- **The proxy path yields the proven-chosen backend**, with the full
response-transform as its continuation. -/
theorem serveStep_proxy_yields (mask : Nat) (input : Bytes) (id : BackendId)
    (h : isApiPath input = true)
    (hpick : Reactor.ProxyDial.pick mask (stickyKey input) = some id) :
    serveStep mask input
      = .yield (.proxyDial id input) (fun up => .done (proxyRespTransform input up)) := by
  unfold serveStep; rw [h, hpick]

/-- **The yielded backend is genuinely up.** -/
theorem serveStep_backend_up (mask : Nat) (input : Bytes) (id : BackendId)
    (hpick : Reactor.ProxyDial.pick mask (stickyKey input) = some id) :
    mask.testBit id = true := by
  cases hbit : mask.testBit id with
  | false => exact absurd hpick (Reactor.ProxyDial.pick_health_ejects hbit)
  | true  => rfl

/-- **The proxy continuation runs the FULL response-transform fold over the
upstream reply.** After the shell dials the backend and returns `upstream`,
resuming produces `proxyRespTransform input upstream` — the reply parsed, run
through cors / gzip / security-headers / header, and re-serialized. -/
theorem serveStep_proxy_resume (mask : Nat) (input upstream : Bytes) (id : BackendId)
    (h : isApiPath input = true)
    (hpick : Reactor.ProxyDial.pick mask (stickyKey input) = some id) :
    resumeStep mask input [upstream] = .done (proxyRespTransform input upstream) := by
  unfold resumeStep
  rw [serveStep_proxy_yields mask input id h hpick]
  simp only [stepFeed_yield, stepFeed_nil]

/-! #### The proxied response carries the response-transform headers -/

/-- Membership of a header in the built result is preserved by `addHeader`. -/
theorem mem_build_addHeader {x nv : Bytes × Bytes} {b : ResponseBuilder}
    (h : x ∈ b.build.headers) : x ∈ (b.addHeader nv).build.headers := by
  rw [Reactor.Pipeline.build_addHeader]
  exact List.mem_append.mpr (Or.inl h)

/-- Membership of a header is preserved by the gzip body rewrite (headers
unchanged; only the body is replaced). -/
theorem mem_build_gzipBody {x : Bytes × Bytes} {b : ResponseBuilder}
    (h : x ∈ b.build.headers) : x ∈ (b.mapResp Reactor.Stage.Gzip.gzipBody).build.headers := by
  rw [Reactor.Pipeline.build_mapResp]
  simpa [Reactor.Stage.Gzip.gzipBody] using h

/-- **The proxied response carries HSTS.** For ANY upstream reply and request,
the built response-transform fold over the reply contains the real
`Strict-Transport-Security` header — a proxied response gets HSTS like a normal
one. (The `Server` header rides the same fold via `headerStage`.) -/
theorem proxyRespStages_hsts (upstream : Bytes) (c : Reactor.Pipeline.Ctx) :
    (Reactor.Stage.SecurityHeaders.hstsHeaderName,
     Reactor.Stage.SecurityHeaders.hstsHeaderVal)
      ∈ ((runPipeline proxyRespStages (fun _ => parseUpstream upstream) c).build).headers := by
  -- security :: header carries HSTS for any tail.
  have hinner :
      (Reactor.Stage.SecurityHeaders.hstsHeaderName,
       Reactor.Stage.SecurityHeaders.hstsHeaderVal)
        ∈ ((runPipeline [Reactor.Stage.SecurityHeaders.securityheadersStage,
              Reactor.Stage.Header.headerStage]
              (fun _ => parseUpstream upstream) c).build).headers :=
    Reactor.Stage.SecurityHeaders.securityheadersStage_hsts_present
      [Reactor.Stage.Header.headerStage] (fun _ => parseUpstream upstream) c
  -- peel gzip (position 2): its onResponse only appends / rewrites the body.
  have hgzip :
      (Reactor.Stage.SecurityHeaders.hstsHeaderName,
       Reactor.Stage.SecurityHeaders.hstsHeaderVal)
        ∈ ((runPipeline (Reactor.Stage.Gzip.gzipStage ::
              [Reactor.Stage.SecurityHeaders.securityheadersStage,
               Reactor.Stage.Header.headerStage])
              (fun _ => parseUpstream upstream) c).build).headers := by
    rw [pipeline_stage_effect Reactor.Stage.Gzip.gzipStage _ (fun _ => parseUpstream upstream) c c rfl]
    show _ ∈ ((match Reactor.Stage.Gzip.acceptsGzip c.req with
      | true => ((runPipeline [Reactor.Stage.SecurityHeaders.securityheadersStage,
                    Reactor.Stage.Header.headerStage]
                    (fun _ => parseUpstream upstream) c).mapResp
                    Reactor.Stage.Gzip.gzipBody).addHeader
                    (Reactor.Stage.Gzip.ceName, Reactor.Stage.Gzip.gzipVal)
      | false => runPipeline [Reactor.Stage.SecurityHeaders.securityheadersStage,
                    Reactor.Stage.Header.headerStage] (fun _ => parseUpstream upstream) c).build).headers
    cases Reactor.Stage.Gzip.acceptsGzip c.req with
    | false => exact hinner
    | true => exact mem_build_addHeader (mem_build_gzipBody hinner)
  -- peel cors (position 1): its onResponse only appends ACAO (or nothing).
  rw [show proxyRespStages
        = Reactor.Deploy.deployCorsStage ::
            (Reactor.Stage.Gzip.gzipStage ::
              [Reactor.Stage.SecurityHeaders.securityheadersStage,
               Reactor.Stage.Header.headerStage]) from rfl,
      pipeline_stage_effect Reactor.Deploy.deployCorsStage _ (fun _ => parseUpstream upstream) c c rfl]
  show _ ∈ ((match _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy
      (Reactor.Deploy.corsOriginOf c) with
    | some v => (runPipeline (Reactor.Stage.Gzip.gzipStage ::
                    [Reactor.Stage.SecurityHeaders.securityheadersStage,
                     Reactor.Stage.Header.headerStage]) (fun _ => parseUpstream upstream) c).addHeader
                    (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v)
    | none => runPipeline (Reactor.Stage.Gzip.gzipStage ::
                    [Reactor.Stage.SecurityHeaders.securityheadersStage,
                     Reactor.Stage.Header.headerStage]) (fun _ => parseUpstream upstream) c).build).headers
  cases _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (Reactor.Deploy.corsOriginOf c) with
  | none => exact hgzip
  | some v => exact mem_build_addHeader hgzip

/-- **The proxied response carries HSTS, end-to-end.** The bytes the proxy resume
produces (`proxyRespTransform`) serialize a response whose header block contains
the real HSTS header. -/
theorem proxyRespTransform_hsts (input upstream : Bytes) :
    (Reactor.Stage.SecurityHeaders.hstsHeaderName,
     Reactor.Stage.SecurityHeaders.hstsHeaderVal)
      ∈ ((runPipeline proxyRespStages (fun _ => parseUpstream upstream)
            (Reactor.Deploy.ctxOf input)).build).headers :=
  proxyRespStages_hsts upstream (Reactor.Deploy.ctxOf input)

/-- **No eligible backend ⇒ the core's 503.** -/
theorem serveStep_proxy_no_backend (mask : Nat) (input : Bytes)
    (h : isApiPath input = true)
    (hpick : Reactor.ProxyDial.pick mask (stickyKey input) = none) :
    serveStep mask input = .done (serialize serviceUnavailable503) := by
  unfold serveStep; rw [h, hpick]

/-! ## Runnable checks — the encode framing round-trips the decision -/

-- A `.done` step encodes tag-0-prefixed.
example (b : Bytes) : encodeStep (.done b) = tagDone :: Reactor.ServeConformant.scrubCorr b := rfl
-- A proxy yield encodes tag-1, backend id, then the forwarded request bytes.
example : encodeStep (.yield (.proxyDial 2 [71, 69, 84]) (fun _ => .done []))
    = [tagYieldProxy, 2, 71, 69, 84] := rfl
-- A cacheLookup yield encodes tag-2, then the key bytes.
example : encodeStep (.yield (.cacheLookup [71, 69, 84]) (fun _ => .done []))
    = [tagYieldCacheLookup, 71, 69, 84] := rfl
-- A cacheStore yield encodes tag-3, lifetime(4), keyLen(4), key, resp.
example : encodeStep (.yield (.cacheStore [75] [82] 60) (fun _ => .done []))
    = [tagYieldCacheStore, 0, 0, 0, 60, 0, 0, 0, 1, 75, 82] := rfl
-- The big-endian request-length prefix decodes as expected.
example : be32 0 0 0 4 = 4 := rfl
example : be32 0 0 1 0 = 256 := rfl
-- The proven cache lifetime is 60s.
example : cacheLifetime = 60 := rfl

/-! ### Executable witnesses — the cache-path finisher genuinely fires

On the extended probe's exact bytes (`ConditionalRequest`'s witnesses): the
matching `If-None-Match` HIT re-serializes as the `304` (body stripped, CL
re-derived to 0), the failing `If-Match` HIT as the `412`, the satisfied `If-Match`
and the plain request serve the stored `200`. Every accepted answer is now `Date`-
spliced by the finisher (`revalidate`), the same close the `conformantServe` default
applies — so a served head carries `Date` on BOTH serve paths. -/

open Reactor.Stage.ConditionalRequest (reqINM reqINMStar reqIMno reqIMyes reqPlain base200)

-- The matching `If-None-Match` HIT re-serializes as the `304` (body stripped)…
#guard (Proto.ResponseParse.parse (revalidate reqINM (serialize base200))).map
    (fun r => (r.status, r.body)) == some (304, [])
#guard (Proto.ResponseParse.parse (revalidate reqINMStar (serialize base200))).map
    (fun r => (r.status, r.body)) == some (304, [])
-- …the failing `If-Match` HIT as the `412`…
#guard (Proto.ResponseParse.parse (revalidate reqIMno (serialize base200))).map
    (fun r => r.status) == some 412
-- …and a satisfied `If-Match` / a plain request serve the stored `200`.
#guard (Proto.ResponseParse.parse (revalidate reqIMyes (serialize base200))).map
    (fun r => r.status) == some 200
#guard (Proto.ResponseParse.parse (revalidate reqPlain (serialize base200))).map
    (fun r => r.status) == some 200

/-- The probe's H1 request over the REAL seam fold, end-to-end through the cache
arms: a conditional `If-None-Match: *` GET to the deployed static asset. -/
def condStarInput : Bytes :=
  str "GET /static/app.js HTTP/1.1\r\nHost: x\r\nIf-None-Match: *\r\n\r\n"

-- The dispatched request genuinely carries the precondition (ground truth for
-- the `reqOf` parse: headers survive the deployed dispatch).
#guard hasConditional (reqOf condStarInput) == true
-- MISS + revalidate on the REAL seam fold: the cold-cache conditional answer is the 304…
#guard (Proto.ResponseParse.parse (revalidate (reqOf condStarInput)
    (seamInner (cacheFoldInput condStarInput)))).map
      (fun r => (r.status, r.body)) == some (304, [])
-- …while the STORED representation is the plain 200 (never a 304 in the store).
#guard (Proto.ResponseParse.parse
    (seamInner (cacheFoldInput condStarInput))).map
      (fun r => r.status) == some 200
def plainInput : Bytes := str "GET /static/app.js HTTP/1.1\r\nHost: x\r\n\r\n"
#guard hasConditional (reqOf plainInput) == false
#guard cacheFoldInput plainInput == plainInput
-- **The path-divergence fix, executable.** The consolidated seam fold now stamps
-- `Content-Location` (RFC 9110 §8.7) on the static 200 — the header the old
-- fourteen-stage seam fold lacked — and the finisher splices `Date`.
def queryInput : Bytes := str "GET /static/app.js?v=1 HTTP/1.1\r\nHost: x\r\n\r\n"
#guard ((Proto.ResponseParse.parse (revalidate (reqOf queryInput) (seamInner queryInput))).map
    (fun r => (r.status,
      r.headers.any (fun kv => kv.1 == Reactor.Stage.ContentLocation.contentLocationName))))
    == some (200, true)
-- A Range request is DECLINED by the proven cache decision (it takes the fold,
-- which answers the 206/416) — while the plain and conditional GETs are admitted.
def rangeInput : Bytes := str "GET /static/app.js HTTP/1.1\r\nHost: x\r\nRange: bytes=0-3\r\n\r\n"
#guard cacheableKey rangeInput == none
#guard (cacheableKey plainInput).isSome
#guard (cacheableKey condStarInput).isSome

#print axioms serveStep_noncacheable
#print axioms serveStep_cacheable
#print axioms cacheResume_hit
#print axioms cacheResume_hit_plain
#print axioms cacheResume_hit_notModified
#print axioms cacheResume_hit_preconditionFailed
#print axioms cacheResume_miss
#print axioms cacheResume_miss_plain
#print axioms revalidate_stored
#print axioms conditionalRewrite_noCond
#print axioms serveStep_gate_rejects
#print axioms resumeStep_cache_hit
#print axioms resumeStep_cache_hit_plain
#print axioms resumeStep_cache_miss
#print axioms resumeStep_cache_miss_plain
#print axioms serveStep_proxy_resume
#print axioms proxyRespTransform_hsts

/-! ### The config LB policy reaches the deployed proxy branch -/

/-- **A config-driven proxy request yields the config-chain's chosen backend.**
For any config policy chain, the proxy branch of `serveStepWith` dials the backend
`Reactor.ProxyDial.pickWith policies` selected — so the deployment's declared
`LbPolicy` decides which backend a proxied request reaches. -/
theorem serveStepWith_proxy_yields (policies : List Proxy.Policy) (mask : Nat)
    (input : Bytes) (id : BackendId) (h : isApiPath input = true)
    (hpick : Reactor.ProxyDial.pickWith policies mask (stickyKey input) = some id) :
    serveStepWith policies mask input
      = .yield (.proxyDial id input) (fun up => .done (proxyRespTransform input up)) := by
  unfold serveStepWith; rw [h, hpick]

/-- **The yielded backend is genuinely up, for ANY config policy.** -/
theorem serveStepWith_backend_up (policies : List Proxy.Policy) (mask : Nat)
    (input : Bytes) (id : BackendId)
    (hpick : Reactor.ProxyDial.pickWith policies mask (stickyKey input) = some id) :
    mask.testBit id = true := by
  cases hbit : mask.testBit id with
  | false => exact absurd hpick (Reactor.ProxyDial.pickWith_health_ejects hbit)
  | true  => rfl

/-- **The config-driven proxy resume runs the response fold over the reply.** After
the shell dials the config-chosen backend and returns `upstream`, replaying the
config serve produces `proxyRespTransform input upstream` — the reply parsed, run
through cors / gzip / security-headers / header, and re-serialized. So driving the
STEP with a config chain and RESUMING with the same chain composes into the proven
proxied response, for ANY config policy. -/
theorem resumeStepWith_proxy (policies : List Proxy.Policy) (mask : Nat)
    (input upstream : Bytes) (id : BackendId) (h : isApiPath input = true)
    (hpick : Reactor.ProxyDial.pickWith policies mask (stickyKey input) = some id) :
    resumeStepWith policies mask input [upstream] = .done (proxyRespTransform input upstream) := by
  unfold resumeStepWith
  rw [serveStepWith_proxy_yields policies mask input id h hpick]
  simp only [stepFeed_yield, stepFeed_nil]

#print axioms serveStepWith_default
#print axioms serveStepWith_deploy
#print axioms serveStepWith_proxy_yields
#print axioms resumeStepWith_proxy

/-! ## The HEAD/BODY-SPLIT proxy resume (the native STREAMING prerequisite)

The proxy resume above (`serveStep_proxy_resume`) feeds the WHOLE upstream reply into
one continuation (`fun up => .done (proxyRespTransform input up)`): the shell must hand
the core the entire reply, so a native path buffers the whole body. The streaming spec
(`Reactor.ServeStream.proxy_emit_refines`) forbids that — it delivers the response as a
HEAD chunk followed by paced body chunks, the body never buffered whole.

This section adds — ADDITIVELY, alongside the whole-reply resume, which is untouched —
a head/body-split resume. The transformed proxy reply `proxyRespTransform input upstream`
is `serialize` of a built `Response` (`proxyBuiltResp`); by the serializer's own framing
(`Reactor.serialize_framing`) it splits EXACTLY as a core-decided HEAD (`proxyRespHead` —
status line, header block including the derived `Content-Length`, blank-line separator)
followed by the transformed BODY (`(proxyBuiltResp …).body`). `proxyStreamResume` takes
that head and the body streamed as a SEQUENCE of chunks and assembles `head ++ chunks`;
`proxyStreamResume_faithful` / `proxy_stream_resume_faithful` prove it produces EXACTLY
the whole-reply resume's bytes on the concatenated reply — the split is faithful, not a
new behavior.

**Residual (honest).** `proxyRespHead` carries the derived `Content-Length`, which is a
function of the transformed body length (and the gzip stage genuinely re-encodes the
body). So the head is byte-computable only once the transformed body length is known —
this split proves head-FIRST delivery is faithful to the buffered bytes, but not yet
head-BEFORE-body emission (respond before the body arrives). Narrowing the head to be
independent of the body (upstream `Content-Length` trust + a body-length-preserving
transform, or chunked transfer-encoding) is the minimal additional lemma that would
unlock true zero-buffer early-head streaming — the same deferred obligation
`Reactor.ServeStream` names as scan-gated early head-emission. -/

/-- **The parsed → transformed proxy `Response`** for an upstream reply — the value
`proxyRespTransform` re-serializes. Naming it lets the head/body split cut it via the
serializer's own framing. -/
def proxyBuiltResp (input upstream : Bytes) : Response :=
  (runPipeline proxyRespStages (fun _ => parseUpstream upstream)
    (Reactor.Deploy.ctxOf input)).build

/-- `proxyRespTransform` is exactly `serialize` of the built proxy response. -/
theorem proxyRespTransform_built (input upstream : Bytes) :
    proxyRespTransform input upstream = serialize (proxyBuiltResp input upstream) := rfl

/-- **The core-decided response HEAD of a transformed proxy reply** — status line,
header block (including the derived `Content-Length`), and the blank-line separator:
everything the serializer emits before the body. This is the head the native streaming
proxy delivers as one chunk. -/
def proxyRespHead (input upstream : Bytes) : Bytes :=
  Reactor.statusLineOf (proxyBuiltResp input upstream) ++ Reactor.crlf
    ++ Reactor.headerBlockOf (proxyBuiltResp input upstream) ++ Reactor.crlf ++ Reactor.crlf

/-- **The transformed proxy reply splits as head ++ body.** `proxyRespTransform` is
exactly its core-decided head (`proxyRespHead`) followed by the transformed body — the
split point the streaming emit cuts at. Definitional (`Reactor.serialize_framing`). -/
theorem proxyRespTransform_split (input upstream : Bytes) :
    proxyRespTransform input upstream
      = proxyRespHead input upstream ++ (proxyBuiltResp input upstream).body := by
  rw [proxyRespTransform_built]
  exact Reactor.serialize_framing (proxyBuiltResp input upstream)

/-- **The head/body-split proxy resume.** The native streaming proxy delivers the
core-decided response HEAD first, then the transformed body as a SEQUENCE of `chunks`
streamed host-side (never buffered whole in the core). This resume assembles
`head ++ (the chunks concatenated)` — the streamed proxy response. Total. -/
def proxyStreamResume (head : Bytes) (chunks : List Bytes) : Step :=
  .done (head ++ chunks.flatten)

/-- **The split/streamed proxy resume is FAITHFUL to the buffered transform.** When the
head is the core-decided transformed response head and the streamed body chunks
concatenate to the transformed body, the head/body-split resume produces EXACTLY
`proxyRespTransform input upstream` — the whole-reply resume's bytes — byte-for-byte. It
is proven EQUAL to the buffered path on the concatenated reply (via
`proxyRespTransform_split`), not a new behavior. Non-vacuous: the head carries the real
transformed status/headers (HSTS rides `proxyRespStages`), and the chunks are the actual
transformed body. -/
theorem proxyStreamResume_faithful (input upstream : Bytes) (chunks : List Bytes)
    (hchunks : chunks.flatten = (proxyBuiltResp input upstream).body) :
    proxyStreamResume (proxyRespHead input upstream) chunks
      = .done (proxyRespTransform input upstream) := by
  unfold proxyStreamResume
  rw [hchunks, ← proxyRespTransform_split]

/-- **The streamed resume equals the proven whole-reply proxy resume.** For a proxy
request whose proven pick finds an eligible backend, feeding the core-decided response
head + the transformed body streamed as chunks produces the SAME `Step` as the existing
whole-reply proxy resume (`serveStep_proxy_resume` ⇒ `resumeStep mask input [upstream]`)
on the concatenated reply. So the head/body split is faithful to the buffered proxy
program, not a new behavior — the prerequisite a native streaming io_uring proxy needs.
Non-vacuous: `hpick` forces `id` genuinely up (`serveStep_backend_up`), and `chunks` are
the real transformed body split. -/
theorem proxy_stream_resume_faithful (mask : Nat) (input upstream : Bytes) (id : BackendId)
    (chunks : List Bytes) (h : isApiPath input = true)
    (hpick : Reactor.ProxyDial.pick mask (stickyKey input) = some id)
    (hchunks : chunks.flatten = (proxyBuiltResp input upstream).body) :
    proxyStreamResume (proxyRespHead input upstream) chunks = resumeStep mask input [upstream] := by
  rw [serveStep_proxy_resume mask input upstream id h hpick]
  exact proxyStreamResume_faithful input upstream chunks hchunks

-- The split resume with the head and a one-chunk body reassembles the buffered transform.
example (input upstream : Bytes) :
    proxyStreamResume (proxyRespHead input upstream) [(proxyBuiltResp input upstream).body]
      = .done (proxyRespTransform input upstream) :=
  proxyStreamResume_faithful input upstream [(proxyBuiltResp input upstream).body] (by simp)

#print axioms proxyRespTransform_split
#print axioms proxyStreamResume_faithful
#print axioms proxy_stream_resume_faithful

end Reactor.ServeStep
