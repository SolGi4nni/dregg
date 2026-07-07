import Reactor.Deploy
import Reactor.ProxyDial
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
  running the handler; on a MISS it runs the fold, yields `.cacheStore` with the
  PROVEN key + lifetime, then `.done`s. Because the gate check runs BEFORE the
  lookup, a cache HIT is gate-admitted: a request the gate refuses (e.g. a
  `/admin` path with no valid credential) never reaches the store — it is the
  gate response, not a cached hit. This is the sans-IO cache done correctly, the
  reason the effect seam was chosen over a shallow dataplane cache that would
  bypass auth / rate on a hit.

## Faithfulness to the deployed serve

* On a **non-cacheable, non-proxy** request, `serveStep` `.done`-s EXACTLY the
  deployed serve bytes (`Reactor.Deploy.servePipelineFull2 input`, the response
  component of `deployStepFull2`) — `serveStep_noncacheable`,
  `serveStep_preserves_deployed`.
* On a **gate-refused cacheable** request, `serveStep` `.done`-s the deployed
  fold (the gate response) and yields NO cache effect (`serveStep_gate_rejects`).
* On a **gate-admitted cacheable** request, `serveStep` yields `.cacheLookup key`
  with the proven key, then (on a miss) `.cacheStore key resp lifetime` with the
  proven lifetime (`serveStep_cacheable`, `cacheResume_miss`); on a hit the
  continuation `.done`s the stored bytes (`cacheResume_hit`).
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

/-- **The proven cacheability decision (request phase).** `some key` iff the
request is a cacheable GET; `none` otherwise. Request-only, so a HIT can skip the
handler entirely. -/
def cacheableKey (input : Bytes) : Option Bytes :=
  let req := reqOf input
  if isGet req && isCacheableTarget req.target then some (cacheKeyOf req) else none

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

/-! ## The resumable serve -/

/-- Continuation of the cache lookup: on a HIT (non-empty stored bytes) `.done`
those bytes WITHOUT running the handler; on a MISS ([]) run the deployed fold,
yield `.cacheStore` with the PROVEN key + lifetime, then `.done` the fold bytes. -/
def cacheResume (key input : Bytes) : Bytes → Step := fun hit =>
  match hit with
  | [] =>
    let resp := Reactor.Deploy.servePipelineFull2 input
    .yield (.cacheStore key resp cacheLifetime) (fun _ => .done resp)
  | _ => .done hit

/-- **The resumable deployed serve.**

* a **proxy** request whose proven pick finds an eligible backend `.yield`s a
  `proxyDial`, with a continuation that runs the full response-transform fold
  over the reply; no eligible backend ⇒ the core's 503;
* a **gate-admitted cacheable** request `.yield`s `.cacheLookup key` (the proven
  key), with `cacheResume` as its continuation;
* a **gate-refused cacheable** request, and every **non-cacheable, non-proxy**
  request, `.done`s the full deployed serve bytes (`servePipelineFull2`).

Total. `mask` is the shell's one live input (the health/breaker bitmask). -/
def serveStep (mask : Nat) (input : Bytes) : Step :=
  match isApiPath input with
  | true =>
    match Reactor.ProxyDial.pick mask (stickyKey input) with
    | some id => .yield (.proxyDial id input) (fun up => .done (proxyRespTransform input up))
    | none    => .done (serialize serviceUnavailable503)
  | false =>
    match cacheableKey input with
    | none => .done (Reactor.Deploy.servePipelineFull2 input)
    | some key =>
      if gateAdmits input then
        .yield (.cacheLookup key) (cacheResume key input)
      else
        .done (Reactor.Deploy.servePipelineFull2 input)

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
    | none => .done (Reactor.Deploy.servePipelineFull2 input)
    | some key =>
      if gateAdmits input then
        .yield (.cacheLookup key) (cacheResume key input)
      else
        .done (Reactor.Deploy.servePipelineFull2 input)

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
  | .done b => tagDone :: b
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

/-- On a non-cacheable, non-proxy request, `serveStep` `.done`-s EXACTLY the
current deployed serve bytes. -/
theorem serveStep_noncacheable (mask : Nat) (input : Bytes)
    (hapi : isApiPath input = false) (hc : cacheableKey input = none) :
    serveStep mask input = .done (Reactor.Deploy.servePipelineFull2 input) := by
  unfold serveStep; rw [hapi, hc]

/-- The `serveStep` `.done` bytes are the FIRST component of
`Reactor.Deploy.deployStepFull2` — the bytes `main` writes — on any
non-cacheable, non-proxy request. -/
theorem serveStep_preserves_deployed (mask : Nat) (st : Reactor.Observe.ObsState)
    (input : Bytes) (hapi : isApiPath input = false) (hc : cacheableKey input = none) :
    serveStep mask input = .done (Reactor.Deploy.deployStepFull2 st input).1 := by
  rw [serveStep_noncacheable mask input hapi hc, Reactor.Deploy.deployStepFull2_serves]

/-! ### The cache path (gate → lookup → store, proven key + lifetime) -/

/-- **A gate-admitted cacheable request yields `.cacheLookup` with the proven
key.** The lookup fires with the PROVEN key `key`, and the continuation is
`cacheResume`. -/
theorem serveStep_cacheable (mask : Nat) (input key : Bytes)
    (hapi : isApiPath input = false) (hc : cacheableKey input = some key)
    (hg : gateAdmits input = true) :
    serveStep mask input = .yield (.cacheLookup key) (cacheResume key input) := by
  unfold serveStep; rw [hapi, hc]; simp [hg]

/-- **On a HIT the stored bytes are served WITHOUT the handler.** For any
non-empty lookup result, `cacheResume` `.done`s exactly those bytes — the
deployed fold (`servePipelineFull2`) is never evaluated. -/
theorem cacheResume_hit (key input : Bytes) (hit : Bytes) (h : hit ≠ []) :
    cacheResume key input hit = .done hit := by
  unfold cacheResume
  cases hit with
  | nil => exact absurd rfl h
  | cons a as => rfl

/-- **On a MISS the fold runs, then `.cacheStore` fires with the proven key +
lifetime, then `.done`.** The store carries the PROVEN key `key` and PROVEN
`cacheLifetime` — the shell only stores what the core told it. -/
theorem cacheResume_miss (key input : Bytes) :
    cacheResume key input [] =
      .yield (.cacheStore key (Reactor.Deploy.servePipelineFull2 input) cacheLifetime)
        (fun _ => .done (Reactor.Deploy.servePipelineFull2 input)) := rfl

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
    serveStep mask input = .done (Reactor.Deploy.servePipelineFull2 input) := by
  unfold serveStep; rw [hapi, hc]; simp [hg]

/-- The full cache-miss drive, at the byte level: replaying with the recorded
`[miss, store-ack]` results ends `.done`-ing the deployed fold bytes — the exact
bytes the shell then stores and writes. -/
theorem resumeStep_cache_miss (mask : Nat) (input key : Bytes) (ack : Bytes)
    (hapi : isApiPath input = false) (hc : cacheableKey input = some key)
    (hg : gateAdmits input = true) :
    resumeStep mask input [[], ack] = .done (Reactor.Deploy.servePipelineFull2 input) := by
  unfold resumeStep
  rw [serveStep_cacheable mask input key hapi hc hg, stepFeed_yield, cacheResume_miss,
    stepFeed_yield, stepFeed_nil]

/-- The full cache-hit drive, at the byte level: replaying with the recorded
`[hit]` result ends `.done`-ing the stored bytes, WITHOUT the handler. -/
theorem resumeStep_cache_hit (mask : Nat) (input key hit : Bytes)
    (hapi : isApiPath input = false) (hc : cacheableKey input = some key)
    (hg : gateAdmits input = true) (hne : hit ≠ []) :
    resumeStep mask input [hit] = .done hit := by
  unfold resumeStep
  rw [serveStep_cacheable mask input key hapi hc hg, stepFeed_yield, stepFeed_nil,
    cacheResume_hit key input hit hne]

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
example : encodeStep (.done [65, 66]) = [tagDone, 65, 66] := rfl
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

#print axioms serveStep_noncacheable
#print axioms serveStep_cacheable
#print axioms cacheResume_hit
#print axioms cacheResume_miss
#print axioms serveStep_gate_rejects
#print axioms resumeStep_cache_hit
#print axioms resumeStep_cache_miss
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

end Reactor.ServeStep
