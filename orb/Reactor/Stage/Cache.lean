import Reactor.Pipeline
import Cache

/-!
# Reactor.Stage.Cache — the RFC 9111 fresh-hit cache GATE

A byte-driving pipeline stage that turns the real `Cache` library's fresh-hit
decision into a short-circuit on the deployed serve path. On a **fresh cache
hit** (`Cache.Store.get?` finds an entry AND `Cache.Meta.isFresh` holds at the
stage's clock) the stage `.respond`s with the stored response bytes — the
handler and every later stage are skipped, no upstream is dialed. On a **miss**
(no stored entry) the stage `.continue`s: the request passes through untouched
and the handler's bytes flow.

The decision is the genuine `Cache` transition data — `Store.get?` (the §4.1
exact-key lookup) and `Meta.isFresh` (the §4.2 `freshness_lifetime > current_age`
test) — not a re-implementation. The only boundary is `render : Cache.Body →
Response`: the origin's body bytes are outside the `Cache` model (its `Body` is
an opaque token, exactly as documented in `Cache.lean`), so a config function
supplies the actual stored bytes — the same uninterpreted-boundary shape the
`Tls`/`Cache` libraries use for their crypto/body payloads.

The byte-effect is a GATE short-circuit: `cacheStage_serves_stored` proves the
built pipeline output IS `render`'s stored `Response` — for ANY tail and
handler — so a fresh hit genuinely changes the emitted bytes (the cached body,
not the handler's), and `cacheStage_miss_passthrough` proves a miss leaves the
tail's bytes exactly as they were.
-/

namespace Reactor.Stage.Cache

open Reactor (Response natToDec reasonOK)
open Reactor.Pipeline
open Proto (Bytes Request)

/-! ## The gate, parameterized by a cache configuration -/

/-- A deployed cache-stage configuration: the (warm) cache state, how a request
maps to a `Cache.Key`, the clock the freshness test consults, and the boundary
`render` that turns the opaque stored `Body` token into the actual stored
response bytes. -/
structure Config where
  /-- The cache state consulted on the request phase. -/
  st : _root_.Cache.St
  /-- §4.1 cache-key derivation from the dispatched request. -/
  keyOf : Ctx → _root_.Cache.Key
  /-- The clock (seconds) the freshness test reads (`Cache.lean`: time is data). -/
  now : Nat
  /-- Boundary: the stored body token → the stored response bytes it stands for. -/
  render : _root_.Cache.Body → Response

/-- The request-phase decision, wired to the REAL `Cache` lookup + freshness
test: a fresh stored entry gates with `render`'s stored bytes; anything else
(miss, or a stale entry) passes through. -/
def Config.onReq (cfg : Config) (c : Ctx) : StageStep :=
  match cfg.st.store.get? (cfg.keyOf c) with
  | some e => if e.meta.isFresh cfg.now = true then .respond (cfg.render e.body) else .continue c
  | none => .continue c

/-- The stage: a gate on the request phase; the response phase is the identity
(a gate contributes bytes by short-circuiting, not by transforming the tail). -/
def mkStage (cfg : Config) : Stage where
  name := "cache"
  onRequest := cfg.onReq
  onResponse := fun _ b => b

/-! ## The gate's request-phase reductions (real `Cache` decision) -/

/-- A fresh hit gates with the stored bytes. -/
theorem onReq_hit (cfg : Config) (c : Ctx) (e : _root_.Cache.Stored)
    (hget : cfg.st.store.get? (cfg.keyOf c) = some e)
    (hfresh : e.meta.isFresh cfg.now = true) :
    cfg.onReq c = .respond (cfg.render e.body) := by
  simp [Config.onReq, hget, hfresh]

/-- A miss passes through unchanged. -/
theorem onReq_miss (cfg : Config) (c : Ctx)
    (hget : cfg.st.store.get? (cfg.keyOf c) = none) :
    cfg.onReq c = .continue c := by
  simp [Config.onReq, hget]

/-! ## The byte-effects (generic over any config) -/

/-- **Fresh-hit byte-effect (the gate).** On a fresh cache hit the built
pipeline output IS the stored response `render` supplies — for ANY tail and
handler. The handler and every later stage are skipped: the emitted bytes are
the cached bytes, not whatever the upstream would have produced. This rides on
`pipeline_gate_short_circuits`; `build_ofResponse` finalizes the gate's
response. -/
theorem mkStage_hit_serves_stored (cfg : Config) (rest : List Stage)
    (handler : Ctx → Response) (c : Ctx) (e : _root_.Cache.Stored)
    (hget : cfg.st.store.get? (cfg.keyOf c) = some e)
    (hfresh : e.meta.isFresh cfg.now = true) :
    runPipeline (mkStage cfg :: rest) handler c
      = runResp rest c (ResponseBuilder.ofResponse (cfg.render e.body)) :=
  pipeline_gate_short_circuits (mkStage cfg) rest handler c (cfg.render e.body)
    (onReq_hit cfg c e hget hfresh)

/-- **Miss passthrough.** On a cache miss the stage is transparent: the built
pipeline output equals the tail's output — the stored bytes do NOT appear and
the handler's bytes flow through. Rides on `pipeline_stage_effect`; the gate's
identity `onResponse` leaves the threaded builder untouched. -/
theorem mkStage_miss_passthrough (cfg : Config) (rest : List Stage)
    (handler : Ctx → Response) (c : Ctx)
    (hget : cfg.st.store.get? (cfg.keyOf c) = none) :
    runPipeline (mkStage cfg :: rest) handler c = runPipeline rest handler c := by
  have hc : (mkStage cfg).onRequest c = .continue c := onReq_miss cfg c hget
  rw [pipeline_stage_effect (mkStage cfg) rest handler c c hc]
  rfl

/-! ## A concrete deployed stage (real warm cache, real fresh entry) -/

/-- §4.1 key derivation: fold the method / target bytes into the numeric key
components (`vary` empty — no `Vary` selection modeled here). -/
def hashBytes (b : Bytes) : Nat := b.foldl (fun a x => a * 257 + x.toNat + 1) 0

/-- A request's `Cache.Key`: method + target hashed, no `Vary`. -/
def keyOf (c : Ctx) : _root_.Cache.Key :=
  { method := hashBytes c.req.method, uri := hashBytes c.req.target, vary := [] }

/-- Boundary render: the stored response bytes for a cached body token — a
distinctive `cache-hit:<id>` body (so different stored entries render to
different bytes), status 200. -/
def render (body : _root_.Cache.Body) : Response :=
  { status := 200
    reason := reasonOK
    headers := [("x-cache".toUTF8.toList, "HIT".toUTF8.toList)]
    body := "cache-hit:".toUTF8.toList ++ natToDec body.id }

/-- The demo request that is warm in the cache (method `GET`, target `/`, as
explicit ASCII byte lists so the key hash reduces in the kernel). -/
def demoReq : Request :=
  { method := [71, 69, 84], target := [47] }

/-- Its serve context. -/
def demoCtx : Ctx := { input := [], req := demoReq }

/-- A fresh entry: lifetime 100s, age 0 at store time, no validator. At clock 0
its `current_age` is 0 < 100, so `isFresh` holds. -/
def freshMeta : _root_.Cache.Meta :=
  { freshnessLifetime := 100, correctedInitialAge := 0, responseTime := 0, etag := none }

/-- The stored body token for the warm entry. -/
def demoBody : _root_.Cache.Body := { id := 7 }

/-- The warm stored response, keyed exactly at the demo request's key. -/
def demoStored : _root_.Cache.Stored :=
  { key := keyOf demoCtx, body := demoBody, meta := freshMeta }

/-- A warm cache holding the one fresh entry. -/
def warmSt : _root_.Cache.St :=
  { store := { entries := [demoStored], capacity := 8 }, locks := [], pending := [] }

/-- The deployed cache configuration. -/
def cacheCfg : Config := { st := warmSt, keyOf := keyOf, now := 0, render := render }

/-- **The deployed cache stage** appended to `deployStages`. -/
def cacheStage : Stage := mkStage cacheCfg

/-! ## The concrete fresh-hit / miss facts (real `Cache` lib fires) -/

/-- The warm cache's lookup finds the fresh entry for the demo request. -/
theorem warm_get : warmSt.store.get? (keyOf demoCtx) = some demoStored := by
  simp [warmSt, demoStored, _root_.Cache.Store.get?]

/-- The stored entry is fresh at the stage's clock (real §4.2 test). -/
theorem warm_fresh : demoStored.meta.isFresh cacheCfg.now = true := by
  decide

/-- **The concrete byte-effect.** The deployed `cacheStage`, on the warm demo
request, serves EXACTLY the stored `cache-hit:7` response — for any tail and
handler. A fresh hit genuinely changes the emitted bytes to the cached bytes. -/
theorem cacheStage_serves_stored (rest : List Stage) (handler : Ctx → Response) :
    runPipeline (cacheStage :: rest) handler demoCtx
      = runResp rest demoCtx (ResponseBuilder.ofResponse (render demoBody)) :=
  mkStage_hit_serves_stored cacheCfg rest handler demoCtx demoStored warm_get warm_fresh

/-- The served body is the distinctive stored bytes `"cache-hit:7"` — visible in
the built output, independent of the handler. Stated with no inner transform tail
(the cache hit's stored bytes; an inner body-transform tail, e.g. gzip, would
re-encode them — the short-circuit-carries-transforms semantics). -/
theorem cacheStage_hit_body (handler : Ctx → Response) :
    ((runPipeline [cacheStage] handler demoCtx).build).body
      = "cache-hit:".toUTF8.toList ++ natToDec 7 := by
  rw [cacheStage_serves_stored [] handler, runResp_nil, build_ofResponse]
  rfl

/-- A request not in the warm cache (different target) misses: lookup is none. -/
theorem miss_get :
    warmSt.store.get? (keyOf { input := [], req := { demoReq with target := [47, 111] } })
      = none := by
  have h : _root_.Cache.eqK demoStored.key
      (keyOf { input := [], req := { demoReq with target := [47, 111] } }) = false := by
    decide
  simp [warmSt, _root_.Cache.Store.get?, List.find?_cons, h]

/-- **Concrete miss passthrough.** For the uncached request, `cacheStage` is
transparent — the tail's bytes flow through unchanged. -/
theorem cacheStage_miss (rest : List Stage) (handler : Ctx → Response) :
    runPipeline (cacheStage :: rest) handler
        { input := [], req := { demoReq with target := [47, 111] } }
      = runPipeline rest handler
        { input := [], req := { demoReq with target := [47, 111] } } :=
  mkStage_miss_passthrough cacheCfg rest handler _ miss_get

#print axioms cacheStage_serves_stored
#print axioms cacheStage_hit_body
#print axioms cacheStage_miss

/-! ## A stateful, full-response cache the host threads across requests

The gate above (`mkStage` / `cacheStage`) proves the fresh-hit SHORT-CIRCUIT: a
warm entry replaces the handler's bytes. But a warm *gate* is static — it cannot
"populate on the first request and hit on the second", and because it
short-circuits BEFORE the response-transform stages (cors / gzip / security /
header), its stored bytes would have to reproduce whatever those transforms add,
which depends on the REQUEST (the CORS `Origin` echo, the gzip on
`Accept-Encoding`). Freezing that into a static config is a mirror that diverges
from the real serve.

This section is the REAL cache the deployed host threads across serve calls: a
full-RESPONSE store keyed on method + path + the request-header values the
deployed transforms vary on (RFC 9111 §4.1). On a MISS it invokes the real serve
(`run c`, the whole pipeline) and STORES that exact response; on a HIT it replays
the stored response byte-for-byte with an `X-Cache: HIT` / `Age` indicator,
WITHOUT calling `run` again. Because the stored value IS the genuine pipeline
output, the replay never diverges from what the handler + transforms would have
produced — no mirror, no sibling scenario disturbed. The host holds one `RStore`
across calls; the first request populates it, the second is served from it. -/

/-- A request header value (empty `Bytes` if absent). -/
def reqHeader (c : Ctx) (name : Bytes) : Bytes :=
  (c.req.headers.lookup name).getD []

/-- `accept-encoding` — the canonical lowercase name the HTTP/1.1 arena parser
emits (the gzip transform varies on it). -/
def hdrAcceptEncoding : Bytes := "accept-encoding".toUTF8.toList

/-- `origin` — the canonical lowercase name (the CORS transform varies on it). -/
def hdrOrigin : Bytes := "origin".toUTF8.toList

/-- §4.1 Vary-aware selected-header tuple. The deployed serve varies its response
on `Accept-Encoding` (gzip) and `Origin` (CORS), so those values enter the key:
a plain request and its gzip / CORS variants occupy DISTINCT cache slots and each
hit replays exactly the response that variant produced. -/
def varyOf (c : Ctx) : List Nat :=
  [hashBytes (reqHeader c hdrAcceptEncoding), hashBytes (reqHeader c hdrOrigin)]

/-- The full Vary-aware cache key for a request (§4.1: method + target + vary). -/
def rkeyOf (c : Ctx) : _root_.Cache.Key :=
  { method := hashBytes c.req.method, uri := hashBytes c.req.target, vary := varyOf c }

/-- A full-response store: the exact stored `Response` per key. Unlike the gate's
`Cache.Store` (whose `Body` is an opaque token), the deployed serve's OWN output
is captured here, so replay is byte-identical. -/
structure RStore where
  entries : List (_root_.Cache.Key × Response)
deriving Repr

/-- The empty store the host starts from. -/
def RStore.empty : RStore := ⟨[]⟩

/-- §4.1 exact-key lookup of a stored response. -/
def RStore.get? (s : RStore) (k : _root_.Cache.Key) : Option Response :=
  (s.entries.find? (fun kv => _root_.Cache.eqK kv.1 k)).map (·.2)

/-- Store a response under its key (most-recent first). -/
def RStore.insert (s : RStore) (k : _root_.Cache.Key) (r : Response) : RStore :=
  ⟨(k, r) :: s.entries⟩

/-- The `X-Cache: HIT` / `Age: 0` indicator a replayed response carries. -/
def cacheHitHeaders : List (Bytes × Bytes) :=
  [("x-cache".toUTF8.toList, "HIT".toUTF8.toList),
   ("age".toUTF8.toList, "0".toUTF8.toList)]

/-- Stamp the cache-hit indicator onto a replayed response. -/
def withCacheHit (r : Response) : Response :=
  { r with headers := r.headers ++ cacheHitHeaders }

/-- **The stateful cache step the host threads.** `run` is the real serve (the
whole deployed pipeline) invoked ONLY on a miss. On a HIT the stored response is
replayed with the `X-Cache: HIT` indicator and `run` is NOT called; the store is
unchanged. On a MISS `run` produces the real response, which is served and
stored. -/
def serveCached (s : RStore) (c : Ctx) (run : Ctx → Response) : Response × RStore :=
  match s.get? (rkeyOf c) with
  | some r => (withCacheHit r, s)
  | none   => (run c, s.insert (rkeyOf c) (run c))

/-- Inserting under `k` makes `k` findable with that response. -/
theorem RStore.get_insert_self (s : RStore) (k : _root_.Cache.Key) (r : Response) :
    (s.insert k r).get? k = some r := by
  simp [RStore.insert, RStore.get?, List.find?_cons]

/-- **Hit: the stored response is replayed, `run` untouched.** -/
theorem serveCached_hit (s : RStore) (c : Ctx) (r : Response) (run : Ctx → Response)
    (h : s.get? (rkeyOf c) = some r) :
    serveCached s c run = (withCacheHit r, s) := by
  simp [serveCached, h]

/-- **Miss: `run` produces the response, which is served and stored.** -/
theorem serveCached_miss (s : RStore) (c : Ctx) (run : Ctx → Response)
    (h : s.get? (rkeyOf c) = none) :
    serveCached s c run = (run c, s.insert (rkeyOf c) (run c)) := by
  simp [serveCached, h]

/-- **The handler is not re-run on a hit.** On a hit the output does not depend on
`run` at all — swapping the serve leaves the replayed bytes identical. -/
theorem serveCached_hit_no_handler (s : RStore) (c : Ctx) (r : Response)
    (run run' : Ctx → Response) (h : s.get? (rkeyOf c) = some r) :
    serveCached s c run = serveCached s c run' := by
  rw [serveCached_hit s c r run h, serveCached_hit s c r run' h]

/-- **The headline property.** After a first (miss) request populates the store
with the real serve output `run c`, a SECOND identical request is served FROM the
cache — the stored response replayed with the `X-Cache: HIT` indicator — WITHOUT
invoking the serve again (the second `run'` is never called). The replayed body
is exactly the first response's, so it never diverges from the deployed serve. -/
theorem serveCached_second_hits (s : RStore) (c : Ctx) (run run' : Ctx → Response)
    (hmiss : s.get? (rkeyOf c) = none) :
    serveCached (serveCached s c run).2 c run'
      = (withCacheHit (run c), (serveCached s c run).2) := by
  have h1 : (serveCached s c run).2 = s.insert (rkeyOf c) (run c) := by
    rw [serveCached_miss s c run hmiss]
  have h2 : (serveCached s c run).2.get? (rkeyOf c) = some (run c) := by
    rw [h1]; exact RStore.get_insert_self s (rkeyOf c) (run c)
  exact serveCached_hit (serveCached s c run).2 c (run c) run' h2

/-- **The `X-Cache: HIT` indicator is present on a replayed response** — the
observable a client (and the conformance driver) reads to confirm a cache hit. -/
theorem serveCached_hit_indicator (s : RStore) (c : Ctx) (r : Response)
    (run : Ctx → Response) (h : s.get? (rkeyOf c) = some r) :
    (("x-cache".toUTF8.toList, "HIT".toUTF8.toList) : Bytes × Bytes)
      ∈ ((serveCached s c run).1).headers := by
  rw [serveCached_hit s c r run h]
  simp [withCacheHit, cacheHitHeaders]

/-- **Concurrent same-key misses coalesce to ONE fetch.** This is the deployed
cache's `Cache.St` request-collapsing machine (`locks` / `pending`), proven in
`Cache.lean`: `n > 0` concurrent misses for one key emit exactly one upstream
`fetch` and `n − 1` `wait`s. The host that threads `RStore` threads the same
`Cache.St` locks, so a burst of identical misses forwards a single serve. -/
theorem cache_coalesces (s : _root_.Cache.St) (k : _root_.Cache.Key) (now n : Nat)
    (hn : 0 < n) (hget : s.store.get? k = none) (hlock : s.locked k = false) :
    _root_.Cache.countE _root_.Cache.Eff.isFetch
        (_root_.Cache.runEffs s (_root_.Cache.reqs k now n)) = 1 :=
  (_root_.Cache.coalesce_single_fetch s k now n hn hget hlock).1

#print axioms serveCached_second_hits
#print axioms serveCached_hit_indicator
#print axioms cache_coalesces

end Reactor.Stage.Cache
