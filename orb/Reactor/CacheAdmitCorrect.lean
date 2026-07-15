import Reactor.ServeStep

/-!
# Reactor.CacheAdmitCorrect — the DEPLOYED cache-admission decision is sound

The deployed effect-seam serve is `drorb_serve_step`
(`Reactor.ServeStep.serveStep`). Its cache decision is `cacheableKey input`: only
for a *cacheable GET* does it yield `.cacheLookup`; otherwise it serves the fresh
fold. `Reactor.ServeStep` already proves the gate-before-lookup discipline and the
key/lifetime the store uses. This module proves the missing SOUNDNESS boundary of
that same deployed decision: which requests the cache is allowed to admit at all.

Concretely, the deployed cache **never** admits a non-`GET` method, never admits a
target outside the two cacheable route prefixes (`/static`, `/admin`), and never
admits a `Range` request (RFC 7233 — the store holds only the FULL `200`; the fold,
which genuinely answers the `206`/`416`, serves it fresh) — so a `POST` (or any
non-`GET`), a `GET` to an ordinary route, and a ranged `GET` are served fresh, not
from cache. This is the "no wrong-request cache serve" boundary for the deployed
path.
-/

namespace Reactor.CacheAdmitCorrect

open Reactor.ServeStep
open Proto (Bytes)

/-- The request-level cache-admission decision the deployed `cacheableKey` factors
through: `some key` iff a cacheable, range-free `GET`, `none` otherwise — the exact
predicate `serveStep` consults. -/
def cacheableOfReq (req : Proto.Request) : Option Bytes :=
  if isGet req && isCacheableTarget req.target && !hasRange req then some (cacheKeyOf req)
  else none

/-- `cacheableKey` (the deployed decision) is exactly `cacheableOfReq` on the
dispatched request. -/
theorem cacheableKey_factors (input : Bytes) :
    cacheableKey input = cacheableOfReq (reqOf input) := rfl

/-! ## Soundness: only cacheable GETs are admitted -/

/-- **A non-`GET` is never cached.** -/
theorem cacheableOfReq_non_get (req : Proto.Request) (h : isGet req = false) :
    cacheableOfReq req = none := by
  unfold cacheableOfReq; rw [h]; rfl

/-- **A target outside the cacheable routes is never cached.** -/
theorem cacheableOfReq_non_cacheable (req : Proto.Request)
    (h : isCacheableTarget req.target = false) : cacheableOfReq req = none := by
  unfold cacheableOfReq; rw [h, Bool.and_false]; rfl

/-- **A `Range` request is never cached** (RFC 7233): the store holds only the FULL
`200` representation, and the fold — which genuinely answers the `206`/`416` —
serves it fresh. -/
theorem cacheableOfReq_range (req : Proto.Request) (h : hasRange req = true) :
    cacheableOfReq req = none := by
  unfold cacheableOfReq; rw [h]; simp

/-- **The deployed decision rejects a non-`GET` request.** -/
theorem cacheableKey_non_get (input : Bytes) (h : isGet (reqOf input) = false) :
    cacheableKey input = none := by
  rw [cacheableKey_factors]; exact cacheableOfReq_non_get _ h

/-- **The deployed decision rejects a non-cacheable-target request.** -/
theorem cacheableKey_non_cacheable (input : Bytes)
    (h : isCacheableTarget (reqOf input).target = false) : cacheableKey input = none := by
  rw [cacheableKey_factors]; exact cacheableOfReq_non_cacheable _ h

/-- **The deployed decision rejects a `Range` request** — it is served by the
fold (`serveStep_noncacheable`), which answers the `206`/`416`. -/
theorem cacheableKey_range (input : Bytes) (h : hasRange (reqOf input) = true) :
    cacheableKey input = none := by
  rw [cacheableKey_factors]; exact cacheableOfReq_range _ h

/-! ## The deployed serve consequence: a non-cacheable request is served fresh,
with no cache effect (never a hit). -/

/-- **A non-`GET`, non-proxy request is served fresh — the cache is never
consulted.** `serveStep` (the deployed `drorb_serve_step`) `.done`-s exactly the
fresh consolidated deployed fold (`seamInner`, `Date`-finished by `revalidate`),
yielding no `.cacheLookup`/`.cacheStore` effect: a `POST` (or any non-`GET`) is
never answered from cache. -/
theorem serveStep_non_get_no_cache (mask : Nat) (input : Bytes)
    (hapi : isApiPath input = false) (h : isGet (reqOf input) = false) :
    serveStep mask input = .done (revalidate (reqOf input) (seamInner input)) :=
  serveStep_noncacheable mask input hapi (cacheableKey_non_get input h)

/-- **A `GET` to an ordinary (non-`/static`, non-`/admin`) route is served fresh.**
The deployed cache is confined to the two cacheable prefixes; every other `GET`
bypasses it. -/
theorem serveStep_non_cacheable_no_cache (mask : Nat) (input : Bytes)
    (hapi : isApiPath input = false)
    (h : isCacheableTarget (reqOf input).target = false) :
    serveStep mask input = .done (revalidate (reqOf input) (seamInner input)) :=
  serveStep_noncacheable mask input hapi (cacheableKey_non_cacheable input h)

/-! ## Non-vacuity — the boundary on real requests -/

/-- `GET /static` — a genuinely cacheable request. -/
def getStaticReq : Proto.Request := { method := getMethod, target := staticPrefix }
/-- `POST /static` — cacheable-shaped target, non-`GET` method. -/
def postStaticReq : Proto.Request := { method := [80, 79, 83, 84], target := staticPrefix }
/-- `GET /` — a `GET` to an ordinary route (not a cacheable prefix). -/
def getRootReq : Proto.Request := { method := getMethod, target := [47] }
/-- `GET /static` with `Range: bytes=0-3` — cacheable-shaped, but a range request. -/
def getStaticRangeReq : Proto.Request :=
  { method := getMethod, target := staticPrefix
    headers := [([82, 97, 110, 103, 101], [98, 121, 116, 101, 115, 61, 48, 45, 51])] }

/-- A cacheable `GET` IS admitted, under its proven key. -/
theorem getStatic_admitted : cacheableOfReq getStaticReq = some (cacheKeyOf getStaticReq) := by decide
/-- A `POST` to the same cacheable route is NOT admitted (method boundary). -/
theorem postStatic_rejected : cacheableOfReq postStaticReq = none := by decide
/-- A `GET` to an ordinary route is NOT admitted (target boundary). -/
theorem getRoot_rejected : cacheableOfReq getRootReq = none := by decide
/-- A `Range` request to the cacheable route is NOT admitted (range boundary). -/
theorem getStaticRange_rejected : cacheableOfReq getStaticRangeReq = none := by decide

/-- **The decision genuinely discriminates.** The cacheable `GET` is admitted and
the same-route `POST` is not — the deployed cache is method-scoped, not a proof
attachment. -/
theorem cache_admit_discriminates :
    cacheableOfReq getStaticReq ≠ cacheableOfReq postStaticReq := by decide

#print axioms cacheableKey_non_get
#print axioms cacheableKey_non_cacheable
#print axioms cacheableKey_range
#print axioms serveStep_non_get_no_cache
#print axioms serveStep_non_cacheable_no_cache
#print axioms getStatic_admitted
#print axioms postStatic_rejected
#print axioms getStaticRange_rejected

end Reactor.CacheAdmitCorrect
