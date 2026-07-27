/-!
# Vary-aware cache keys (RFC 9111 §4.1 — secondary cache keys)

A sans-IO model of how a shared HTTP cache derives the *secondary* cache key
from the request headers that the stored response's `Vary` field nominates.
This is the `vary` component of the `Cache.Key` triple `(method, uri, vary)`
made explicit: instead of taking the selected-header tuple as a given opaque
list, this module *computes* it from a request's header set and the response's
`Vary` field, and proves the three properties a correct Vary implementation
must satisfy.

RFC 9111 §4.1 ("Calculating Cache Keys with the Vary Header Field"):

> When a cache receives a request that can be satisfied by a stored response
> that has a `Vary` header field (Section 12.5.5 of [HTTP]), it MUST NOT use
> that response unless all of the presented request header fields nominated by
> the `Vary` header field match those fields in the original request…
>
> A `Vary` header field value of "*" always fails to match.

So the cache key must *incorporate* the value of every request header the
`Vary` field names — two requests that differ in any nominated header (e.g. a
different `Accept-Encoding`) get **different** keys, and a `Vary: *` response is
never reusable (has no key at all).

## The opaque oracle

Production caches store entries under a fixed-width *digest* of the key material
(method, target, and the selected header tuple), not the raw tuple. The digest
function is modelled as a single named, uninterpreted oracle

    hash : KeyMaterial → Digest

(cf. the `Tls`/`Crypto` libraries' named crypto boundary). This module proves
the *structure and decision around* that oracle: the key material is built
correctly from the Vary-nominated headers, and — under the oracle's
collision-freeness, taken as an explicit hypothesis `CollisionFree hash`
rather than an axiom — distinct key material yields distinct stored keys.

## Theorems

* `vary_key_includes_headers` — the derived key material incorporates every
  request header named in `Vary`: if two requests carry a *different* value for
  a nominated header, their key material differs (different `Accept-Encoding` ⇒
  different key).
* `vary_star_uncacheable` — a `Vary: *` response yields **no** cache key
  (`cacheKey r .star` has no `some`), so it can never be reused from cache.
* `vary_no_false_hit` — two requests that agree on method and target and differ
  only in a `Vary`-nominated header **never** share a stored cache key (under a
  collision-free digest oracle).
* `vary_key_same_when_headers_agree` — the converse non-degeneracy: requests
  agreeing on method, target, and every nominated header **do** share a key
  (so a legitimate cache hit remains possible; the model is not trivially
  always-miss).
-/

namespace Cache.VaryKey

/-! ## Requests, headers, and the Vary field -/

/-- A request/response header name, as an opaque identifier (e.g. the interned
token for `accept-encoding`). Comparison is case-normalised at the boundary. -/
abbrev HeaderName := Nat

/-- A header field value, as an opaque identifier. -/
abbrev HeaderValue := Nat

/-- A request reduced to what secondary-key derivation depends on: the method,
the target URI, and the presented header fields as an association list mapping
each header name to its value. -/
structure Request where
  method : Nat
  uri : Nat
  headers : List (HeaderName × HeaderValue)
deriving Repr

/-- First value presented for header `n`, or `none` if the request omits it.
RFC 9111 §4.1 treats an absent nominated field as a value that must still match
(absent-vs-present is a mismatch), which `Option` captures directly. -/
def hlookup : List (HeaderName × HeaderValue) → HeaderName → Option HeaderValue
  | [], _ => none
  | (k, v) :: t, n => if k = n then some v else hlookup t n

/-- The response's `Vary` field (RFC 9111 §4.1): either the wildcard `*`, or a
list of nominated request-header names. -/
inductive Vary where
  | star
  | names (ns : List HeaderName)
deriving Repr

/-! ## Selected header tuple and key material -/

/-- The *selected representations* tuple (RFC 9111 §4.1): pair every nominated
header name, in `Vary` order, with the value the request presents for it
(`none` if absent). This is the secondary component of the cache key. -/
def selectVary (r : Request) : List HeaderName → List (HeaderName × Option HeaderValue)
  | [] => []
  | n :: t => (n, hlookup r.headers n) :: selectVary r t

/-- The material a cache key is computed from: the primary key (method, URI)
together with the selected Vary tuple. -/
structure KeyMaterial where
  method : Nat
  uri : Nat
  selected : List (HeaderName × Option HeaderValue)
deriving Repr, DecidableEq

/-- Derive the key material for a request under a response's `Vary` field.
`Vary: *` yields `none` — RFC 9111 §4.1: such a response never matches, so no
key is produced. -/
def keyMaterial (r : Request) : Vary → Option KeyMaterial
  | .star => none
  | .names ns => some ⟨r.method, r.uri, selectVary r ns⟩

/-! ## The digest oracle -/

/-- Stored cache keys are fixed-width digests. -/
abbrev Digest := Nat

/-- The named, uninterpreted key-digest oracle (the crypto boundary). Its only
assumed property, where needed, is collision-freeness, supplied as an explicit
`CollisionFree hash` hypothesis (below) rather than an axiom. -/
axiom hash : KeyMaterial → Digest

/-- Collision-freeness of the digest oracle, stated explicitly so it is a
premise carried by the theorem that needs it — never an axiom. -/
def CollisionFree (f : KeyMaterial → Digest) : Prop :=
  ∀ a b, f a = f b → a = b

/-- The stored cache key: the digest of the key material, or `none` when the
material does not exist (`Vary: *`). -/
noncomputable def cacheKey (r : Request) (v : Vary) : Option Digest :=
  (keyMaterial r v).map hash

/-- Unfolding for a nominated-header key: it is `some` of the digest of the
concrete key material. -/
theorem cacheKey_names (r : Request) (ns : List HeaderName) :
    cacheKey r (.names ns) = some (hash ⟨r.method, r.uri, selectVary r ns⟩) := rfl

/-! ## Structural lemma: the selected tuple pins the nominated headers -/

/-- The selected Vary tuple is equal for two requests **iff** they present the
same value for every nominated header. This is the heart of §4.1 matching. -/
theorem selectVary_eq_iff (r1 r2 : Request) (ns : List HeaderName) :
    selectVary r1 ns = selectVary r2 ns
      ↔ ∀ n ∈ ns, hlookup r1.headers n = hlookup r2.headers n := by
  induction ns with
  | nil => simp [selectVary]
  | cons a t ih =>
    simp only [selectVary, List.mem_cons]
    constructor
    · intro h n hn
      rw [List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨_, hva⟩, ht⟩ := h
      rcases hn with rfl | hn
      · exact hva
      · exact ih.mp ht n hn
    · intro h
      rw [List.cons.injEq, Prod.mk.injEq]
      exact ⟨⟨rfl, h a (Or.inl rfl)⟩, ih.mpr (fun n hn => h n (Or.inr hn))⟩

/-- If two requests differ on any nominated header, their selected tuples
differ. -/
theorem selectVary_ne_of_header_ne (r1 r2 : Request) (ns : List HeaderName)
    {n : HeaderName} (hn : n ∈ ns)
    (hval : hlookup r1.headers n ≠ hlookup r2.headers n) :
    selectVary r1 ns ≠ selectVary r2 ns :=
  fun h => hval ((selectVary_eq_iff r1 r2 ns).mp h n hn)

/-! ## The three required properties -/

/-- **Vary-nominated headers are part of the key.** If a header `n` is named in
`Vary` and two requests present different values for it, their derived key
material differs. Concretely: `Vary: Accept-Encoding` with `gzip` vs `br` ⇒
different keys. -/
theorem vary_key_includes_headers (r1 r2 : Request) (ns : List HeaderName)
    {n : HeaderName} (hn : n ∈ ns)
    (hval : hlookup r1.headers n ≠ hlookup r2.headers n) :
    keyMaterial r1 (.names ns) ≠ keyMaterial r2 (.names ns) := by
  intro h
  rw [keyMaterial, keyMaterial, Option.some.injEq] at h
  exact selectVary_ne_of_header_ne r1 r2 ns hn hval (congrArg KeyMaterial.selected h)

/-- **`Vary: *` is uncacheable.** A response with `Vary: *` produces no cache
key, so it can never be served from cache (RFC 9111 §4.1: `*` always fails to
match). -/
theorem vary_star_uncacheable (r : Request) : ¬ ∃ d, cacheKey r .star = some d := by
  rintro ⟨d, h⟩
  simp [cacheKey, keyMaterial] at h

/-- **No false hit.** Two requests that agree on method and target but differ in
a `Vary`-nominated header never share a stored cache key — even when they are
otherwise identical — provided the digest oracle is collision-free. -/
theorem vary_no_false_hit (r1 r2 : Request) (ns : List HeaderName)
    {n : HeaderName} (hn : n ∈ ns)
    (_hmethod : r1.method = r2.method) (_huri : r1.uri = r2.uri)
    (hval : hlookup r1.headers n ≠ hlookup r2.headers n)
    (hcf : CollisionFree hash) :
    cacheKey r1 (.names ns) ≠ cacheKey r2 (.names ns) := by
  rw [cacheKey_names, cacheKey_names]
  intro h
  rw [Option.some.injEq] at h
  have hmat := hcf _ _ h
  rw [KeyMaterial.mk.injEq] at hmat
  exact selectVary_ne_of_header_ne r1 r2 ns hn hval hmat.2.2

/-- **Non-degeneracy (converse).** Requests that agree on method, target, and
every nominated header share the same cache key, so a genuine cache hit remains
possible — the model does not force every request to miss. -/
theorem vary_key_same_when_headers_agree (r1 r2 : Request) (ns : List HeaderName)
    (hmethod : r1.method = r2.method) (huri : r1.uri = r2.uri)
    (hagree : ∀ n ∈ ns, hlookup r1.headers n = hlookup r2.headers n) :
    cacheKey r1 (.names ns) = cacheKey r2 (.names ns) := by
  rw [cacheKey_names, cacheKey_names, hmethod, huri,
    (selectVary_eq_iff r1 r2 ns).mpr hagree]

/-! ## Concrete witness — the hypotheses are satisfiable (non-vacuity)

`Vary: Accept-Encoding`, one request with `gzip`, one with `br`, otherwise
identical, produce different key material. This exhibits a real instance of the
`vary_key_includes_headers` / `vary_no_false_hit` premises. -/

/-- Interned token for `accept-encoding`. -/
def acceptEncoding : HeaderName := 42

def reqGzip : Request := ⟨0, 7, [(acceptEncoding, 1)]⟩
def reqBr : Request := ⟨0, 7, [(acceptEncoding, 2)]⟩

example :
    keyMaterial reqGzip (.names [acceptEncoding])
      ≠ keyMaterial reqBr (.names [acceptEncoding]) :=
  vary_key_includes_headers reqGzip reqBr [acceptEncoding]
    (n := acceptEncoding) (by simp) (by decide)

example :
    cacheKey reqGzip (.names [acceptEncoding]) = cacheKey reqGzip (.names [acceptEncoding]) :=
  vary_key_same_when_headers_agree reqGzip reqGzip [acceptEncoding] rfl rfl (fun _ _ => rfl)

end Cache.VaryKey
