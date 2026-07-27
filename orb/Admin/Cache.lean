/-
Admin.Cache — the proven invalidation decision behind `POST /admin/cache/purge`.

The admin purge drops cache entries so the next request for a purged key misses
(re-fetches from origin) instead of being served a stale body. The untrusted
shell (`crates/dataplane/src/cache.rs` → `ResponseCache::purge_all`) clears the
store; the DECISION that matters is that a purged key is thereafter a miss.

Reusing the proven RFC-9111 cache store (`Cache.Store`, whose `get?` is the
exact-key lookup the serve path hits on), this file states the purge as a store
transformer and proves:

  * `cache_purge_invalidates` — after purging a key, `get?` for that key is
    `none`: the next request is not served from cache;
  * `purgeAll_misses` — after a full purge, every key misses.

Non-vacuity: a concrete store that HITS a key is shown to MISS it after the
purge (`purge_turns_hit_to_miss`), and a no-op "purge" that leaves the store
untouched is proved to VIOLATE the invalidation contract — so the purge is
load-bearing, not decorative.
-/

import Cache

namespace Admin
namespace Cache

open _root_.Cache (Store Stored Key Body Meta eqK)

/-! ## The purge transformers -/

/-- **Full purge** (`POST /admin/cache/purge` with no key): drop every entry. -/
def purgeAll (s : Store) : Store := { s with entries := [] }

/-- **Keyed purge**: drop the entry(ies) for one exact cache key, keeping the
rest — the filter mirrors `Store.invalidate`'s drop-by-predicate shape. -/
def purgeKey (s : Store) (k : Key) : Store :=
  { s with entries := s.entries.filter (fun e => !eqK e.key k) }

/-! ## The invalidation obligation -/

/-- After a full purge the store is empty, so every key misses. -/
theorem purgeAll_misses (s : Store) (k : Key) : (purgeAll s).get? k = none := rfl

/-- **Purge invalidates.** After purging a key, the proven exact-key lookup
(`Store.get?`, the lookup the serve path hits on) returns `none` for that key:
the next request for it is NOT served from cache — it misses and re-fetches. -/
theorem cache_purge_invalidates (s : Store) (k : Key) :
    (purgeKey s k).get? k = none := by
  simp only [purgeKey, _root_.Cache.Store.get?]
  apply List.find?_eq_none.2
  intro x hx
  have hx2 := (List.mem_filter.1 hx).2
  simp only [Bool.not_eq_true'] at hx2
  simp [hx2]

/-! ## Non-vacuity — a real hit turned into a miss, and a mutant -/

/-- A concrete key. -/
def k0 : Key := { method := 0, uri := 0, vary := [] }

/-- A concrete stored entry for `k0`. -/
def e0 : Stored :=
  { key := k0, body := { id := 0 },
    «meta» := { freshnessLifetime := 100, correctedInitialAge := 0,
                responseTime := 0, etag := none } }

/-- A store holding exactly the entry for `k0`. -/
def s0 : Store := { entries := [e0], capacity := 8 }

/-- **Non-vacuity.** The store genuinely HITS `k0` before the purge, and MISSES
it after — the purge turns a real hit into a miss, so
`cache_purge_invalidates` is not vacuous. -/
theorem purge_turns_hit_to_miss :
    (s0.get? k0).isSome = true ∧ (purgeKey s0 k0).get? k0 = none :=
  ⟨by decide, cache_purge_invalidates s0 k0⟩

/-! ### The invalidation contract, and a mutant that violates it -/

/-- **The invalidation contract** over an arbitrary purge `p`: after `p s k`, the
key `k` misses. -/
def Invalidates (p : Store → Key → Store) : Prop :=
  ∀ s k, (p s k).get? k = none

/-- The real keyed purge satisfies the contract. -/
theorem purgeKey_invalidates : Invalidates purgeKey := cache_purge_invalidates

/-- A no-op mutant: pretends to purge but leaves the store untouched. -/
def noopPurge (s : Store) (_ : Key) : Store := s

/-- **Non-vacuity via a mutant.** The no-op purge VIOLATES the invalidation
contract: on `s0`/`k0` the key still HITS, so an admin purge that fails to drop
the entry would keep serving the stale body — exactly the failure the real purge
forbids. -/
theorem noopPurge_violates : ¬ Invalidates noopPurge := by
  intro h
  have hn : s0.get? k0 = none := h s0 k0
  have hs : (s0.get? k0).isSome = true := by decide
  rw [hn] at hs
  simp at hs

end Cache
end Admin
