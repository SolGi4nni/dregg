import Cache.Zones

/-!
# Cache.ZonePartition — the partitioning invariant of zoned caches

`Cache.Zones` builds a *zoned* cache: the pool is split into independent named
partitions (`Zone`), a key is routed to its owning zone by `Config.zoneOf`, and
`ZonedCache.put` / `get?` operate zone-locally with per-zone LRU eviction. That
module proves the *installation-level* isolation (`zone_isolation`: a put in one
zone leaves every other zone's stored bytes untouched) and the *single-zone*
eviction bound (`zone_evict_respects_limit`).

This module deepens the partitioning story to the three properties a partitioned
cache must actually guarantee to a tenant, stated over the top-level cache:

* `zone_partition_isolation` — **cross-zone serving never happens.** An entry
  whose key routes to a *different* zone than a request is never returned for
  that request, no matter how the cache was built. The served entry always lives
  in the request's own zone (`served_in_query_zone`). This is isolation on the
  *read* path: a zone-B request can never be answered with zone-A data.

* `zone_key_disjoint` — **keyspaces are disjoint by construction.** In a
  well-routed cache (the invariant every `put` sequence maintains), an entry
  stored in zone A always routes back to A, so no key can belong to two distinct
  zones' contents at once. The routing invariant `WellRouted` is established by
  `wellRouted_empty` and preserved by `wellRouted_put` — so it holds of every
  cache reachable from `empty`, which `wc_wellRouted` witnesses concretely.

* `zone_quota_bounded` — **each zone's eviction respects its *own* quota.** After
  a `put`, the zone that was written is within *its* byte budget and *its* entry
  budget — lifted from the single-zone bound to the routed top-level operation.

## The theorems (0 sorries; axioms ⊆ {propext, Quot.sound, Classical.choice})

All three carry real hypotheses (a served result, a stored membership, a routed
put) rather than a vacuous `P → P`, and the `§ demo` section discharges each on
concrete data built by an actual `put` sequence from `empty`.
-/

namespace Cache.ZonePartition

open Cache (Key Body eqK eqK_true)
open Cache.Zones (ZEntry Zone ZoneId ZonedCache Config)

/-! ## Read-path isolation: a request is only ever served its own zone's data -/

/-- **Whatever is served for a request lives in the request's zone.** If a
zone-scoped lookup of `k` returns `e`, then `e.key` routes to the same zone as
`k` — because `Zone.get?` only ever returns an entry whose key equals the looked
up key (`eqK`), and equal keys route identically. This holds for *any* cache,
regardless of how it was populated. -/
theorem served_in_query_zone (zc : ZonedCache) (cfg : Config) (k : Key) (e : ZEntry)
    (h : zc.get? cfg k = some e) : cfg.zoneOf e.key = cfg.zoneOf k := by
  simp only [ZonedCache.get?, Zone.get?, Option.bind_eq_some_iff] at h
  obtain ⟨z, _, hfind⟩ := h
  have hp := List.find?_some hfind
  simp only at hp
  have hkey : e.key = k := eqK_true hp
  rw [hkey]

/-- **`zone_partition_isolation`.** An entry whose key routes to a *different*
zone than the request is never served for that request — cross-partition reads
are impossible. (Contrapositive of `served_in_query_zone`.) -/
theorem zone_partition_isolation (zc : ZonedCache) (cfg : Config) (k : Key) (e : ZEntry)
    (hne : cfg.zoneOf e.key ≠ cfg.zoneOf k) : zc.get? cfg k ≠ some e := by
  intro h
  exact hne (served_in_query_zone zc cfg k e h)

/-! ## The routing invariant: keyspaces are disjoint by construction -/

/-- **Well-routed:** every entry stored in a zone routes back to that zone. This
is the structural invariant that makes the partition's keyspaces disjoint — no
zone ever holds an entry that belongs to another zone. -/
def WellRouted (cfg : Config) (zc : ZonedCache) : Prop :=
  ∀ zid z, zc.getZone? zid = some z → ∀ e ∈ z.entries, cfg.zoneOf e.key = zid

/-- Reading a zone straight after installing it under the same id returns it. -/
theorem getZone_setZone_eq (zc : ZonedCache) (zid : ZoneId) (z : Zone) :
    (zc.setZone zid z).getZone? zid = some z := by
  simp only [ZonedCache.setZone, ZonedCache.getZone?, List.find?_cons,
    decide_true, if_true]
  rfl

/-- The empty zoned cache is trivially well-routed (it stores nothing). -/
theorem wellRouted_empty (cfg : Config) : WellRouted cfg ZonedCache.empty := by
  intro zid z hz e he
  simp [ZonedCache.empty, ZonedCache.getZone?] at hz

/-- **`put` preserves well-routedness.** After routing an entry to its owning
zone and evicting, every zone still holds only its own keys: the newly-put entry
`e` routes to the target zone by definition, every surviving entry of the target
zone came from a cache that already satisfied the invariant, and every other
zone is untouched. So the invariant holds of every cache reachable from
`empty`. -/
theorem wellRouted_put (cfg : Config) (zc : ZonedCache) (e : ZEntry)
    (h : WellRouted cfg zc) : WellRouted cfg (zc.put cfg e) := by
  intro zid z hz e' he'
  simp only [ZonedCache.put] at hz
  by_cases hcase : zid = cfg.zoneOf e.key
  · subst hcase
    rw [getZone_setZone_eq] at hz
    injection hz with hzeq
    subst hzeq
    have hsub : e' ∈ ((zc.zoneFor cfg (cfg.zoneOf e.key)).put e).entries := by
      have hpre := Cache.Zones.zone_lru_evicts_oldest ((zc.zoneFor cfg (cfg.zoneOf e.key)).put e)
      exact hpre.sublist.subset he'
    rw [Zone.put] at hsub
    simp only [List.mem_cons, List.mem_filter] at hsub
    rcases hsub with rfl | ⟨hmem, _⟩
    · rfl
    · cases hg : zc.getZone? (cfg.zoneOf e.key) with
      | none =>
        rw [ZonedCache.zoneFor, hg] at hmem
        simp [Config.emptyZone] at hmem
      | some zold =>
        rw [ZonedCache.zoneFor, hg] at hmem
        simp only [Option.getD_some] at hmem
        exact h (cfg.zoneOf e.key) zold hg e' hmem
  · rw [Cache.Zones.getZone_setZone_ne zc (cfg.zoneOf e.key) zid _
        (fun heq => hcase heq.symm)] at hz
    exact h zid z hz e' he'

/-- **`zone_key_disjoint`.** In a well-routed cache the partition's keyspaces do
not overlap: an entry stored in zone `zidA` whose key routes to zone `zidB`
forces `zidA = zidB`. So a single key can never populate two distinct zones —
the partition is disjoint by construction. -/
theorem zone_key_disjoint (cfg : Config) (zc : ZonedCache) (hwr : WellRouted cfg zc)
    (zidA zidB : ZoneId) (zA : Zone) (e : ZEntry)
    (hzA : zc.getZone? zidA = some zA) (hmem : e ∈ zA.entries)
    (hroute : cfg.zoneOf e.key = zidB) : zidA = zidB := by
  have hin : cfg.zoneOf e.key = zidA := hwr zidA zA hzA e hmem
  exact Eq.trans hin.symm hroute

/-! ## Per-zone quota: a routed put respects the written zone's own budget -/

/-- **`zone_quota_bounded`.** After a routed `put`, the zone that was written is
within *its own* byte budget and *its own* entry budget — the top-level lift of
`zone_evict_respects_limit`. A zone's eviction is accounted against that zone's
quota alone. -/
theorem zone_quota_bounded (zc : ZonedCache) (cfg : Config) (e : ZEntry) (z' : Zone)
    (hz' : (zc.put cfg e).getZone? (cfg.zoneOf e.key) = some z') :
    z'.bytes ≤ z'.maxBytes ∧ z'.count ≤ z'.maxEntries := by
  simp only [ZonedCache.put] at hz'
  rw [getZone_setZone_eq] at hz'
  injection hz' with hz'
  subst hz'
  exact Cache.Zones.zone_evict_respects_limit ((zc.zoneFor cfg (cfg.zoneOf e.key)).put e)

/-! ## Non-vacuous demo: the invariant on a cache built by real puts

Two entries are inserted from `empty` under a URI-partitioner: `eA` (uri 1 →
zone 1) and `eB` (uri 2 → zone 2). We show the resulting cache satisfies
`WellRouted` (via the preservation theorems, not by hand), then discharge each
headline theorem on this concrete cache. -/

def cfg2 : Config where
  zoneOf := fun k => k.uri
  maxBytes := fun _ => 1000
  maxEntries := fun _ => 4

def kA : Key := { method := 71, uri := 1, vary := [] }
def kB : Key := { method := 71, uri := 2, vary := [] }
def eA : ZEntry := { key := kA, body := ⟨1⟩, size := 10 }
def eB : ZEntry := { key := kB, body := ⟨2⟩, size := 10 }

/-- A cache built by two real `put`s from `empty`. -/
def wc : ZonedCache := (ZonedCache.empty.put cfg2 eA).put cfg2 eB

/-- `wc` is well-routed — established purely from the preservation theorems, so
the routing invariant is not assumed but *derived* for a reachable cache. -/
theorem wc_wellRouted : WellRouted cfg2 wc :=
  wellRouted_put cfg2 _ eB (wellRouted_put cfg2 _ eA (wellRouted_empty cfg2))

/-- The two demo keys really land in different zones. -/
example : cfg2.zoneOf eA.key ≠ cfg2.zoneOf eB.key := by decide

/-- `eA` is served for its own request. -/
example : wc.get? cfg2 kA = some eA := by decide

/-- **Read isolation on real data:** `eA` (zone 1) is never served for a `kB`
(zone 2) request. -/
example : wc.get? cfg2 kB ≠ some eA :=
  zone_partition_isolation wc cfg2 kB eA (by decide)

/-- **Disjointness on real data:** `eA` is stored in zone 1, and its key routes
to zone 1 — so `zone_key_disjoint` forces any zone claiming it to be zone 1. -/
example (zidB : ZoneId) (hroute : cfg2.zoneOf eA.key = zidB) : (1 : ZoneId) = zidB := by
  have hz1 : wc.getZone? 1 = some ⟨[eA], 1000, 4⟩ := by decide
  exact zone_key_disjoint cfg2 wc wc_wellRouted 1 zidB _ eA hz1 (by decide) hroute

/-- **Quota on real data:** the zone written by the last `put` stays within its
own entry budget. -/
example : ∀ z', wc.getZone? (cfg2.zoneOf eB.key) = some z' →
    z'.count ≤ z'.maxEntries :=
  fun z' h => (zone_quota_bounded (ZonedCache.empty.put cfg2 eA) cfg2 eB z' h).2

end Cache.ZonePartition

#print axioms Cache.ZonePartition.zone_partition_isolation
#print axioms Cache.ZonePartition.zone_key_disjoint
#print axioms Cache.ZonePartition.zone_quota_bounded
#print axioms Cache.ZonePartition.wellRouted_put
