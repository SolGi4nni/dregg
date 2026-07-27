import Cache

/-!
# Cache.Zones — partitioned cache zones (RFC 9111 storage, isolated partitions)

The `Cache` library models one shared (proxy) HTTP cache: a bounded LRU `Store`
with freshness, coalescing, and revalidation (the *hot* tier), and `Cache.Disk`
adds the durable *cold* tier. Both are a single, undivided pool: eviction
pressure anywhere competes with every entry everywhere.

This module adds **zones**: the cache is partitioned into independent named
partitions, each with its own byte / entry budget and its own LRU eviction. A
cache key is routed to a zone by a `zoneOf` partitioner (e.g. by host / route),
and eviction is *zone-local* — a burst that overflows one zone evicts only that
zone's least-recently-used entries and can never displace another zone's data.

RFC 9111 §3 permits a cache to bound its storage and evict; nothing there
requires one global pool. Zones realize the bound *per partition* so a hot,
churny tenant (one host) cannot starve a cold, valuable one. This is the model
behind a per-zone size limit: a tenant gets a guaranteed slice, isolated from
its neighbours' pressure.

## The model

* `ZEntry` — a zone entry: the reused `Cache.Key` + opaque `Cache.Body` payload
  token, plus the byte `size` the zone's byte budget accounts. `ZEntry.ofStored`
  adapts an in-memory `Cache.Stored` into a zone entry, so a zone composes over
  the reused hot-tier entry type.
* `Zone` — one partition: its `entries` (most-recently-used first, exactly the
  hot-tier `Cache.Store` recency discipline), a `maxBytes` and a `maxEntries`
  budget. `Zone.put` prepends (MRU) and drops any prior entry for the key;
  `Zone.evict` drops least-recently-used entries (from the tail) until the zone
  is within *both* budgets.
* `ZonedCache` — the top-level partitioner: a finite map `ZoneId → Zone`.
  `ZonedCache.put`/`get?` route through a `Config.zoneOf` to the owning zone and
  operate zone-locally.

## The theorems (0 sorries; axioms ⊆ {propext, Quot.sound, Classical.choice})

* `zone_isolation` — **the partitioning property**: putting (and evicting) in the
  zone that owns `e` leaves *every other* zone's contents bit-for-bit unchanged.
  `zone_isolation_get`: a lookup in another zone is entirely unaffected. So
  eviction pressure in one zone cannot evict another zone's entries.
* `zone_evict_respects_limit` — a zone's eviction brings it within *both* its
  byte budget and its entry budget (`bytes ≤ maxBytes ∧ count ≤ maxEntries`).
* `zone_get_put` — get-after-put within a zone returns the stored entry.
* `zone_lru_evicts_oldest` — eviction drops the least-recently-used entries: the
  kept set is a *prefix* of the entries (the most-recently-used), so what is
  dropped is exactly the LRU tail. A concrete two-entry truth table nails it.

A non-vacuous truth table (`§ demo`) puts pressure on one zone (entry budget 1,
two entries) and asserts the *other* zone's entry survives untouched while the
pressured zone evicts its LRU entry.
-/

namespace Cache.Zones

open Cache (Key Body Stored eqK eqK_refl eqK_true)

/-! ## Zone entries -/

/-- A zone id — a partition identifier (e.g. a host / route hash). -/
abbrev ZoneId := Nat

/-- A zone entry: the reused `Cache.Key` and opaque `Cache.Body` payload token
(the body bytes are outside the model, exactly as the hot tier), plus the byte
`size` the zone's byte budget accounts for this entry. -/
structure ZEntry where
  key : Key
  body : Body
  size : Nat
deriving Repr, DecidableEq

/-- Adapt an in-memory `Cache.Stored` into a zone entry with an accounted byte
size — a zone composes over the reused hot-tier entry type. -/
def ZEntry.ofStored (s : Stored) (size : Nat) : ZEntry :=
  { key := s.key, body := s.body, size := size }

/-! ## A single zone (partition) -/

/-- One cache partition: its entries most-recently-used first (the hot-tier
`Cache.Store` recency discipline — `put` prepends, so the tail is LRU), and its
byte / entry budgets. -/
structure Zone where
  entries : List ZEntry
  maxBytes : Nat
  maxEntries : Nat
deriving Repr, DecidableEq

/-- Total bytes a list of entries accounts. -/
def sizeSum (es : List ZEntry) : Nat := (es.map (·.size)).sum

/-- The zone's current byte occupancy (sum of entry sizes). -/
def Zone.bytes (z : Zone) : Nat := sizeSum z.entries

/-- The zone's current entry count. -/
def Zone.count (z : Zone) : Nat := z.entries.length

/-- §4.1 exact-key lookup within a zone. -/
def Zone.get? (z : Zone) (k : Key) : Option ZEntry :=
  z.entries.find? (fun e => eqK e.key k)

/-- Insert/replace, LRU: drop any prior entry for the key and prepend the new
one (most-recently-used at the head), mirroring `Cache.Store.insert`. -/
def Zone.put (z : Zone) (e : ZEntry) : Zone :=
  { z with entries := e :: z.entries.filter (fun x => !eqK x.key e.key) }

/-- A hit moves the entry to the front (LRU recency), mirroring
`Cache.Store.touch`. A miss leaves the zone unchanged. -/
def Zone.touch (z : Zone) (k : Key) : Zone :=
  match z.get? k with
  | some e => { z with entries := e :: z.entries.filter (fun x => !eqK x.key k) }
  | none => z

/-! ## Zone-local LRU / size eviction

Evict least-recently-used entries — the tail, since the head is MRU — until the
zone is within *both* budgets. When a zone is over budget it is non-empty (an
empty zone has 0 bytes and 0 entries, within any budget), so each step strictly
shrinks it; the recursion terminates and the postcondition holds (worst case:
the zone empties, which is trivially within budget). -/

/-- Fuel-driven eviction: each step drops the LRU tail (`dropLast`) while the
list is over either budget. `fuel = es.length` is enough steps to empty the list
in the worst case (each step shrinks it by one), so `evictTo` below always
reaches a within-budget fixpoint. Structural on `fuel` — it reduces in the
kernel, so the demo truth table below decides. -/
def evictFuel (maxB maxE : Nat) : Nat → List ZEntry → List ZEntry
  | 0, es => es
  | fuel + 1, es =>
    if sizeSum es > maxB ∨ es.length > maxE then
      evictFuel maxB maxE fuel es.dropLast
    else es

/-- Evict from the tail (LRU) until `sizeSum ≤ maxB` and `length ≤ maxE`. -/
def evictTo (maxB maxE : Nat) (es : List ZEntry) : List ZEntry :=
  evictFuel maxB maxE es.length es

/-- The zone after eviction: within both budgets, dropping only the LRU tail. -/
def Zone.evict (z : Zone) : Zone :=
  { z with entries := evictTo z.maxBytes z.maxEntries z.entries }

/-- With at least `es.length` fuel, eviction reaches a within-budget fixpoint. -/
theorem evictFuel_within (maxB maxE : Nat) :
    ∀ (fuel : Nat) (es : List ZEntry), es.length ≤ fuel →
      sizeSum (evictFuel maxB maxE fuel es) ≤ maxB
        ∧ (evictFuel maxB maxE fuel es).length ≤ maxE := by
  intro fuel
  induction fuel with
  | zero =>
    intro es hlen
    have hnil : es = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    subst hnil
    simp [evictFuel, sizeSum]
  | succ fuel ih =>
    intro es hlen
    rw [evictFuel]
    split
    · apply ih
      rw [List.length_dropLast]
      omega
    · next h =>
      exact ⟨Nat.le_of_not_lt (fun hlt => h (Or.inl hlt)),
             Nat.le_of_not_lt (fun hlt => h (Or.inr hlt))⟩

/-- **Eviction respects both budgets.** After a zone evicts, its byte occupancy
is within its byte budget and its entry count is within its entry budget. -/
theorem evictTo_within (maxB maxE : Nat) (es : List ZEntry) :
    sizeSum (evictTo maxB maxE es) ≤ maxB ∧ (evictTo maxB maxE es).length ≤ maxE :=
  evictFuel_within maxB maxE es.length es (Nat.le_refl _)

/-- Each eviction step keeps a prefix of the entries (the most-recently-used). -/
theorem evictFuel_prefix (maxB maxE : Nat) :
    ∀ (fuel : Nat) (es : List ZEntry), evictFuel maxB maxE fuel es <+: es := by
  intro fuel
  induction fuel with
  | zero => intro es; rw [evictFuel]; exact List.prefix_refl es
  | succ fuel ih =>
    intro es
    rw [evictFuel]
    split
    · refine (ih es.dropLast).trans ?_
      rw [List.dropLast_eq_take]
      exact List.take_prefix _ es
    · exact List.prefix_refl es

/-- **Eviction drops only the least-recently-used tail.** The kept entries are a
prefix of the originals — the most-recently-used — so what is evicted is exactly
the LRU tail. -/
theorem evictTo_prefix (maxB maxE : Nat) (es : List ZEntry) :
    evictTo maxB maxE es <+: es :=
  evictFuel_prefix maxB maxE es.length es

/-- **`zone_evict_respects_limit`.** A zone's eviction brings it within its byte
budget *and* its entry budget. -/
theorem zone_evict_respects_limit (z : Zone) :
    z.evict.bytes ≤ z.maxBytes ∧ z.evict.count ≤ z.maxEntries := by
  simp only [Zone.evict, Zone.bytes, Zone.count]
  exact evictTo_within z.maxBytes z.maxEntries z.entries

/-- **`zone_lru_evicts_oldest`.** The entries a zone keeps after eviction are a
prefix (the most-recently-used) of its entries — eviction drops the LRU tail. -/
theorem zone_lru_evicts_oldest (z : Zone) : z.evict.entries <+: z.entries := by
  simp only [Zone.evict]
  exact evictTo_prefix z.maxBytes z.maxEntries z.entries

/-- **`zone_get_put`.** Reading a key straight after putting it into a zone
returns the stored entry. -/
theorem zone_get_put (z : Zone) (e : ZEntry) : (z.put e).get? e.key = some e := by
  simp [Zone.put, Zone.get?, List.find?_cons, eqK_refl]

/-! ## The top-level zoned cache (the partitioner) -/

/-- The zoned cache: a finite map from zone id to `Zone` (association list,
keys unique after `setZone`). -/
structure ZonedCache where
  zones : List (ZoneId × Zone)
deriving Repr, DecidableEq

/-- The empty zoned cache. -/
def ZonedCache.empty : ZonedCache := ⟨[]⟩

/-- Look up a zone by id. -/
def ZonedCache.getZone? (zc : ZonedCache) (zid : ZoneId) : Option Zone :=
  (zc.zones.find? (fun p => decide (p.1 = zid))).map (·.2)

/-- Install (replace/insert) a zone under an id. -/
def ZonedCache.setZone (zc : ZonedCache) (zid : ZoneId) (z : Zone) : ZonedCache :=
  ⟨(zid, z) :: zc.zones.filter (fun p => !decide (p.1 = zid))⟩

/-- The zoned-cache configuration: how a key routes to a zone, and each zone's
byte / entry budgets. -/
structure Config where
  /-- The partitioner: a cache key's owning zone (e.g. by host / route). -/
  zoneOf : Key → ZoneId
  /-- Per-zone byte budget. -/
  maxBytes : ZoneId → Nat
  /-- Per-zone entry budget. -/
  maxEntries : ZoneId → Nat

/-- The (empty) zone template a zone id gets on first use — its budgets from the
config. -/
def Config.emptyZone (cfg : Config) (zid : ZoneId) : Zone :=
  { entries := [], maxBytes := cfg.maxBytes zid, maxEntries := cfg.maxEntries zid }

/-- The current zone for an id, or a fresh (empty) one with the configured
budgets if the id has no entries yet. -/
def ZonedCache.zoneFor (zc : ZonedCache) (cfg : Config) (zid : ZoneId) : Zone :=
  (zc.getZone? zid).getD (cfg.emptyZone zid)

/-- **Zone-scoped put.** Route the entry to its owning zone, put it there, evict
that zone back within budget, and install the updated zone. Only the owning zone
is touched. -/
def ZonedCache.put (zc : ZonedCache) (cfg : Config) (e : ZEntry) : ZonedCache :=
  let zid := cfg.zoneOf e.key
  zc.setZone zid ((zc.zoneFor cfg zid).put e).evict

/-- **Zone-scoped get.** Route the key to its owning zone and look it up there. -/
def ZonedCache.get? (zc : ZonedCache) (cfg : Config) (k : Key) : Option ZEntry :=
  (zc.getZone? (cfg.zoneOf k)).bind (fun z => z.get? k)

/-! ### The partitioning (isolation) property -/

/-- `find?` over a `filter` that only removes entries the search predicate never
matches returns the same result as `find?` over the whole list. -/
theorem find?_filter_of_removed_nomatch {α} (p keep : α → Bool)
    (h : ∀ a, keep a = false → p a = false) :
    ∀ l : List α, (l.filter keep).find? p = l.find? p := by
  intro l
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.filter_cons]
    by_cases hk : keep a = true
    · rw [if_pos hk]
      cases hp : p a <;> simp [List.find?_cons, hp, ih]
    · rw [if_neg hk, ih]
      have hkf : keep a = false := by simpa using hk
      have hpf : p a = false := h a hkf
      simp [List.find?_cons, hpf]

/-- **Installing a zone leaves every *other* zone's lookup unchanged.** -/
theorem getZone_setZone_ne (zc : ZonedCache) (zidA zidB : ZoneId) (z : Zone)
    (hne : zidA ≠ zidB) :
    (zc.setZone zidA z).getZone? zidB = zc.getZone? zidB := by
  simp only [ZonedCache.setZone, ZonedCache.getZone?]
  have hkey : (List.find? (fun p => decide (p.1 = zidB))
      ((zidA, z) :: zc.zones.filter (fun p => !decide (p.1 = zidA))))
      = zc.zones.find? (fun p => decide (p.1 = zidB)) := by
    rw [List.find?_cons]
    have hhead : decide ((zidA, z).1 = zidB) = false := by
      simp only [decide_eq_false_iff_not]; exact hne
    rw [hhead]
    simp only [Bool.false_eq_true, if_false]
    exact find?_filter_of_removed_nomatch
      (fun p => decide (p.1 = zidB)) (fun p => !decide (p.1 = zidA))
      (by
        intro a ha
        simp only [Bool.not_eq_false', decide_eq_true_eq] at ha
        simp only [decide_eq_false_iff_not]
        rw [ha]; exact hne) zc.zones
  rw [hkey]

/-- **`zone_isolation` (the core partitioning property).** Putting (with its
zone-local eviction) into the zone that owns `e` leaves every *other* zone's
contents bit-for-bit unchanged — eviction pressure in one zone cannot evict, or
even perturb, another zone's entries. -/
theorem zone_isolation (zc : ZonedCache) (cfg : Config) (e : ZEntry) (zidB : ZoneId)
    (hne : zidB ≠ cfg.zoneOf e.key) :
    (zc.put cfg e).getZone? zidB = zc.getZone? zidB := by
  simp only [ZonedCache.put]
  exact getZone_setZone_ne zc (cfg.zoneOf e.key) zidB _ (Ne.symm hne)

/-- **`zone_isolation` at the lookup level.** A key that lives in a different
zone than `e` reads exactly the same before and after `e`'s put — a neighbour's
pressure is invisible. -/
theorem zone_isolation_get (zc : ZonedCache) (cfg : Config) (e : ZEntry) (k : Key)
    (hne : cfg.zoneOf k ≠ cfg.zoneOf e.key) :
    (zc.put cfg e).get? cfg k = zc.get? cfg k := by
  simp only [ZonedCache.get?]
  rw [zone_isolation zc cfg e (cfg.zoneOf k) hne]

/-- **Zone-scoped get-after-put (same zone).** Putting `e` then reading its key
returns `e`, *provided* the entry survives its zone's eviction (e.g. it fits the
zone's budgets). The hypothesis is exactly "`e` is still the owning zone's head
entry after eviction". -/
theorem zoned_get_put (zc : ZonedCache) (cfg : Config) (e : ZEntry)
    (hsurv : (((zc.zoneFor cfg (cfg.zoneOf e.key)).put e).evict).get? e.key = some e) :
    (zc.put cfg e).get? cfg e.key = some e := by
  simp only [ZonedCache.get?, ZonedCache.put]
  rw [ZonedCache.getZone?, ZonedCache.setZone]
  simp only [List.find?_cons, decide_eq_true_eq, Option.map_some, Option.bind_some]
  exact hsurv

/-! ## Non-vacuous truth table: pressure on one zone, isolation of the other

Two zones partitioned by `zoneOf k = k.uri`. Zone `1` has an entry budget of 1
and already holds one (older) entry; zone `2` holds its own entry with a roomy
budget. We put a *second* entry into zone `1`, forcing an eviction. The
assertions below check, on real data, that:

* zone `1` evicts its LRU entry (the older one) and keeps the newly-put one, and
* zone `2`'s entry is untouched — the pressure did not cross the partition. -/

/-- A distinct payload token per entry. -/
def bOld : Body := { id := 1 }
def bNew : Body := { id := 2 }
def bOther : Body := { id := 3 }

/-- Two keys in zone `1` (`uri = 1`, distinct `vary`), one in zone `2`
(`uri = 2`). -/
def kOld : Key := { method := 71, uri := 1, vary := [] }
def kNew : Key := { method := 71, uri := 1, vary := [1] }
def kOther : Key := { method := 71, uri := 2, vary := [] }

def eOld : ZEntry := { key := kOld, body := bOld, size := 10 }
def eNew : ZEntry := { key := kNew, body := bNew, size := 10 }
def eOther : ZEntry := { key := kOther, body := bOther, size := 10 }

/-- Partition by target URI; zone `1` caps at one entry, others are roomy. -/
def demoCfg : Config where
  zoneOf := fun k => k.uri
  maxBytes := fun _ => 1000
  maxEntries := fun z => if z = 1 then 1 else 8

/-- Zone `1` already holds the older entry (at its cap of 1); zone `2` holds its
own entry with room to spare. -/
def demoCache : ZonedCache :=
  ⟨[(1, { entries := [eOld], maxBytes := 1000, maxEntries := 1 }),
    (2, { entries := [eOther], maxBytes := 1000, maxEntries := 8 })]⟩

/-- The two keys really are in the same (pressured) zone, distinct from the
other. -/
example : demoCfg.zoneOf kOld = demoCfg.zoneOf kNew := rfl
example : demoCfg.zoneOf kOther ≠ demoCfg.zoneOf kNew := by decide

/-- The zone-`1` eviction, computed: putting `eNew` on top of `[eOld]` at an
entry cap of 1 drops the LRU tail `eOld`, keeping `[eNew]`. -/
example : evictTo 1000 1 [eNew, eOld] = [eNew] := by decide

/-- **Pressure evicts the LRU entry of zone `1`.** After putting `eNew`, zone `1`
holds exactly `[eNew]` — the older `eOld` was evicted (it is the LRU tail). -/
example : ((demoCache.put demoCfg eNew).getZone? 1).map (·.entries) = some [eNew] := by
  decide

/-- The evicted `eOld` is gone from zone `1`. -/
example : (demoCache.put demoCfg eNew).get? demoCfg kOld = none := by decide

/-- The newly-put `eNew` is served from zone `1`. -/
example : (demoCache.put demoCfg eNew).get? demoCfg kNew = some eNew := by decide

/-- **Isolation:** zone `2`'s entry is completely untouched by the pressure in
zone `1` — its lookup is unchanged (concretely, and by the general theorem). -/
example : (demoCache.put demoCfg eNew).get? demoCfg kOther = some eOther := by decide

example : (demoCache.put demoCfg eNew).getZone? 2 = demoCache.getZone? 2 :=
  zone_isolation demoCache demoCfg eNew 2 (by decide)

end Cache.Zones

#print axioms Cache.Zones.zone_isolation
#print axioms Cache.Zones.zone_isolation_get
#print axioms Cache.Zones.zone_evict_respects_limit
#print axioms Cache.Zones.zone_lru_evicts_oldest
#print axioms Cache.Zones.zone_get_put
