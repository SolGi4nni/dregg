/-
# CacheDiskLive — driving the PROVEN content-addressable disk cache over the byte level

The `Cache` foundation models RFC 9111 caching as sans-IO, proven Lean. Two
modules build the durable tiers on top of it, both *inert* (the deployed cache is
a native dataplane; these are the semantics it must realize):

  * `Cache.Disk` — the cold, content-addressable on-disk store keyed by the same
    `Cache.Key`. A key's on-disk location is `pathOf : Key → List Nat`, an
    injective, traversal-safe byte string (`pathOf_injective`, `pathOf_no_slash`,
    `pathOf_no_dot`); `put`/`get?` round-trip the real stored bytes
    (`disk_get_put`), a stale entry reads as a miss (`disk_get_expired_none`), and
    the reaper keeps exactly the fresh entries (`disk_evict_removes_expired`,
    `disk_evict_keeps_fresh`).
  * `Cache.Zones` — the cache partitioned into isolated named zones, each with its
    own byte / entry budget and its own LRU eviction. `zone_isolation` proves a
    burst that overflows one zone evicts only that zone's tail and can never
    displace — or even perturb — another zone's data.

This lane isolates the **inert, crypto-free** cold-tier logic and wires it over
the byte level, one process, under the pure Lean interpreter. It adds a
self-delimiting byte codec for a `DiskEntry` — status, headers, real body bytes,
store-time and TTL — built from a proven hex-field `Nat` codec (reusing
`Cache.Disk.toHex`/`ofHex`) and length-prefixed byte fields. The `selftest`
drives the WHOLE chain with **no crypto and no disk I/O** (the store is modelled
as the proven pure map): serialize an entry, deserialize it, store it under a key,
read it back byte-identical; check distinct keys get distinct path bytes; honour
a TTL; run a reaper sweep; and put a second entry into a budget-1 zone to show a
neighbour zone is untouched. So it runs under `lake env lean --run`.

## Honesty / realization boundary (the NetmapLive / DnsResolveLive discipline)

This is **drorb-native** and **pure**. The encoder and decoder are our own
spec-conformant peers speaking a modelled binary framing; the store is the proven
`DiskStore`/`ZonedCache` map, NOT a real filesystem and NOT the native dataplane
(the named residual: byte-exact on-disk sharded layout + fsync/rename durability +
the Rust hot/cold coupling). No socket, no FFI call: the reused C objects are
linked only to satisfy the shared executable link line and are never invoked
(this exe touches no crypto). Everything structural/codec here is the proven Lean;
the gap the selftest discharges by construction is that this exe faithfully CALLS
the proven functions on real bytes. The faithfulness of decode→store→read ITSELF
is proven below as `cache_disk_faithful`, and cross-zone non-interference as
`cache_zone_isolation`.

Usage:
  cache-disk-live selftest
-/
import Cache.Disk
import Cache.Zones

namespace CacheDiskLive

open Cache (Key)
open Cache.Disk (DiskEntry DiskStore pathOf toHex ofHex toHex_no_sep ofHex_toHex
  disk_get_put disk_path_distinct)

/-- Bytes on the wire / on disk are a list of natural-number octets, exactly as
the `Cache.Disk` model (`pathOf`, the entry body) uses them. -/
abbrev Bytes := List Nat

/-! ## §1  A self-delimiting byte codec over the proven hex machinery

A `Nat` is rendered as a hex field terminated by the separator `-` (45), reusing
`Cache.Disk.toHex` (proven to contain no separator, `toHex_no_sep`) and its left
inverse `ofHex` (`ofHex_toHex`). Raw byte fields — which may contain any octet,
separator included — are length-prefixed. Every piece carries its own round-trip
theorem, all chaining to `getEntry_put`. -/

/-- Render a `Nat` as a hex field terminated by the separator byte `45`. -/
def putNat (n : Nat) : Bytes := toHex n ++ [45]

/-- Read bytes up to (and consuming) the first separator `45`, returning the
collected field and the remaining input. -/
def getField : Bytes → Option (Bytes × Bytes)
  | [] => none
  | b :: bs => if b = 45 then some ([], bs)
               else (getField bs).map (fun fr => (b :: fr.1, fr.2))

/-- A separator-free field followed by a separator reads back verbatim. -/
theorem getField_field (f t : Bytes) (h : ∀ x ∈ f, x ≠ 45) :
    getField (f ++ 45 :: t) = some (f, t) := by
  induction f with
  | nil => simp [getField]
  | cons b bs ih =>
    have hb : b ≠ 45 := h b (by simp)
    have hbs : ∀ x ∈ bs, x ≠ 45 := fun x hx => h x (by simp [hx])
    simp [getField, List.cons_append, hb, ih hbs]

/-- Decode a hex-field `Nat`: read up to the separator, then `ofHex`. -/
def getNat (bs : Bytes) : Option (Nat × Bytes) :=
  (getField bs).map (fun fr => (ofHex fr.1, fr.2))

theorem getNat_putNat (n : Nat) (t : Bytes) : getNat (putNat n ++ t) = some (n, t) := by
  have hno : ∀ x ∈ toHex n, x ≠ 45 := toHex_no_sep n
  have h1 : putNat n ++ t = toHex n ++ 45 :: t := by
    simp [putNat, List.append_assoc]
  simp [getNat, h1, getField_field _ _ hno, ofHex_toHex]

/-- A length-prefixed raw byte field: any octet, separator included. -/
def putBytes (bs : Bytes) : Bytes := putNat bs.length ++ bs

def getBytes (bs : Bytes) : Option (Bytes × Bytes) := do
  let (n, r) ← getNat bs
  some (r.take n, r.drop n)

/-- Taking / dropping the first list's length splits an append. -/
theorem take_drop_append (l₁ l₂ : Bytes) :
    (l₁ ++ l₂).take l₁.length = l₁ ∧ (l₁ ++ l₂).drop l₁.length = l₂ := by
  induction l₁ with
  | nil => exact ⟨rfl, rfl⟩
  | cons a as ih =>
    refine ⟨?_, ?_⟩
    · show (a :: (as ++ l₂)).take (as.length + 1) = a :: as
      rw [List.take_succ_cons, ih.1]
    · show (a :: (as ++ l₂)).drop (as.length + 1) = l₂
      rw [List.drop_succ_cons, ih.2]

theorem getBytes_putBytes (bs t : Bytes) : getBytes (putBytes bs ++ t) = some (bs, t) := by
  have h1 : putBytes bs ++ t = putNat bs.length ++ (bs ++ t) := by
    simp [putBytes, List.append_assoc]
  obtain ⟨ht, hd⟩ := take_drop_append bs t
  simp [getBytes, h1, getNat_putNat, ht, hd]

/-! ### A generic count-prefixed list codec -/

def putList {α} (put1 : α → Bytes) (xs : List α) : Bytes :=
  putNat xs.length ++ (xs.map put1).flatten

def getListAux {α} (get1 : Bytes → Option (α × Bytes)) : Nat → Bytes → Option (List α × Bytes)
  | 0, bs => some ([], bs)
  | n + 1, bs => do
    let (a, r) ← get1 bs
    let (as, r2) ← getListAux get1 n r
    some (a :: as, r2)

def getList {α} (get1 : Bytes → Option (α × Bytes)) (bs : Bytes) : Option (List α × Bytes) := do
  let (n, r) ← getNat bs
  getListAux get1 n r

theorem getListAux_put {α} (put1 : α → Bytes) (get1 : Bytes → Option (α × Bytes))
    (hrt : ∀ a t, get1 (put1 a ++ t) = some (a, t)) :
    ∀ (xs : List α) (t : Bytes),
      getListAux get1 xs.length ((xs.map put1).flatten ++ t) = some (xs, t) := by
  intro xs
  induction xs with
  | nil => intro t; rfl
  | cons x xs ih =>
    intro t
    simp [List.map_cons, List.flatten_cons, List.length_cons, List.append_assoc,
      getListAux, hrt, ih t]

theorem getList_putList {α} (put1 : α → Bytes) (get1 : Bytes → Option (α × Bytes))
    (hrt : ∀ a t, get1 (put1 a ++ t) = some (a, t)) (xs : List α) (t : Bytes) :
    getList get1 (putList put1 xs ++ t) = some (xs, t) := by
  have h1 : putList put1 xs ++ t = putNat xs.length ++ ((xs.map put1).flatten ++ t) := by
    simp [putList, List.append_assoc]
  simp [getList, h1, getNat_putNat, getListAux_put put1 get1 hrt xs t]

/-! ### The `DiskEntry` codec

A stored response is the actual bytes the shell must reproduce: status code, a
list of header name/value byte pairs, the body bytes, the store time, and the
TTL. Each field goes through the codec above and round-trips. -/

def putHeader (h : Bytes × Bytes) : Bytes := putBytes h.1 ++ putBytes h.2

def getHeader (bs : Bytes) : Option ((Bytes × Bytes) × Bytes) := do
  let (name, r) ← getBytes bs
  let (val, r) ← getBytes r
  some ((name, val), r)

theorem getHeader_put (h : Bytes × Bytes) (t : Bytes) :
    getHeader (putHeader h ++ t) = some (h, t) := by
  obtain ⟨name, val⟩ := h
  simp [putHeader, getHeader, List.append_assoc, getBytes_putBytes]

def putEntry (e : DiskEntry) : Bytes :=
  putNat e.status ++
  putList putHeader e.headers ++
  putBytes e.body ++
  putNat e.storedAt ++
  putNat e.ttl

def getEntry (bs : Bytes) : Option (DiskEntry × Bytes) := do
  let (status, r) ← getNat bs
  let (headers, r) ← getList getHeader r
  let (body, r) ← getBytes r
  let (storedAt, r) ← getNat r
  let (ttl, r) ← getNat r
  some ({ status, headers, body, storedAt, ttl }, r)

/-- **The `DiskEntry` wire round-trip.** Serializing an entry then deserializing
returns it verbatim — status, every header byte pair, and the body bytes come
back unchanged — leaving the trailing bytes untouched. -/
theorem getEntry_put (e : DiskEntry) (t : Bytes) : getEntry (putEntry e ++ t) = some (e, t) := by
  obtain ⟨status, headers, body, storedAt, ttl⟩ := e
  simp [putEntry, getEntry, List.append_assoc, getNat_putNat, getBytes_putBytes,
    getList_putList putHeader getHeader getHeader_put]

/-! ## §2  Byte-level faithfulness of the disk store

Serializing an entry, deserializing it, writing it under a key, and reading that
key back yields PRECISELY the original entry — the bytes on the wire realize the
proven store, mediated only by the codec round-trip (`getEntry_put`) and the
proven `disk_get_put`.

Not a `P → P`: it is inhabited (the selftest produces such a buffer and witnesses
the equality on concrete bytes) and its content is the codec round-trip composed
with a real store operation over every store `s`, key `k`, entry `e`, and trailing
`t`. -/
theorem cache_disk_faithful (s : DiskStore) (k : Key) (e : DiskEntry) (t : Bytes) :
    (getEntry (putEntry e ++ t)).map (fun r => (s.put k r.1).get? k) = some (some e) := by
  rw [getEntry_put e t]
  show some ((s.put k e).get? k) = some (some e)
  rw [disk_get_put]

/-- **No collision at the byte level.** Distinct keys never map to the same disk
path — a hit at one key's path can never serve another key's bytes. -/
theorem cache_disk_paths_distinct {k1 k2 : Key} (h : k1 ≠ k2) : pathOf k1 ≠ pathOf k2 :=
  disk_path_distinct h

/-! ## §3  Cross-zone non-interference (eviction isolation) -/

open Cache.Zones (ZonedCache Config ZEntry zone_isolation)

/-- **`cache_zone_isolation`.** Putting an entry into the zone that owns it —
which may trigger that zone's LRU / size eviction — leaves every *other* zone's
contents bit-for-bit unchanged. So one zone's eviction pressure can never evict,
or even perturb, another zone's entries. A genuine equation over an actually
distinct zone id (`hne`), directly the proven `Cache.Zones.zone_isolation`. -/
theorem cache_zone_isolation (zc : ZonedCache) (cfg : Config) (e : ZEntry)
    (zidB : Cache.Zones.ZoneId) (hne : zidB ≠ cfg.zoneOf e.key) :
    (zc.put cfg e).getZone? zidB = zc.getZone? zidB :=
  zone_isolation zc cfg e zidB hne

/-! ## §4  Byte helpers (pure) -/

def hexNib (d : Nat) : Char := "0123456789abcdef".toList.getD d '0'

def bytesHex (b : Bytes) : String :=
  b.foldl (fun s x => s ++ s!"{hexNib (x / 16)}{hexNib (x % 16)}") ""

/-! ## §5  The selftest — the disk cache over the byte level, one process, NO crypto -/

def selftest : IO UInt32 := do
  IO.println "== cache-disk-live selftest : content-addressable disk cache, byte-level, NO crypto =="

  -- ── a real stored response: status, a header pair, real body bytes, TTL ──
  let e : DiskEntry :=
    { status := 200,
      headers := [([99, 97, 99, 104, 101], [104, 105, 116])],  -- "cache" : "hit"
      body := [104, 101, 108, 108, 111],                        -- "hello"
      storedAt := 0, ttl := 100 }

  -- ENCODE it with the codec, DECODE it back
  let wire := putEntry e
  IO.println s!"\n-- entry serialized (putEntry) --"
  IO.println s!"wire bytes             : {wire.length}B  {bytesHex (wire.take 24)}…"
  let some (decoded, rest) := getEntry wire
    | do IO.eprintln "getEntry FAILED to decode the entry"; return 1
  let decodeOk := rest.isEmpty && decide (decoded = e)
  IO.println s!"getEntry∘putEntry == entry (wire round-trip realized) : {decodeOk}"
  if !decodeOk then do IO.eprintln "entry did NOT round-trip"; return 1

  -- ── store the DECODED entry under a key, read it back byte-identical ──
  let kX : Key := { method := 71, uri := 100, vary := [] }
  let s := DiskStore.empty.put kX decoded
  let got := s.get? kX
  let roundtripOk := decide (got = some e)
  let bodyOk := decide (got.map (·.body) = some e.body)
  IO.println s!"\n-- store round-trip (put → get?) --"
  IO.println s!"get? after put == entry : {roundtripOk}"
  IO.println s!"stored body bytes match : {bodyOk}  ({bytesHex e.body})"

  -- ── distinct keys map to distinct disk paths (no collision) ──
  let kA : Key := { method := 71, uri := 100, vary := [] }
  let kB : Key := { method := 71, uri := 200, vary := [] }
  let pA := pathOf kA
  let pB := pathOf kB
  let distinctPaths := !(pA == pB)
  IO.println s!"\n-- key → path bytes (injective, traversal-safe) --"
  IO.println s!"pathOf kA              : {bytesHex pA}"
  IO.println s!"pathOf kB              : {bytesHex pB}"
  IO.println s!"distinct keys, distinct paths : {distinctPaths}"

  -- ── TTL discipline + the reaper sweep ──
  let eFresh : DiskEntry := { status := 200, headers := [], body := [104, 105], storedAt := 0, ttl := 100 }
  let eStale : DiskEntry := { status := 200, headers := [], body := [122], storedAt := 0, ttl := 10 }
  let getFreshOk := decide ((DiskStore.empty.put kA eFresh).getFresh kA 5 = some eFresh)
  let getStaleNone := decide ((DiskStore.empty.put kB eStale).getFresh kB 50 = none)
  let swept := ((DiskStore.empty.put kA eFresh).put kB eStale).evict 50
  let freshKept := decide (swept.get? kA = some eFresh)
  let staleDropped := decide (swept.get? kB = none)
  IO.println s!"\n-- freshness (RFC 9111 §4.2) + reaper sweep at now=50 --"
  IO.println s!"fresh entry served (now=5)       : {getFreshOk}"
  IO.println s!"stale entry not served (now=50)  : {getStaleNone}"
  IO.println s!"reaper keeps fresh               : {freshKept}"
  IO.println s!"reaper drops expired             : {staleDropped}"

  -- ── zone isolation: pressure one zone, a neighbour is untouched ──
  let cfg : Config :=
    { zoneOf := fun k => k.uri, maxBytes := fun _ => 1000, maxEntries := fun z => if z = 1 then 1 else 8 }
  let kOld : Key := { method := 71, uri := 1, vary := [] }
  let kNew : Key := { method := 71, uri := 1, vary := [1] }
  let kOther : Key := { method := 71, uri := 2, vary := [] }
  let eOld : ZEntry := { key := kOld, body := ⟨1⟩, size := 10 }
  let eNew : ZEntry := { key := kNew, body := ⟨2⟩, size := 10 }
  let eOther : ZEntry := { key := kOther, body := ⟨3⟩, size := 10 }
  let zc : ZonedCache :=
    ⟨[(1, { entries := [eOld], maxBytes := 1000, maxEntries := 1 }),
      (2, { entries := [eOther], maxBytes := 1000, maxEntries := 8 })]⟩
  let zc' := zc.put cfg eNew
  let evictedOld := decide (zc'.get? cfg kOld = none)     -- pressured zone dropped its LRU
  let keptNew := decide (zc'.get? cfg kNew = some eNew)
  let zone2Untouched := decide (zc'.getZone? 2 = zc.getZone? 2)  -- neighbour bit-for-bit equal
  let otherKept := decide (zc'.get? cfg kOther = some eOther)
  IO.println s!"\n-- zone isolation (put into budget-1 zone 1, neighbour zone 2) --"
  IO.println s!"zone 1 evicted its LRU entry     : {evictedOld}"
  IO.println s!"zone 1 kept the newly-put entry  : {keptNew}"
  IO.println s!"zone 2 untouched (bit-for-bit)   : {zone2Untouched}"
  IO.println s!"zone 2 entry still served        : {otherKept}"

  let ok := decodeOk && roundtripOk && bodyOk && distinctPaths &&
    getFreshOk && getStaleNone && freshKept && staleDropped &&
    evictedOld && keptNew && zone2Untouched && otherKept
  if ok then do
    IO.println "\nPASS — entry serialized, decoded, stored, read back byte-identical;"
    IO.println "       distinct keys keep distinct paths; TTL honoured, reaper swept;"
    IO.println "       zone pressure evicted only its own LRU, the neighbour zone untouched."
    IO.println "       decode→store→read equals the proven model (cache_disk_faithful),"
    IO.println "       cross-zone non-interference proven (cache_zone_isolation)."
    IO.println "DISK CACHE LIVE-WIRED (drorb-native, byte-level, NO crypto, verified codec+store)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the disk-cache pipeline did not cross-check."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do
    IO.eprintln "usage: cache-disk-live selftest"
    return 1

end CacheDiskLive

def main (args : List String) : IO UInt32 := CacheDiskLive.main args

#print axioms CacheDiskLive.cache_disk_faithful
#print axioms CacheDiskLive.cache_zone_isolation
#print axioms CacheDiskLive.getEntry_put
#print axioms CacheDiskLive.cache_disk_paths_distinct
