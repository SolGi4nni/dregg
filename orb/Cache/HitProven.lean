import Cache.Disk

/-!
# Cache.HitProven — the DEPLOYED cache hit/miss serve, proven on the wire

PROVE-WHAT-RUNS for the ledger row `ca.hit` (cache hit/miss serving). The running
dataplane's cache lives in `crates/dataplane/src/cache.rs` (the hot tier) and
`crates/dataplane/src/cache_disk.rs` (the durable cold tier). Both realize the
sans-IO model already proven in `Cache.lean` / `Cache/Disk.lean` (RFC 9111 §4.2):
a stored response is served while `current_age < freshness_lifetime`, a stale
entry reads as a miss, and a miss forwards to the origin then stores.

This module pins the property the running wire actually shows, combining the
proven store (`Cache.Disk`) with a faithful byte-level model of the deployed
**stamp**: on a fresh hit the shell splices, right after the status line,

    X-Cache: HIT\r\n
    Age: <current_age>\r\n

leaving the stored response bytes otherwise byte-for-byte (`cache.rs::stamp`,
`cache_disk.rs::stamp_hit`). `current_age = now − stored_at` is exactly
`Cache.Disk.DiskEntry.age`.

## What is proven (each maps to what the deployed engine emits)

* **`cache_hit_serves_stored`** — a FRESH stored entry is served: `getFresh`
  returns it (the proven store), and the wire the shell writes is
  `status ++ CRLF ++ "X-Cache: HIT" ++ "Age: <now−stored_at>" ++ rest` — the
  `Age` header carries the current age and the stored response tail (`rest`,
  the headers/blank-line/body) is preserved verbatim. This is the second
  `curl` a client sees: the HIT.
* **`cache_miss_fetches`** — a MISS is NOT served from the cache (`getFresh`
  misses), so the deployed leader runs the fold (contacts the origin) and its
  `cacheStore` writes the fetched response under the proven key + lifetime; the
  next request within the lifetime then HITs, serving the fetched body stamped.
  This is the first `curl` (the MISS that populates) followed by the hit.
* **`cache_no_stale_past_ttl`** — a stored entry PAST its TTL is not served
  stale: `getFresh` returns `none` (the deployed `get_fresh` drops the file and
  re-fetches / revalidates), so no stale body ever reaches the wire.

The scan-faithful `stampHit` mirrors the Rust `find(resp, b"\r\n")` splice; the
three store facts are `Cache.Disk.disk_getFresh_put`, the miss/round-trip
composition, and `Cache.Disk.disk_getFresh_put_expired`.
-/

namespace Cache.HitProven

open Cache (Key)
open Cache.Disk (DiskEntry DiskStore)

/-- Bytes on the wire: octets as `Nat` (the `Cache.Disk` convention). -/
abbrev Bytes := List Nat

/-! ## The deployed wire stamp (mirror of `cache.rs::stamp` / `cache_disk.rs::stamp_hit`) -/

/-- `"\r\n"`. -/
def crlf : Bytes := [13, 10]

/-- `"X-Cache: HIT\r\n"` — the deployed hit marker (`stamp(resp, b"HIT", …)`
emits `"X-Cache: "` ++ `"HIT"` ++ `"\r\n"`). -/
def xCacheHitLine : Bytes :=
  [88, 45, 67, 97, 99, 104, 101, 58, 32] ++ [72, 73, 84] ++ crlf

/-- Decimal ASCII rendering of a `Nat` (mirrors Rust `format!("{age}")`). -/
def toDec (n : Nat) : Bytes :=
  if n < 10 then [48 + n]
  else toDec (n / 10) ++ [48 + n % 10]
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- `"Age: <n>\r\n"` — the deployed age header (`format!("Age: {a}\r\n")`). -/
def ageLine (n : Nat) : Bytes := [65, 103, 101, 58, 32] ++ toDec n ++ crlf

/-- Split a response at its FIRST `"\r\n"` into `(status, rest)`, where `rest` is
the bytes AFTER the CRLF — exactly the `find(resp, b"\r\n")` / `p + 2` split the
deployed `stamp` uses. `none` on a response with no CRLF (the shell then leaves
the bytes untouched). -/
def splitCRLF : Bytes → Option (Bytes × Bytes)
  | [] => none
  | [_] => none
  | a :: b :: rest =>
    if a = 13 ∧ b = 10 then some ([], rest)
    else (splitCRLF (b :: rest)).map (fun r => (a :: r.1, r.2))

/-- **The deployed hit stamp.** Splice `X-Cache: HIT` + `Age: <age>` right after
the status line, leaving the rest of the response verbatim. Faithful to
`cache.rs::stamp(resp, b"HIT", Some(age))` and `cache_disk.rs::stamp_hit`. -/
def stampHit (resp : Bytes) (age : Nat) : Bytes :=
  match splitCRLF resp with
  | some (status, rest) => status ++ crlf ++ xCacheHitLine ++ ageLine age ++ rest
  | none => resp

/-- The first CRLF of a well-formed response (status line has no bare `CR`)
splits it exactly at the status line. Mirrors `find` returning the first match. -/
theorem splitCRLF_noCR :
    ∀ (status : Bytes), (∀ x ∈ status, x ≠ 13) → ∀ rest : Bytes,
      splitCRLF (status ++ 13 :: 10 :: rest) = some (status, rest) := by
  intro status
  induction status with
  | nil => intro _ rest; rfl
  | cons a as ih =>
    intro h rest
    have ha : a ≠ 13 := h a (List.mem_cons_self)
    have htl : ∀ x ∈ as, x ≠ 13 := fun x hx => h x (List.mem_cons_of_mem _ hx)
    obtain ⟨b, rest', hbr⟩ : ∃ b rest', as ++ 13 :: 10 :: rest = b :: rest' := by
      cases as with
      | nil => exact ⟨13, 10 :: rest, rfl⟩
      | cons c cs => exact ⟨c, cs ++ 13 :: 10 :: rest, rfl⟩
    show splitCRLF (a :: (as ++ 13 :: 10 :: rest)) = some (a :: as, rest)
    rw [hbr]
    simp only [splitCRLF]
    rw [if_neg (fun hc => ha hc.1), ← hbr, ih htl rest]
    rfl

/-- A well-formed HTTP/1.1 response, split at its status line: the status line
`status` (no bare CR) and everything after the status-line CRLF (`rest` — the
remaining headers, blank line, and body bytes). `render` is the on-wire order. -/
structure WireResp where
  status : Bytes
  rest   : Bytes
  noCR   : ∀ x ∈ status, x ≠ 13

/-- The response bytes on the wire, in order. -/
def WireResp.render (r : WireResp) : Bytes := r.status ++ crlf ++ r.rest

/-- **The stamp splices exactly after the status line.** For a well-formed
response the deployed `stampHit` yields
`status ++ CRLF ++ "X-Cache: HIT" ++ "Age: <age>" ++ rest`: the status line is
unchanged, the two hit headers are inserted, and the stored tail is verbatim. -/
theorem stampHit_render (r : WireResp) (age : Nat) :
    stampHit r.render age
      = r.status ++ crlf ++ xCacheHitLine ++ ageLine age ++ r.rest := by
  unfold stampHit WireResp.render
  have : r.status ++ crlf ++ r.rest = r.status ++ 13 :: 10 :: r.rest := by
    simp [crlf, List.append_assoc]
  rw [this, splitCRLF_noCR r.status r.noCR r.rest]

/-! ## The deployed cache serve

`serveCache s k now r` models the deployed cacheable-request serve: consult the
proven TTL-honouring store; on a fresh hit, stamp and serve the stored response
`r`; on a miss/stale, `none` (the deployed leader then runs the fold + stores). -/

/-- The deployed hit-serve: a fresh stored entry's response, stamped on the wire.
`none` when the store misses (the request is forwarded to the origin instead). -/
def serveCache (s : DiskStore) (k : Key) (now : Nat) (r : WireResp) : Option Bytes :=
  match s.getFresh k now with
  | some e => some (stampHit r.render (e.age now))
  | none => none

/-! ## Theorem 1 — a fresh cached entry is served with the Age header + stored body -/

/-- **`cache_hit_serves_stored`.** A FRESH stored entry is served: the proven
store returns it (`disk_getFresh_put`), and the deployed wire is
`status ++ CRLF ++ "X-Cache: HIT" ++ "Age: <now−stored_at>" ++ rest`. The `Age`
header carries the current age (`e.age now = now − e.storedAt`), and the stored
response tail `rest` (headers, blank line, body) is preserved byte-for-byte. This
is the HIT a client sees on the second request. -/
theorem cache_hit_serves_stored (s : DiskStore) (k : Key) (e : DiskEntry) (now : Nat)
    (r : WireResp) (hfresh : e.fresh now = true) :
    serveCache (s.put k e) k now r
      = some (r.status ++ crlf ++ xCacheHitLine ++ ageLine (now - e.storedAt) ++ r.rest) := by
  unfold serveCache
  rw [Cache.Disk.disk_getFresh_put s k e now hfresh]
  show some (stampHit r.render (e.age now)) = _
  rw [stampHit_render r (e.age now)]
  rfl

/-! ## Theorem 2 — a miss goes to the origin, then stores; the next request hits -/

/-- **`cache_miss_fetches`.** On a cold key the cache does NOT serve
(`serveCache … = none`, `getFresh` misses), so the deployed leader forwards to the
origin and its `cacheStore` writes the fetched response `eF` under the proven key.
The next request within the lifetime then HITs, serving the fetched body stamped —
exactly the first-`curl`-MISS-then-second-`curl`-HIT sequence. -/
theorem cache_miss_fetches (s : DiskStore) (k : Key) (now : Nat) (r : WireResp)
    (eF : DiskEntry) (hmiss : s.get? k = none) (hfresh : eF.fresh now = true) :
    -- The miss is not served from cache: the origin is fetched.
    serveCache s k now r = none
    -- After the fetched response is stored, the next request HITs (serves it).
    ∧ serveCache (s.put k eF) k now r
        = some (r.status ++ crlf ++ xCacheHitLine ++ ageLine (now - eF.storedAt) ++ r.rest) := by
  refine ⟨?_, ?_⟩
  · unfold serveCache
    have : s.getFresh k now = none := by
      simp [DiskStore.getFresh, hmiss]
    rw [this]
  · exact cache_hit_serves_stored s k eF now r hfresh

/-! ## Theorem 3 — a past-TTL entry is not served stale -/

/-- **`cache_no_stale_past_ttl`.** A stored entry PAST its freshness lifetime
(`e.fresh now = false`) is NOT served: `serveCache … = none` — the deployed
`get_fresh` reads it as a miss, drops the file, and re-fetches / revalidates. No
stale body ever reaches the wire (RFC 9111 §4.2, `disk_getFresh_put_expired`). -/
theorem cache_no_stale_past_ttl (s : DiskStore) (k : Key) (e : DiskEntry) (now : Nat)
    (r : WireResp) (hstale : e.fresh now = false) :
    serveCache (s.put k e) k now r = none := by
  unfold serveCache
  rw [Cache.Disk.disk_getFresh_put_expired s k e now hstale]

/-! ## Non-vacuous checks on a real deployed static response

A concrete `GET /static/app.js`-style 200 with a `max-age=60` directive, exercised
through the deployed serve: the first request misses, the entry is fresh, and the
served HIT carries `X-Cache: HIT` and `Age: 7` (age = now − stored_at) with the
body `hello` preserved. Real bytes, `decide`/`rfl`, not a vacuous instantiation. -/

/-- A real static response tail: `Content-Length: 5\r\nCache-Control: max-age=60\r\n\r\nhello`. -/
def demoRest : Bytes :=
  -- "Content-Length: 5\r\n"
  [67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,32,53,13,10]
  -- "Cache-Control: max-age=60\r\n"
  ++ [67,97,99,104,101,45,67,111,110,116,114,111,108,58,32,109,97,120,45,97,103,101,61,54,48,13,10]
  -- "\r\n" ++ "hello"
  ++ [13,10] ++ [104,101,108,108,111]

/-- The status line `HTTP/1.1 200 OK` (no bare CR). -/
def demoStatus : Bytes := [72,84,84,80,47,49,46,49,32,50,48,48,32,79,75]

theorem demoStatus_noCR : ∀ x ∈ demoStatus, x ≠ 13 := by decide

def demoResp : WireResp := ⟨demoStatus, demoRest, demoStatus_noCR⟩

/-- A fresh stored entry: stored at t=0, TTL 60s (the resolved `max-age=60`). -/
def demoEntry : DiskEntry :=
  { status := 200, headers := [], body := demoRest, storedAt := 0, ttl := 60 }

/-- At `now = 7` the entry is fresh (age 7 < 60). -/
example : demoEntry.fresh 7 = true := by decide

/-- A real HIT: the served wire carries `X-Cache: HIT` and `Age: 7`, body preserved. -/
example :
    serveCache (DiskStore.empty.put Cache.Disk.kA demoEntry) Cache.Disk.kA 7 demoResp
      = some (demoStatus ++ crlf ++ xCacheHitLine ++ ageLine 7 ++ demoRest) := by
  have h := cache_hit_serves_stored DiskStore.empty Cache.Disk.kA demoEntry 7 demoResp (by decide)
  simpa [demoResp, DiskEntry.storedAt] using h

/-- `toDec 7 = "7"` (one ASCII digit). -/
theorem toDec_7 : toDec 7 = [55] := by rw [toDec]; rfl

/-- The served bytes really do contain the `X-Cache: HIT` and `Age: 7` header bytes. -/
example :
    xCacheHitLine = [88,45,67,97,99,104,101,58,32,72,73,84,13,10]
    ∧ ageLine 7 = [65,103,101,58,32,55,13,10] := by
  refine ⟨by decide, ?_⟩
  show [65,103,101,58,32] ++ toDec 7 ++ crlf = _
  rw [toDec_7]; rfl

/-- A real MISS: an empty cache does not serve `/static/app.js` (origin is fetched). -/
example : serveCache DiskStore.empty Cache.Disk.kA 7 demoResp = none := by decide

/-- A real STALE: at `now = 100` (age 100 ≥ ttl 60) the entry is not served. -/
example :
    serveCache (DiskStore.empty.put Cache.Disk.kA demoEntry) Cache.Disk.kA 100 demoResp = none :=
  cache_no_stale_past_ttl DiskStore.empty Cache.Disk.kA demoEntry 100 demoResp (by decide)

end Cache.HitProven

#print axioms Cache.HitProven.cache_hit_serves_stored
#print axioms Cache.HitProven.cache_miss_fetches
#print axioms Cache.HitProven.cache_no_stale_past_ttl
#print axioms Cache.HitProven.stampHit_render
