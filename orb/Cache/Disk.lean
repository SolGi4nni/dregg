import Cache

/-!
# Cache.Disk — a proven content-addressable on-disk cache (the cold tier)

The `Cache` library (RFC 9111) models the *hot* in-memory tier: a bounded LRU
`Store` with freshness, coalescing, and revalidation. This module adds the
**cold tier**: a durable on-disk store keyed by the same `Cache.Key`, so a large
working set survives a restart of the hot tier.

The model is a pure transition system over an explicit clock (`now : Nat`
seconds), exactly as `Cache.lean` — time is data. A `DiskEntry` carries the
*actual* stored response (status, header bytes, body bytes) — unlike the hot
tier's opaque `Cache.Body` token, the cold tier holds the real bytes it must
reproduce byte-for-byte, because durable replay is its whole point.

## The key → path discipline (no-traversal, injective)

The disk location of a key is `pathOf : Cache.Key → List Nat` (a byte string).
Two properties are proven, both of which the untrusted disk shell must preserve:

* **injective** (`pathOf_injective`, `disk_key_injective`): distinct keys map to
  distinct paths — no two keys ever collide on one file, so a hit never serves
  another key's bytes. This is *strictly stronger than a hash*: a SHA-based
  filename is injective only modulo (unproven) collision resistance; here the
  path is a decodable encoding of the key, so injectivity is a theorem.
* **path-safe / no-traversal** (`pathOf_no_slash`, `pathOf_no_dot`): every byte
  of a path is drawn from the hex alphabet `[0-9a-f]` plus the field separator
  `-`, none of which is `'/'` (47) or `'.'` (46). So a path can contain no
  directory separator and no `..` component — it never escapes the cache
  directory, the same discipline the static-file handler enforces.

## The store operations and their theorems

* `put` / `get?` — `disk_get_put`: reading a key straight after writing it
  returns *the same* entry (round-trip faithfulness — the stored response bytes
  come back unchanged).
* `getFresh` — a lookup that honours the TTL: `disk_get_expired_none` proves an
  entry past its freshness lifetime is *not* served; `disk_getFresh_put` proves a
  fresh entry is.
* `evict` (the reaper sweep) — `evict_mem_iff` proves the swept store contains
  *exactly* the fresh entries: `disk_evict_removes_expired` (no expired entry
  survives) and `disk_evict_keeps_fresh` (every fresh entry is kept).

`freshness` matches the hot tier verbatim: `current_age = now − stored_at` and
`fresh ↔ current_age < ttl` (RFC 9111 §4.2 / §4.2.3), so the two tiers agree on
when an entry may be served.
-/

namespace Cache.Disk

open Cache (Key eqK eqK_refl)

/-! ## Stored entries and freshness (RFC 9111 §4.2) -/

/-- A durable cache entry: the actual response the shell must reproduce
byte-for-byte (status code, header name/value byte pairs, body bytes), the
store time, and the freshness lifetime (seconds) the origin's directive
resolved to. Unlike the hot tier's opaque `Cache.Body`, the bytes are real. -/
structure DiskEntry where
  status  : Nat
  headers : List (List Nat × List Nat)
  body    : List Nat
  storedAt : Nat
  ttl      : Nat
deriving Repr, DecidableEq

/-- §4.2.3 `current_age = now − stored_at` (Nat subtraction clamps at 0). -/
def DiskEntry.age (e : DiskEntry) (now : Nat) : Nat := now - e.storedAt

/-- §4.2 `response_is_fresh = current_age < freshness_lifetime`. -/
def DiskEntry.fresh (e : DiskEntry) (now : Nat) : Bool := decide (e.age now < e.ttl)

/-- An entry is *expired* iff it is not fresh (its TTL has elapsed). -/
def DiskEntry.expired (e : DiskEntry) (now : Nat) : Bool := !e.fresh now

/-! ## The on-disk store -/

/-- The cold-tier store: a key → entry mapping (association list, keys unique
after `put`). This models the whole sharded directory tree as one map; the disk
*layout* of a key is `pathOf` below. -/
structure DiskStore where
  entries : List (Key × DiskEntry)
deriving Repr

/-- The empty store a fresh cache directory presents. -/
def DiskStore.empty : DiskStore := ⟨[]⟩

/-- §4.1 exact-key lookup of a stored entry (whatever its freshness). -/
def DiskStore.get? (s : DiskStore) (k : Key) : Option DiskEntry :=
  (s.entries.find? (fun kv => eqK kv.1 k)).map (·.2)

/-- Write an entry: drop any prior entry for the key, prepend the new one
(atomic temp-file + rename on disk; here, replace-in-place). -/
def DiskStore.put (s : DiskStore) (k : Key) (e : DiskEntry) : DiskStore :=
  ⟨(k, e) :: s.entries.filter (fun kv => !eqK kv.1 k)⟩

/-- A TTL-honouring lookup: return the stored entry only while it is fresh
(RFC 9111 §4.2). A stale entry reads as a miss — the shell drops it. -/
def DiskStore.getFresh (s : DiskStore) (k : Key) (now : Nat) : Option DiskEntry :=
  match s.get? k with
  | some e => if e.fresh now then some e else none
  | none => none

/-- The reaper sweep: drop every entry whose TTL has elapsed, keep the fresh. -/
def DiskStore.evict (s : DiskStore) (now : Nat) : DiskStore :=
  ⟨s.entries.filter (fun kv => kv.2.fresh now)⟩

/-! ## The key → path mapping: an injective, traversal-safe encoding

The path of a key is a byte string over the hex alphabet `[0-9a-f]` plus a
field separator `-`. It is built from a *decodable* encoding of the key, so it
is injective; and every byte is a safe character, so it can contain neither a
directory separator `'/'` nor a `.` — no path component can be `..`. -/

/-- Lowercase-hex digit byte of a nibble (`0..15`): `0..9 → '0'..'9'`,
`10..15 → 'a'..'f'`. -/
def hexDigit (d : Nat) : Nat := if d < 10 then 48 + d else 87 + d

/-- The inverse of `hexDigit` on the two ASCII ranges it produces. -/
def unHex (b : Nat) : Nat := if b < 97 then b - 48 else b - 87

theorem unHex_hexDigit (d : Nat) (h : d < 16) : unHex (hexDigit d) = d := by
  unfold unHex hexDigit
  split <;> split <;> omega

/-- Every hex digit byte avoids the separator `-` (45), the dot `.` (46), and
the slash `/` (47) — it is `≥ 48`. -/
theorem hexDigit_safe (d : Nat) (h : d < 16) :
    hexDigit d ≠ 45 ∧ hexDigit d ≠ 46 ∧ hexDigit d ≠ 47 := by
  unfold hexDigit; split <;> omega

/-- Hex bytes of a Nat, most-significant-first, always nonempty (`0 → "0"`). -/
def toHex (n : Nat) : List Nat :=
  if n < 16 then [hexDigit n]
  else toHex (n / 16) ++ [hexDigit (n % 16)]
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

theorem toHex_nonempty (n : Nat) : toHex n ≠ [] := by
  rw [toHex]; split <;> simp

/-- Every byte of `toHex n` is `hexDigit d` for some nibble `d < 16`. -/
theorem toHex_mem_hex (n : Nat) : ∀ x ∈ toHex n, ∃ d, d < 16 ∧ x = hexDigit d := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [toHex]; split
    · rename_i h; intro x hx; simp only [List.mem_singleton] at hx; exact ⟨n, h, hx⟩
    · rename_i h
      intro x hx
      rw [List.mem_append] at hx
      cases hx with
      | inl hx => exact ih (n / 16) (Nat.div_lt_self (by omega) (by omega)) x hx
      | inr hx => simp only [List.mem_singleton] at hx; exact ⟨n % 16, Nat.mod_lt _ (by omega), hx⟩

/-- No byte of `toHex n` is the separator `-` (45). -/
theorem toHex_no_sep (n : Nat) : ∀ x ∈ toHex n, x ≠ 45 := by
  intro x hx; obtain ⟨d, hd, rfl⟩ := toHex_mem_hex n x hx; exact (hexDigit_safe d hd).1

/-- Left-inverse of hex rendering, folding MSB-first. -/
def ofHexAux (acc : Nat) : List Nat → Nat
  | [] => acc
  | b :: bs => ofHexAux (acc * 16 + unHex b) bs

def ofHex (bs : List Nat) : Nat := ofHexAux 0 bs

theorem ofHexAux_snoc (acc : Nat) (xs : List Nat) (b : Nat) :
    ofHexAux acc (xs ++ [b]) = ofHexAux acc xs * 16 + unHex b := by
  induction xs generalizing acc with
  | nil => simp [ofHexAux]
  | cons x xs ih => simp [ofHexAux, ih]

theorem ofHex_toHex (n : Nat) : ofHex (toHex n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [toHex]
    split
    · rename_i h
      simp [ofHex, ofHexAux, unHex_hexDigit n h]
    · rename_i h
      have hlt : n / 16 < n := Nat.div_lt_self (by omega) (by omega)
      have hrec : ofHex (toHex (n / 16)) = n / 16 := ih (n / 16) hlt
      simp only [ofHex] at hrec ⊢
      rw [ofHexAux_snoc, hrec, unHex_hexDigit _ (Nat.mod_lt _ (by omega))]
      omega

/-- Hex rendering is injective (it has a left inverse). -/
theorem toHex_injective {a b : Nat} (h : toHex a = toHex b) : a = b := by
  have := congrArg ofHex h
  rwa [ofHex_toHex, ofHex_toHex] at this

/-! ### The unique-split lemma for the separator -/

/-- If two `sep`-delimited concatenations agree and neither prefix contains
`sep`, the prefixes and the suffixes agree. (The first `sep` splits uniquely.) -/
theorem split_sep_unique {sep : Nat} :
    ∀ {l1 l2 r1 r2 : List Nat}, l1 ++ sep :: r1 = l2 ++ sep :: r2 →
      (∀ x ∈ l1, x ≠ sep) → (∀ x ∈ l2, x ≠ sep) → l1 = l2 ∧ r1 = r2 := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 r1 r2 h _ h2
    cases l2 with
    | nil => simp only [List.nil_append, List.cons.injEq] at h; exact ⟨rfl, h.2⟩
    | cons b bs =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.1.symm (h2 b (by simp))
  | cons a as ih =>
    intro l2 r1 r2 h h1 h2
    cases l2 with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.1 (h1 a (by simp))
    | cons b bs =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨hab, htl⟩ := h
      have hl1 : ∀ x ∈ as, x ≠ sep := fun x hx => h1 x (by simp [hx])
      have hl2 : ∀ x ∈ bs, x ≠ sep := fun x hx => h2 x (by simp [hx])
      obtain ⟨hAs, hR⟩ := ih htl hl1 hl2
      exact ⟨by rw [hab, hAs], hR⟩

/-! ### The token rendering and its injectivity -/

/-- Render a list of Nats to bytes: each as a hex field terminated by `-`. -/
def render : List Nat → List Nat
  | [] => []
  | n :: ns => toHex n ++ 45 :: render ns

theorem render_cons_ne_nil (n : Nat) (ns : List Nat) : render (n :: ns) ≠ [] := by
  have : (45 : Nat) ∈ render (n :: ns) := by
    simp only [render]; exact List.mem_append_right _ (List.mem_cons_self)
  intro h; rw [h] at this; exact absurd this (by simp)

theorem render_injective : ∀ (a b : List Nat), render a = render b → a = b := by
  intro a
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => rfl
    | cons y ys => exact absurd h.symm (render_cons_ne_nil y ys)
  | cons x xs ih =>
    intro b h
    cases b with
    | nil => exact absurd h (render_cons_ne_nil x xs)
    | cons y ys =>
      simp only [render] at h
      obtain ⟨hxy, htl⟩ := split_sep_unique h (toHex_no_sep x) (toHex_no_sep y)
      rw [toHex_injective hxy, ih ys htl]

/-- Every byte of `render ts` is either the separator `-` (45) or a hex digit. -/
theorem render_mem (ts : List Nat) :
    ∀ x ∈ render ts, x = 45 ∨ ∃ d, d < 16 ∧ x = hexDigit d := by
  induction ts with
  | nil => intro x hx; simp only [render, List.not_mem_nil] at hx
  | cons t ts ih =>
    intro x hx
    simp only [render, List.mem_append, List.mem_cons] at hx
    rcases hx with hx | hx | hx
    · exact Or.inr (toHex_mem_hex t x hx)
    · exact Or.inl hx
    · exact ih x hx

/-! ### The key → path map -/

/-- The token stream of a key: method, uri, then the vary values. Injective
because the whole `vary` list is the tail. -/
def keyTokens (k : Key) : List Nat := k.method :: k.uri :: k.vary

theorem keyTokens_injective {a b : Key} (h : keyTokens a = keyTokens b) : a = b := by
  obtain ⟨am, au, av⟩ := a
  obtain ⟨bm, bu, bv⟩ := b
  simp only [keyTokens, List.cons.injEq] at h
  obtain ⟨hm, hu, hv⟩ := h
  simp [hm, hu, hv]

/-- **The on-disk path of a cache key.** The injective, traversal-safe byte
string under which the key's entry is stored (the shell shards it by a prefix). -/
def pathOf (k : Key) : List Nat := render (keyTokens k)

/-- **Distinct keys map to distinct paths** — no two keys ever collide on disk. -/
theorem pathOf_injective {a b : Key} (h : pathOf a = pathOf b) : a = b :=
  keyTokens_injective (render_injective _ _ h)

theorem disk_key_injective {k1 k2 : Key} (h : pathOf k1 = pathOf k2) : k1 = k2 :=
  pathOf_injective h

theorem disk_path_distinct {k1 k2 : Key} (h : k1 ≠ k2) : pathOf k1 ≠ pathOf k2 :=
  fun heq => h (pathOf_injective heq)

/-- **No-traversal, part 1: a path contains no directory separator `'/'`.** -/
theorem pathOf_no_slash (k : Key) : ∀ x ∈ pathOf k, x ≠ 47 := by
  intro x hx
  rcases render_mem (keyTokens k) x hx with h | ⟨d, hd, rfl⟩
  · omega
  · exact (hexDigit_safe d hd).2.2

/-- **No-traversal, part 2: a path contains no `.` — so no `..` component.** -/
theorem pathOf_no_dot (k : Key) : ∀ x ∈ pathOf k, x ≠ 46 := by
  intro x hx
  rcases render_mem (keyTokens k) x hx with h | ⟨d, hd, rfl⟩
  · omega
  · exact (hexDigit_safe d hd).2.1

/-! ## Store round-trip, TTL, and eviction theorems -/

/-- **Round-trip faithfulness.** Reading a key straight after writing it returns
*the same* entry — the stored status/headers/body come back byte-for-byte. -/
theorem disk_get_put (s : DiskStore) (k : Key) (e : DiskEntry) :
    (s.put k e).get? k = some e := by
  simp [DiskStore.put, DiskStore.get?, List.find?_cons, eqK_refl]

/-- The round-trip preserves the body bytes exactly. -/
theorem disk_get_put_body (s : DiskStore) (k : Key) (e : DiskEntry) :
    ((s.put k e).get? k).map (·.body) = some e.body := by
  rw [disk_get_put]; rfl

/-- **A fresh entry, once written, is served.** -/
theorem disk_getFresh_put (s : DiskStore) (k : Key) (e : DiskEntry) (now : Nat)
    (h : e.fresh now = true) :
    (s.put k e).getFresh k now = some e := by
  simp [DiskStore.getFresh, disk_get_put, h]

/-- **An entry past its TTL is not returned.** A stored-but-stale entry reads as
a miss under the TTL-honouring lookup (RFC 9111 §4.2). -/
theorem disk_get_expired_none (s : DiskStore) (k : Key) (e : DiskEntry) (now : Nat)
    (hget : s.get? k = some e) (hexp : e.fresh now = false) :
    s.getFresh k now = none := by
  simp [DiskStore.getFresh, hget, hexp]

/-- Writing an already-expired entry never makes it servable. -/
theorem disk_getFresh_put_expired (s : DiskStore) (k : Key) (e : DiskEntry) (now : Nat)
    (h : e.fresh now = false) :
    (s.put k e).getFresh k now = none :=
  disk_get_expired_none _ k e now (disk_get_put s k e) h

/-- **The reaper keeps exactly the fresh entries.** After a sweep, an entry is
present iff it was present before AND is fresh. -/
theorem evict_mem_iff (s : DiskStore) (now : Nat) (kv : Key × DiskEntry) :
    kv ∈ (s.evict now).entries ↔ kv ∈ s.entries ∧ kv.2.fresh now = true := by
  simp [DiskStore.evict, List.mem_filter]

/-- **The reaper drops exactly the expired entries** — no expired entry survives
the sweep. -/
theorem disk_evict_removes_expired (s : DiskStore) (now : Nat) :
    ∀ kv ∈ (s.evict now).entries, kv.2.fresh now = true :=
  fun _ h => ((evict_mem_iff s now _).mp h).2

/-- **The reaper keeps every fresh entry** — a still-fresh entry survives. -/
theorem disk_evict_keeps_fresh (s : DiskStore) (now : Nat) :
    ∀ kv ∈ s.entries, kv.2.fresh now = true → kv ∈ (s.evict now).entries :=
  fun _ hmem hfresh => (evict_mem_iff s now _).mpr ⟨hmem, hfresh⟩

/-- The reaper never invents entries — the swept store is a sublist by
membership of the original. -/
theorem disk_evict_subset (s : DiskStore) (now : Nat) :
    ∀ kv ∈ (s.evict now).entries, kv ∈ s.entries :=
  fun _ h => ((evict_mem_iff s now _).mp h).1

/-! ## Non-vacuous truth-table checks on real keys and entries

Concrete keys, entries, and clocks that exercise each theorem with real data
(not a vacuous instantiation): distinct paths, a fresh round-trip, an expired
miss, and an eviction that keeps one entry and drops another. -/

/-- Two genuinely distinct keys (a `GET /a` and a `GET /b`, say). -/
def kA : Key := { method := 71, uri := 100, vary := [] }
def kB : Key := { method := 71, uri := 200, vary := [] }

/-- A fresh entry (lifetime 100s, stored at t=0) and an already-stale one
(lifetime 10s, stored at t=0). -/
def eFresh : DiskEntry :=
  { status := 200, headers := [([120], [121])], body := [104, 105], storedAt := 0, ttl := 100 }
def eStale : DiskEntry :=
  { status := 200, headers := [], body := [122], storedAt := 0, ttl := 10 }

/-- Distinct keys really do get distinct paths (non-vacuous injectivity). -/
example : pathOf kA ≠ pathOf kB := disk_path_distinct (by decide)

/-- At `now = 5` the fresh entry is fresh; at `now = 50` the stale one is not. -/
example : eFresh.fresh 5 = true := by decide
example : eStale.fresh 50 = false := by decide

/-- A real round-trip: write `eFresh` under `kA`, read it back byte-identical. -/
example : (DiskStore.empty.put kA eFresh).getFresh kA 5 = some eFresh :=
  disk_getFresh_put _ kA eFresh 5 (by decide)

/-- A real expiry: the stale entry, once its TTL elapsed, is not served. -/
example : (DiskStore.empty.put kB eStale).getFresh kB 50 = none :=
  disk_getFresh_put_expired _ kB eStale 50 (by decide)

/-- A real reaper sweep at `now = 50`: `kA`'s fresh entry survives, `kB`'s stale
entry is dropped. -/
example :
    let s : DiskStore := ⟨[(kA, eFresh), (kB, eStale)]⟩
    (kA, eFresh) ∈ (s.evict 50).entries ∧ (kB, eStale) ∉ (s.evict 50).entries := by
  refine ⟨?_, ?_⟩
  · exact disk_evict_keeps_fresh _ 50 (kA, eFresh) (by simp) (by decide)
  · intro h; exact absurd (disk_evict_removes_expired _ 50 (kB, eStale) h) (by decide)

end Cache.Disk

#print axioms Cache.Disk.disk_get_put
#print axioms Cache.Disk.disk_getFresh_put
#print axioms Cache.Disk.disk_get_expired_none
#print axioms Cache.Disk.disk_evict_removes_expired
#print axioms Cache.Disk.disk_evict_keeps_fresh
#print axioms Cache.Disk.pathOf_injective
#print axioms Cache.Disk.disk_key_injective
#print axioms Cache.Disk.pathOf_no_slash
#print axioms Cache.Disk.pathOf_no_dot
