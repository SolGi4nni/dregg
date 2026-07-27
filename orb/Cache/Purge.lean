import Cache

/-!
# Cache.Purge — tag-based cache purge / invalidation (surrogate-key eviction)

`Cache.lean` invalidates by *URI* (RFC 9111 §4.4): an unsafe method drops every
entry keyed at one target URI. That is too coarse for a content platform, where
one logical asset (a blog post, a product) is cached under *many* keys (URI ×
`Vary`, plus derived/rendered variants) and an origin edit must evict all of
them at once — but nothing else.

This module models **tag-based purge** (the "surrogate key" / "Cache-Tag"
discipline): every stored entry carries a set of opaque **tag ids**, and a purge
names a single tag `t` and must evict *exactly* the entries carrying `t` and
leave every entry without `t` untouched. The tags themselves are opaque `Nat`
ids — the untrusted shell is responsible for mapping a tag *string* to an id
(e.g. by an injective interning table, or a fingerprint whose collisions it
owns); the model reasons about the eviction *decision* over the ids, exactly,
with no hash in the trusted core.

Two purge flavours, both proven:

* **hard purge** (`TagStore.purge t`) — drop every entry carrying `t`.
  `purge_by_tag` (via `purge_mem_iff`) proves the swept store contains an entry
  iff it was present *and does not carry* `t`: `purge_removes_tagged` (no tagged
  entry survives) and `purge_keeps_untagged` (every untagged entry is kept —
  *none without the tag* is touched). `purge_idempotent` proves purging the same
  tag twice equals purging once.

* **soft purge** (`TagStore.softPurge t`) — mark every entry carrying `t`
  *stale* (rather than delete it), so it stays available for revalidation but is
  never served as-is. `purge_soft_no_serve_stale` proves a soft-purged entry is
  *not served* after the purge (`serve?` returns a miss), while
  `soft_purge_serves_untagged` proves an entry without `t` is served exactly as
  before — the purge is targeted, not global. `soft_purge_preserves_entry`
  witnesses the soft/hard distinction: the entry's bytes survive a soft purge
  (available to a revalidating fetch), it is only withheld from cache serving.

Freshness (`age = now − storedAt`, `fresh ↔ age < ttl`) matches the hot and cold
tiers verbatim (RFC 9111 §4.2), so "servable" folds the ordinary TTL check
together with the purge flag: `servable ↔ ¬stale ∧ fresh`.
-/

namespace Cache.Purge

open Cache (Key Body eqK eqK_refl eqK_true)

/-! ## Tags and tagged entries -/

/-- An opaque tag id. The shell interns a tag *string* to one of these; the
model reasons about the eviction decision over ids, exactly. -/
abbrev TagId := Nat

/-- A cache entry that carries a set of surrogate-key tags. `stale` is the
soft-purge marker: a soft purge sets it, and a stale entry is withheld from
cache serving while its bytes remain for revalidation. -/
structure TagEntry where
  key : Key
  body : Body
  tags : List TagId
  storedAt : Nat
  ttl : Nat
  stale : Bool := false
deriving Repr, DecidableEq

/-- Whether an entry carries a given tag (exact set membership). -/
def TagEntry.carries (e : TagEntry) (t : TagId) : Bool := decide (t ∈ e.tags)

theorem carries_iff (e : TagEntry) (t : TagId) : e.carries t = true ↔ t ∈ e.tags := by
  simp [TagEntry.carries]

/-- §4.2.3 `current_age = now − stored_at` (Nat subtraction clamps at 0). -/
def TagEntry.age (e : TagEntry) (now : Nat) : Nat := now - e.storedAt

/-- §4.2 `response_is_fresh = current_age < freshness_lifetime`. -/
def TagEntry.fresh (e : TagEntry) (now : Nat) : Bool := decide (e.age now < e.ttl)

/-- An entry is servable from cache iff it is not soft-purged *and* still fresh. -/
def TagEntry.servable (e : TagEntry) (now : Nat) : Bool := !e.stale && e.fresh now

/-- The soft-purge marking: withhold the entry from serving, keep its bytes. -/
def TagEntry.markStale (e : TagEntry) : TagEntry := { e with stale := true }

theorem markStale_key (e : TagEntry) : e.markStale.key = e.key := rfl

theorem markStale_carries (e : TagEntry) (t : TagId) :
    e.markStale.carries t = e.carries t := rfl

/-- A soft-purged entry is never servable — the mark forces a cache miss. -/
theorem markStale_not_servable (e : TagEntry) (now : Nat) :
    e.markStale.servable now = false := by
  simp [TagEntry.servable, TagEntry.markStale]

/-- Soft purge preserves the entry's response bytes and key (it is not deleted),
so a revalidating fetch still has the entry to conditionally refresh. -/
theorem markStale_preserves (e : TagEntry) :
    e.markStale.key = e.key ∧ e.markStale.body = e.body ∧ e.markStale.tags = e.tags := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## The tagged store -/

/-- The store: a list of tagged entries. -/
structure TagStore where
  entries : List TagEntry
deriving Repr, DecidableEq

/-- The empty store. -/
def TagStore.empty : TagStore := ⟨[]⟩

/-- §4.1 exact-key lookup (whatever the entry's freshness / purge state). -/
def TagStore.get? (s : TagStore) (k : Key) : Option TagEntry :=
  s.entries.find? (fun e => eqK e.key k)

/-- A serving lookup: return the entry only while it is servable (fresh *and*
not soft-purged). A stale or purged entry reads as a miss. -/
def TagStore.serve? (s : TagStore) (k : Key) (now : Nat) : Option TagEntry :=
  match s.get? k with
  | some e => if e.servable now then some e else none
  | none => none

/-! ## Hard purge: drop exactly the entries carrying the tag -/

/-- **Hard purge by tag.** Drop every entry carrying `t`; keep the rest. -/
def TagStore.purge (s : TagStore) (t : TagId) : TagStore :=
  ⟨s.entries.filter (fun e => !e.carries t)⟩

/-- **`purge_by_tag` (the exact characterization).** After a hard purge of `t`,
the store holds an entry iff it was present *and does not carry* `t`. -/
theorem purge_mem_iff (s : TagStore) (t : TagId) (e : TagEntry) :
    e ∈ (s.purge t).entries ↔ e ∈ s.entries ∧ e.carries t = false := by
  simp only [TagStore.purge, List.mem_filter]
  constructor
  · rintro ⟨hm, hp⟩; exact ⟨hm, by simpa using hp⟩
  · rintro ⟨hm, hc⟩; exact ⟨hm, by simp [hc]⟩

/-- **Every tagged entry is evicted** — no entry carrying `t` survives. -/
theorem purge_removes_tagged (s : TagStore) (t : TagId) (e : TagEntry)
    (hmem : e ∈ s.entries) (hc : e.carries t = true) :
    e ∉ (s.purge t).entries := by
  intro h
  have := ((purge_mem_iff s t e).mp h).2
  rw [hc] at this; simp at this

/-- **Every untagged entry is kept** — an entry *without* `t` is never touched. -/
theorem purge_keeps_untagged (s : TagStore) (t : TagId) (e : TagEntry)
    (hmem : e ∈ s.entries) (hc : e.carries t = false) :
    e ∈ (s.purge t).entries :=
  (purge_mem_iff s t e).mpr ⟨hmem, hc⟩

/-- The purge never invents entries — the swept store is a subset. -/
theorem purge_subset (s : TagStore) (t : TagId) :
    ∀ e ∈ (s.purge t).entries, e ∈ s.entries :=
  fun _ h => ((purge_mem_iff s t _).mp h).1

/-- **`purge_idempotent`.** Purging the same tag twice equals purging it once. -/
theorem purge_idempotent (s : TagStore) (t : TagId) :
    (s.purge t).purge t = s.purge t := by
  simp only [TagStore.purge, List.filter_filter, Bool.and_self]

/-! ## Soft purge: mark carriers stale, withheld from serving -/

/-- **Soft purge by tag.** Mark every entry carrying `t` stale; leave the rest. -/
def TagStore.softPurge (s : TagStore) (t : TagId) : TagStore :=
  ⟨s.entries.map (fun e => if e.carries t then e.markStale else e)⟩

/-- `find?` on a key commutes with a map that preserves each entry's key. -/
theorem find?_map_stale (l : List TagEntry) (t : TagId) (k : Key) :
    (l.map (fun e => if e.carries t then e.markStale else e)).find? (fun e => eqK e.key k)
      = (l.find? (fun e => eqK e.key k)).map (fun e => if e.carries t then e.markStale else e) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    have hkey : eqK (if a.carries t then a.markStale else a).key k = eqK a.key k := by
      by_cases h : a.carries t = true
      · rw [if_pos h]; rfl
      · rw [if_neg h]
    simp only [List.map_cons, List.find?_cons, hkey]
    cases eqK a.key k with
    | true => simp
    | false => simpa using ih

/-- A soft purge relocates each key's entry through the stale-marking map. -/
theorem get?_softPurge (s : TagStore) (t : TagId) (k : Key) :
    (s.softPurge t).get? k = (s.get? k).map (fun e => if e.carries t then e.markStale else e) := by
  simp only [TagStore.softPurge, TagStore.get?]
  exact find?_map_stale s.entries t k

/-- **`purge_soft_no_serve_stale`.** After a soft purge of `t`, an entry carrying
`t` is *not served* — the serving lookup returns a miss (it was marked stale). -/
theorem purge_soft_no_serve_stale (s : TagStore) (t : TagId) (k : Key) (now : Nat)
    (e : TagEntry) (hget : s.get? k = some e) (hc : e.carries t = true) :
    (s.softPurge t).serve? k now = none := by
  have h1 : (s.softPurge t).get? k = some e.markStale := by
    rw [get?_softPurge, hget]; simp [hc]
  simp only [TagStore.serve?, h1]
  simp [TagEntry.servable, TagEntry.markStale]

/-- **Targeted, not global.** After a soft purge of `t`, an entry *without* `t`
that is otherwise servable is served exactly as before — a neighbour's purge is
invisible to it. -/
theorem soft_purge_serves_untagged (s : TagStore) (t : TagId) (k : Key) (now : Nat)
    (e : TagEntry) (hget : s.get? k = some e) (hc : e.carries t = false)
    (hs : e.servable now = true) :
    (s.softPurge t).serve? k now = some e := by
  have h1 : (s.softPurge t).get? k = some e := by
    rw [get?_softPurge, hget]; simp [hc]
  simp only [TagStore.serve?, h1, hs, if_true]

/-- **Soft ≠ hard.** A soft-purged entry's bytes survive the purge — the entry is
still present (available for a revalidating fetch), it is only withheld from
serving. This is the whole point of *soft* purge over hard eviction. -/
theorem soft_purge_preserves_entry (s : TagStore) (t : TagId) (k : Key)
    (e : TagEntry) (hget : s.get? k = some e) (hc : e.carries t = true) :
    (s.softPurge t).get? k = some e.markStale ∧ e.markStale.body = e.body := by
  refine ⟨?_, rfl⟩
  rw [get?_softPurge, hget]; simp [hc]

/-! ## Non-vacuous truth table on real tags, keys, and entries

Three cached assets tagged as a real content platform would tag them: a home
page and a blog post both tagged `html` and `blog`; a cart page tagged `shop`.
A purge of `blog` must take the home page and the post and leave the cart page
completely alone — hard and soft — while the demos show the cart page still
served and (for soft purge) the blog entries withheld but not deleted. -/

def tHtml : TagId := 10
def tBlog : TagId := 20
def tShop : TagId := 30

def kHome : Key := { method := 71, uri := 100, vary := [] }
def kPost : Key := { method := 71, uri := 200, vary := [] }
def kCart : Key := { method := 71, uri := 300, vary := [] }

def eHome : TagEntry :=
  { key := kHome, body := { id := 1 }, tags := [tHtml, tBlog], storedAt := 0, ttl := 100 }
def ePost : TagEntry :=
  { key := kPost, body := { id := 2 }, tags := [tHtml, tBlog], storedAt := 0, ttl := 100 }
def eCart : TagEntry :=
  { key := kCart, body := { id := 3 }, tags := [tShop], storedAt := 0, ttl := 100 }

def demoStore : TagStore := ⟨[eHome, ePost, eCart]⟩

/-- The tag carriage is genuinely mixed: the home page carries `blog`, the cart
page does not (so the two purge branches are both exercised). -/
example : eHome.carries tBlog = true := by decide
example : eCart.carries tBlog = false := by decide

/-- **Hard purge of `blog` evicts exactly the two blog assets**, leaving the cart
page — `[eCart]` is precisely the untagged remainder. -/
example : (demoStore.purge tBlog).entries = [eCart] := by decide

/-- The two blog entries are gone; the cart entry survives (none without `blog`
was touched) — the general theorems, applied to real data. -/
example : eHome ∉ (demoStore.purge tBlog).entries :=
  purge_removes_tagged demoStore tBlog eHome (by decide) (by decide)
example : eCart ∈ (demoStore.purge tBlog).entries :=
  purge_keeps_untagged demoStore tBlog eCart (by decide) (by decide)

/-- Idempotence, concretely: a second purge of `blog` changes nothing. -/
example : (demoStore.purge tBlog).purge tBlog = demoStore.purge tBlog := by decide

/-- **Soft purge of `blog` withholds the home page from serving** (miss), by the
general theorem on real data. -/
example : (demoStore.softPurge tBlog).serve? kHome 5 = none :=
  purge_soft_no_serve_stale demoStore tBlog kHome 5 eHome (by decide) (by decide)

/-- …yet the home page's bytes survive the soft purge (it is only marked stale,
available to revalidate) — soft, not hard. -/
example : ((demoStore.softPurge tBlog).get? kHome).isSome = true := by decide

/-- **Isolation:** the cart page, untouched by the `blog` purge, is still served. -/
example : (demoStore.softPurge tBlog).serve? kCart 5 = some eCart :=
  soft_purge_serves_untagged demoStore tBlog kCart 5 eCart (by decide) (by decide) (by decide)

end Cache.Purge

#print axioms Cache.Purge.purge_mem_iff
#print axioms Cache.Purge.purge_removes_tagged
#print axioms Cache.Purge.purge_keeps_untagged
#print axioms Cache.Purge.purge_idempotent
#print axioms Cache.Purge.purge_soft_no_serve_stale
#print axioms Cache.Purge.soft_purge_serves_untagged
#print axioms Cache.Purge.soft_purge_preserves_entry
