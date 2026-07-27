import Cache.Disk
import Reactor.ServeStream

/-!
# Cache.Tee — a verified streaming tee-into-cache (cache while streaming to client)

When a cacheable response streams from an origin (or from a local body source),
the reactor must do two things at once: forward the bytes to the client *now*
(no buffer-the-whole-body latency), and populate the cache so the next request
hits. The naive way — append each chunk directly into the live cache entry — is
a correctness hazard: if the stream aborts halfway, a *partial* (poisoned) entry
is left behind, and a later reader serves a truncated body as if it were whole.

The discipline this module models and proves is the **temp-file + atomic rename**
one the cold-tier store (`Cache.Disk`) already documents: the in-flight bytes
accumulate in a *staging* buffer (a `.tmp` file) that is invisible to readers;
only when the stream completes are they atomically installed into the committed
store as one `DiskStore.put` (the rename). An aborted stream simply drops the
staging buffer — the committed store is never touched, so no partial entry can
be observed.

The fork itself is a **write-through tee**: every body chunk is written to the
client sink and to the staging buffer as *the same bytes* (`Tee.mirrored` is an
invariant, not an assumption). So the bytes the client receives and the bytes
that land in the cache are identical by construction.

## What is proven

* `tee_stores_while_streaming` — running the tee over the whole chunked body then
  committing yields (a) a client stream equal to the whole body and (b) a cached
  entry whose body equals, byte-for-byte, what the client received.
* `tee_abort_no_partial` — feeding any prefix of chunks then aborting leaves the
  committed store *byte-for-byte unchanged*; in particular a key absent before the
  stream is still absent, so no partial/poisoned entry is ever observable.
* `tee_vs_naive_abort` — the non-vacuous witness: the forbidden direct-write shell
  (append-in-place) DOES leave a partial entry on abort, while the verified tee
  does not. This is the mutant that violates the contract.
* `tee_stores_streamed_source` — the composition with the real streaming emit
  (`Reactor.ServeStream.srcChunks`): teeing the actual paced body chunks of a
  body SOURCE (inline / static-file window / proxied upstream), whatever the chunk
  size, caches exactly the source's whole body.

Bytes are modelled as `List Nat` — the on-disk numeric representation the
`Cache.Disk` store natively uses (its `DiskEntry.body : List Nat`). The bridge to
the wire-level `List UInt8` streaming emit is the injective `·.toNat` image.
-/

namespace Cache.Tee

open Cache (Key eqK eqK_refl)
open Cache.Disk (DiskStore DiskEntry)

/-- A byte string in the on-disk numeric representation (`Cache.Disk`'s own). -/
abbrev Bytes := List Nat

/-! ## The write-through tee (one read, two identical writes) -/

/-- The in-flight tee. `toClient` — the bytes forked to the client socket;
`staged` — the bytes appended to the temp staging file (still uncommitted, and
invisible to cache readers until the atomic rename). -/
structure Tee where
  toClient : Bytes := []
  staged   : Bytes := []
deriving Repr, DecidableEq

/-- The empty tee at the start of a stream. -/
def Tee.empty : Tee := {}

/-- Fork one body chunk: the SAME bytes are written to the client and to the
temp staging file. This is the write-through fork — it cannot write different
bytes to the two sinks. -/
def Tee.chunk (t : Tee) (bs : Bytes) : Tee :=
  { toClient := t.toClient ++ bs, staged := t.staged ++ bs }

/-- The mirror invariant: the client bytes equal the staged bytes. Because the
fork appends the same chunk to both, this holds throughout a stream — it is a
theorem (`run_mirrored`), not an assumption. -/
def Tee.mirrored (t : Tee) : Prop := t.toClient = t.staged

theorem empty_mirrored : Tee.empty.mirrored := rfl

theorem chunk_mirrored {t : Tee} (h : t.mirrored) (bs : Bytes) :
    (t.chunk bs).mirrored := by
  unfold Tee.mirrored Tee.chunk at *
  simp only []
  rw [h]

/-- Fork a whole sequence of chunks (the paced body), left to right. -/
def Tee.run (chunks : List Bytes) : Tee :=
  chunks.foldl (fun t c => t.chunk c) Tee.empty

/-- The client sink of a fold accumulates the seed's client bytes then the flat
concatenation of every chunk — no byte is dropped or reordered at a boundary. -/
theorem foldl_toClient (t0 : Tee) (chunks : List Bytes) :
    (chunks.foldl (fun t c => t.chunk c) t0).toClient
      = t0.toClient ++ chunks.flatten := by
  induction chunks generalizing t0 with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, ih]
    simp [Tee.chunk, List.flatten_cons, List.append_assoc]

/-- The staging buffer of a fold accumulates identically (same append). -/
theorem foldl_staged (t0 : Tee) (chunks : List Bytes) :
    (chunks.foldl (fun t c => t.chunk c) t0).staged
      = t0.staged ++ chunks.flatten := by
  induction chunks generalizing t0 with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, ih]
    simp [Tee.chunk, List.flatten_cons, List.append_assoc]

/-- **The client received the whole body.** -/
theorem run_toClient (chunks : List Bytes) :
    (Tee.run chunks).toClient = chunks.flatten := by
  rw [Tee.run, foldl_toClient]; simp [Tee.empty]

/-- **The staging buffer holds the whole body.** -/
theorem run_staged (chunks : List Bytes) :
    (Tee.run chunks).staged = chunks.flatten := by
  rw [Tee.run, foldl_staged]; simp [Tee.empty]

/-- **The mirror invariant holds after any stream** — client bytes = staged bytes. -/
theorem run_mirrored (chunks : List Bytes) : (Tee.run chunks).mirrored := by
  unfold Tee.mirrored; rw [run_toClient, run_staged]

/-! ## The session: committed store + the in-flight temp file -/

/-- The disk shell's state during a streaming tee: the committed cache the
readers see, the key being populated, and the in-flight temp file (`temp`). -/
structure Session where
  store : DiskStore
  key   : Key
  temp  : Tee

/-- Feed one chunk: it is teed to the client and the temp file; the COMMITTED
store is untouched (the temp file is not yet renamed, so no reader can see it). -/
def Session.feed (sess : Session) (bs : Bytes) : Session :=
  { sess with temp := sess.temp.chunk bs }

/-- Feed a whole sequence of chunks — the committed store stays untouched. -/
def Session.feedAll (sess : Session) (chunks : List Bytes) : Session :=
  { sess with temp := chunks.foldl (fun t c => t.chunk c) sess.temp }

/-- **COMMIT** (end-of-stream success): atomically install the staged bytes into
the committed store as one entry — the temp-file → cache rename, a single
`DiskStore.put`. -/
def Session.commit (sess : Session) (status ttl storedAt : Nat)
    (headers : List (Bytes × Bytes)) : DiskStore :=
  sess.store.put sess.key
    { status := status, headers := headers, body := sess.temp.staged,
      storedAt := storedAt, ttl := ttl }

/-- **ABORT**: drop the temp file; the committed store is returned untouched (the
rename never happens). -/
def Session.abort (sess : Session) : DiskStore := sess.store

/-! ## Headline theorem 1 — the tee stores exactly what it streams -/

/-- **The tee writes the response to the cache AND to the client, and the cached
bytes equal the streamed bytes.** Running the write-through tee over the whole
chunked body and committing yields: (a) the client stream is the whole body; and
(b) the committed cache entry's body equals, byte-for-byte, what the client
received (and hence the whole streamed body). Composes the real `Cache.Disk`
store round-trip (`disk_get_put`). -/
theorem tee_stores_while_streaming
    (s : DiskStore) (k : Key) (chunks : List Bytes)
    (status ttl storedAt : Nat) (headers : List (Bytes × Bytes)) :
    let sess : Session := { store := s, key := k, temp := Tee.run chunks }
    let s' := sess.commit status ttl storedAt headers
    -- (a) the client received the whole body
    sess.temp.toClient = chunks.flatten
    -- (b) the cached body equals the streamed (client) bytes
    ∧ ((s'.get? k).map DiskEntry.body) = some sess.temp.toClient
    -- (c) and that is exactly the whole streamed body
    ∧ ((s'.get? k).map DiskEntry.body) = some chunks.flatten := by
  refine ⟨run_toClient chunks, ?_, ?_⟩
  · rw [Session.commit, Cache.Disk.disk_get_put]
    show some (Tee.run chunks).staged = some (Tee.run chunks).toClient
    rw [run_staged, run_toClient]
  · rw [Session.commit, Cache.Disk.disk_get_put]
    show some (Tee.run chunks).staged = some chunks.flatten
    rw [run_staged]

/-! ## Headline theorem 2 — an aborted stream leaves no partial entry -/

/-- **An aborted stream does not leave a partial/poisoned cache entry.** Feeding
any prefix of chunks then aborting leaves the committed store byte-for-byte
unchanged; in particular, a key absent before the stream is still absent after
the abort — no reader can ever observe a truncated body. -/
theorem tee_abort_no_partial
    (s : DiskStore) (k : Key) (chunks : List Bytes)
    (hpre : s.get? k = none) :
    let sess' : Session := Session.feedAll { store := s, key := k, temp := Tee.empty } chunks
    -- feeding never touches the committed store
    sess'.store = s
    -- the committed store is byte-for-byte unchanged by the abort
    ∧ sess'.abort = s
    -- so after streaming any prefix, the aborted key has NO entry
    ∧ (sess'.abort).get? k = none := by
  refine ⟨rfl, rfl, ?_⟩
  show s.get? k = none
  exact hpre

/-! ## Non-vacuous witness: the mutant the contract forbids -/

/-- The MUTANT the temp-file discipline forbids: a shell that writes each chunk
DIRECTLY into the committed store (append-in-place) rather than into a temp file.
On abort it leaves whatever partial body it had written. -/
def naiveFeed (s : DiskStore) (k : Key) (body : Bytes) : DiskStore :=
  s.put k { status := 200, headers := [], body := body, storedAt := 0, ttl := 100 }

/-- **The mutant contrast (non-vacuity).** After streaming a non-empty body and
then ABORTING: the verified tee leaves NO cache entry (`get? = none`), while the
forbidden direct-write shell leaves a PARTIAL entry (`get? ≠ none`) — the exact
poisoning the temp-file + atomic-rename discipline prevents. This proves the
`tee_abort_no_partial` contract is real, not vacuous: a natural implementation
violates it. -/
theorem tee_vs_naive_abort
    (s : DiskStore) (k : Key) (part : Bytes)
    (hpre : s.get? k = none) :
    -- verified tee: aborted → no entry
    (Session.abort { store := s, key := k, temp := Tee.run [part] }).get? k = none
    -- forbidden direct-write: aborted → a partial entry survives
    ∧ (naiveFeed s k part).get? k ≠ none := by
  refine ⟨hpre, ?_⟩
  rw [naiveFeed, Cache.Disk.disk_get_put]
  exact Option.some_ne_none _

/-! ## Composition with the real streaming emit (`Reactor.ServeStream`)

The chunks the tee forks are not arbitrary — they are the paced body chunks the
streaming serve emits (`Reactor.ServeStream.srcChunks`), whose flatten is proven
to be the source's whole body (`srcChunks_flatten`), whatever the chunk size. The
streaming emit works over wire bytes (`List UInt8`); the cache stores their
numeric image (`List Nat`). The bridge is the injective `·.toNat`. -/

open Reactor.ServeStream (BodySrc bodyBytes srcChunks srcChunks_flatten ServeConfig)

/-- The on-disk numeric image of a chunk list from the (wire-level) streaming
emit — each `List UInt8` chunk mapped byte-wise to `List Nat`. -/
def numChunks (chunks : List (List UInt8)) : List Bytes :=
  chunks.map (fun c => c.map (·.toNat))

/-- The numeric image of a chunk list flattens to the numeric image of the flat
body — mapping and flattening commute, so no boundary is disturbed. -/
theorem numChunks_flatten (chunks : List (List UInt8)) :
    (numChunks chunks).flatten = chunks.flatten.map (·.toNat) := by
  unfold numChunks
  rw [← List.map_flatten]

/-- **The tee caches exactly the streamed source body.** Teeing the REAL paced
body chunks of a body SOURCE (`Reactor.ServeStream.srcChunks` — an inline body, a
static-file window, or a proxied upstream), whatever the chunk size `cfg.chunk`,
and committing, stores a cache entry whose body is exactly the numeric image of
the source's whole body. So streaming-while-caching a chunked body loses nothing:
the cache holds the same bytes the client received. Composes the streaming emit's
`srcChunks_flatten` with the store round-trip. -/
theorem tee_stores_streamed_source
    (s : DiskStore) (k : Key) (cfg : ServeConfig) (src : BodySrc)
    (status ttl storedAt : Nat) (headers : List (Bytes × Bytes)) :
    let chunks := numChunks (srcChunks cfg src)
    let sess : Session := { store := s, key := k, temp := Tee.run chunks }
    ((sess.commit status ttl storedAt headers).get? k).map DiskEntry.body
      = some ((bodyBytes src).map (·.toNat)) := by
  show ((DiskStore.put s k _).get? k).map DiskEntry.body = _
  rw [Cache.Disk.disk_get_put]
  show some (Tee.run (numChunks (srcChunks cfg src))).staged = _
  rw [run_staged, numChunks_flatten, srcChunks_flatten]

/-! ## Runnable checks -/

/-- A concrete stream: three chunks `[1,2] [3] [4,5,6]` into an empty cache under
a real key. The client gets `[1,2,3,4,5,6]` and the cache holds the same bytes. -/
def demoKey : Key := { method := 71, uri := 100, vary := [] }
def demoChunks : List Bytes := [[1, 2], [3], [4, 5, 6]]

example : (Tee.run demoChunks).toClient = [1, 2, 3, 4, 5, 6] := by decide
example :
    ((Session.commit { store := DiskStore.empty, key := demoKey, temp := Tee.run demoChunks }
        200 100 0 []).get? demoKey).map DiskEntry.body = some [1, 2, 3, 4, 5, 6] :=
  (tee_stores_while_streaming DiskStore.empty demoKey demoChunks 200 100 0 []).2.2

-- A real abort: stream two chunks then abort; the empty cache stays empty.
example :
    (Session.abort (Session.feedAll
      { store := DiskStore.empty, key := demoKey, temp := Tee.empty } [[9], [8, 7]])).get? demoKey
      = none :=
  (tee_abort_no_partial DiskStore.empty demoKey [[9], [8, 7]] rfl).2.2

#print axioms tee_stores_while_streaming
#print axioms tee_abort_no_partial
#print axioms tee_vs_naive_abort
#print axioms tee_stores_streamed_source

end Cache.Tee
