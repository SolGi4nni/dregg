import Cache.Disk
import Reactor.ServeStream

/-!
# Cache.StreamTee — a verified streaming tee-into-cache, client-first

When a cacheable response streams from an upstream (or from a local body source),
the reactor forks each body chunk two ways at once: it forwards the bytes to the
client *now* (no buffer-the-whole-body latency), and it appends the same bytes to
a *staging* buffer that will populate the cache. Two hazards make this subtle, and
this module models the engine's discipline for both, then proves it:

* **client-first, cache-best-effort.** The client's delivery must not be held
  hostage to the cache. Whether the cache commit *succeeds* (the atomic rename
  lands), *fails* (a disk error / ENOSPC / a full-store eviction drops it), or the
  stream is *aborted* — the client receives the whole body all the same. The cache
  is a side effect of streaming, never a gate on it.
* **no partial entry.** The staging bytes accumulate in a temp file that is
  invisible to readers; the committed store is touched only by the final atomic
  rename (one `Cache.Disk.DiskStore.put`). An aborted or failed stream simply drops
  the temp file — the committed store is never mutated, so no reader can ever
  observe a truncated body.

This mirrors the deployed engine's cold-tier write path exactly: bytes are written
to a `.tmp` sibling then `rename`d into place ("this prevents partial reads on
crash"), and in-flight `.tmp` files are skipped by every reader and reaper. The
on-disk path is a content address of the *key*; `Cache.Disk` already abstracts that
addressing as an injective, traversal-safe encoding (a theorem strictly stronger
than a hash's collision-resistance), so no cryptographic oracle is load-bearing
here — the tee's correctness is the streaming fork plus the rename atomicity, and
this module keeps it crypto-free.

## What is proven

* `tee_client_gets_full` — the client receives the whole streamed body, and the
  bytes it receives are **identical across every cache outcome**: commit success,
  commit failure, and abort all deliver the same full body. The cache result never
  perturbs the client stream.
* `tee_cache_exact` — after a successful commit, the cached entry's body equals the
  streamed body **byte-for-byte**, and equals exactly what the client received.
* `tee_abort_no_partial` — a client abort mid-stream (after any prefix of chunks)
  leaves the committed store byte-for-byte unchanged; a key absent before the
  stream is still absent — no partial/poisoned entry is observable. A *failed*
  commit (rename never lands) is proved to leave the store untouched too.
* `tee_vs_naive_abort` — the non-vacuous witness: the forbidden append-in-place
  shell DOES leave a partial entry on abort, while the tee does not.
* `tee_streamed_source_client_and_cache` — the composition with the real streaming
  emit (`Reactor.ServeStream.srcChunks`): teeing the actual paced body chunks of a
  body SOURCE (inline / static-file window / proxied upstream), whatever the chunk
  size, delivers the source's whole body to the client and (on success) caches
  exactly those bytes.

Bytes are `List Nat` — the on-disk numeric representation `Cache.Disk` natively
uses (`DiskEntry.body : List Nat`). The bridge to the wire-level `List UInt8`
streaming emit is the injective `·.toNat` image.
-/

namespace Cache.StreamTee

open Cache (Key eqK eqK_refl)
open Cache.Disk (DiskStore DiskEntry)

/-- A byte string in the on-disk numeric representation (`Cache.Disk`'s own). -/
abbrev Bytes := List Nat

/-! ## The write-through fork (one read, two identical writes) -/

/-- The in-flight fork. `client` — the bytes forwarded to the client socket;
`staged` — the bytes appended to the temp staging file (uncommitted, invisible to
cache readers until the atomic rename). -/
structure Fork where
  client : Bytes := []
  staged : Bytes := []
deriving Repr, DecidableEq

/-- The empty fork at the start of a stream. -/
def Fork.empty : Fork := {}

/-- Fork one body chunk: the SAME bytes are written to the client and to the temp
staging file. This is the write-through fork — it cannot write different bytes to
the two sinks. -/
def Fork.chunk (f : Fork) (bs : Bytes) : Fork :=
  { client := f.client ++ bs, staged := f.staged ++ bs }

/-- The mirror invariant: the client bytes equal the staged bytes. -/
def Fork.mirrored (f : Fork) : Prop := f.client = f.staged

theorem chunk_mirrored {f : Fork} (h : f.mirrored) (bs : Bytes) :
    (f.chunk bs).mirrored := by
  unfold Fork.mirrored Fork.chunk at *; simp only []; rw [h]

/-- Fork a whole sequence of chunks (the paced body), left to right. -/
def Fork.run (chunks : List Bytes) : Fork :=
  chunks.foldl (fun f c => f.chunk c) Fork.empty

/-- The client sink of a fold accumulates the seed's client bytes then the flat
concatenation of every chunk — nothing dropped or reordered at a boundary. -/
theorem foldl_client (f0 : Fork) (chunks : List Bytes) :
    (chunks.foldl (fun f c => f.chunk c) f0).client
      = f0.client ++ chunks.flatten := by
  induction chunks generalizing f0 with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, ih]
    simp [Fork.chunk, List.flatten_cons, List.append_assoc]

/-- The staging buffer of a fold accumulates identically (same append). -/
theorem foldl_staged (f0 : Fork) (chunks : List Bytes) :
    (chunks.foldl (fun f c => f.chunk c) f0).staged
      = f0.staged ++ chunks.flatten := by
  induction chunks generalizing f0 with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, ih]
    simp [Fork.chunk, List.flatten_cons, List.append_assoc]

/-- **The client received the whole body.** -/
theorem run_client (chunks : List Bytes) :
    (Fork.run chunks).client = chunks.flatten := by
  rw [Fork.run, foldl_client]; simp [Fork.empty]

/-- **The staging buffer holds the whole body.** -/
theorem run_staged (chunks : List Bytes) :
    (Fork.run chunks).staged = chunks.flatten := by
  rw [Fork.run, foldl_staged]; simp [Fork.empty]

/-- **The mirror invariant holds after any stream** — client bytes = staged bytes. -/
theorem run_mirrored (chunks : List Bytes) : (Fork.run chunks).mirrored := by
  unfold Fork.mirrored; rw [run_client, run_staged]

/-! ## The session: committed store + the in-flight temp file -/

/-- The disk shell's state during a streaming tee: the committed cache the readers
see, the key being populated, and the in-flight temp file (`fork`). -/
structure Session where
  store : DiskStore
  key   : Key
  fork  : Fork

/-- Feed one chunk: it is teed to the client and the temp file; the COMMITTED store
is untouched (the temp file is not yet renamed, so no reader can see it). -/
def Session.feed (sess : Session) (bs : Bytes) : Session :=
  { sess with fork := sess.fork.chunk bs }

/-- Feed a whole sequence of chunks — the committed store stays untouched. -/
def Session.feedAll (sess : Session) (chunks : List Bytes) : Session :=
  { sess with fork := chunks.foldl (fun f c => f.chunk c) sess.fork }

/-- **COMMIT** (end-of-stream): return the bytes already delivered to the client
together with the resulting committed store. `ok` models whether the atomic rename
landed: on `true` the staged bytes are installed as one entry (`DiskStore.put`); on
`false` the rename never happened (a disk error / ENOSPC / a full-store eviction
dropped it) and the committed store is returned untouched. **The client bytes are
the same in both arms** — the cache is best-effort, never a gate on delivery. -/
def Session.commit (sess : Session) (ok : Bool) (status ttl storedAt : Nat)
    (headers : List (Bytes × Bytes)) : Bytes × DiskStore :=
  if ok then
    (sess.fork.client,
      sess.store.put sess.key
        { status := status, headers := headers, body := sess.fork.staged,
          storedAt := storedAt, ttl := ttl })
  else
    (sess.fork.client, sess.store)

/-- **ABORT**: the client keeps the bytes it already received; the temp file is
dropped and the committed store is returned untouched (the rename never happens). -/
def Session.abort (sess : Session) : Bytes × DiskStore :=
  (sess.fork.client, sess.store)

/-! ## Headline theorem 1 — the client gets the full body, regardless of the cache -/

/-- **The client receives the whole body, and its bytes do not depend on the cache
outcome.** Running the write-through tee over the whole chunked body, the bytes
delivered to the client equal the whole body `chunks.flatten` whether the commit
*succeeds*, the commit *fails*, or the stream is *aborted* — all three outcomes
deliver byte-identical client streams. The cache is a side effect of streaming,
never a gate on it. -/
theorem tee_client_gets_full
    (s : DiskStore) (k : Key) (chunks : List Bytes)
    (status ttl storedAt : Nat) (headers : List (Bytes × Bytes)) :
    let sess : Session := { store := s, key := k, fork := Fork.run chunks }
    -- (a) a SUCCESSFUL commit delivers the whole body to the client
    (sess.commit true status ttl storedAt headers).1 = chunks.flatten
    -- (b) a FAILED commit delivers the identical whole body to the client
    ∧ (sess.commit false status ttl storedAt headers).1 = chunks.flatten
    -- (c) an ABORT delivers the identical whole body to the client
    ∧ sess.abort.1 = chunks.flatten
    -- (d) so the client stream is byte-identical across every cache outcome
    ∧ (sess.commit true status ttl storedAt headers).1
        = (sess.commit false status ttl storedAt headers).1
    ∧ (sess.commit true status ttl storedAt headers).1 = sess.abort.1 := by
  have hc := run_client chunks
  refine ⟨hc, hc, hc, ?_, ?_⟩ <;> simp [Session.commit, Session.abort]

/-! ## Headline theorem 2 — the cached body equals the streamed body, exactly -/

/-- **A successful commit caches exactly the streamed body, byte-for-byte.** After
the atomic rename lands, the committed cache entry's body equals the whole streamed
body `chunks.flatten`, which is exactly the bytes the client received. Composes the
real `Cache.Disk` store round-trip (`disk_get_put`). -/
theorem tee_cache_exact
    (s : DiskStore) (k : Key) (chunks : List Bytes)
    (status ttl storedAt : Nat) (headers : List (Bytes × Bytes)) :
    let sess : Session := { store := s, key := k, fork := Fork.run chunks }
    let res := sess.commit true status ttl storedAt headers
    -- (a) the cached body is the whole streamed body, byte-for-byte
    (res.2.get? k).map DiskEntry.body = some chunks.flatten
    -- (b) and that is exactly what the client received
    ∧ (res.2.get? k).map DiskEntry.body = some res.1 := by
  have hput : (Session.commit { store := s, key := k, fork := Fork.run chunks }
      true status ttl storedAt headers).2.get? k
        = some { status := status, headers := headers, body := (Fork.run chunks).staged,
                 storedAt := storedAt, ttl := ttl } := by
    simp only [Session.commit, if_pos]
    exact Cache.Disk.disk_get_put s k _
  refine ⟨?_, ?_⟩
  · rw [hput]; show some (Fork.run chunks).staged = some chunks.flatten; rw [run_staged]
  · rw [hput]
    show some (Fork.run chunks).staged = some (Fork.run chunks).client
    rw [run_staged, run_client]

/-! ## Headline theorem 3 — an aborted stream leaves no partial entry -/

/-- **A client abort mid-stream does not leave a partial/poisoned cache entry.**
Feeding any prefix of chunks then aborting leaves the committed store byte-for-byte
unchanged; a key absent before the stream is still absent after the abort. A commit
whose rename *fails* is proved to leave the store untouched the same way — no reader
can ever observe a truncated body. -/
theorem tee_abort_no_partial
    (s : DiskStore) (k : Key) (chunks : List Bytes)
    (status ttl storedAt : Nat) (headers : List (Bytes × Bytes))
    (hpre : s.get? k = none) :
    let sess' : Session := Session.feedAll { store := s, key := k, fork := Fork.empty } chunks
    -- feeding never touches the committed store
    sess'.store = s
    -- the abort leaves the committed store byte-for-byte unchanged
    ∧ sess'.abort.2 = s
    -- so after streaming any prefix, the aborted key has NO entry
    ∧ sess'.abort.2.get? k = none
    -- and a FAILED commit (rename never lands) leaves nothing either
    ∧ (sess'.commit false status ttl storedAt headers).2.get? k = none := by
  refine ⟨rfl, rfl, hpre, ?_⟩
  show s.get? k = none
  exact hpre

/-! ## Non-vacuous witness: the mutant the temp-file discipline forbids -/

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
    (Session.abort { store := s, key := k, fork := Fork.run [part] }).2.get? k = none
    -- forbidden direct-write: aborted → a partial entry survives
    ∧ (naiveFeed s k part).get? k ≠ none := by
  refine ⟨hpre, ?_⟩
  rw [naiveFeed, Cache.Disk.disk_get_put]
  exact Option.some_ne_none _

/-! ## Composition with the real streaming emit (`Reactor.ServeStream`)

The chunks the tee forks are not arbitrary — they are the paced body chunks the
streaming serve emits (`Reactor.ServeStream.srcChunks`), whose flatten is proven to
be the source's whole body (`srcChunks_flatten`), whatever the chunk size. The
streaming emit works over wire bytes (`List UInt8`); the cache stores their numeric
image (`List Nat`). The bridge is the injective `·.toNat`.

Rung note: this composes the drorb-native streaming-emit MODEL (`ServeStream`), not
the byte-for-byte deployed serve path; it grounds the tee in the same paced-chunk
emit the deployed streaming export reassembles. -/

open Reactor.ServeStream (BodySrc bodyBytes srcChunks srcChunks_flatten ServeConfig)

/-- The on-disk numeric image of a chunk list from the (wire-level) streaming emit —
each `List UInt8` chunk mapped byte-wise to `List Nat`. -/
def numChunks (chunks : List (List UInt8)) : List Bytes :=
  chunks.map (fun c => c.map (·.toNat))

/-- The numeric image of a chunk list flattens to the numeric image of the flat
body — mapping and flattening commute, so no boundary is disturbed. -/
theorem numChunks_flatten (chunks : List (List UInt8)) :
    (numChunks chunks).flatten = chunks.flatten.map (·.toNat) := by
  unfold numChunks; rw [← List.map_flatten]

/-- **Streaming a real body SOURCE: client gets the whole body, cache holds it
exactly.** Teeing the REAL paced body chunks of a body SOURCE
(`Reactor.ServeStream.srcChunks` — an inline body, a static-file window, or a
proxied upstream), whatever the chunk size `cfg.chunk`: (a) the client receives the
numeric image of the source's whole body; and (b) on a successful commit the cache
entry's body is exactly that same numeric image. So streaming-while-caching a
chunked body loses nothing, at any chunk size. Composes the streaming emit's
`srcChunks_flatten` with the store round-trip. -/
theorem tee_streamed_source_client_and_cache
    (s : DiskStore) (k : Key) (cfg : ServeConfig) (src : BodySrc)
    (status ttl storedAt : Nat) (headers : List (Bytes × Bytes)) :
    let chunks := numChunks (srcChunks cfg src)
    let sess : Session := { store := s, key := k, fork := Fork.run chunks }
    let res := sess.commit true status ttl storedAt headers
    -- (a) the client received the source's whole body (numeric image)
    res.1 = (bodyBytes src).map (·.toNat)
    -- (b) the cache holds exactly that
    ∧ (res.2.get? k).map DiskEntry.body = some ((bodyBytes src).map (·.toNat)) := by
  refine ⟨?_, ?_⟩
  · show (Fork.run (numChunks (srcChunks cfg src))).client = _
    rw [run_client, numChunks_flatten, srcChunks_flatten]
  · show ((DiskStore.put s k _).get? k).map DiskEntry.body = _
    rw [Cache.Disk.disk_get_put]
    show some (Fork.run (numChunks (srcChunks cfg src))).staged = _
    rw [run_staged, numChunks_flatten, srcChunks_flatten]

/-! ## Runnable checks -/

/-- A concrete stream: three chunks `[1,2] [3] [4,5,6]` into an empty cache under a
real key. The client gets `[1,2,3,4,5,6]`. -/
def demoKey : Key := { method := 71, uri := 100, vary := [] }
def demoChunks : List Bytes := [[1, 2], [3], [4, 5, 6]]

example : (Fork.run demoChunks).client = [1, 2, 3, 4, 5, 6] := by decide

-- Client gets the full body under a FAILED commit too (regardless of cache outcome).
example :
    (Session.commit { store := DiskStore.empty, key := demoKey, fork := Fork.run demoChunks }
        false 200 100 0 []).1 = [1, 2, 3, 4, 5, 6] := by decide

-- A successful commit caches exactly the streamed body, byte-for-byte.
example :
    ((Session.commit { store := DiskStore.empty, key := demoKey, fork := Fork.run demoChunks }
        true 200 100 0 []).2.get? demoKey).map DiskEntry.body = some [1, 2, 3, 4, 5, 6] :=
  (tee_cache_exact DiskStore.empty demoKey demoChunks 200 100 0 []).1

-- A real abort: stream two chunks then abort; the empty cache stays empty.
example :
    (Session.abort (Session.feedAll
      { store := DiskStore.empty, key := demoKey, fork := Fork.empty } [[9], [8, 7]])).2.get? demoKey
      = none :=
  (tee_abort_no_partial DiskStore.empty demoKey [[9], [8, 7]] 200 100 0 [] rfl).2.2.1

#print axioms tee_client_gets_full
#print axioms tee_cache_exact
#print axioms tee_abort_no_partial
#print axioms tee_vs_naive_abort
#print axioms tee_streamed_source_client_and_cache

end Cache.StreamTee
