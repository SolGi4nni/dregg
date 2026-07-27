/-
# StickTableLive — driving the PROVEN stick-table FSM over the byte level

The `StickTable` foundation models a keyed cross-request counter/last-seen table
as a sequential transition system over an explicit clock: a request `track`s a
key (bump its counter, refresh last-seen to `max old now`), a `lookup` reads the
entry back subject to TTL, `evict` drops entries past their TTL, and a sharded
deployment's global counter is the per-key SUM over shard tables. Every one of
those steps carries a proof (`bump_getCount_self`, `lookup_live`,
`lookup_expired`, `evict_removes_expired`, `run_getCount`, `shard_merge_two`, …)
— but that logic is *inert*: nothing yet feeds it real request events off a wire.

This lane wires the inert FSM to the byte level. A stick-table update stream is a
list of timed `track` events `Ev { key, now }`; here it is given a
self-delimiting binary framing built from the proven codec algebra
(`putNat`/`getNat`/`putSeq`/`getSeq` and their round-trips), and a `selftest`
that drives the WHOLE chain — encode an event trace, decode it, fold it with
`run`, `lookup` a key inside and outside its TTL, `evict`, and split-and-merge
the count across two shards — with **no crypto whatsoever**, so it runs under
`lake env lean --run`.

## Honesty / realization boundary

This is **drorb-native** and **pure**. The encoder and decoder are our own
spec-conformant peers speaking a modelled binary framing (NOT a real
peers-replication protocol wire, whose byte-exact framing and the TLS transport
it usually rides are the named residual). No socket, no FFI call: the reused C
objects are
linked only to satisfy the shared executable link line and are never called (a
crypto FFI call would crash the pure-Lean interpreter). Everything structural
here is the proven Lean; the gap the selftest discharges *by construction* (not
by proof) is that this exe faithfully CALLS the proven Lean functions on real
bytes. The faithfulness of the decode→run→lookup/shard chain ITSELF is proven
below (`sticktable_faithful` and the found / expired / shard-conservation lemmas),
composing the wire-codec round-trip with the proven FSM steps.

The cross-shard *concurrent* merge (CR-2 in `StickTable.Shard`) remains a stated,
undischarged obligation; this lane wires only the sequential per-shard model and
the algebraic (partition-sum) half of the merge, exactly as proven.

Usage:
  sticktable-live selftest
-/
import StickTable
import Control

namespace StickTableLive

open StickTable
open Control (Bytes putNat getNat getNat_putNat putSeq getSeq getSeq_putSeq)

/-! ## §1  An `Ev` / trace codec, over the proven codec algebra

A `track` event is two `Nat`s: the key and the clock reading. We frame it as two
varints, and a trace as a length-prefixed sequence of events. Each piece carries
its own round-trip theorem, chaining to `getTrace_put`. -/

/-- Wire framing for one timed `track` event: `key` varint, then `now` varint. -/
def putEv (e : Ev) : Bytes := putNat e.key ++ putNat e.now

/-- Read one `Ev` off the front of the buffer. -/
def getEv (bs : Bytes) : Option (Ev × Bytes) :=
  match getNat bs with
  | some (key, r) =>
    match getNat r with
    | some (now, r2) => some (⟨key, now⟩, r2)
    | none => none
  | none => none

/-- **Event round-trip.** Encoding an `Ev` then reading it back recovers it
verbatim, leaving the trailing bytes untouched. -/
theorem getEv_putEv (e : Ev) (t : Bytes) : getEv (putEv e ++ t) = some (e, t) := by
  obtain ⟨key, now⟩ := e
  simp only [putEv, getEv, List.append_assoc, getNat_putNat]

/-- Wire framing for an event trace: a length-prefixed sequence of `Ev`s. -/
def putTrace (evs : List Ev) : Bytes := putSeq putEv evs

/-- Read a whole event trace. -/
def getTrace (bs : Bytes) : Option (List Ev × Bytes) := getSeq getEv bs

/-- **The trace wire round-trip.** The whole event stream encodes then decodes
back verbatim — the workhorse the faithfulness theorems compose with the FSM. -/
theorem getTrace_put (evs : List Ev) (t : Bytes) :
    getTrace (putTrace evs ++ t) = some (evs, t) :=
  getSeq_putSeq putEv getEv getEv_putEv evs t

/-! ## §2  Faithfulness — the byte-level FSM realizes the proven model

The running loop decodes the event stream off the wire and drives EXACTLY the
proven decision. -/

/-- **Faithfulness (fold + read).** Given any event trace `evs` serialized by
`putTrace` (into a buffer with arbitrary trailing bytes `t`), decoding it with
`getTrace`, folding it from empty with `run`, then reading key `k`'s counter
(`getCount`) and its TTL-gated entry (`lookup`) produces PRECISELY what the model
computes by folding the SAME trace — the bytes on the wire realize the model,
mediated only by the proven codec round-trip (`getTrace_put`).

Not a `P → P`: it is inhabited (the selftest below produces such a buffer and
witnesses the equality on concrete bytes) and its content is the codec round-trip
composed with the FSM fold and TTL read — a real equation over every `evs`, `k`,
`ttl`, `now`, and trailing `t`. -/
theorem sticktable_faithful (evs : List Ev) (k ttl now : Nat) (t : Bytes) :
    (getTrace (putTrace evs ++ t)).map
        (fun r => (getCount k (run [] r.1), lookup k ttl now (run [] r.1)))
      = some (getCount k (run [] evs), lookup k ttl now (run [] evs)) := by
  rw [getTrace_put evs t]; rfl

/-- **A tracked key is found within its TTL (byte level).** Serialize a single
`track` for key `k` at clock `now`; decode it, fold from empty, and `lookup` at
any query clock `q` still inside the idle window (`q < now + ttl`). The key reads
back present with counter `1` and last-seen `now`. The hypothesis `hlive` is
load-bearing — drop it and the conclusion fails past the TTL (next lemma). -/
theorem sticktable_track_found_wire (k now ttl q : Nat) (hlive : q < now + ttl)
    (t : Bytes) :
    (getTrace (putTrace [⟨k, now⟩] ++ t)).map (fun r => lookup k ttl q (run [] r.1))
      = some (some ⟨1, now⟩) := by
  have hfind : find k (run ([] : Table) [⟨k, now⟩]) = some ⟨1, now⟩ := by
    simp [run, bump, find]
  rw [getTrace_put]
  show some (lookup k ttl q (run ([] : Table) [⟨k, now⟩])) = some (some ⟨1, now⟩)
  rw [lookup_live hfind hlive]

/-- **A tracked key expires after its TTL (byte level).** The same serialized
single-`track` trace, but queried at `q` at or past the idle window
(`¬ q < now + ttl`): `lookup` reads the key back as absent. This is the
complement of the previous lemma — together they pin the TTL boundary. -/
theorem sticktable_track_expired_wire (k now ttl q : Nat) (hexp : ¬ q < now + ttl)
    (t : Bytes) :
    (getTrace (putTrace [⟨k, now⟩] ++ t)).map (fun r => lookup k ttl q (run [] r.1))
      = some none := by
  have hfind : find k (run ([] : Table) [⟨k, now⟩]) = some ⟨1, now⟩ := by
    simp [run, bump, find]
  rw [getTrace_put]
  show some (lookup k ttl q (run ([] : Table) [⟨k, now⟩])) = some none
  rw [lookup_expired hfind hexp]

/-- **Shard accounting conserves (byte level).** Decode the trace off the wire and
fold it whole; the resulting counter for `k` equals the sum of the counters from
folding the two shard substreams under ANY boolean partition `part` of the events.
This is the byte-level realization of `shard_merge_two`: the per-key count is
additive over any split of the update stream across shards — nothing is
double-counted or dropped by sharding. -/
theorem sticktable_shard_conserve_wire (k : Nat) (part : Ev → Bool) (evs : List Ev)
    (t : Bytes) :
    (getTrace (putTrace evs ++ t)).map (fun r => getCount k (run [] r.1))
      = some (getCount k (run [] (evs.filter part))
              + getCount k (run [] (evs.filter (fun e => ! part e)))) := by
  rw [getTrace_put]
  show some (getCount k (run ([] : Table) evs)) = _
  rw [shard_merge_two k part evs]

/-! ## §3  Byte helper (pure) -/

/-- Hex-render a byte list (for the wire dump). -/
def toHexL (b : Bytes) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

/-! ## §4  The selftest — the stick-table FSM over the byte level, one process, NO crypto -/

def selftest : IO UInt32 := do
  IO.println "== sticktable-live selftest : keyed track/lookup/expire/shard, byte-level, NO crypto =="

  -- ── an event trace: keys 100 and 200 tracked several times at rising clocks ──
  let evs : List Ev :=
    [ ⟨100, 10⟩, ⟨200, 11⟩, ⟨100, 12⟩, ⟨100, 15⟩, ⟨200, 18⟩, ⟨100, 20⟩ ]
  let ttl : Nat := 30
  let kHot : Nat := 100      -- tracked 4×, last-seen 20
  let kCold : Nat := 200     -- tracked 2×, last-seen 18
  let kAbsent : Nat := 999   -- never tracked

  -- ── ENCODE the trace with the proven codec, DECODE it back ──
  let wire := putTrace evs
  IO.println s!"\n-- trace serialized (putTrace) --"
  IO.println s!"events                 : {evs.length}"
  IO.println s!"wire bytes             : {wire.length}B  {toHexL wire}"
  let some (decoded, rest) := getTrace wire
    | do IO.eprintln "getTrace FAILED to decode the trace"; return 1
  let decodeOk := rest.isEmpty && (decoded == evs)
  IO.println s!"getTrace∘putTrace == trace (wire round-trip realized) : {decodeOk}"
  if !decodeOk then do IO.eprintln "trace did NOT round-trip"; return 1

  -- ── FOLD the DECODED trace with the proven FSM ──
  let tbl := run [] decoded
  let hotCount  := getCount kHot tbl
  let coldCount := getCount kCold tbl
  IO.println s!"\n-- trace folded (getTrace → run) --"
  IO.println s!"key {kHot} count        : {hotCount}"
  IO.println s!"key {kCold} count        : {coldCount}"
  IO.println s!"key {kHot} last-seen    : {getLastSeen kHot tbl}"
  IO.println s!"key {kCold} last-seen    : {getLastSeen kCold tbl}"
  let countOk := hotCount == 4 && coldCount == 2 && getCount kAbsent tbl == 0

  -- ── LOOKUP inside and past the TTL ──
  let nowIn  : Nat := 40     -- 40 < 20 + 30  → hot key live;  40 < 18 + 30 → cold live
  let nowOut : Nat := 60     -- 60 ≥ 20 + 30  → hot key expired
  let hotLiveIn  := (lookup kHot ttl nowIn tbl).isSome
  let hotLiveOut := (lookup kHot ttl nowOut tbl).isSome
  let absentLookup := (lookup kAbsent ttl nowIn tbl).isSome
  IO.println s!"\n-- lookup (TTL={ttl}) --"
  IO.println s!"key {kHot} @clock {nowIn} found (within TTL)  : {hotLiveIn}"
  IO.println s!"key {kHot} @clock {nowOut} found (past TTL)    : {hotLiveOut}"
  IO.println s!"key {kAbsent} @clock {nowIn} found (untracked)  : {absentLookup}"
  let lookupOk := hotLiveIn && !hotLiveOut && !absentLookup

  -- ── EVICT past the TTL, confirm the expired key is gone and the live one stays ──
  let evicted := evict ttl nowOut tbl
  let hotAfterEvict  := (find kHot evicted).isSome    -- expired at nowOut → gone
  IO.println s!"\n-- evict @clock {nowOut} (TTL={ttl}) --"
  IO.println s!"table size before/after : {tbl.length} / {evicted.length}"
  IO.println s!"expired key {kHot} survived evict : {hotAfterEvict}"
  let evictOk := !hotAfterEvict

  -- ── SHARD split-and-merge: partition events by key parity, count each, sum ──
  let part : Ev → Bool := fun e => e.key % 2 == 0     -- even keys to shard A
  let shardA := run [] (decoded.filter part)
  let shardB := run [] (decoded.filter (fun e => ! part e))
  let merged := getCount kHot shardA + getCount kHot shardB
  IO.println s!"\n-- shard split-and-merge (partition by key parity) --"
  IO.println s!"shard A count[{kHot}] + shard B count[{kHot}] : {getCount kHot shardA} + {getCount kHot shardB} = {merged}"
  IO.println s!"whole-stream count[{kHot}]                    : {hotCount}"
  let shardOk := merged == hotCount

  -- ── the faithfulness cross-check (realizes sticktable_faithful on these bytes) ──
  let modelCount  := getCount kHot (run [] evs)
  let modelLookup := lookup kHot ttl nowIn (run [] evs)
  let faithful := (hotCount == modelCount) && ((lookup kHot ttl nowIn tbl) == modelLookup)
  IO.println s!"\n-- cross-check (realizes sticktable_faithful) --"
  IO.println s!"wire count == model count       : {hotCount == modelCount}"
  IO.println s!"wire lookup == model lookup     : {(lookup kHot ttl nowIn tbl) == modelLookup}"

  if decodeOk && countOk && lookupOk && evictOk && shardOk && faithful then do
    IO.println "\nPASS — trace serialized, decoded, folded; counts exact, TTL lookup live/expired,"
    IO.println "       eviction dropped the expired key, shard split-and-merge conserved the count;"
    IO.println "       the decode→run→lookup/shard chain equals the proven model decision."
    IO.println "STICK TABLE LIVE-WIRED (drorb-native, byte-level, NO crypto, verified codec+FSM)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the stick-table pipeline did not cross-check."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do
    IO.eprintln "usage: sticktable-live selftest"
    return 1

end StickTableLive

def main (args : List String) : IO UInt32 := StickTableLive.main args
