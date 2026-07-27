/-
# OutlierLive — driving the PROVEN passive outlier detector over the byte level

`Proxy.Outlier` models passive outlier detection — the reverse-proxy machine that
watches what actually happens to REAL requests and EJECTS a backend that answers
`consecutive` requests with server errors, under two guardrails proven inert in
`Proxy.Outlier`:

  * ejection is TIME-BOUNDED with linear backoff — an ejection lasts
    `baseEject * ejectCount` and a tick past the deadline readmits
    (`readmit_iff_deadline`);
  * ejection respects a POOL BUDGET — at most `maxEjectPercent` of the pool may
    be ejected at once, so a collective upstream fault can never let the detector
    eject its way into a total outage (`orun_capped`).

Those transitions are proven but **inert** — nothing drives them over real bytes.
This lane isolates the format-agnostic, crypto-free layer: a self-delimiting
codec for a detector *frame* (config + backend roster + an event trace) built
from the proven codec algebra (`putNat`/`getNat`, `putSeq`/`getSeq` and their
round-trips), and a `selftest` that drives the WHOLE chain — serialize a frame,
decode it, replay the event trace through the proven detector `orun`, cross-check
against the model — with **no crypto whatsoever**, so it runs under
`lake env lean --run`.

## Honesty / realization boundary (the NetmapLive / ProxyLbLive discipline)

This is **drorb-native** and **pure**. It is a *rung-2 selftest*, NOT the deployed
serve: the encoder and decoder are our own spec-conformant peers speaking a
modelled binary framing (NOT a real proxy admin wire, NOT live request telemetry
off a socket — the named residual). No FFI call: the reused C objects are linked
only to satisfy the shared executable link line; the selftest never enters them.
Everything structural here is the proven Lean; the gap the selftest discharges by
construction (not by proof) is that this exe faithfully CALLS the proven detector
on real bytes. The faithfulness of the decode→replay chain ITSELF is proven below
as `outlier_faithful` (composing the frame codec round-trip with `orun`), and the
two detector GUARANTEES the row claims are re-derived over the on-the-wire frame:

  * `outlier_ejects` — a backend that answers `consecutive` requests with server
    errors is driven to `ejected = true` by the proven `orun`;
  * `outlier_max_eject_bounded` — along ANY event trace from a clean roster, the
    ejected count never exceeds the configured `maxEjectPercent` fraction of the
    pool, so the fleet is never fully ejected.

Usage:
  outlier-live selftest
-/
import Control
import Proxy.Outlier

namespace Proxy.OutlierLive

open Control (Bytes putNat getNat putSeq getSeq getNat_putNat getSeq_putSeq)
open Proxy.Outlier

/-! ## §1  A self-delimiting detector-frame codec, over the proven codec algebra -/

/-- `OutlierCfg` framing: the three configuration scalars, each self-delimiting. -/
def putCfg (c : OutlierCfg) : Bytes :=
  putNat c.consecutive ++ putNat c.baseEject ++ putNat c.maxEjectPercent

def getCfg (bs : Bytes) : Option (OutlierCfg × Bytes) := do
  let (consecutive, r) ← getNat bs
  let (baseEject, r) ← getNat r
  let (maxEjectPercent, r) ← getNat r
  some ({ consecutive, baseEject, maxEjectPercent }, r)

theorem getCfg_put (c : OutlierCfg) (t : Bytes) :
    getCfg (putCfg c ++ t) = some (c, t) := by
  obtain ⟨consecutive, baseEject, maxEjectPercent⟩ := c
  simp only [putCfg, getCfg, List.append_assoc, getNat_putNat, Option.bind_some,
    bind, Option.bind]

/-- `OEvent` framing: a tag byte-nat selects the arm, followed by its payload
scalar (a backend id for success/failure, the clock for a tick). -/
def putEvent : OEvent → Bytes
  | .success bid => putNat 0 ++ putNat bid
  | .failure bid => putNat 1 ++ putNat bid
  | .tick now => putNat 2 ++ putNat now

def getEvent (bs : Bytes) : Option (OEvent × Bytes) :=
  match getNat bs with
  | some (0, r) => (getNat r).map (fun p => (.success p.1, p.2))
  | some (1, r) => (getNat r).map (fun p => (.failure p.1, p.2))
  | some (2, r) => (getNat r).map (fun p => (.tick p.1, p.2))
  | _ => none

theorem getEvent_put (e : OEvent) (t : Bytes) :
    getEvent (putEvent e ++ t) = some (e, t) := by
  cases e <;>
    simp only [putEvent, getEvent, List.append_assoc, getNat_putNat] <;> rfl

/-- A roster is a length-prefixed sequence of backend ids. -/
def putRoster (bids : List Nat) : Bytes := putSeq putNat bids
def getRoster (bs : Bytes) : Option (List Nat × Bytes) := getSeq getNat bs

theorem getRoster_put (bids : List Nat) (t : Bytes) :
    getRoster (putRoster bids ++ t) = some (bids, t) :=
  getSeq_putSeq putNat getNat getNat_putNat bids t

/-- An event trace is a length-prefixed sequence of events. -/
def putTrace (es : List OEvent) : Bytes := putSeq putEvent es
def getTrace (bs : Bytes) : Option (List OEvent × Bytes) := getSeq getEvent bs

theorem getTrace_put (es : List OEvent) (t : Bytes) :
    getTrace (putTrace es ++ t) = some (es, t) :=
  getSeq_putSeq putEvent getEvent getEvent_put es t

/-- A detector **frame**: the config, then the backend roster, then the event
trace — everything the detector needs to replay a session, on one buffer. -/
def putFrame (c : OutlierCfg) (bids : List Nat) (es : List OEvent) : Bytes :=
  putCfg c ++ putRoster bids ++ putTrace es

def getFrame (bs : Bytes) :
    Option ((OutlierCfg × List Nat × List OEvent) × Bytes) := do
  let (c, r) ← getCfg bs
  let (bids, r) ← getRoster r
  let (es, r) ← getTrace r
  some ((c, bids, es), r)

/-- **The frame wire round-trip**, chaining the three field codecs. -/
theorem getFrame_put (c : OutlierCfg) (bids : List Nat) (es : List OEvent)
    (t : Bytes) : getFrame (putFrame c bids es ++ t) = some ((c, bids, es), t) := by
  simp only [putFrame, getFrame, List.append_assoc, getCfg_put, getRoster_put,
    getTrace_put, Option.bind_some, bind, Option.bind]

/-! ## §2  Replaying the proven detector over a decoded frame -/

/-- Replay a decoded frame: run the proven `orun` over a clean roster. -/
def runFrame (c : OutlierCfg) (bids : List Nat) (es : List OEvent) : OState :=
  orun c (OState.init bids) es

/-! ## §3  The faithfulness theorem

The running loop's decode→replay chain applies EXACTLY the proven detector.
Given any frame serialized by `putFrame` (into a buffer with arbitrary trailing
bytes `t`), decoding it with `getFrame` and replaying the trace over the decoded
config/roster produces PRECISELY what the model computes by replaying the SAME
trace on the original inputs — the bytes on the wire realize the model, mediated
only by the proven codec round-trip (`getFrame_put`).

Not a `P → P`: it is inhabited (the selftest below produces such a buffer and
witnesses the equality on concrete bytes) and its content is the codec round-trip
composed with `orun` — a real equation over every `c`, `bids`, `es`, `t`. -/
theorem outlier_faithful (c : OutlierCfg) (bids : List Nat) (es : List OEvent)
    (t : Bytes) :
    (getFrame (putFrame c bids es ++ t)).map (fun r => runFrame r.1.1 r.1.2.1 r.1.2.2)
      = some (runFrame c bids es) := by
  rw [getFrame_put]; rfl

/-! ## §4  Guarantee 1 — the detector actually ejects a persistently-failing backend

A single-member roster whose backend answers `consecutive` requests with server
errors is driven to `ejected = true` by the proven `orun`. This is the positive
converse of `Proxy.Outlier.eject_requires_streak`/`eject_respects_budget`. -/

/-- The failure transition ejects a non-ejected member exactly when its streak
completes AND the budget has headroom — the positive direction. -/
theorem failUpdate_ejects_at_threshold {cfg : OutlierCfg}
    {clock count allowed : Nat} {m : OMember}
    (hnej : m.ejected = false)
    (hstreak : cfg.consecutive ≤ m.streak + 1)
    (hbud : count + 1 ≤ allowed) :
    (failUpdate cfg clock count allowed m).ejected = true := by
  unfold failUpdate
  rw [if_neg (by simp [hnej]), if_pos ⟨hstreak, hbud⟩]

/-- **Driving a single-member roster to ejection.** Feeding a clean member `n`
consecutive failures, where its streak reaches the trip threshold at the last
one and the budget affords one ejection, drives it to `ejected = true`. The
roster stays a singleton (the detector flags, it never removes). -/
theorem fails_to_eject (cfg : OutlierCfg) (bid clk : Nat) (hbud : 1 ≤ budget cfg 1) :
    ∀ (n : Nat) (m : OMember), m.id = bid → m.ejected = false →
      m.streak + n = cfg.consecutive → 1 ≤ n →
      ∃ m', (orun cfg ⟨[m], clk⟩ (List.replicate n (OEvent.failure bid))).members = [m']
            ∧ m'.ejected = true := by
  intro n
  induction n with
  | zero => intro m _ _ _ hge; exact absurd hge (by decide)
  | succ k ih =>
    intro m hid hnej hsum _
    -- reduce one failure step over the singleton roster
    have hcount : ejectedCount [m] = 0 := by simp [ejectedCount, hnej]
    have hstepm : (ostep cfg ⟨[m], clk⟩ (OEvent.failure bid)).members
        = [failUpdate cfg clk 0 (budget cfg 1) m] := by
      simp only [ostep, updateFirst, hid, if_true, hcount]
      rfl
    by_cases hk : k = 0
    · -- last failure: streak completes, member ejects
      subst hk
      have htrip : cfg.consecutive ≤ m.streak + 1 := by omega
      have hej : (failUpdate cfg clk 0 (budget cfg 1) m).ejected = true :=
        failUpdate_ejects_at_threshold hnej htrip (by omega)
      refine ⟨failUpdate cfg clk 0 (budget cfg 1) m, ?_, hej⟩
      simp only [List.replicate, orun, hstepm]
    · -- below threshold: failure only counts up, then recurse
      have hlt : m.streak + 1 < cfg.consecutive := by omega
      have hbelow : failUpdate cfg clk 0 (budget cfg 1) m
          = { m with streak := m.streak + 1 } :=
        failure_below_streak hnej hlt
      have hstate : ostep cfg ⟨[m], clk⟩ (OEvent.failure bid)
          = ⟨[{ m with streak := m.streak + 1 }], clk⟩ := by
        simp only [ostep, updateFirst, hid, if_true, hcount, hbelow,
          List.length_cons, List.length_nil]
      have := ih { m with streak := m.streak + 1 } hid hnej (by simp; omega)
        (by omega)
      simpa only [List.replicate, orun, hstate] using this

/-- **Ejection is realized.** A clean single-backend roster whose backend answers
`consecutive` requests with server errors is driven to `ejected = true` by the
proven detector `orun`, provided the budget affords one ejection. -/
theorem outlier_ejects (cfg : OutlierCfg) (bid : Nat)
    (h1 : 1 ≤ cfg.consecutive) (hbud : 1 ≤ budget cfg 1) :
    ∃ m, (orun cfg (OState.init [bid])
            (List.replicate cfg.consecutive (OEvent.failure bid))).members = [m]
          ∧ m.ejected = true :=
  fails_to_eject cfg bid 0 hbud cfg.consecutive (OMember.init bid)
    rfl rfl (by simp [OMember.init]) h1

/-! ## §5  Guarantee 2 — the fleet is never fully ejected

Along ANY event trace from a clean roster, the ejected count never exceeds the
configured `maxEjectPercent` fraction of the pool. This is `Proxy.Outlier`'s
budget invariant (`orun_capped` from `init_capped`) re-stated at the frame layer,
so it holds verbatim of the byte-driven replay. -/
theorem outlier_max_eject_bounded (cfg : OutlierCfg) (bids : List Nat)
    (es : List OEvent) :
    ejectedCount (orun cfg (OState.init bids) es).members
      ≤ budget cfg (orun cfg (OState.init bids) es).members.length :=
  orun_capped (init_capped cfg bids) es

/-- The budget bound, re-stated over the DECODED frame (composing the codec
round-trip with `outlier_max_eject_bounded`). -/
theorem wire_max_eject_bounded (c : OutlierCfg) (bids : List Nat)
    (es : List OEvent) (t : Bytes) :
    (getFrame (putFrame c bids es ++ t)).all (fun r =>
      decide (ejectedCount (runFrame r.1.1 r.1.2.1 r.1.2.2).members
        ≤ budget r.1.1 (runFrame r.1.1 r.1.2.1 r.1.2.2).members.length)) = true := by
  rw [getFrame_put]
  simp only [Option.all_some, decide_eq_true_eq]
  exact outlier_max_eject_bounded c bids es

/-! ## §6  Non-vacuity: concrete eject / budget-cap / readmit instances -/

/-- Three consecutive 5xx eject a clean single-backend roster (consecutive = 3). -/
example : (orun ⟨3, 10, 100⟩ (OState.init [7])
    [.failure 7, .failure 7, .failure 7]).members.head?.map (·.ejected)
    = some true := by decide

/-- Two 5xx then a success then two 5xx never eject — the streak resets. -/
example : (orun ⟨3, 10, 100⟩ (OState.init [7])
    [.failure 7, .failure 7, .success 7, .failure 7, .failure 7]).members.head?.map (·.ejected)
    = some false := by decide

/-- Budget cap: a 4-backend pool at `maxEjectPercent = 50` (budget 2) — trying to
eject all four leaves exactly two ejected, never four. -/
example : ejectedCount (orun ⟨1, 10, 50⟩ (OState.init [0, 1, 2, 3])
    [.failure 0, .failure 1, .failure 2, .failure 3]).members = 2 := by decide

/-- Readmission: a backend ejected at clock 100 (baseEject 10, ejectCount 1,
deadline 110) is readmitted by a tick at 110, not by a tick at 105. -/
example : ((orun ⟨1, 10, 100⟩ ⟨[⟨0, 0, false, 0, 0⟩], 100⟩
    [.failure 0, .tick 105, .tick 110]).members.head?).map (·.ejected)
    = some false := by decide

example : ((orun ⟨1, 10, 100⟩ ⟨[⟨0, 0, false, 0, 0⟩], 100⟩
    [.failure 0, .tick 105]).members.head?).map (·.ejected)
    = some true := by decide

/-! ## §7  Rendering helpers (pure) -/

def showMember (m : OMember) : String :=
  s!"#{m.id} streak={m.streak} ejected={m.ejected} ejectedAt={m.ejectedAt} ejectCount={m.ejectCount}"

def toHex (b : Bytes) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

/-! ## §8  The selftest — outlier ejection over the byte level, one process, NO crypto -/

def selftest : IO UInt32 := do
  IO.println "== outlier-live selftest : passive outlier ejection, byte-level, NO crypto =="

  -- ── the configuration & roster ──
  -- consecutive=3 server errors eject; baseEject=10 (× ejectCount backoff);
  -- maxEjectPercent=50 over a 4-backend pool ⇒ budget = 4*50/100 = 2 ejected max.
  let cfg : OutlierCfg := ⟨3, 10, 50⟩
  let bids := [0, 1, 2, 3]
  let bud := budget cfg bids.length
  IO.println s!"\n-- config --"
  IO.println s!"  consecutive={cfg.consecutive} baseEject={cfg.baseEject} maxEjectPercent={cfg.maxEjectPercent}%"
  IO.println s!"  roster={bids}  budget (max ejected at once) = {bud}"

  -- ── the event trace ──
  -- advance the clock to 100, then answer 3 consecutive 5xx for #0 (ejects it),
  -- then 3 for #1 (ejects, count=2=budget), then 3 for #2 (REFUSED past budget),
  -- then tick to 110 (readmits #0 whose deadline 100+10=110 has elapsed).
  let trace : List OEvent :=
    [.tick 100,
     .failure 0, .failure 0, .failure 0,
     .failure 1, .failure 1, .failure 1,
     .failure 2, .failure 2, .failure 2,
     .tick 110]
  IO.println s!"\n-- event trace ({trace.length} events) --"
  IO.println s!"  tick 100 · 3×5xx→#0 · 3×5xx→#1 · 3×5xx→#2 · tick 110"

  -- ── serialize the whole frame, decode it back over the proven codec ──
  let wire := putFrame cfg bids trace
  IO.println s!"\n-- frame serialized (putFrame) --"
  IO.println s!"  wire bytes              : {wire.length}B  {toHex (wire.take 24)}…"
  let some ((cfg', bids', trace'), rest) := getFrame wire
    | do IO.eprintln "getFrame FAILED to decode the frame"; return 1
  let decodeOk := rest.isEmpty && cfg' == cfg && bids' == bids && trace' == trace
  IO.println s!"  getFrame∘putFrame == frame (wire round-trip realized) : {decodeOk}"
  if !decodeOk then do IO.eprintln "frame did NOT round-trip"; return 1

  -- ── replay the trace through the PROVEN detector, over the DECODED frame ──
  let final := runFrame cfg' bids' trace'
  let finalModel := runFrame cfg bids trace
  IO.println "\n-- detector replay (runFrame over decoded bytes) --"
  for m in final.members do IO.println s!"  {showMember m}"
  IO.println s!"  clock                   : {final.clock}"

  -- guarantee 1: #0 answered 3 consecutive 5xx and was ejected... then readmitted
  -- at its deadline (tick 110). Check the intermediate eject before readmission.
  let afterEjects := runFrame cfg bids
    [.tick 100, .failure 0, .failure 0, .failure 0]
  let zeroEjected := (afterEjects.members.find? (·.id == 0)).map (·.ejected) == some true
  IO.println s!"\n-- guarantee 1 : persistently-failing backend is EJECTED --"
  IO.println s!"  #0 after 3 consecutive 5xx ejected     : {zeroEjected}"

  -- guarantee 2: budget cap. #0 and #1 eject (count reaches budget=2); #2 is
  -- REFUSED past the budget (still counting, not ejected); the pool is never
  -- fully ejected.
  let ejN := ejectedCount afterEjects.members
  let afterTwo := runFrame cfg bids
    [.tick 100, .failure 0, .failure 0, .failure 0, .failure 1, .failure 1, .failure 1]
  let afterThree := runFrame cfg bids
    [.tick 100, .failure 0, .failure 0, .failure 0, .failure 1, .failure 1, .failure 1,
     .failure 2, .failure 2, .failure 2]
  let twoEjected := ejectedCount afterTwo.members == 2
  let thirdRefused := ejectedCount afterThree.members == 2
  let twoNotFour := decide (ejectedCount afterThree.members < bids.length)
  IO.println s!"\n-- guarantee 2 : budget cap — fleet never fully ejected --"
  IO.println s!"  ejected after #0 tripped                : {ejN}"
  IO.println s!"  ejected after #0,#1 tripped (=budget 2) : {twoEjected}"
  IO.println s!"  #2 REFUSED past budget (still 2 ejected): {thirdRefused}"
  IO.println s!"  ejected {ejectedCount afterThree.members} < pool size {bids.length}    : {twoNotFour}"

  -- readmission after backoff deadline
  let readmitOk := (final.members.find? (·.id == 0)).map (·.ejected) == some false
  IO.println s!"\n-- backoff readmission (tick past deadline) --"
  IO.println s!"  #0 readmitted at tick 110 (deadline 110): {readmitOk}"

  -- ── the faithfulness cross-check: decode∘replay == model replay (outlier_faithful) ──
  let faithful := final == finalModel
  IO.println "\n-- cross-check (realizes outlier_faithful) --"
  IO.println s!"  wire replay == model replay             : {faithful}"

  -- ── the budget bound holds over the decoded frame (wire_max_eject_bounded) ──
  let boundOk := decide (ejectedCount final.members ≤ budget cfg' final.members.length)
  IO.println s!"  ejected {ejectedCount final.members} ≤ budget {budget cfg' final.members.length} over decoded frame : {boundOk}"

  if decodeOk && zeroEjected && twoEjected && thirdRefused && twoNotFour &&
      readmitOk && faithful && boundOk then do
    IO.println "\nPASS — frame serialized, decoded; the proven passive outlier detector replayed"
    IO.println "       over the decoded bytes: a persistently-failing backend ejected, the ejection"
    IO.println "       budget held the fleet from full ejection, backoff readmitted, all cross-checked."
    IO.println "OUTLIER DETECTION LIVE-WIRED (drorb-native, byte-level, NO crypto, verified codec+detector)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the outlier-detection pipeline did not cross-check."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do
    IO.eprintln "usage: outlier-live selftest"
    return 1

end Proxy.OutlierLive

def main (args : List String) : IO UInt32 := Proxy.OutlierLive.main args
