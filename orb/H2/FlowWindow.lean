import H2.Conn

/-!
# HTTP/2 flow-control window enforcement — end-to-end ledger (RFC 9113 §5.2, §6.9)

This module closes the flow-control parity row by lifting the **proven DATA
pacer** (`H2.Conn.sendChunks`, with its `sendChunks_accounting` /
`sendChunks_no_overdraw` / `sendChunks_parks` obligations) into a
**connection+stream trajectory ledger** and proving the three headline
enforcement properties over *arbitrary interleavings* of DATA sends and
`WINDOW_UPDATE` credits.

The pacer is the trusted single-step; here we account for *every* step of a run:

* **`connWindow` / `strWindow`** — the two live send windows (RFC 9113 §5.2):
  a shared connection window and one stream window. Both are `Int`, so
  "never overdrawn" is a genuine proposition (a `Nat` would make it vacuous).
* **`connCredit` / `strCredit`** — the running sum of accepted `WINDOW_UPDATE`
  increments on each level (the peer's granted credit).
* **`connSent` / `strSent`** — the running total of DATA payload octets the
  pacer has actually emitted, accumulated from each `sendChunks` call.

The ledger invariant `window = initial + credits − sent` (`Conserved`) is the
bridge: composing it with `0 ≤ window` yields the enforcement bound
`sent ≤ initial + credits`. Every step preserves the invariant — the send step
because `sendChunks_accounting` says both windows drop by exactly the emitted
octet count and `sendChunks_no_overdraw` keeps them non-negative; the
`WINDOW_UPDATE` step because an accepted increment raises the window and the
credit ledger by the same amount, and a rejected one is a no-op.

Headline theorems (each 0-sorry, non-vacuous, over an arbitrary run):

1. `window_never_exceeded` — total DATA sent on a stream never exceeds the peer
   initial window plus the sum of its `WINDOW_UPDATE` increments (and the
   connection form `window_never_exceeded_conn`). This *composes*
   `sendChunks`'s per-call conservation across the whole trajectory.
2. `window_update_credits` — a valid `WINDOW_UPDATE` raises the available
   window by exactly its increment.
3. `window_zero_stalls` — a send offered against a zero window emits nothing
   and advances no counter: the DATA parks (via `sendChunks_parks`).
-/

namespace H2
namespace FlowWindow

open H2.Conn (maxWindow sendChunks credit sendChunks_accounting sendChunks_no_overdraw
  sendChunks_parks)

/-! ## The connection+stream flow-control ledger -/

/-- The send-side flow-control state for one focused stream together with its
shared connection window, plus the ghost accounting ledger on each level. -/
structure Flow where
  /-- Live connection-level send window (shared across streams). -/
  connWindow : Int
  /-- Live stream-level send window. -/
  strWindow : Int
  /-- Connection `SETTINGS_INITIAL_WINDOW_SIZE`. -/
  connInit : Int
  /-- Running sum of accepted connection `WINDOW_UPDATE` increments. -/
  connCredit : Int
  /-- Running total DATA octets emitted, charged to the connection window. -/
  connSent : Int
  /-- Stream `SETTINGS_INITIAL_WINDOW_SIZE` (the peer's initial stream window). -/
  strInit : Int
  /-- Running sum of accepted stream `WINDOW_UPDATE` increments. -/
  strCredit : Int
  /-- Running total DATA octets emitted on this stream. -/
  strSent : Int
deriving Repr, DecidableEq

/-- The **conservation invariant** on both levels: each live window equals its
initial size plus every accepted increment minus every emitted octet. -/
def Flow.Conserved (f : Flow) : Prop :=
  f.connWindow = f.connInit + f.connCredit - f.connSent ∧
  f.strWindow = f.strInit + f.strCredit - f.strSent

/-- **Well-formedness**: conserved on both levels, both windows in
`[0, 2^31 − 1]`. Maintained by every step. -/
def Flow.WF (f : Flow) : Prop :=
  f.Conserved ∧
  0 ≤ f.connWindow ∧ 0 ≤ f.strWindow ∧
  f.connWindow ≤ maxWindow ∧ f.strWindow ≤ maxWindow

/-- A fresh flow from the peer's connection and stream initial-window sizes. -/
def Flow.fresh (connInit strInit : Int) : Flow :=
  { connWindow := connInit, strWindow := strInit
    connInit := connInit, connCredit := 0, connSent := 0
    strInit := strInit, strCredit := 0, strSent := 0 }

/-- A fresh flow with in-range initial windows is well-formed. -/
theorem Flow.fresh_WF {ci si : Int}
    (hc0 : 0 ≤ ci) (hs0 : 0 ≤ si) (hcm : ci ≤ maxWindow) (hsm : si ≤ maxWindow) :
    (Flow.fresh ci si).WF := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp only [Flow.fresh] <;> omega

/-! ## Operations -/

/-- Offer `body` as DATA via the proven pacer, charging both windows by the
emitted octet count and growing both `sent` ledgers by the same amount. Fuel
`body.length + 1` always suffices (the pacer's own precondition). -/
def Flow.send (f : Flow) (body : Bytes) (maxFrame : Nat) : Flow :=
  match sendChunks (body.length + 1) 0 f.connWindow f.strWindow maxFrame body with
  | (_, rem, cw', sw') =>
      let emitted : Int := ((body.length - rem.length : Nat) : Int)
      { f with
        connWindow := cw', strWindow := sw'
        connSent := f.connSent + emitted
        strSent := f.strSent + emitted }

/-- Apply a stream `WINDOW_UPDATE` of `inc`. A non-positive increment (0 is a
PROTOCOL_ERROR; the 31-bit field is `≥ 0`) or one that would push the window
past `2^31 − 1` (FLOW_CONTROL_ERROR) is rejected as a no-op; otherwise the
window and the credit ledger both grow by `inc`. -/
def Flow.strUpdate (f : Flow) (inc : Int) : Flow :=
  if inc ≤ 0 ∨ maxWindow < f.strWindow + inc then f
  else { f with strWindow := f.strWindow + inc, strCredit := f.strCredit + inc }

/-- Apply a connection `WINDOW_UPDATE` of `inc` (same discipline as
`Flow.strUpdate`, on the connection window). -/
def Flow.connUpdate (f : Flow) (inc : Int) : Flow :=
  if inc ≤ 0 ∨ maxWindow < f.connWindow + inc then f
  else { f with connWindow := f.connWindow + inc, connCredit := f.connCredit + inc }

/-! ## Property 2 — a `WINDOW_UPDATE` credits the window by its increment -/

/-- **`window_update_credits`**: a valid stream `WINDOW_UPDATE` raises the
available stream window by *exactly* its increment (RFC 9113 §6.9). -/
theorem window_update_credits (f : Flow) (inc : Int)
    (hpos : 0 < inc) (hcap : f.strWindow + inc ≤ maxWindow) :
    (f.strUpdate inc).strWindow = f.strWindow + inc := by
  unfold Flow.strUpdate
  rw [if_neg (by omega)]

/-- The connection-level companion: a valid connection `WINDOW_UPDATE` raises
the connection window by exactly its increment. -/
theorem window_update_credits_conn (f : Flow) (inc : Int)
    (hpos : 0 < inc) (hcap : f.connWindow + inc ≤ maxWindow) :
    (f.connUpdate inc).connWindow = f.connWindow + inc := by
  unfold Flow.connUpdate
  rw [if_neg (by omega)]

/-- A rejected (zero or overflowing) `WINDOW_UPDATE` is a no-op — the window and
its credit ledger are untouched, so no phantom credit is conjured. -/
theorem strUpdate_reject (f : Flow) (inc : Int)
    (h : inc ≤ 0 ∨ maxWindow < f.strWindow + inc) : f.strUpdate inc = f := by
  unfold Flow.strUpdate
  rw [if_pos h]

/-! ## Property 3 — a zero window stalls the send (DATA parks) -/

/-- **`window_zero_stalls`**: with a zero stream window (and a non-negative
connection window) the pacer emits nothing and the send step is a no-op — the
whole body parks, no octet is charged, no counter advances. Proven by composing
`sendChunks_parks`. -/
theorem window_zero_stalls (f : Flow) (body : Bytes) (maxFrame : Nat)
    (hstr : f.strWindow = 0) (hconn : 0 ≤ f.connWindow) :
    f.send body maxFrame = f := by
  have hcred : credit f.connWindow f.strWindow = 0 := by
    unfold H2.Conn.credit
    rw [if_pos (by rw [hstr]; omega : min f.connWindow f.strWindow ≤ 0)]
  unfold Flow.send
  rw [sendChunks_parks (body.length + 1) 0 f.connWindow f.strWindow maxFrame body hcred]
  dsimp only
  have he : ((body.length - body.length : Nat) : Int) = 0 := by rw [Nat.sub_self]; rfl
  rw [he, Int.add_zero, Int.add_zero]

/-! ## The trajectory: arbitrary interleavings of sends and `WINDOW_UPDATE`s -/

/-- Send-path event alphabet. -/
inductive Event where
  /-- Offer `body` as DATA under `maxFrame`. -/
  | send (body : Bytes) (maxFrame : Nat)
  /-- A stream-level `WINDOW_UPDATE` of `inc`. -/
  | strUpdate (inc : Int)
  /-- A connection-level `WINDOW_UPDATE` of `inc`. -/
  | connUpdate (inc : Int)

/-- One step of the flow-control transition system. -/
def Flow.step (f : Flow) : Event → Flow
  | .send body maxFrame => f.send body maxFrame
  | .strUpdate inc => f.strUpdate inc
  | .connUpdate inc => f.connUpdate inc

/-- Run a whole event sequence through the step. -/
def Flow.run (f : Flow) (es : List Event) : Flow :=
  es.foldl Flow.step f

/-! ### Well-formedness is preserved by every step and every run -/

/-- **The send step preserves well-formedness** — this is where the proven
pacer obligations are composed: `sendChunks_accounting` (both windows drop by
the emitted count, `rem ≤ body`) gives conservation and the cap;
`sendChunks_no_overdraw` gives non-negativity. -/
theorem Flow.send_WF {f : Flow} (body : Bytes) (maxFrame : Nat) (hwf : f.WF) :
    (f.send body maxFrame).WF := by
  obtain ⟨⟨hcc, hsc⟩, hcn, hsn, hcm, hsm⟩ := hwf
  unfold Flow.send
  rcases hsend : sendChunks (body.length + 1) 0 f.connWindow f.strWindow maxFrame body
    with ⟨fs, rem, cw', sw'⟩
  obtain ⟨hle, hcweq, hsweq⟩ :=
    sendChunks_accounting (body.length + 1) 0 f.connWindow f.strWindow maxFrame body
      fs rem cw' sw' hsend
  obtain ⟨hcpos, hspos⟩ :=
    sendChunks_no_overdraw (body.length + 1) 0 f.connWindow f.strWindow maxFrame body
      fs rem cw' sw' hsend
  have hcp := hcpos hcn
  have hsp := hspos hsn
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp only [] <;> omega

/-- **The `WINDOW_UPDATE` steps preserve well-formedness** (both levels), with
no validity side-condition: an out-of-range increment is rejected as a no-op. -/
theorem Flow.strUpdate_WF {f : Flow} (inc : Int) (hwf : f.WF) :
    (f.strUpdate inc).WF := by
  obtain ⟨⟨hcc, hsc⟩, hcn, hsn, hcm, hsm⟩ := hwf
  unfold Flow.strUpdate
  by_cases h : inc ≤ 0 ∨ maxWindow < f.strWindow + inc
  · rw [if_pos h]; exact ⟨⟨hcc, hsc⟩, hcn, hsn, hcm, hsm⟩
  · rw [if_neg h]
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp only [] <;> omega

theorem Flow.connUpdate_WF {f : Flow} (inc : Int) (hwf : f.WF) :
    (f.connUpdate inc).WF := by
  obtain ⟨⟨hcc, hsc⟩, hcn, hsn, hcm, hsm⟩ := hwf
  unfold Flow.connUpdate
  by_cases h : inc ≤ 0 ∨ maxWindow < f.connWindow + inc
  · rw [if_pos h]; exact ⟨⟨hcc, hsc⟩, hcn, hsn, hcm, hsm⟩
  · rw [if_neg h]
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp only [] <;> omega

/-- **The step preserves well-formedness** — for every event. -/
theorem Flow.step_WF {f : Flow} {e : Event} (hwf : f.WF) : (f.step e).WF := by
  cases e with
  | send body maxFrame => exact Flow.send_WF body maxFrame hwf
  | strUpdate inc => exact Flow.strUpdate_WF inc hwf
  | connUpdate inc => exact Flow.connUpdate_WF inc hwf

/-- **The run preserves well-formedness** — from a well-formed start, under
*any* interleaving of DATA sends and `WINDOW_UPDATE`s, the reached state is
well-formed. -/
theorem Flow.run_WF : ∀ (es : List Event) (f : Flow), f.WF → (f.run es).WF
  | [], f, hwf => hwf
  | e :: rest, f, hwf => by
      have : (f.step e).WF := Flow.step_WF hwf
      exact Flow.run_WF rest (f.step e) this

/-! ## Property 1 — total DATA sent never exceeds initial window + credits -/

/-- **`window_never_exceeded`**: from a well-formed start, after *any* run, the
total DATA octets emitted on the stream never exceed the peer's initial stream
window plus the sum of its accepted `WINDOW_UPDATE` increments. This composes
the pacer's per-call conservation (via `run_WF`) across the whole trajectory:
`sent = initial + credits − window` and `window ≥ 0`. -/
theorem window_never_exceeded {f : Flow} {es : List Event} (hwf : f.WF) :
    (f.run es).strSent ≤ (f.run es).strInit + (f.run es).strCredit := by
  obtain ⟨⟨_, hsc⟩, _, hsn, _, _⟩ := Flow.run_WF es f hwf
  omega

/-- **Connection-level companion**: the same bound on the shared connection
window — total emitted DATA never exceeds the connection initial window plus its
`WINDOW_UPDATE` credits. -/
theorem window_never_exceeded_conn {f : Flow} {es : List Event} (hwf : f.WF) :
    (f.run es).connSent ≤ (f.run es).connInit + (f.run es).connCredit := by
  obtain ⟨⟨hcc, _⟩, hcn, _, _, _⟩ := Flow.run_WF es f hwf
  omega

/-- **Exact stream accounting** (the identity behind the bound): at every
reachable state the total DATA emitted equals initial + credits − current
window; no octet is conjured or lost. -/
theorem run_stream_accounting {f : Flow} {es : List Event} (hwf : f.WF) :
    (f.run es).strSent =
      (f.run es).strInit + (f.run es).strCredit - (f.run es).strWindow := by
  obtain ⟨⟨_, hsc⟩, _, _, _, _⟩ := Flow.run_WF es f hwf
  omega

/-! ## Non-vacuity — the properties fire on real, non-trivial traces -/

/-- A concrete trajectory: an initial stream window of 10, a 4-byte send, a
`WINDOW_UPDATE` of 20, then an 8-byte send — the peer's DATA is really emitted
(the pacer moves octets, the counters advance past zero). -/
def demoStart : Flow := Flow.fresh 1000000 10

def demoTrace : List Event :=
  [ .send [1, 2, 3, 4] 16384
  , .strUpdate 20
  , .send [5, 6, 7, 8, 9, 10, 11, 12] 16384 ]

/-- The demo start is well-formed. -/
theorem demoStart_WF : demoStart.WF := by
  refine Flow.fresh_WF ?_ ?_ ?_ ?_ <;> decide

/-- The bound is **non-vacuous**: on the demo trace the stream really sends 12
octets (> 0), and that is `≤ 10 + 20 = 30`. -/
theorem demo_sent_pos : (demoStart.run demoTrace).strSent = 12 := by decide

theorem demo_bound :
    (demoStart.run demoTrace).strSent ≤
      (demoStart.run demoTrace).strInit + (demoStart.run demoTrace).strCredit :=
  window_never_exceeded demoStart_WF

/-- And the enforcement is real: on the demo trace `12 ≤ 30`, strictly below the
granted total, with credit actually accrued. -/
theorem demo_credited : (demoStart.run demoTrace).strCredit = 20 := by decide

end FlowWindow
end H2
