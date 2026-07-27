/-
HedgedRequest — hedged (raced) and shadow (mirrored) request dispatch for a
reverse proxy, as a pure, crypto-free, sans-IO transition system.

Tail latency in a fan-out service is dominated not by the median backend but by
the slowest of the backends a request touches ("The Tail at Scale", Dean &
Barroso, CACM 2013). Two well-known mitigations sit at the proxy:

  * HEDGED requests — dispatch the request to a primary backend and, rather than
    wait out a slow tail, RACE a *duplicate* to a second backend. Whichever
    responds first is the client's answer; the loser is CANCELLED so it stops
    consuming an upstream slot. Left unmetered this doubles offered load, so the
    number of hedges is capped by a budget (`maxHedges`).

  * SHADOW / MIRROR requests — dispatch a *copy* of live traffic to a candidate
    backend (a canary, a new build, a migration target) purely to observe it.
    A shadow response is DISCARDED: it must never become the client's answer and
    must never perturb the winner. Getting this wrong turns a passive experiment
    into a correctness incident.

The machine is sans-IO in the `Proxy.RetryBudget` / `Proxy.Breaker` style: the
environment injects events (dispatch the primary, fire a hedge, fire a shadow, a
backend responds) and the machine is a pure step function with an explicit
output. It carries NO crypto and no I/O — it decides *which* attempts are in
flight, *which* response wins, and *which* are cancelled or discarded.

Headline results:

  * `hedge_first_wins` — with a primary and a hedge both in flight, the FIRST
    response to arrive becomes the winner and the losing attempt is CANCELLED;
    the emitted output is `won`. A concrete two-backend race witnesses it end to
    end (`hedge_race_witness`).

  * `hedge_bounded` — over ANY event history the number of hedges dispatched is
    `≤ maxHedges`: the duplicate load a hedging proxy adds is capped by the
    budget, never an unbounded multiple. The `unbudgetedHedge` mutant, which
    hedges without the budget check, provably exceeds it.

  * `shadow_no_client_effect` — when the responding attempt is a shadow, the
    step leaves the winner field UNCHANGED and emits `discarded`: a shadow
    response can neither become the client answer nor displace an existing one.
    The `shadowWins` mutant, which lets a shadow win, provably diverges.

Non-vacuity is witnessed by concrete runs and by two mutant machines (one that
ignores the hedge budget, one that lets a shadow win), each of which provably
violates the corresponding headline. No `native_decide`, no crypto FFI: the
selftest drives the FSM over a self-delimiting byte codec under the pure
interpreter (`lake env lean --run`).
-/

import Control
import Proxy.RetryBudget

namespace Proxy.HedgedRequest

open Control (Bytes putNat getNat putSeq getSeq getNat_putNat getSeq_putSeq)

/-! ## §1  The model -/

/-- A backend the proxy can dispatch to (config index / hash-ring identity). -/
abbrev BackendId := Nat

/-- An opaque response token (the payload the backend returned). Modelled as a
`Nat` so the machine can compare *which* response is the client's answer without
committing to a wire format for the body. -/
abbrev Resp := Nat

/-- Why an attempt was dispatched. The role fixes what a response is allowed to
do: a `primary` or `hedge` response may WIN (become the client answer); a
`shadow` response is observed-only and is always DISCARDED. -/
inductive Role where
  | primary   -- the original request
  | hedge     -- a duplicate raced against the primary; may win
  | shadow    -- a mirror; its response is discarded, never wins
deriving DecidableEq, Repr, Inhabited, BEq

/-- One in-flight upstream attempt: which backend, dispatched in which role. -/
structure Attempt where
  id : BackendId
  role : Role
deriving DecidableEq, Repr, Inhabited, BEq

/-- Hedge configuration. `maxHedges` is the budget: at most this many *duplicate*
(hedge) attempts may be dispatched over the life of the machine. -/
structure HedgeCfg where
  maxHedges : Nat
deriving DecidableEq, Repr

/-- Machine state: the currently-outstanding attempts, the ids that were
cancelled because a winner emerged, the client-facing winner (the first
non-shadow response), and the running count of hedges dispatched. -/
structure HState where
  inflight : List Attempt              -- outstanding attempts
  cancelled : List BackendId           -- attempts cancelled once a winner emerged
  winner : Option (BackendId × Resp)   -- the client-facing response
  hedges : Nat                         -- total hedges dispatched (accounting)
deriving Repr, BEq

/-- A fresh machine: nothing in flight, no winner, no hedges spent. -/
def HState.init : HState :=
  { inflight := [], cancelled := [], winner := none, hedges := 0 }

/-- Events injected by the environment. -/
inductive HEvent where
  /-- Dispatch the primary attempt to backend `id`. -/
  | dispatch (id : BackendId)
  /-- Fire a hedge (a duplicate) to backend `id`; charged against `maxHedges`. -/
  | hedge (id : BackendId)
  /-- Fire a shadow/mirror to backend `id`; its response is observed-only. -/
  | shadow (id : BackendId)
  /-- Backend `id` responded with `r`. -/
  | respond (id : BackendId) (r : Resp)
deriving Repr, BEq

/-- Outputs. A step emits exactly one. -/
inductive HOutput where
  | dispatched (a : Attempt)       -- an attempt was launched upstream
  | rejected                       -- dispatch/hedge refused (winner already, or budget spent)
  | won (id : BackendId) (r : Resp)  -- this response became the client answer; losers cancelled
  | discarded (id : BackendId)     -- a shadow response, or a late/unknown response — dropped
deriving DecidableEq, Repr, BEq

/-! ## §2  The step function — the deployed transition

`dispatch`/`hedge` launch attempts (a hedge only under budget); a `respond` for
a non-shadow attempt, while no winner is set, WINS and cancels the rest; a
`respond` for a shadow is always discarded; a late response after a winner is
discarded. -/

/-- One step of the hedge/shadow machine. -/
def step (cfg : HedgeCfg) (s : HState) : HEvent → HState × List HOutput
  | .dispatch id =>
      if s.winner.isSome then (s, [HOutput.rejected])
      else
        let a : Attempt := ⟨id, Role.primary⟩
        ({ s with inflight := a :: s.inflight }, [HOutput.dispatched a])
  | .hedge id =>
      if s.winner.isSome then (s, [HOutput.rejected])
      else if s.hedges < cfg.maxHedges then
        let a : Attempt := ⟨id, Role.hedge⟩
        ({ s with inflight := a :: s.inflight, hedges := s.hedges + 1 },
         [HOutput.dispatched a])
      else (s, [HOutput.rejected])
  | .shadow id =>
      let a : Attempt := ⟨id, Role.shadow⟩
      ({ s with inflight := a :: s.inflight }, [HOutput.dispatched a])
  | .respond id r =>
      match s.inflight.find? (fun a => a.id == id) with
      | none => (s, [HOutput.discarded id])
      | some a =>
        if a.role = Role.shadow then
          -- shadow response: DISCARD; drop it from inflight, never touch winner
          ({ s with inflight := s.inflight.filter (fun a => a.id != id) },
           [HOutput.discarded id])
        else if s.winner.isSome then
          -- a loser arriving after the winner: discard
          ({ s with inflight := s.inflight.filter (fun a => a.id != id) },
           [HOutput.discarded id])
        else
          -- FIRST non-shadow response WINS; cancel every other in-flight attempt
          let losers := (s.inflight.filter (fun a => a.id != id)).map (fun a => a.id)
          ({ s with winner := some (id, r), inflight := [],
                    cancelled := s.cancelled ++ losers },
           [HOutput.won id r])

/-- Run an event history, oldest first, returning the final state. -/
def run (cfg : HedgeCfg) (s : HState) : List HEvent → HState
  | [] => s
  | e :: es => run cfg (step cfg s e).1 es

/-- Run an event history, accumulating every output (for the selftest). -/
def exec (cfg : HedgeCfg) (s : HState) : List HEvent → HState × List HOutput
  | [] => (s, [])
  | e :: es =>
    let (s1, o1) := step cfg s e
    let (s2, o2) := exec cfg s1 es
    (s2, o1 ++ o2)

@[simp] theorem run_nil (cfg : HedgeCfg) (s : HState) : run cfg s [] = s := rfl
@[simp] theorem run_cons (cfg : HedgeCfg) (s : HState) (e : HEvent) (es : List HEvent) :
    run cfg s (e :: es) = run cfg (step cfg s e).1 es := rfl

/-! ## §3  Theorem 1 — the first response wins, the loser is cancelled

With a primary and a hedge both in flight and no winner yet, the first response
to arrive becomes the winner; the emitted output is `won`, and the other backend
is moved into the cancelled set (its attempt is torn down). This is the whole
point of hedging: race two, take the fast one, cancel the slow one. -/

/-- **THEOREM 1 — FIRST RESPONSE WINS, LOSER CANCELLED.** From a state whose only
in-flight attempts are a primary on `id1` and a hedge on `id2` (`id1 ≠ id2`) with
no winner yet, a response from `id1` makes `id1` the winner (output `won id1 r`,
`winner = (id1, r)`) and the losing hedge `id2` is CANCELLED. -/
theorem hedge_first_wins (cfg : HedgeCfg) (id1 id2 : BackendId) (r : Resp)
    (s : HState) (hne : id1 ≠ id2)
    (hin : s.inflight = [⟨id1, Role.primary⟩, ⟨id2, Role.hedge⟩])
    (hw : s.winner = none) :
    (step cfg s (.respond id1 r)).2 = [HOutput.won id1 r]
      ∧ (step cfg s (.respond id1 r)).1.winner = some (id1, r)
      ∧ id2 ∈ (step cfg s (.respond id1 r)).1.cancelled := by
  have hbe : (id2 == id1) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => hne h.symm
  simp only [step, hin, hw, List.find?, beq_self_eq_true, Option.isSome_none,
    Bool.false_eq_true, if_false, List.filter, bne, hbe, Bool.not_false,
    Bool.not_true, List.map_cons, List.map_nil]
  refine ⟨rfl, rfl, ?_⟩
  simp

/-! ## §4  Theorem 2 — the hedge budget is bounded (no unbounded duplication)

The number of hedges dispatched never exceeds `maxHedges`. A hedge is only
launched inside the `s.hedges < maxHedges` guard, so the counter lands at most at
the budget; every other event leaves it untouched. Hence a hedging proxy adds at
most `maxHedges` duplicate requests — a bounded increment, not a per-request
multiplier. -/

/-- The budget invariant. -/
def HedgeBounded (cfg : HedgeCfg) (s : HState) : Prop := s.hedges ≤ cfg.maxHedges

/-- The invariant holds at the fresh state. -/
theorem hedgeBounded_init (cfg : HedgeCfg) : HedgeBounded cfg HState.init :=
  Nat.zero_le _

/-- Every step preserves the hedge-budget invariant. The hedge case is the only
one that spends the counter, and it does so under the `< maxHedges` guard. -/
theorem step_hedgeBounded (cfg : HedgeCfg) (s : HState) (e : HEvent)
    (h : HedgeBounded cfg s) : HedgeBounded cfg (step cfg s e).1 := by
  unfold HedgeBounded at h ⊢
  cases e with
  | dispatch id =>
      simp only [step]; split <;> simpa using h
  | hedge id =>
      simp only [step]
      split
      · simpa using h
      · split
        · rename_i hlt; simp only; omega
        · simpa using h
  | shadow id => simp only [step]; simpa using h
  | respond id r =>
      simp only [step]
      split
      · simpa using h
      · rename_i a _
        split
        · simpa using h
        · split <;> simpa using h

/-- **THEOREM 2 — BOUNDED HEDGE BUDGET.** For any configuration and any event
history, the number of hedges dispatched never exceeds `maxHedges`: the duplicate
load a hedging proxy offers is capped by the budget, not an unbounded multiple of
traffic. -/
theorem hedge_bounded (cfg : HedgeCfg) (trace : List HEvent) :
    (run cfg HState.init trace).hedges ≤ cfg.maxHedges :=
  go cfg HState.init (hedgeBounded_init cfg) trace
where
  go (cfg : HedgeCfg) (s : HState) (h : HedgeBounded cfg s) :
      (trace : List HEvent) → (run cfg s trace).hedges ≤ cfg.maxHedges
    | [] => h
    | e :: es => by
      rw [run_cons]; exact go cfg (step cfg s e).1 (step_hedgeBounded cfg s e h) es

/-! ## §5  Theorem 3 — a shadow response has no client effect

When the responding attempt is a shadow, the step leaves the winner field
unchanged and emits `discarded`: a mirror can neither become the client answer
nor displace an existing one. Mirrored traffic is a passive observation, exactly
as a canary/migration shadow must be. -/

/-- **THEOREM 3 — SHADOW HAS NO CLIENT EFFECT.** If the in-flight attempt that
`id` resolves to is a shadow, then responding for it leaves the winner UNCHANGED
and emits `discarded id` — never `won`. A shadow response cannot set, change, or
displace the client-facing answer. -/
theorem shadow_no_client_effect (cfg : HedgeCfg) (s : HState) (id : BackendId)
    (r : Resp) (a : Attempt)
    (hfind : s.inflight.find? (fun a => a.id == id) = some a)
    (hrole : a.role = Role.shadow) :
    (step cfg s (.respond id r)).1.winner = s.winner
      ∧ (step cfg s (.respond id r)).2 = [HOutput.discarded id] := by
  constructor <;> simp [step, hfind, hrole]

/-! ## §6  Non-vacuity — concrete race, and two mutant machines

The theorems above carry real hypotheses (not `P → P`). These concrete runs and
mutants pin them to genuine content. -/

/-- A concrete two-backend hedged race from a fresh machine: dispatch to #1,
hedge to #2, #1 responds first, #2 responds late. #1 wins, #2 is cancelled, the
late #2 response is discarded, and exactly one hedge was spent (within budget).
This witnesses `hedge_first_wins` (and `hedge_bounded`) end to end. -/
theorem hedge_race_witness :
    let cfg : HedgeCfg := ⟨2⟩
    let final := run cfg HState.init [.dispatch 1, .hedge 2, .respond 1 100, .respond 2 200]
    final.winner = some (1, 100) ∧ 2 ∈ final.cancelled ∧ final.hedges = 1 := by
  decide

/-- The output stream of that race: two dispatches, a `won 1 100`, then the late
#2 response is `discarded`. -/
theorem hedge_race_outputs :
    let cfg : HedgeCfg := ⟨2⟩
    (exec cfg HState.init [.dispatch 1, .hedge 2, .respond 1 100, .respond 2 200]).2
      = [HOutput.dispatched ⟨1, Role.primary⟩, HOutput.dispatched ⟨2, Role.hedge⟩,
         HOutput.won 1 100, HOutput.discarded 2] := by
  decide

/-- Mutant A — IGNORES THE HEDGE BUDGET: fires every hedge with no budget check. -/
def unbudgetedHedgeStep (cfg : HedgeCfg) (s : HState) : HEvent → HState × List HOutput
  | .hedge id =>
      let a : Attempt := ⟨id, Role.hedge⟩
      ({ s with inflight := a :: s.inflight, hedges := s.hedges + 1 },
       [HOutput.dispatched a])
  | e => step cfg s e

def unbudgetedHedgeRun (cfg : HedgeCfg) (s : HState) : List HEvent → HState
  | [] => s
  | e :: es => unbudgetedHedgeRun cfg (unbudgetedHedgeStep cfg s e).1 es

/-- With `maxHedges = 1`, firing two hedges drives the budget-ignoring machine to
2 hedges, exceeding the budget — whereas the correct machine stays `≤ 1`
(`hedge_bounded`). So the budget bound has genuine content. -/
theorem unbudgetedHedge_breaks_budget :
    let cfg : HedgeCfg := ⟨1⟩
    (unbudgetedHedgeRun cfg HState.init [.hedge 1, .hedge 2]).hedges > cfg.maxHedges
      ∧ (run cfg HState.init [.hedge 1, .hedge 2]).hedges ≤ cfg.maxHedges := by
  decide

/-- Mutant B — LETS A SHADOW WIN: treats a shadow response like a real one, so a
mirror can become the client answer. -/
def shadowWinsStep (cfg : HedgeCfg) (s : HState) : HEvent → HState × List HOutput
  | .respond id r =>
      match s.inflight.find? (fun a => a.id == id) with
      | none => (s, [HOutput.discarded id])
      | some _ =>
        if s.winner.isSome then
          ({ s with inflight := s.inflight.filter (fun a => a.id != id) },
           [HOutput.discarded id])
        else
          ({ s with winner := some (id, r), inflight := [] }, [HOutput.won id r])
  | e => step cfg s e

/-- With only a shadow in flight, the shadow-wins machine makes the shadow the
winner, which the correct machine never does (`shadow_no_client_effect` keeps the
winner `none`): the two disagree, so "a shadow never wins" is genuine content. -/
theorem shadowWins_breaks_shadow :
    let cfg : HedgeCfg := ⟨2⟩
    let s : HState := (step cfg HState.init (.shadow 9)).1
    (shadowWinsStep cfg s (.respond 9 500)).1.winner = some (9, 500)
      ∧ (step cfg s (.respond 9 500)).1.winner = none := by
  decide

/-! ## §7  A self-delimiting event-trace codec (over the proven codec algebra)

`Control` gives round-tripping field codecs (`putNat`/`getNat`) and the generic
length-prefixed sequence codec (`putSeq`/`getSeq`). An `HEvent` is a tag byte
plus its `Nat` fields; a trace is `putSeq putEvent`. Each piece carries its own
round-trip theorem, chaining to `getTrace_put` — so the byte-driven selftest runs
the SAME events the model does. No crypto: pure varint framing. -/

/-- `HEvent` framing: a tag byte selects the arm, then the field(s). -/
def putEvent : HEvent → Bytes
  | .dispatch id  => putNat 0 ++ putNat id
  | .hedge id     => putNat 1 ++ putNat id
  | .shadow id    => putNat 2 ++ putNat id
  | .respond id r => putNat 3 ++ putNat id ++ putNat r

def getEvent (bs : Bytes) : Option (HEvent × Bytes) :=
  match getNat bs with
  | some (0, r) => match getNat r with
    | some (id, r2) => some (.dispatch id, r2) | none => none
  | some (1, r) => match getNat r with
    | some (id, r2) => some (.hedge id, r2) | none => none
  | some (2, r) => match getNat r with
    | some (id, r2) => some (.shadow id, r2) | none => none
  | some (3, r) => match getNat r with
    | some (id, r2) => match getNat r2 with
      | some (rr, r3) => some (.respond id rr, r3) | none => none
    | none => none
  | _ => none

/-- **The `HEvent` wire round-trip.** -/
theorem getEvent_put (e : HEvent) (t : Bytes) : getEvent (putEvent e ++ t) = some (e, t) := by
  cases e <;>
    simp only [putEvent, getEvent, List.append_assoc, getNat_putNat]

/-- A trace is a length-prefixed sequence of events. -/
def putTrace (es : List HEvent) : Bytes := putSeq putEvent es
def getTrace (bs : Bytes) : Option (List HEvent × Bytes) := getSeq getEvent bs

/-- **The trace wire round-trip**, from the sequence codec + the event codec. -/
theorem getTrace_put (es : List HEvent) (t : Bytes) :
    getTrace (putTrace es ++ t) = some (es, t) :=
  getSeq_putSeq putEvent getEvent getEvent_put es t

/-- **FAITHFULNESS — the wire realizes the model.** Decoding a serialized trace
and running the hedge FSM over the decoded events produces EXACTLY the state the
model computes over the original events. The byte layer changes nothing but the
representation; the decision (winner, cancelled, hedges) is identical. Mediated
only by the proven codec round-trip (`getTrace_put`) — not a `P → P`: it is a
real equation over every `cfg`, `trace`, and trailing `t`, inhabited by the
selftest's concrete buffer. -/
theorem hedge_wire_faithful (cfg : HedgeCfg) (trace : List HEvent) (t : Bytes) :
    (getTrace (putTrace trace ++ t)).map (fun p => exec cfg HState.init p.1)
      = some (exec cfg HState.init trace) := by
  rw [getTrace_put]; rfl

/-! ## §8  Rendering helpers (pure) -/

def showRole : Role → String
  | .primary => "primary" | .hedge => "hedge" | .shadow => "shadow"

def showAttempt (a : Attempt) : String := s!"#{a.id}/{showRole a.role}"

def showOutput : HOutput → String
  | .dispatched a => s!"dispatched {showAttempt a}"
  | .rejected     => "rejected"
  | .won id r     => s!"won #{id} r={r}"
  | .discarded id => s!"discarded #{id}"

def showWinner : Option (BackendId × Resp) → String
  | none => "(none)"
  | some (id, r) => s!"#{id} r={r}"

def toHex (b : Bytes) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

/-! ## §9  The selftest — the hedge FSM over the byte level, one process, NO crypto -/

def selftest : IO UInt32 := do
  IO.println "== hedged-request-live selftest : hedge/shadow dispatch FSM, byte-level, NO crypto =="

  let cfg : HedgeCfg := ⟨2⟩   -- budget: at most 2 hedges

  -- ── the injected history ──
  -- primary→#1; hedge→#2 (race); shadow→#9 (mirror); #2 wins the race;
  -- #9 (shadow) responds late — must be discarded; #1 responds late — discarded.
  let trace : List HEvent :=
    [.dispatch 1, .hedge 2, .shadow 9, .respond 2 200, .respond 9 500, .respond 1 100]

  IO.println s!"\n-- injected history ({trace.length} events), budget maxHedges={cfg.maxHedges} --"

  -- ── serialize the trace, decode it back over the proven codec ──
  let wire := putTrace trace
  IO.println s!"-- trace serialized (putTrace) --"
  IO.println s!"wire bytes             : {wire.length}B  {toHex (wire.take 24)}…"
  let some (decoded, rest) := getTrace wire
    | do IO.eprintln "getTrace FAILED to decode the trace"; return 1
  let decodeOk := rest.isEmpty && (decoded == trace)
  IO.println s!"getTrace∘putTrace == trace (wire round-trip realized) : {decodeOk}"
  if !decodeOk then do IO.eprintln "trace did NOT round-trip"; return 1

  -- ── drive the FSM over the DECODED bytes ──
  let (final, outs) := exec cfg HState.init decoded
  IO.println "\n-- FSM driven over the decoded bytes --"
  for o in outs do IO.println s!"  → {showOutput o}"
  IO.println s!"winner                 : {showWinner final.winner}"
  IO.println s!"cancelled              : {final.cancelled}"
  IO.println s!"hedges spent           : {final.hedges} / {cfg.maxHedges}"

  -- ── the three guarantees, observed on the wire-driven run ──
  -- 1. first response wins, loser cancelled: #2 answered first ⇒ winner #2, #1 cancelled.
  let firstWins := final.winner == some (2, 200) && final.cancelled.contains 1
  -- 2. hedge budget bounded: exactly one hedge fired (#2), ≤ maxHedges.
  let budgetOk := decide (final.hedges ≤ cfg.maxHedges)
  -- 3. shadow no client effect: #9 (shadow) responded but never became winner,
  --    and its response was discarded (not `won`).
  let shadowInert := !(final.winner == some (9, 500)) && outs.contains (.discarded 9)
  IO.println "\n-- guarantees, observed on the wire-driven run --"
  IO.println s!"  first response wins, loser cancelled   (hedge_first_wins)      : {firstWins}"
  IO.println s!"  hedges spent ≤ budget                  (hedge_bounded)         : {budgetOk}"
  IO.println s!"  shadow #9 never client answer, discarded (shadow_no_client…)   : {shadowInert}"

  -- ── faithfulness cross-check: wire-driven run == model run (hedge_wire_faithful) ──
  let modelFinal := (exec cfg HState.init trace)
  let faithful := (final == modelFinal.1) && (outs == modelFinal.2)
  IO.println "\n-- cross-check (realizes hedge_wire_faithful) --"
  IO.println s!"  wire-driven exec == model exec         : {faithful}"

  if decodeOk && firstWins && budgetOk && shadowInert && faithful then do
    IO.println "\nPASS — trace serialized, decoded; hedge FSM driven over the decoded bytes;"
    IO.println "       first-wins / bounded-budget / shadow-inert each observed and cross-checked."
    IO.println "HEDGED/SHADOW DISPATCH LIVE-WIRED (drorb-native, byte-level, NO crypto, verified codec+FSM)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the hedge/shadow pipeline did not cross-check."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do
    IO.eprintln "usage: hedged-request-live selftest"
    return 1

end Proxy.HedgedRequest

def main (args : List String) : IO UInt32 := Proxy.HedgedRequest.main args
