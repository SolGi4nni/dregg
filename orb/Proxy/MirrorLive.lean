/-
# MirrorLive — driving the PROVEN traffic-mirror / shadow FSM over the byte level

Traffic mirroring ("request shadowing") duplicates a live request to a SHADOW
backend so the shadow can be exercised with production traffic — a canary, a new
build, a regression differ — WITHOUT the shadow ever being on the client's
critical path.
The two load-bearing guarantees, and the ways a naive fanout gets them wrong:

  1. FIRE-AND-FORGET — the shadow's response is DISCARDED. The client sees the
     PRIMARY response and only the primary response; the shadow's body, status,
     latency, and failures are invisible to the client. A fanout that waits on
     the shadow, or lets a slow/failed shadow bleed into the client answer, has
     coupled a non-critical experiment to production availability — the exact
     outage mirroring is supposed to make impossible.

  2. FAITHFUL DUPLICATION — when the request IS mirrored, the shadow receives a
     byte-exact copy of what the primary received (same method, path, body): the
     shadow is being tested against real traffic, not a mutated re-render. (This
     is why mirroring a NON-idempotent method duplicates its side effect on the
     shadow — the named residual below, grounded in `Proxy.RetryBudget.Method`.)

The machine is sans-IO in the `Proxy.RetryBudget` / `Proxy.Breaker` style: the
environment injects events (a request arrives and is dispatched, the primary
answers, the shadow answers, the shadow fails) and the machine is a pure step
function with explicit client-visible state. It COMPOSES with the fabric — the
`Method` idempotency algebra is reused verbatim from `Proxy.RetryBudget`.

Headline results:

  * `mirror_duplicates` — when a request is mirrored, the bytes dispatched to the
    shadow are IDENTICAL to the bytes dispatched to the primary (a byte-exact
    duplicate); `mirror_disabled_no_shadow` shows the config gate has content
    (disabled ⇒ no shadow dispatch at all);
  * `mirror_no_client_effect` — removing EVERY shadow event from a run leaves the
    client-visible transcript unchanged: the shadow (its responses, its
    failures) has zero effect on the client. `shadow_fail_no_client_effect` and
    `shadow_resp_no_client_effect` make the pointwise form concrete — a single
    shadow failure, resp. a single discarded shadow response, never perturbs the
    client transcript;
  * `run_clientLog` — the characterization the two headlines rest on: after any
    event trace the client transcript is EXACTLY the primary responses, in order
    (`clientTranscript`), a pure function of the primary events alone.

Non-vacuity is witnessed by concrete runs and by two mutant machines — a
`leakyStep` that delivers the shadow response to the client, and a `mangleDispatch`
that mutates the shadow copy — each of which provably violates the corresponding
headline.

## Honesty / realization boundary (the FabricLive / drorb-native discipline)

This is **drorb-native** and **pure** (NO crypto, NO FFI on the running path):
the mirror FSM is pure decision logic, so the whole `selftest` runs under the
plain Lean interpreter (`lake env lean --run`) with no sockets and no crypto.
Everything structural is the proven Lean; the only gap the selftest discharges
by construction (not by proof) is that this exe faithfully CALLS the proven
functions on real bytes. The faithfulness of the dispatch/no-client-effect
composition ITSELF is proven below.

REAL FINDING (reported, not papered over): the *deployed* drorb serve has NO
traffic-mirror stage today — `grep -rin mirror|shadow` over `Route`,
`RouteAdvanced`, `Dsl/*`, and `crates/dataplane` finds only the word "mirrors"
in prose and unrelated build tooling. So `px.mirror` is realized here at RUNG 2
(a drorb-native selftest of the proven inert FSM), NOT in the deployed serve.
This lane proves the FSM and its two safety properties; wiring a mirror Stage
into `deployStages` is a separate, named residual.

Usage:
  mirror-live selftest
-/
import Proxy.RetryBudget

namespace Proxy.MirrorLive

open Proxy.RetryBudget (Method)

/-- A request, at the byte level: an HTTP method (reused from the fabric's
idempotency algebra) plus the request-line path and the body bytes. -/
structure Req where
  method : Method
  path : List UInt8
  body : List UInt8
deriving DecidableEq, Repr, Inhabited

/-! ## §1  Dispatch — the fanout with faithful duplication

A request is always dispatched to the PRIMARY. It is ALSO dispatched to the
shadow iff mirroring is enabled and the request is sampled. When it is, the
shadow copy is byte-identical to the primary copy. -/

/-- Mirror configuration: an on/off gate and a sampling fraction `sampleNum /
sampleDen` (a request whose sample hash `h` satisfies `h % sampleDen < sampleNum`
is mirrored; `sampleDen = 0` disables sampling). -/
structure MirrorCfg where
  enabled : Bool
  sampleNum : Nat
  sampleDen : Nat
deriving Repr, DecidableEq

/-- Whether a request with sample hash `h` is mirrored under `cfg`. -/
def MirrorCfg.mirrors (cfg : MirrorCfg) (h : Nat) : Bool :=
  cfg.enabled && decide (0 < cfg.sampleDen) && decide (h % cfg.sampleDen < cfg.sampleNum)

/-- The result of dispatching one request: the primary copy (always) and,
optionally, the shadow copy. -/
structure Dispatch where
  toPrimary : Req
  toShadow : Option Req
deriving DecidableEq, Repr

/-- Dispatch a request: the primary always gets it; the shadow gets a byte-exact
copy iff `cfg.mirrors h`. -/
def dispatch (cfg : MirrorCfg) (h : Nat) (req : Req) : Dispatch :=
  { toPrimary := req,
    toShadow := if cfg.mirrors h then some req else none }

/-- **THEOREM 1 — FAITHFUL DUPLICATION.** When a request is mirrored, the bytes
handed to the shadow are IDENTICAL to the bytes handed to the primary — same
method, same path, same body. The shadow is exercised with the real request, not
a re-render of it. -/
theorem mirror_duplicates (cfg : MirrorCfg) (h : Nat) (req : Req) {sreq : Req}
    (hs : (dispatch cfg h req).toShadow = some sreq) :
    sreq = (dispatch cfg h req).toPrimary ∧ sreq = req := by
  simp only [dispatch] at hs ⊢
  by_cases hm : cfg.mirrors h
  · simp only [hm, if_true, Option.some.injEq] at hs
    exact ⟨hs.symm, hs.symm⟩
  · simp [hm] at hs

/-- The config gate has content: with mirroring disabled, NO shadow copy is
dispatched (`mirror_duplicates` is therefore not vacuously about the empty case). -/
theorem mirror_disabled_no_shadow (h : Nat) (req : Req) (n d : Nat) :
    (dispatch ⟨false, n, d⟩ h req).toShadow = none := by
  simp [dispatch, MirrorCfg.mirrors]

/-- Non-vacuity of duplication: an ENABLED, fully-sampled config genuinely
mirrors — the shadow gets a copy, and it equals the primary. -/
theorem mirror_enabled_duplicates (h : Nat) (req : Req) :
    (dispatch ⟨true, 1, 1⟩ h req).toShadow = some req := by
  simp [dispatch, MirrorCfg.mirrors, Nat.mod_one]

/-! ## §2  The client-visible FSM — the shadow is fire-and-forget

The lifecycle machine steps on events. Its state carries the CLIENT-visible
transcript (the ordered list of responses actually delivered to the client) plus
internal shadow bookkeeping that the client never sees. Only a PRIMARY response
appends to the client transcript; shadow responses and shadow failures touch
only the internal bookkeeping. -/

/-- Lifecycle events injected by the environment. -/
inductive MEvent where
  /-- A request arrived and was dispatched (bookkeeping; not client-visible). -/
  | request (d : Dispatch)
  /-- The primary produced the client-facing response bytes. -/
  | primaryResp (resp : List UInt8)
  /-- The shadow produced a response — to be DISCARDED (never client-visible). -/
  | shadowResp (resp : List UInt8)
  /-- The shadow failed / timed out — never surfaced to the client. -/
  | shadowFail
deriving Repr

/-- Machine state: the client-visible response transcript, the (internal) shadow
response log, and a shadow-failure counter. -/
structure MState where
  clientLog : List (List UInt8)   -- responses actually delivered to the client
  shadowLog : List (List UInt8)   -- shadow responses observed (internal only)
  shadowFails : Nat               -- shadow failures observed (internal only)
deriving DecidableEq, Repr

/-- The fresh machine. -/
def MState.init : MState := ⟨[], [], 0⟩

/-- One step of the mirror lifecycle machine. Only `primaryResp` touches the
client transcript; the shadow arms touch internal bookkeeping ONLY. -/
def step (s : MState) : MEvent → MState
  | .request _      => s
  | .primaryResp r  => { s with clientLog := s.clientLog ++ [r] }
  | .shadowResp r   => { s with shadowLog := s.shadowLog ++ [r] }   -- DISCARDED
  | .shadowFail     => { s with shadowFails := s.shadowFails + 1 }  -- never client-visible

/-- Run an event history, oldest first. -/
def run (s : MState) : List MEvent → MState
  | [] => s
  | e :: es => run (step s e) es

@[simp] theorem run_nil (s : MState) : run s [] = s := rfl

@[simp] theorem run_cons (s : MState) (e : MEvent) (es : List MEvent) :
    run s (e :: es) = run (step s e) es := rfl

/-! ## §3  The client transcript is exactly the primary responses -/

/-- The client-affecting payload of an event: only a primary response carries
one. Shadow events carry `none` — they never reach the client. -/
def primaryOf : MEvent → Option (List UInt8)
  | .primaryResp r => some r
  | _ => none

/-- Is this event a shadow event (a shadow response or a shadow failure)? -/
def isShadow : MEvent → Bool
  | .shadowResp _ => true
  | .shadowFail   => true
  | _ => false

/-- The client transcript predicted from a trace: the primary responses, in
order. This is the ONLY thing the client sees. -/
def clientTranscript (trace : List MEvent) : List (List UInt8) :=
  trace.filterMap primaryOf

/-- **CHARACTERIZATION.** After any event trace, the machine's client transcript
is EXACTLY the initial transcript followed by the primary responses in order — a
pure function of the primary events, with the shadow events contributing nothing. -/
theorem run_clientLog (s : MState) (trace : List MEvent) :
    (run s trace).clientLog = s.clientLog ++ clientTranscript trace := by
  induction trace generalizing s with
  | nil => simp [clientTranscript]
  | cons e es ih =>
    cases e with
    | request d => simp [step, clientTranscript, primaryOf, ih]
    | primaryResp r =>
      simp [step, clientTranscript, primaryOf, ih, List.append_assoc]
    | shadowResp r => simp [step, clientTranscript, primaryOf, ih]
    | shadowFail => simp [step, clientTranscript, primaryOf, ih]

/-! ## §4  No client effect — the shadow never perturbs the client -/

/-- Filtering out elements that `filterMap` already drops (map to `none`) leaves
the `filterMap` result unchanged. -/
theorem filterMap_filter_none {α β} (f : α → Option β) (p : α → Bool) (l : List α)
    (h : ∀ x, p x = false → f x = none) :
    (l.filter p).filterMap f = l.filterMap f := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    by_cases hp : p a
    · simp only [List.filter_cons, hp, if_true, List.filterMap_cons, ih]
    · have hpf : p a = false := by simpa using hp
      simp [List.filter_cons, hpf, List.filterMap_cons, h a hpf, ih]

/-- Dropping every shadow event from a trace does not change the client
transcript, since shadow events carry no primary payload. -/
theorem clientTranscript_dropShadow (trace : List MEvent) :
    clientTranscript (trace.filter (fun e => !isShadow e)) = clientTranscript trace := by
  unfold clientTranscript
  apply filterMap_filter_none
  intro x hx
  cases x with
  | request d => simp [isShadow] at hx
  | primaryResp r => simp [isShadow] at hx
  | shadowResp r => rfl
  | shadowFail => rfl

/-- **THEOREM 2 — NO CLIENT EFFECT (FIRE-AND-FORGET).** Removing EVERY shadow
event from an event history leaves the client-visible transcript IDENTICAL. The
shadow — its responses, its failures, its latency — has zero effect on what the
client sees; the client answer is a pure function of the primary path. -/
theorem mirror_no_client_effect (s : MState) (trace : List MEvent) :
    (run s (trace.filter (fun e => !isShadow e))).clientLog = (run s trace).clientLog := by
  rw [run_clientLog, run_clientLog, clientTranscript_dropShadow]

/-- **POINTWISE — a shadow FAILURE never affects the client.** Injecting a shadow
failure anywhere in a run leaves the client transcript unchanged. This is the
guarantee that a broken/slow shadow can never take down the client path. -/
theorem shadow_fail_no_client_effect (s : MState) (pre post : List MEvent) :
    (run s (pre ++ MEvent.shadowFail :: post)).clientLog = (run s (pre ++ post)).clientLog := by
  simp only [run_clientLog, clientTranscript, List.filterMap_append, List.filterMap_cons,
    primaryOf]

/-- **POINTWISE — a discarded shadow RESPONSE never affects the client.**
Injecting a shadow response anywhere in a run leaves the client transcript
unchanged: the shadow body is discarded, never delivered. -/
theorem shadow_resp_no_client_effect (s : MState) (pre post : List MEvent) (r : List UInt8) :
    (run s (pre ++ MEvent.shadowResp r :: post)).clientLog = (run s (pre ++ post)).clientLog := by
  simp only [run_clientLog, clientTranscript, List.filterMap_append, List.filterMap_cons,
    primaryOf]

/-! ## §5  Non-vacuity: two mutant machines fail the two headlines -/

/-- Mutant A — LEAKY SHADOW: delivers the shadow response to the client (appends
it to the client transcript instead of discarding it). -/
def leakyStep (s : MState) : MEvent → MState
  | .shadowResp r => { s with clientLog := s.clientLog ++ [r] }  -- LEAK: client sees the shadow
  | e => step s e

def leakyRun (s : MState) : List MEvent → MState
  | [] => s
  | e :: es => leakyRun (leakyStep s e) es

/-- The leaky machine DELIVERS a shadow response to the client (its transcript
gains the shadow bytes), whereas the correct machine discards it — so
`shadow_resp_no_client_effect` has genuine content, not `spec = spec`. -/
theorem leaky_breaks_no_client_effect :
    let trace : List MEvent := [.primaryResp [0x50], .shadowResp [0x53]]
    (leakyRun MState.init trace).clientLog = [[0x50], [0x53]]
      ∧ (run MState.init trace).clientLog = [[0x50]] := by
  decide

/-- Mutant B — MANGLING DISPATCH: sends a MUTATED copy to the shadow (drops the
body) instead of a byte-exact duplicate. -/
def mangleDispatch (req : Req) : Dispatch :=
  { toPrimary := req, toShadow := some { req with body := [] } }

/-- With a non-empty body, the mangling dispatch's shadow copy DIFFERS from the
primary, whereas the correct `dispatch` (enabled) sends an identical copy — so
`mirror_duplicates` is genuine content. -/
theorem mangle_breaks_duplication :
    let req : Req := ⟨Method.get, [0x2f], [0x68, 0x69]⟩
    (mangleDispatch req).toShadow ≠ some req
      ∧ (dispatch ⟨true, 1, 1⟩ 0 req).toShadow = some req := by
  decide

/-! ## §6  The selftest — the mirror FSM over the byte level, one process, NO crypto -/

/-- Render a byte list that is UTF-8 text as text, else a short debug form. -/
def textOf (b : List UInt8) : String :=
  (String.fromUTF8? ⟨b.toArray⟩).getD (toString b)

def selftest : IO UInt32 := do
  IO.println "== mirror-live selftest : traffic-mirror / shadow FSM, byte-level, NO crypto =="

  -- ── a live request, dispatched under an ENABLED, fully-sampled mirror ──
  let req : Req := ⟨Method.get, "/health".toUTF8.toList, "ping".toUTF8.toList⟩
  let cfg : MirrorCfg := ⟨true, 1, 1⟩
  let disp := dispatch cfg 0 req
  IO.println s!"\n-- dispatch (mirror enabled, sampled) --"
  IO.println s!"primary path/body      : {textOf disp.toPrimary.path} / {textOf disp.toPrimary.body}"
  let dupOk ←
    match disp.toShadow with
    | some sreq => do
        let ok := (sreq == req) && (sreq == disp.toPrimary)
        IO.println s!"shadow  path/body      : {textOf sreq.path} / {textOf sreq.body}"
        IO.println s!"shadow == primary (byte-exact duplicate)   : {ok}  [realizes mirror_duplicates]"
        pure ok
    | none => do IO.eprintln "shadow copy MISSING under enabled mirror"; pure false

  -- ── the config gate has content: DISABLED ⇒ no shadow dispatch ──
  let dispOff := dispatch ⟨false, 1, 1⟩ 0 req
  let gateOk := dispOff.toShadow == none
  IO.println s!"disabled ⇒ no shadow dispatch               : {gateOk}  [realizes mirror_disabled_no_shadow]"

  -- ── an event history: primary answers; the shadow answers AND fails, interleaved ──
  let primaryBody := "200 OK from PRIMARY".toUTF8.toList
  let shadowBody  := "500 ERR from shadow (discarded)".toUTF8.toList
  let trace : List MEvent :=
    [ .request disp,
      .shadowResp shadowBody,          -- discarded
      .primaryResp primaryBody,        -- the ONLY client-visible response
      .shadowFail ]                    -- shadow failure — must not affect the client
  let final := run MState.init trace
  IO.println s!"\n-- run the lifecycle FSM over the interleaved trace --"
  IO.println s!"client transcript      : {final.clientLog.map textOf}"
  IO.println s!"shadow log (internal)  : {final.shadowLog.map textOf}"
  IO.println s!"shadow failures        : {final.shadowFails}"

  -- ── no-client-effect: drop EVERY shadow event, the client transcript is unchanged ──
  let traceNoShadow := trace.filter (fun e => !isShadow e)
  let noEffect := (run MState.init traceNoShadow).clientLog == final.clientLog
  let clientOnlyPrimary := final.clientLog == [primaryBody]
  IO.println s!"\n-- no-client-effect cross-check (realizes mirror_no_client_effect) --"
  IO.println s!"client transcript == primary-only            : {clientOnlyPrimary}"
  IO.println s!"drop all shadow events ⇒ same client log      : {noEffect}"

  -- ── pointwise: flip the shadow FAILURE into a shadow SUCCESS — client unchanged ──
  let traceFlip : List MEvent :=
    [ .request disp, .shadowResp shadowBody, .primaryResp primaryBody, .shadowResp shadowBody ]
  let flipSame := (run MState.init traceFlip).clientLog == final.clientLog
  IO.println s!"shadow fail⇄success ⇒ same client log         : {flipSame}  [realizes shadow_*_no_client_effect]"

  -- ── the leaky mutant DELIVERS the shadow to the client (must DIFFER) ──
  let leaked := (leakyRun MState.init trace).clientLog
  let leakDiffers := leaked != final.clientLog
  IO.println s!"\n-- mutant cross-check (non-vacuity) --"
  IO.println s!"leaky-shadow client log DIFFERS from correct : {leakDiffers}  (leaky={leaked.map textOf})"

  if dupOk && gateOk && noEffect && clientOnlyPrimary && flipSame && leakDiffers then do
    IO.println "\nPASS — request duplicated byte-exact to the shadow; the shadow response is"
    IO.println "       discarded and its failure never reaches the client; the client transcript"
    IO.println "       equals the proven primary-only decision (mirror_no_client_effect / mirror_duplicates)."
    IO.println "TRAFFIC-MIRROR FSM LIVE-WIRED (drorb-native rung 2, byte-level, NO crypto)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the mirror FSM did not cross-check."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do
    IO.eprintln "usage: mirror-live selftest"
    return 1

#print axioms mirror_duplicates
#print axioms mirror_no_client_effect
#print axioms shadow_fail_no_client_effect
#print axioms run_clientLog

end Proxy.MirrorLive

def main (args : List String) : IO UInt32 := Proxy.MirrorLive.main args
