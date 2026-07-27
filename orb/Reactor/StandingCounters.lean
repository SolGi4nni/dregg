import Reactor.Stage.ConnLimit
import Reactor.Stage.StickTable
import Reactor.Stage.Slowloris

/-!
# Reactor.StandingCounters — the accept-path per-source counter store as an LTS

The proven serve stages `Reactor.Stage.ConnLimit` / `StickTable` / `Slowloris`
DECIDE on per-source STANDING state (how many connections a source has open right
now, its aggregated request rate, how long its header phase has run). The sans-IO
serve fold is one stateless `ByteArray → ByteArray` call per request
(`ctxOfMetered` carries only the client IP + a per-connection sequence number), so
that standing state cannot ride the fold — it lives in the ACCEPT PATH, which owns
the connection lifecycle. This file models that accept-path store, mirroring the
`Uring/Conservation.lean` proof style (an LTS + a conservation law), and proves the
connection-limit enforcement it now realizes in the reactor
(`crates/dataplane/src/{uring,kqueue,blocking}.rs` + `standing.rs`).

## The model

A single per-source counter store `St := Ip → Nat` (active concurrent connections
per source). Two actions drive it, matching the two edges the reactor owns:

* `accept ip` — a connection from `ip` is accepted; the source's active count is
  incremented. The reactor calls `Standing::on_accept` here, exactly once per
  connection that enters the slab.
* `close ip` — a connection from `ip` closes; the count is decremented. GUARDED by
  `0 < s ip`: you can only close what is open. The reactor calls
  `Standing::on_close` here, exactly once per connection, on the single close funnel
  every path (served / refused / EOF / error) exits through.

## What is proved

* `conn_conservation` — in every reachable state, `active(ip) + #close(ip) =
  #accept(ip)`, hence `active(ip) = #accept(ip) − #close(ip)` and, on `Nat`, never
  negative. This is the decrement-EXACTLY-once discipline: the count reflects the
  real accept/close history with no drift.
* `close_le_accept` — `#close(ip) ≤ #accept(ip)` always: the counter never
  underflows (no leak that would wedge the limiter permanently).
* `conn_limit_fires` — a source at/over the cap makes the accept gate `.refuse` the
  REAL `Reactor.Stage.ConnLimit.resp503` (the proven `admits_over`).
* `conn_limit_transparent` — a source under the cap is `.admit`ted (pass through,
  the serve's bytes untouched — the proven `admits_under`).
* `flood_refused` / `init_admitted` — a concrete reachable 5-deep flood at cap 4 is
  refused while the fresh store admits: the gate genuinely distinguishes, so nothing
  above is vacuous.
-/

namespace Reactor.StandingCounters

/-- A source identifier (the client IP, abstracted to a `Nat` key). -/
abbrev Ip := Nat

/-- The per-source counter store: active concurrent connections per source. -/
abbrev St := Ip → Nat

/-- The initial store: every source has zero active connections. -/
def init : St := fun _ => 0

/-- Transition labels: the two accept-path edges the reactor owns. -/
inductive Lbl where
  | accept (ip : Ip)
  | close (ip : Ip)
deriving DecidableEq, Repr

/-- Increment the source `ip`'s active count. -/
def bump (s : St) (ip : Ip) : St := fun j => if j = ip then s j + 1 else s j

/-- Decrement the source `ip`'s active count (`Nat` truncated at zero; the `close`
guard keeps it from ever actually reaching the truncation). -/
def drop (s : St) (ip : Ip) : St := fun j => if j = ip then s j - 1 else s j

/-- The store's labeled transition system. `accept` is always enabled; `close` is
guarded by an actually-open connection (`0 < s ip`) — the decrement-once discipline
that makes the counter track the real history. -/
inductive Step : St → Lbl → St → Prop where
  | accept {s : St} (ip : Ip) : Step s (.accept ip) (bump s ip)
  | close {s : St} (ip : Ip) (h : 0 < s ip) : Step s (.close ip) (drop s ip)

/-- Finite traces of the store's LTS. -/
inductive Trace : St → List Lbl → St → Prop where
  | nil {s : St} : Trace s [] s
  | cons {s s' s'' : St} {l : Lbl} {ls : List Lbl}
      (h : Step s l s') (t : Trace s' ls s'') : Trace s (l :: ls) s''

/-- Reachability from the empty store. -/
def Reachable (s : St) : Prop := ∃ ls, Trace init ls s

theorem Trace.single {s s' : St} {l : Lbl} (h : Step s l s') : Trace s [l] s' :=
  .cons h .nil

theorem Trace.append {s s' s'' : St} {l₁ l₂ : List Lbl}
    (t₁ : Trace s l₁ s') (t₂ : Trace s' l₂ s'') : Trace s (l₁ ++ l₂) s'' := by
  induction t₁ with
  | nil => exact t₂
  | cons h _ ih => exact .cons h (ih t₂)

/-! ## Per-source accept / close counting -/

/-- Number of `accept ip` labels in a trace's label list. -/
def acc (ip : Ip) : List Lbl → Nat
  | [] => 0
  | (.accept j) :: t => (if j = ip then 1 else 0) + acc ip t
  | (.close _) :: t => acc ip t

/-- Number of `close ip` labels in a trace's label list. -/
def clo (ip : Ip) : List Lbl → Nat
  | [] => 0
  | (.close j) :: t => (if j = ip then 1 else 0) + clo ip t
  | (.accept _) :: t => clo ip t

/-! ## The conservation law -/

/-- **Per-trace conservation.** For any trace `s0 —ls→ s`, the final active count of
`ip` plus the closes of `ip` equals the initial count plus the accepts of `ip`:
`s ip + #close(ip) = s0 ip + #accept(ip)`. The `close` guard (`0 < s ip`) is exactly
what keeps the `Nat` decrement from underflowing the accounting. -/
theorem trace_active {s0 s : St} {ls : List Lbl} (tr : Trace s0 ls s) (ip : Ip) :
    s ip + clo ip ls = s0 ip + acc ip ls := by
  induction tr with
  | nil => simp [acc, clo]
  | cons h _ ih =>
    cases h with
    | accept ipa =>
      by_cases hip : ipa = ip
      · subst hip
        simp [acc, clo, bump] at ih ⊢
        omega
      · have hip' : ip ≠ ipa := fun hh => hip hh.symm
        simp only [acc, clo, bump, if_neg hip, if_neg hip'] at ih ⊢
        omega
    | close ipc hpos =>
      by_cases hip : ipc = ip
      · subst hip
        simp [acc, clo, drop] at ih ⊢
        omega
      · have hip' : ip ≠ ipc := fun hh => hip hh.symm
        simp only [acc, clo, drop, if_neg hip, if_neg hip'] at ih ⊢
        omega

/-- **CONSERVATION.** In every reachable state, `active(ip) = #accept(ip) −
#close(ip)` (additive form, no truncation): the counter faithfully tracks the real
accept/close history, under every interleaving. -/
theorem conn_conservation {s : St} {ls : List Lbl} (tr : Trace init ls s) (ip : Ip) :
    s ip + clo ip ls = acc ip ls := by
  have h := trace_active tr ip
  simpa [init] using h

/-- **No underflow / no leak.** The closes of a source never exceed its accepts — so
the counter never wedges below zero and the limiter can never get stuck rejecting a
source that has, in truth, no open connections. This is the decrement-exactly-once
guarantee stated as an accounting inequality. -/
theorem close_le_accept {s : St} {ls : List Lbl} (tr : Trace init ls s) (ip : Ip) :
    clo ip ls ≤ acc ip ls := by
  have h := conn_conservation tr ip; omega

/-- The active count as the honest difference `#accept − #close`. -/
theorem active_eq_sub {s : St} {ls : List Lbl} (tr : Trace init ls s) (ip : Ip) :
    s ip = acc ip ls - clo ip ls := by
  have h := conn_conservation tr ip; omega

/-- A `close` is enabled only on a source with an actually-open connection: you can
never decrement below zero (the reactor's `on_close` is only ever reached from the
close funnel of a connection that was accepted). -/
theorem close_needs_active {s s' : St} {ip : Ip} (h : Step s (.close ip) s') :
    0 < s ip := by
  cases h; assumption

/-! ## The accept gate — reusing the proven `ConnLimit` decision -/

/-- The reactor's accept decision: admit the connection, or refuse it with a real
`Response` (the `503`). -/
inductive AcceptDecision where
  | admit
  | refuse (r : Reactor.Response)

/-- **The accept gate.** Consult the PROVEN admission rule
(`Reactor.Stage.ConnLimit.admits`: `cap 0` = unlimited, else admit iff the source's
active count is under `cap`) on the store's standing count for `ip`. Admit →
`.admit`; reject → `.refuse` the REAL `Reactor.Stage.ConnLimit.resp503`. -/
def gate (cap : Nat) (s : St) (ip : Ip) : AcceptDecision :=
  if Reactor.Stage.ConnLimit.admits cap (s ip)
  then .admit
  else .refuse Reactor.Stage.ConnLimit.resp503

/-- **`conn_limit_fires`.** A source at/over a live cap makes the gate `.refuse` the
REAL proven `resp503` — composing `Reactor.Stage.ConnLimit.admits_over`. -/
theorem conn_limit_fires (cap : Nat) (s : St) (ip : Ip) (hpos : 0 < cap)
    (hover : cap ≤ s ip) :
    gate cap s ip = .refuse Reactor.Stage.ConnLimit.resp503 := by
  have h := Reactor.Stage.ConnLimit.admits_over hpos hover
  simp [gate, h]

/-- **`conn_limit_transparent`.** A source strictly under the cap is `.admit`ted —
the gate adds nothing, so the connection proceeds to the serve with its bytes
untouched (`Reactor.Stage.ConnLimit.admits_under`). -/
theorem conn_limit_transparent (cap : Nat) (s : St) (ip : Ip) (hunder : s ip < cap) :
    gate cap s ip = .admit := by
  have hpos : 0 < cap := Nat.lt_of_le_of_lt (Nat.zero_le _) hunder
  have h := Reactor.Stage.ConnLimit.admits_under hpos hunder
  simp [gate, h]

/-- A disabled cap (`0`) admits every source — the unlimited default. -/
theorem gate_unlimited (s : St) (ip : Ip) : gate 0 s ip = .admit := by
  simp [gate, Reactor.Stage.ConnLimit.admits_unlimited]

/-- The refused response is a genuine `503`. -/
theorem gate_refuse_status : Reactor.Stage.ConnLimit.resp503.status = 503 :=
  Reactor.Stage.ConnLimit.resp503_status

/-! ## Non-vacuity: a concrete reachable flood the gate refuses -/

/-- A five-deep accept flood from source `0`. -/
def floodLabels : List Lbl :=
  [Lbl.accept 0, Lbl.accept 0, Lbl.accept 0, Lbl.accept 0, Lbl.accept 0]

/-- The store after the flood. -/
def flood : St := bump (bump (bump (bump (bump init 0) 0) 0) 0) 0

/-- The flood is reachable from the empty store. -/
theorem flood_trace : Trace init floodLabels flood :=
  .cons (.accept 0) (.cons (.accept 0) (.cons (.accept 0)
    (.cons (.accept 0) (.cons (.accept 0) .nil))))

theorem flood_reachable : Reachable flood := ⟨floodLabels, flood_trace⟩

/-- Source `0` has five active connections after the flood. -/
theorem flood_active : flood 0 = 5 := by
  simp [flood, bump, init]

/-- Conservation on the concrete flood: `active(0) + #close(0) = #accept(0)`, i.e.
`5 + 0 = 5` — the accounting is exact and non-vacuous. -/
theorem flood_conservation : flood 0 + clo 0 floodLabels = acc 0 floodLabels :=
  conn_conservation flood_trace 0

/-- **The gate actually refuses the flood.** At a CONFIGURED per-source cap of `4`
— the value an operator writes as `max-connections 4` — source `0`'s five active
connections trip the gate to the REAL `503`. The cap is a PARAMETER of the model and
of the deployed gate; this used to be stated at the module constant
`Reactor.Stage.ConnLimit.connCap`, which no operator directive could move. -/
theorem flood_refused :
    gate 4 flood 0 = .refuse Reactor.Stage.ConnLimit.resp503 :=
  conn_limit_fires _ flood 0 (by decide) (by rw [flood_active]; decide)

/-- **The DEFAULT cap ADMITS the same flood.** Five concurrent connections from one
source is ordinary browser traffic, and the default per-source cap
(`Reactor.Stage.ConnLimit.defaultConnCap`, `512`) lets every one of them through. The
same standing state, two configured caps, two different decisions — the config
decides, which is exactly what the retired constant prevented. -/
theorem flood_admitted_by_default :
    gate Reactor.Stage.ConnLimit.defaultConnCap flood 0 = .admit :=
  conn_limit_transparent _ flood 0 (by rw [flood_active]; decide)

/-- **The gate admits a fresh source.** With no standing connections, the same cap
admits — so the gate genuinely distinguishes over-cap from under-cap (nothing above
is vacuous). -/
theorem init_admitted : gate 4 init 0 = .admit :=
  conn_limit_transparent _ init 0 (by decide)

/-! ## The request-rate window — a per-source AGING counter (the `429` gate)

The connection counter above is decremented once per close; the request-rate counter
is a different discipline — it AGES by TIME. Each source has a fixed window that
counts request arrivals and, once the window's span elapses, RESETS (the reactor's
`Standing::rate_note` resets `count` to `0` when `now - start ≥ window`). We model the
window as an LTS with two edges — `req ip` (an arrival: `+1`) and `roll ip` (the window
ages: reset to `0`) — and prove the window count is exactly the arrivals in the current
window (`rate_window_conservation`), that a `roll` genuinely ages it to zero (no leak,
the recovery edge), and that a source over the cap makes the gate refuse the REAL proven
`Reactor.Stage.StickTable.resp429` (`rate_limit_fires`, composing `admits_over`). -/

/-- The per-source request-rate store: arrivals counted in the current window. -/
abbrev RSt := Ip → Nat

/-- The initial rate store: every source's window count is zero. -/
def rinit : RSt := fun _ => 0

/-- The rate window's two edges: a request arrival, or the window aging (reset). -/
inductive RLbl where
  | req (ip : Ip)
  | roll (ip : Ip)
deriving DecidableEq, Repr

/-- An arrival from `ip`: increment its window count. -/
def rbump (s : RSt) (ip : Ip) : RSt := fun j => if j = ip then s j + 1 else s j

/-- `ip`'s window ages: reset its count to zero (the recovery edge — a source that has
gone quiet for a full window is counted from scratch, so the limiter never wedges). -/
def rreset (s : RSt) (ip : Ip) : RSt := fun j => if j = ip then 0 else s j

/-- The rate window's labeled transition system: `req` always enabled (an arrival),
`roll` always enabled (the window may age at any window boundary). -/
inductive RStep : RSt → RLbl → RSt → Prop where
  | req {s : RSt} (ip : Ip) : RStep s (.req ip) (rbump s ip)
  | roll {s : RSt} (ip : Ip) : RStep s (.roll ip) (rreset s ip)

/-- Finite traces of the rate window's LTS. -/
inductive RTrace : RSt → List RLbl → RSt → Prop where
  | nil {s : RSt} : RTrace s [] s
  | cons {s s' s'' : RSt} {l : RLbl} {ls : List RLbl}
      (h : RStep s l s') (t : RTrace s' ls s'') : RTrace s (l :: ls) s''

theorem RTrace.single {s s' : RSt} {l : RLbl} (h : RStep s l s') : RTrace s [l] s' :=
  .cons h .nil

theorem RTrace.append {s s' s'' : RSt} {l₁ l₂ : List RLbl}
    (t₁ : RTrace s l₁ s') (t₂ : RTrace s' l₂ s'') : RTrace s (l₁ ++ l₂) s'' := by
  induction t₁ with
  | nil => exact t₂
  | cons h _ ih => exact .cons h (ih t₂)

/-- One label's effect on `ip`'s running window count, chronologically: an arrival of
`ip` bumps it, `ip`'s roll zeroes it, any other label leaves it. -/
def stepCount (n : Nat) (ip : Ip) : RLbl → Nat
  | .req j  => if ip = j then n + 1 else n
  | .roll j => if ip = j then 0 else n

/-- `ip`'s window count after replaying the labels chronologically from a start count
`n` — the fold that a `roll` resets. This is the "requests in the current window". -/
def windowCount (ip : Ip) : Nat → List RLbl → Nat
  | n, []      => n
  | n, l :: t  => windowCount ip (stepCount n ip l) t

/-- A `roll` of `ip` ages the window to zero regardless of the prior count — the
counter cannot leak past a window boundary. -/
theorem windowCount_roll_ages (ip : Ip) (n : Nat) (t : List RLbl) :
    windowCount ip n (RLbl.roll ip :: t) = windowCount ip 0 t := by
  simp [windowCount, stepCount]

/-- **Per-trace window conservation.** For any trace `s0 —ls→ s`, the window count of
`ip` in `s` is exactly the chronological replay of the arrivals-and-rolls in `ls` from
`s0 ip`. -/
theorem rtrace_count {s0 s : RSt} {ls : List RLbl} (tr : RTrace s0 ls s) (ip : Ip) :
    s ip = windowCount ip (s0 ip) ls := by
  induction tr with
  | nil => rfl
  | @cons a b c lbl rest h _t ih =>
    -- h : RStep a lbl b, ih : c ip = windowCount ip (b ip) rest
    -- goal : c ip = windowCount ip (a ip) (lbl :: rest)
    have hstep : b ip = stepCount (a ip) ip lbl := by
      cases h with
      | req ip'  => simp [rbump, stepCount]
      | roll ip' => simp [rreset, stepCount]
    calc c ip = windowCount ip (b ip) rest := ih
      _ = windowCount ip (stepCount (a ip) ip lbl) rest := by rw [hstep]
      _ = windowCount ip (a ip) (lbl :: rest) := rfl

/-- **RATE-WINDOW CONSERVATION.** In every reachable rate state, `active-window(ip)` is
exactly the requests-in-the-current-window (arrivals since the last `roll`): the counter
faithfully tracks the arrival history and ages on each window boundary. -/
theorem rate_window_conservation {s : RSt} {ls : List RLbl}
    (tr : RTrace rinit ls s) (ip : Ip) : s ip = windowCount ip 0 ls := by
  have h := rtrace_count tr ip; simpa [rinit] using h

/-- A run of `n` arrivals from one source (from any start count `k`) counts to `k + n` —
the window count is the real arrival tally within the window. -/
theorem windowCount_reqs (ip : Ip) (n k : Nat) :
    windowCount ip k (List.replicate n (RLbl.req ip)) = k + n := by
  induction n generalizing k with
  | zero => simp [windowCount]
  | succ m ih =>
    rw [List.replicate_succ]
    show windowCount ip (stepCount k ip (RLbl.req ip)) (List.replicate m (RLbl.req ip))
      = k + (m + 1)
    have hstep : stepCount k ip (RLbl.req ip) = k + 1 := by
      show (if ip = ip then k + 1 else k) = k + 1
      simp
    rw [hstep, ih]; omega

/-- A pure `n`-arrival burst from source `ip` is reachable, landing in a state whose
window count for `ip` is exactly `n`. -/
theorem reachable_reqs (ip : Ip) (n : Nat) :
    ∃ s, RTrace rinit (List.replicate n (RLbl.req ip)) s ∧ s ip = n := by
  induction n with
  | zero => exact ⟨rinit, RTrace.nil, rfl⟩
  | succ m ih =>
    obtain ⟨s, tr, hc⟩ := ih
    refine ⟨rbump s ip, ?_, by simp [rbump, hc]⟩
    rw [List.replicate_succ']
    exact RTrace.append tr (RTrace.single (RStep.req ip))

/-! ## The rate gate — reusing the proven `StickTable` threshold decision -/

/-- The reactor's rate decision: admit, or refuse with the real `429` response. -/
inductive RateDecision where
  | admit
  | refuse (r : Reactor.Response)

/-- **The rate gate.** Consult the PROVEN threshold rule
(`Reactor.Stage.StickTable.admits`: admit iff the count is under the threshold) on the
source's standing window count. Admit → `.admit`; reject → `.refuse` the REAL proven
`Reactor.Stage.StickTable.resp429`. -/
def rgate (count : Nat) : RateDecision :=
  if Reactor.Stage.StickTable.admits count
  then .admit
  else .refuse Reactor.Stage.StickTable.resp429

/-- **`rate_limit_fires`.** A source whose in-window count is at/over the threshold
makes the gate `.refuse` the REAL proven `resp429` — composing
`Reactor.Stage.StickTable.admits_over`. -/
theorem rate_limit_fires (count : Nat)
    (hover : Reactor.Stage.StickTable.threshold ≤ count) :
    rgate count = .refuse Reactor.Stage.StickTable.resp429 := by
  have h := Reactor.Stage.StickTable.admits_over hover
  simp [rgate, h]

/-- **`rate_limit_transparent`.** A source strictly under the threshold is `.admit`ted —
the gate adds nothing (`Reactor.Stage.StickTable.admits_under`). -/
theorem rate_limit_transparent (count : Nat)
    (hunder : count < Reactor.Stage.StickTable.threshold) :
    rgate count = .admit := by
  have h := Reactor.Stage.StickTable.admits_under hunder
  simp [rgate, h]

/-- The refused response is a genuine `429`. -/
theorem rate_refuse_status : Reactor.Stage.StickTable.resp429.status = 429 := rfl

/-! ### Non-vacuity: a reachable rate flood the gate refuses, and recovery on aging -/

/-- **The gate refuses a reachable flood.** A burst of `threshold` arrivals from one
source is reachable and drives its window count to `threshold`, tripping the gate to the
REAL `429`. -/
theorem rate_flood_refused :
    ∃ s, RTrace rinit
        (List.replicate Reactor.Stage.StickTable.threshold (RLbl.req 0)) s
      ∧ rgate (s 0) = .refuse Reactor.Stage.StickTable.resp429 := by
  obtain ⟨s, tr, hc⟩ := reachable_reqs 0 Reactor.Stage.StickTable.threshold
  exact ⟨s, tr, by rw [hc]; exact rate_limit_fires _ (Nat.le_refl _)⟩

/-- **Recovery: the window ages, no leak.** After `roll`ing source `0` (its window
elapsed), its count is zero and the gate admits again — the limiter never wedges a source
that has gone quiet. -/
theorem rate_recovers_after_roll (s : RSt) : rgate ((rreset s 0) 0) = .admit := by
  have h0 : (rreset s 0) 0 = 0 := by simp [rreset]
  rw [h0]; exact rate_limit_transparent 0 (by decide)

/-! ## The slowloris gate — reusing the proven `Slowloris` expiry decision

The header-arrival deadline is per-CONNECTION, not per-source: the reactor records when a
connection's header phase began and, if it overruns the timeout, drops it with a `408`.
We reuse the PROVEN expiry decision (`Reactor.Stage.Slowloris.expired`) directly. -/

/-- The reactor's slowloris decision: keep the connection, or drop it with the `408`. -/
inductive SlowDecision where
  | keep
  | drop (r : Reactor.Response)

/-- **The slowloris gate.** Consult the PROVEN expiry rule
(`Reactor.Stage.Slowloris.expired`: enabled iff `timeout ≠ 0`, expired iff
`started + timeout ≤ now`) on the connection's header clocks. Expired → `.drop` the REAL
proven `Reactor.Stage.Slowloris.resp408`; in time → `.keep`. -/
def sgate (timeout started now : Nat) : SlowDecision :=
  if Reactor.Stage.Slowloris.expired timeout started now
  then .drop Reactor.Stage.Slowloris.resp408
  else .keep

/-- **`slowloris_fires`.** A connection whose header phase has overrun a live timeout
makes the gate `.drop` the REAL proven `resp408` — composing
`Reactor.Stage.Slowloris.expired_over`. -/
theorem slowloris_fires (timeout started now : Nat) (hpos : timeout ≠ 0)
    (hover : started + timeout ≤ now) :
    sgate timeout started now = .drop Reactor.Stage.Slowloris.resp408 := by
  have h := Reactor.Stage.Slowloris.expired_over hpos hover
  simp [sgate, h]

/-- **`slowloris_transparent`.** A connection still within its header window is `.keep`t —
the gate adds nothing (`Reactor.Stage.Slowloris.expired_in_time`). -/
theorem slowloris_transparent (timeout started now : Nat) (hin : now < started + timeout) :
    sgate timeout started now = .keep := by
  have h := Reactor.Stage.Slowloris.expired_in_time hin
  simp [sgate, h]

/-- A disabled timeout (`0`) never drops — the protection-off default. -/
theorem slowloris_disabled (started now : Nat) : sgate 0 started now = .keep := by
  have h := Reactor.Stage.Slowloris.expired_disabled started now
  simp [sgate, h]

/-- The dropped response is a genuine `408`. -/
theorem slow_drop_status : Reactor.Stage.Slowloris.resp408.status = 408 := rfl

/-! ### Non-vacuity: a slow-drip connection is dropped, a fast one is kept -/

/-- **A slow-drip connection is dropped.** A connection whose header phase began at clock
`0` and reaches the configured `headerTimeout` is dropped with the REAL `408`. -/
theorem slow_drip_dropped :
    sgate Reactor.Stage.Slowloris.headerTimeout 0 Reactor.Stage.Slowloris.headerTimeout
      = .drop Reactor.Stage.Slowloris.resp408 :=
  slowloris_fires _ 0 _ (by decide) (by decide)

/-- **A fast connection is kept.** With no elapsed header span the same timeout keeps the
connection — the gate genuinely distinguishes slow from fast (nothing above is vacuous). -/
theorem fast_request_kept :
    sgate Reactor.Stage.Slowloris.headerTimeout 0 0 = .keep :=
  slowloris_transparent _ 0 0 (by decide)

/-! ## Axiom audit (fully qualified) -/

#print axioms Reactor.StandingCounters.trace_active
#print axioms Reactor.StandingCounters.conn_conservation
#print axioms Reactor.StandingCounters.close_le_accept
#print axioms Reactor.StandingCounters.active_eq_sub
#print axioms Reactor.StandingCounters.close_needs_active
#print axioms Reactor.StandingCounters.conn_limit_fires
#print axioms Reactor.StandingCounters.conn_limit_transparent
#print axioms Reactor.StandingCounters.flood_reachable
#print axioms Reactor.StandingCounters.flood_conservation
#print axioms Reactor.StandingCounters.flood_refused
#print axioms Reactor.StandingCounters.flood_admitted_by_default
#print axioms Reactor.StandingCounters.init_admitted
#print axioms Reactor.StandingCounters.rate_window_conservation
#print axioms Reactor.StandingCounters.windowCount_roll_ages
#print axioms Reactor.StandingCounters.windowCount_reqs
#print axioms Reactor.StandingCounters.reachable_reqs
#print axioms Reactor.StandingCounters.rate_limit_fires
#print axioms Reactor.StandingCounters.rate_limit_transparent
#print axioms Reactor.StandingCounters.rate_flood_refused
#print axioms Reactor.StandingCounters.rate_recovers_after_roll
#print axioms Reactor.StandingCounters.slowloris_fires
#print axioms Reactor.StandingCounters.slowloris_transparent
#print axioms Reactor.StandingCounters.slowloris_disabled
#print axioms Reactor.StandingCounters.slow_drip_dropped
#print axioms Reactor.StandingCounters.fast_request_kept

end Reactor.StandingCounters
