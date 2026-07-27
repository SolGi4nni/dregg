import Reactor.Pipeline
import Reactor.Stage.ConnLimit
import Rate

/-!
# Reactor.Stage.Rate — the PER-CONNECTION token-bucket GATE, as a pipeline stage

A byte-driving `Stage` for the extensible serve fold: on the request phase it
consults the **real** `Rate` token bucket for THIS CONNECTION and, when the bucket
is over the limit (no token to spend), short-circuits the whole pipeline with a
`429 Too Many Requests` — the handler and every later stage are skipped. Under the
limit the request passes through untouched.

The decision is the real limiter, not a stub: `admitsAt` runs `Rate.refill` and then
`Rate.tryAdmit`, exactly the `Rate.Bucket` transition proven in `Rate/Bucket.lean`.

## THREE DIFFERENT BOUNDS — do not conflate them

This gate is ONE of three admission bounds the deployed fold enforces, over three
different quantities and three different pieces of state:

| bound | directive | quantity | state |
|---|---|---|---|
| per-CONNECTION burst | `burst-cap` / `burst-refill` | requests issued on ONE connection | the connection's request index + its elapsed clock |
| per-SOURCE arrival rate | `rate-limit` / `rate-window` | request arrivals from ONE source, across all its connections | the source's in-window arrival count (`Reactor.Stage.StickTable`) |
| per-SOURCE connection cap | `max-connections` | connections ONE source holds at once | the source's standing active-connection count (`Reactor.Stage.ConnLimit`) |

A source holding `max-connections` connections, each spending its full `burst-cap`,
is bounded by the per-SOURCE arrival rate, not by either per-connection number.
Setting one of the three does not move the other two, and a deployment that wants a
single source bounded must set the per-SOURCE ones — this gate only bounds what ONE
connection can do.

## The burst cap and refill rate are OPERATOR CONFIG, not module constants

They used to be Lean literals (`rateCap := 8`, `rateRate := 1`) that no directive in
the config grammar could reach, so a DEFAULT drorb answered `429` to the NINTH
request on a single keep-alive connection — while one page load on one HTTP/2 or
keep-alive connection is dozens of requests. Both now ride the SAME extensible
attribute bag every other host-threaded scalar does, through the SAME positional word
codec (`Reactor.Stage.ConnLimit.encodeCap` / `decodeWordD`, round-trip proven for
every `UInt64` by `decodeWordD_encodeCap`) — ONE encoding, proven once, shared with
the connection cap and the arrival limit. A context that carries no such attr reads
`defaultBurstCap` / `defaultBurstRate`, so nothing that predates the knob changes.

## The per-connection readings

Because the FFI serve is one stateless call per request, the depletion of the bucket
across a burst is reconstructed from two per-connection data the accept path
supplies: the number of requests already served on this connection (`seqKey`) and the
connection's monotonic elapsed-seconds clock (`clockKey`). Both are POSITIONAL
little-endian words in the same codec as the knobs — not the unary byte-runs they
used to be. That matters at the new defaults: a unary reading costs one cons per
counted request, so a 512-request burst cap would have consed 512 cells per request
on a busy keep-alive connection. Positional is eight bytes at every count.

* standing tokens `cap - seq` (truncated), refilled by `rate * clock` and capped at
  `cap` — the REAL `Rate.refill` / `Rate.tryAdmit` transition;
* a connection that has spent its burst RECOVERS as its clock advances
  (`admitsAt_recovers`) — the gate is a live bucket, not a latch;
* `cap = 0` DISABLES the gate (`admitsAt_unlimited`), matching `max-connections 0`
  and `rate-limit 0`. Without that case a `0` would mean "refuse everything", which
  is the opposite of what an operator writing `0` on the other two knobs means.

The byte effect is a genuine change to the emitted response:

* `rateStage_gate_build` — over the limit, the built pipeline response IS the `429`;
* `rateStage_pass` — under the limit, the stage is transparent: the emitted bytes are
  the tail/handler's, unchanged;
* `rateStage_changes_bytes` — with the same handler and tail, an over-limit request
  and an under-limit request emit *different* status bytes: the gate really drives the
  wire.

`overCtx_over` / `underCtx_under` exhibit concrete over- and under-limit contexts
(closed by `decide` on the real bucket), and `knob_moves_the_gate` exhibits ONE
depletion at which two different CONFIGURED caps disagree — so none of the above is
vacuous and none of it is a constant baked into the decision.
-/

namespace Reactor.Stage.Rate

open Reactor.Pipeline
open Proto (Bytes)

/-! ## The 429 rejection response -/

/-- Reason phrase for the rejection. -/
def reason429 : Bytes := "Too Many Requests".toUTF8.toList

/-- Body prose for the rejection. -/
def tooManyBody : Bytes := "rate limit exceeded\n".toUTF8.toList

/-- The `429 Too Many Requests` response the gate answers with when the bucket is
over the limit — a real `Response` (`error4xx`) whose status is `429`. -/
def resp429 : Response := error4xx 429 reason429 tooManyBody

/-! ## The DEFAULT per-connection burst parameters

The values in force when a context carries no configured ones. Chosen against what a
real client does on ONE connection, which is what this bound is about.

`defaultBurstCap = 512`. A browser multiplexes a whole page over one HTTP/2
connection, and a keep-alive HTTP/1.1 connection is reused across a whole page too:
nginx and h2o default `SETTINGS_MAX_CONCURRENT_STREAMS` to 128 and 100, a heavy page
is two to four hundred subresources, and an XHR-driven app adds more over the same
connection. `512` sits above the heaviest realistic page load as an INSTANTANEOUS
burst, while still bounding what one connection can fire before any time passes.

The retired value was `8` — below a browser by nearly two orders of magnitude, and
unreachable from config.

`defaultBurstRate = 64` tokens per elapsed second. Sixty-four requests per second
SUSTAINED on ONE connection is far above a browser (which is bounded by round trips
and rendering) and above an ordinary API client, while a request cannon on a single
connection is held to 64/s once its burst is spent. The retired value was `1`, i.e. a
connection recovered one request per second.

`defaultBurstCap` numerically equals `Reactor.Stage.ConnLimit.defaultConnCap`; that
is a coincidence of scale, not a shared bound — see the three-bounds table above. -/

/-- **DEFAULT per-connection burst capacity** — max standing tokens on ONE
connection when the operator configured none. See the section note for why `512`. -/
def defaultBurstCap : Nat := 512

/-- **DEFAULT per-connection refill rate**, tokens per elapsed second, when the
operator configured none. See the section note for why `64`. -/
def defaultBurstRate : Nat := 64

/-! ## The decision core, over NUMBERS

Stated on the four scalars — configured cap, configured refill rate, the
connection's standing request count and its elapsed clock — so every theorem below
is about the CONFIGURED values, never about a constant. Mirrors
`Reactor.Stage.ConnLimit.admits cap active`. -/

/-- The live bucket for a connection with `cnt` requests already served under a
configured capacity `cap` and refill rate `rate`: `cap - cnt` standing tokens
(truncated), `last := 0` so the refill credits the full elapsed clock. -/
def bucketAt (cap rate cnt : Nat) : _root_.Rate.Bucket :=
  { tokens := cap - cnt, last := 0, cap := cap, rate := rate }

/-- **The admission decision.** A disabled cap (`0`) admits everything; otherwise
refill the reconstructed bucket to the connection's elapsed clock and consult the
real `Rate.tryAdmit`. `true` = a token was available (admit), `false` = none
(reject). This is exactly the `Rate` transition, not a stub. -/
def admitsAt (cap rate cnt clk : Nat) : Bool :=
  (cap == 0) || (_root_.Rate.tryAdmit (_root_.Rate.refill clk (bucketAt cap rate cnt))).2

/-- The refill of the reconstructed bucket to the connection clock leaves
`min cap ((cap - cnt) + rate * clk)` tokens: the standing tokens plus the time
credit, capped at capacity. -/
theorem refill_tokens (cap rate cnt clk : Nat) :
    (_root_.Rate.refill clk (bucketAt cap rate cnt)).tokens
      = min cap ((cap - cnt) + rate * clk) := by
  unfold _root_.Rate.refill bucketAt
  rw [if_pos (Nat.zero_le _)]
  simp

/-- `tryAdmit` admits iff the bucket holds at least one token. -/
theorem tryAdmit_snd (b : _root_.Rate.Bucket) :
    (_root_.Rate.tryAdmit b).2 = decide (1 ≤ b.tokens) := by
  unfold _root_.Rate.tryAdmit; split <;> simp_all

/-- **A disabled cap admits any load** — the unlimited path, the reading
`max-connections 0` and `rate-limit 0` already have. Without this case a configured
`0` would mean "refuse every request", the opposite of what an operator writing `0`
on the sibling knobs means. -/
theorem admitsAt_unlimited (rate cnt clk : Nat) : admitsAt 0 rate cnt clk = true := by
  simp [admitsAt]

/-- **The exact time-based admission boundary, at a LIVE configured cap.** The gate
admits IFF the standing tokens plus the elapsed-time credit reach one — a total
characterization, for every configured `cap`/`rate` and every `cnt`/`clk`. -/
theorem admitsAt_iff {cap : Nat} (rate cnt clk : Nat) (hpos : 0 < cap) :
    admitsAt cap rate cnt clk = decide (1 ≤ (cap - cnt) + rate * clk) := by
  have h0 : (cap == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    omega
  unfold admitsAt
  rw [h0, Bool.false_or, tryAdmit_snd, refill_tokens]
  simp only [decide_eq_decide]
  generalize rate * clk = x
  omega

/-- **Saturation at the exhaustion instant.** With no elapsed time, once the standing
count reaches the configured capacity EVERY further request is rejected — the burst
limit, before any refill. -/
theorem admitsAt_saturates_at_zero {cap : Nat} (rate cnt : Nat) (hpos : 0 < cap)
    (h : cap ≤ cnt) : admitsAt cap rate cnt 0 = false := by
  rw [admitsAt_iff rate cnt 0 hpos]
  simp only [Nat.mul_zero, decide_eq_false_iff_not, Nat.not_le]
  omega

/-- **TIME RECOVERY — impossible at refill rate `0`.** A connection that has spent
its burst is admitted again once its clock has advanced enough to credit one token.
This is the `429 → wait → 200` recovery: the gate is a live bucket, not a latch. -/
theorem admitsAt_recovers (cap rate cnt clk : Nat) (hcredit : 1 ≤ rate * clk) :
    admitsAt cap rate cnt clk = true := by
  rcases Nat.eq_zero_or_pos cap with h | h
  · subst h; exact admitsAt_unlimited rate cnt clk
  · rw [admitsAt_iff rate cnt clk h]
    simp only [decide_eq_true_eq]
    omega

/-- **THE CLOCK CLAMP IS INERT.** Clamping the connection's elapsed-seconds clock at
the configured capacity changes NO verdict — for EVERY cap, refill rate, standing
count and clock. This is what licenses the host-side context to store the clock as a
bounded word (`min clk cap`, so it always fits the eight-byte codec) instead of an
unbounded one: once the elapsed time would credit a full capacity there is nothing
further to credit, and at refill rate `0` the clock is not read at all.

Three cases, all real: a disabled cap admits either way; a clock under the cap is
unchanged by the clamp; and above the cap both the clamped and the raw credit already
exceed one token (at rate `0` both credits are `0` and the standing stock decides). -/
theorem admitsAt_clock_clamp (cap rate cnt clk : Nat) :
    admitsAt cap rate cnt (min clk cap) = admitsAt cap rate cnt clk := by
  rcases Nat.eq_zero_or_pos cap with h0 | h0
  · subst h0; rw [admitsAt_unlimited, admitsAt_unlimited]
  · rcases Nat.le_total clk cap with hle | hle
    · rw [Nat.min_eq_left hle]
    · rw [Nat.min_eq_right hle, admitsAt_iff _ _ _ h0, admitsAt_iff _ _ _ h0]
      rcases Nat.eq_zero_or_pos rate with hr | hr
      · subst hr; simp
      · have h1 : 0 < rate * cap := Nat.mul_pos hr h0
        have h2 : rate * cap <= rate * clk := Nat.mul_le_mul_left _ hle
        simp only [decide_eq_decide]
        omega

/-- **Depletion monotonicity (antitone) at a fixed cap, rate and clock.** A
more-depleted connection is never more likely to admit than a less-depleted one —
the token bucket's defining monotonicity. -/
theorem admitsAt_antitone {cap rate cnt cnt' clk : Nat} (h : cnt ≤ cnt')
    (ha : admitsAt cap rate cnt' clk = true) : admitsAt cap rate cnt clk = true := by
  rcases Nat.eq_zero_or_pos cap with h0 | h0
  · subst h0; exact admitsAt_unlimited rate cnt clk
  · rw [admitsAt_iff rate cnt' clk h0] at ha
    rw [admitsAt_iff rate cnt clk h0]
    simp only [decide_eq_true_eq] at ha ⊢
    omega

/-! ### The DEFAULT parameters admit a browser (non-vacuity of the DEFAULT choice) -/

/-- **A browser-shaped burst is admitted by default.** Fifty requests already served
on one keep-alive/HTTP/2 connection, with NO elapsed time to refill — the shape of a
single page load — pass the default burst cap. -/
theorem defaultBurst_admits_browserBurst :
    admitsAt defaultBurstCap defaultBurstRate 50 0 = true := by decide

/-- …and the RETIRED module constants genuinely did NOT admit it: the two parameter
pairs DISAGREE on the browser burst, so raising the defaults is a real change of
decision, not a rename. This is the regression, stated. -/
theorem retiredBurst8_refused_browserBurst : admitsAt 8 1 50 0 = false := by decide

/-- The retired constants refused the NINTH request on a connection outright — the
reproduction, as a theorem. -/
theorem retiredBurst8_refused_at_nine : admitsAt 8 1 8 0 = false := by decide

/-! ## Reading the CONFIGURED parameters and the per-connection state off the context

Everything the gate decides on rides the extensible attribute bag: two OPERATOR
numbers (`burst-cap`, `burst-refill`) and two ACCEPT-PATH readings (the connection's
request index and its elapsed-seconds clock). All four are positional little-endian
eight-byte words in the ONE shared codec (`ConnLimit.encodeCap` / `decodeWordD`), so
they inherit the single round-trip theorem `decodeWordD_encodeCap`. -/

/-- Attribute key holding the per-connection request index — the number of requests
already served on this connection. Written by the accept path. -/
def seqKey : String := "rate-seq"

/-- Attribute key holding the per-connection elapsed-seconds clock. Written alongside
`seqKey`; drives the time-based `Rate.refill`. -/
def clockKey : String := "rate-clock"

/-- Attribute key holding the CONFIGURED per-connection burst capacity. Written by
the host from the operator's `burst-cap`. -/
def burstCapKey : String := "rate-burst-cap"

/-- Attribute key holding the CONFIGURED per-connection refill rate. Written by the
host from the operator's `burst-refill`. -/
def burstRateKey : String := "rate-burst-refill"

/-! ### The host packs both per-connection readings into ONE scalar

The accept path crosses a single `UInt64`: the connection's request count in the low
32 bits and its monotonic elapsed-seconds clock in the high bits. Splitting it here
keeps the seam one scalar wide while the gate still sees two independent readings. -/

/-- Width of the low field of the accept-path rate scalar (`2^32`): the low 32 bits
hold the per-connection request count, the high bits the elapsed-seconds clock. -/
def packWidth : Nat := 4294967296

/-- The per-connection request count carried in the low 32 bits of a packed rate
scalar. -/
def countOfPacked (s : Nat) : Nat := s % packWidth

/-- The elapsed-seconds clock carried in the high bits of a packed rate scalar. -/
def clockOfPacked (s : Nat) : Nat := s / packWidth

/-- The packed request count is under `2^32`, hence inside the eight-byte word the
attribute-bag codec round-trips exactly — the count needs no clamp at any capacity. -/
theorem countOfPacked_lt64 (n : Nat) : countOfPacked n < 2 ^ 64 := by
  unfold countOfPacked packWidth
  omega

/-- Look the value bytes up for a key in the attribute bag (`[]` if absent). -/
def lookupBytes (c : Ctx) (k : String) : Bytes :=
  match c.attrs.find? (fun p => p.1 == k) with
  | some p => p.2
  | none   => []

/-- The per-connection request count the context carries (`0` when absent — a fresh,
unmetered connection). -/
def seqOf (c : Ctx) : Nat := Reactor.Stage.ConnLimit.decodeWordD 0 (lookupBytes c seqKey)

/-- The per-connection elapsed-seconds clock the context carries (`0` when absent —
a fresh connection reads clock `0`). This is the reading the REAL `Rate.refill`
advances the bucket to, so an over-limit connection recovers over time. -/
def clockOf (c : Ctx) : Nat := Reactor.Stage.ConnLimit.decodeWordD 0 (lookupBytes c clockKey)

/-- **The CONFIGURED burst capacity the context carries** — the operator's
`burst-cap` where the host threaded one, `defaultBurstCap` otherwise. -/
def burstCapOf (c : Ctx) : Nat :=
  Reactor.Stage.ConnLimit.decodeWordD defaultBurstCap (lookupBytes c burstCapKey)

/-- **The CONFIGURED refill rate the context carries** — the operator's
`burst-refill` where the host threaded one, `defaultBurstRate` otherwise. -/
def burstRateOf (c : Ctx) : Nat :=
  Reactor.Stage.ConnLimit.decodeWordD defaultBurstRate (lookupBytes c burstRateKey)

/-- A context with no `burst-cap` attr reads the DEFAULT capacity (the no-regression
fact every pre-knob context relies on). -/
theorem burstCapOf_absent {c : Ctx} (h : lookupBytes c burstCapKey = []) :
    burstCapOf c = defaultBurstCap := by
  simp [burstCapOf, h, Reactor.Stage.ConnLimit.decodeWordD]

/-- A context with no `burst-refill` attr reads the DEFAULT refill rate. -/
theorem burstRateOf_absent {c : Ctx} (h : lookupBytes c burstRateKey = []) :
    burstRateOf c = defaultBurstRate := by
  simp [burstRateOf, h, Reactor.Stage.ConnLimit.decodeWordD]

/-- The live bucket the gate decides on, reconstructed from the connection's standing
depletion against the CONFIGURED capacity and refill rate. -/
def bucketOf (c : Ctx) : _root_.Rate.Bucket :=
  bucketAt (burstCapOf c) (burstRateOf c) (seqOf c)

/-- **The real admit decision on a context.** The four scalars come off the
attribute bag; the DECISION is `admitsAt`, the proven `Rate` transition. Nothing
here is a module constant. -/
def admits (c : Ctx) : Bool :=
  admitsAt (burstCapOf c) (burstRateOf c) (seqOf c) (clockOf c)

/-! ## The stage -/

/-- **The per-connection rate-limit gate stage.** Request phase: consult the real
bucket — admit → `.continue` (pass through), reject → `.respond resp429`
(short-circuit with the `429`, skipping the handler and every later stage). Response
phase: transparent — the affine builder is threaded through unchanged. -/
def rateStage : Stage where
  name := "rate"
  onRequest  := fun c => cond (admits c) (.continue c) (.respond resp429)
  onResponse := fun _ b => b

/-! ## The gate's request-phase decision -/

/-- Over the limit, the gate short-circuits with the `429`. -/
theorem rateStage_onReq_respond (c : Ctx) (hover : admits c = false) :
    rateStage.onRequest c = .respond resp429 := by
  simp only [rateStage, hover, cond]

/-- Under the limit, the gate passes the context through. -/
theorem rateStage_onReq_continue (c : Ctx) (hunder : admits c = true) :
    rateStage.onRequest c = .continue c := by
  simp only [rateStage, hunder, cond]

/-! ## The byte effect -/

/-- **Gate byte-effect.** Over the limit, the BUILT pipeline response — for ANY
tail and handler — is exactly `resp429`: the handler and every later stage are
skipped and the emitted bytes are the `429`. -/
theorem rateStage_gate_build (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hover : admits c = false) :
    runPipeline (rateStage :: rest) h c = runResp rest c (ResponseBuilder.ofResponse resp429) :=
  pipeline_gate_short_circuits rateStage rest h c resp429 (rateStage_onReq_respond c hover)

/-- The `429`'s status field is `429`. -/
theorem resp429_status : resp429.status = 429 := rfl

/-- The over-limit response's status byte is `429` — preserved through a
status-stable inner onion. -/
theorem rateStage_over_status (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hover : admits c = false) (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (rateStage :: rest) h c).build).status = 429 :=
  pipeline_gate_status rateStage rest h c resp429 (rateStage_onReq_respond c hover) hst

/-- **Pass-through byte-effect.** Under the limit, the stage is transparent: the
pipeline output is exactly the tail's — the gate contributes no bytes. -/
theorem rateStage_pass (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hunder : admits c = true) :
    runPipeline (rateStage :: rest) h c = runPipeline rest h c := by
  rw [pipeline_stage_effect rateStage rest h c c (rateStage_onReq_continue c hunder)]
  rfl

/-! ## Concrete configured contexts (non-vacuity of the KNOB) -/

/-- A context carrying an explicit CONFIGURED burst cap and refill rate together with
an explicit per-connection request count and clock — the shape the host builds per
request. -/
def cfgCtx (cap rate cnt clk : Nat) : Ctx :=
  { input := [], req := {},
    attrs := [ (burstCapKey, Reactor.Stage.ConnLimit.encodeCap cap)
             , (burstRateKey, Reactor.Stage.ConnLimit.encodeCap rate)
             , (seqKey, Reactor.Stage.ConnLimit.encodeCap cnt)
             , (clockKey, Reactor.Stage.ConnLimit.encodeCap clk) ] }

/-- The configured capacity is read back off `cfgCtx` exactly, for every value the
host can cross. -/
theorem cfgCtx_cap {cap : Nat} (rate cnt clk : Nat) (h : cap < 2 ^ 64) :
    burstCapOf (cfgCtx cap rate cnt clk) = cap := by
  have hl : lookupBytes (cfgCtx cap rate cnt clk) burstCapKey
      = Reactor.Stage.ConnLimit.encodeCap cap := by
    simp [lookupBytes, cfgCtx, burstCapKey, burstRateKey, seqKey, clockKey]
  rw [burstCapOf, hl, Reactor.Stage.ConnLimit.decodeWordD_encodeCap defaultBurstCap h]

/-- The configured refill rate is read back off `cfgCtx` exactly. -/
theorem cfgCtx_rate (cap : Nat) {rate : Nat} (cnt clk : Nat) (h : rate < 2 ^ 64) :
    burstRateOf (cfgCtx cap rate cnt clk) = rate := by
  have hl : lookupBytes (cfgCtx cap rate cnt clk) burstRateKey
      = Reactor.Stage.ConnLimit.encodeCap rate := by
    simp [lookupBytes, cfgCtx, burstCapKey, burstRateKey, seqKey, clockKey]
  rw [burstRateOf, hl, Reactor.Stage.ConnLimit.decodeWordD_encodeCap defaultBurstRate h]

/-- The standing request count is read back off `cfgCtx` exactly. -/
theorem cfgCtx_seq (cap rate : Nat) {cnt : Nat} (clk : Nat) (h : cnt < 2 ^ 64) :
    seqOf (cfgCtx cap rate cnt clk) = cnt := by
  have hl : lookupBytes (cfgCtx cap rate cnt clk) seqKey
      = Reactor.Stage.ConnLimit.encodeCap cnt := by
    simp [lookupBytes, cfgCtx, burstCapKey, burstRateKey, seqKey, clockKey]
  rw [seqOf, hl, Reactor.Stage.ConnLimit.decodeWordD_encodeCap 0 h]

/-- The standing clock is read back off `cfgCtx` exactly. -/
theorem cfgCtx_clock (cap rate cnt : Nat) {clk : Nat} (h : clk < 2 ^ 64) :
    clockOf (cfgCtx cap rate cnt clk) = clk := by
  have hl : lookupBytes (cfgCtx cap rate cnt clk) clockKey
      = Reactor.Stage.ConnLimit.encodeCap clk := by
    simp [lookupBytes, cfgCtx, burstCapKey, burstRateKey, seqKey, clockKey]
  rw [clockOf, hl, Reactor.Stage.ConnLimit.decodeWordD_encodeCap 0 h]

/-- **THE KNOB MOVES THE GATE.** At the SAME eight requests already served on one
connection and the SAME zero elapsed clock, a connection under a configured
`burst-cap` of `8` is REFUSED and one under a configured `burst-cap` of `16` is
ADMITTED. The decision follows the configured value; nothing here is a constant.
(Under the retired hardcoded `8` both were refused — that was the bug.) -/
theorem knob_moves_the_gate :
    admits (cfgCtx 8 1 8 0) = false ∧ admits (cfgCtx 16 1 8 0) = true := by decide

/-- **A configured cap of `0` DISABLES the gate** on the real context shape — an
exhausted connection is still admitted. -/
theorem knob_zero_disables : admits (cfgCtx 0 0 1000000 0) = true := by decide

/-- A context carrying ONLY the accept-path readings — no configured burst
parameters, so the DEFAULTS apply. This is the shape every pre-knob context has. -/
def unconfiguredCtx (cnt clk : Nat) : Ctx :=
  { input := [], req := {},
    attrs := [ (seqKey, Reactor.Stage.ConnLimit.encodeCap cnt)
             , (clockKey, Reactor.Stage.ConnLimit.encodeCap clk) ] }

/-- An unconfigured context reads the DEFAULT capacity. -/
theorem unconfiguredCtx_cap (cnt clk : Nat) :
    burstCapOf (unconfiguredCtx cnt clk) = defaultBurstCap := by
  simp [burstCapOf, lookupBytes, unconfiguredCtx, burstCapKey, seqKey, clockKey,
    Reactor.Stage.ConnLimit.decodeWordD]

/-- An unconfigured context reads the DEFAULT refill rate. -/
theorem unconfiguredCtx_rate (cnt clk : Nat) :
    burstRateOf (unconfiguredCtx cnt clk) = defaultBurstRate := by
  simp [burstRateOf, lookupBytes, unconfiguredCtx, burstRateKey, seqKey, clockKey,
    Reactor.Stage.ConnLimit.decodeWordD]

/-- **The defaults admit the browser burst on the real context shape.** With no
configured burst parameters the gate admits a connection that has already served
fifty requests with no elapsed time — the case a default deployment used to answer
`429` to at request nine. -/
theorem default_admits_browserBurst : admits (unconfiguredCtx 50 0) = true := by decide

/-! ## Concrete over- and under-limit contexts (non-vacuity of the DECISION) -/

/-- A context whose connection has already spent its CONFIGURED burst — the bucket is
empty, so this request is over the limit. The witness carries an explicit configured
cap, so it exercises the CONFIGURED path rather than a module constant. -/
def overCtx : Ctx := cfgCtx 8 1 8 0

/-- A fresh connection (no requests served yet, no configured parameters) — a full
bucket, under the limit. -/
def underCtx : Ctx := { input := [], req := {}, attrs := [] }

/-- `overCtx` is over the limit — the real bucket rejects it. -/
theorem overCtx_over : admits overCtx = false := by decide

/-- `underCtx` is under the limit — the real bucket admits it. -/
theorem underCtx_under : admits underCtx = true := by decide

/-- An over-limit request emits a `429` (through a status-stable inner onion). -/
theorem overCtx_emits_429 (rest : List Stage) (h : Ctx → Response)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (rateStage :: rest) h overCtx).build).status = 429 :=
  rateStage_over_status rest h overCtx overCtx_over hst

/-- An under-limit request passes through to the tail unchanged. -/
theorem underCtx_passes (rest : List Stage) (h : Ctx → Response) :
    runPipeline (rateStage :: rest) h underCtx = runPipeline rest h underCtx :=
  rateStage_pass rest h underCtx underCtx_under

/-- **The gate genuinely drives the wire.** With the SAME handler and tail, an
over-limit request and an under-limit request emit different status bytes: the
over-limit one is forced to `429`, the under-limit one keeps the handler's status
(here, any status `≠ 429`). So the stage really changes the bytes the serve
emits — it is a byte-driver, not a proof attachment. -/
theorem rateStage_changes_bytes (h : Ctx → Response)
    (hstatus : (h underCtx).status ≠ 429) :
    ((runPipeline [rateStage] h overCtx).build).status
      ≠ ((runPipeline [rateStage] h underCtx).build).status := by
  rw [overCtx_emits_429 [] h (by intro t ht; exact absurd ht (List.not_mem_nil)),
      underCtx_passes [] h, pipeline_empty, build_ofResponse]
  exact fun heq => hstatus heq.symm

/-! ## The general characterization, lifted to contexts

`admitsAt_*` above characterize the decision for EVERY configured pair and EVERY
reading; these lift them to whatever a context carries, so the deployed gate's
behaviour is pinned at the configured values rather than at samples. -/

/-- **The exact time-based admission boundary on a context, at a live configured
cap.** -/
theorem admits_iff (c : Ctx) (hpos : 0 < burstCapOf c) :
    admits c = decide (1 ≤ (burstCapOf c - seqOf c) + burstRateOf c * clockOf c) :=
  admitsAt_iff _ _ _ hpos

/-- A context whose configured cap is `0` admits everything. -/
theorem admits_unlimited (c : Ctx) (h : burstCapOf c = 0) : admits c = true := by
  unfold admits; rw [h]; exact admitsAt_unlimited _ _ _

/-- **Saturation at the exhaustion instant**, on a context. -/
theorem admits_saturates_at_zero (c : Ctx) (hclock : clockOf c = 0)
    (hpos : 0 < burstCapOf c) (h : burstCapOf c ≤ seqOf c) : admits c = false := by
  unfold admits; rw [hclock]; exact admitsAt_saturates_at_zero _ _ hpos h

/-- **TIME RECOVERY**, on a context: an exhausted connection is admitted again once
its clock has credited one token. -/
theorem admits_recovers (c : Ctx) (hcredit : 1 ≤ burstRateOf c * clockOf c) :
    admits c = true :=
  admitsAt_recovers _ _ _ _ hcredit

/-- **Depletion monotonicity (antitone)** at equal configured parameters and clock. -/
theorem admits_antitone {c c' : Ctx} (hcap : burstCapOf c = burstCapOf c')
    (hrate : burstRateOf c = burstRateOf c') (hclock : clockOf c = clockOf c')
    (h : seqOf c ≤ seqOf c') (ha : admits c' = true) : admits c = true := by
  unfold admits at ha ⊢
  rw [hcap, hrate, hclock]
  exact admitsAt_antitone h ha

/-! ## Axiom audit -/

#print axioms overCtx_over
#print axioms underCtx_under
#print axioms knob_moves_the_gate
#print axioms knob_zero_disables
#print axioms default_admits_browserBurst
#print axioms defaultBurst_admits_browserBurst
#print axioms retiredBurst8_refused_browserBurst
#print axioms rateStage_gate_build
#print axioms rateStage_over_status
#print axioms rateStage_pass
#print axioms rateStage_changes_bytes

#print axioms refill_tokens
#print axioms admitsAt_iff
#print axioms admitsAt_unlimited
#print axioms admitsAt_saturates_at_zero
#print axioms admitsAt_recovers
#print axioms admitsAt_antitone
#print axioms admitsAt_clock_clamp
#print axioms countOfPacked_lt64
#print axioms admits_iff
#print axioms cfgCtx_cap
#print axioms cfgCtx_rate
#print axioms cfgCtx_seq
#print axioms cfgCtx_clock

end Reactor.Stage.Rate
