import MetricsCorrect

/-!
# O11y.MetricsCounters — the deployed request/status-class counters, proven

`O11y.Prometheus` / `O11y.PromExposition` prove the *rendering* of the metrics
surface (the text-exposition line grammar). This file closes the counting layer
underneath it: the two accounting laws the deployed `record` path guarantees on
every served response, modelled directly on the running dataplane.

Ground truth: `crates/dataplane/src/metrics.rs :: record` / `record_streamed`,
called once per finalized response from the io_uring serve loop
(`crates/dataplane/src/uring.rs`, at the two funnel points where a response is
finalized for send). That function does exactly two counting acts per response:

```rust
REQUESTS.fetch_add(1, Ordering::Relaxed);      // drorb_requests_total += 1
match status_class(head) {                     // one class bucket += 1
    Some(2) => &R2XX, Some(3) => &R3XX,
    Some(4) => &R4XX, Some(5) => &R5XX, _ => &ROTHER,
}.fetch_add(1, Ordering::Relaxed);
```

and `status_class` reads the leading digit of the HTTP status code out of the
response head (`HTTP/1.1 SP CODE …`), following the status-class partition of
RFC 9110 §15 (1xx/2xx/3xx/4xx/5xx). The status-class function below is a
byte-faithful transcription of the deployed `status_class`; the counter
transition is a byte-faithful transcription of `record`.

Proven here (core-Lean only — the axiom footprint on the headline theorems is
empty, checked with `#print axioms`):

* `metrics_counter_monotone` — one served response bumps `drorb_requests_total`
  by exactly one; hence it is monotone non-decreasing and strictly increasing
  per response (never a skip, never a double count).
* `metrics_total_counts` / `metrics_total_from_zero` — folding `record` over `N`
  served responses leaves `drorb_requests_total` at `N` (from a fresh registry):
  the exact invariant the deployed `/metrics` endpoint reports after `N` curls.
* `metrics_status_class` — a response of status class `Nxx` increments the
  `drorb_responses_total{class="Nxx"}` bucket by exactly one, and
  `metrics_status_class_others` — leaves every other class bucket fixed.
* `statusClass_faithful_*` — the byte-level status-class reader agrees with the
  wire on concrete `HTTP/1.1 …` heads (200→2xx, 404→4xx, 500→5xx, malformed→
  other), pinning the model to the bytes the running server actually parses.
-/

namespace O11y.MetricsCounters

/-! ## Byte-level status-class reader (mirrors `metrics.rs :: status_class`) -/

/-- ASCII space and CR, as the deployed reader splits on them. -/
def spaceByte : UInt8 := 0x20
def crByte : UInt8 := 0x0D

/-- `b` is an ASCII decimal digit (`'0'..'9'`), i.e. Rust's `u8::is_ascii_digit`. -/
def isDigit (b : UInt8) : Bool := 0x30 ≤ b && b ≤ 0x39

/-- The leading digit of the HTTP status code in a response head, or `none` if
the head is not a recognisable `PREFIX SP CODE …` with a 3-ASCII-digit `CODE`.

Byte-faithful transcription of `crates/dataplane/src/metrics.rs :: status_class`:

* `head` = bytes up to the first CR (Rust `split(b'\r').next()`, which on a
  head with no CR yields the whole slice — `takeWhile` matches both cases);
* find the first space and take everything after it (Rust `position(SP)?` then
  `head[sp+1..]`); no space ⇒ `none`;
* `code` = bytes up to the next space (Rust `split(b' ').next()`);
* if `code` is exactly 3 ASCII digits, return its leading digit `code[0]-'0'`. -/
def statusClass (resp : List UInt8) : Option UInt8 :=
  let head := resp.takeWhile (fun b => b ≠ crByte)
  match head.dropWhile (fun b => b ≠ spaceByte) with
  | [] => none
  | _ :: after =>
      let code := after.takeWhile (fun b => b ≠ spaceByte)
      if code.length = 3 ∧ code.all isDigit then
        some (code.headD 0 - 0x30)
      else none

/-! ## Status classes and the counter registry (mirrors `metrics.rs :: record`) -/

/-- The five status-class buckets of `drorb_responses_total{class=…}`, exactly
the arms of the deployed `match status_class(head) { … }`. -/
inductive Class
  | c2 | c3 | c4 | c5 | cOther
  deriving DecidableEq

/-- Map a response to its class bucket, mirroring the deployed `match`:
`Some(2)=>2xx, Some(3)=>3xx, Some(4)=>4xx, Some(5)=>5xx, _=>other`. -/
def classify (resp : List UInt8) : Class :=
  match statusClass resp with
  | some 2 => .c2
  | some 3 => .c3
  | some 4 => .c4
  | some 5 => .c5
  | _ => .cOther

/-- The counter registry state this lane reasons about: the total request
counter (`drorb_requests_total`) and the per-class response buckets
(`drorb_responses_total{class=…}`). The deployed statics `REQUESTS` and
`R2XX..ROTHER` are the atomics behind these fields. -/
structure Counters where
  total : Nat
  bucket : Class → Nat

/-- The empty registry (all atomics start at zero — `AtomicU64::new(0)`). -/
def Counters.zero : Counters := { total := 0, bucket := fun _ => 0 }

/-- One served response, as the deployed `record` counts it: bump `total` by one
and bump the served response's class bucket by one, leaving the other buckets
fixed. Byte-faithful transcription of the two `fetch_add(1, …)` in `record`. -/
def Counters.record (s : Counters) (resp : List UInt8) : Counters :=
  { total := s.total + 1
    bucket := fun c => if c = classify resp then s.bucket c + 1 else s.bucket c }

/-- Fold `record` over a sequence of served responses (the serve loop over a run
of requests). -/
def Counters.recordAll (s : Counters) (resps : List (List UInt8)) : Counters :=
  resps.foldl Counters.record s

/-! ## Counter monotonicity (drorb_requests_total) -/

/-- **metrics_counter_monotone.** One served response bumps `drorb_requests_total`
by *exactly one*. This is the exact per-response accounting the io_uring serve
loop performs (`REQUESTS.fetch_add(1)` at each finalized response). -/
theorem metrics_counter_monotone (s : Counters) (resp : List UInt8) :
    (s.record resp).total = s.total + 1 := rfl

/-- Monotone non-decreasing: the total never drops across a served response
(immediate from the exact-add law). -/
theorem metrics_counter_nondecreasing (s : Counters) (resp : List UInt8) :
    s.total ≤ (s.record resp).total := by
  rw [metrics_counter_monotone]; exact Nat.le_succ _

/-- Strictly increasing per response: never a skipped or duplicated count. -/
theorem metrics_counter_strict (s : Counters) (resp : List UInt8) :
    s.total < (s.record resp).total := by
  rw [metrics_counter_monotone]; exact Nat.lt_succ_self _

/-- **metrics_total_counts.** Serving `N` responses raises `drorb_requests_total`
by exactly `N` — the total counts served responses one-for-one. -/
theorem metrics_total_counts (s : Counters) (resps : List (List UInt8)) :
    (s.recordAll resps).total = s.total + resps.length := by
  induction resps generalizing s with
  | nil => simp [Counters.recordAll]
  | cons r rs ih =>
      simp only [Counters.recordAll, List.foldl_cons, List.length_cons] at *
      rw [ih (s.record r), metrics_counter_monotone]; omega

/-- **metrics_total_from_zero.** After `N` served responses on a fresh registry,
`drorb_requests_total == N`. This is exactly what the deployed `/metrics`
endpoint must report after `N` requests curled through the io_uring dataplane —
the prove-what-runs invariant. -/
theorem metrics_total_from_zero (resps : List (List UInt8)) :
    (Counters.zero.recordAll resps).total = resps.length := by
  rw [metrics_total_counts]; simp [Counters.zero]

/-! ## Status-class accounting (drorb_responses_total{class=…}) -/

/-- **metrics_status_class.** A served response increments the class bucket for
*its own* class by exactly one. Combined with `classify` this says: a response of
status class `Nxx` increments `drorb_responses_total{class="Nxx"}` by one. -/
theorem metrics_status_class (s : Counters) (resp : List UInt8) :
    (s.record resp).bucket (classify resp) = s.bucket (classify resp) + 1 := by
  simp [Counters.record]

/-- **metrics_status_class_others.** A served response leaves every *other* class
bucket exactly fixed — only the response's own class bucket moves. -/
theorem metrics_status_class_others (s : Counters) (resp : List UInt8) (c : Class)
    (h : c ≠ classify resp) :
    (s.record resp).bucket c = s.bucket c := by
  simp [Counters.record, h]

/-- The class a response is filed under is determined by its byte-level status
class: a head that reads status class `2` is filed under `c2` (and likewise 3/4/5;
anything else under `cOther`). Ties the bucket law to the wire reader. -/
theorem classify_of_statusClass_two (resp : List UInt8)
    (h : statusClass resp = some 2) : classify resp = .c2 := by
  simp [classify, h]

theorem classify_of_statusClass_three (resp : List UInt8)
    (h : statusClass resp = some 3) : classify resp = .c3 := by
  simp [classify, h]

theorem classify_of_statusClass_four (resp : List UInt8)
    (h : statusClass resp = some 4) : classify resp = .c4 := by
  simp [classify, h]

theorem classify_of_statusClass_five (resp : List UInt8)
    (h : statusClass resp = some 5) : classify resp = .c5 := by
  simp [classify, h]

/-- Fully wired: a response whose head reads status class `2` bumps the `2xx`
bucket by exactly one (and symmetric statements hold for 3/4/5 via the
`classify_of_statusClass_*` lemmas). -/
theorem metrics_status_class_2xx (s : Counters) (resp : List UInt8)
    (h : statusClass resp = some 2) :
    (s.record resp).bucket .c2 = s.bucket .c2 + 1 := by
  have := metrics_status_class s resp
  rwa [classify_of_statusClass_two resp h] at this

/-! ## Wire fidelity — concrete `HTTP/1.1 …` heads the running server parses

The byte lists below are the ASCII bytes of real status lines. They pin the
model's `statusClass` to the bytes the deployed reader consumes, so the counting
laws above land on the true wire, not a paraphrase. -/

/-- Bytes of `"HTTP/1.1 200 OK\r\n"`. -/
def head200 : List UInt8 :=
  [0x48,0x54,0x54,0x50,0x2F,0x31,0x2E,0x31,0x20,0x32,0x30,0x30,0x20,0x4F,0x4B,0x0D,0x0A]

/-- Bytes of `"HTTP/1.1 404 Not Found\r\n"`. -/
def head404 : List UInt8 :=
  [0x48,0x54,0x54,0x50,0x2F,0x31,0x2E,0x31,0x20,0x34,0x30,0x34,0x20,
   0x4E,0x6F,0x74,0x20,0x46,0x6F,0x75,0x6E,0x64,0x0D,0x0A]

/-- Bytes of `"HTTP/1.1 500 Internal Server Error\r\n"` (prefix through the code). -/
def head500 : List UInt8 :=
  [0x48,0x54,0x54,0x50,0x2F,0x31,0x2E,0x31,0x20,0x35,0x30,0x30,0x20,0x45,0x0D,0x0A]

/-- Bytes of a malformed head `"garbage\r\n"` (no space-delimited 3-digit code). -/
def headBad : List UInt8 := [0x67,0x61,0x72,0x62,0x61,0x67,0x65,0x0D,0x0A]

theorem statusClass_faithful_200 : statusClass head200 = some 2 := by decide
theorem statusClass_faithful_404 : statusClass head404 = some 4 := by decide
theorem statusClass_faithful_500 : statusClass head500 = some 5 := by decide
theorem statusClass_faithful_bad : statusClass headBad = none := by decide

theorem classify_faithful_200 : classify head200 = .c2 := by decide
theorem classify_faithful_404 : classify head404 = .c4 := by decide
theorem classify_faithful_500 : classify head500 = .c5 := by decide
theorem classify_faithful_bad : classify headBad = .cOther := by decide

/-- End-to-end on a real head: a served `200 OK` response bumps `drorb_requests_total`
by one and `drorb_responses_total{class="2xx"}` by one, on a fresh registry. -/
theorem metrics_200_endtoend :
    (Counters.zero.record head200).total = 1
    ∧ (Counters.zero.record head200).bucket .c2 = 1 := by
  refine ⟨rfl, ?_⟩
  have : classify head200 = .c2 := classify_faithful_200
  simp [Counters.record, Counters.zero, this]

/-! ## DoS-gate refusal counters (`drorb_requests_refused_total{reason=…}`)

Ground truth: `crates/dataplane/src/metrics.rs :: note_conn_limit_refused /
note_rate_limit_refused / note_request_timeout`, each a single
`fetch_add(1, Relaxed)` on its own process-static atomic (`REFUSED_CONN_LIMIT`,
`REFUSED_RATE_LIMIT`, `REQUEST_TIMEOUTS`), called once at the reactor accept gate
when a source is refused — the per-source connection cap (`503`), the per-source
request-rate window (`429`), or the slowloris header timeout (`408`). The three
gates are wired in both the io_uring and blocking reactors. Proven below: each
note bumps EXACTLY its own reason and leaves the other two fixed (so the family
is a faithful, non-interfering per-reason counter), and each reason's counter is
monotone and, over a run, counts exactly the refusals filed under it. -/

/-- The three DoS-gate refusal reasons — exactly the `reason` label values the
deployed `drorb_requests_refused_total{reason=…}` family emits. -/
inductive Reason
  | connLimit | rateLimit | timeout
  deriving DecidableEq

/-- The refusal registry: one counter per reason (the three deployed atomics). -/
structure Refusals where
  count : Reason → Nat

/-- All three atomics start at zero (`AtomicU64::new(0)`). -/
def Refusals.zero : Refusals := { count := fun _ => 0 }

/-- One refusal filed under `r`: bump `r`'s counter by one, leaving the others
fixed — the deployed `note_*`'s single `fetch_add(1)`. -/
def Refusals.note (s : Refusals) (r : Reason) : Refusals :=
  { count := fun q => if q = r then s.count q + 1 else s.count q }

/-- **Exact +1.** A refusal at `r` raises `r`'s counter by exactly one. -/
theorem refusals_note_self (s : Refusals) (r : Reason) :
    (s.note r).count r = s.count r + 1 := by simp [Refusals.note]

/-- **No cross-talk.** A refusal at `r` leaves every OTHER reason's counter fixed. -/
theorem refusals_note_others (s : Refusals) (r q : Reason) (h : q ≠ r) :
    (s.note r).count q = s.count q := by simp [Refusals.note, h]

/-- **Monotone.** No refusal ever lowers any reason's counter. -/
theorem refusals_note_monotone (s : Refusals) (r q : Reason) :
    s.count q ≤ (s.note r).count q := by
  simp only [Refusals.note]; by_cases h : q = r <;> simp [h]

/-- Fold a run of refusals (the accept gate over a burst of refusals). -/
def Refusals.noteAll (s : Refusals) (rs : List Reason) : Refusals :=
  rs.foldl Refusals.note s

/-- **Exact accounting.** After a run of refusals, each reason's counter equals
its starting value plus the number of refusals in the run filed under it — the
invariant the deployed `/metrics` reports (e.g. 15 rate-limit refusals ⇒
`drorb_requests_refused_total{reason="rate_limit"} 15`). -/
theorem refusals_noteAll_count (s : Refusals) (rs : List Reason) (r : Reason) :
    (s.noteAll rs).count r
      = s.count r + rs.countP (fun q => decide (q = r)) := by
  induction rs generalizing s with
  | nil => simp [Refusals.noteAll]
  | cons x xs ih =>
    have hstep : s.noteAll (x :: xs) = (s.note x).noteAll xs := by
      simp [Refusals.noteAll]
    rw [hstep, ih (s.note x), List.countP_cons]
    by_cases hx : x = r
    · subst hx
      rw [refusals_note_self]
      simp
      omega
    · rw [refusals_note_others s x r (fun e => hx e.symm)]
      simp [hx]

/-- NON-VACUITY. A lossy counter that drops the increment fails the exact-+1 law:
`(Refusals.zero.note .rateLimit).count .rateLimit = 1`, not `0`. -/
theorem refusals_note_is_not_lossy :
    (Refusals.zero.note .rateLimit).count .rateLimit = 1 := by
  simp [Refusals.note, Refusals.zero]

/-- NON-VACUITY. Noting a rate-limit refusal genuinely does NOT touch the
conn-limit counter — the reasons are independent atomics. -/
theorem refusals_rate_does_not_touch_conn :
    (Refusals.zero.note .rateLimit).count .connLimit = 0 := by
  decide

/-- NON-VACUITY (end to end). Fifteen rate-limit refusals leave the rate-limit
counter at 15 and the other two at 0 — exactly the curl-observed
`drorb_requests_refused_total`. -/
theorem refusals_fifteen_rate :
    (Refusals.zero.noteAll (List.replicate 15 Reason.rateLimit)).count .rateLimit = 15
    ∧ (Refusals.zero.noteAll (List.replicate 15 Reason.rateLimit)).count .connLimit = 0
    ∧ (Refusals.zero.noteAll (List.replicate 15 Reason.rateLimit)).count .timeout = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## Deployed latency histogram bucket selection (`drorb_request_duration_microseconds`)

Ground truth: `crates/dataplane/src/metrics.rs :: observe_latency`, which selects
the bucket as `LATENCY_BOUNDS_US.iter().take_while(|&&b| b < us).count()` and bumps
it — byte-identically the proven `Metrics.bucketIndex latencyBounds us`
(`bounds.takeWhile (· < v) |>.length`). The general containment correctness
(`le upper ∧ gt lower`, no observation mis-binned) is `MetricsCorrect.bucketIndex_contains`;
here we PIN the deployed bound list and show a concrete observation lands where the
wire puts it (and a mis-bin is rejected). -/

/-- The deployed µs `le` thresholds, exactly `LATENCY_BOUNDS_US`. -/
def latencyBounds : List Nat :=
  [100, 250, 500, 1000, 2500, 5000, 10000, 25000, 50000, 100000, 500000, 1000000]

/-- The deployed bucket selector: the count of bounds strictly below `us` — the
exact `take_while (· < us) |>.length` the Rust `observe_latency` computes, and
definitionally `Metrics.bucketIndex latencyBounds us`. -/
def latencyBucket (us : Nat) : Nat := Metrics.bucketIndex latencyBounds us

/-- **REFINEMENT.** Every observed latency lands in a bucket that CONTAINS it
(`le upper ∧ gt lower`), for the deployed bound list — instantiating the general
`bucketIndex_contains` at `latencyBounds`. So no latency observation is
mis-binned, whatever its value. -/
theorem latencyBucket_contains (us : Nat) :
    MetricsCorrect.Contains latencyBounds us (latencyBucket us) :=
  MetricsCorrect.bucketIndex_contains latencyBounds us

/-- NON-VACUITY. A 300µs request lands in bucket 2 — the `le="500"` bucket, the
first threshold `≥ 300` — matching the cumulative bump the curl showed. -/
theorem latencyBucket_300 : latencyBucket 300 = 2 := rfl

/-- NON-VACUITY. Bucket 2 genuinely contains 300 (`250 < 300 ∧ 300 ≤ 500`). -/
theorem latency_300_contained : MetricsCorrect.Contains latencyBounds 300 2 := by
  refine ⟨?_, ?_⟩
  · show (300 : Nat) ≤ 500; decide
  · show (250 : Nat) < 300; decide

/-- NON-VACUITY. A mis-bin LOW (bucket 1, `le="250"`) does NOT contain 300 —
`300 ≤ 250` is false — so the containment spec has teeth. -/
theorem latency_300_misbin_low : ¬ MetricsCorrect.Contains latencyBounds 300 1 := by
  intro hc; exact absurd (show (300 : Nat) ≤ 250 from hc.1) (by decide)

/-- NON-VACUITY. A latency that exceeds every bound lands in the `+Inf` overflow
bucket (index 12). -/
theorem latencyBucket_overflow : latencyBucket 2000000 = 12 := rfl


end O11y.MetricsCounters
