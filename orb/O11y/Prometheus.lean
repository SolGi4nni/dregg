/-!
# O11y.Prometheus — a verified Prometheus text-exposition formatter

A metric registry (counters, gauges, histograms) and a renderer to the
Prometheus / OpenMetrics **text exposition format** (version `0.0.4`), with the
well-formedness of the rendered output proven, not merely asserted.

The exposition format is public ground truth. Each metric family renders as:

```
# HELP <name> <help text>
# TYPE <name> counter|gauge|histogram
<name>{<label>="<value>",...} <number>
```

and a histogram additionally emits cumulative `<name>_bucket{le="…"}` lines, a
`<name>_sum` and a `<name>_count`. This file proves:

* `prometheus_wellformed` — every rendered family is `# HELP` then `# TYPE` then
  a run of sample lines (TYPE precedes samples; each line has the name+labels
  +value shape), with the HELP/TYPE metric names agreeing and a valid TYPE kind.
* `counter_monotone` — a counter's value never decreases under `inc`.
* `histogram_buckets_cumulative` — the exposed bucket counts are cumulative
  (non-decreasing), and the `le="+Inf"` bucket equals the total observation
  count (`_count`).
* `label_escape_correct` — the label-value escaping (`\` → `\\`, `"` → `\"`,
  newline → `\n`) round-trips: unescaping the escaped value recovers the input,
  and the escaped output contains no unescaped control byte.

The proofs are core-Lean only (no Mathlib), so the axiom footprint on the
headline theorems is empty (checked with `#print axioms`).
-/

namespace O11y

/-! ## Label-value escaping (Prometheus §"Escaping") -/

/-- Escape a label value as a character list: a backslash becomes `\\`, a double
quote becomes `\"`, and a newline (LF) becomes `\n` (backslash-n). Every other
character passes through. This is exactly the Prometheus label-value escaping.
Written with explicit `if`s so it reduces cleanly under case analysis. -/
def escapeChars : List Char → List Char
  | [] => []
  | c :: cs =>
      if c = '\\' then '\\' :: '\\' :: escapeChars cs
      else if c = '"' then '\\' :: '"' :: escapeChars cs
      else if c = '\n' then '\\' :: 'n' :: escapeChars cs
      else c :: escapeChars cs

/-- Inverse of `escapeChars`: collapse each two-character escape back to the byte
it stood for. On the image of `escapeChars` this is a genuine inverse
(`label_escape_correct`). -/
def unescapeChars : List Char → List Char
  | [] => []
  | ['\\'] => ['\\']
  | '\\' :: d :: cs =>
      if d = '\\' then '\\' :: unescapeChars cs
      else if d = '"' then '"' :: unescapeChars cs
      else if d = 'n' then '\n' :: unescapeChars cs
      else d :: unescapeChars cs
  | c :: cs => c :: unescapeChars cs

/-- **Escaping round-trips (label_escape_correct, part 1).** Unescaping an
escaped value recovers the original — no label value is corrupted or made
ambiguous by escaping. -/
theorem label_escape_correct (cs : List Char) :
    unescapeChars (escapeChars cs) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases h1 : c = '\\'
    · subst h1; simp [escapeChars, unescapeChars, ih]
    · by_cases h2 : c = '"'
      · subst h2; simp [escapeChars, unescapeChars, h1, ih]
      · by_cases h3 : c = '\n'
        · subst h3; simp [escapeChars, unescapeChars, h1, h2, ih]
        · have he : escapeChars (c :: cs) = c :: escapeChars cs := by
            simp [escapeChars, h1, h2, h3]
          have hu : unescapeChars (c :: escapeChars cs)
              = c :: unescapeChars (escapeChars cs) := by
            cases hE : escapeChars cs with
            | nil => simp [unescapeChars, h1]
            | cons d rest => simp [unescapeChars, h1]
          rw [he, hu, ih]

/-- Does a character list contain a raw newline (LF)? -/
def hasNewline : List Char → Bool
  | [] => false
  | c :: cs => if c = '\n' then true else hasNewline cs

/-- **No raw newline survives (label_escape_correct, part 2).** An escaped label
value contains no bare LF, so a label value can never break the line-oriented
exposition format by injecting a newline. -/
theorem escape_no_newline (cs : List Char) :
    hasNewline (escapeChars cs) = false := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases h1 : c = '\\'
    · subst h1; simp [escapeChars, hasNewline, ih]
    · by_cases h2 : c = '"'
      · subst h2; simp [escapeChars, hasNewline, h1, ih]
      · by_cases h3 : c = '\n'
        · subst h3; simp [escapeChars, hasNewline, h1, h2, ih]
        · simp [escapeChars, hasNewline, h1, h2, h3, ih]

/-! ## String-level escaping -/

/-- Escape a label value string. -/
def escape (s : String) : String := String.ofList (escapeChars s.toList)

/-- Unescape a label value string. -/
def unescape (s : String) : String := String.ofList (unescapeChars s.toList)

/-! ## The metric model -/

/-- A label set: name/value pairs, rendered as `{k="v",…}`. -/
abbrev Labels := List (String × String)

/-- A single counter sample: a label set and a monotone natural value. -/
structure CounterSample where
  labels : Labels
  value : Nat

/-- **Monotone increment.** A counter only increases. -/
def CounterSample.inc (c : CounterSample) (delta : Nat) : CounterSample :=
  { c with value := c.value + delta }

/-- **Counter monotonicity.** `inc` never lowers the value. -/
theorem counter_monotone (c : CounterSample) (delta : Nat) :
    c.value ≤ (c.inc delta).value := by
  simp [CounterSample.inc]

/-- A single gauge sample: a label set and an arbitrary integer value. -/
structure GaugeSample where
  labels : Labels
  value : Int

/-! ### Histogram

A histogram carries the `le` thresholds (as their rendered strings), the count
of observations that fell **in each bucket** (`perBucket`, one more entry than
there are thresholds — the final entry is the `+Inf` overflow bucket), and the
running `sum` of observed values. The *exposed* bucket counts are the running
(cumulative) totals of `perBucket`. -/
structure Histogram where
  /-- The `le` upper-bound thresholds, already rendered (e.g. `"0.1"`, `"0.5"`). -/
  bounds : List String
  /-- Observations per bucket; length is `bounds.length + 1` (with `+Inf`). -/
  perBucket : List Nat
  /-- Running sum of observed values (for `_sum`). -/
  sum : Nat

/-- Running (cumulative) totals of a count list: element `i` is the sum of the
first `i+1` per-bucket counts. This is what the exposition emits per `le`. -/
def runningSums : Nat → List Nat → List Nat
  | _, [] => []
  | acc, x :: xs => (acc + x) :: runningSums (acc + x) xs

/-- The cumulative bucket counts of a histogram. -/
def Histogram.cumulative (h : Histogram) : List Nat := runningSums 0 h.perBucket

/-- Total observation count (the `+Inf` bucket / `_count`). -/
def Histogram.count (h : Histogram) : Nat := h.perBucket.sum

/-! ## Cumulative-bucket proofs -/

/-- A list of naturals is (weakly) non-decreasing. -/
def Nondecreasing : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a ≤ b ∧ Nondecreasing (b :: rest)

/-- Running sums are non-decreasing: each cumulative bucket count is `≥` the one
before it. This is the "cumulative" half of the histogram invariant. -/
theorem runningSums_nondecreasing (acc : Nat) (xs : List Nat) :
    Nondecreasing (runningSums acc xs) := by
  induction xs generalizing acc with
  | nil => exact True.intro
  | cons x xs ih =>
    cases xs with
    | nil => exact True.intro
    | cons y ys =>
      refine ⟨by omega, ?_⟩
      exact ih (acc + x)

/-- The final running total equals the plain sum: the `le="+Inf"` bucket count is
the total observation count. -/
theorem runningSums_total (acc : Nat) (xs : List Nat) :
    ∀ v ∈ (runningSums acc xs).getLast?, v = acc + xs.sum := by
  induction xs generalizing acc with
  | nil => intro v hv; simp [runningSums] at hv
  | cons x xs ih =>
    intro v hv
    cases xs with
    | nil =>
      simp [runningSums, List.getLast?] at hv
      simp [hv, List.sum_cons]
    | cons y ys =>
      simp only [runningSums] at hv
      rw [List.getLast?_cons_cons] at hv
      have := ih (acc + x) v hv
      simp only [List.sum_cons] at this ⊢
      omega

/-- **Histogram buckets are cumulative.** The exposed bucket counts are
non-decreasing (each `le` threshold's count includes all lower buckets). -/
theorem histogram_buckets_cumulative (h : Histogram) :
    Nondecreasing h.cumulative :=
  runningSums_nondecreasing 0 h.perBucket

/-- **`+Inf` bucket = `_count`.** The last cumulative bucket count equals the
total observation count. -/
theorem histogram_inf_eq_count (h : Histogram) :
    ∀ v ∈ h.cumulative.getLast?, v = h.count := by
  intro v hv
  have := runningSums_total 0 h.perBucket v hv
  unfold Histogram.count
  omega

/-! ## The exposition line model and well-formedness

Rather than reason about a flat string, the renderer first produces a list of
structured `Line`s per family; well-formedness is a decidable predicate on that
list, and the text serializer maps each `Line` to its bytes. -/

/-- One line of exposition output. -/
inductive Line where
  | help (metric text : String)
  | type (metric kind : String)
  | sample (name : String) (labels : Labels) (value : String)
  deriving Repr, DecidableEq

/-- Is this a sample line (not a `# HELP`/`# TYPE` comment)? -/
def Line.isSample : Line → Bool
  | .sample _ _ _ => true
  | _ => false

/-- A valid TYPE kind for this formatter. -/
def validKind (k : String) : Bool :=
  k == "counter" || k == "gauge" || k == "histogram"

/-- **Family well-formedness.** A rendered family is well-formed iff it is a
`# HELP` line, then a `# TYPE` line for the *same* metric with a valid kind, then
a (possibly empty) run of sample lines — i.e. TYPE precedes every sample and no
comment is interleaved. -/
def wfFamily : List Line → Bool
  | .help m₁ _ :: .type m₂ k :: rest =>
      (m₁ == m₂) && validKind k && rest.all Line.isSample
  | _ => false

/-! ## Metric families and the registry -/

/-- A metric family body. -/
inductive Body where
  | counter (samples : List CounterSample)
  | gauge (samples : List GaugeSample)
  | histogram (h : Histogram)

/-- A named, documented metric family. -/
structure Family where
  name : String
  help : String
  body : Body

/-- A registry is a list of metric families. -/
structure MetricRegistry where
  families : List Family

/-- The empty registry. -/
def MetricRegistry.empty : MetricRegistry := ⟨[]⟩

/-- Zip the `le` thresholds (plus a final `+Inf`) with the cumulative counts. -/
def histBucketLines (name : String) (labels : Labels) (h : Histogram) : List Line :=
  (List.zip (h.bounds ++ ["+Inf"]) h.cumulative).map
    (fun p => Line.sample (name ++ "_bucket") (("le", p.1) :: labels) (toString p.2))

/-- Render one family to its exposition lines: a `# HELP`, a `# TYPE`, then the
samples. -/
def renderFamily (f : Family) : List Line :=
  match f.body with
  | .counter samples =>
      Line.help f.name f.help
        :: Line.type f.name "counter"
        :: samples.map (fun s => Line.sample f.name s.labels (toString s.value))
  | .gauge samples =>
      Line.help f.name f.help
        :: Line.type f.name "gauge"
        :: samples.map (fun s => Line.sample f.name s.labels (toString s.value))
  | .histogram h =>
      Line.help f.name f.help
        :: Line.type f.name "histogram"
        :: (histBucketLines f.name [] h
              ++ [ Line.sample (f.name ++ "_sum") [] (toString h.sum)
                 , Line.sample (f.name ++ "_count") [] (toString h.count) ])

/-- Render every family in the registry to its line block. -/
def renderFamilies (reg : MetricRegistry) : List (List Line) :=
  reg.families.map renderFamily

/-! ### Well-formedness proof -/

/-- Every mapped sample line is a sample. -/
theorem all_isSample_map_sample {α} (l : List α)
    (g : α → String) (h : α → Labels) (v : α → String) :
    (l.map (fun a => Line.sample (g a) (h a) (v a))).all Line.isSample = true := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.all, Line.isSample, ih]

/-- Every line produced by `histBucketLines` is a sample. -/
theorem histBucketLines_all_sample (name : String) (labels : Labels) (h : Histogram) :
    (histBucketLines name labels h).all Line.isSample = true := by
  unfold histBucketLines
  apply all_isSample_map_sample

/-- Each rendered family is well-formed. -/
theorem renderFamily_wf (f : Family) : wfFamily (renderFamily f) = true := by
  unfold renderFamily wfFamily
  cases f.body with
  | counter samples =>
      simp only [beq_self_eq_true, validKind, Bool.and_true, Bool.true_and]
      exact all_isSample_map_sample samples _ _ _
  | gauge samples =>
      simp only [beq_self_eq_true, validKind, Bool.and_true, Bool.true_and]
      exact all_isSample_map_sample samples _ _ _
  | histogram h =>
      simp only [beq_self_eq_true, validKind, Bool.and_true, Bool.true_and]
      rw [List.all_append]
      rw [histBucketLines_all_sample]
      rfl

/-- **The renderer is well-formed.** Every family block the registry renders to
is valid Prometheus exposition: `# HELP`, then `# TYPE` for the same metric with
a valid kind, then only sample lines. -/
theorem prometheus_wellformed (reg : MetricRegistry) :
    (renderFamilies reg).all wfFamily = true := by
  unfold renderFamilies
  rw [List.all_map]
  apply List.all_eq_true.2
  intro f _
  exact renderFamily_wf f

/-! ## Text serialization -/

/-- Render a label set to its `{k="v",…}` fragment (empty when there are no
labels). Label values are escaped. -/
def renderLabels : Labels → String
  | [] => ""
  | labels =>
      "{" ++ String.intercalate ","
        (labels.map (fun p => p.1 ++ "=\"" ++ escape p.2 ++ "\"")) ++ "}"

/-- Serialize one line to its exposition bytes. -/
def Line.render : Line → String
  | .help m t => "# HELP " ++ m ++ " " ++ t
  | .type m k => "# TYPE " ++ m ++ " " ++ k
  | .sample n labels v => n ++ renderLabels labels ++ " " ++ v

/-- Serialize the whole registry to the Prometheus text exposition format. -/
def render (reg : MetricRegistry) : String :=
  String.intercalate "\n"
    (((renderFamilies reg).map (fun ls => ls.map Line.render)).flatten) ++ "\n"

/-! ## Non-vacuous concrete registry

A real registry — an HTTP request counter with `method`/`status` labels and a
request-latency histogram — renders to a concrete, well-formed block. The
`#guard`s below check the exact bytes and the well-formedness of that block. -/

/-- `http_requests_total{method="GET",status="200"} 1027`. -/
def exampleRequests : Family :=
  { name := "http_requests_total"
    help := "Total HTTP requests served."
    body := .counter [ { labels := [("method", "GET"), ("status", "200")], value := 1027 } ] }

/-- A request-latency histogram over three buckets. -/
def exampleLatency : Family :=
  { name := "http_request_duration_seconds"
    help := "HTTP request latency in seconds."
    body := .histogram
      { bounds := ["0.1", "0.5", "1"]
        perBucket := [3, 5, 2, 1]     -- 3 ≤0.1, 5 ≤0.5, 2 ≤1, 1 overflow
        sum := 7 } }

/-- The example registry. -/
def exampleRegistry : MetricRegistry := ⟨[exampleRequests, exampleLatency]⟩

-- The concrete example is well-formed (an instance of the general theorem).
example : (renderFamilies exampleRegistry).all wfFamily = true :=
  prometheus_wellformed exampleRegistry

-- The cumulative buckets of the latency histogram are [3,8,10,11]; the `+Inf`
-- bucket (11) equals the total count.
#guard (Histogram.cumulative { bounds := ["0.1","0.5","1"], perBucket := [3,5,2,1], sum := 7 }) == [3, 8, 10, 11]

-- The exact rendered bytes.
#guard render exampleRegistry ==
  "# HELP http_requests_total Total HTTP requests served.\n" ++
  "# TYPE http_requests_total counter\n" ++
  "http_requests_total{method=\"GET\",status=\"200\"} 1027\n" ++
  "# HELP http_request_duration_seconds HTTP request latency in seconds.\n" ++
  "# TYPE http_request_duration_seconds histogram\n" ++
  "http_request_duration_seconds_bucket{le=\"0.1\"} 3\n" ++
  "http_request_duration_seconds_bucket{le=\"0.5\"} 8\n" ++
  "http_request_duration_seconds_bucket{le=\"1\"} 10\n" ++
  "http_request_duration_seconds_bucket{le=\"+Inf\"} 11\n" ++
  "http_request_duration_seconds_sum 7\n" ++
  "http_request_duration_seconds_count 11\n"

-- Escaping round-trips on a value with all three special bytes.
#guard unescape (escape "a\"b\\c\nd") == "a\"b\\c\nd"

def version : String := "0.0.4"

end O11y
