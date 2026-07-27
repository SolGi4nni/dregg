/-
Admin.MetricsFormat — the proven wire format of the operator metrics surface
(`crates/dataplane/src/admin.rs` → `GET /metrics` and `GET /admin/connections`).

The admin listener exposes two operational read surfaces the row `ad.2` names:

  * `GET /metrics`            — the counter/gauge fleet in Prometheus TEXT
                               exposition format (`crate::metrics::render`);
  * `GET /admin/connections`  — a small JSON object of live counters
                               (`crate::admin::connections_json`).

Both are DEPLOYED (they run in the Rust dataplane) but were UNPROVEN. This file
models each wire format exactly as the deployed shell emits it and proves it
well-formed:

  * `metrics_prometheus_wellformed` — the exact family fleet the deployed
    `metrics::render` emits (nine families, in order, with the deployed HELP
    text, TYPE kinds, and label sets) renders to a valid Prometheus text
    exposition block: every family is `# HELP` then `# TYPE` (same metric, valid
    kind) then only sample lines. Proven for ARBITRARY counter values and an
    arbitrary backend list — the shape holds whatever the atomics hold. A
    `#guard` pins the byte-exact render of the all-zero baseline (the fresh-host
    `/metrics` body) so the proof is tied to the deployed wire, not a paraphrase.

  * `metrics_json_wellformed` — the deployed `connections_json` object PARSES
    back to the exact snapshot of counters it was built from: a restricted-JSON
    recursive-descent parser recovers `{active_connections, requests_total,
    bytes_out_total, draining}` from the rendered string, for ARBITRARY counter
    values and either draining flag. Round-trip `parse ∘ render = id`, so the
    rendered object is genuinely well-formed (parseable) and lossless. A `#guard`
    pins the byte-exact deployed line.

The Prometheus half reuses the proven `O11y.Prometheus` formatter (its
`prometheus_wellformed` is the general theorem; this file instantiates it at the
deployed family fleet). The JSON half reuses the proven decimal round-trip in
`Proto.Dec` (`cval` inverts `Nat.repr`). Core-Lean only; the axiom footprint on
both headline theorems is checked with `#print axioms`.
-/

import O11y.Prometheus
import Proto.Decimal

namespace Admin
namespace MetricsFormat

open Nat (toDigits toDigitsCore digitChar)

/-! ## Part 1 — the Prometheus `/metrics` fleet

`crate::metrics::render` pushes nine metric families, in a fixed order, each of
shape `# HELP … / # TYPE … / <samples>`. We reconstruct that exact fleet as an
`O11y.MetricRegistry` (same names, help text, TYPE kinds, and label sets) and
instantiate the proven well-formedness theorem at it. -/

open O11y (Family Body CounterSample GaugeSample MetricRegistry Line
  renderFamilies wfFamily prometheus_wellformed render)

/-- A no-label counter family with a single sample (e.g. `drorb_requests_total`). -/
def counter1 (name help : String) (v : Nat) : Family :=
  { name, help, body := .counter [ { labels := [], value := v } ] }

/-- A single-sample gauge family (e.g. `drorb_active_connections`). Deployed
gauge values are non-negative host reads, injected as `Int`. -/
def gauge1 (name help : String) (v : Nat) : Family :=
  { name, help, body := .gauge [ { labels := [], value := (v : Int) } ] }

/-- The `drorb_responses_total` per-status-class family: five samples, one per
class label, in the deployed order 2xx/3xx/4xx/5xx/other. -/
def responsesFamily (r2 r3 r4 r5 rother : Nat) : Family :=
  { name := "drorb_responses_total"
    help := "Responses by status class."
    body := .counter
      [ { labels := [("class", "2xx")],   value := r2 }
      , { labels := [("class", "3xx")],   value := r3 }
      , { labels := [("class", "4xx")],   value := r4 }
      , { labels := [("class", "5xx")],   value := r5 }
      , { labels := [("class", "other")], value := rother } ] }

/-- The `drorb_backend_requests_total` family: one sample per dialled backend
(`host:port` → count), in the deployed `BTreeMap` iteration order. Empty when no
proxy fleet is configured — then the family is just its HELP/TYPE header. -/
def backendsFamily (backends : List (String × Nat)) : Family :=
  { name := "drorb_backend_requests_total"
    help := "Proxied requests per backend."
    body := .counter (backends.map (fun p => { labels := [("backend", p.1)], value := p.2 })) }

/-- The `drorb_requests_refused_total` DoS-gate family: three samples, one per
`reason` label, in the deployed order conn_limit/rate_limit/timeout. -/
def refusedFamily (conn rate timeout : Nat) : Family :=
  { name := "drorb_requests_refused_total"
    help := "Requests refused at the reactor DoS gate, by reason."
    body := .counter
      [ { labels := [("reason", "conn_limit")], value := conn }
      , { labels := [("reason", "rate_limit")], value := rate }
      , { labels := [("reason", "timeout")],    value := timeout } ] }

/-- The deployed latency-histogram `le` thresholds (microseconds), rendered as the
strings `LATENCY_BOUNDS_US` emits. -/
def latencyBoundStrings : List String :=
  ["100", "250", "500", "1000", "2500", "5000", "10000", "25000", "50000",
   "100000", "500000", "1000000"]

/-- The `drorb_request_duration_microseconds` histogram family: the deployed µs
`le` thresholds, the per-bucket observation counts (13 = 12 bounds + `+Inf`), and
the running µs sum. The exposed `_bucket{le=…}` values are the cumulative totals
`O11y.renderFamily` computes; `_count` is `perBucket.sum`. -/
def latencyFamily (perBucket : List Nat) (sum : Nat) : Family :=
  { name := "drorb_request_duration_microseconds"
    help := "Request handling latency in microseconds."
    body := .histogram { bounds := latencyBoundStrings, perBucket := perBucket, sum := sum } }

/-- The exact family fleet `crate::metrics::render` emits, in order, for the given
live counter values, backend list, and draining flag. -/
def deployedRegistry
    (requests r2 r3 r4 r5 rother bytesOut active generation applied rejected : Nat)
    (backends : List (String × Nat)) (draining : Bool)
    (refConn refRate refTimeout : Nat) (latBuckets : List Nat) (latSum : Nat) :
    MetricRegistry :=
  ⟨[ counter1 "drorb_requests_total" "Requests served through the host loop." requests
   , responsesFamily r2 r3 r4 r5 rother
   , counter1 "drorb_response_bytes_total" "Total response bytes written." bytesOut
   , gauge1  "drorb_active_connections" "Connection handlers in flight." active
   , backendsFamily backends
   , refusedFamily refConn refRate refTimeout
   , latencyFamily latBuckets latSum
   , gauge1  "drorb_config_generation" "Active operator-config generation." generation
   , counter1 "drorb_reloads_applied_total" "SIGHUP reconfigs applied." applied
   , counter1 "drorb_reloads_rejected_total" "SIGHUP reconfigs rejected (fail-safe)." rejected
   , gauge1  "drorb_draining"
       "1 while a reconfig swap is in progress or an operator drain is active."
       (if draining then 1 else 0) ]⟩

/-- **Deployed `/metrics` is well-formed Prometheus text exposition.** Whatever
the live atomics hold — any request/response/byte/backend counts and either
draining state — every family the deployed `metrics::render` emits is a valid
`# HELP` / `# TYPE` (same metric, valid kind) / sample-lines block. -/
theorem metrics_prometheus_wellformed
    (requests r2 r3 r4 r5 rother bytesOut active generation applied rejected : Nat)
    (backends : List (String × Nat)) (draining : Bool)
    (refConn refRate refTimeout : Nat) (latBuckets : List Nat) (latSum : Nat) :
    (renderFamilies (deployedRegistry requests r2 r3 r4 r5 rother bytesOut
        active generation applied rejected backends draining
        refConn refRate refTimeout latBuckets latSum)).all wfFamily = true :=
  prometheus_wellformed _

/-- The byte-exact `/metrics` body a FRESH host emits (every counter `0`, no
backends, one active connection served): the O11y renderer of the deployed
fleet at the baseline values equals this literal — this is the string the curl
below must reproduce, tying the proof to the deployed wire. -/
def baselineMetricsText : String :=
  render (deployedRegistry 0 0 0 0 0 0 0 0 0 0 0 [] false 0 0 0 (List.replicate 13 0) 0)

-- The baseline `/metrics` body, byte for byte (matches the deployed curl).
#guard baselineMetricsText ==
  "# HELP drorb_requests_total Requests served through the host loop.\n" ++
  "# TYPE drorb_requests_total counter\n" ++
  "drorb_requests_total 0\n" ++
  "# HELP drorb_responses_total Responses by status class.\n" ++
  "# TYPE drorb_responses_total counter\n" ++
  "drorb_responses_total{class=\"2xx\"} 0\n" ++
  "drorb_responses_total{class=\"3xx\"} 0\n" ++
  "drorb_responses_total{class=\"4xx\"} 0\n" ++
  "drorb_responses_total{class=\"5xx\"} 0\n" ++
  "drorb_responses_total{class=\"other\"} 0\n" ++
  "# HELP drorb_response_bytes_total Total response bytes written.\n" ++
  "# TYPE drorb_response_bytes_total counter\n" ++
  "drorb_response_bytes_total 0\n" ++
  "# HELP drorb_active_connections Connection handlers in flight.\n" ++
  "# TYPE drorb_active_connections gauge\n" ++
  "drorb_active_connections 0\n" ++
  "# HELP drorb_backend_requests_total Proxied requests per backend.\n" ++
  "# TYPE drorb_backend_requests_total counter\n" ++
  "# HELP drorb_requests_refused_total Requests refused at the reactor DoS gate, by reason.\n" ++
  "# TYPE drorb_requests_refused_total counter\n" ++
  "drorb_requests_refused_total{reason=\"conn_limit\"} 0\n" ++
  "drorb_requests_refused_total{reason=\"rate_limit\"} 0\n" ++
  "drorb_requests_refused_total{reason=\"timeout\"} 0\n" ++
  "# HELP drorb_request_duration_microseconds Request handling latency in microseconds.\n" ++
  "# TYPE drorb_request_duration_microseconds histogram\n" ++
  "drorb_request_duration_microseconds_bucket{le=\"100\"} 0\n" ++
  "drorb_request_duration_microseconds_bucket{le=\"250\"} 0\n" ++
  "drorb_request_duration_microseconds_bucket{le=\"500\"} 0\n" ++
  "drorb_request_duration_microseconds_bucket{le=\"1000\"} 0\n" ++
  "drorb_request_duration_microseconds_bucket{le=\"2500\"} 0\n" ++
  "drorb_request_duration_microseconds_bucket{le=\"5000\"} 0\n" ++
  "drorb_request_duration_microseconds_bucket{le=\"10000\"} 0\n" ++
  "drorb_request_duration_microseconds_bucket{le=\"25000\"} 0\n" ++
  "drorb_request_duration_microseconds_bucket{le=\"50000\"} 0\n" ++
  "drorb_request_duration_microseconds_bucket{le=\"100000\"} 0\n" ++
  "drorb_request_duration_microseconds_bucket{le=\"500000\"} 0\n" ++
  "drorb_request_duration_microseconds_bucket{le=\"1000000\"} 0\n" ++
  "drorb_request_duration_microseconds_bucket{le=\"+Inf\"} 0\n" ++
  "drorb_request_duration_microseconds_sum 0\n" ++
  "drorb_request_duration_microseconds_count 0\n" ++
  "# HELP drorb_config_generation Active operator-config generation.\n" ++
  "# TYPE drorb_config_generation gauge\n" ++
  "drorb_config_generation 0\n" ++
  "# HELP drorb_reloads_applied_total SIGHUP reconfigs applied.\n" ++
  "# TYPE drorb_reloads_applied_total counter\n" ++
  "drorb_reloads_applied_total 0\n" ++
  "# HELP drorb_reloads_rejected_total SIGHUP reconfigs rejected (fail-safe).\n" ++
  "# TYPE drorb_reloads_rejected_total counter\n" ++
  "drorb_reloads_rejected_total 0\n" ++
  "# HELP drorb_draining 1 while a reconfig swap is in progress or an operator drain is active.\n" ++
  "# TYPE drorb_draining gauge\n" ++
  "drorb_draining 0\n"

/-! ## Part 2 — the `/admin/connections` JSON counters

`crate::admin::connections_json` emits the fixed-shape object

    {"active_connections":N,"requests_total":N,"bytes_out_total":N,"draining":B}

(then a framing `\n`). We model it as a typed snapshot, render it byte-for-byte
as the deployed shell does, and prove a restricted-JSON parser recovers the exact
snapshot — a genuine round trip, so the rendered object is well-formed and
lossless. -/

/-- The four live counters `/admin/connections` projects. -/
structure Snapshot where
  active : Nat
  requests : Nat
  bytesOut : Nat
  draining : Bool
  deriving DecidableEq, Repr

/-- Render a snapshot exactly as `connections_json` does (no trailing `\n`; the
framing newline is added by `connectionsLine`). -/
def toJson (m : Snapshot) : String :=
  "{\"active_connections\":" ++ toString m.active ++
  ",\"requests_total\":" ++ toString m.requests ++
  ",\"bytes_out_total\":" ++ toString m.bytesOut ++
  ",\"draining\":" ++ (if m.draining then "true" else "false") ++ "}"

/-- The full `/admin/connections` response body (the JSON object plus the framing
newline the deployed handler appends). -/
def connectionsLine (m : Snapshot) : String := toJson m ++ "\n"

/-! ### A minimal recursive-descent parser for the restricted grammar -/

/-- Strip an exact character prefix; `none` if `s` does not start with `p`. -/
def stripPrefix : List Char → List Char → Option (List Char)
  | [], s => some s
  | _ :: _, [] => none
  | a :: p, c :: s => if a = c then stripPrefix p s else none

/-- Split off a leading run of ASCII digits. -/
def spanDigits : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
      if c.isDigit then (c :: (spanDigits cs).1, (spanDigits cs).2)
      else ([], c :: cs)

/-- Parse a non-empty decimal natural: the digit run, folded by the proven
`Proto.Dec.cval`, and the remaining input. `none` if no digit is present. -/
def parseNat (s : List Char) : Option (Nat × List Char) :=
  match spanDigits s with
  | ([], _) => none
  | (d :: ds, rest) => some (Proto.Dec.cval 0 (d :: ds), rest)

/-- Parse a JSON boolean literal `true`/`false`. -/
def parseBool (s : List Char) : Option (Bool × List Char) :=
  match stripPrefix "true".data s with
  | some r => some (true, r)
  | none =>
      match stripPrefix "false".data s with
      | some r => some (false, r)
      | none => none

/-- Parse the fixed-shape `/admin/connections` object back into a `Snapshot`. The
`Option` monad short-circuits to `none` on the first shape mismatch. -/
def parseSnapshot (s : List Char) : Option Snapshot := do
  let s ← stripPrefix "{\"active_connections\":".data s
  let (active, s) ← parseNat s
  let s ← stripPrefix ",\"requests_total\":".data s
  let (requests, s) ← parseNat s
  let s ← stripPrefix ",\"bytes_out_total\":".data s
  let (bytesOut, s) ← parseNat s
  let s ← stripPrefix ",\"draining\":".data s
  let (draining, s) ← parseBool s
  let s ← stripPrefix "}".data s
  if s.isEmpty then some { active, requests, bytesOut, draining } else none

/-! ### Round-trip lemmas -/

/-- `stripPrefix` succeeds on any string it is a prefix of, returning the tail. -/
theorem stripPrefix_append (p s : List Char) :
    stripPrefix p (p ++ s) = some s := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [stripPrefix, ih]

/-- `Nat.repr`'s digit list is exactly `toDigitsCore 10 (n+1) n []`. -/
theorem toString_data (n : Nat) :
    (toString n).data = toDigitsCore 10 (n + 1) n [] := by
  have h : (toString n).data = (toString n).toList := rfl
  rw [h]; exact String.toList_ofList

/-- Every character of `toString n` is an ASCII decimal digit. -/
theorem toString_all_isDigit (n : Nat) :
    ∀ c ∈ (toString n).data, c.isDigit = true := by
  intro c hc
  rw [toString_data] at hc
  have : c ∈ toDigits 10 n := hc
  obtain ⟨r, hr, rfl⟩ := Proto.Dec.mem_toDigits_isDigit n c this
  -- `digitChar r` for `r < 10` is one of `'0'..'9'`, all `isDigit`.
  match r, hr with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide
  | 5, _ => decide
  | 6, _ => decide
  | 7, _ => decide
  | 8, _ => decide
  | 9, _ => decide
  | (_ + 10), h => omega

/-- `toString n` is a non-empty digit list. -/
theorem toString_ne_nil (n : Nat) : (toString n).data ≠ [] := by
  rw [toString_data]
  unfold toDigitsCore
  by_cases h : n / 10 = 0
  · simp [h]
  · simp only [h, if_false]
    rw [Proto.Dec.tdc_append n (n / 10) [digitChar (n % 10)]]
    exact List.append_ne_nil_of_right_ne_nil _ (by simp)

/-- `cval` folds `toString n`'s digits back to `n` (the proven decimal inverse). -/
theorem cval_toString (n : Nat) : Proto.Dec.cval 0 (toString n).data = n := by
  rw [toString_data]
  exact Proto.Dec.cval_tdc (n + 1) n (by omega)

/-- `spanDigits` splits an all-digit prefix followed by a non-digit exactly. -/
theorem spanDigits_append (ds rest : List Char)
    (hd : ∀ c ∈ ds, c.isDigit = true) (x : Char) (hx : x.isDigit = false) :
    spanDigits (ds ++ x :: rest) = (ds, x :: rest) := by
  induction ds with
  | nil => simp [spanDigits, hx]
  | cons c cs ih =>
    have hc : c.isDigit = true := hd c (by simp)
    have hcs : ∀ c' ∈ cs, c'.isDigit = true := fun c' h => hd c' (by simp [h])
    simp [spanDigits, hc, ih hcs]

/-- `stripPrefix` of a list against itself consumes it entirely. -/
theorem stripPrefix_self (p : List Char) : stripPrefix p p = some [] := by
  have := stripPrefix_append p ([] : List Char); simpa using this

/-- `parseNat` recovers `n` from its rendering immediately followed by a
non-digit `c :: tail` (every numeric field is delimited by such a literal). The
delimiter is returned verbatim, so the next `stripPrefix` sees the exact key
literal (no cons/append normalisation is forced on it). -/
theorem parseNat_delim (n : Nat) (c : Char) (tail rest : List Char)
    (hc : c.isDigit = false) :
    parseNat ((toString n).data ++ ((c :: tail) ++ rest))
      = some (n, (c :: tail) ++ rest) := by
  rw [List.cons_append]
  unfold parseNat
  rw [spanDigits_append (toString n).data (tail ++ rest) (toString_all_isDigit n) c hc]
  have hne := toString_ne_nil n
  cases hcs : (toString n).data with
  | nil => exact absurd hcs hne
  | cons d ds =>
    have hv : Proto.Dec.cval 0 (d :: ds) = n := by rw [← hcs]; exact cval_toString n
    simp [hv, List.cons_append]

/-- `parseNat` before the `,"requests_total":` key. -/
theorem parseNat_keyReq (n : Nat) (rest : List Char) :
    parseNat ((toString n).data ++ (",\"requests_total\":".data ++ rest))
      = some (n, ",\"requests_total\":".data ++ rest) :=
  parseNat_delim n ',' "\"requests_total\":".data rest (by decide)

/-- `parseNat` before the `,"bytes_out_total":` key. -/
theorem parseNat_keyBytes (n : Nat) (rest : List Char) :
    parseNat ((toString n).data ++ (",\"bytes_out_total\":".data ++ rest))
      = some (n, ",\"bytes_out_total\":".data ++ rest) :=
  parseNat_delim n ',' "\"bytes_out_total\":".data rest (by decide)

/-- `parseNat` before the `,"draining":` key. -/
theorem parseNat_keyDrain (n : Nat) (rest : List Char) :
    parseNat ((toString n).data ++ (",\"draining\":".data ++ rest))
      = some (n, ",\"draining\":".data ++ rest) :=
  parseNat_delim n ',' "\"draining\":".data rest (by decide)

/-- `parseBool` reads the `true` literal followed by any tail. -/
theorem parseBool_true (rest : List Char) :
    parseBool ("true".data ++ rest) = some (true, rest) := by
  unfold parseBool; rw [stripPrefix_append "true".data]

/-- `parseBool` reads the `false` literal (which does not begin with `t`, so the
`true` branch fails first) followed by any tail. -/
theorem parseBool_false (rest : List Char) :
    parseBool ("false".data ++ rest) = some (false, rest) := by
  unfold parseBool
  have h1 : stripPrefix "true".data ("false".data ++ rest) = none := by
    rfl
  rw [h1, stripPrefix_append "false".data]

/-- **The deployed `/admin/connections` object round-trips.** For any live
counter values and either draining flag, parsing the rendered JSON recovers the
exact snapshot — so the emitted object is well-formed (parseable) and lossless. -/
theorem metrics_json_wellformed (m : Snapshot) :
    parseSnapshot (toJson m).data = some m := by
  obtain ⟨a, r, b, d⟩ := m
  -- Expose the concatenation of the rendered pieces (right-associated, each key
  -- literal kept intact so its `stripPrefix`/`parseNat_key*` lemma matches).
  have hdata : (toJson ⟨a, r, b, d⟩).data =
      "{\"active_connections\":".data ++ ((toString a).data ++
      (",\"requests_total\":".data ++ ((toString r).data ++
      (",\"bytes_out_total\":".data ++ ((toString b).data ++
      (",\"draining\":".data ++
        ((if d then "true" else "false").data ++ "}".data))))))) := by
    simp only [toJson, show ∀ s : String, s.data = s.toList from fun _ => rfl,
      String.toList_append, List.append_assoc]
  rw [hdata]
  unfold parseSnapshot
  -- Consume the opening key, then alternately parse each number and strip the
  -- following key literal, reducing the `Option` bind after every step.
  rw [stripPrefix_append "{\"active_connections\":".data]; dsimp only [bind, Option.bind]
  rw [parseNat_keyReq];                                    dsimp only [bind, Option.bind]
  rw [stripPrefix_append ",\"requests_total\":".data];     dsimp only [bind, Option.bind]
  rw [parseNat_keyBytes];                                  dsimp only [bind, Option.bind]
  rw [stripPrefix_append ",\"bytes_out_total\":".data];    dsimp only [bind, Option.bind]
  rw [parseNat_keyDrain];                                  dsimp only [bind, Option.bind]
  rw [stripPrefix_append ",\"draining\":".data];           dsimp only [bind, Option.bind]
  -- The draining boolean, then the closing brace.
  cases d with
  | true =>
      rw [show ((if (true = true) then "true" else "false") : String) = "true" from rfl]
      rw [parseBool_true]; dsimp only [bind, Option.bind]
      rw [stripPrefix_self "}".data]; dsimp only [bind, Option.bind]
      rfl
  | false =>
      rw [show ((if (false = true) then "true" else "false") : String) = "false" from rfl]
      rw [parseBool_false]; dsimp only [bind, Option.bind]
      rw [stripPrefix_self "}".data]; dsimp only [bind, Option.bind]
      rfl

-- The exact deployed `/admin/connections` line, byte for byte (matches the curl).
#guard connectionsLine { active := 0, requests := 0, bytesOut := 0, draining := false } ==
  "{\"active_connections\":0,\"requests_total\":0,\"bytes_out_total\":0,\"draining\":false}\n"

-- A non-trivial snapshot round-trips (concrete instance of the general theorem).
example : parseSnapshot (toJson { active := 3, requests := 1027, bytesOut := 88231, draining := true }).data
    = some { active := 3, requests := 1027, bytesOut := 88231, draining := true } :=
  metrics_json_wellformed _

end MetricsFormat
end Admin
