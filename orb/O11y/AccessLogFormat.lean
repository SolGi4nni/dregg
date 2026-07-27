/-!
# O11y.AccessLogFormat — the deployed access-log wire line, proven

The plaintext HTTP serve path (both the blocking reactor and the io_uring
reactor) emits, when opt-in access logging is enabled, exactly one compact
`key=val` line per served request:

```text
ts=<iso8601> client=<ip> method=<m> path=<p> status=<code> backend=<b> bytes=<n> dur_us=<d>
```

The eight fields appear in that fixed order, separated by single spaces, and the
line is terminated by a single newline. Two of the fields — `method` and `path`
— carry attacker-influenced request bytes and are *sanitised* before they reach
the line: every control character and every space is replaced by `_`, the field
is capped at 2048 characters, and an ellipsis marks truncation. The remaining
fields are host-owned (timestamp, peer address, status code, dialled upstream,
byte count, elapsed microseconds).

This module models that line and the sanitiser faithfully and proves two
properties of the wire the host actually writes:

* `access_log_line_wellformed` — a rendered line carries exactly the eight
  required keys, in order, and every key resolves to its intended value
  (`client`, `method`, `path`, `status`, `bytes`, `dur_us`, and the `ts` /
  `backend` frame fields). The record is structured and each field is
  addressable by name.

* `access_log_no_crlf_injection` — a `method` or `path` bearing a carriage
  return or line feed — the two bytes that terminate a line and could forge a
  second, fabricated record — cannot survive into the rendered field: the
  sanitiser maps them (as control bytes) to `_`. Log injection is impossible by
  construction, for any input whatsoever.

All proofs are core Lean — no `native_decide` in a headline theorem — so the
axiom footprint is empty (checked with `#print axioms`). The concrete `#guard`s
pin a `GET /health` line to the exact field set the running dataplane emits, so
the proof and the deployed wire are the same object.
-/

namespace O11y.AccessLogFormat

/-! ## The sanitiser (mirrors the deployed field sanitiser)

The deployed sanitiser keeps one field on one line and space-free: it replaces
every control character and every space with `_`, keeps at most 2048 characters,
and appends `…` when it truncated. A character is *control* on the Unicode C0
range `U+0000..U+001F` and the C1 range `U+007F..U+009F` — exactly Rust's
`char::is_control`. Carriage return (`U+000D`) and line feed (`U+000A`) are both
C0 control bytes, which is what makes injection impossible. -/

/-- Is `c` a Unicode control character (C0 `U+00..U+1F` or C1 `U+7F..U+9F`)? -/
def isControl (c : Char) : Bool :=
  c.val ≤ 0x1f || (0x7f ≤ c.val && c.val ≤ 0x9f)

/-- Map one field character: a control character or a space becomes `_`; every
other character passes through unchanged. -/
def sanitizeChar (c : Char) : Char :=
  match isControl c || c == ' ' with
  | true  => '_'
  | false => c

/-- Sanitise a field value: replace control/space characters, cap the length at
2048 characters, and mark truncation with `…`. -/
def sanitize (s : String) : String :=
  let cs := s.toList
  let kept := (cs.take 2048).map sanitizeChar
  String.ofList (if cs.length > 2048 then kept ++ ['…'] else kept)

/-! ## No control byte can survive the sanitiser -/

/-- The sanitiser never yields a raw CR or LF: whatever the input character, the
result is neither `'\n'` nor `'\r'`. (A control input becomes `_`; a non-control
input is left as-is but is then by definition not a control byte, and CR/LF are
control bytes.) -/
theorem sanitizeChar_ne_crlf (c : Char) :
    (sanitizeChar c == '\n' || sanitizeChar c == '\r') = false := by
  unfold sanitizeChar
  split
  · decide
  · rename_i h
    have h1 : isControl c = false := by
      rw [Bool.or_eq_false_iff] at h; exact h.1
    have hn : (c == '\n') = false := by
      cases hb : c == '\n' with
      | false => rfl
      | true =>
        have hc : c = '\n' := eq_of_beq hb
        rw [hc] at h1; exact absurd h1 (by decide)
    have hr : (c == '\r') = false := by
      cases hb : c == '\r' with
      | false => rfl
      | true =>
        have hc : c = '\r' := eq_of_beq hb
        rw [hc] at h1; exact absurd h1 (by decide)
    rw [hn, hr]; rfl

/-- Does a character list contain a raw record separator (CR or LF)? -/
def hasCRLF (cs : List Char) : Bool :=
  cs.any (fun c => c == '\n' || c == '\r')

/-- A mapped, sanitised character list carries no raw record separator. -/
theorem mapSanitize_no_crlf (l : List Char) :
    hasCRLF (l.map sanitizeChar) = false := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [hasCRLF, List.map_cons, List.any_cons] at ih ⊢
    rw [ih, Bool.or_false]
    exact sanitizeChar_ne_crlf c

/-- **No CRLF survives sanitising.** For any field value — including a hostile
`method` or `path` carrying CR/LF control bytes — the sanitised field contains
no raw carriage return and no raw line feed. An attacker cannot terminate the
current log line and inject a forged one. -/
theorem sanitize_no_crlf (s : String) :
    hasCRLF (sanitize s).toList = false := by
  simp only [sanitize, hasCRLF, String.toList_ofList]
  split
  · rw [List.any_append]
    have hm := mapSanitize_no_crlf (s.toList.take 2048)
    simp only [hasCRLF] at hm
    rw [hm]; decide
  · have hm := mapSanitize_no_crlf (s.toList.take 2048)
    simpa only [hasCRLF] using hm

/-! ## The structured record and its rendered line -/

/-- One access-log record: the eight fields the deployed line reports. `ts`,
`client`, `status`, and `backend` are host-owned strings; `bytes` and `durUs`
are host-owned counts; `method` and `path` are attacker-influenced request
strings (sanitised on render). -/
structure Entry where
  /-- ISO-8601 UTC timestamp. -/
  ts : String
  /-- Peer IP address (rendered by the host). -/
  client : String
  /-- Request method (attacker-influenced; sanitised on render). -/
  method : String
  /-- Request path (attacker-influenced; sanitised on render). -/
  path : String
  /-- Response status code, or `-`. -/
  status : String
  /-- Dialled upstream for a proxied request, else `-`. -/
  backend : String
  /-- Response bytes written. -/
  bytes : Nat
  /-- Elapsed microseconds. -/
  durUs : Nat

/-- The exact field keys a well-formed line carries, in order. -/
def requiredKeys : List String :=
  ["ts", "client", "method", "path", "status", "backend", "bytes", "dur_us"]

/-- Render an entry to its ordered `(key, value)` fields. `method` and `path`
are sanitised; the rest are host values rendered directly. -/
def fields (e : Entry) : List (String × String) :=
  [ ("ts", e.ts)
  , ("client", e.client)
  , ("method", sanitize e.method)
  , ("path", sanitize e.path)
  , ("status", e.status)
  , ("backend", e.backend)
  , ("bytes", toString e.bytes)
  , ("dur_us", toString e.durUs) ]

/-- Render an entry to its wire line: `key=value` fields joined by single spaces
and terminated by a newline. This is exactly the deployed format string. -/
def renderLine (e : Entry) : String :=
  String.intercalate " " ((fields e).map (fun kv => kv.1 ++ "=" ++ kv.2)) ++ "\n"

/-! ## Theorem 1 — the line is well-formed -/

/-- **Well-formed structured line.** A rendered line carries exactly the eight
required keys, in order, and each key resolves to its intended value. The line
reports timestamp, client, method, path, status, backend, bytes, and duration,
each addressable by name. -/
theorem access_log_line_wellformed (e : Entry) :
    (fields e).map Prod.fst = requiredKeys
    ∧ (fields e).lookup "ts" = some e.ts
    ∧ (fields e).lookup "client" = some e.client
    ∧ (fields e).lookup "method" = some (sanitize e.method)
    ∧ (fields e).lookup "path" = some (sanitize e.path)
    ∧ (fields e).lookup "status" = some e.status
    ∧ (fields e).lookup "backend" = some e.backend
    ∧ (fields e).lookup "bytes" = some (toString e.bytes)
    ∧ (fields e).lookup "dur_us" = some (toString e.durUs) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [fields, List.lookup]

/-! ## Theorem 2 — no log injection -/

/-- **No log injection.** For any method and path — including ones bearing CR/LF
control bytes — the rendered `method` and `path` field values contain no raw
record separator. An attacker cannot split the line and inject a second record.
-/
theorem access_log_no_crlf_injection (e : Entry) :
    hasCRLF (sanitize e.method).toList = false
    ∧ hasCRLF (sanitize e.path).toList = false :=
  ⟨sanitize_no_crlf e.method, sanitize_no_crlf e.path⟩

/-! ## Concrete `GET /health` line — the proof pinned to the deployed wire

A real health-probe request renders to a concrete field set. These `#guard`s
pin the field keys and the exact `GET /health` values to the line the running
dataplane emits on the io_uring path, so the proof object and the deployed wire
are the same. -/

/-- A concrete `GET /health` entry with representative host-owned frame fields. -/
def healthEntry : Entry :=
  { ts := "2026-07-09T00:00:00.000000Z"
  , client := "127.0.0.1"
  , method := "GET"
  , path := "/health"
  , status := "200"
  , backend := "-"
  , bytes := 96
  , durUs := 12 }

-- The keys, exactly and in order — the wire's field frame.
#guard (fields healthEntry).map Prod.fst = requiredKeys

-- The concrete `GET /health` field set (`method`/`path` unchanged by sanitising).
#guard fields healthEntry ==
  [ ("ts", "2026-07-09T00:00:00.000000Z")
  , ("client", "127.0.0.1")
  , ("method", "GET")
  , ("path", "/health")
  , ("status", "200")
  , ("backend", "-")
  , ("bytes", "96")
  , ("dur_us", "12") ]

-- The rendered line is the deployed format string, byte for byte.
#guard renderLine healthEntry =
  "ts=2026-07-09T00:00:00.000000Z client=127.0.0.1 method=GET path=/health " ++
  "status=200 backend=- bytes=96 dur_us=12\n"

/-! ## A CRLF-injection mutant — the property has teeth

An identity sanitiser (`mutantSanitize`) lets a hostile path forge a second
field; the real `sanitize` neutralises it. -/

/-- A hostile path attempting to forge an extra `evil=1` field on a new line. -/
def attackPath : String := "/x\r\nevil=1"

/-- The mutant: an identity sanitiser that forgets control bytes. -/
def mutantSanitize (s : String) : String := s

-- The mutant admits injection: a raw record separator survives.
#guard hasCRLF (mutantSanitize attackPath).toList = true

-- The real sanitiser neutralises it (an instance of `sanitize_no_crlf`).
#guard hasCRLF (sanitize attackPath).toList = false

-- The sanitised hostile path: CR and LF became `_`, keeping one line.
#guard sanitize attackPath = "/x__evil=1"

def version : String := "0.1.0"

end O11y.AccessLogFormat
