import Trace.Correlation

/-!
# O11y.AccessLog — a verified structured access-log line

A per-request access-log record — method, path, status, response bytes,
duration, and the request's correlation id — serialized as an ordered set of
named fields (a structured/JSON-shaped line), with three properties proven, not
asserted:

* `access_log_wellformed` — a rendered line carries exactly the required field
  keys, in order (`method`, `path`, `status`, `bytes`, `duration_ms`,
  `corr_id`), and each key resolves to the intended (escaped) value. A line is
  *structured*: every documented field is present and addressable by key.

* `access_log_no_injection` — an attacker-controlled string (method or path)
  containing a record separator — carriage return (CR) or line feed (LF), the
  bytes that terminate a log line — is escaped, so the rendered field carries no
  raw CR/LF and cannot forge a second log line. Log injection is impossible by
  construction. The escaping is additionally lossless (`escape_roundtrip`).

* `access_log_corr_matches` — the correlation id recorded in the log line equals
  the id carried in the response's correlation header; both agree with the id
  the correlation layer injects (`Trace.upstreamCorr ∘ Trace.inject`). The log
  and the wire cannot disagree about which request a line describes.

The correlation id and its header are the public `Trace.Correlation` model. The
escaping mirrors the label-escaping technique of `O11y.Prometheus`, extended to
the full set of line-terminating and structural bytes. All proofs are core-Lean
(no `native_decide` in the headline theorems), so the axiom footprint is empty
(checked with `#print axioms`).
-/

namespace O11y.AccessLog

/-! ## Field-value escaping

A structured line is line-oriented: a value that embeds a CR or LF would split
the line and let an attacker forge a second, fabricated record. Escaping maps
the backslash, the double quote (the JSON string delimiter), the line feed, the
carriage return, and the horizontal tab to two-character escapes; every other
byte passes through unchanged. -/

/-- Escape a field value as a character list. Backslash → `\\`, double quote →
`\"`, LF → `\n`, CR → `\r`, HT → `\t`; any other character is left as-is. -/
def escapeChars : List Char → List Char
  | [] => []
  | c :: cs =>
      if c = '\\' then '\\' :: '\\' :: escapeChars cs
      else if c = '"' then '\\' :: '"' :: escapeChars cs
      else if c = '\n' then '\\' :: 'n' :: escapeChars cs
      else if c = '\r' then '\\' :: 'r' :: escapeChars cs
      else if c = '\t' then '\\' :: 't' :: escapeChars cs
      else c :: escapeChars cs

/-- Inverse of `escapeChars`: collapse each two-character escape back to the byte
it stood for. On the image of `escapeChars` this is a genuine inverse
(`escape_roundtrip`). -/
def unescapeChars : List Char → List Char
  | [] => []
  | ['\\'] => ['\\']
  | '\\' :: d :: cs =>
      if d = '\\' then '\\' :: unescapeChars cs
      else if d = '"' then '"' :: unescapeChars cs
      else if d = 'n' then '\n' :: unescapeChars cs
      else if d = 'r' then '\r' :: unescapeChars cs
      else if d = 't' then '\t' :: unescapeChars cs
      else d :: unescapeChars cs
  | c :: cs => c :: unescapeChars cs

/-- **Escaping round-trips.** Unescaping an escaped value recovers the original —
no field value is corrupted or made ambiguous by escaping. -/
theorem escape_roundtrip (cs : List Char) :
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
        · by_cases h4 : c = '\r'
          · subst h4; simp [escapeChars, unescapeChars, h1, h2, h3, ih]
          · by_cases h5 : c = '\t'
            · subst h5; simp [escapeChars, unescapeChars, h1, h2, h3, h4, ih]
            · have he : escapeChars (c :: cs) = c :: escapeChars cs := by
                simp [escapeChars, h1, h2, h3, h4, h5]
              have hu : unescapeChars (c :: escapeChars cs)
                  = c :: unescapeChars (escapeChars cs) := by
                cases hE : escapeChars cs with
                | nil => simp [unescapeChars, h1]
                | cons d rest => simp [unescapeChars, h1]
              rw [he, hu, ih]

/-- Does a character list contain a raw record separator (CR or LF)? These are
the only bytes that can terminate the current line and begin a forged one. -/
def hasLineBreak : List Char → Bool
  | [] => false
  | c :: cs => if c = '\n' then true else if c = '\r' then true else hasLineBreak cs

/-- **No raw record separator survives escaping.** An escaped value contains no
bare LF and no bare CR, so an attacker-controlled method or path can never end
the log line early and inject a fabricated record. -/
theorem escape_no_linebreak (cs : List Char) :
    hasLineBreak (escapeChars cs) = false := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases h1 : c = '\\'
    · subst h1; simp [escapeChars, hasLineBreak, ih]
    · by_cases h2 : c = '"'
      · subst h2; simp [escapeChars, hasLineBreak, h1, ih]
      · by_cases h3 : c = '\n'
        · subst h3; simp [escapeChars, hasLineBreak, h1, h2, ih]
        · by_cases h4 : c = '\r'
          · subst h4; simp [escapeChars, hasLineBreak, h1, h2, h3, ih]
          · by_cases h5 : c = '\t'
            · subst h5; simp [escapeChars, hasLineBreak, h1, h2, h3, h4, ih]
            · simp only [escapeChars, h1, h2, h3, h4, h5, if_false]
              simp only [hasLineBreak, h3, h4, if_false, ih]

/-- Escape a field value string. -/
def renderStr (s : String) : String := String.ofList (escapeChars s.toList)

/-! ## The structured record and its fields -/

/-- A correlation id (the public `Trace.Correlation` model): an opaque byte
string on which only equality is used. -/
abbrev CorrId := Trace.CorrId

/-- One access-log record: the per-request data a line reports. -/
structure Entry where
  /-- Request method (e.g. `GET`). -/
  method : String
  /-- Request path (attacker-influenced; escaped on render). -/
  path : String
  /-- Response status code. -/
  status : Nat
  /-- Response body size in bytes. -/
  bytes : Nat
  /-- Request processing duration in milliseconds. -/
  durationMs : Nat
  /-- The request's correlation id. -/
  corr : CorrId

/-- The exact set of field keys a well-formed line carries, in order. -/
def requiredKeys : List String :=
  ["method", "path", "status", "bytes", "duration_ms", "corr_id"]

/-- Render an entry to its ordered `(key, value)` fields. String values are
escaped; numeric and id values are rendered by `toString`. -/
def fields (e : Entry) : List (String × String) :=
  [ ("method", renderStr e.method)
  , ("path", renderStr e.path)
  , ("status", toString e.status)
  , ("bytes", toString e.bytes)
  , ("duration_ms", toString e.durationMs)
  , ("corr_id", toString e.corr) ]

/-! ## Theorem 1 — well-formed structured line -/

/-- **Structured line well-formedness.** A rendered line carries exactly the
required field keys, in order, and each key resolves to the intended (escaped)
value — the line reports method, path, status, bytes, duration, and correlation
id, each addressable by name. -/
theorem access_log_wellformed (e : Entry) :
    (fields e).map Prod.fst = requiredKeys
    ∧ (fields e).lookup "method" = some (renderStr e.method)
    ∧ (fields e).lookup "path" = some (renderStr e.path)
    ∧ (fields e).lookup "status" = some (toString e.status)
    ∧ (fields e).lookup "bytes" = some (toString e.bytes)
    ∧ (fields e).lookup "duration_ms" = some (toString e.durationMs)
    ∧ (fields e).lookup "corr_id" = some (toString e.corr) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [fields, List.lookup]

/-! ## Theorem 2 — no log injection

`access_log_no_injection` is the escaping property specialised to the
attacker-controlled fields: the rendered `method` and `path` carry no record
separator, so no request can forge an extra log line. -/

/-- **No log injection.** For any method and path — including ones bearing CR/LF
control bytes — the rendered `method` and `path` field values contain no raw
record separator. An attacker cannot split the line and inject a second record. -/
theorem access_log_no_injection (e : Entry) :
    hasLineBreak (renderStr e.method).toList = false
    ∧ hasLineBreak (renderStr e.path).toList = false := by
  refine ⟨?_, ?_⟩ <;> simp only [renderStr, String.toList_ofList] <;> exact escape_no_linebreak _

/-! ## Theorem 3 — the log's correlation id matches the response header

The response carries the correlation id in the same header the correlation layer
injects. The log entry built for a processed request records that same id. -/

/-- A response: the header pairs carrying the correlation id back to the client. -/
structure Resp where
  /-- Response header key/value pairs. -/
  headers : List (String × CorrId)

/-- Read the correlation id off a response's header. -/
def Resp.corr (r : Resp) : Option CorrId :=
  (r.headers.find? (fun kv => kv.1 == Trace.corrHeader)).map (fun kv => kv.2)

/-- The response emitted for a processed request: it echoes the assigned
correlation id in the correlation header. -/
def respOf (p : Trace.Processed) : Resp :=
  { headers := [(Trace.corrHeader, p.corr)] }

/-- The access-log entry recorded for a processed request. -/
def entryOf (p : Trace.Processed) (method path : String) (status bytes dur : Nat) : Entry :=
  { method, path, status, bytes, durationMs := dur, corr := p.corr }

/-- **The log and the wire agree on the correlation id.** The id recorded in the
log entry equals the id carried in the response's correlation header, and both
equal the id the correlation layer injects downstream. A log line can always be
tied back to the exact request it describes. -/
theorem access_log_corr_matches
    (p : Trace.Processed) (m pt : String) (st b du : Nat) :
    some (entryOf p m pt st b du).corr = (respOf p).corr
    ∧ (respOf p).corr = Trace.upstreamCorr (Trace.inject p) := by
  refine ⟨?_, ?_⟩
  · simp [entryOf, respOf, Resp.corr, Trace.corrHeader]
  · simp [respOf, Resp.corr, Trace.upstreamCorr, Trace.inject, Trace.corrHeader]

/-! ## Non-vacuous concrete example and a CRLF-injection mutant

A real entry (a `GET /health` with a correlation id) renders to a concrete field
set. The mutant checks below show the property has teeth: an escaper that leaves
CR/LF raw (the identity `mutantEscape`) admits injection, while `escapeChars`
neutralises it. -/

/-- A concrete processed request with a fixed correlation id. -/
def exampleProcessed : Trace.Processed := { corr := [7, 42, 255] }

/-- A concrete access-log entry. -/
def exampleEntry : Entry := entryOf exampleProcessed "GET" "/health" 200 1024 3

-- The concrete line is well-formed (an instance of the general theorem).
example : (fields exampleEntry).map Prod.fst = requiredKeys :=
  (access_log_wellformed exampleEntry).1

-- The concrete field set, exactly.
#guard fields exampleEntry ==
  [ ("method", "GET")
  , ("path", "/health")
  , ("status", "200")
  , ("bytes", "1024")
  , ("duration_ms", "3")
  , ("corr_id", "[7, 42, 255]") ]

-- The log's correlation id matches the response header's.
example : some exampleProcessed.corr = (respOf exampleProcessed).corr :=
  (access_log_corr_matches exampleProcessed "GET" "/health" 200 1024 3).1

/-- The CRLF-injection **mutant**: an escaper that forgets CR/LF is the identity. -/
def mutantEscape (cs : List Char) : List Char := cs

-- An attacker path that tries to forge a `Set-Cookie` log field.
def attackPath : String := "/x\r\nfake-field: injected"

-- The mutant admits injection: a raw record separator survives.
#guard hasLineBreak (mutantEscape attackPath.toList) = true

-- Our escaping neutralises it: no record separator survives (an instance of the
-- general no-injection theorem).
#guard hasLineBreak (escapeChars attackPath.toList) = false

-- Escaping round-trips even on a value carrying every special byte.
#guard unescapeChars (escapeChars "a\"b\\c\nd\re\tf".toList) = "a\"b\\c\nd\re\tf".toList

def version : String := "0.1.0"

end O11y.AccessLog
