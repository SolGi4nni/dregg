import H2.Frame

/-!
# H2.Ext — the HTTP/2 extension surface (ORIGIN, ALT-SVC, Extensible Priority, trailers)

`H2/Conn.lean` proves the RFC 9113 core connection engine. This module adds the
**extension surface** a full-featured HTTP/2 server speaks, each with its own
byte-exact codec and a machine-checked correctness statement:

* **ORIGIN** (RFC 8336 §2) — a stream-0 frame carrying a list of authoritative
  origins, each a big-endian 16-bit length prefix followed by the ASCII origin.
  `decodeOrigins` / `encodeOrigins` round-trip (`decodeOrigins_encodeOrigins`).
* **ALT-SVC** (RFC 7838 §4) — an `Origin-Len ‖ Origin ‖ Alt-Svc-field-value`
  frame advertising alternative services. `decodeAltSvc` / `encodeAltSvc`
  round-trip (`decodeAltSvc_encodeAltSvc`).
* **Extensible Priority** (RFC 9218 §4) — the `priority` request-header field
  (`u=` urgency 0–7, `i` incremental), parsed into a `Priority`. Urgency is
  always clamped into range (`parsePriority_urgency_le`); encode/parse round-trip
  over the whole legal space (`parsePriority_encode`).
* **Trailers** (RFC 9113 §8.1) — the detection rule that a second HEADERS block
  carrying `END_STREAM`, arriving after the initial HEADERS and ≥ 1 DATA frame,
  is a *trailer* section, not a second header block
  (`detectTrailers` + `detectTrailers_true_iff`).

Every codec here operates on the frame **payload** (the octets after the 9-octet
frame header); `H2.Conn` strips the header and calls into these, then surfaces an
`Event`. All theorems are grounded on concrete wire octets (`#guard`), never
vacuous.
-/

namespace H2
namespace Ext

/-! ## Big-endian 16-bit length prefix (the shared field of ORIGIN + ALT-SVC) -/

/-- Encode `n` as a big-endian 16-bit field (`UInt8.ofNat` reduces mod 256). -/
def be16 (n : Nat) : Bytes := [UInt8.ofNat (n / 256), UInt8.ofNat n]

/-- Read a big-endian 16-bit field off the head of `bs`. `none` when fewer than
two octets remain. -/
def readBe16 : Bytes → Option (Nat × Bytes)
  | a :: b :: rest => some (a.toNat * 256 + b.toNat, rest)
  | _ => none

theorem be16_length (n : Nat) : (be16 n).length = 2 := rfl

/-- `readBe16` inverts `be16` for any 16-bit value, leaving the tail untouched. -/
theorem readBe16_be16 (n : Nat) (rest : Bytes) (h : n < 65536) :
    readBe16 (be16 n ++ rest) = some (n, rest) := by
  simp only [be16, List.cons_append, List.nil_append, readBe16, UInt8.toNat_ofNat',
    Option.some.injEq, Prod.mk.injEq, and_true]
  omega

/-! ## ORIGIN (RFC 8336 §2)

Payload = a sequence of `(Origin-Len : u16, Origin : ASCII)` entries on stream 0.
-/

/-- Encode one origin entry: its length prefix then its bytes. -/
def encodeOrigin (o : Bytes) : Bytes := be16 o.length ++ o

/-- Encode a list of origins into an ORIGIN frame payload (RFC 8336 §2). -/
def encodeOrigins : List Bytes → Bytes
  | [] => []
  | o :: rest => encodeOrigin o ++ encodeOrigins rest

/-- Decode an ORIGIN frame payload into its list of origins. Fueled by the entry
count (every entry consumes ≥ 2 octets). A trailing single octet, or an entry
whose declared length overruns the payload, is malformed (`none`). -/
def decodeOrigins : Nat → Bytes → Option (List Bytes)
  | 0, [] => some []
  | 0, _ :: _ => none
  | _ + 1, [] => some []
  | fuel + 1, (a :: b :: rest) =>
      if rest.length < a.toNat * 256 + b.toNat then none
      else (decodeOrigins fuel (rest.drop (a.toNat * 256 + b.toNat))).map
            (fun os => rest.take (a.toNat * 256 + b.toNat) :: os)
  | _ + 1, [_] => none

/-- **ORIGIN round-trip** (RFC 8336 §2): decoding the encoding of any origin list
(each origin under the 16-bit length bound) returns exactly the list. -/
theorem decodeOrigins_encodeOrigins (os : List Bytes)
    (hlen : ∀ o ∈ os, o.length < 65536) :
    decodeOrigins os.length (encodeOrigins os) = some os := by
  induction os with
  | nil => rfl
  | cons o rest ih =>
    have ho : o.length < 65536 := hlen o (List.mem_cons_self)
    have hrest : ∀ x ∈ rest, x.length < 65536 :=
      fun x hx => hlen x (List.mem_cons_of_mem _ hx)
    have hlenval :
        (UInt8.ofNat (o.length / 256)).toNat * 256 + (UInt8.ofNat o.length).toNat
          = o.length := by
      simp only [UInt8.toNat_ofNat']; omega
    have hnlt : ¬ (o ++ encodeOrigins rest).length < o.length := by
      rw [List.length_append]; omega
    have htake : (o ++ encodeOrigins rest).take o.length = o := List.take_left
    have hdrop : (o ++ encodeOrigins rest).drop o.length = encodeOrigins rest :=
      List.drop_left
    show decodeOrigins (rest.length + 1) (be16 o.length ++ o ++ encodeOrigins rest) = _
    rw [List.append_assoc]
    show decodeOrigins (rest.length + 1)
        (UInt8.ofNat (o.length / 256) :: UInt8.ofNat o.length :: (o ++ encodeOrigins rest)) = _
    rw [decodeOrigins]
    simp only [hlenval]
    rw [if_neg hnlt, hdrop, ih hrest]
    simp only [Option.map_some, htake]

/-! ## ALT-SVC (RFC 7838 §4)

Payload = `Origin-Len : u16 ‖ Origin ‖ Alt-Svc-field-value`. On stream 0 the
origin is non-empty and names the origin the value applies to; on a non-zero
stream the origin is empty and the value applies to that stream's origin.
-/

/-- Encode an ALT-SVC frame payload (RFC 7838 §4). -/
def encodeAltSvc (origin value : Bytes) : Bytes := be16 origin.length ++ origin ++ value

/-- Decode an ALT-SVC frame payload into `(origin, value)`. `none` when the
length prefix is missing or overruns the payload. -/
def decodeAltSvc (bs : Bytes) : Option (Bytes × Bytes) :=
  match readBe16 bs with
  | none => none
  | some (len, rest) =>
      if rest.length < len then none
      else some (rest.take len, rest.drop len)

/-- **ALT-SVC round-trip** (RFC 7838 §4): decoding the encoding of any
`(origin, value)` (origin under the 16-bit length bound) returns exactly it. -/
theorem decodeAltSvc_encodeAltSvc (origin value : Bytes) (h : origin.length < 65536) :
    decodeAltSvc (encodeAltSvc origin value) = some (origin, value) := by
  have hnlt : ¬ (origin ++ value).length < origin.length := by
    rw [List.length_append]; omega
  have htake : (origin ++ value).take origin.length = origin := List.take_left
  have hdrop : (origin ++ value).drop origin.length = value := List.drop_left
  unfold encodeAltSvc decodeAltSvc
  rw [List.append_assoc, readBe16_be16 origin.length _ h]
  show (if (origin ++ value).length < origin.length then none
        else some ((origin ++ value).take origin.length, (origin ++ value).drop origin.length))
      = some (origin, value)
  rw [if_neg hnlt, htake, hdrop]

/-! ## Extensible Priority (RFC 9218 §4)

The `priority` request-header field is a Structured-Fields dictionary with two
defined members: urgency `u` (an integer 0–7, default 3) and incremental `i`
(a boolean, default false). We parse the subset RFC 9218 §4 defines; unknown
members are ignored, and an out-of-range urgency is clamped into `[0,7]`.
-/

/-- A parsed HTTP priority signal (RFC 9218 §4). -/
structure Priority where
  urgency : Nat := 3
  incremental : Bool := false
deriving Repr, DecidableEq

def strBytes (s : String) : Bytes := (String.toUTF8 s).toList

/-! The ASCII byte literals the parser matches against, spelled as explicit
octets so the codec reduces in the kernel (`String.toUTF8` does not). -/
def bUrgency : Bytes := [0x75, 0x3d]              -- "u="
def bIncr : Bytes := [0x69]                       -- "i"
def bIncrSemi : Bytes := [0x69, 0x3b]             -- "i;"
def bIncrTrue : Bytes := [0x69, 0x3d, 0x3f, 0x31] -- "i=?1"
def bIncrFalse : Bytes := [0x69, 0x3d, 0x3f, 0x30]-- "i=?0"
def bCommaIncr : Bytes := [0x2c, 0x20, 0x69]      -- ", i"

/-- ASCII whitespace stripped when trimming a dictionary member. -/
def isWs (b : UInt8) : Bool := b == 0x20 || b == 0x09

/-- Trim leading and trailing ASCII whitespace. -/
def trimWs (bs : Bytes) : Bytes :=
  ((bs.dropWhile isWs).reverse.dropWhile isWs).reverse

/-- Parse a run of ASCII decimal digits into a `Nat`. `none` on empty or on any
non-digit octet. -/
def parseNat? (bs : Bytes) : Option Nat :=
  if bs.isEmpty then none
  else bs.foldl (init := some 0) fun acc b =>
    match acc with
    | none => none
    | some v =>
      if 0x30 ≤ b.toNat ∧ b.toNat ≤ 0x39 then some (v * 10 + (b.toNat - 0x30))
      else none

/-- Split a payload on the comma octet `0x2c` into its dictionary members. Always
returns at least one (possibly empty) segment. -/
def splitComma : Bytes → List Bytes
  | [] => [[]]
  | b :: rest =>
    let tail := splitComma rest
    if b == 0x2c then [] :: tail
    else match tail with
      | [] => [[b]]
      | cur :: more => (b :: cur) :: more

/-- Fold one trimmed dictionary member into the raw `(urgency, incremental)`
accumulator (RFC 9218 §4). `u=<int>` sets urgency, the bare `i` / `i=?1` set
incremental true, `i=?0` sets it false, everything else is ignored. -/
def applyMember (acc : Nat × Bool) (member : Bytes) : Nat × Bool :=
  let t := trimWs member
  if t.isEmpty then acc
  else if bUrgency.isPrefixOf t then
    match parseNat? (t.drop 2) with
    | some u => (u, acc.2)
    | none => acc
  else if t == bIncr || bIncrSemi.isPrefixOf t || t == bIncrTrue then
    (acc.1, true)
  else if t == bIncrFalse then
    (acc.1, false)
  else acc

/-- The raw parse, before urgency clamping: fold the members left-to-right over
the default `(3, false)` (last value wins). -/
def parsePriorityRaw (bs : Bytes) : Nat × Bool :=
  (splitComma bs).foldl applyMember (3, false)

/-- Parse a `priority` header-field value into a `Priority` (RFC 9218 §4), with
urgency clamped into the legal `[0,7]` range. -/
def parsePriority (bs : Bytes) : Priority :=
  let (u, i) := parsePriorityRaw bs
  { urgency := min u 7, incremental := i }

/-- The ASCII digit octet for `n` (single digit; urgency is always 0–9). -/
def digitByte (n : Nat) : UInt8 := UInt8.ofNat (0x30 + n % 10)

/-- Encode a `Priority` back to a `priority` field value, omitting members left
at their defaults (RFC 9218 §4). Urgency is a single digit (always 0–7 after a
parse), matching the legal range. -/
def encodePriority (p : Priority) : Bytes :=
  if p.urgency == 3 then
    (if p.incremental then bIncr else [])
  else
    bUrgency ++ [digitByte p.urgency] ++ (if p.incremental then bCommaIncr else [])

/-- **Priority urgency in range** (RFC 9218 §4): every parsed urgency is a valid
urgency level, `0 ≤ u ≤ 7` — the clamp is total. -/
theorem parsePriority_urgency_le (bs : Bytes) : (parsePriority bs).urgency ≤ 7 := by
  simp only [parsePriority]
  exact Nat.min_le_right _ _

/-- **Priority round-trip** (RFC 9218 §4): every in-range priority survives
encode-then-parse — the codec is faithful across the whole legal space
(urgency 0–7 × incremental). -/
theorem parsePriority_encode (u : Nat) (i : Bool) (h : u ≤ 7) :
    parsePriority (encodePriority { urgency := u, incremental := i }) = { urgency := u, incremental := i } := by
  have hu : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 ∨ u = 5 ∨ u = 6 ∨ u = 7 := by omega
  rcases hu with h|h|h|h|h|h|h|h <;> subst h <;> cases i <;> rfl

/-! ## Trailers (RFC 9113 §8.1)

A HEADERS block carrying `END_STREAM` that arrives on a stream on which the
initial HEADERS have already been received *and* at least one DATA frame has
been seen is a **trailer** section, not a second header block. gRPC uses this to
carry `grpc-status` / `grpc-message` after the response body.
-/

/-- The trailer-detection rule (RFC 9113 §8.1): a subsequent HEADERS block is a
trailer section exactly when the stream has both received its initial headers and
seen data. -/
def detectTrailers (initialHeaders dataSeen : Bool) : Bool := initialHeaders && dataSeen

/-- **Trailer detection is exactly `initialHeaders ∧ dataSeen`** — the full truth
table, both directions. -/
theorem detectTrailers_true_iff (initialHeaders dataSeen : Bool) :
    detectTrailers initialHeaders dataSeen = true ↔ initialHeaders = true ∧ dataSeen = true := by
  cases initialHeaders <;> cases dataSeen <;> simp [detectTrailers]

/-- The trailer rule fires only after BOTH the initial headers and data — never
on the initial HEADERS (no data yet), never before any headers. -/
theorem detectTrailers_truth_table :
    detectTrailers true true = true ∧
    detectTrailers true false = false ∧
    detectTrailers false true = false ∧
    detectTrailers false false = false := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ## The extension event vocabulary

`H2.Conn.feed` accumulates these on the connection state as it recognizes each
extension frame, so a host can observe them without changing the engine's
`ConnState × Bytes × Bool` transition shape. -/

/-- An extension-surface event surfaced by the connection engine. -/
inductive Event where
  /-- An ORIGIN frame (RFC 8336) declared these authoritative origins (stream 0). -/
  | origin (origins : List Bytes)
  /-- An ALT-SVC frame (RFC 7838) advertised an alternative service. -/
  | altSvc (streamId : Nat) (origin value : Bytes)
  /-- A trailer section (RFC 9113 §8.1) was detected on this stream. -/
  | trailers (streamId : Nat)
deriving Repr, DecidableEq

/-! ## Grounding on concrete wire octets

Each decode is exercised on real bytes so the theorems above are not vacuous.
-/

/- ORIGIN payload with two origins "a.io" (4) and "ex.test" (7):
   00 04 'a' '.' 'i' 'o'  00 07 'e' 'x' '.' 't' 'e' 's' 't'. -/
#guard decodeOrigins 4
    [0x00, 0x04, 0x61, 0x2e, 0x69, 0x6f,
     0x00, 0x07, 0x65, 0x78, 0x2e, 0x74, 0x65, 0x73, 0x74]
  = some [strBytes "a.io", strBytes "ex.test"]

/- Encoding those two origins yields exactly those payload octets. -/
#guard encodeOrigins [strBytes "a.io", strBytes "ex.test"]
  = [0x00, 0x04, 0x61, 0x2e, 0x69, 0x6f,
     0x00, 0x07, 0x65, 0x78, 0x2e, 0x74, 0x65, 0x73, 0x74]

/- An ORIGIN payload with a length that overruns the buffer is rejected. -/
#guard decodeOrigins 4 [0x00, 0x09, 0x61, 0x62] = none

/- ALT-SVC payload on stream 0: origin "https://x.io" (12), value h3=":443"; ma=3600. -/
#guard decodeAltSvc (encodeAltSvc (strBytes "https://x.io") (strBytes "h3=\":443\"; ma=3600"))
  = some (strBytes "https://x.io", strBytes "h3=\":443\"; ma=3600")

/- ALT-SVC on a non-zero stream: empty origin, value applies to that stream. -/
#guard decodeAltSvc [0x00, 0x00, 0x68, 0x33] = some ([], strBytes "h3")

/- priority: u=1, i  → urgency 1, incremental. -/
#guard parsePriority (strBytes "u=1, i") = { urgency := 1, incremental := true }
/- priority: i  → default urgency 3, incremental. -/
#guard parsePriority (strBytes "i") = { urgency := 3, incremental := true }
/- priority: u=5  → urgency 5, non-incremental. -/
#guard parsePriority (strBytes "u=5") = { urgency := 5, incremental := false }
/- priority: u=9  → clamped to urgency 7. -/
#guard parsePriority (strBytes "u=9") = { urgency := 7, incremental := false }
/- Empty value → the RFC 9218 §4 default. -/
#guard parsePriority (strBytes "") = { urgency := 3, incremental := false }
/- priority: i=?0  → incremental explicitly false. -/
#guard parsePriority (strBytes "i=?0") = { urgency := 3, incremental := false }
/- Reversed order + unknown members ignored: i, u=2, x=9. -/
#guard parsePriority (strBytes "i, u=2, x=9") = { urgency := 2, incremental := true }

/- Trailer rule: initial headers + data ⇒ trailers; anything less ⇒ not. -/
#guard detectTrailers true true = true
#guard detectTrailers true false = false
#guard detectTrailers false false = false

end Ext
end H2
