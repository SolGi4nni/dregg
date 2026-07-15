/-
Arena — an executable HTTP/1.1 request-head parser written AS the model.

This is the runnable face of the arena theory: it parses a request line +
header fields into the two-arena `Store` representation (main arena = the wire
bytes; sidecar arena = synthesized canonical header names) and registers every
view range as an `Entry`. Of the two hypotheses the theory carries:

* `Store.Wf` holds *statically*: `parse_wf` (Arena/ParseTheorems.lean) proves
  every store a `complete` outcome carries is well-formed — including the
  sidecar entries the canonicalization path synthesizes — so the parser runs
  no well-formedness check (the old runtime `wfCheck` gate and its
  `internal-wf-violation` error class were provably dead and are gone);
* `Store.WfUtf8` is *dynamically discharged* via `String.validateUTF8` per
  resolved range — content validity is the one hypothesis that genuinely
  enters at runtime.

Total by construction (structural recursion only), written for clarity over
speed. Canonicalization: header names are lowercased; a name that is already
lowercase points into the main arena, otherwise the lowered bytes are appended
to the sidecar and the entry's offset carries the sidecar discriminant
(`sidecarBase + sidecarOffset`).
-/
import Arena.Basic
import Arena.Theorems

namespace Arena
namespace Parse

/-- Wire bytes as a list (clarity over speed). -/
abbrev Bytes := List UInt8

def CR : UInt8 := 13
def LF : UInt8 := 10
def SP : UInt8 := 32
def HTAB : UInt8 := 9
def COLON : UInt8 := 58

/-- A `(offset, length)` span, in `Nat`, relative to the start of the input. -/
structure Span where
  off : Nat
  len : Nat
  deriving Repr, DecidableEq

/-- The bytes a span denotes. -/
def sliceSpan (bs : Bytes) (s : Span) : Bytes :=
  (bs.drop s.off).take s.len

/-- Index-native span slice over a flat buffer: `Array.extract` is `O(len)` (it
copies only the window), whereas `sliceSpan`'s `bs.drop s.off` walks `O(off)`
cons cells from the head — so slicing header `k` (offset ≈ head length) is
`O(head)`, and the per-header sweep is `O(head²)`. `sliceArr` reads the same
bytes in `O(len)` from the buffer the head is converted to *once*. -/
def sliceArr (arr : Array UInt8) (s : Span) : Bytes :=
  (arr.extract s.off (s.off + s.len)).toList

/-- `sliceArr` on the buffer view of `bs` reads exactly `sliceSpan bs`. -/
theorem sliceArr_toArray (bs : Bytes) (s : Span) :
    sliceArr bs.toArray s = sliceSpan bs s := by
  unfold sliceArr sliceSpan
  rw [Array.toList_extract, Array.toList_toArray, List.extract_eq_drop_take]
  congr 1
  omega

/-- Offset of the first `CRLFCRLF`, if any. -/
def findDoubleCrlf : Bytes → Option Nat
  | a :: rest@(b :: c :: d :: _) =>
    if a == CR && b == LF && c == CR && d == LF then some 0
    else (findDoubleCrlf rest).map (· + 1)
  | _ => none

/-! ### Bounded-stack `findDoubleCrlf`

`findDoubleCrlf` recurses *inside* `Option.map`, so the compiled code pushes one
stack frame per input byte until the `CRLFCRLF` — recursion depth = input
length, and a large request head exhausts the thread stack before any byte
gate can refuse it. `findDoubleCrlfGo` is the same single pass in
accumulator-passing (tail-recursive) form: the compiler emits a loop, so the
stack cost is `O(1)` **regardless of input length**. `findDoubleCrlf_eq_tail`
proves the two agree and installs the loop as the compiled implementation
(`@[csimp]`); every theorem about `findDoubleCrlf` (the framing lemmas, the
span-scan refinements) keeps referring to the unchanged spec. -/

/-- Tail-recursive `findDoubleCrlf` carrying the running offset: the recursive
call is the whole `else` branch, so the compiler emits a loop (constant
stack). -/
def findDoubleCrlfGo : Nat → Bytes → Option Nat
  | _, [] => none
  | _, [_] => none
  | _, [_, _] => none
  | _, [_, _, _] => none
  | i, a :: b :: c :: d :: t =>
    if a == CR && b == LF && c == CR && d == LF then some i
    else findDoubleCrlfGo (i + 1) (b :: c :: d :: t)

/-- The loop equals the spec up to the running-offset shift. -/
theorem findDoubleCrlfGo_eq (bs : Bytes) :
    ∀ i, findDoubleCrlfGo i bs = (findDoubleCrlf bs).map (· + i) := by
  induction bs with
  | nil => intro i; simp [findDoubleCrlfGo, findDoubleCrlf]
  | cons a xs ih =>
    intro i
    match xs, ih with
    | [], _ => simp [findDoubleCrlfGo, findDoubleCrlf]
    | [_], _ => simp [findDoubleCrlfGo, findDoubleCrlf]
    | [_, _], _ => simp [findDoubleCrlfGo, findDoubleCrlf]
    | b :: c :: d :: t, ih =>
      rw [findDoubleCrlfGo, findDoubleCrlf]
      by_cases h : a == CR && b == LF && c == CR && d == LF
      · simp [h]
      · rw [if_neg h, if_neg h, ih (i + 1), Option.map_map]
        congr 1
        funext x
        simp only [Function.comp_apply]
        omega

/-- The bounded-stack `findDoubleCrlf`: the loop from offset `0`. -/
def findDoubleCrlfTail (bs : Bytes) : Option Nat := findDoubleCrlfGo 0 bs

/-- **The loop/spec agreement.** `findDoubleCrlfTail` computes the same offset
as `findDoubleCrlf`, in constant stack. -/
@[csimp] theorem findDoubleCrlf_eq_tail : @findDoubleCrlf = @findDoubleCrlfTail := by
  funext bs
  rw [findDoubleCrlfTail, findDoubleCrlfGo_eq bs 0]
  simp

/-- Offsets of every `CRLF` within `bs`. -/
def crlfPositions (bs : Bytes) : List Nat :=
  (List.range bs.length).filter fun i =>
    bs.getD i 0 == CR && bs.getD (i + 1) 0 == LF

/-! ### Linear-time `crlfPositions`

The `List.range … |>.filter` reading of `crlfPositions` indexes the cons-list
with `getD i` at every position, and `getD i` on a list is `O(i)`, so the sweep
is `O(n²)` in the head length — the dominant super-linear cost on the request
parse. `crlfPositionsFast` computes the identical list of positions in a single
left-to-right pass (each step peels one cons and does `O(1)` work), so the sweep
is `O(n)`. `crlfPositions_eq_fast` proves the two agree and installs the linear
pass as the compiled implementation (`@[csimp]`); every theorem about
`crlfPositions` (`crlfPositions_lt`, `crlfPositions_pairwise`, the span-scan
refinements) keeps referring to the unchanged spec. -/

/-- Single left-to-right pass recording each `CR,LF` adjacency at its running
index. Peels one cons per step (`O(1)` work) ⇒ the whole sweep is `O(n)`. -/
def crlfPositionsGo : Nat → Bytes → List Nat
  | _, [] => []
  | _, [_] => []
  | i, a :: b :: rest =>
    if a == CR && b == LF then i :: crlfPositionsGo (i + 1) (b :: rest)
    else crlfPositionsGo (i + 1) (b :: rest)

/-! `crlfPositionsGo` made the sweep linear-*time* but left it linear-*stack*:
it conses the hit *before* recursing, so the compiled code pushes one frame per
byte — depth = head length. `crlfPositionsRevGo` is the same pass with the hits
accumulated in reverse (tail-recursive ⇒ compiled to a loop, constant stack);
`crlfPositionsGo_eq_tail` installs it as the compiled implementation
(`@[csimp]`), so `crlfPositionsFast` — and through `crlfPositions_eq_fast`
every compiled caller of `crlfPositions` — runs in `O(1)` stack. -/

/-- Tail-recursive `crlfPositionsGo`: hits accumulate in reverse, one loop
iteration per byte, constant stack. -/
def crlfPositionsRevGo : Nat → Bytes → List Nat → List Nat
  | _, [], acc => acc.reverse
  | _, [_], acc => acc.reverse
  | i, a :: b :: rest, acc =>
    crlfPositionsRevGo (i + 1) (b :: rest) (if a == CR && b == LF then i :: acc else acc)

/-- The reverse-accumulator pass equals `crlfPositionsGo` under the flushed
accumulator. -/
theorem crlfPositionsRevGo_eq (bs : Bytes) :
    ∀ (i : Nat) (acc : List Nat),
      crlfPositionsRevGo i bs acc = acc.reverse ++ crlfPositionsGo i bs := by
  induction bs with
  | nil => intro i acc; simp [crlfPositionsRevGo, crlfPositionsGo]
  | cons a xs ih =>
    intro i acc
    match xs, ih with
    | [], _ => simp [crlfPositionsRevGo, crlfPositionsGo]
    | b :: rest, ih =>
      show crlfPositionsRevGo (i + 1) (b :: rest)
              (if a == CR && b == LF then i :: acc else acc)
          = acc.reverse ++ crlfPositionsGo i (a :: b :: rest)
      rw [ih (i + 1)]
      show _ = acc.reverse ++
          (if a == CR && b == LF then i :: crlfPositionsGo (i + 1) (b :: rest)
            else crlfPositionsGo (i + 1) (b :: rest))
      by_cases h : a == CR && b == LF
      · simp [h]
      · simp [h]

/-- The loop form `crlfPositionsGo` compiles to. -/
def crlfPositionsGoTail (i : Nat) (bs : Bytes) : List Nat := crlfPositionsRevGo i bs []

/-- **The loop/pass agreement.** Installs the constant-stack loop as the
compiled implementation of `crlfPositionsGo`. -/
@[csimp] theorem crlfPositionsGo_eq_tail : @crlfPositionsGo = @crlfPositionsGoTail := by
  funext i bs
  rw [crlfPositionsGoTail, crlfPositionsRevGo_eq bs i []]
  rfl

/-- The linear `crlfPositions`: one pass from index `0`. -/
def crlfPositionsFast (bs : Bytes) : List Nat := crlfPositionsGo 0 bs

/-- filter/map swap (proved locally to avoid depending on a core lemma name). -/
private theorem filter_map_swap (l : List Nat) (p : Nat → Bool) (f : Nat → Nat) :
    List.filter p (List.map f l) = List.map f (List.filter (fun x => p (f x)) l) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.filter_cons]
    by_cases h : p (f a) <;> simp [h, ih]

/-- Cons unfolding of the spec: the head contributes offset `0` iff it starts a
`CR,LF`, and every tail position shifts up by one. -/
theorem crlfPositions_cons (x : UInt8) (xs : Bytes) :
    crlfPositions (x :: xs) =
      (if x == CR && xs.getD 0 0 == LF then [0] else [])
        ++ (crlfPositions xs).map (· + 1) := by
  unfold crlfPositions
  have hFM :
      List.filter (fun i => (x :: xs).getD i 0 == CR && (x :: xs).getD (i + 1) 0 == LF)
          (List.map Nat.succ (List.range xs.length))
        = List.map (· + 1)
            (List.filter (fun i => xs.getD i 0 == CR && xs.getD (i + 1) 0 == LF)
              (List.range xs.length)) := by
    rw [filter_map_swap]
    simp only [List.getD_cons_succ]
  rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, hFM]
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add]
  by_cases h : x == CR && xs.getD 0 0 == LF
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h]; rfl

/-- The linear pass equals the spec up to the running-index shift. -/
theorem crlfPositionsGo_eq (bs : Bytes) :
    ∀ base, crlfPositionsGo base bs = (crlfPositions bs).map (· + base) := by
  have hcomp : ∀ base : Nat, ((· + base) ∘ (· + 1)) = (fun x => x + (base + 1)) := by
    intro base; funext x; simp; omega
  induction bs with
  | nil => intro base; simp [crlfPositionsGo, crlfPositions]
  | cons a xs ih =>
    intro base
    match xs, ih with
    | [], _ =>
      show ([] : List Nat) = List.map (· + base) (crlfPositions [a])
      have hlf : ((0 : UInt8) == LF) = false := by decide
      rw [crlfPositions_cons a [], show crlfPositions ([] : Bytes) = [] from rfl]
      simp [List.getD_nil, hlf]
    | b :: rest, ih =>
      show (if a == CR && b == LF then base :: crlfPositionsGo (base + 1) (b :: rest)
              else crlfPositionsGo (base + 1) (b :: rest)) =
            List.map (· + base) (crlfPositions (a :: b :: rest))
      rw [crlfPositions_cons a (b :: rest), ih (base + 1)]
      simp only [List.getD_cons_zero]
      by_cases h : a == CR && b == LF
      · rw [if_pos h, if_pos h]
        simp only [List.singleton_append, List.map_cons, Nat.zero_add, List.map_map, hcomp]
      · rw [if_neg h, if_neg h]
        simp only [List.nil_append, List.map_map, hcomp]

/-- **The linear/spec agreement.** `crlfPositionsFast` computes the same offsets
as `crlfPositions`, in `O(n)`. -/
@[csimp] theorem crlfPositions_eq_fast : @crlfPositions = @crlfPositionsFast := by
  funext bs
  rw [crlfPositionsFast, crlfPositionsGo_eq bs 0]
  simp

/-- Cut `[start, headLen)` into the segments between the given `CRLF`
positions (each position `p` consumes bytes `p` and `p+1`). -/
def segments (start headLen : Nat) : List Nat → List Span
  | [] => [⟨start, headLen - start⟩]
  | p :: ps => ⟨start, p - start⟩ :: segments (p + 2) headLen ps

/-! `segments` conses before recursing — one frame per header line. The
reverse-accumulator form compiles to a loop (constant stack); the `@[csimp]`
below installs it, spec untouched. -/

/-- Tail-recursive `segments`: spans accumulate in reverse, constant stack. -/
def segmentsRevGo (headLen : Nat) : Nat → List Nat → List Span → List Span
  | start, [], acc => (⟨start, headLen - start⟩ :: acc).reverse
  | start, p :: ps, acc => segmentsRevGo headLen (p + 2) ps (⟨start, p - start⟩ :: acc)

/-- The reverse-accumulator cut equals `segments` under the flushed
accumulator. -/
theorem segmentsRevGo_eq (headLen : Nat) (ps : List Nat) :
    ∀ (start : Nat) (acc : List Span),
      segmentsRevGo headLen start ps acc = acc.reverse ++ segments start headLen ps := by
  induction ps with
  | nil => intro start acc; simp [segmentsRevGo, segments]
  | cons p t ih =>
    intro start acc
    show segmentsRevGo headLen (p + 2) t (⟨start, p - start⟩ :: acc)
        = acc.reverse ++ segments start headLen (p :: t)
    rw [ih (p + 2), segments]
    simp

/-- The loop form `segments` compiles to. -/
def segmentsTail (start headLen : Nat) (ps : List Nat) : List Span :=
  segmentsRevGo headLen start ps []

/-- **The loop/spec agreement.** Installs the constant-stack loop as the
compiled implementation of `segments`. -/
@[csimp] theorem segments_eq_tail : @segments = @segmentsTail := by
  funext start headLen ps
  rw [segmentsTail, segmentsRevGo_eq headLen ps start []]
  rfl

def findByteIdx (t : UInt8) (l : Bytes) : Option Nat :=
  l.findIdx? (· == t)

def isOws (b : UInt8) : Bool := b == SP || b == HTAB

/-- The DEL byte (`0x7F`). -/
def DEL : UInt8 := 127

/-- RFC 7230 field-value discipline for a single header-value byte: a value
byte must be SP, HTAB, a visible ASCII char (`0x21`–`0x7E`), or obs-text
(`0x80`–`0xFF`). The bytes this predicate flags are exactly the ones a value
may not contain: the C0 control bytes other than HTAB (so `NUL`, `CR`, `LF`,
… below `0x20`) and the DEL byte. -/
def isCtlValueByte (b : UInt8) : Bool := (b < SP && b != HTAB) || b == DEL

/-- `"HTTP/"` prefix check for the version field. -/
def startsWithHttpSlash : Bytes → Bool
  | h :: t₁ :: t₂ :: p :: sl :: _ =>
    h == 72 && t₁ == 84 && t₂ == 84 && p == 80 && sl == 47
  | _ => false

structure ReqLineSpans where
  method : Span
  target : Span
  version : Span
  deriving Repr

/-- Parse a request line at absolute offset `off`: exactly three
space-separated parts, non-empty method, version starting `HTTP/`. -/
def parseRequestLine (off : Nat) (line : Bytes) : Option ReqLineSpans := do
  let i₁ ← findByteIdx SP line
  let rest₁ := line.drop (i₁ + 1)
  let i₂ ← findByteIdx SP rest₁
  let rest₂ := rest₁.drop (i₂ + 1)
  if (findByteIdx SP rest₂).isSome then none
  else if i₁ == 0 then none
  else if !startsWithHttpSlash rest₂ then none
  else
    some
      { method := ⟨off, i₁⟩
        target := ⟨off + i₁ + 1, i₂⟩
        version := ⟨off + i₁ + 1 + i₂ + 1, rest₂.length⟩ }

structure RawHeaderSpans where
  name : Span
  value : Span
  deriving Repr

/-- Parse one header line at absolute offset `off`: a non-empty,
whitespace-free name before the first `:`, then the value with leading and
trailing optional whitespace (SP / HTAB) trimmed. The value must satisfy the
RFC 7230 field-value discipline (`isCtlValueByte`): a control byte other than
HTAB (in particular `NUL`) — or DEL — anywhere in the value rejects the line.
The OWS trim only strips SP / HTAB, neither of which `isCtlValueByte` flags, so
checking the raw value is equivalent to checking the trimmed value. -/
def parseHeaderLine (off : Nat) (line : Bytes) : Option RawHeaderSpans := do
  let ci ← findByteIdx COLON line
  if ci == 0 then none
  else
    let name := line.take ci
    if name.any (fun b => isOws b || b == CR || b == LF) then none
    else
      let rawVal := line.drop (ci + 1)
      if rawVal.any isCtlValueByte then none
      else
        let lead := (rawVal.takeWhile isOws).length
        let trimmedFront := rawVal.drop lead
        let trail := (trimmedFront.reverse.takeWhile isOws).length
        some
          { name := ⟨off, ci⟩
            value := ⟨off + ci + 1 + lead, trimmedFront.length - trail⟩ }

/-! ## Canonicalization into the sidecar -/

def isUpperAscii (b : UInt8) : Bool := decide (65 ≤ b ∧ b ≤ 90)

def lowerByte (b : UInt8) : UInt8 := if isUpperAscii b then b + 32 else b

def hasUpper (l : Bytes) : Bool := l.any isUpperAscii

def mkEntry (tag : NameTag) (off len : Nat) : Entry :=
  { tag, off := UInt32.ofNat off, len := UInt32.ofNat len }

/-- The canonical (lowercase) name entry for a raw name span. Already-lowercase
names point into the main arena; otherwise the lowered bytes are appended to
the sidecar and the entry addresses them through the sidecar discriminant. -/
def canonNameEntry (input sidecar : Bytes) (sp : Span) : Bytes × Entry :=
  let raw := sliceSpan input sp
  if hasUpper raw then
    (sidecar ++ raw.map lowerByte,
     mkEntry .headerName (sidecarBaseNat + sidecar.length) sp.len)
  else
    (sidecar, mkEntry .headerName sp.off sp.len)

/-- Flat-buffer `canonNameEntry` with a **flat sidecar accumulator**: the raw
name bytes are read by `sliceArr` (`O(len)`), and the sidecar is an `Array` — its
length is `O(1)` (`Array.size`) and appending a lowered name is amortized
`O(name)` (`Array.append` into the uniquely-owned accumulator), instead of the
spec's `sidecar ++ …` List append that copies the whole growing sidecar and
`sidecar.length` that walks it (`O(sidecar²)` over a header run that lowercases). -/
def canonNameEntryAcc (arr : Array UInt8) (sidecar : Array UInt8) (sp : Span) :
    Array UInt8 × Entry :=
  let raw := sliceArr arr sp
  if hasUpper raw then
    (sidecar ++ (raw.map lowerByte).toArray,
     mkEntry .headerName (sidecarBaseNat + sidecar.size) sp.len)
  else
    (sidecar, mkEntry .headerName sp.off sp.len)

/-- The flat-accumulator name entry matches the spec: reading back the array
sidecar as a list, `canonNameEntryAcc` produces the same `(sidecar, Entry)` as
`canonNameEntry` on the list sidecar. -/
theorem canonNameEntryAcc_toArray (input : Bytes) (sacc : Array UInt8) (sp : Span) :
    (fun p => (Array.toList p.1, p.2)) (canonNameEntryAcc input.toArray sacc sp)
      = canonNameEntry input sacc.toList sp := by
  unfold canonNameEntryAcc canonNameEntry
  rw [sliceArr_toArray]
  by_cases h : hasUpper (sliceSpan input sp)
  · simp [h, Array.toList_append, Array.toList_toArray, Array.length_toList]
  · simp [h]

/-! ## The parse outcome -/

/-- Typed error classes of the head parse. -/
inductive ErrClass where
  /-- The request line is not `method SP target SP HTTP/…`. -/
  | malformedRequestLine
  /-- A header line is not `name ":" OWS value OWS` with a clean name and a
  control-free value, or the head carries more than `maxHeaders` header lines. -/
  | malformedHeader
  /-- A referenced range failed the explicit UTF-8 hypothesis. -/
  | nonUtf8
  /-- Input exceeds the 31-bit addressable range of the main arena. -/
  | tooLarge
  deriving Repr, DecidableEq

def ErrClass.tag : ErrClass → String
  | .malformedRequestLine => "malformed-request-line"
  | .malformedHeader => "malformed-header"
  | .nonUtf8 => "non-utf8"
  | .tooLarge => "too-large"

structure ParsedHeader where
  name : Entry
  value : Entry
  deriving Repr

/-- A parsed request head: the store plus the tagged view entries. -/
structure Request where
  store : Store
  method : Entry
  target : Entry
  version : Entry
  headers : List ParsedHeader
  consumed : Nat
  deriving Repr

inductive Outcome where
  /-- The head parsed; the store is well-formed by `parse_wf` (a theorem, not
  a runtime check) and every range passed the UTF-8 check. -/
  | complete (req : Request)
  /-- No `CRLFCRLF` yet — need more bytes. No consumed count exists. -/
  | incomplete
  | error (e : ErrClass) (detail : String)

/-- Parse all header lines, accumulating the sidecar and parsed headers. -/
def parseHeaders (input : Bytes) (spans : List Span) (sidecar : Bytes) :
    Option (Bytes × List ParsedHeader) :=
  match spans with
  | [] => some (sidecar, [])
  | sp :: rest =>
    if sp.len == 0 then
      -- an empty segment inside the head (bare CRLF) is malformed
      none
    else do
      let raw ← parseHeaderLine sp.off (sliceSpan input sp)
      let (sidecar', nameEntry) := canonNameEntry input sidecar raw.name
      let valueEntry := mkEntry .headerValue raw.value.off raw.value.len
      let (sidecar'', parsed) ← parseHeaders input rest sidecar'
      some (sidecar'', { name := nameEntry, value := valueEntry } :: parsed)

/-! ### Linear-time header parse

`parseHeaders` carries two super-linear costs over a run of header lines:
* it re-slices every header line straight out of the cons-list `input`
  (`sliceSpan input sp`, again inside `canonNameEntry`), and `sliceSpan` walks
  `O(off)` cons cells from the head — header `k` at offset ≈ head length ⇒ the
  per-header sweep is `O(head²)`;
* the sidecar is grown by `sidecar ++ …` (a List append that copies the whole
  growing accumulator) and indexed by `sidecar.length` (which walks it) — a run
  that lowercases `H` names is `O(sidecar²)`.

`parseHeadersAcc` removes both: it reads every header window by index (`sliceArr`)
out of a flat buffer the head is materialized to **once**, and threads the sidecar
as a flat `Array` whose length is `O(1)` and whose append is amortized `O(name)`.
`parseHeaders_eq_fast` proves it computes the same result and installs it as the
compiled implementation (`@[csimp]`): `parse` — the spec every theorem references
— is untouched; only the runtime changes. The recursion is on `parseHeadersAcc`
itself (carrying the already-converted buffer + array sidecar), so the conversion
happens once, not once per header. -/

/-- Flat-buffer header parse with a flat `Array` sidecar accumulator: every header
window is read by index (`sliceArr`) out of `arr`, and the sidecar's length and
append are `O(1)`/amortized-`O(name)`. Recurses on itself carrying both — no
re-conversion per header. Result sidecar is the accumulator's `toList`. -/
def parseHeadersAcc (arr : Array UInt8) (spans : List Span) (sidecar : Array UInt8) :
    Option (Bytes × List ParsedHeader) :=
  match spans with
  | [] => some (sidecar.toList, [])
  | sp :: rest =>
    if sp.len == 0 then
      none
    else do
      let raw ← parseHeaderLine sp.off (sliceArr arr sp)
      let (sidecar', nameEntry) := canonNameEntryAcc arr sidecar raw.name
      let valueEntry := mkEntry .headerValue raw.value.off raw.value.len
      let (sidecar'', parsed) ← parseHeadersAcc arr rest sidecar'
      some (sidecar'', { name := nameEntry, value := valueEntry } :: parsed)

/-- The flat header pass equals the spec: reading the array sidecar back as a list
at the boundary, `parseHeadersAcc` on the buffer view yields the same
`(sidecar, headers)` as `parseHeaders`. -/
theorem parseHeadersAcc_toArray (input : Bytes) (spans : List Span) (sacc : Array UInt8) :
    parseHeadersAcc input.toArray spans sacc = parseHeaders input spans sacc.toList := by
  induction spans generalizing sacc with
  | nil => rfl
  | cons sp rest ih =>
    unfold parseHeadersAcc parseHeaders
    rw [sliceArr_toArray]
    by_cases hlen : sp.len == 0
    · simp [hlen]
    · simp only [hlen, Bool.false_eq_true, if_false]
      rcases hpl : parseHeaderLine sp.off (sliceSpan input sp) with _ | raw
      · rfl
      · have hce := canonNameEntryAcc_toArray input sacc raw.name
        rcases hp : canonNameEntryAcc input.toArray sacc raw.name with ⟨sA, neA⟩
        rw [hp] at hce
        simp [hp, ← hce, ih sA]

/-! `parseHeadersAcc` still conses the parsed header *after* its recursive call
— one frame per header line, depth = header count. `parseHeadersAccRevGo` is
the same pass with the parsed headers accumulated in reverse (tail-recursive ⇒
loop, constant stack); `parseHeadersAcc_eq_tail` installs it as the compiled
implementation (`@[csimp]`), so `parseHeadersFast` and every other compiled
caller of `parseHeadersAcc` run in `O(1)` stack. Spec chain untouched:
`parseHeaders` ← `parseHeadersAcc_toArray` still names the same functions. -/

/-- Tail-recursive `parseHeadersAcc`: parsed headers accumulate in reverse,
one loop iteration per header line, constant stack. -/
def parseHeadersAccRevGo (arr : Array UInt8) :
    List Span → Array UInt8 → List ParsedHeader → Option (Bytes × List ParsedHeader)
  | [], sidecar, acc => some (sidecar.toList, acc.reverse)
  | sp :: rest, sidecar, acc =>
    if sp.len == 0 then
      none
    else
      match parseHeaderLine sp.off (sliceArr arr sp) with
      | none => none
      | some raw =>
        let (sidecar', nameEntry) := canonNameEntryAcc arr sidecar raw.name
        let valueEntry := mkEntry .headerValue raw.value.off raw.value.len
        parseHeadersAccRevGo arr rest sidecar'
          ({ name := nameEntry, value := valueEntry } :: acc)

/-- The reverse-accumulator pass equals `parseHeadersAcc` under the flushed
accumulator. -/
theorem parseHeadersAccRevGo_eq (arr : Array UInt8) (spans : List Span) :
    ∀ (sidecar : Array UInt8) (acc : List ParsedHeader),
      parseHeadersAccRevGo arr spans sidecar acc
        = (parseHeadersAcc arr spans sidecar).map (fun p => (p.1, acc.reverse ++ p.2)) := by
  induction spans with
  | nil => intro sidecar acc; simp [parseHeadersAccRevGo, parseHeadersAcc]
  | cons sp rest ih =>
    intro sidecar acc
    unfold parseHeadersAccRevGo parseHeadersAcc
    by_cases hlen : sp.len == 0
    · simp [hlen]
    · simp only [hlen, Bool.false_eq_true, if_false]
      rcases hpl : parseHeaderLine sp.off (sliceArr arr sp) with _ | raw
      · simp [hpl]
      · rcases hce : canonNameEntryAcc arr sidecar raw.name with ⟨sidecar', nameEntry⟩
        rcases hpa : parseHeadersAcc arr rest sidecar' with _ | ⟨s, ps⟩ <;>
          simp [hpl, hce, hpa, ih sidecar']

/-- The loop form `parseHeadersAcc` compiles to. -/
def parseHeadersAccTail (arr : Array UInt8) (spans : List Span) (sidecar : Array UInt8) :
    Option (Bytes × List ParsedHeader) :=
  parseHeadersAccRevGo arr spans sidecar []

/-- **The loop/pass agreement.** Installs the constant-stack loop as the
compiled implementation of `parseHeadersAcc`. -/
@[csimp] theorem parseHeadersAcc_eq_tail : @parseHeadersAcc = @parseHeadersAccTail := by
  funext arr spans sidecar
  rw [parseHeadersAccTail, parseHeadersAccRevGo_eq arr spans sidecar []]
  rcases parseHeadersAcc arr spans sidecar with _ | ⟨s, ps⟩
  · rfl
  · simp

/-- The compiled header parse: materialize the head into a flat buffer once, then
slice every header window by index, growing the sidecar in a flat array. -/
def parseHeadersFast (input : Bytes) (spans : List Span) (sidecar : Bytes) :
    Option (Bytes × List ParsedHeader) :=
  parseHeadersAcc input.toArray spans sidecar.toArray

/-- **The linear/spec agreement for the header parse.** `parseHeadersFast`
computes the same result as `parseHeaders`, in `O(head)`. -/
@[csimp] theorem parseHeaders_eq_fast : @parseHeaders = @parseHeadersFast := by
  funext input spans sidecar
  rw [parseHeadersFast, parseHeadersAcc_toArray, Array.toList_toArray]

/-- Default header-count bound: the number of header lines a head may carry
before the parser refuses it. `64` matches the slot cap the hand-written
differential baselines enforce; it caps the unbounded-allocation surface an
attacker reaches for with a header flood. -/
def defaultMaxHeaders : Nat := 64

/-- The head parser: bytes → arena view. Total; every referenced range is
registered in the store. The store of every `complete` outcome is well-formed
*by theorem* (`parse_wf`, Arena/ParseTheorems.lean); the explicit UTF-8
hypothesis is the one check discharged dynamically before a `complete` is
produced. `maxHeaders` is the configurable header-count bound (default
`defaultMaxHeaders`): a head with more than `maxHeaders` header lines is
refused as `malformedHeader`, so the parser never registers an unbounded
number of entries. -/
def parse (input : Bytes) (maxHeaders : Nat := defaultMaxHeaders) : Outcome :=
  if sidecarBaseNat ≤ input.length then
    .error .tooLarge "input exceeds the 2^31-1 addressable range"
  else
    match findDoubleCrlf input with
    | none => .incomplete
    | some headEnd =>
      let consumed := headEnd + 4
      let head := input.take headEnd
      match segments 0 headEnd (crlfPositions head) with
      | [] => .error .malformedRequestLine "empty head"
      | reqSpan :: headerSpans =>
        match parseRequestLine reqSpan.off (sliceSpan input reqSpan) with
        | none => .error .malformedRequestLine "want: method SP target SP HTTP/…"
        | some rl =>
          match parseHeaders input headerSpans [] with
          | none => .error .malformedHeader "want: name \":\" OWS value OWS"
          | some (sidecar, headers) =>
            -- Header-count bound: refuse a head that carries more than
            -- `maxHeaders` header lines before any entry is registered.
            if maxHeaders < headers.length then
              .error .malformedHeader "header count exceeds the configured bound"
            else
              let methodE := mkEntry .method rl.method.off rl.method.len
              let targetE := mkEntry .target rl.target.off rl.target.len
              let versionE := mkEntry .version rl.version.off rl.version.len
              let allEntries :=
                methodE :: targetE :: versionE ::
                  headers.flatMap fun h => [h.name, h.value]
              -- `entries := allEntries.reverse` keeps the registration order the
              -- old `foldl Store.pushEntry` produced (each push consed).
              let store : Store :=
                { main := input.toArray, sidecar := sidecar.toArray,
                  entries := allEntries.reverse }
              -- `store.Wf` needs no runtime gate: `parse_wf` proves every store
              -- built here is well-formed (so the `none` arm below is provably
              -- dead too — `Store.resolve_total` — but `resolve` is total-as-
              -- Option, so the match must still spell it).
              -- Dynamic discharge of the explicit UTF-8 hypothesis, per range:
              if allEntries.any (fun e =>
                  match store.resolve e with
                  | some b => !(decide (Utf8Valid b))
                  | none => true) then
                .error .nonUtf8 "a referenced range is not valid UTF-8"
              else
                .complete
                  { store, method := methodE, target := targetE,
                    version := versionE, headers, consumed }

end Parse
end Arena
