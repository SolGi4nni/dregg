import Body.Framing

/-!
# Raw-buffer request framing — the whole boundary decision, in the core

`Body/Framing.lean` proves the framing *decision* smuggling-safe, but it takes an
already-parsed head: `frameFixed` is given the head length `headEnd` and the
parsed `Smuggling.Request`. The step from a **raw accumulation buffer** to that
decision — scan for `CRLFCRLF`, split the head into header fields, classify
`Content-Length`/`Transfer-Encoding` — was, until now, a reimplementation living
only in the trusted host (`crates/dataplane/src/http.rs::next_request` /
`body_frame`). That host code *decides where each HTTP/1.1 request ends* and
*whether the framing is a smuggling reject* — a semantic, correctness-critical
decision the proven core did not govern. A bug there is a request-smuggling
desync on the wire even though `frame_no_smuggle` is green: green-proof + wrong-
wire.

This file closes that gap by lifting the decision into the core. `frameRaw` is a
total `Bytes → Framing.Outcome` that takes the *raw* buffer and produces the
same `{needMore | reject | complete}` verdict, composing:

* `scanHeadEnd` — locate the octet just past the first `CRLFCRLF` (the head end);
* `parseFramingHead` — split the head block into `Smuggling.Header` fields
  (name before the first `:`, value the rest of the line), exactly the raw parse
  the host performed by hand;
* `Body.Framing.frameFixed` — the **already-proven** smuggling-safe boundary.

Everything downstream of the parse is reused unchanged, so `frameRaw` inherits
the smuggling safety and boundary faithfulness the `Body.Framing` theorems
established, now over *raw bytes* rather than a pre-parsed head:

* `frameRaw_no_smuggle` — whenever the parsed head frames both a `Content-Length`
  and a chunked `Transfer-Encoding`, `frameRaw` **rejects**; it is never
  `complete`. The boundary-over-raw-bytes form of `Body.Smuggling.no_desync`.
* `frameRaw_faithful` — a fixed-`Content-Length` framing consumes exactly
  `head ++ body` and leaves the next request verbatim; the boundary is a function
  of the head alone.
* `frameRaw_faithful_empty` — the same for a body-less request.
* `frameRaw_bounded` — a `complete` boundary never runs past the buffer.
* Concrete non-vacuity: a real CL.TE wire head (`clteBuf`) is parsed and
  **rejected** by `frameRaw`; a real body-less GET is framed to its exact
  boundary. The naive length-only host framer (`frameRawNaive`) *would* have
  split the CL.TE head into a 6-octet body and admitted the smuggled tail —
  `frameRaw` refuses it, so the contract is not vacuous.

`frameRequestExport` (`@[export drorb_frame_request]`) is the C-ABI seam the host
crosses instead of deciding framing itself: raw buffer in, an encoded `Outcome`
out (`0`=needMore, `1 r`=reject reason, `2 …le64`=complete count). The resource
cap (`REQUEST_CAP`) stays host-side — it is a DoS limit, not a framing decision.
-/

namespace Body
namespace FrameRaw

open Body Body.Framing Body.Smuggling

/-! ## Octet constants (kept local so this module opens no name-clashing scope) -/

/-- ASCII carriage return. -/
def CR : UInt8 := 13
/-- ASCII line feed. -/
def LF : UInt8 := 10
/-- ASCII colon, the header name/value separator. -/
def COLON : UInt8 := 58
/-- The two-octet line terminator. -/
def crlf : Bytes := [CR, LF]

/-! ## (1) Head-end scan: locate the octet past the first `CRLFCRLF` -/

/-- Does the buffer *begin* with `CRLFCRLF`? Structural cons match + `==` so it
reduces in the kernel (no numeric-literal patterns). -/
def crlfcrlfHere : Bytes → Bool
  | a :: b :: c :: d :: _ => a == CR && b == LF && c == CR && d == LF
  | _ => false

/-- Fuel-bounded scan for the first `CRLFCRLF`; returns the index just past it.
Fuel counts down one per octet consumed, so `buf.length + 1` always suffices.
Structural on the `Nat` fuel, so it reduces in the kernel (no well-founded
recursion) — the concrete-vector theorems below discharge by `decide`. -/
def scanHeadEndFuel : Nat → Nat → Bytes → Option Nat
  | 0, _, _ => none
  | fuel + 1, idx, bs =>
    if crlfcrlfHere bs then some (idx + 4)
    else match bs with
      | [] => none
      | _ :: rest => scanHeadEndFuel fuel (idx + 1) rest

/-- Locate the head end (octet just past the first `CRLFCRLF`), or `none` if the
buffer holds no complete head yet. -/
def scanHeadEnd (buf : Bytes) : Option Nat := scanHeadEndFuel (buf.length + 1) 0 buf

/-! ## (2) Head parse: raw head block → the framing header fields -/

/-- Read up to (and consume) the first `CRLF`: the bytes before it and the bytes
after. `none` if no `CRLF` occurs. Structural on the list. -/
def takeLine : Bytes → Option (Bytes × Bytes)
  | [] => none
  | [_] => none
  | a :: b :: rest =>
    if a == CR && b == LF then some ([], rest)
    else (takeLine (b :: rest)).map (fun p => (a :: p.1, p.2))

/-! ### Bounded-stack head scans

`takeLine` / `splitColon` recurse *inside* `Option.map` and `headerFieldsFuel`
conses after its recursive call, so the compiled code pushes one C stack frame
per octet (per line for the fold) — recursion depth = line length, and this
framing decision runs on the RAW accumulation buffer for every request, before
any size gate can refuse it. Each gets a reverse-accumulator (tail-recursive)
twin the compiler emits as a loop — `O(1)` stack regardless of input —
installed as the compiled implementation by `@[csimp]`. The specs (and every
kernel-reduction `decide` theorem below) are untouched. -/

/-- Tail-recursive `takeLine`: the line accumulates in reverse, one loop
iteration per octet, constant stack. -/
def takeLineRevGo : Bytes → Bytes → Option (Bytes × Bytes)
  | _, [] => none
  | _, [_] => none
  | acc, a :: b :: rest =>
    if a == CR && b == LF then some (acc.reverse, rest)
    else takeLineRevGo (a :: acc) (b :: rest)

/-- The reverse-accumulator scan equals `takeLine` under the flushed
accumulator. -/
theorem takeLineRevGo_eq (bs : Bytes) :
    ∀ acc, takeLineRevGo acc bs
        = (takeLine bs).map (fun p => (acc.reverse ++ p.1, p.2)) := by
  induction bs with
  | nil => intro acc; rfl
  | cons a xs ih =>
    intro acc
    match xs, ih with
    | [], _ => rfl
    | b :: rest, ih =>
      show (if a == CR && b == LF then some (acc.reverse, rest)
              else takeLineRevGo (a :: acc) (b :: rest))
          = (takeLine (a :: b :: rest)).map (fun p => (acc.reverse ++ p.1, p.2))
      rw [takeLine]
      by_cases h : a == CR && b == LF
      · simp [h]
      · rw [if_neg h, if_neg h, ih (a :: acc), Option.map_map]
        rcases takeLine (b :: rest) with _ | ⟨pre, rest'⟩
        · rfl
        · simp

/-- The loop form `takeLine` compiles to. -/
def takeLineTail (bs : Bytes) : Option (Bytes × Bytes) := takeLineRevGo [] bs

/-- **The loop/spec agreement.** Installs the constant-stack loop as the
compiled implementation of `takeLine`. -/
@[csimp] theorem takeLine_eq_tail : @takeLine = @takeLineTail := by
  funext bs
  rw [takeLineTail, takeLineRevGo_eq bs []]
  rcases takeLine bs with _ | ⟨pre, rest⟩
  · rfl
  · simp

/-- Split a header line at the first `:`: the name (before it) and the value (the
rest of the line, colon consumed). `none` if the line carries no `:`. The value
keeps its leading whitespace; `Smuggling`'s own `trim` normalizes it, so the
classification matches the host's trimmed lookup. -/
def splitColon : Bytes → Option (Bytes × Bytes)
  | [] => none
  | b :: bs =>
    if b == COLON then some ([], bs)
    else (splitColon bs).map (fun p => (b :: p.1, p.2))

/-- Tail-recursive `splitColon`: the name accumulates in reverse, one loop
iteration per octet, constant stack. -/
def splitColonRevGo : Bytes → Bytes → Option (Bytes × Bytes)
  | _, [] => none
  | acc, b :: bs =>
    if b == COLON then some (acc.reverse, bs)
    else splitColonRevGo (b :: acc) bs

/-- The reverse-accumulator scan equals `splitColon` under the flushed
accumulator. -/
theorem splitColonRevGo_eq (bs : Bytes) :
    ∀ acc, splitColonRevGo acc bs
        = (splitColon bs).map (fun p => (acc.reverse ++ p.1, p.2)) := by
  induction bs with
  | nil => intro acc; rfl
  | cons b t ih =>
    intro acc
    show (if b == COLON then some (acc.reverse, t) else splitColonRevGo (b :: acc) t)
        = (splitColon (b :: t)).map (fun p => (acc.reverse ++ p.1, p.2))
    rw [splitColon]
    by_cases h : b == COLON
    · simp [h]
    · rw [if_neg h, if_neg h, ih (b :: acc), Option.map_map]
      rcases splitColon t with _ | ⟨pre, rest⟩
      · rfl
      · simp

/-- The loop form `splitColon` compiles to. -/
def splitColonTail (bs : Bytes) : Option (Bytes × Bytes) := splitColonRevGo [] bs

/-- **The loop/spec agreement.** Installs the constant-stack loop as the
compiled implementation of `splitColon`. -/
@[csimp] theorem splitColon_eq_tail : @splitColon = @splitColonTail := by
  funext bs
  rw [splitColonTail, splitColonRevGo_eq bs []]
  rcases splitColon bs with _ | ⟨pre, rest⟩
  · rfl
  · simp

/-- Fold header lines out of the head block until the blank line. A line without
a `:` (the request line) is skipped — it carries no framing signal. Fuel-bounded
for kernel reduction; `head.length + 1` always suffices (each step consumes at
least a line's `CRLF`). -/
def headerFieldsFuel : Nat → Bytes → List Smuggling.Header
  | 0, _ => []
  | fuel + 1, bs =>
    match takeLine bs with
    | none => []
    | some ([], _) => []                      -- blank line: end of the head block
    | some (line, rest) =>
      match splitColon line with
      | none => headerFieldsFuel fuel rest     -- no colon (request line): skip
      | some (name, value) =>
        { name := name, value := value } :: headerFieldsFuel fuel rest

/-- Tail-recursive `headerFieldsFuel`: fields accumulate in reverse, one loop
iteration per header line, constant stack. -/
def headerFieldsFuelRevGo : Nat → Bytes → List Smuggling.Header → List Smuggling.Header
  | 0, _, acc => acc.reverse
  | fuel + 1, bs, acc =>
    match takeLine bs with
    | none => acc.reverse
    | some ([], _) => acc.reverse
    | some (line, rest) =>
      match splitColon line with
      | none => headerFieldsFuelRevGo fuel rest acc
      | some (name, value) =>
        headerFieldsFuelRevGo fuel rest ({ name := name, value := value } :: acc)

/-- The reverse-accumulator fold equals `headerFieldsFuel` under the flushed
accumulator. -/
theorem headerFieldsFuelRevGo_eq :
    ∀ (fuel : Nat) (bs : Bytes) (acc : List Smuggling.Header),
      headerFieldsFuelRevGo fuel bs acc = acc.reverse ++ headerFieldsFuel fuel bs := by
  intro fuel
  induction fuel with
  | zero => intro bs acc; simp [headerFieldsFuelRevGo, headerFieldsFuel]
  | succ f ih =>
    intro bs acc
    unfold headerFieldsFuelRevGo headerFieldsFuel
    rcases htl : takeLine bs with _ | ⟨line, rest⟩
    · simp [htl]
    · rcases line with _ | ⟨x, xs⟩
      · simp [htl]
      · rcases hsc : splitColon (x :: xs) with _ | ⟨name, value⟩ <;>
          simp [htl, hsc, ih rest]

/-- The loop form `headerFieldsFuel` compiles to. -/
def headerFieldsFuelTail (fuel : Nat) (bs : Bytes) : List Smuggling.Header :=
  headerFieldsFuelRevGo fuel bs []

/-- **The loop/spec agreement.** Installs the constant-stack loop as the
compiled implementation of `headerFieldsFuel`. -/
@[csimp] theorem headerFieldsFuel_eq_tail : @headerFieldsFuel = @headerFieldsFuelTail := by
  funext fuel bs
  rw [headerFieldsFuelTail, headerFieldsFuelRevGo_eq fuel bs []]
  rfl

/-- Parse the framing-relevant head into a `Smuggling.Request`. The decision
classifiers (`clStatus`/`teStatus`) read only the `content-length` /
`transfer-encoding` fields, so carrying every field is faithful and harmless. -/
def parseFramingHead (head : Bytes) : Smuggling.Request :=
  { headers := headerFieldsFuel (head.length + 1) head }

/-! ## (3) The whole raw-buffer framing decision -/

/-- **`frameRaw`.** The complete request-framing decision over a *raw* buffer:
scan for the head end, parse the head, and take the proven smuggling-safe
boundary `Body.Framing.frameFixed`. No head yet ⇒ `needMore`. This is the
decision the trusted host reimplemented in `http.rs`; here it is one proven
function of the bytes. -/
def frameRaw (buf : Bytes) : Framing.Outcome :=
  match scanHeadEnd buf with
  | none => .needMore
  | some headEnd => Framing.frameFixed buf headEnd (parseFramingHead (buf.take headEnd))

/-! ## No smuggling: a CL/TE overlap in the raw bytes is never a length boundary -/

/-- **`frameRaw_no_smuggle` (headline).** If the head the scan locates parses to a
request that frames *both* a valid `Content-Length` and a chunked
`Transfer-Encoding`, `frameRaw` **rejects** the raw buffer — it is never
`complete`. So the host can never consume only the `Content-Length` octets while
leaving the chunked tail as a smuggled second request. The raw-buffer form of
`Body.Framing.frame_no_smuggle` (itself the boundary form of
`Body.Smuggling.no_desync`). -/
theorem frameRaw_no_smuggle (buf : Bytes) (headEnd n : Nat)
    (hscan : scanHeadEnd buf = some headEnd)
    (hcl : Smuggling.clStatus (parseFramingHead (buf.take headEnd)) = .present n)
    (hte : Smuggling.teStatus (parseFramingHead (buf.take headEnd)) = .chunked) :
    frameRaw buf = .reject .bothClAndTe
    ∧ (∀ c, frameRaw buf ≠ .complete c) := by
  have hff := Framing.frame_no_smuggle buf headEnd n (parseFramingHead (buf.take headEnd)) hcl hte
  have hfr : frameRaw buf = Framing.frameFixed buf headEnd (parseFramingHead (buf.take headEnd)) := by
    simp only [frameRaw, hscan]
  exact ⟨hfr.trans hff.1, by intro c h; rw [hfr] at h; exact hff.2 c h⟩

/-- **`frameRaw_no_smuggle_general`.** The full guarantee: whenever *any*
`Content-Length` field (valid, invalid, or duplicated) is present alongside a
chunked `Transfer-Encoding`, `frameRaw` rejects and is never `complete`. -/
theorem frameRaw_no_smuggle_general (buf : Bytes) (headEnd : Nat)
    (hscan : scanHeadEnd buf = some headEnd)
    (hcl : Smuggling.clStatus (parseFramingHead (buf.take headEnd)) ≠ .absent)
    (hte : Smuggling.teStatus (parseFramingHead (buf.take headEnd)) = .chunked) :
    (∃ r, frameRaw buf = .reject r) ∧ (∀ c, frameRaw buf ≠ .complete c) := by
  have hff := Framing.frame_no_smuggle_general buf headEnd (parseFramingHead (buf.take headEnd)) hcl hte
  have hfr : frameRaw buf = Framing.frameFixed buf headEnd (parseFramingHead (buf.take headEnd)) := by
    simp only [frameRaw, hscan]
  obtain ⟨⟨r, hr⟩, hnc⟩ := hff
  exact ⟨⟨r, hfr.trans hr⟩, by intro c h; rw [hfr] at h; exact hnc c h⟩

/-! ## Faithfulness: the consumed prefix is exactly head ++ body -/

/-- **`frameRaw_faithful` (headline).** When the scan locates the head end and the
parsed head frames a fixed `Content-Length` of `n` octets, over a buffer
`head ++ body ++ rest` with `head` the located head (length `headEnd`) and `body`
exactly `n` octets, `frameRaw` reports `complete (headEnd + n)` and that boundary
splits the buffer exactly: the consumed prefix is `head ++ body`, the remainder
is `rest` verbatim. The boundary is a function of the head alone — no
attacker-chosen `body`/`rest` byte can shift it. -/
theorem frameRaw_faithful (head body rest : Bytes) (headEnd n : Nat)
    (hhead : head.length = headEnd) (hbody : body.length = n)
    (hscan : scanHeadEnd (head ++ body ++ rest) = some headEnd)
    (hdec : Smuggling.decide (parseFramingHead head) = .length n) :
    frameRaw (head ++ body ++ rest) = .complete (headEnd + n)
    ∧ (head ++ body ++ rest).take (headEnd + n) = head ++ body
    ∧ (head ++ body ++ rest).drop (headEnd + n) = rest := by
  have htakehead : (head ++ body ++ rest).take headEnd = head := by
    rw [List.append_assoc, ← hhead]; exact List.take_left _ _
  have hfr : frameRaw (head ++ body ++ rest)
      = Framing.frameFixed (head ++ body ++ rest) headEnd (parseFramingHead head) := by
    simp only [frameRaw, hscan, htakehead]
  have hff := Framing.framing_faithful head body rest headEnd n (parseFramingHead head)
    hhead hbody hdec
  exact ⟨hfr.trans hff.1, hff.2.1, hff.2.2⟩

/-- **`frameRaw_faithful_empty`.** A body-less request (the parsed head frames no
body) consumes exactly the located head; the whole remainder is the next request
verbatim. -/
theorem frameRaw_faithful_empty (head rest : Bytes) (headEnd : Nat)
    (hhead : head.length = headEnd)
    (hscan : scanHeadEnd (head ++ rest) = some headEnd)
    (hdec : Smuggling.decide (parseFramingHead head) = .empty) :
    frameRaw (head ++ rest) = .complete headEnd
    ∧ (head ++ rest).take headEnd = head
    ∧ (head ++ rest).drop headEnd = rest := by
  have htakehead : (head ++ rest).take headEnd = head := by
    rw [← hhead]; exact List.take_left _ _
  have hfr : frameRaw (head ++ rest)
      = Framing.frameFixed (head ++ rest) headEnd (parseFramingHead head) := by
    simp only [frameRaw, hscan, htakehead]
  have hff := Framing.framing_faithful_empty head rest headEnd (parseFramingHead head) hhead hdec
  exact ⟨hfr.trans hff.1, hff.2.1, hff.2.2⟩

/-! ## No overread: a complete boundary stays inside the buffer -/

/-- **`frameRaw_bounded`.** A `complete` framing never runs past the buffer: the
consumed count is at most the buffer length. -/
theorem frameRaw_bounded (buf : Bytes) (c : Nat) (h : frameRaw buf = .complete c) :
    c ≤ buf.length := by
  unfold frameRaw at h
  cases hscan : scanHeadEnd buf with
  | none => rw [hscan] at h; exact Framing.Outcome.noConfusion h
  | some headEnd =>
    rw [hscan] at h
    exact Framing.frame_bounded buf headEnd c (parseFramingHead (buf.take headEnd)) h

/-! ## Concrete non-vacuity: a real CL.TE wire head is rejected -/

/-- A real CL.TE request head on the wire:

    content-length: 6 CRLF
    transfer-encoding: chunked CRLF
    CRLF

built from the lower-case field-name constants and the `chunked` token. The
scan locates its `CRLFCRLF`; the parse recovers a `Content-Length: 6` and a
chunked `Transfer-Encoding`. -/
def clteHead : Bytes :=
  Smuggling.clName ++ [COLON, 32, 54] ++ crlf ++          -- "content-length: 6"
  Smuggling.teName ++ [COLON, 32] ++ Smuggling.chunkedToken ++ crlf ++  -- "transfer-encoding: chunked"
  crlf

/-- The raw CL.TE buffer: the head plus the attacker chunk terminator and the
smuggled tail (`0 CRLF SMUGGLED`). The tail is irrelevant to the reject (a
function of the head), but long enough that the naive length-only framer below
*would* compute a 6-octet-body boundary — the desync `frameRaw` refuses. -/
def clteBuf : Bytes :=
  clteHead ++ [48, CR, LF, 83, 77, 85, 71, 71, 76, 69, 68]   -- "0" CRLF "SMUGGLED"

/-- The scan locates the head end of the CL.TE buffer. -/
theorem clte_scan : scanHeadEnd clteBuf = some clteHead.length := by decide

/-- The parsed CL.TE head frames a valid `Content-Length: 6`. -/
theorem clte_parsed_cl :
    Smuggling.clStatus (parseFramingHead (clteBuf.take clteHead.length)) = .present 6 := by decide

/-- The parsed CL.TE head frames a chunked `Transfer-Encoding`. -/
theorem clte_parsed_te :
    Smuggling.teStatus (parseFramingHead (clteBuf.take clteHead.length)) = .chunked := by decide

/-- **`frameRaw` rejects the raw CL.TE buffer.** The smuggling decision now lives
in the core over raw bytes: the boundary is never computed for a CL/TE overlap,
so the `0`-terminated chunk tail is never split off as a separate request. -/
theorem clte_frameRaw_reject : frameRaw clteBuf = .reject .bothClAndTe :=
  (frameRaw_no_smuggle clteBuf clteHead.length 6 clte_scan clte_parsed_cl clte_parsed_te).1

/-- **`frameRaw` never frames the CL.TE buffer to the 6-octet-body boundary** —
the exact desync a length-only host framer would produce. -/
theorem clte_frameRaw_not_length (c : Nat) : frameRaw clteBuf ≠ .complete c :=
  (frameRaw_no_smuggle clteBuf clteHead.length 6 clte_scan clte_parsed_cl clte_parsed_te).2 c

/-! ## Concrete: a body-less GET is framed to its exact boundary -/

/-- A body-less request head:

    host: x CRLF
    CRLF

(the request line is elided; it carries no framing signal and the parser skips
lines without a `:`). -/
def getHead : Bytes :=
  [104, 111, 115, 116] ++ [COLON, 32, 120] ++ crlf ++      -- "host: x"
  crlf

/-- The parsed GET head frames no body. -/
theorem get_parsed_empty :
    Smuggling.decide (parseFramingHead getHead) = .empty := by decide

/-- The scan locates the GET head end. -/
theorem get_scan : scanHeadEnd getHead = some getHead.length := by decide

/-- **`frameRaw` frames the body-less GET to its exact boundary.** (The general
`frameRaw_faithful_empty` above extends this to any pipelined remainder once the
scan is located.) -/
theorem get_frameRaw_complete : frameRaw getHead = .complete getHead.length := by
  have h := frameRaw_faithful_empty getHead [] getHead.length rfl
    (by rw [List.append_nil]; exact get_scan) get_parsed_empty
  rw [List.append_nil] at h
  exact h.1

/-! ## The mutant the raw-boundary proof buys -/

/-- A naive host framer that consults only `Content-Length`, ignoring
`Transfer-Encoding` — the vulnerable behaviour `frameRaw` replaces. -/
def frameRawNaive (buf : Bytes) : Framing.Outcome :=
  match scanHeadEnd buf with
  | none => .needMore
  | some headEnd =>
    match Smuggling.clStatus (parseFramingHead (buf.take headEnd)) with
    | .present n => if headEnd + n ≤ buf.length then .complete (headEnd + n) else .needMore
    | _ => .needMore

/-- **The mutant desyncs on the raw CL.TE buffer.** The naive framer computes a
6-octet-body boundary — precisely the split `frameRaw` refuses
(`clte_frameRaw_reject`). The two disagree, so the raw-buffer contract is not
vacuous: a natural host mutant violates it. -/
theorem naive_would_smuggle_raw :
    frameRawNaive clteBuf = .complete (clteHead.length + 6)
    ∧ frameRaw clteBuf ≠ frameRawNaive clteBuf := by
  have hn : frameRawNaive clteBuf = .complete (clteHead.length + 6) := by decide
  refine ⟨hn, ?_⟩
  rw [hn, clte_frameRaw_reject]
  intro h; exact Framing.Outcome.noConfusion h

/-! ## (4) The host-facing C-ABI seam -/

/-- A framing reason as one wire byte (host reads it to pick a close/response). -/
def reasonByte : Smuggling.Reason → UInt8
  | .bothClAndTe => 0
  | .dupContentLength => 1
  | .invalidContentLength => 2
  | .chunkedNotLast => 3
  | .unsupportedTransferEncoding => 4

/-- Little-endian 8-octet encoding of a consumed count (host reads the boundary). -/
def le64 (n : Nat) : Bytes :=
  (List.range 8).map (fun i => UInt8.ofNat (n / (256 ^ i) % 256))

/-- Encode a framing outcome for the host: `0`=needMore, `1 r`=reject reason,
`2 …le64`=complete count. -/
def encodeOutcome : Framing.Outcome → Bytes
  | .needMore => [0]
  | .reject r => [1, reasonByte r]
  | .complete c => 2 :: le64 c

/-- **`drorb_frame_request`.** The seam the host crosses instead of deciding
framing itself: the raw accumulation buffer in, the encoded `frameRaw` verdict
out. Total `ByteArray → ByteArray`. -/
@[export drorb_frame_request]
def frameRequestExport (input : ByteArray) : ByteArray :=
  ByteArray.mk (encodeOutcome (frameRaw input.toList)).toArray

/-- The encoder maps a CL/TE reject to the two host bytes `[1, 0]`. -/
theorem encode_reject_bothClAndTe :
    encodeOutcome (.reject .bothClAndTe) = [1, 0] := rfl

/-- **ABI check.** The exported seam's payload for the raw CL.TE buffer is the
reject encoding `[1, 0]`: the host is told to refuse, never handed a length
boundary. (`frameRequestExport` wraps exactly `encodeOutcome ∘ frameRaw`.) -/
theorem clte_encoded : encodeOutcome (frameRaw clteBuf) = [1, 0] := by
  rw [clte_frameRaw_reject]; rfl

end FrameRaw
end Body
