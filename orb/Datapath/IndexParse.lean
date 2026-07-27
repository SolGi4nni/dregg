import Datapath.Scan
import Reactor.Config

/-!
# Datapath.IndexParse — the INDEX-NATIVE request-head parse (no request-list materialization)

The deployed serve parses through `Reactor.Config.h1ParseFn s.read`, where
`s.read` (`Datapath.Span`) is `List.ofFn` — it conses the ENTIRE borrowed request
window into a `List UInt8` (one heap cell per received byte) *before* a single byte
is parsed. That per-byte cons is the dominant datapath tax.

This module builds the parse that never materializes that list. `parseIndexNative`
reads the borrowed span by INDEX:

* it frames the request with `spanFindDoubleCrlf` — the index-native `CRLFCRLF`
  scan of `Datapath.Scan` (a `getByte` cursor loop, materializing no list);
* it sweeps the head's `CRLF` positions with `spanCrlfPositions` over the head
  sub-window (again index reads, no list);
* it materializes the recv window ONCE as a **flat `Array`** via
  `s.buf.data.extract` — an `O(len)` buffer copy, NOT a per-byte cons-list — and
  feeds that array to the deployed head parser's array-native fast path
  (`sliceArr` / `parseHeadersAcc`, already the compiled `@[csimp]` implementation).

`parseIndexNative_refines` proves it computes the **byte-identical** `ParseOutcome`
the deployed `h1ParseFn s.read` produces — via equality transfer (`spanArr_toList`,
`arrSpan_read`, the `Scan` refinements), not a re-specification. The `List UInt8` of
the request appears only on the RHS of that theorem (the spec); it is never computed
on the index-native path.

This is additive: `Datapath.{Span,Scan,Refine,Serve}` and `Arena.Parse` are used, not
modified. It is the request-cons-removal seam of CODEGEN-SEAM-SCOPE.
-/

namespace Datapath
namespace SpanBytes

open Arena.Parse (findDoubleCrlf crlfPositions segments parseRequestLine parseHeaders
  parseHeadersAcc sliceArr sliceSpan mkEntry defaultMaxHeaders Span)

/-! ## The full span over a flat `Array` — reused as an index-native scan surface -/

/-- A full `SpanBytes` window over an `Array UInt8` (via `ByteArray.mk`). Its
`getByte i` is the direct array load `arr[i]!`, so the `Scan` index-native scanners
run on it as pure `getByte` loops. -/
def arrSpan (arr : Array UInt8) : SpanBytes := full (ByteArray.mk arr)

@[simp] theorem arrSpan_len (arr : Array UInt8) : (arrSpan arr).len = arr.size := rfl

/-- The full array span reads back exactly the array's byte list — the bridge that
lets the index-native scanners over `arrSpan arr` be proven equal to the deployed
list scanners on `arr.toList`. -/
theorem arrSpan_read (arr : Array UInt8) : (arrSpan arr).read = arr.toList := by
  unfold arrSpan
  rw [read_eq_denote _ (full_wf _), denote_full]

/-! ## The head sub-window read (index-native), and the CRLFCRLF-offset bound -/

/-- The `(0, n)` sub-window of `w` reads the first `n` bytes of `w` (index-native),
provided `n` fits the window. This restricts the `CRLF` sweep to the head. -/
theorem sub0_read (w : SpanBytes) (n : Nat) (h : n ≤ w.len) :
    (w.sub 0 n).read = w.read.take n := by
  apply List.ext_getElem
  · rw [length_read, sub_len, List.length_take, length_read]; omega
  · intro i h1 _
    rw [length_read, sub_len] at h1
    rw [getByte_eq_read_getElem (w.sub 0 n) i (by rw [length_read, sub_len]; exact h1)]
    rw [List.getElem_take, getByte_eq_read_getElem w i (by rw [length_read]; omega)]
    simp only [SpanBytes.getByte, sub_buf, sub_off, Nat.add_zero]

/-- The deployed `CRLFCRLF` scan reports an offset that leaves at least four bytes:
`findDoubleCrlf l = some k ⇒ k ≤ l.length`. Lets the head sub-window `(0, k)` be a
well-formed restriction of the recv window. -/
theorem findDoubleCrlf_some_le (l : List UInt8) (k : Nat)
    (h : findDoubleCrlf l = some k) : k ≤ l.length := by
  induction l generalizing k with
  | nil => simp [findDoubleCrlf] at h
  | cons a t ih =>
    match t, ih with
    | [], _ => simp [findDoubleCrlf] at h
    | [b], _ => simp [findDoubleCrlf] at h
    | [b, c], _ => simp [findDoubleCrlf] at h
    | b :: c :: d :: t', ih =>
      rw [findDoubleCrlf] at h
      by_cases hm : a == Arena.Parse.CR && b == Arena.Parse.LF
          && c == Arena.Parse.CR && d == Arena.Parse.LF
      · rw [if_pos hm] at h; simp only [Option.some.injEq] at h; omega
      · rw [if_neg hm] at h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨k', hk', hkeq⟩ := h
        have := ih k' hk'
        simp only [List.length_cons] at *
        omega

/-! ## The index-native primitives agree with the deployed list primitives -/

/-- The index-native `CRLFCRLF` scan over the array span equals the deployed
framing scan on the array's list — computed with no materialized list. -/
theorem spanFindDoubleCrlf_arrSpan (arr : Array UInt8) :
    spanFindDoubleCrlf (arrSpan arr) = findDoubleCrlf arr.toList := by
  rw [spanFindDoubleCrlf_eq_read, arrSpan_read]

/-- The index-native head `CRLF` sweep equals the deployed `crlfPositions` on the
head slice `arr.toList.take n` — index reads over the head sub-window, no list. -/
theorem headCrlf_arrSpan (arr : Array UInt8) (n : Nat) (h : n ≤ arr.size) :
    spanCrlfPositions ((arrSpan arr).sub 0 n) = crlfPositions (arr.toList.take n) := by
  rw [spanCrlfPositions_eq_read, sub0_read (arrSpan arr) n (by rw [arrSpan_len]; exact h),
    arrSpan_read]

/-- The array slice (`Array.extract`, `O(len)`) equals the deployed list slice. -/
theorem sliceArr_list (arr : Array UInt8) (sp : Span) :
    sliceArr arr sp = sliceSpan arr.toList sp := by
  simpa using Arena.Parse.sliceArr_toArray arr.toList sp

/-- The flat-buffer header parse equals the deployed list header parse. -/
theorem parseHeadersAcc_list (arr : Array UInt8) (hs : List Span) :
    parseHeadersAcc arr hs #[] = parseHeaders arr.toList hs [] := by
  simpa using Arena.Parse.parseHeadersAcc_toArray arr.toList hs #[]

/-! ## The array-native head parse — a byte-identical mirror of `Arena.Parse.parse` -/

/-- The array-native head parser: structurally identical to `Arena.Parse.parse`, but
reading the head by INDEX (`spanFindDoubleCrlf` / `spanCrlfPositions` over the
`arrSpan`, `sliceArr` per line) with the main arena taken directly as the flat `arr`
— no `input.toArray` re-copy, no cons-list. Proven equal to `parse arr.toList`. -/
def parseArr (arr : Array UInt8) : Arena.Parse.Outcome :=
  if Arena.sidecarBaseNat ≤ arr.size then
    .error .tooLarge "input exceeds the 2^31-1 addressable range"
  else
    match spanFindDoubleCrlf (arrSpan arr) with
    | none => .incomplete
    | some headEnd =>
      let consumed := headEnd + 4
      match segments 0 headEnd (spanCrlfPositions ((arrSpan arr).sub 0 headEnd)) with
      | [] => .error .malformedRequestLine "empty head"
      | reqSpan :: headerSpans =>
        match parseRequestLine reqSpan.off (sliceArr arr reqSpan) with
        | none => .error .malformedRequestLine "want: method SP target SP HTTP/…"
        | some rl =>
          match parseHeadersAcc arr headerSpans #[] with
          | none => .error .malformedHeader "want: name \":\" OWS value OWS"
          | some (sidecar, headers) =>
            if defaultMaxHeaders < headers.length then
              .error .malformedHeader "header count exceeds the configured bound"
            else
              let methodE := mkEntry .method rl.method.off rl.method.len
              let targetE := mkEntry .target rl.target.off rl.target.len
              let versionE := mkEntry .version rl.version.off rl.version.len
              let allEntries :=
                methodE :: targetE :: versionE ::
                  headers.flatMap fun h => [h.name, h.value]
              let store : Arena.Store :=
                { main := arr, sidecar := sidecar.toArray,
                  entries := allEntries.reverse }
              if allEntries.any (fun e =>
                  match store.resolve e with
                  | some b => !(decide (Arena.Utf8Valid b))
                  | none => true) then
                .error .nonUtf8 "a referenced range is not valid UTF-8"
              else
                .complete
                  { store, method := methodE, target := targetE,
                    version := versionE, headers, consumed }

/-- **The array-native head parse equals the deployed list parse.** Byte-for-byte
the same `Arena.Parse.Outcome` as `parse arr.toList`, with every list scan replaced
by an index-native scan and the main arena taken as the flat `arr`. -/
theorem parseArr_eq (arr : Array UInt8) : parseArr arr = Arena.Parse.parse arr.toList := by
  unfold parseArr Arena.Parse.parse
  rw [Array.length_toList, spanFindDoubleCrlf_arrSpan]
  by_cases hg : Arena.sidecarBaseNat ≤ arr.size
  · rw [if_pos hg, if_pos hg]
  · rw [if_neg hg, if_neg hg]
    -- The two functions compile to distinct `match_N` auxiliaries, so equality is
    -- established by splitting every scrutinee to constructor leaves (defeq closes
    -- each). Scrutinees are made equal first by the index-native ↦ list rewrites.
    rcases hfd : findDoubleCrlf arr.toList with _ | headEnd
    · rfl
    · have hbound : headEnd ≤ arr.size := by
        have := findDoubleCrlf_some_le arr.toList headEnd hfd
        rwa [Array.length_toList] at this
      simp only [headCrlf_arrSpan arr headEnd hbound]
      rcases hseg : segments 0 headEnd (crlfPositions (arr.toList.take headEnd)) with
        _ | ⟨reqSpan, headerSpans⟩
      · rfl
      · simp only [sliceArr_list]
        rcases hrl : parseRequestLine reqSpan.off (sliceSpan arr.toList reqSpan) with _ | rl
        · rfl
        · simp only [parseHeadersAcc_list]
          rcases hph : parseHeaders arr.toList headerSpans [] with _ | ⟨sidecar, headers⟩
          · rfl
          · simp only [Array.toArray_toList]
            rfl

/-! ## The index-native serve read — `parseIndexNative` -/

/-- The flat array view of the borrowed span — the recv window copied ONCE with
`Array.extract` (`O(len)`, no per-byte cons). Equal to `s.read.toArray` on a
well-formed span, but computed without ever building `s.read`. -/
def spanArr (s : SpanBytes) : Array UInt8 := s.buf.data.extract s.off (s.off + s.len)

/-- The array view's byte list is exactly the deployed `s.read` — the equality that
transfers the deployed parse spec onto the index-native path. `s.read` (the cons
`List.ofFn`) is on the RHS only; it is never computed to obtain the LHS. -/
theorem spanArr_toList (s : SpanBytes) (h : s.Wf) : (spanArr s).toList = s.read := by
  unfold spanArr
  rw [Array.toList_extract, List.extract_eq_drop_take, Nat.add_sub_cancel_left]
  show s.denote = s.read
  exact (read_eq_denote s h).symm

/-- **The index-native request-head parse.** Reads the borrowed span by INDEX:
`spanArr` copies the recv window once as a flat array (no cons-list), the head is
framed and swept by the `Scan` index-native scanners, and the deployed adapter maps
the arena outcome to a `Proto.ParseOutcome`. `s.read` / `List.ofFn` is never called
on this path. -/
def parseIndexNative (s : SpanBytes) : Proto.ParseOutcome :=
  Reactor.Config.arenaToProto (parseArr (spanArr s))

/-- **THE REFINEMENT.** The index-native head parse computes the *byte-identical*
`ParseOutcome` the deployed cons-list parse (`h1ParseFn s.read`) produces on the
span's denotation — proven by equality transfer, not re-specification. The request
`List UInt8` is materialized only in the RHS spec, never on the index-native path. -/
theorem parseIndexNative_refines (s : SpanBytes) (h : s.Wf) :
    parseIndexNative s = Reactor.Config.h1ParseFn s.read := by
  unfold parseIndexNative Reactor.Config.h1ParseFn
  rw [parseArr_eq (spanArr s), spanArr_toList s h]

/-! ## Non-vacuity — a concrete request span parses to the exact request

Real request spans; the index-native parse computes the exact deployed
`Proto.Request`, and differs on differing bytes. `spanArr` / `parseArr` never invoke
`SpanBytes.read`. -/

/-- `"GET /health HTTP/1.1\r\n\r\n"` as a whole-buffer span. -/
def healthBytes : ByteArray := "GET /health HTTP/1.1\r\n\r\n".toUTF8
def healthSpan : SpanBytes := full healthBytes

def postBytes : ByteArray := "POST /health HTTP/1.1\r\n\r\n".toUTF8
def postSpan : SpanBytes := full postBytes

def truncBytes : ByteArray := "GET /health HTTP/1.1\r\n".toUTF8
def truncSpan : SpanBytes := full truncBytes

/-- The index-native parse of the health span yields the exact request. -/
def healthIndexParsesExact : Bool :=
  match parseIndexNative healthSpan with
  | .request _ req _ =>
      req.method == "GET".toUTF8.toList &&
      req.target == "/health".toUTF8.toList &&
      req.version == "HTTP/1.1".toUTF8.toList &&
      req.headers == []
  | _ => false

#guard healthIndexParsesExact

/- The index-native parse agrees with the deployed parse on the health span. -/
#guard parseIndexNative healthSpan == Reactor.Config.h1ParseFn healthSpan.read

/-- Differing request bytes (POST) give a different parsed method. -/
def indexParseMethodDiffers : Bool :=
  match parseIndexNative healthSpan, parseIndexNative postSpan with
  | .request _ r1 _, .request _ r2 _ => r1.method != r2.method
  | _, _ => false

#guard indexParseMethodDiffers

/-- An incomplete span (no `CRLFCRLF`) is not a dispatchable request. -/
def truncNotRequest : Bool :=
  match parseIndexNative truncSpan with
  | .request .. => false
  | _ => true

#guard truncNotRequest

/- The index-native frame finds the `CRLFCRLF` at offset 20 with no list. -/
#guard spanFindDoubleCrlf (arrSpan (spanArr healthSpan)) == some 20

end SpanBytes
end Datapath
