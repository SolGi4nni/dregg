/-
  Pancake/SerializeStruct.lean — the NESTED per-header outer loop lifted to the FULL
  structured response. THE COMPOSITION ADVANCE.

  Two prior results sit either side of a gap:

   * SerializeFull.lean `serialize_structured_correct` materializes the whole
     `serialize resp` — but with the header block a SINGLE FLAT segment
     (`respSegs = [statusSeg, headerSeg, body]`, a 3-way split), written by the
     static right-nest `writeSegs`, not the per-header loop.
   * SerializeHeaders.lean `segWhile_membytes` runs the GENUINE per-header outer
     `While` (`segWhile`), landing `concatSegs segs` — but proven only for the
     header BLOCK in isolation (`header_seg_framing`), not the whole response.

  This file closes the gap: it exhibits the FULL wire response as the concatenation
  of a segment list whose HEADERS are split ONE-SEGMENT-PER-HEADER — a status-line
  segment, then the per-header `name ": " value CRLF` segments (the same `segOf` the
  header loop writes), then a final `CRLF ++ body` segment (the blank-line separator
  glued to the body) — and proves the SAME per-header outer loop `segWhile`, fed that
  segment list, lands the WHOLE `serialize resp` byte-for-byte.

  THE KEY DECOMPOSITION (`flatten_fullSegProj`, `concatSegs_fullSegs`): for ALL
  `resp`,

      serialize resp
        = concatSegs (fullSegs resp ptr)
        = (statusSeg resp)
          ++ (allHeaders (build resp)).map segOf .flatten
          ++ (CRLF ++ resp.body)

  i.e. the full structured response IS the flattening of `statusSeg :: per-header
  segOf … ++ [CRLF ++ body]`. Grounded in the deployed serializer via
  `serialize_framing` (SerializeCompile) and `header_seg_framing` (SerializeHeaders);
  the header split is the REAL per-header `segOf`, so the loop's segments are exactly
  the response's status line, each of its headers, and its body.

  THE POST-STATE (`full_response_membytes`): running the per-header outer loop
  `segWhile` from a record/source layout of `fullSegs resp ptr` lands the output
  region at `obase` equal, byte for byte, to `serialize resp`. This is
  `segWhile_membytes` (the header-loop keystone) instantiated at the FULL segment
  list, its conclusion rewritten by the decomposition — the same loop, now proven to
  materialize the entire structured response, not just the header block.

  WHY NO Div/Mod. The status line and body are carried as PRE-MATERIALIZED segment
  SOURCES (byte regions the loop copies), exactly as the per-header segments are;
  the loop is a pure segmented memcpy. Rendering the status NUMBER and the
  Content-Length as ASCII DECIMAL from scalars (`natToDec`) — which needs `Div`/`Mod`
  in the modelled expression subset — is upstream of these segment sources and is the
  standing SerializeCompile residual, UNTOUCHED here.

  This is Stack L (the Lean model of Pancake) + a memory post-state claim; the same
  word-addressed output model and residuals as SerializeHeaders / SerializeFull.
-/
import Pancake.SerializeHeaders

namespace Pancake.SerializeStruct

open Pancake Pancake.SerializeCompile Pancake.SerializeFull Pancake.SerializeHeaders

variable {σ : Type}

/-! ## 1. A pointer-tagging of a byte-segment list

`concatSegs` reads only each segment's BYTES (its `.2`); the source pointers (`.1`)
are irrelevant to the concatenation. `withPtrs` tags a plain list of byte segments
with an arbitrary per-index source pointer, threading the index, and its
`concatSegs` is exactly the flattening — the pointers wash out. -/

/-- Tag a byte-segment list with a per-index source pointer. -/
def withPtrs (ptr : Nat → Word) : List Bytes → List Seg
  | []      => []
  | b :: bs => (ptr 0, b) :: withPtrs (fun k => ptr (k + 1)) bs

/-- **`concatSegs` of a pointer-tagged list is the flattening.** The source pointers
do not affect the concatenated bytes. -/
theorem concatSegs_withPtrs (ptr : Nat → Word) (bss : List Bytes) :
    concatSegs (withPtrs ptr bss) = bss.flatten := by
  induction bss generalizing ptr with
  | nil => rfl
  | cons b bs ih =>
    show b ++ concatSegs (withPtrs (fun k => ptr (k + 1)) bs) = _
    rw [ih]; rfl

/-! ## 2. The full response as a per-header segment list

`statusSeg resp` (`= statusLineOf resp ++ CRLF`), then one `segOf` segment per header
(`name ": " value CRLF`), then `CRLF ++ resp.body` (the blank-line separator + body).
Its flattening is exactly `serialize resp`. -/

/-- The final segment: the blank-line separator glued to the body. -/
def bodySeg (resp : Response) : Bytes := crlf ++ resp.body

/-- **The full response's per-header segment BYTES**, in wire order: the status-line
segment, one `segOf` segment per header, and the `CRLF ++ body` tail. -/
def fullSegProj (resp : Response) : List Bytes :=
  (statusSeg resp :: (allHeaders (build resp)).map segOf) ++ [bodySeg resp]

/-- **THE FULL RESPONSE IS THE FLATTENED PER-HEADER SEGMENTS.** For ALL `resp`, the
flattening of the status-line segment, the per-header `segOf` segments, and the
`CRLF ++ body` tail is exactly `serialize resp`. Grounded in `serialize_framing`
(the wire framing) and `header_seg_framing` (the header block as flattened `segOf`s);
the trailing separator CRLF is absorbed into the body segment. -/
theorem flatten_fullSegProj (resp : Response) :
    (fullSegProj resp).flatten = serialize resp := by
  have hs : serialize resp
      = statusSeg resp ++ (((allHeaders (build resp)).map segOf).flatten ++ crlf) ++ resp.body := by
    rw [serialize_framing, ← header_seg_framing]
    simp only [statusSeg, headerSeg, List.append_assoc]
  rw [hs]
  simp only [fullSegProj, bodySeg, List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]

/-- **The full response segment list** (with an arbitrary per-segment source pointer
`ptr`): the status-line segment, the per-header segments, and the body segment,
tagged with sources. -/
def fullSegs (resp : Response) (ptr : Nat → Word) : List Seg :=
  withPtrs ptr (fullSegProj resp)

/-- **`concatSegs (fullSegs resp ptr) = serialize resp`.** The per-header segment
list the outer loop writes concatenates to exactly the full wire response. -/
theorem concatSegs_fullSegs (resp : Response) (ptr : Nat → Word) :
    concatSegs (fullSegs resp ptr) = serialize resp := by
  rw [fullSegs, concatSegs_withPtrs, flatten_fullSegProj]

/-! ## 3. THE COMPOSITION — the per-header outer loop lands the FULL response

`segWhile_membytes` (SerializeHeaders) runs the genuine per-header outer `While`
`segWhile` and lands `concatSegs segs`. Instantiated at `fullSegs resp ptr` and its
conclusion rewritten by `concatSegs_fullSegs`, the SAME loop lands the WHOLE
`serialize resp` — the full structured response, materialized by the per-header
loop, not the flat 3-segment static nest. The side conditions are exactly the
header loop's (a segmented memcpy's record/source layout + iteration budget), now
over the status-line + per-header + body segment list. -/
theorem full_response_membytes (o : Oracle σ) (resp : Response) (ptr recPtr : Nat → Word)
    (obase : Word)
    (hN63 : totalLen (fullSegs resp ptr) < 2 ^ 63)
    (hcount63 : (fullSegs resp ptr).length < 2 ^ 63)
    (hfit : ∀ k, k < (fullSegs resp ptr).length →
        psum (fun k => ((fullSegs resp ptr)[k]!).2.length) k
          + ((fullSegs resp ptr)[k]!).2.length ≤ totalLen (fullSegs resp ptr))
    (hOinj : ∀ p q, p < totalLen (fullSegs resp ptr) → q < totalLen (fullSegs resp ptr) →
        obase + BitVec.ofNat 64 p = obase + BitVec.ofNat 64 q → p = q)
    (hOS : ∀ k m q, k < (fullSegs resp ptr).length → m < ((fullSegs resp ptr)[k]!).2.length →
        q < totalLen (fullSegs resp ptr) →
        ((fullSegs resp ptr)[k]!).1 + BitVec.ofNat 64 m ≠ obase + BitVec.ofNat 64 q)
    (hOR : ∀ k q, k < (fullSegs resp ptr).length → q < totalLen (fullSegs resp ptr) →
        recPtr k ≠ obase + BitVec.ofNat 64 q ∧ recPtr k + w8 ≠ obase + BitVec.ofNat 64 q)
    (hstep : ∀ k, recPtr (k + 1) = recPtr k + w32)
    (s : PancakeState σ)
    (hj : s.locals "j" = some (BitVec.ofNat 64 0))
    (hcount : s.locals "count" = some (BitVec.ofNat 64 (fullSegs resp ptr).length))
    (hoff : s.locals "off" = some (BitVec.ofNat 64 0))
    (hp : s.locals "p" = some (recPtr 0))
    (hobase : s.locals "obase" = some obase)
    (hrec : ∀ k, k < (fullSegs resp ptr).length →
        s.memaddrs (recPtr k) = true ∧ s.memory (recPtr k) = ((fullSegs resp ptr)[k]!).1 ∧
        s.memaddrs (recPtr k + w8) = true ∧
        s.memory (recPtr k + w8) = BitVec.ofNat 64 ((fullSegs resp ptr)[k]!).2.length)
    (hsrc : ∀ k m, k < (fullSegs resp ptr).length → m < ((fullSegs resp ptr)[k]!).2.length →
        s.memaddrs (((fullSegs resp ptr)[k]!).1 + BitVec.ofNat 64 m) = true ∧
        s.memory (((fullSegs resp ptr)[k]!).1 + BitVec.ofNat 64 m)
          = wordOfByte (((fullSegs resp ptr)[k]!).2)[m]!)
    (hOaddr : ∀ q, q < totalLen (fullSegs resp ptr) →
        s.memaddrs (obase + BitVec.ofNat 64 q) = true)
    (hclock : (fullSegs resp ptr).length + totalLen (fullSegs resp ptr) ≤ s.clock) :
    ∃ s', PancakeSem o segWhile s = (none, s') ∧ MemBytesAt s' obase (serialize resp) := by
  obtain ⟨s', hrun, hpost⟩ :=
    segWhile_membytes o (fullSegs resp ptr) recPtr obase hN63 hcount63 hfit hOinj hOS hOR hstep
      s hj hcount hoff hp hobase hrec hsrc hOaddr hclock
  refine ⟨s', hrun, ?_⟩
  rwa [concatSegs_fullSegs resp ptr] at hpost

/-! ## 4. Non-vacuity on the real `sampleResp`

`sampleResp` is a `200 OK` with one caller header and a 2-byte body. Its per-header
decomposition is a genuine FOUR-segment split (status line, `X-A` header, derived
`Content-Length` header, `CRLF ++ body`) — one more segment than the flat 3-way
`respSegs`, the header block now split per header — and flattens to the 48 serialized
bytes. So the composition theorems' conclusions name a real, non-trivial memory
relation, not a `P → P` tautology. -/

-- FOUR segments: status line, the two headers split individually, and the body tail
-- (the flat `respSegs` had THREE — the header block was one segment; here it is two):
#guard (fullSegProj sampleResp).length = 4
#guard (respSegs sampleResp 0 0 0).length = 3
-- their per-segment byte lengths (status 17, `X-A: 1` 8, `Content-Length: 2` 19, CRLF+body 4):
#guard (fullSegProj sampleResp).map List.length = [17, 8, 19, 4]
-- the flattening is exactly the 48-byte wire response:
#guard (fullSegProj sampleResp).flatten = serialize sampleResp
#guard (fullSegProj sampleResp).flatten.length = 48
-- and via the pointer-tagged segment list the outer loop consumes:
#guard concatSegs (fullSegs sampleResp (fun _ => 0)) = serialize sampleResp
-- the middle two segments ARE the two real header lines (per-header, not one block):
#guard ((fullSegProj sampleResp).drop 1).take 2
       = [[88, 45, 65, 58, 32, 49, 13, 10],
          [67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104, 58, 32, 50, 13, 10]]

/-! ## 5. THE BODY-COPY COMPOSITION — the response memory image factors into the
    header-loop region GLUED to the body-copy region

`full_response_membytes` (§3) lands the WHOLE `serialize resp` with ONE per-header outer
loop whose final segment is `crlf ++ body`. This section FACTORS that post-state: the
wire response splits at the blank-line boundary into a HEAD block (status line + header
block + the `CRLF CRLF` separator) and the BODY, and the memory image of the whole is
exactly the memory image of the head at `obase` GLUED to the memory image of the body at
`obase + |head|`. This is the post-state algebra a two-phase serializer discharges — the
per-header nested loop writing the head region, a SEPARATE body copy (`copyWhile`)
writing the body region at the known offset — with NO `Div`/`Mod`: the head and body are
byte regions, exactly as the per-header segments are; rendering the status /
`Content-Length` decimal from scalars is the standing SerializeCompile residual, upstream
and untouched. -/

/-- **`MemBytesAt` splits over a byte-string append.** The output region at `obase`
holds `bs1 ++ bs2` iff it holds `bs1` at `obase` AND `bs2` at `obase + |bs1|` — the two
sub-regions abut at the boundary offset. (`hlen` keeps the offsets inside the word range
so the address arithmetic is exact.) -/
theorem MemBytesAt_append (s : PancakeState σ) (obase : Word) (bs1 bs2 : Bytes)
    (hlen : (bs1 ++ bs2).length < 2 ^ 64) :
    MemBytesAt s obase (bs1 ++ bs2) ↔
      MemBytesAt s obase bs1 ∧
      MemBytesAt s (obase + BitVec.ofNat 64 bs1.length) bs2 := by
  rw [List.length_append] at hlen
  constructor
  · intro H
    refine ⟨?_, ?_⟩
    · intro i hi
      have hi' : i < (bs1 ++ bs2).length := by rw [List.length_append]; omega
      rw [H i hi', bytes_append_left bs1 bs2 i hi]
    · intro j hj
      have hj' : bs1.length + j < (bs1 ++ bs2).length := by rw [List.length_append]; omega
      rw [seg_addr obase bs1.length j (by omega), H _ hj',
          bytes_append_right bs1 bs2 (bs1.length + j) (by omega),
          show bs1.length + j - bs1.length = j from by omega]
  · intro ⟨HA, HB⟩ i hi
    rw [List.length_append] at hi
    by_cases hlt : i < bs1.length
    · rw [bytes_append_left bs1 bs2 i hlt]; exact HA i hlt
    · have hle : bs1.length ≤ i := by omega
      have hj : i - bs1.length < bs2.length := by omega
      rw [bytes_append_right bs1 bs2 i hle]
      have hb := HB (i - bs1.length) hj
      rw [seg_addr obase bs1.length (i - bs1.length) (by omega),
          show bs1.length + (i - bs1.length) = i from by omega] at hb
      exact hb

/-- The HEAD block of the wire response: the status line, the header block, and the
blank-line separator (`CRLF CRLF`) — everything up to, but not including, the body. -/
def headBytes (resp : Response) : Bytes :=
  statusLineOf resp ++ crlf ++ headerBlockOf resp ++ crlf ++ crlf

/-- **`serialize resp = headBytes resp ++ resp.body`.** The wire response is the head
block glued to the body — the framing (`serialize_framing`) re-associated at the body
boundary. -/
theorem serialize_head_body (resp : Response) :
    serialize resp = headBytes resp ++ resp.body := by
  rw [serialize_framing, headBytes]

/-- **THE RESPONSE MEMORY IMAGE FACTORS AT THE BODY BOUNDARY.** For ALL `resp`, the
output region at `obase` holds `serialize resp` iff it holds the HEAD block at `obase`
AND the BODY at `obase + |head|`. The two conjuncts are precisely the post-states a
per-header nested loop (head region) and a separate body copy (body region) establish —
the composition, on the memory relation. -/
theorem full_response_body_split (s : PancakeState σ) (obase : Word) (resp : Response)
    (hlen : (serialize resp).length < 2 ^ 64) :
    MemBytesAt s obase (serialize resp) ↔
      MemBytesAt s obase (headBytes resp) ∧
      MemBytesAt s (obase + BitVec.ofNat 64 (headBytes resp).length) resp.body := by
  rw [serialize_head_body] at hlen ⊢
  exact MemBytesAt_append s obase (headBytes resp) resp.body hlen

/-- **THE GLUE (compose).** If a state holds the HEAD block at `obase` (the per-header
loop's region) AND the BODY at `obase + |head|` (a separate body copy's region), then it
holds the WHOLE `serialize resp` — the two independent region-writes compose to the full
wire response. This is the `.mpr` of the factorization: the reason a head-loop + a body
copy suffice to materialize the structured response. -/
theorem full_response_glue (s : PancakeState σ) (obase : Word) (resp : Response)
    (hlen : (serialize resp).length < 2 ^ 64)
    (hhead : MemBytesAt s obase (headBytes resp))
    (hbody : MemBytesAt s (obase + BitVec.ofNat 64 (headBytes resp).length) resp.body) :
    MemBytesAt s obase (serialize resp) :=
  (full_response_body_split s obase resp hlen).mpr ⟨hhead, hbody⟩

/-- **THE FACTORED VIEW OF A REAL LOOP RUN.** From ANY machine run of the per-header
outer loop `segWhile` that lands the full `serialize resp` (i.e. `full_response_membytes`'s
own conclusion), the SAME landed state exhibits the head block at `obase` AND the body as
a contiguous region at offset `|head|` — the post-state the composed head-loop + body-copy
would produce, now read off a genuine `segWhile` run. -/
theorem loop_run_head_and_body (o : Oracle σ) (s : PancakeState σ) (obase : Word)
    (resp : Response) (hlen : (serialize resp).length < 2 ^ 64)
    (hrun : ∃ s', PancakeSem o segWhile s = (none, s') ∧ MemBytesAt s' obase (serialize resp)) :
    ∃ s', PancakeSem o segWhile s = (none, s') ∧
      MemBytesAt s' obase (headBytes resp) ∧
      MemBytesAt s' (obase + BitVec.ofNat 64 (headBytes resp).length) resp.body := by
  obtain ⟨s', hsem, hpost⟩ := hrun
  exact ⟨s', hsem, (full_response_body_split s' obase resp hlen).mp hpost⟩

/-! ### 5.1 Non-vacuity on the real `sampleResp`

`sampleResp` serializes to 48 bytes with a 2-byte body, so the head block is a genuine
46-byte prefix and the body a 2-byte suffix at offset 46 — the factorization names a real,
non-trivial region split, not a `P → P` tautology. -/

-- the head block is 46 bytes, the body 2, and they glue to the 48-byte wire response:
#guard (headBytes sampleResp).length = 46
#guard sampleResp.body.length = 2
#guard headBytes sampleResp ++ sampleResp.body = serialize sampleResp
#guard (headBytes sampleResp).length + sampleResp.body.length = (serialize sampleResp).length
-- the head is exactly the 46-byte prefix, the body the 2-byte suffix at offset 46:
#guard headBytes sampleResp = (serialize sampleResp).take 46
#guard sampleResp.body = (serialize sampleResp).drop 46
-- and the body region genuinely starts PAST the head (offset > 0), so the split is real:
#guard (headBytes sampleResp).length > 0


/-! ## 6. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms concatSegs_withPtrs
#print axioms flatten_fullSegProj
#print axioms concatSegs_fullSegs
#print axioms full_response_membytes
#print axioms MemBytesAt_append
#print axioms serialize_head_body
#print axioms full_response_body_split
#print axioms full_response_glue
#print axioms loop_run_head_and_body

end Pancake.SerializeStruct
