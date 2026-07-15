import Reactor.Pipeline
import Proto.Decimal

/-!
# Reactor.Stage.MultiRange — RFC 9110 §14.6 `multipart/byteranges`, as a pipeline stage
(rt.6 residual — and a deployed wire-conformance BUG witness)

The deployed serve handles a SINGLE range correctly (`206` + `Content-Range`,
`StaticRangeCorrect.lean`). A MULTI-range request is where it goes WRONG on the wire:

## Ground truth — curl against the running dataplane (io_uring, port 8144, 2026-07-11)

```
$ curl -s -D - -H 'Range: bytes=0-4' http://127.0.0.1:8144/static/app.js
HTTP/1.1 206 Partial Content
Content-Range: bytes 0-4/35          ← single range: correct
Content-Length: 5

$ curl -s -D - -H 'Range: bytes=0-4,10-14' http://127.0.0.1:8144/static/app.js
HTTP/1.1 206 Partial Content
ETag: "9e983f35"
Accept-Ranges: bytes                 ← NO Content-Range, NO multipart/byteranges
Content-Length: 10

consog('dr                           ← the two slices blindly CONCATENATED
```

The deployed multi-range `206` violates RFC 9110 §14.6: a 206 with multiple ranges
MUST carry `Content-Type: multipart/byteranges; boundary=…` with per-part
`Content-Range` headers — instead it concatenates the slices with no framing at all,
so a client cannot tell where one range ends and the next begins.

This module builds the missing feature as a response-phase `Stage`: on a valid
multi-range request against a full `200`, emit a `206` whose body is a genuine
`multipart/byteranges` payload (per-part `--boundary` + `Content-Range: bytes a-b/total`
headers, terminated `--boundary--`), with the top-level `Content-Type` replaced.

## What is proved (pure-kernel; no `native_decide`, no `Lean.ofReduceBool`)

* `slice_decomposition` — for ANY body and `a ≤ b`:
  `body = body.take a ++ slice body (a,b) ++ body.drop (b+1)` — the slice is EXACTLY
  the requested byte window, in place.
* `slice_length` — an in-bounds slice has exactly `b + 1 - a` bytes.
* `multipart_carries_slice` — EVERY requested range's slice appears contiguously in
  the multipart body (for ANY body/ranges).
* `part_carries_slice` / `multipart_cons` / `multipart_part_count` — the framing
  structure: one part per range, each `partHeader ++ slice ++ CRLF`.
* `parseRanges_le` / `parseSpec_le` / `seqO_sound` — parser soundness: every parsed
  range satisfies `first ≤ last` (a syntactically invalid or inverted spec never
  produces a range).
* `validFor_mem` / `fires_valid` — the stage only fires when every range is within
  the body; combined in `transform_range_exact`: when the stage fires, EVERY
  requested range's slice sits in the emitted body and has EXACTLY the requested
  length.
* `transform_status_206` / `transform_body` / `transform_ct` — the firing branch:
  status `206`, multipart body, top-level `Content-Type: multipart/byteranges;
  boundary=…` (old Content-Type stripped, `setCt_ct_unique`).
* `transform_single_passthrough` / `transform_no_range` / `transform_non200` — the
  stage NEVER touches a single-range request (the deployed path already correct), a
  request without `Range`, or a non-`200`.
* `multiRangeStage_effect` — the stage's response phase is exactly `transform` on
  the finalized response, for ANY tail/handler (via `pipeline_stage_effect`).
* `demo_*` — non-vacuous witnesses on the REAL failing request shape
  (`bytes=0-4,10-14` — the curl above): the parse, both slices, the `206` through
  the real `runPipeline` fold, and the exact wire bytes of a part header
  (`--drorbrange␍␊Content-Range: bytes 0-4/16␍␊␍␊`, via `Proto.Dec.natToDec_eq`).

Residual (named): wire into `deployStagesFull2` + fix the deployed Rust range path +
curl the multipart framing off the running socket (dataplane rebuild deferred —
box-safety this session); `If-Range` interaction; coalescing of overlapping ranges
(RFC 9110 §14.1.2 SHOULD).
-/

namespace Reactor.Stage.MultiRange

open Reactor.Pipeline
open Proto (Bytes Request)
open Proto.Dec (dval dval_natToDec natToDec_eq natToDec_isDigit)

/-! ## Byte slicing -/

/-- The closed byte window `[r.1, r.2]` of `body` (RFC 9110 ranges are inclusive). -/
def slice (body : Bytes) (r : Nat × Nat) : Bytes :=
  (body.drop r.1).take (r.2 + 1 - r.1)

/-- **Slice exactness (position).** For ANY body and any `a ≤ b`, the body decomposes
around the slice: everything before `a`, the slice, everything after `b`. The slice
is the requested window IN PLACE — no byte moved, none invented. -/
theorem slice_decomposition (body : Bytes) (a b : Nat) (h : a ≤ b) :
    body = body.take a ++ slice body (a, b) ++ body.drop (b + 1) := by
  have h2 : (body.drop a).take (b + 1 - a) ++ (body.drop a).drop (b + 1 - a)
      = body.drop a := List.take_append_drop (b + 1 - a) (body.drop a)
  have h3 : (body.drop a).drop (b + 1 - a) = body.drop (b + 1) := by
    rw [List.drop_drop]
    congr 1
    omega
  calc body = body.take a ++ body.drop a := (List.take_append_drop a body).symm
    _ = body.take a ++ ((body.drop a).take (b + 1 - a)
          ++ (body.drop a).drop (b + 1 - a)) := by rw [h2]
    _ = body.take a ++ slice body (a, b) ++ body.drop (b + 1) := by
          rw [h3, ← List.append_assoc]
          rfl

/-- **Slice exactness (length).** An in-bounds slice has exactly `b + 1 - a` bytes. -/
theorem slice_length (body : Bytes) (r : Nat × Nat) (h1 : r.1 ≤ r.2)
    (h2 : r.2 < body.length) : (slice body r).length = r.2 + 1 - r.1 := by
  simp [slice, List.length_take, List.length_drop]
  omega

/-! ## Range-spec parsing (`bytes=a-b,c-d,…`) -/

/-- Is this byte an ASCII decimal digit? -/
def isDigitB (b : UInt8) : Bool := decide (48 ≤ b.toNat) && decide (b.toNat ≤ 57)

/-- Parse a non-empty all-digit byte string as a decimal `Nat`. -/
def parseNatB (bs : Bytes) : Option Nat :=
  if bs.isEmpty then none
  else if bs.all isDigitB then some (dval 0 bs) else none

/-- Split on `,` (0x2C). -/
def splitComma : Bytes → List Bytes
  | [] => [[]]
  | b :: t =>
    if b == 44 then [] :: splitComma t
    else
      match splitComma t with
      | h :: rt => (b :: h) :: rt
      | [] => [[b]]

/-- Parse one `first-last` spec; `none` unless both are decimal and `first ≤ last`.
(Suffix `-N` and open `N-` forms are out of scope for this stage — named residual.) -/
def parseSpec (bs : Bytes) : Option (Nat × Nat) :=
  if (bs.dropWhile isDigitB).take 1 == [45] then
    match parseNatB (bs.takeWhile isDigitB),
          parseNatB ((bs.dropWhile isDigitB).drop 1) with
    | some a, some b => if a ≤ b then some (a, b) else none
    | _, _ => none
  else none

/-- Sequence a list of optional ranges: `some` only when EVERY spec parsed. -/
def seqO : List (Option (Nat × Nat)) → Option (List (Nat × Nat))
  | [] => some []
  | none :: _ => none
  | some a :: t => (seqO t).map (a :: ·)

/-- The units token TAIL (`"ytes="` — split off so `bytesEqTok ++ rest` is
definitionally a `cons`). -/
def bytesEqTokT : Bytes := [121, 116, 101, 115, 61]

/-- The units token `"bytes="` (lowercase, ASCII). -/
def bytesEqTok : Bytes := 98 :: bytesEqTokT

/-- Is `p` a prefix of `l`? -/
def isPrefixB (p l : Bytes) : Bool := p == l.take p.length

/-- **Parse a (lowercased) `Range` value.** `bytes=a-b,c-d,…` to ranges; `none` on
any malformed or inverted spec (fail-closed: a bad spec never fires the stage). -/
def parseRanges (v : Bytes) : Option (List (Nat × Nat)) :=
  if isPrefixB bytesEqTok v then
    seqO ((splitComma (v.drop bytesEqTok.length)).map parseSpec)
  else none

/-- A parsed spec always satisfies `first ≤ last`. -/
theorem parseSpec_le (bs : Bytes) (a b : Nat) (h : parseSpec bs = some (a, b)) :
    a ≤ b := by
  unfold parseSpec at h
  split at h
  · split at h
    next a' b' _ _ =>
      split at h
      · injection h with h'
        injection h' with h1 h2
        subst h1; subst h2
        assumption
      · exact absurd h (by simp)
    next => exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Everything `seqO` returns was one of the input options. -/
theorem seqO_sound (l : List (Option (Nat × Nat))) (xs : List (Nat × Nat))
    (h : seqO l = some xs) : ∀ x ∈ xs, some x ∈ l := by
  induction l generalizing xs with
  | nil =>
    injection h with h'
    subst h'
    intro x hx
    cases hx
  | cons o t ih =>
    cases o with
    | none => exact absurd h (by simp [seqO])
    | some a =>
      cases ht : seqO t with
      | none => rw [seqO, ht] at h; exact absurd h (by simp)
      | some ys =>
        rw [seqO, ht] at h
        injection h with h'
        subst h'
        intro x hx
        cases List.mem_cons.mp hx with
        | inl he => subst he; exact List.mem_cons_self _ _
        | inr ht' => exact List.mem_cons_of_mem _ (ih ys ht x ht')

/-- **Parser soundness.** Every range `parseRanges` produces satisfies
`first ≤ last` — an inverted spec (`5-4`) can never reach the assembler. -/
theorem parseRanges_le (v : Bytes) (rs : List (Nat × Nat))
    (h : parseRanges v = some rs) : ∀ p ∈ rs, p.1 ≤ p.2 := by
  unfold parseRanges at h
  split at h
  · intro p hp
    have hm := seqO_sound _ _ h p hp
    obtain ⟨seg, _, hseg⟩ := List.mem_map.mp hm
    exact parseSpec_le seg p.1 p.2 (by rw [hseg])
  · exact absurd h (by simp)

/-! ## Multipart assembly (RFC 9110 §14.6) -/

/-- CRLF. -/
def crlf : Bytes := [13, 10]

/-- `--`. -/
def dashdash : Bytes := [45, 45]

/-- The multipart boundary token `"drorbrange"`. -/
def boundary : Bytes := [100, 114, 111, 114, 98, 114, 97, 110, 103, 101]

/-- `"Content-Range: bytes "`. -/
def crHead : Bytes :=
  [67, 111, 110, 116, 101, 110, 116, 45, 82, 97, 110, 103, 101, 58, 32, 98, 121,
   116, 101, 115, 32]

/-- One part's header block: `--boundary CRLF Content-Range: bytes a-b/total CRLF CRLF`. -/
def partHeader (total : Nat) (r : Nat × Nat) : Bytes :=
  dashdash ++ boundary ++ crlf
    ++ crHead ++ Proto.Dec.natToDec r.1 ++ [45] ++ Proto.Dec.natToDec r.2
    ++ [47] ++ Proto.Dec.natToDec total ++ crlf ++ crlf

/-- One part: header block, the slice, CRLF. -/
def part (body : Bytes) (r : Nat × Nat) : Bytes :=
  partHeader body.length r ++ slice body r ++ crlf

/-- The terminating delimiter `--boundary-- CRLF`. -/
def closer : Bytes := dashdash ++ boundary ++ dashdash ++ crlf

/-- **The multipart/byteranges payload**: one part per range, terminated. -/
def multipartBody (body : Bytes) (rs : List (Nat × Nat)) : Bytes :=
  (rs.map (part body)).flatten ++ closer

/-- A part carries its slice contiguously (header block before, CRLF after). -/
theorem part_carries_slice (body : Bytes) (r : Nat × Nat) :
    part body r = partHeader body.length r ++ slice body r ++ crlf := rfl

/-- The multipart body peels one part per range. -/
theorem multipart_cons (body : Bytes) (hd : Nat × Nat) (tl : List (Nat × Nat)) :
    multipartBody body (hd :: tl) = part body hd ++ multipartBody body tl := by
  simp [multipartBody, List.append_assoc]

/-- One part per range, exactly. -/
theorem multipart_part_count (body : Bytes) (rs : List (Nat × Nat)) :
    (rs.map (part body)).length = rs.length := List.length_map _ _

/-- **Every requested range's slice appears contiguously in the multipart body** —
for ANY body and range list. (With `slice_decomposition`/`slice_length`, the
payload carries exactly the requested windows.) -/
theorem multipart_carries_slice (body : Bytes) (rs : List (Nat × Nat))
    (r : Nat × Nat) (h : r ∈ rs) :
    ∃ pre post, multipartBody body rs = pre ++ slice body r ++ post := by
  induction rs with
  | nil => cases h
  | cons hd tl ih =>
    rw [multipart_cons]
    cases List.mem_cons.mp h with
    | inl he =>
      subst he
      refine ⟨partHeader body.length r, crlf ++ multipartBody body tl, ?_⟩
      simp [part, List.append_assoc]
    | inr ht =>
      obtain ⟨pre, post, he⟩ := ih ht
      refine ⟨part body hd ++ pre, post, ?_⟩
      rw [he]
      simp [List.append_assoc]

/-! ## The stage -/

/-- ASCII-lowercase one byte. -/
def lowerByte (b : UInt8) : UInt8 := if 65 ≤ b && b ≤ 90 then b + 32 else b

/-- ASCII-lowercase a byte string. -/
def lower (bs : Bytes) : Bytes := bs.map lowerByte

/-- Lowercase field-name token `"range"`. -/
def rangeTok : Bytes := [114, 97, 110, 103, 101]

/-- Lowercase field-name token `"content-type"`. -/
def ctTok : Bytes := [99, 111, 110, 116, 101, 110, 116, 45, 116, 121, 112, 101]

/-- The emitted field name `"Content-Type"`. -/
def ctName : Bytes := [67, 111, 110, 116, 101, 110, 116, 45, 84, 121, 112, 101]

/-- The emitted value `"multipart/byteranges; boundary=drorbrange"`. -/
def mpCtVal : Bytes :=
  [109, 117, 108, 116, 105, 112, 97, 114, 116, 47, 98, 121, 116, 101, 114, 97,
   110, 103, 101, 115, 59, 32, 98, 111, 117, 110, 100, 97, 114, 121, 61]
    ++ boundary

/-- Is this field name `Content-Type` (case-insensitive)? -/
def isCt (name : Bytes) : Bool := lower name == ctTok

/-- Replace the top-level `Content-Type` with the multipart one (strip any old,
append the new — a 206 multipart's top-level type is the framing's, RFC 9110 §14.6). -/
def setCt (hs : List (Bytes × Bytes)) : List (Bytes × Bytes) :=
  hs.filter (fun nv => !(isCt nv.1)) ++ [(ctName, mpCtVal)]

/-- After `setCt`, the ONLY `Content-Type` is the multipart one. -/
theorem setCt_ct_unique (hs : List (Bytes × Bytes)) :
    ∀ nv ∈ setCt hs, isCt nv.1 = true → nv = (ctName, mpCtVal) := by
  intro nv hmem hct
  unfold setCt at hmem
  cases List.mem_append.mp hmem with
  | inl hf =>
    have := (List.mem_filter.mp hf).2
    rw [hct] at this
    exact absurd this (by decide)
  | inr hs' =>
    cases List.mem_cons.mp hs' with
    | inl he => exact he
    | inr h0 => cases h0

/-- The multipart `Content-Type` is present after `setCt` (its name matches the
detector — kernel-decided — and it is appended last). -/
theorem setCt_has (hs : List (Bytes × Bytes)) :
    (setCt hs).any (fun nv => isCt nv.1) = true := by
  unfold setCt
  rw [List.any_append]
  have hlast : List.any [(ctName, mpCtVal)] (fun nv => isCt nv.1) = true := by decide
  rw [hlast, Bool.or_true]

/-- The request's `Range` value, if any (case-insensitive name). -/
def rangeValOf (req : Request) : Option Bytes :=
  match req.headers.find? (fun nv => lower nv.1 == rangeTok) with
  | some nv => some nv.2
  | none => none

/-- The parsed ranges of the request (value lowercased: `BYTES=` accepted;
digits/`-`/`,` are fixed points of lowercasing). -/
def rangesOf (req : Request) : Option (List (Nat × Nat)) :=
  match rangeValOf req with
  | some v => parseRanges (lower v)
  | none => none

/-- Every range fits the body (`last < total`; `first ≤ last` from the parser). -/
def validFor (total : Nat) (rs : List (Nat × Nat)) : Bool :=
  rs.all (fun r => decide (r.2 < total))

/-- A member of a valid range list is in bounds. -/
theorem validFor_mem (total : Nat) (rs : List (Nat × Nat)) (r : Nat × Nat)
    (hv : validFor total rs = true) (hm : r ∈ rs) : r.2 < total :=
  of_decide_eq_true (List.all_eq_true.mp hv r hm)

/-- Does the stage fire? MULTI-range (≥ 2 — the deployed single-range path is
already correct and untouched), on a full `200`, all ranges in bounds. -/
def fires (rs : List (Nat × Nat)) (r : Response) : Bool :=
  decide (2 ≤ rs.length) && (r.status == 200) && validFor r.body.length rs

/-- A firing condition certifies all ranges in bounds. -/
theorem fires_valid (rs : List (Nat × Nat)) (r : Response)
    (h : fires rs r = true) : validFor r.body.length rs = true := by
  unfold fires at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.2

/-- The response transform: on a parsed multi-range against a full `200`, emit the
RFC 9110 §14.6 `206`; otherwise pass through untouched. -/
def transform (req : Request) (r : Response) : Response :=
  match rangesOf req with
  | some rs =>
    if fires rs r then
      { status := 206,
        reason := [80, 97, 114, 116, 105, 97, 108, 32, 67, 111, 110, 116, 101,
                   110, 116],
        headers := setCt r.headers,
        body := multipartBody r.body rs }
    else r
  | none => r

/-- The transform on a parsed range list, unfolded (the match reduced). -/
theorem transform_some (req : Request) (r : Response) (rs : List (Nat × Nat))
    (hr : rangesOf req = some rs) :
    transform req r
      = if fires rs r then
          { status := 206,
            reason := [80, 97, 114, 116, 105, 97, 108, 32, 67, 111, 110, 116,
                       101, 110, 116],
            headers := setCt r.headers,
            body := multipartBody r.body rs }
        else r := by
  unfold transform
  rw [hr]

/-- The firing branch answers `206`. -/
theorem transform_status_206 (req : Request) (r : Response) (rs : List (Nat × Nat))
    (hr : rangesOf req = some rs) (hc : fires rs r = true) :
    (transform req r).status = 206 := by
  rw [transform_some req r rs hr, if_pos hc]

/-- The firing branch's body is the multipart payload of the parsed ranges. -/
theorem transform_body (req : Request) (r : Response) (rs : List (Nat × Nat))
    (hr : rangesOf req = some rs) (hc : fires rs r = true) :
    (transform req r).body = multipartBody r.body rs := by
  rw [transform_some req r rs hr, if_pos hc]

/-- The firing branch's headers carry the multipart `Content-Type` (uniquely —
`setCt_ct_unique`). -/
theorem transform_ct (req : Request) (r : Response) (rs : List (Nat × Nat))
    (hr : rangesOf req = some rs) (hc : fires rs r = true) :
    (transform req r).headers = setCt r.headers := by
  rw [transform_some req r rs hr, if_pos hc]

/-- **The exactness composition.** When the stage fires, EVERY parsed range's slice
sits contiguously in the emitted body, and (with `first ≤ last`, which
`parseRanges_le` supplies for every parsed range) it has EXACTLY the requested
`last + 1 - first` bytes. -/
theorem transform_range_exact (req : Request) (r : Response)
    (rs : List (Nat × Nat)) (p : Nat × Nat)
    (hr : rangesOf req = some rs) (hc : fires rs r = true) (hp : p ∈ rs)
    (hle : p.1 ≤ p.2) :
    (∃ pre post, (transform req r).body = pre ++ slice r.body p ++ post)
      ∧ (slice r.body p).length = p.2 + 1 - p.1 := by
  constructor
  · rw [transform_body req r rs hr hc]
    exact multipart_carries_slice r.body rs p hp
  · exact slice_length r.body p hle (validFor_mem _ rs p (fires_valid rs r hc) hp)

/-- **Single-range passthrough.** One range never fires the stage — the deployed
single-range `206 + Content-Range` path stays exactly as it is. -/
theorem transform_single_passthrough (req : Request) (r : Response)
    (rs : List (Nat × Nat)) (hr : rangesOf req = some rs) (hlen : rs.length = 1) :
    transform req r = r := by
  have hc : fires rs r = false := by
    unfold fires
    rw [hlen]
    rfl
  rw [transform_some req r rs hr, hc]
  rfl

/-- No `Range` (or a malformed one): pass through. -/
theorem transform_no_range (req : Request) (r : Response)
    (hr : rangesOf req = none) : transform req r = r := by
  unfold transform; rw [hr]

/-- A non-`200` (already partial, redirect, error) is never rewritten. -/
theorem transform_non200 (req : Request) (r : Response)
    (h : (r.status == 200) = false) : transform req r = r := by
  cases hr : rangesOf req with
  | none => exact transform_no_range req r hr
  | some rs =>
    have hc : fires rs r = false := by
      unfold fires
      rw [h, Bool.and_false, Bool.false_and]
    rw [transform_some req r rs hr, hc]
    rfl

/-- **The multi-range stage.** Request phase: pass through. Response phase:
`transform` on the finalized response (one affine `mapResp`). Never gates. -/
def multiRangeStage : Stage where
  name := "multi-range"
  onRequest := fun c => .continue c
  onResponse := fun c b => b.mapResp (transform c.req)

/-- **The byte-effect.** The stage's response phase is exactly `transform` on the
finalized response, for ANY tail and handler. -/
theorem multiRangeStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    (runPipeline (multiRangeStage :: rest) h c).build
      = transform c.req ((runPipeline rest h c).build) := by
  rw [pipeline_stage_effect multiRangeStage rest h c c rfl]
  rfl

/-! ## End-to-end witnesses (non-vacuous — the REAL failing request shape) -/

/-- A 16-byte body `"0123456789abcdef"`. -/
def demoBody : Bytes :=
  [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 97, 98, 99, 100, 101, 102]

/-- The curl request's header value: `"bytes=0-4,10-14"`. -/
def demoRangeVal : Bytes :=
  [98, 121, 116, 101, 115, 61, 48, 45, 52, 44, 49, 48, 45, 49, 52]

/-- A `GET / HTTP/1.1` carrying exactly that `Range`. -/
def demoReq : Request :=
  { method := [71, 69, 84], target := [47],
    version := [72, 84, 84, 80, 47, 49, 46, 49],
    headers := [([82, 97, 110, 103, 101], demoRangeVal)] }

/-- The demo context. -/
def demoCtx : Ctx := { input := [], req := demoReq, attrs := [] }

/-- A full `200` for the 16-byte body, `Content-Type: txt`. -/
def demoHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [],
             headers := [(ctName, [116, 120, 116])], body := demoBody }

/-- **The parse.** The curl request's exact bytes parse to the two ranges. -/
theorem demo_parses : rangesOf demoReq = some [(0, 4), (10, 14)] := by decide

/-- **The slices.** The two windows are the real bytes (`"01234"`, `"abcde"`). -/
theorem demo_slices :
    slice demoBody (0, 4) = [48, 49, 50, 51, 52]
      ∧ slice demoBody (10, 14) = [97, 98, 99, 100, 101] := by decide

/-- **End-to-end status.** Through the real `runPipeline` fold, the multi-range
request against the full `200` is answered `206`. -/
theorem demo_status :
    ((runPipeline [multiRangeStage] demoHandler demoCtx).build).status = 206 := by
  decide

/-- **End-to-end body.** The served body IS the multipart payload of the two
parsed ranges. -/
theorem demo_body :
    ((runPipeline [multiRangeStage] demoHandler demoCtx).build).body
      = multipartBody demoBody [(0, 4), (10, 14)] := rfl

/-- **End-to-end Content-Type.** The old `txt` is stripped; the multipart type is
the one Content-Type served. -/
theorem demo_ct :
    ((runPipeline [multiRangeStage] demoHandler demoCtx).build).headers
      = [(ctName, mpCtVal)] := by decide

/-- **The wire bytes of a part header** (`--drorbrange␍␊Content-Range: bytes
0-4/16␍␊␍␊`) — the serializer's real decimal rendering, pinned byte-for-byte via
`Proto.Dec.natToDec_eq`. -/
theorem demo_part_header_wire :
    partHeader 16 (0, 4)
      = [45, 45, 100, 114, 111, 114, 98, 114, 97, 110, 103, 101, 13, 10, 67, 111,
         110, 116, 101, 110, 116, 45, 82, 97, 110, 103, 101, 58, 32, 98, 121, 116,
         101, 115, 32, 48, 45, 52, 47, 49, 54, 13, 10, 13, 10] := by
  simp only [partHeader, natToDec_eq]
  rfl

/-- The terminating delimiter's wire bytes (`--drorbrange--␍␊`). -/
theorem demo_closer_wire :
    closer = [45, 45, 100, 114, 111, 114, 98, 114, 97, 110, 103, 101, 45, 45, 13,
              10] := rfl

/-- **Single-range stays deployed-correct.** `bytes=0-4` alone never fires this
stage (through the parse, non-vacuously). -/
theorem demo_single_passthrough (r : Response) :
    transform { demoReq with
                headers := [([82, 97, 110, 103, 101],
                             [98, 121, 116, 101, 115, 61, 48, 45, 52])] } r = r := by
  apply transform_single_passthrough _ _ [(0, 4)]
  · decide
  · rfl

#print axioms Reactor.Stage.MultiRange.slice_decomposition
#print axioms Reactor.Stage.MultiRange.slice_length
#print axioms Reactor.Stage.MultiRange.parseSpec_le
#print axioms Reactor.Stage.MultiRange.seqO_sound
#print axioms Reactor.Stage.MultiRange.parseRanges_le
#print axioms Reactor.Stage.MultiRange.multipart_cons
#print axioms Reactor.Stage.MultiRange.multipart_carries_slice
#print axioms Reactor.Stage.MultiRange.setCt_ct_unique
#print axioms Reactor.Stage.MultiRange.validFor_mem
#print axioms Reactor.Stage.MultiRange.transform_status_206
#print axioms Reactor.Stage.MultiRange.transform_body
#print axioms Reactor.Stage.MultiRange.transform_range_exact
#print axioms Reactor.Stage.MultiRange.transform_single_passthrough
#print axioms Reactor.Stage.MultiRange.transform_non200
#print axioms Reactor.Stage.MultiRange.multiRangeStage_effect
#print axioms Reactor.Stage.MultiRange.demo_parses
#print axioms Reactor.Stage.MultiRange.demo_status
#print axioms Reactor.Stage.MultiRange.demo_body
#print axioms Reactor.Stage.MultiRange.demo_ct
#print axioms Reactor.Stage.MultiRange.demo_part_header_wire

end Reactor.Stage.MultiRange
