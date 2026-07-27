/-
Route.StaticDecide — the static lane's FULL response decision, in the core.

`Route.StaticResolve` moved the PATH decision across the host boundary and
`Route.StaticHead` the plain-`200`/`404` head decision. The differential
harness (`conformance/differential/`) then mapped what the static lane still
did NOT decide, against a stock reference server: no `Range` handling (a
whole-body `200` while advertising `Accept-Ranges: bytes`), no conditional
GET (`If-None-Match` / `If-Modified-Since` never earn a `304`), and no `405`
for methods a static file cannot support. This module closes those gaps as
ONE core decision. The exported `drorb_static_decide` takes the host's
boundary facts — found, byte length, mtime, the real (post-canonicalize)
file name, the client's keep-alive intent — plus the RAW request bytes, and
returns the complete serving PLAN:

  * `.reply r`            — write `r` verbatim (the batch-small responses:
                            `301` directory redirect, `304`, `405`, `416`,
                            `404`, and every `HEAD`);
  * `.whole head`         — write `head`, then stream the whole file;
  * `.window off n head`  — `206`: write `head`, then stream the file bytes
                            `[off, off+n)`;
  * `.parts head segs tl` — `206 multipart/byteranges`: write `head`, then
                            for each `(pre, off, n)` in `segs` write `pre`
                            followed by the file bytes `[off, off+n)`, then
                            write `tl`.

The host executes the plan; it decides nothing — not the status, not one
header byte, not a single window bound.

## Reuse (proven stages composed, not mirrored)

  * `Reactor.Stage.ConditionalRequest` — `ifNoneMatchMatches` (the RFC 7232
    precondition matcher the deployed cache revalidation already crosses) IS
    this module's `If-None-Match` decision, applied to the parsed request.
    `stage_bridge_304` / `cond_fires_iff_stage` tie the `304` decision to
    `conditionalRewrite` on a candidate `200`: this lane goes `304` exactly
    when the proven finisher stage would rewrite that `200` to `304`.
  * `Reactor.Stage.MultiRange` — `slice` grounds every streamed window
    (`window_exact` + `slice_length` / `slice_decomposition`: the window is
    the requested byte range, in place, exactly); the multipart framing
    (`partHeader` / `closer` / `boundary`) IS the emitted framing:
    `partsWire_eq_multipartBody` proves the plan's preface/window/tail
    emission reassembles to EXACTLY `multipartBody`, so
    `multipart_carries_slice` speaks about this wire.
  * `Route.StaticHead` — `extOf` / `ctypeFor` (the proven MIME decision) and
    the `Proto.Dec` decimal grounding: every framed number (`Content-Length`,
    `Content-Range`) round-trips (`adec_roundtrip` = `dval_natToDec`).

## What is proven (headline)

  * `plan_405` / `plan_404` / `plan_404_head` / `plan_301` / `plan_304` /
    `plan_whole` / `plan_416` / `plan_single` / `plan_multi` — the decision
    arms, as equations on `plan`.
  * `stage_bridge_304` — `conditionalRewrite` on a candidate `200` goes
    `304` iff `ifNoneMatchMatches`; `cond_fires_iff_stage` lifts it to this
    module's guard. `cond_ims_exact` — the `If-Modified-Since` arm is the
    exact-date compare (fires iff the sent date equals the representation's
    `Last-Modified` bytes; the safe direction — a non-equal date re-serves).
  * `resolveSpec_sound` / `resolved_inbounds` — every resolved range
    satisfies `a ≤ b < len`, for all of `a-b` / `a-` / `-n`.
  * `window_exact` — a single-range decision's streamed window IS
    `Reactor.Stage.MultiRange.slice` of the body: exact length, in place, in bounds.
  * `head206_cl` / `resp416_content_range` — the `206` head carries
    `Content-Range: bytes a-b/total` with a `Content-Length` whose digits
    parse back to the exact streamed count (∀ values, via `dval_natToDec`);
    the `416` carries the `bytes */total` form.
  * `partsWire_eq_multipartBody` + `multiLen_exact` (packaged as
    `parts_exact`) — the multipart plan's wire = `Reactor.Stage.MultiRange.multipartBody`
    exactly, and the framed `Content-Length` counts it exactly.
  * `notFound_split` — the `404` is the MODEL's `notFoundResp` verbatim
    (`HEAD` writes its head half, byte-split proven).
  * End-to-end witnesses on the differential corpus's exact request bytes
    (`demo_*` — kernel-decided, no `native_decide`): single/suffix/open/
    unsatisfiable/multi ranges, foreign unit, `If-None-Match: *`, non-match,
    exact/past `If-Modified-Since`, `POST`/`PUT` ⇒ `405`, `HEAD`, `404`.

Residual (named): `If-Range` is not evaluated (a conditional range request
streams the full range set — safe, never stale); range handling applies to
`GET` only (RFC 9110 §14.2 defines range handling for `GET`; a `HEAD` with
`Range` gets the plain `200` head); `If-Modified-Since` compares the
HTTP-date BYTES (exact semantics — an equivalent rfc850/asctime date
re-serves the body, the safe direction); overlapping ranges are not
coalesced (each requested range is emitted as sent); the multipart boundary
token is this server's own; the `301` directory redirect carries a RELATIVE
`Location` (the request target plus `/`); a directory requested WITH its
trailing slash is served by the host resolving its `index.html` (a directory
with no `index.html` is a `404`, the host reporting `found = false`).
-/

import Route.StaticHead
import Reactor.Stage.ConditionalRequest
import Reactor.Stage.MultiRange

namespace Route.StaticDecide

open Route.StaticServe (strBytes crlf statusLine200 statusLine404 connHeader
  acceptRanges ctBlock clBlock decimal okHead notFoundResp)
open Route.StaticHead (ascii ascii_eq_strBytes flatMap_utf8_ascii extOf ctypeFor beNat)
open Reactor.Stage.FramingValidation (isOWS lowerBytes trimOWS)
open Reactor.Stage.ConditionalRequest (headerVal tagMatches condTags
  ifNoneMatchMatches ifMatchFails etagNameLower ifNoneMatchNameLower
  conditionalRewrite respETag notModifiedOf)

/-- Raw bytes. -/
abbrev Bytes := List UInt8

/-! ## Kernel-computable renderings (bridged to the model's) -/

/-- Decimal rendering, kernel-computable (`Nat.toDigits` char map — unlike
`decimal` = `Nat.repr`/`toUTF8`, which the kernel will not reduce), so the
corpus witnesses below evaluate under `decide`. Bridged by `adec_eq_decimal`. -/
def adec (n : Nat) : Bytes := (Nat.toDigits 10 n).map (fun c => UInt8.ofNat c.toNat)

/-- Every digit char is ASCII. -/
theorem digitChar_ascii : ∀ r, r < 10 → (Nat.digitChar r).val ≤ 0x7f := by decide

/-- **`adec` = the model's `decimal`** (definitionally `Proto.Dec.natToDec`),
for every `n`. -/
theorem adec_eq_decimal (n : Nat) : adec n = decimal n := by
  show adec n = Proto.Dec.natToDec n
  rw [Proto.Dec.natToDec_eq,
      flatMap_utf8_ascii _ (fun c hc => by
        obtain ⟨r, hr, rfl⟩ := Proto.Dec.mem_toDigits_isDigit n c hc
        exact digitChar_ascii r hr)]
  rfl

/-- **∀ n**: the digits `adec` frames parse back to exactly `n` — the framed
`Content-Length` / `Content-Range` numbers are EXACT. -/
theorem adec_roundtrip (n : Nat) : Proto.Dec.dval 0 (adec n) = n := by
  rw [adec_eq_decimal]; exact Proto.Dec.dval_natToDec n

/-- Lowercase-hex rendering (kernel-computable) — the entity-tag digits. -/
def ahex (n : Nat) : Bytes := (Nat.toDigits 16 n).map (fun c => UInt8.ofNat c.toNat)

/-! ## The entity tag and `Last-Modified` (the representation validators) -/

/-- The strong entity tag for a static file: `"hex(mtime)-hex(len)"`, quoted.
Deterministic in the two boundary facts the host reports (length, mtime), so
one representation has one tag. -/
def etagVal (len mtime : Nat) : Bytes :=
  34 :: ((ahex mtime ++ [45] ++ ahex len) ++ [34])

/-- ASCII zero-padded two-digit rendering (`5` ↦ `05`). -/
def two (n : Nat) : Bytes :=
  [UInt8.ofNat (48 + n / 10 % 10), UInt8.ofNat (48 + n % 10)]

/-- Four-digit year rendering. -/
def four (n : Nat) : Bytes := two (n / 100) ++ two (n % 100)

/-- IMF-fixdate weekday names (`0` = Sunday; 1970-01-01 was a Thursday). -/
def wkday : Nat → Bytes
  | 0 => ascii "Sun" | 1 => ascii "Mon" | 2 => ascii "Tue" | 3 => ascii "Wed"
  | 4 => ascii "Thu" | 5 => ascii "Fri" | _ => ascii "Sat"

/-- IMF-fixdate month names (`1`-based). -/
def mon : Nat → Bytes
  | 1 => ascii "Jan" | 2 => ascii "Feb" | 3 => ascii "Mar" | 4 => ascii "Apr"
  | 5 => ascii "May" | 6 => ascii "Jun" | 7 => ascii "Jul" | 8 => ascii "Aug"
  | 9 => ascii "Sep" | 10 => ascii "Oct" | 11 => ascii "Nov" | _ => ascii "Dec"

/-- Civil date from days since 1970-01-01 (proleptic Gregorian; the era
decomposition over the 146097-day 400-year cycle). Returns `(y, m, d)`. -/
def civil (days : Nat) : Nat × Nat × Nat :=
  let z := days + 719468
  let era := z / 146097
  let doe := z % 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (if m ≤ 2 then y + 1 else y, m, d)

/-- The RFC 9110 IMF-fixdate rendering of a Unix time (seconds):
`Www, DD Mmm YYYY HH:MM:SS GMT`. Kernel-computable. -/
def httpDate (secs : Nat) : Bytes :=
  let days := secs / 86400
  let rem := secs % 86400
  let (y, m, d) := civil days
  wkday ((days + 4) % 7) ++ ascii ", " ++ two d ++ [32] ++ mon m ++ [32]
    ++ four y ++ [32] ++ two (rem / 3600) ++ [58] ++ two (rem % 3600 / 60)
    ++ [58] ++ two (rem % 60) ++ ascii " GMT"

/-- The epoch renders to the canonical fixdate. -/
theorem httpDate_epoch : httpDate 0 = ascii "Thu, 01 Jan 1970 00:00:00 GMT" := by decide

/-- The differential site's pinned mtime (2026-01-02 03:04:05 UTC) renders to
the reference server's exact `Last-Modified` bytes. -/
theorem httpDate_site :
    httpDate 1767323045 = ascii "Fri, 02 Jan 2026 03:04:05 GMT" := by decide

/-! ## Header blocks (kernel-computable, bridged to the model blocks) -/

/-- CRLF. -/
def acrlf : Bytes := [13, 10]

theorem acrlf_eq : acrlf = crlf := by
  rw [show acrlf = ascii "\r\n" from by decide]; exact ascii_eq_strBytes _ (by decide)

/-- The `Connection` header (the client's keep-alive intent). -/
def aConn (ka : Bool) : Bytes :=
  if ka then ascii "Connection: keep-alive\r\n" else ascii "Connection: close\r\n"

theorem aConn_eq (ka : Bool) : aConn ka = connHeader ka := by
  cases ka <;> exact ascii_eq_strBytes _ (by decide)

/-- `Accept-Ranges: bytes` (advertised on the full `200` only — a `206` does
not re-advertise). -/
def aAccept : Bytes := ascii "Accept-Ranges: bytes\r\n"

theorem aAccept_eq : aAccept = acceptRanges := ascii_eq_strBytes _ (by decide)

/-- The `Content-Type` header line. -/
def actBlock (ct : Bytes) : Bytes := ascii "Content-Type: " ++ ct ++ acrlf

theorem actBlock_eq (ct : Bytes) : actBlock ct = ctBlock ct := by
  unfold actBlock ctBlock
  rw [ascii_eq_strBytes "Content-Type: " (by decide), acrlf_eq]

/-- The `Content-Length` header line. -/
def aclBlock (n : Nat) : Bytes := ascii "Content-Length: " ++ adec n ++ acrlf

theorem aclBlock_eq (n : Nat) : aclBlock n = clBlock n := by
  unfold aclBlock clBlock
  rw [ascii_eq_strBytes "Content-Length: " (by decide), acrlf_eq, adec_eq_decimal]

/-- The `ETag` header line (`e` is the full quoted tag). -/
def etagBlock (e : Bytes) : Bytes := ascii "ETag: " ++ e ++ acrlf

/-- The `Last-Modified` header line (`t` is the rendered fixdate). -/
def lmBlock (t : Bytes) : Bytes := ascii "Last-Modified: " ++ t ++ acrlf

/-- `Content-Range: bytes a-b/total`. Same rendering the proven multipart
part header carries (`contentRange_eq_partHeader_line`). -/
def contentRange (a b total : Nat) : Bytes :=
  ascii "Content-Range: bytes " ++ adec a ++ [45] ++ adec b ++ [47]
    ++ adec total ++ acrlf

/-- The top-level `Content-Range` rendering is byte-identical to the line the
PROVEN multipart part header frames (`Reactor.Stage.MultiRange.crHead` + `natToDec`s). -/
theorem contentRange_eq_partHeader_line (a b total : Nat) :
    contentRange a b total
      = Reactor.Stage.MultiRange.crHead ++ Proto.Dec.natToDec a ++ [45] ++ Proto.Dec.natToDec b
          ++ [47] ++ Proto.Dec.natToDec total ++ [13, 10] := by
  unfold contentRange
  rw [show ascii "Content-Range: bytes " = Reactor.Stage.MultiRange.crHead from by decide,
      show (adec a : Bytes) = Proto.Dec.natToDec a from adec_eq_decimal a,
      show (adec b : Bytes) = Proto.Dec.natToDec b from adec_eq_decimal b,
      show (adec total : Bytes) = Proto.Dec.natToDec total from adec_eq_decimal total]
  rfl

/-- `Content-Range: bytes */total` — the `416` form. -/
def contentRangeStar (total : Nat) : Bytes :=
  ascii "Content-Range: bytes */" ++ adec total ++ acrlf

/-! ## Status lines -/

def aStatus200 : Bytes := ascii "HTTP/1.1 200 OK\r\n"
def aStatus206 : Bytes := ascii "HTTP/1.1 206 Partial Content\r\n"
def aStatus301 : Bytes := ascii "HTTP/1.1 301 Moved Permanently\r\n"
def aStatus304 : Bytes := ascii "HTTP/1.1 304 Not Modified\r\n"
def aStatus405 : Bytes := ascii "HTTP/1.1 405 Method Not Allowed\r\n"
def aStatus416 : Bytes := ascii "HTTP/1.1 416 Range Not Satisfiable\r\n"

theorem aStatus200_eq : aStatus200 = statusLine200 := ascii_eq_strBytes _ (by decide)

/-! ## Response heads and batch-small responses -/

/-- **The validated `200` head**: the model's `okHead` layout with the two
representation validators (`ETag`, `Last-Modified`) inserted after
`Accept-Ranges` (`okHead2_eq_model_plus`). -/
def okHead2 (ct : Bytes) (len : Nat) (etag lm : Bytes) (ka : Bool) : Bytes :=
  aStatus200 ++ aConn ka ++ aAccept ++ etagBlock etag ++ lmBlock lm
    ++ actBlock ct ++ aclBlock len ++ acrlf

/-- Deployed `200` head = the MODEL's blocks with exactly the two validator
lines added — drift from `okHead`'s layout would break this build. -/
theorem okHead2_eq_model_plus (ct : Bytes) (len : Nat) (etag lm : Bytes) (ka : Bool) :
    okHead2 ct len etag lm ka
      = statusLine200 ++ connHeader ka ++ acceptRanges
          ++ (etagBlock etag ++ lmBlock lm)
          ++ ctBlock ct ++ clBlock len ++ crlf := by
  unfold okHead2
  rw [aStatus200_eq, aConn_eq, aAccept_eq, actBlock_eq, aclBlock_eq, acrlf_eq]
  simp [List.append_assoc]

/-- **The single-range `206` head**: status, `Connection`, validators,
`Content-Range: bytes a-b/total`, the file's `Content-Type`, and a
`Content-Length` of exactly the window (`b + 1 - a`). No `Accept-Ranges`
re-advertisement. -/
def head206 (ct : Bytes) (a b total : Nat) (etag lm : Bytes) (ka : Bool) : Bytes :=
  aStatus206 ++ aConn ka ++ etagBlock etag ++ lmBlock lm
    ++ contentRange a b total ++ actBlock ct ++ aclBlock (b + 1 - a) ++ acrlf

/-- The `206` head carries the `Content-Range` line, and its `Content-Length`
digits parse back to EXACTLY the streamed window size — ∀ bounds. -/
theorem head206_cl (ct : Bytes) (a b total : Nat) (etag lm : Bytes) (ka : Bool) :
    (contentRange a b total <:+: head206 ct a b total etag lm ka)
    ∧ Proto.Dec.dval 0 (adec (b + 1 - a)) = b + 1 - a := by
  refine ⟨⟨aStatus206 ++ aConn ka ++ etagBlock etag ++ lmBlock lm,
          actBlock ct ++ aclBlock (b + 1 - a) ++ acrlf, ?_⟩,
         adec_roundtrip (b + 1 - a)⟩
  simp [head206, List.append_assoc]

/-! ## The multipart plan pieces (reusing the PROVEN `MultiRange` framing) -/

/-- The multipart `Content-Type` value, carrying the proven stage's boundary
token. -/
def multiCT : Bytes := ascii "multipart/byteranges; boundary=" ++ Reactor.Stage.MultiRange.boundary

/-- Per-part prefaces: the FIRST part's preface is its `partHeader`; every
later preface carries the previous part's terminating CRLF first, so that
`preface ++ window` concatenation reassembles `part` exactly
(`partsWire_eq_multipartBody`). Each entry is `(preface, first, last)`. -/
def prefaces (total : Nat) : List (Nat × Nat) → List (Bytes × Nat × Nat)
  | [] => []
  | r :: rs =>
      (Reactor.Stage.MultiRange.partHeader total r, r.1, r.2)
        :: rs.map (fun r' => (Reactor.Stage.MultiRange.crlf ++ Reactor.Stage.MultiRange.partHeader total r', r'.1, r'.2))

/-- The tail after the last window: the last part's CRLF, then the proven
closing delimiter. -/
def multiCloser : Bytes := Reactor.Stage.MultiRange.crlf ++ Reactor.Stage.MultiRange.closer

/-- The multipart body's exact byte count, from the framing and the (in-bounds)
window sizes. This is the number the `206` head frames as `Content-Length`. -/
def multiLen (total : Nat) (rs : List (Nat × Nat)) : Nat :=
  (rs.map (fun r => (Reactor.Stage.MultiRange.partHeader total r).length + (r.2 + 1 - r.1) + 2)).sum
    + Reactor.Stage.MultiRange.closer.length

/-- **The multipart `206` head.** -/
def head206multi (total : Nat) (rs : List (Nat × Nat)) (etag lm : Bytes) (ka : Bool) : Bytes :=
  aStatus206 ++ aConn ka ++ etagBlock etag ++ lmBlock lm
    ++ actBlock multiCT ++ aclBlock (multiLen total rs) ++ acrlf

/-- What the host's execution of a `.parts` plan puts on the wire AFTER the
head: each preface, then its file window, then the tail. -/
def partsWire (body : Bytes) (segs : List (Bytes × Nat × Nat)) (tail : Bytes) : Bytes :=
  (segs.map (fun s => s.1 ++ (body.drop s.2.1).take (s.2.2 + 1 - s.2.1))).flatten ++ tail

/-- A streamed window IS the proven stage's `slice` — definitionally. -/
theorem window_is_slice (body : Bytes) (r : Nat × Nat) :
    (body.drop r.1).take (r.2 + 1 - r.1) = Reactor.Stage.MultiRange.slice body r := rfl

/-- Tail helper: the CRLF-carrying prefaces plus the closing tail reassemble
to CRLF followed by the PROVEN `multipartBody`. -/
theorem parts_tail_eq (body : Bytes) (rest : List (Nat × Nat)) :
    (rest.map (fun r' =>
        (Reactor.Stage.MultiRange.crlf ++ Reactor.Stage.MultiRange.partHeader body.length r')
          ++ (body.drop r'.1).take (r'.2 + 1 - r'.1))).flatten
      ++ (Reactor.Stage.MultiRange.crlf ++ Reactor.Stage.MultiRange.closer)
    = Reactor.Stage.MultiRange.crlf ++ Reactor.Stage.MultiRange.multipartBody body rest := by
  induction rest with
  | nil => simp [Reactor.Stage.MultiRange.multipartBody]
  | cons r t ih =>
      simp only [List.map_cons, List.flatten_cons, List.append_assoc] at ih ⊢
      rw [ih, Reactor.Stage.MultiRange.multipart_cons, Reactor.Stage.MultiRange.part_carries_slice,
          window_is_slice]
      simp [List.append_assoc]

/-- **The multipart wire is EXACTLY the proven `multipartBody`.** The plan's
preface/window/tail emission — what the host writes — reassembles to the
`Reactor.Stage.MultiRange` payload, so `multipart_carries_slice` (every
requested range's slice on the wire, contiguously) speaks about this lane. -/
theorem partsWire_eq_multipartBody (body : Bytes) (r : Nat × Nat) (rs : List (Nat × Nat)) :
    partsWire body (prefaces body.length (r :: rs)) multiCloser
      = Reactor.Stage.MultiRange.multipartBody body (r :: rs) := by
  simp only [partsWire, prefaces, multiCloser, List.map_cons, List.map_map,
    List.flatten_cons, List.append_assoc]
  rw [show ((fun s : Bytes × Nat × Nat =>
        s.1 ++ (body.drop s.2.1).take (s.2.2 + 1 - s.2.1)) ∘
        (fun r' : Nat × Nat =>
          (Reactor.Stage.MultiRange.crlf ++ Reactor.Stage.MultiRange.partHeader body.length r', r'.1, r'.2)))
      = (fun r' : Nat × Nat =>
          (Reactor.Stage.MultiRange.crlf ++ Reactor.Stage.MultiRange.partHeader body.length r')
            ++ (body.drop r'.1).take (r'.2 + 1 - r'.1)) from rfl,
      parts_tail_eq body rs, Reactor.Stage.MultiRange.multipart_cons,
      Reactor.Stage.MultiRange.part_carries_slice, window_is_slice]
  simp [List.append_assoc]

/-- **The framed `Content-Length` counts the multipart body exactly** (every
window in bounds ⇒ `multiLen` = the proven payload's length). -/
theorem multiLen_exact (body : Bytes) (rs : List (Nat × Nat))
    (hb : ∀ p ∈ rs, p.1 ≤ p.2 ∧ p.2 < body.length) :
    (Reactor.Stage.MultiRange.multipartBody body rs).length = multiLen body.length rs := by
  induction rs with
  | nil => simp [Reactor.Stage.MultiRange.multipartBody, multiLen]
  | cons r t ih =>
      have hr := hb r (List.mem_cons_self ..)
      have hlen := Reactor.Stage.MultiRange.slice_length body r hr.1 hr.2
      have ht := ih (fun p hp => hb p (List.mem_cons_of_mem _ hp))
      have hcl : (Reactor.Stage.MultiRange.crlf).length = 2 := rfl
      rw [Reactor.Stage.MultiRange.multipart_cons, List.length_append,
          Reactor.Stage.MultiRange.part_carries_slice, List.length_append,
          List.length_append, hlen, ht]
      simp only [multiLen, List.map_cons, List.sum_cons]
      omega

/-! ## The batch-small responses -/

/-- `304 Not Modified`: status, `Connection`, the validators, NO body (RFC
7232 §4.1 — same shape the proven `notModifiedOf` produces: `304`, body
stripped). -/
def resp304 (etag lm : Bytes) (ka : Bool) : Bytes :=
  aStatus304 ++ aConn ka ++ etagBlock etag ++ lmBlock lm ++ acrlf

/-- The `304` is header-terminated — no body octets follow the blank line. -/
theorem resp304_no_body (etag lm : Bytes) (ka : Bool) :
    acrlf ++ acrlf <:+ resp304 etag lm ka :=
  ⟨aStatus304 ++ aConn ka ++ etagBlock etag ++ (ascii "Last-Modified: " ++ lm),
   by simp [resp304, lmBlock, List.append_assoc]⟩

/-- The `405` body. -/
def body405 : Bytes := ascii "method not allowed\n"

/-- `405 Method Not Allowed`, with the RFC-mandated `Allow` listing exactly
the two methods a static file supports. -/
def resp405 (ka : Bool) : Bytes :=
  aStatus405 ++ aConn ka ++ ascii "Allow: GET, HEAD\r\n"
    ++ actBlock (ascii "text/plain; charset=utf-8")
    ++ aclBlock body405.length ++ acrlf ++ body405

/-- The `416` body. -/
def body416 : Bytes := ascii "range not satisfiable\n"

/-- `416 Range Not Satisfiable`, carrying `Content-Range: bytes */total`
(RFC 9110 §14.4 — the current representation length). -/
def resp416 (total : Nat) (ka : Bool) : Bytes :=
  aStatus416 ++ aConn ka ++ contentRangeStar total
    ++ actBlock (ascii "text/plain; charset=utf-8")
    ++ aclBlock body416.length ++ acrlf ++ body416

/-- The `416` carries the star form with the representation's exact length. -/
theorem resp416_content_range (total : Nat) (ka : Bool) :
    (contentRangeStar total <:+: resp416 total ka)
    ∧ Proto.Dec.dval 0 (adec total) = total :=
  ⟨⟨aStatus416 ++ aConn ka,
    actBlock (ascii "text/plain; charset=utf-8") ++ aclBlock body416.length
      ++ acrlf ++ body416,
    by simp [resp416, List.append_assoc]⟩,
   adec_roundtrip total⟩

/-- The `301` body. -/
def body301 : Bytes := ascii "moved permanently\n"

/-- `301 Moved Permanently` for a directory target requested without its
trailing slash (RFC 9110 §15.4.2). `loc` is the redirect target — the request
target with a `/` appended — carried in a relative `Location`. The host reports
only the boundary fact (the resolved entity is a directory, target lacks the
trailing slash); the location bytes and every header byte are decided here. -/
def resp301 (loc : Bytes) (ka : Bool) : Bytes :=
  aStatus301 ++ aConn ka ++ ascii "Location: " ++ loc ++ acrlf
    ++ actBlock (ascii "text/plain; charset=utf-8")
    ++ aclBlock body301.length ++ acrlf ++ body301

/-- The `301` carries the `Location` line, with a `Content-Length` whose digits
parse back to the exact body byte count. -/
theorem resp301_location (loc : Bytes) (ka : Bool) :
    ((ascii "Location: " ++ loc ++ acrlf) <:+: resp301 loc ka)
    ∧ Proto.Dec.dval 0 (adec body301.length) = body301.length :=
  ⟨⟨aStatus301 ++ aConn ka,
    actBlock (ascii "text/plain; charset=utf-8") ++ aclBlock body301.length
      ++ acrlf ++ body301,
    by simp [resp301, List.append_assoc]⟩,
   adec_roundtrip body301.length⟩

/-- The `404` head half (through the blank line): the model's `notFoundResp`
minus its 9 body bytes — what a `HEAD` for a missing file gets. -/
def notFoundHead (ka : Bool) : Bytes :=
  ascii "HTTP/1.1 404 Not Found\r\n" ++ aConn ka ++ ascii "Content-Length: 9\r\n\r\n"

/-- **The `404` byte-split**: the MODEL's `notFoundResp` is exactly
`notFoundHead ++ "not found"` — the GET `404` is the model's bytes verbatim
(unchanged from `Route.StaticHead`'s deployment), and the `HEAD` `404` is its
head half. -/
theorem notFound_split (ka : Bool) :
    notFoundResp ka = notFoundHead ka ++ ascii "not found" := by
  unfold notFoundResp notFoundHead
  rw [← ascii_eq_strBytes "Content-Length: 9\r\n\r\nnot found" (by decide),
      show statusLine404 = ascii "HTTP/1.1 404 Not Found\r\n" from
        (ascii_eq_strBytes _ (by decide)).symm,
      ← aConn_eq]
  cases ka <;> decide

/-! ## The conditional decision (reusing the PROVEN precondition matcher) -/

/-- `if-modified-since` (lowercase). -/
def imsNameLower : Bytes := ascii "if-modified-since"

/-- **The conditional-GET guard.** `If-None-Match` (the PROVEN
`ifNoneMatchMatches` — same matcher the deployed cache revalidation crosses)
takes precedence; only in its absence is `If-Modified-Since` consulted, as
the exact-date compare against the representation's `Last-Modified` bytes
(RFC 9110 §13.1.3 precedence). -/
def condNotModified (req : Proto.Request) (etag lm : Bytes) : Bool :=
  match headerVal ifNoneMatchNameLower req.headers with
  | some _ => ifNoneMatchMatches req etag
  | none =>
    match headerVal imsNameLower req.headers with
    | some v => v == lm
    | none => false

/-- `If-None-Match` absent ⇒ the guard is exactly the `If-Modified-Since`
exact-date compare. -/
theorem cond_ims_exact (req : Proto.Request) (etag lm v : Bytes)
    (hno : headerVal ifNoneMatchNameLower req.headers = none)
    (hims : headerVal imsNameLower req.headers = some v) :
    condNotModified req etag lm = (v == lm) := by
  unfold condNotModified
  rw [hno, hims]

/-- Both preconditions absent ⇒ the guard never fires. -/
theorem cond_absent (req : Proto.Request) (etag lm : Bytes)
    (hno : headerVal ifNoneMatchNameLower req.headers = none)
    (hnims : headerVal imsNameLower req.headers = none) :
    condNotModified req etag lm = false := by
  unfold condNotModified
  rw [hno, hnims]

/-! ### The bridge to the proven `ConditionalRequest` stage -/

/-- A candidate `200` carrying the representation's `ETag` — what the static
lane WOULD have built; the proven finisher stage's rewrite of it defines the
`304` decision. -/
def cand200 (etag body : Bytes) : Reactor.Response :=
  { status := 200, reason := ascii "OK"
    headers := [(ascii "ETag", etag)], body := body }

/-- Head byte `"` is not OWS, so a quoted value trims to itself. -/
theorem trimOWS_quoted (mid : Bytes) :
    trimOWS (34 :: (mid ++ [34])) = 34 :: (mid ++ [34]) := by
  have hdrop : ∀ t : Bytes, (34 :: t).dropWhile isOWS = 34 :: t := fun t => by
    rw [List.dropWhile_cons]
    simp [show isOWS 34 = false from rfl]
  unfold trimOWS
  rw [hdrop]
  have hrev : (34 :: (mid ++ [34])).reverse = 34 :: (34 :: mid).reverse := by
    simp [List.reverse_append]
  rw [hrev, hdrop, ← hrev, List.reverse_reverse]

/-- The entity tag survives field-value trimming. -/
theorem trimOWS_etagVal (len mtime : Nat) :
    trimOWS (etagVal len mtime) = etagVal len mtime :=
  trimOWS_quoted _

/-- The candidate's `ETag` is found by the stage's own reader. -/
theorem cand200_etag (etag body : Bytes) (hq : trimOWS etag = etag) :
    respETag (cand200 etag body) = some etag := by
  have hp : (lowerBytes (ascii "ETag") == etagNameLower) = true := by decide
  simp [respETag, Reactor.Stage.ConditionalRequest.headerVal, cand200,
    List.find?, hp, hq]

/-- **The stage bridge**: the PROVEN finisher's rewrite of the candidate `200`
goes `304` exactly when `ifNoneMatchMatches` — the matcher this lane's guard
crosses. (The `If-Match` premise is the corpus case: no `If-Match` sent.) -/
theorem stage_bridge_304 (req : Proto.Request) (etag body : Bytes)
    (hq : trimOWS etag = etag) (him : ifMatchFails req etag = false) :
    ((conditionalRewrite req (cand200 etag body)).status = 304)
      ↔ ifNoneMatchMatches req etag = true := by
  have hE := cand200_etag etag body hq
  have h200 : ((cand200 etag body).status == 200) = true := by rfl
  constructor
  · intro h
    cases hn : ifNoneMatchMatches req etag with
    | true => rfl
    | false =>
        rw [Reactor.Stage.ConditionalRequest.conditionalRewrite_passes
              req _ etag h200 hE him hn] at h
        simp [cand200] at h
  · intro h
    rw [Reactor.Stage.ConditionalRequest.conditionalRewrite_ifNoneMatch
          req _ etag h200 hE him h]
    rfl

/-- **The lane agrees with the stage**: with `If-None-Match` present, this
module's `304` guard fires exactly when `conditionalRewrite` would rewrite
the candidate `200` to `304`. -/
theorem cond_fires_iff_stage (req : Proto.Request) (len mtime : Nat) (body lm : Bytes)
    (v : Bytes) (hinm : headerVal ifNoneMatchNameLower req.headers = some v)
    (him : ifMatchFails req (etagVal len mtime) = false) :
    (condNotModified req (etagVal len mtime) lm = true)
      ↔ (conditionalRewrite req (cand200 (etagVal len mtime) body)).status = 304 := by
  rw [stage_bridge_304 req _ body (trimOWS_etagVal len mtime) him]
  unfold condNotModified
  rw [hinm]

/-! ## Range parsing and resolution (RFC 9110 §14) -/

/-- One `Range` spec: `a-b` (closed), `a-` (from), `-n` (suffix). -/
inductive RangeSpec where
  | closed (a b : Nat)
  | fromA (a : Nat)
  | suffix (n : Nat)
deriving Repr, DecidableEq

/-- Parse one spec. `none` on anything malformed — including an inverted
`a-b` with `a > b` (fail-closed: the whole header is then ignored). -/
def parseSpecX (bs : Bytes) : Option RangeSpec :=
  if bs.take 1 == [45] then
    (Reactor.Stage.MultiRange.parseNatB (bs.drop 1)).map .suffix
  else
    let ds := bs.takeWhile Reactor.Stage.MultiRange.isDigitB
    let rest := bs.drop ds.length
    if rest.take 1 == [45] then
      let tl := rest.drop 1
      if tl.isEmpty then (Reactor.Stage.MultiRange.parseNatB ds).map .fromA
      else
        match Reactor.Stage.MultiRange.parseNatB ds, Reactor.Stage.MultiRange.parseNatB tl with
        | some a, some b => if a ≤ b then some (.closed a b) else none
        | _, _ => none
    else none

/-- Sequence: `some` only when EVERY spec parsed (one malformed spec voids
the header — it is then ignored, RFC 9110 §14.2's MAY, matching the
reference behaviour). -/
def seqSpec : List (Option RangeSpec) → Option (List RangeSpec)
  | [] => some []
  | none :: _ => none
  | some a :: t => (seqSpec t).map (a :: ·)

/-- Parse a `Range` field value: `bytes=spec,spec,…` (unit lowercased). -/
def parseRangeVal (v : Bytes) : Option (List RangeSpec) :=
  let lv := lowerBytes (trimOWS v)
  if Reactor.Stage.MultiRange.isPrefixB Reactor.Stage.MultiRange.bytesEqTok lv then
    seqSpec ((Reactor.Stage.MultiRange.splitComma (lv.drop Reactor.Stage.MultiRange.bytesEqTok.length)).map
      (fun s => parseSpecX (trimOWS s)))
  else none

/-- Resolve one spec against the representation length: the satisfiable
closed window, or `none` (unsatisfiable). The `a ≤ b` re-check on the closed
form is defense in depth — `parseSpecX` already refuses inverted specs, but
resolution stays locally sound for EVERY input. -/
def resolveSpec (len : Nat) : RangeSpec → Option (Nat × Nat)
  | .closed a b => if a < len ∧ a ≤ b then some (a, min b (len - 1)) else none
  | .fromA a => if a < len then some (a, len - 1) else none
  | .suffix n => if n = 0 ∨ len = 0 then none else some (len - min n len, len - 1)

/-- **Resolution soundness**: every resolved window is well-formed and in
bounds — `a ≤ b < len` — for all three spec forms. -/
theorem resolveSpec_sound (len : Nat) (s : RangeSpec) (a b : Nat)
    (h : resolveSpec len s = some (a, b)) : a ≤ b ∧ b < len := by
  cases s with
  | closed x y =>
      simp only [resolveSpec] at h
      split at h
      · injection h with h'; injection h' with h1 h2; omega
      · exact absurd h (by simp)
  | fromA x =>
      simp only [resolveSpec] at h
      split at h
      · injection h with h'; injection h' with h1 h2; omega
      · exact absurd h (by simp)
  | suffix n =>
      simp only [resolveSpec] at h
      split at h
      · exact absurd h (by simp)
      · injection h with h'; injection h' with h1 h2; omega

/-- Every window a resolved spec-list carries is in bounds. -/
theorem resolved_inbounds (len : Nat) (specs : List RangeSpec) :
    ∀ p ∈ specs.filterMap (resolveSpec len), p.1 ≤ p.2 ∧ p.2 < len := by
  intro p hp
  obtain ⟨s, _, hs⟩ := List.mem_filterMap.mp hp
  exact resolveSpec_sound len s p.1 p.2 hs

/-- `range` (lowercase). -/
def rangeNameLower : Bytes := ascii "range"

/-- The range decision on a request. -/
inductive RangeD where
  | noRange
  | unsat
  | single (a b : Nat)
  | multi (rs : List (Nat × Nat))
deriving Repr, DecidableEq

/-- Classify a resolved window list (explicit patterns — no catch-all — so
the inversions below are clean). -/
def rangeOf : List (Nat × Nat) → RangeD
  | [] => .unsat
  | [(a, b)] => .single a b
  | p :: q :: t => .multi (p :: q :: t)

theorem rangeOf_single : ∀ (l : List (Nat × Nat)) (a b : Nat),
    rangeOf l = .single a b → l = [(a, b)]
  | [], a, b, h => by simp [rangeOf] at h
  | [(x, y)], a, b, h => by
      simp only [rangeOf, RangeD.single.injEq] at h
      rw [h.1, h.2]
  | (p :: q :: t), a, b, h => by simp [rangeOf] at h

theorem rangeOf_multi : ∀ (l : List (Nat × Nat)) (rs : List (Nat × Nat)),
    rangeOf l = .multi rs → l = rs ∧ 2 ≤ rs.length
  | [], rs, h => by simp [rangeOf] at h
  | [(x, y)], rs, h => by simp [rangeOf] at h
  | (p :: q :: t), rs, h => by
      simp only [rangeOf, RangeD.multi.injEq] at h
      subst h
      exact ⟨rfl, Nat.le_add_left 2 t.length⟩

/-- **The range decision**: no/foreign/malformed `Range` ⇒ serve whole;
none satisfiable ⇒ `416`; exactly one ⇒ single `206`; several ⇒ multipart. -/
def rangeDecision (req : Proto.Request) (len : Nat) : RangeD :=
  match headerVal rangeNameLower req.headers with
  | none => .noRange
  | some v =>
    match parseRangeVal v with
    | none => .noRange
    | some specs => rangeOf (specs.filterMap (resolveSpec len))

/-- A `.single` decision's window is in bounds. -/
theorem rangeDecision_single_inbounds (req : Proto.Request) (len a b : Nat)
    (h : rangeDecision req len = .single a b) : a ≤ b ∧ b < len := by
  unfold rangeDecision at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · have hl := rangeOf_single _ _ _ h
      exact resolved_inbounds len _ (a, b) (by rw [hl]; exact List.mem_cons_self ..)

/-- A `.multi` decision's windows are all in bounds, and there are at least
two of them. -/
theorem rangeDecision_multi_inbounds (req : Proto.Request) (len : Nat)
    (rs : List (Nat × Nat)) (h : rangeDecision req len = .multi rs) :
    (∀ p ∈ rs, p.1 ≤ p.2 ∧ p.2 < len) ∧ 2 ≤ rs.length := by
  unfold rangeDecision at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · obtain ⟨hl, h2⟩ := rangeOf_multi _ _ h
      exact ⟨fun p hp => resolved_inbounds len _ p (by rw [hl]; exact hp), h2⟩

/-! ## The request parse (permissive header split, host boundary shape) -/

/-- Split on LF (a permissive line split; a CR remainder is trimmed by
`dropCR`). -/
def splitLF : Bytes → List Bytes
  | [] => [[]]
  | b :: t =>
    if b == 10 then [] :: splitLF t
    else
      match splitLF t with
      | h :: rt => (b :: h) :: rt
      | [] => [[b]]

/-- `splitLF` never yields the empty list: every input carries at least the
(possibly empty) final line. -/
theorem splitLF_ne_nil (bs : Bytes) : splitLF bs ≠ [] := by
  cases bs with
  | nil => simp [splitLF]
  | cons b t =>
    rw [splitLF]
    by_cases h : b == 10
    · simp [h]
    · rw [if_neg h]
      rcases splitLF t with _ | ⟨h', rt⟩ <;> simp

/-- Tail-recursive `splitLF`: the line under construction accumulates in
reverse in `cur`, finished lines accumulate in reverse in `acc` — one loop
iteration per octet, constant stack regardless of input length. -/
def splitLFRevGo : List Bytes → Bytes → Bytes → List Bytes
  | acc, cur, [] => (cur.reverse :: acc).reverse
  | acc, cur, b :: t =>
    if b == 10 then splitLFRevGo (cur.reverse :: acc) [] t
    else splitLFRevGo acc (b :: cur) t

/-- The double-accumulator scan equals `splitLF` under the flushed
accumulators. -/
theorem splitLFRevGo_eq (bs : Bytes) :
    ∀ acc cur h rt, splitLF bs = h :: rt →
      splitLFRevGo acc cur bs = acc.reverse ++ (cur.reverse ++ h) :: rt := by
  induction bs with
  | nil =>
    intro acc cur h rt heq
    simp only [splitLF] at heq
    injection heq with h1 h2
    subst h1; subst h2
    simp [splitLFRevGo]
  | cons b t ih =>
    intro acc cur h rt heq
    rw [splitLF] at heq
    rw [splitLFRevGo]
    by_cases hb : b == 10
    · rw [if_pos hb] at heq
      rw [if_pos hb]
      injection heq with h1 h2
      subst h1; subst h2
      rcases hsp : splitLF t with _ | ⟨h', rt'⟩
      · exact absurd hsp (splitLF_ne_nil t)
      · rw [ih (cur.reverse :: acc) [] h' rt' hsp]
        simp
    · rw [if_neg hb] at heq
      rw [if_neg hb]
      rcases hsp : splitLF t with _ | ⟨h', rt'⟩
      · exact absurd hsp (splitLF_ne_nil t)
      · rw [hsp] at heq
        injection heq with h1 h2
        subst h1; subst h2
        rw [ih acc (b :: cur) h' rt' hsp]
        simp

/-- The loop form `splitLF` compiles to. -/
def splitLFTail (bs : Bytes) : List Bytes := splitLFRevGo [] [] bs

/-- **The loop/spec agreement.** Installs the constant-stack loop as the
compiled implementation of `splitLF`, so the parse's stack cost no longer
grows with the raw request byte count. -/
@[csimp] theorem splitLF_eq_tail : @splitLF = @splitLFTail := by
  funext bs
  rcases hsp : splitLF bs with _ | ⟨h, rt⟩
  · exact absurd hsp (splitLF_ne_nil bs)
  · rw [splitLFTail, splitLFRevGo_eq bs [] [] h rt hsp]
    simp

/-- Trim one trailing CR. -/
def dropCR (l : Bytes) : Bytes :=
  if l.getLast? == some 13 then l.dropLast else l

/-- Split a header line at the first `:`. -/
def splitColon (l : Bytes) : Option (Bytes × Bytes) :=
  let name := l.takeWhile (fun b => b != 58)
  if name.length == l.length then none
  else some (name, l.drop (name.length + 1))

/-- Header lines through the first blank line (the body is never inspected). -/
def headerLines : List Bytes → List (Bytes × Bytes)
  | [] => []
  | l :: rest =>
    let l' := dropCR l
    if l'.isEmpty then []
    else
      match splitColon l' with
      | some kv => kv :: headerLines rest
      | none => headerLines rest

/-- Tail-recursive `headerLines`: header pairs accumulate in reverse, one
loop iteration per line, constant stack regardless of header count. -/
def headerLinesRevGo : List (Bytes × Bytes) → List Bytes → List (Bytes × Bytes)
  | acc, [] => acc.reverse
  | acc, l :: rest =>
    if (dropCR l).isEmpty then acc.reverse
    else
      match splitColon (dropCR l) with
      | some kv => headerLinesRevGo (kv :: acc) rest
      | none => headerLinesRevGo acc rest

/-- The reverse-accumulator fold equals `headerLines` under the flushed
accumulator. -/
theorem headerLinesRevGo_eq (ls : List Bytes) :
    ∀ acc, headerLinesRevGo acc ls = acc.reverse ++ headerLines ls := by
  induction ls with
  | nil => intro acc; simp [headerLinesRevGo, headerLines]
  | cons l rest ih =>
    intro acc
    rw [headerLinesRevGo, headerLines]
    by_cases h : (dropCR l).isEmpty
    · simp [h]
    · rw [if_neg h, if_neg h]
      rcases splitColon (dropCR l) with _ | kv
      · exact ih acc
      · show headerLinesRevGo (kv :: acc) rest = acc.reverse ++ (kv :: headerLines rest)
        rw [ih (kv :: acc)]
        simp

/-- The loop form `headerLines` compiles to. -/
def headerLinesTail (ls : List Bytes) : List (Bytes × Bytes) :=
  headerLinesRevGo [] ls

/-- **The loop/spec agreement.** Installs the constant-stack loop as the
compiled implementation of `headerLines`, so the parse's stack cost no
longer grows with the header-line count. -/
@[csimp] theorem headerLines_eq_tail : @headerLines = @headerLinesTail := by
  funext ls
  rw [headerLinesTail, headerLinesRevGo_eq ls []]
  simp

/-- Parse the raw request bytes into the `Proto.Request` shape the proven
matchers consume: request-line method/target, then the header pairs. A
malformed request yields an empty method — which the plan answers `405`
(fail-closed; the host's own lane gate already required a parseable line). -/
def reqParse (raw : Bytes) : Proto.Request :=
  match splitLF raw with
  | [] => {}
  | rl :: rest =>
    let rl' := dropCR rl
    let method := rl'.takeWhile (fun b => b != 32)
    let after := (rl'.drop method.length).drop 1
    let target := after.takeWhile (fun b => b != 32)
    { method := method, target := target, version := [], headers := headerLines rest }

/-! ## The plan -/

/-- `GET`. -/ def getM : Bytes := [71, 69, 84]
/-- `HEAD`. -/ def headM : Bytes := [72, 69, 65, 68]

/-- The two methods a static file supports. -/
def isGetOrHead (m : Bytes) : Bool := m == getM || m == headM

/-- **The serving plan** — what the host must write, decided entirely here. -/
inductive Plan where
  | reply (resp : Bytes)
  | whole (head : Bytes)
  | window (off n : Nat) (head : Bytes)
  | parts (head : Bytes) (segs : List (Bytes × Nat × Nat)) (tail : Bytes)
deriving Repr, DecidableEq

/-- **The static lane's response decision.** Method gate (`405`), directory
trailing-slash redirect (`301`, when the host reports the resolved entity is a
directory and the request target lacks its trailing slash), existence (`404`,
model bytes), conditional (`304`, via the proven matcher), then the range
decision (`206` single/multipart, `416`) — range handling on `GET` only
(RFC 9110 §14.2 defines range handling for `GET`; a `HEAD` gets the plain
head). Every `HEAD` is a batch-small `.reply` of the head bytes. -/
def plan (redir found ka : Bool) (len mtime : Nat) (name : Bytes) (req : Proto.Request) :
    Plan :=
  if isGetOrHead req.method then
    if redir then .reply (resp301 (req.target ++ [47]) ka)
    else if found then
      let etag := etagVal len mtime
      let lm := httpDate mtime
      let ct := ctypeFor (extOf name)
      if condNotModified req etag lm then .reply (resp304 etag lm ka)
      else if req.method == headM then .reply (okHead2 ct len etag lm ka)
      else
        match rangeDecision req len with
        | .noRange => .whole (okHead2 ct len etag lm ka)
        | .unsat => .reply (resp416 len ka)
        | .single a b => .window a (b + 1 - a) (head206 ct a b len etag lm ka)
        | .multi rs =>
            .parts (head206multi len rs etag lm ka) (prefaces len rs) multiCloser
    else .reply (if req.method == headM then notFoundHead ka else notFoundResp ka)
  else .reply (resp405 ka)

/-! ### Plan arm equations -/

/-- A method a file cannot support ⇒ the `405`, regardless of existence. -/
theorem plan_405 (redir found ka : Bool) (len mtime : Nat) (name : Bytes)
    (req : Proto.Request) (h : isGetOrHead req.method = false) :
    plan redir found ka len mtime name req = .reply (resp405 ka) := by
  simp [plan, h]

/-- A missing target under `GET` ⇒ the MODEL's `notFoundResp`, verbatim —
the `404` bytes are unchanged from `Route.StaticHead`'s deployment. -/
theorem plan_404 (ka : Bool) (len mtime : Nat) (name : Bytes)
    (req : Proto.Request) (hm : isGetOrHead req.method = true)
    (hh : (req.method == headM) = false) :
    plan false false ka len mtime name req = .reply (notFoundResp ka) := by
  simp [plan, hm, hh]

/-- A missing target under `HEAD` ⇒ the model `404`'s head half (no body
octets — `notFound_split` is the byte-split). -/
theorem plan_404_head (ka : Bool) (len mtime : Nat) (name : Bytes)
    (req : Proto.Request) (hm : isGetOrHead req.method = true)
    (hh : (req.method == headM) = true) :
    plan false false ka len mtime name req = .reply (notFoundHead ka) := by
  simp [plan, hm, hh]

/-- The conditional guard fires ⇒ the `304` (whose body is empty —
`resp304_no_body`), before any range processing. -/
theorem plan_304 (ka : Bool) (len mtime : Nat) (name : Bytes)
    (req : Proto.Request) (hm : isGetOrHead req.method = true)
    (hc : condNotModified req (etagVal len mtime) (httpDate mtime) = true) :
    plan false true ka len mtime name req
      = .reply (resp304 (etagVal len mtime) (httpDate mtime) ka) := by
  simp [plan, hm, hc]

/-- No `Range` (or a foreign/malformed one) on a plain `GET` ⇒ the whole-file
`200` under the validated head. -/
theorem plan_whole (ka : Bool) (len mtime : Nat) (name : Bytes)
    (req : Proto.Request) (hm : isGetOrHead req.method = true)
    (hh : (req.method == headM) = false)
    (hc : condNotModified req (etagVal len mtime) (httpDate mtime) = false)
    (hr : rangeDecision req len = .noRange) :
    plan false true ka len mtime name req
      = .whole (okHead2 (ctypeFor (extOf name)) len (etagVal len mtime)
          (httpDate mtime) ka) := by
  simp [plan, hm, hh, hc, hr]

/-- No satisfiable range ⇒ the `416` with `Content-Range: bytes */len`. -/
theorem plan_416 (ka : Bool) (len mtime : Nat) (name : Bytes)
    (req : Proto.Request) (hm : isGetOrHead req.method = true)
    (hh : (req.method == headM) = false)
    (hc : condNotModified req (etagVal len mtime) (httpDate mtime) = false)
    (hr : rangeDecision req len = .unsat) :
    plan false true ka len mtime name req = .reply (resp416 len ka) := by
  simp [plan, hm, hh, hc, hr]

/-- One satisfiable range ⇒ the single-window `206`. -/
theorem plan_single (ka : Bool) (len mtime : Nat) (name : Bytes) (a b : Nat)
    (req : Proto.Request) (hm : isGetOrHead req.method = true)
    (hh : (req.method == headM) = false)
    (hc : condNotModified req (etagVal len mtime) (httpDate mtime) = false)
    (hr : rangeDecision req len = .single a b) :
    plan false true ka len mtime name req
      = .window a (b + 1 - a)
          (head206 (ctypeFor (extOf name)) a b len (etagVal len mtime)
            (httpDate mtime) ka) := by
  simp [plan, hm, hh, hc, hr]

/-- Several satisfiable ranges ⇒ the multipart plan (prefaces + windows +
closing tail — grounded by `parts_exact`). -/
theorem plan_multi (ka : Bool) (len mtime : Nat) (name : Bytes)
    (rs : List (Nat × Nat)) (req : Proto.Request)
    (hm : isGetOrHead req.method = true) (hh : (req.method == headM) = false)
    (hc : condNotModified req (etagVal len mtime) (httpDate mtime) = false)
    (hr : rangeDecision req len = .multi rs) :
    plan false true ka len mtime name req
      = .parts (head206multi len rs (etagVal len mtime) (httpDate mtime) ka)
          (prefaces len rs) multiCloser := by
  simp [plan, hm, hh, hc, hr]

/-- A directory target requested without its trailing slash (the host's
`redir` boundary fact) ⇒ the `301` redirect to the request target plus `/`,
regardless of existence, conditional, or range facts. -/
theorem plan_301 (found ka : Bool) (len mtime : Nat) (name : Bytes)
    (req : Proto.Request) (hm : isGetOrHead req.method = true) :
    plan true found ka len mtime name req
      = .reply (resp301 (req.target ++ [47]) ka) := by
  simp [plan, hm]

/-! ### Window exactness (the streamed bytes are the proven slice) -/

/-- **Single-range exactness.** The `.single` decision's window copy — what
the host streams under the `.window` plan — IS the proven `Reactor.Stage.MultiRange.slice`:
non-empty, in bounds, the exact requested length (`slice_length`), and in
place (`slice_decomposition`). -/
theorem window_exact (req : Proto.Request) (len a b : Nat) (body : Bytes)
    (hbody : body.length = len) (h : rangeDecision req len = .single a b) :
    1 ≤ b + 1 - a ∧ a + (b + 1 - a) ≤ len
    ∧ (body.drop a).take (b + 1 - a) = Reactor.Stage.MultiRange.slice body (a, b)
    ∧ ((body.drop a).take (b + 1 - a)).length = b + 1 - a
    ∧ body = body.take a ++ (body.drop a).take (b + 1 - a) ++ body.drop (b + 1) := by
  obtain ⟨hab, hb⟩ := rangeDecision_single_inbounds req len a b h
  refine ⟨by omega, by omega, rfl, ?_, ?_⟩
  · exact Reactor.Stage.MultiRange.slice_length body (a, b) hab (by omega)
  · exact Reactor.Stage.MultiRange.slice_decomposition body a b hab

/-- **Multipart exactness.** A `.multi` decision's emitted wire — the
prefaces/windows/tail the host writes under the `.parts` plan — is EXACTLY
the proven `multipartBody`, and the framed `Content-Length` counts it
exactly. (`Reactor.Stage.MultiRange.multipart_carries_slice` therefore applies to the
wire: every requested slice is on it, contiguously.) -/
theorem parts_exact (req : Proto.Request) (len : Nat) (rs : List (Nat × Nat))
    (body : Bytes) (hbody : body.length = len)
    (h : rangeDecision req len = .multi rs) :
    partsWire body (prefaces len rs) multiCloser = Reactor.Stage.MultiRange.multipartBody body rs
    ∧ (Reactor.Stage.MultiRange.multipartBody body rs).length = multiLen len rs := by
  obtain ⟨hin, hlen2⟩ := rangeDecision_multi_inbounds req len rs h
  subst hbody
  constructor
  · cases rs with
    | nil => simp at hlen2
    | cons r t => exact partsWire_eq_multipartBody body r t
  · exact multiLen_exact body rs hin

/-! ## The exported seam -/

/-- Big-endian rendering, `w` bytes. -/
def be (w n : Nat) : Bytes :=
  (List.range w).map (fun i => UInt8.ofNat (n / 256 ^ (w - 1 - i) % 256))

/-- Serialize a plan for the host: tag byte, then the shape.
`1` reply · `2` whole · `3` window (`off(8) n(8) head`) ·
`4` parts (`headLen(4) head tailLen(2) tail count(2)
{preLen(2) pre off(8) n(8)}*`). -/
def encodePlan : Plan → Bytes
  | .reply r => 1 :: r
  | .whole h => 2 :: h
  | .window off n h => 3 :: (be 8 off ++ be 8 n ++ h)
  | .parts h segs tail =>
      4 :: (be 4 h.length ++ h ++ be 2 tail.length ++ tail ++ be 2 segs.length
        ++ (segs.map (fun s => be 2 s.1.length ++ s.1 ++ be 8 s.2.1
              ++ be 8 (s.2.2 + 1 - s.2.1))).flatten)

/-- **`drorb_static_decide` — the static response decision as `ByteArray →
ByteArray`.** Input framing: `flags(1) :: len(8 BE) :: mtime(8 BE) ::
nameLen(2 BE) :: name :: requestBytes`, flags bit 0 = keep-alive intent,
bit 1 = found (a regular file resolved), bit 2 = redir (the resolved entity is
a directory and the request target lacks its trailing slash). Output: the
encoded plan. A malformed frame returns EMPTY — the host fails safe (drops the
connection), never building response bytes itself. -/
@[export drorb_static_decide]
def staticDecideC (input : ByteArray) : ByteArray :=
  match input.toList with
  | [] => ⟨#[]⟩
  | flags :: rest =>
    if rest.length < 18 then ⟨#[]⟩
    else
      let ka := (flags &&& 0x01) == 0x01
      let found := (flags &&& 0x02) == 0x02
      let redir := (flags &&& 0x04) == 0x04
      let len := beNat (rest.take 8)
      let mtime := beNat ((rest.drop 8).take 8)
      let nameLen := beNat ((rest.drop 16).take 2)
      if rest.length < 18 + nameLen then ⟨#[]⟩
      else
        let name := (rest.drop 18).take nameLen
        let req := reqParse (rest.drop (18 + nameLen))
        ⟨(encodePlan (plan redir found ka len mtime name req)).toArray⟩

/-- The seam is the plan, verbatim: on a well-formed frame the output is
`encodePlan` of `plan` on the decoded boundary facts. -/
theorem staticDecideC_spec (input : ByteArray) (flags : UInt8) (rest : List UInt8)
    (hin : input.toList = flags :: rest) (h18 : ¬ rest.length < 18)
    (hname : ¬ rest.length < 18 + beNat ((rest.drop 16).take 2)) :
    staticDecideC input
      = ⟨(encodePlan (plan ((flags &&& 0x04) == 0x04) ((flags &&& 0x02) == 0x02)
            ((flags &&& 0x01) == 0x01)
            (beNat (rest.take 8)) (beNat ((rest.drop 8).take 8))
            ((rest.drop 18).take (beNat ((rest.drop 16).take 2)))
            (reqParse (rest.drop (18 + beNat ((rest.drop 16).take 2)))))).toArray⟩ := by
  unfold staticDecideC
  rw [hin]
  simp [h18, hname]

/-! ## Corpus witnesses (the differential harness's exact request shapes,
all kernel-decided) -/

set_option maxRecDepth 16384

/-- Parse a corpus request literal. -/
def wReq (s : String) : Proto.Request := reqParse (ascii s)

/-- The site fixture's pinned mtime (2026-01-02 03:04:05 UTC). -/
def siteMtime : Nat := 1767323045

/-- `Range: bytes=0-15` on the 204800-byte fixture ⇒ the exact first-16
window `206`. -/
theorem demo_range_first16 :
    plan false true false 204800 siteMtime (ascii "big.bin")
      (wReq "GET /static/big.bin HTTP/1.1\r\nHost: h\r\nConnection: close\r\nRange: bytes=0-15\r\n\r\n")
    = .window 0 16
        (head206 (ascii "application/octet-stream") 0 15 204800
          (etagVal 204800 siteMtime) (httpDate siteMtime) false) := by decide

/-- `Range: bytes=-100` (suffix) ⇒ the final-100 window. -/
theorem demo_range_suffix :
    plan false true false 204800 siteMtime (ascii "big.bin")
      (wReq "GET /static/big.bin HTTP/1.1\r\nHost: h\r\nConnection: close\r\nRange: bytes=-100\r\n\r\n")
    = .window 204700 100
        (head206 (ascii "application/octet-stream") 204700 204799 204800
          (etagVal 204800 siteMtime) (httpDate siteMtime) false) := by decide

/-- `Range: bytes=204700-` (open end) ⇒ the same final-100 window. -/
theorem demo_range_open :
    plan false true false 204800 siteMtime (ascii "big.bin")
      (wReq "GET /static/big.bin HTTP/1.1\r\nHost: h\r\nConnection: close\r\nRange: bytes=204700-\r\n\r\n")
    = .window 204700 100
        (head206 (ascii "application/octet-stream") 204700 204799 204800
          (etagVal 204800 siteMtime) (httpDate siteMtime) false) := by decide

/-- `Range: bytes=999999999-1000000000` ⇒ the `416` with `bytes */204800`. -/
theorem demo_range_unsat :
    plan false true false 204800 siteMtime (ascii "big.bin")
      (wReq "GET /static/big.bin HTTP/1.1\r\nHost: h\r\nConnection: close\r\nRange: bytes=999999999-1000000000\r\n\r\n")
    = .reply (resp416 204800 false) := by decide

/-- `Range: bytes=0-9,20-29` resolves to the two-window multi decision. -/
theorem demo_range_multi_decision :
    rangeDecision
      (wReq "GET /static/big.bin HTTP/1.1\r\nHost: h\r\nConnection: close\r\nRange: bytes=0-9,20-29\r\n\r\n")
      204800
    = .multi [(0, 9), (20, 29)] := by decide

/-- `Range: bytes=0-9,20-29` ⇒ the two-part `multipart/byteranges` plan
(whose wire, by `parts_exact`, is EXACTLY the proven `multipartBody`). -/
theorem demo_range_multi :
    plan false true false 204800 siteMtime (ascii "big.bin")
      (wReq "GET /static/big.bin HTTP/1.1\r\nHost: h\r\nConnection: close\r\nRange: bytes=0-9,20-29\r\n\r\n")
    = .parts
        (head206multi 204800 [(0, 9), (20, 29)]
          (etagVal 204800 siteMtime) (httpDate siteMtime) false)
        (prefaces 204800 [(0, 9), (20, 29)]) multiCloser :=
  plan_multi false 204800 siteMtime (ascii "big.bin") [(0, 9), (20, 29)] _
    (by decide) (by decide) (by decide) demo_range_multi_decision

/-- `Range: items=0-15` (foreign unit) ⇒ ignored, whole-file `200`. -/
theorem demo_range_bad_unit :
    plan false true false 204800 siteMtime (ascii "big.bin")
      (wReq "GET /static/big.bin HTTP/1.1\r\nHost: h\r\nConnection: close\r\nRange: items=0-15\r\n\r\n")
    = .whole (okHead2 (ascii "application/octet-stream") 204800
        (etagVal 204800 siteMtime) (httpDate siteMtime) false) := by decide

/-- `If-None-Match: *` ⇒ the `304` (H3's wildcard, via the proven matcher). -/
theorem demo_inm_star :
    plan false true false 12 siteMtime (ascii "hello.txt")
      (wReq "GET /static/hello.txt HTTP/1.1\r\nHost: h\r\nConnection: close\r\nIf-None-Match: *\r\n\r\n")
    = .reply (resp304 (etagVal 12 siteMtime) (httpDate siteMtime) false) := by decide

/-- A non-matching `If-None-Match` ⇒ the whole-file `200`. -/
theorem demo_inm_miss :
    plan false true false 12 siteMtime (ascii "hello.txt")
      (wReq "GET /static/hello.txt HTTP/1.1\r\nHost: h\r\nConnection: close\r\nIf-None-Match: \"does-not-match\"\r\n\r\n")
    = .whole (okHead2 (ascii "text/plain; charset=utf-8") 12
        (etagVal 12 siteMtime) (httpDate siteMtime) false) := by decide

/-- `If-Modified-Since` equal to the representation's `Last-Modified` ⇒ the
`304` (the exact-date arm). -/
theorem demo_ims_exact :
    plan false true false 12 siteMtime (ascii "hello.txt")
      (wReq "GET /static/hello.txt HTTP/1.1\r\nHost: h\r\nConnection: close\r\nIf-Modified-Since: Fri, 02 Jan 2026 03:04:05 GMT\r\n\r\n")
    = .reply (resp304 (etagVal 12 siteMtime) (httpDate siteMtime) false) := by decide

/-- A past `If-Modified-Since` (the corpus's 1970 date) ⇒ the whole-file
`200` (exact semantics — only the equal date revalidates). -/
theorem demo_ims_past :
    plan false true false 12 siteMtime (ascii "hello.txt")
      (wReq "GET /static/hello.txt HTTP/1.1\r\nHost: h\r\nConnection: close\r\nIf-Modified-Since: Thu, 01 Jan 1970 00:00:00 GMT\r\n\r\n")
    = .whole (okHead2 (ascii "text/plain; charset=utf-8") 12
        (etagVal 12 siteMtime) (httpDate siteMtime) false) := by decide

/-- `POST` (found) and `PUT` (missing) on static targets ⇒ the `405`. -/
theorem demo_post_405 :
    plan false true false 12 siteMtime (ascii "hello.txt")
      (wReq "POST /static/hello.txt HTTP/1.1\r\nHost: h\r\nConnection: close\r\nContent-Length: 0\r\n\r\n")
    = .reply (resp405 false)
    ∧ plan false false false 0 0 []
        (wReq "PUT /static/hello.txt HTTP/1.1\r\nHost: h\r\nConnection: close\r\nContent-Length: 0\r\n\r\n")
      = .reply (resp405 false) := by decide

/-- `HEAD` on a found file ⇒ the batch-small validated head, no body plan. -/
theorem demo_head :
    plan false true false 12 siteMtime (ascii "hello.txt")
      (wReq "HEAD /static/hello.txt HTTP/1.1\r\nHost: h\r\nConnection: close\r\n\r\n")
    = .reply (okHead2 (ascii "text/plain; charset=utf-8") 12
        (etagVal 12 siteMtime) (httpDate siteMtime) false) := by decide

/-- `GET` on a missing target ⇒ the model `404`, verbatim bytes. -/
theorem demo_404 :
    plan false false false 0 0 []
      (wReq "GET /static/nope.txt HTTP/1.1\r\nHost: h\r\nConnection: close\r\n\r\n")
    = .reply (notFoundResp false) :=
  plan_404 false 0 0 [] _ (by decide) (by decide)

/-- `HEAD` on a missing target ⇒ the model `404`'s head half. -/
theorem demo_404_head :
    plan false false false 0 0 []
      (wReq "HEAD /static/nope.txt HTTP/1.1\r\nHost: h\r\nConnection: close\r\n\r\n")
    = .reply (notFoundHead false) :=
  plan_404_head false 0 0 [] _ (by decide) (by decide)

/-- `GET /static/sub` (a directory target, host `redir` fact set) ⇒ the `301`
redirect to the request target plus `/` — `/static/sub/`. -/
theorem demo_dir_redirect :
    plan true false false 0 0 []
      (wReq "GET /static/sub HTTP/1.1\r\nHost: h\r\nConnection: close\r\n\r\n")
    = .reply (resp301 (ascii "/static/sub/") false) := by decide

end Route.StaticDecide
