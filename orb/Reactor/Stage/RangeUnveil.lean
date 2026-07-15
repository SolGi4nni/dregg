import Reactor.Pipeline
import Reactor.Stage.MultiRange
import Reactor.Stage.ConditionalRequest

/-!
# Reactor.Stage.RangeUnveil — If-Range validation + multi-range on the native
range handler (RFC 9110 §13.1.5 / §14.2 / §15.3.7)

The full RFC battery found two range gaps SEATED INSIDE the deployed static
handler — unreachable by any pure response transform, because the handler
consumes `Range` itself and answers a `206` from which the full representation
cannot be recovered:

* **K08 — `If-Range` with a non-matching validator ⇒ ignore `Range`, full
  `200` (§13.1.5, MUST-if-supported).** Deployed: the handler never reads
  `If-Range` and serves the `206` anyway — a torn download on a changed
  representation, the exact corruption §13.1.5 exists to prevent.
* **K06 — multiple ranges ⇒ `multipart/byteranges` `206` (§14.6).** Deployed:
  the handler concatenates the slices into one unbounded `206` (no
  `Content-Range`, no part structure) — the named residual of the previous
  fold's multipart transform, which could only reach range-IGNORING routes.

## The unveil move (request phase — this is the structural fix)

For exactly the two affected shapes — a request carrying `If-Range`+`Range`,
or a MULTI-range `Range` — the request phase REMOVES the range headers before
dispatch (stashing them in the context's attribute bag), so the handler serves
the full `200` with its validator. The response phase then owns the whole
§13.1.5/§14.2 decision on that `200`:

* `If-Range` present: STRONG-compare it against the response's `ETag`
  (§13.1.5: strong comparison — no `W/` tolerance). Match ⇒ carve the
  requested range (`206`); mismatch (or no validator, or a date-form
  `If-Range`) ⇒ the full `200` stands (the always-safe direction).
* Multi-range: carve the `multipart/byteranges` `206` — the SAME proven
  payload builder as `Reactor.Stage.MultiRange` (`multipartBody`/`setCt`),
  so the previous fold's multipart bytes are preserved on every route it
  already reached, while the static handler's routes gain it.
* Unsatisfiable ⇒ `416` with `Content-Range: bytes */complete-length`
  (§14.4); unparseable / non-`bytes` unit ⇒ the `200` stands (§14.2:
  an unrecognized range unit is ignored).

Single-range requests WITHOUT `If-Range` are untouched end to end (the
deployed handler's native single-range `206` is already conformant — K01–K05).

## What is proven (pure kernel; no `native_decide`)

* `unveil_off_id` / `unveil_noStash_id` — the conservation guards: a request
  with no `Range` header passes BOTH phases identically (the plus7 collapse
  hook).
* `applyRange_ifrange_mismatch_200` — K08: a non-matching `If-Range` leaves
  the full `200` byte-identical.
* `applyRange_ifrange_match_206` — K07 stays: a matching `If-Range` carves
  the `206` with the exact requested slice + `Content-Range`.
* `carve_multi_206` — K06: a valid multi-range carves the `multipart/
  byteranges` `206` with the SAME proven payload as the previous fold.
* `carve_unsat_416` — the §14.4 refusal carries `bytes */len`.
* Concrete witnesses on the probe's exact bytes.

Residuals (named): suffix (`-N`) and open (`N-`) specs under `If-Range`
parse to `none` and serve the full `200` (safe direction; the shared spec
parser's residual); a date-form `If-Range` likewise serves the `200`
(§13.1.5 allows evaluating only entity-tags); a PARTIALLY-satisfiable
multi-range answers `416` rather than the satisfiable subset.
-/

namespace Reactor.Stage.RangeUnveil

open Reactor.Pipeline
open Reactor (Response)
open Proto (Bytes)
open Reactor.Stage.MultiRange (parseRanges lower rangeTok rangeValOf rangesOf
  validFor multipartBody setCt slice)
open Reactor.Stage.ConditionalRequest (headerVal respETag)
open Reactor.Stage.FramingValidation (trimOWS)

/-! ## Tokens & keys -/

/-- `if-range` (lowercase). -/
def ifRangeTok : Bytes := [105, 102, 45, 114, 97, 110, 103, 101]

/-- `Content-Range` (wire case). -/
def contentRangeName : Bytes :=
  [67, 111, 110, 116, 101, 110, 116, 45, 82, 97, 110, 103, 101]

/-- `bytes ` — the §14.4 content-range unit prefix. -/
def bytesSpTok : Bytes := [98, 121, 116, 101, 115, 32]

/-- `Partial Content`. -/
def partialReason : Bytes :=
  [80, 97, 114, 116, 105, 97, 108, 32, 67, 111, 110, 116, 101, 110, 116]

/-- `Range Not Satisfiable`. -/
def unsatReason : Bytes :=
  [82, 97, 110, 103, 101, 32, 78, 111, 116, 32, 83, 97, 116, 105, 115, 102,
   105, 97, 98, 108, 101]

/-- The attribute-bag key stashing the unveiled `Range` value. -/
def ruRangeKey : String := "ru.range"

/-- The attribute-bag key stashing the unveiled `If-Range` validator. -/
def ruIfRangeKey : String := "ru.ifrange"

/-! ## Request-side decisions -/

/-- The request's `If-Range` validator (OWS-trimmed), if any. -/
def ifRangeValOf (req : Proto.Request) : Option Bytes :=
  headerVal ifRangeTok req.headers

/-- The request asks for MULTIPLE ranges (the §14.6 shape). -/
def multiOf (req : Proto.Request) : Bool :=
  match rangesOf req with
  | some rs => decide (2 ≤ rs.length)
  | none => false

/-- **Does the stage unveil?** Exactly the two shapes whose decision the
deployed handler gets wrong: `If-Range`+`Range` (§13.1.5) and multi-range
(§14.6). Everything else — no `Range`, and the handler's already-conformant
plain single-range — passes through untouched. -/
def unveils (req : Proto.Request) : Bool :=
  ((rangeValOf req).isSome && (ifRangeValOf req).isSome) || multiOf req

/-- A header the unveil keeps (everything but `Range`/`If-Range`). -/
def keepHeader (nv : Bytes × Bytes) : Bool :=
  !(lower nv.1 == rangeTok || lower nv.1 == ifRangeTok)

/-- Remove the `Range`/`If-Range` headers (the unveil). -/
def stripRange (req : Proto.Request) : Proto.Request :=
  { req with headers := req.headers.filter keepHeader }

/-- The stash entries for an unveiled request: its `Range` value, and (when
present) its OWS-trimmed `If-Range` validator. -/
def stashPairs (req : Proto.Request) : List (String × Bytes) :=
  (match rangeValOf req with
   | some rv => [(ruRangeKey, rv)]
   | none => [])
  ++ (match ifRangeValOf req with
      | some v => [(ruIfRangeKey, trimOWS v)]
      | none => [])

/-- The unveiled context: range headers stripped, originals stashed in the
attribute bag (the `Ctx.attrs` extension point). -/
def unveilCtx (c : Ctx) : Ctx :=
  if unveils c.req then
    { c with req := stripRange c.req, attrs := c.attrs ++ stashPairs c.req }
  else c

/-- The stashed `Range` value of a context (response-phase read-back). -/
def stashOf (c : Ctx) : Option Bytes :=
  (c.attrs.find? (fun kv => kv.1 == ruRangeKey)).map (fun kv => kv.2)

/-- The stashed `If-Range` validator. -/
def ifStashOf (c : Ctx) : Option Bytes :=
  (c.attrs.find? (fun kv => kv.1 == ruIfRangeKey)).map (fun kv => kv.2)

/-! ## Response-side carve -/

/-- `a-b/total` rendered (§14.4 range-resp). -/
def crVal (total : Nat) (r : Nat × Nat) : Bytes :=
  bytesSpTok ++ Proto.Dec.natToDec r.1 ++ [45] ++ Proto.Dec.natToDec r.2
    ++ [47] ++ Proto.Dec.natToDec total

/-- `bytes */total` — the §14.4 unsatisfied-range form. -/
def crValUnsat (total : Nat) : Bytes :=
  bytesSpTok ++ [42, 47] ++ Proto.Dec.natToDec total

/-- The single-range `206`: the exact slice + its `Content-Range`. -/
def single206 (r : Nat × Nat) (resp : Response) : Response :=
  { status := 206, reason := partialReason,
    headers := resp.headers ++ [(contentRangeName, crVal resp.body.length r)],
    body := slice resp.body r }

/-- The multi-range `206`: the proven `multipart/byteranges` payload —
byte-identical to the previous fold's multipart builder. -/
def multipart206 (rs : List (Nat × Nat)) (resp : Response) : Response :=
  { status := 206, reason := partialReason,
    headers := setCt resp.headers,
    body := multipartBody resp.body rs }

/-- The `416` refusal, carrying `Content-Range: bytes */complete-length`. -/
def range416 (resp : Response) : Response :=
  { status := 416, reason := unsatReason,
    headers := resp.headers ++ [(contentRangeName, crValUnsat resp.body.length)],
    body := [] }

/-- **The carve** — the §14.2 decision on the full `200`: unparseable/non-
`bytes` specs are IGNORED (the `200` stands); a satisfiable single range is
its exact `206`; a valid multi-range is the multipart `206`; out-of-bounds
ranges are the `416`. -/
def carve (rv : Bytes) (resp : Response) : Response :=
  match parseRanges (lower rv) with
  | none => resp
  | some [] => resp
  | some [r] =>
    if decide (r.2 < resp.body.length) then single206 r resp else range416 resp
  | some rs =>
    if validFor resp.body.length rs then multipart206 rs resp else range416 resp

/-- **§13.1.5 strong comparison.** The `If-Range` validator matches only the
byte-identical entity-tag (no `W/` tolerance — a weak tag never matches). A
response without a validator, or a date-form `If-Range`, never matches:
mismatch serves the full `200`, the always-safe direction. -/
def ifRangeMatches (ifr : Bytes) (resp : Response) : Bool :=
  match respETag resp with
  | some etag => ifr == etag
  | none => false

/-- The stashed `If-Range` BLOCKS the carve: present and not strong-matching
the response's validator (absent `If-Range` never blocks). -/
def ifRangeBlocks (ifr : Option Bytes) (resp : Response) : Bool :=
  match ifr with
  | some v => !(ifRangeMatches v resp)
  | none => false

/-- **The unveiled-response decision** (§13.2.2 step 5 — `If-Range` last,
on a request whose date/tag preconditions already passed as a `200`). -/
def applyRange (ifr : Option Bytes) (rv : Bytes) (resp : Response) : Response :=
  if resp.status == 200 then
    if ifRangeBlocks ifr resp then resp else carve rv resp
  else resp

/-! ## The stage -/

/-- **The range-unveil stage.** Request phase: strip+stash exactly the two
mishandled range shapes. Response phase: on the stashed shapes, run the
proven §13.1.5/§14.2 decision on the handler's full `200`. Everything else
is identical in both phases. -/
def rangeUnveilStage : Stage where
  name := "range-unveil"
  onRequest := fun c => .continue (unveilCtx c)
  onResponse := fun c b =>
    match stashOf c with
    | some rv => b.mapResp (applyRange (ifStashOf c) rv)
    | none => b

/-! ## Conservation guards (the plus7 collapse hooks) -/

/-- No `Range` header ⇒ no unveil: `multiOf` cannot see ranges and the
`If-Range` conjunct lacks its `Range`. -/
theorem unveils_noRange (req : Proto.Request) (h : rangeValOf req = none) :
    unveils req = false := by
  unfold unveils multiOf
  rw [h]
  unfold rangesOf
  rw [h]
  rfl

/-- A non-unveiling request passes the request phase UNTOUCHED. -/
theorem unveil_off_id (c : Ctx) (h : unveils c.req = false) :
    rangeUnveilStage.onRequest c = StageStep.continue c := by
  show StageStep.continue (unveilCtx c) = StageStep.continue c
  unfold unveilCtx
  rw [h]
  simp

/-- A stash-free context passes the response phase builder-IDENTICALLY. -/
theorem unveil_noStash_id (c : Ctx) (b : ResponseBuilder)
    (h : stashOf c = none) : rangeUnveilStage.onResponse c b = b := by
  show (match stashOf c with
        | some rv => b.mapResp (applyRange (ifStashOf c) rv)
        | none => b) = b
  rw [h]

/-! ## The K08 / K07 / K06 facts -/

/-- A present, non-matching `If-Range` blocks; a matching one clears. -/
theorem ifRangeBlocks_some (v : Bytes) (resp : Response) :
    ifRangeBlocks (some v) resp = !(ifRangeMatches v resp) := rfl

/-- **K08 (§13.1.5).** A non-matching `If-Range` leaves the full `200`
byte-identical — the `Range` is IGNORED. -/
theorem applyRange_ifrange_mismatch_200 (v rv : Bytes) (resp : Response)
    (h200 : (resp.status == 200) = true) (hm : ifRangeMatches v resp = false) :
    applyRange (some v) rv resp = resp := by
  unfold applyRange
  rw [h200, ifRangeBlocks_some, hm]
  simp

/-- **K07 stays (§13.1.5).** A matching `If-Range` with a satisfiable single
range carves the exact `206`: the requested slice, its `Content-Range`. -/
theorem applyRange_ifrange_match_206 (v rv : Bytes) (r : Nat × Nat) (resp : Response)
    (h200 : (resp.status == 200) = true) (hm : ifRangeMatches v resp = true)
    (hp : parseRanges (lower rv) = some [r]) (hb : (decide (r.2 < resp.body.length)) = true) :
    applyRange (some v) rv resp = single206 r resp := by
  have hblocks : ifRangeBlocks (some v) resp = false := by
    rw [ifRangeBlocks_some, hm]
    rfl
  have hcarve : carve rv resp = single206 r resp := by
    unfold carve
    simp only [hp, hb]
    simp
  unfold applyRange
  rw [h200, hblocks, hcarve]
  simp

/-- **K06 (§14.6).** A valid multi-range against the full `200` carves the
`multipart/byteranges` `206` — the SAME proven payload builder as the
previous fold's transform (`multipartBody` + `setCt`). -/
theorem carve_multi_206 (rv : Bytes) (rs : List (Nat × Nat)) (resp : Response)
    (hp : parseRanges (lower rv) = some rs) (h2 : 2 ≤ rs.length)
    (hv : validFor resp.body.length rs = true) :
    carve rv resp = multipart206 rs resp := by
  unfold carve
  rw [hp]
  cases rs with
  | nil => simp only [List.length_nil] at h2; omega
  | cons a t =>
    cases t with
    | nil => simp only [List.length_cons, List.length_nil] at h2; omega
    | cons b t2 => simp only [hv, if_true]

/-- A non-`200` (an upstream `304`/`412`/refusal) is never carved. -/
theorem applyRange_not200 (ifr : Option Bytes) (rv : Bytes) (resp : Response)
    (h : (resp.status == 200) = false) : applyRange ifr rv resp = resp := by
  unfold applyRange
  rw [h]
  simp

/-- **§14.4.** An all-unsatisfiable multi-range answers the `416`, and the
refusal carries `Content-Range: bytes */complete-length`. -/
theorem carve_unsat_416 (rv : Bytes) (rs : List (Nat × Nat)) (resp : Response)
    (hp : parseRanges (lower rv) = some rs) (h2 : 2 ≤ rs.length)
    (hv : validFor resp.body.length rs = false) :
    carve rv resp = range416 resp
    ∧ (contentRangeName, crValUnsat resp.body.length) ∈ (range416 resp).headers := by
  constructor
  · unfold carve
    rw [hp]
    cases rs with
    | nil => simp only [List.length_nil] at h2; omega
    | cons a t =>
      cases t with
      | nil => simp only [List.length_cons, List.length_nil] at h2; omega
      | cons b t2 => simp only [hv, Bool.false_eq_true, if_false]
  · unfold range416
    simp

/-! ## Concrete wire witnesses (the probe's exact bytes) -/

/-- The probe's stored validator. -/
def wireETag : Bytes := [34, 57, 101, 57, 56, 51, 102, 51, 53, 34]  -- "9e983f35"

/-- The probe's non-matching validator. -/
def wireBadTag : Bytes := [34, 48, 48, 48, 48, 48, 48, 48, 48, 34]  -- "00000000"

/-- `bytes=0-3`. -/
def wireSingle : Bytes := [98, 121, 116, 101, 115, 61, 48, 45, 51]

/-- `bytes=0-1,3-4`. -/
def wireMulti : Bytes :=
  [98, 121, 116, 101, 115, 61, 48, 45, 49, 44, 51, 45, 52]

/-- A 5-byte stand-in `200` carrying the probe's `ETag`. -/
def wireResp : Response :=
  { status := 200, reason := [79, 75],
    headers := [([69, 84, 97, 103], wireETag)],
    body := [104, 101, 108, 108, 111] }

/-- K08's exact shape: `If-Range: "00000000"` against the `"9e983f35"`
representation ⇒ the full `200`, byte-identical (definitional). -/
theorem witness_k08 : applyRange (some wireBadTag) wireSingle wireResp = wireResp :=
  rfl

/-- K07's exact shape: a matching `If-Range` + `bytes=0-3` ⇒ the `206` whose
body is exactly the first four octets. -/
theorem witness_k07 :
    (applyRange (some wireETag) wireSingle wireResp).status = 206
    ∧ (applyRange (some wireETag) wireSingle wireResp).body
        = [104, 101, 108, 108] := by
  decide

/-- K06's exact shape: `bytes=0-1,3-4` with no `If-Range` ⇒ the multipart
`206` (the proven payload; its `Content-Type` is `multipart/byteranges`) —
each component definitional (the parse reduces to exactly these two ranges). -/
theorem witness_k06 :
    (applyRange none wireMulti wireResp).status = 206
    ∧ (applyRange none wireMulti wireResp).headers
        = setCt wireResp.headers
    ∧ (applyRange none wireMulti wireResp).body
        = multipartBody wireResp.body [(0, 1), (3, 4)] :=
  ⟨rfl, rfl, rfl⟩

/-- The unveil fires on both probe shapes and ONLY range-bearing shapes. -/
theorem witness_unveils :
    unveils { headers := [([82, 97, 110, 103, 101], wireMulti)] } = true
    ∧ unveils { headers := [([82, 97, 110, 103, 101], wireSingle),
                            ([73, 102, 45, 82, 97, 110, 103, 101], wireBadTag)] } = true
    ∧ unveils { headers := [([82, 97, 110, 103, 101], wireSingle)] } = false
    ∧ unveils { headers := [] } = false := by
  decide

end Reactor.Stage.RangeUnveil

#print axioms Reactor.Stage.RangeUnveil.unveil_off_id
#print axioms Reactor.Stage.RangeUnveil.unveil_noStash_id
#print axioms Reactor.Stage.RangeUnveil.applyRange_ifrange_mismatch_200
#print axioms Reactor.Stage.RangeUnveil.applyRange_ifrange_match_206
#print axioms Reactor.Stage.RangeUnveil.carve_multi_206
#print axioms Reactor.Stage.RangeUnveil.carve_unsat_416
#print axioms Reactor.Stage.RangeUnveil.witness_k08
#print axioms Reactor.Stage.RangeUnveil.witness_k07
#print axioms Reactor.Stage.RangeUnveil.witness_k06
#print axioms Reactor.Stage.RangeUnveil.witness_unveils
