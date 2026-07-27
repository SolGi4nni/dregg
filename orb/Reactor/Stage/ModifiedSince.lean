import Reactor.Pipeline
import Reactor.Stage.CacheControl
import Proto.Kernel.Shortcuts

/-!
# Reactor.Stage.ModifiedSince — `Last-Modified` + `If-Modified-Since` (RFC 9110 §8.8.2 / §13.1.3)

Two byte-driving pipeline `Stage`s closing the date-validator gap on the static
asset surface. The deployed static handler answers `GET /static/…` with an
entity-tag validator (`ETag`, and it discharges `If-None-Match`) but NO date
validator: no `Last-Modified` on the `200`, and an `If-Modified-Since`
revalidation is silently ignored (wire capture 2026-07-13: `GET /static/app.js`
with `If-Modified-Since` is answered the full `200`). A cache that stored the
asset from an older origin (or a client with only the date validator) has no
revalidation path but the ETag. These stages close both halves:

* **`lmStampStage`** (response transform): stamp
  `Last-Modified: Mon, 01 Jan 2024 00:00:00 GMT` onto a static-`GET` `200` that
  does not already carry one — the SAME fixed epoch instant the deployed `Date`
  stage stamps, so `Last-Modified ≤ Date` holds on the wire (RFC 9110 §8.8.2.1:
  a recipient MUST treat a future modification date as the message origination
  date; equality is conformant and deterministic).
* **`msGateStage`** (request gate): a static-`GET` carrying
  `If-Modified-Since` EQUAL (byte-exact, OWS-trimmed) to the stamped validator —
  and no `If-None-Match` (RFC 9110 §13.1.3: an origin MUST ignore
  `If-Modified-Since` when the request carries `If-None-Match`) — is answered
  `304 (Not Modified)` carrying the validator, with an empty body.

EXACT-MATCH SEMANTICS (named): the gate revalidates by byte equality with the
deployed validator instant, not by HTTP-date ORDERING; a date other than the
validator is served the full `200` (conservative — never a stale `304`). The
date-ordering comparison is a named residual.

## What is proven here (pure kernel; no `native_decide`, no `ofReduceBool`)

* `msGate_fires` / `msGate_passes` — the gate's exact firing condition.
* `notModified_no_body` / `notModified_carries_validator` — the `304` shape
  (RFC 9110 §15.4.5: no content; §13.1.3: the validator on the refusal).
* `lmStamp_effect` / `lmStamp_noop_nonstatic` / `lmStamp_no_double` — the stamp
  fires exactly on the un-stamped static `200`.
* Both stages are status-stable; concrete non-vacuous witnesses by `decide`
  (through the `isStaticGet_lit` ASCII characterization).
-/

namespace Reactor.Stage.ModifiedSince

open Reactor.Pipeline
open Reactor (Response)
open Proto (Bytes)
open Reactor.Stage.CacheControl (isStaticGet)

/-! ## Field names and the deployed validator instant (explicit wire bytes —
kernel-reducible; each doc comment names the ASCII) -/

/-- Lowercase one ASCII byte. -/
def lowerByte (b : UInt8) : UInt8 := if 65 ≤ b && b ≤ 90 then b + 32 else b

/-- Lowercase a byte string (ASCII). -/
def lower (bs : Bytes) : Bytes := bs.map lowerByte

/-- `Last-Modified` (wire case, RFC 9110 §8.8.2). -/
def lmName : Bytes :=
  [76, 97, 115, 116, 45, 77, 111, 100, 105, 102, 105, 101, 100]

/-- `last-modified` (the case-insensitive probe). -/
def lmNameLower : Bytes :=
  [108, 97, 115, 116, 45, 109, 111, 100, 105, 102, 105, 101, 100]

/-- `if-modified-since` (the case-insensitive probe). -/
def imsNameLower : Bytes :=
  [105, 102, 45, 109, 111, 100, 105, 102, 105, 101, 100, 45, 115, 105, 110,
   99, 101]

/-- `if-none-match` (the case-insensitive probe — §13.1.3 precedence). -/
def inmNameLower : Bytes :=
  [105, 102, 45, 110, 111, 110, 101, 45, 109, 97, 116, 99, 104]

/-- **The deployed validator instant** — `Mon, 01 Jan 2024 00:00:00 GMT`,
byte-identical to the fixed epoch instant the deployed `Date` stage stamps on
every response, so the stamped `Last-Modified` never exceeds the message
`Date` on the wire. -/
def lmVal : Bytes :=
  [77, 111, 110, 44, 32, 48, 49, 32, 74, 97, 110, 32, 50, 48, 50, 52, 32,
   48, 48, 58, 48, 48, 58, 48, 48, 32, 71, 77, 84]

-- The literals are the strings they claim to be.
#guard lmName == "Last-Modified".toUTF8.toList
#guard lmNameLower == "last-modified".toUTF8.toList
#guard imsNameLower == "if-modified-since".toUTF8.toList
#guard inmNameLower == "if-none-match".toUTF8.toList
#guard lmVal == "Mon, 01 Jan 2024 00:00:00 GMT".toUTF8.toList

/-! ## The static scope, kernel-characterized -/

/-- `GET` as wire bytes. -/
theorem getMethod_lit : Reactor.Stage.CacheControl.getMethod = [71, 69, 84] := by
  show ("GET".toUTF8.toList : Bytes) = _
  rw [Proto.Kernel.Shortcuts.toUTF8_toList_ascii _ (by decide)]
  rfl

/-- `/static/` as wire bytes. -/
theorem staticPrefix_lit : Reactor.Stage.CacheControl.staticPrefix
    = [47, 115, 116, 97, 116, 105, 99, 47] := by
  show ("/static/".toUTF8.toList : Bytes) = _
  rw [Proto.Kernel.Shortcuts.toUTF8_toList_ascii _ (by decide)]
  rfl

/-- **The kernel-reducible characterization of the static scope** — the
`decide`-path form of `isStaticGet` (whose constants are `toUTF8` terms the
kernel does not reduce). -/
theorem isStaticGet_lit (c : Ctx) :
    isStaticGet c
      = (c.req.method == [71, 69, 84]
          && List.isPrefixOf [47, 115, 116, 97, 116, 105, 99, 47]
              c.req.target) := by
  show (c.req.method == Reactor.Stage.CacheControl.getMethod
    && Reactor.Stage.CacheControl.staticPrefix.isPrefixOf c.req.target) = _
  rw [getMethod_lit, staticPrefix_lit]

/-! ## The request-side reads -/

/-- Strip leading OWS (SP / HTAB). -/
def trimOWSLeft : Bytes → Bytes
  | [] => []
  | b :: rest => if b == 32 || b == 9 then trimOWSLeft rest else b :: rest

/-- Strip leading and trailing OWS (RFC 9110 §5.6.3). -/
def trimOWS (bs : Bytes) : Bytes :=
  trimOWSLeft ((trimOWSLeft bs.reverse).reverse)

/-- The request's `If-Modified-Since` value (first, case-insensitive name,
OWS-trimmed), if any. -/
def imsValOf (req : Proto.Request) : Option Bytes :=
  match req.headers.find? (fun nv => lower nv.1 == imsNameLower) with
  | some nv => some (trimOWS nv.2)
  | none => none

/-- Is the request carrying any `If-None-Match` (§13.1.3 precedence)? -/
def hasInm (req : Proto.Request) : Bool :=
  req.headers.any (fun nv => lower nv.1 == inmNameLower)

/-- Is the request carrying any `If-Modified-Since`? -/
def hasIms (req : Proto.Request) : Bool :=
  req.headers.any (fun nv => lower nv.1 == imsNameLower)

/-! ## The `304` gate -/

/-- The `304 (Not Modified)` refusal: no content (RFC 9110 §15.4.5), the date
validator on the refusal (§13.1.3). -/
def notModifiedResp : Response :=
  { status := 304
    reason := "Not Modified".toUTF8.toList
    headers := [(lmName, lmVal)]
    body := [] }

/-- **The firing condition**: a static `GET`, no `If-None-Match` (precedence),
and `If-Modified-Since` byte-equal to the deployed validator instant. -/
def fires (c : Ctx) : Bool :=
  isStaticGet c && !hasInm c.req && (imsValOf c.req == some lmVal)

/-- **The `If-Modified-Since` gate.** A firing revalidation is answered the
`304`; everything else passes through UNTOUCHED. -/
def msGateStage : Stage where
  name := "modified-since-304"
  onRequest := fun c => if fires c then .respond notModifiedResp else .continue c
  onResponse := fun _ b => b

theorem msGate_fires (c : Ctx) (h : fires c = true) :
    msGateStage.onRequest c = .respond notModifiedResp := by
  show (if fires c then StageStep.respond notModifiedResp
        else StageStep.continue c) = _
  rw [h]
  rfl

theorem msGate_passes (c : Ctx) (h : fires c = false) :
    msGateStage.onRequest c = .continue c := by
  show (if fires c then StageStep.respond notModifiedResp
        else StageStep.continue c) = _
  rw [h]
  rfl

/-- The gate's response phase is the identity. -/
theorem msGate_onResponse_id (c : Ctx) (b : ResponseBuilder) :
    msGateStage.onResponse c b = b := rfl

theorem msGate_statusStable : Stage.statusStable msGateStage :=
  fun _ _ => rfl

/-- A firing gate is scoped to the static surface. -/
theorem fires_scope (c : Ctx) (h : fires c = true) : isStaticGet c = true := by
  unfold fires at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.1

/-- Off the static surface the gate NEVER fires. -/
theorem fires_nonstatic (c : Ctx) (h : isStaticGet c = false) :
    fires c = false := by
  unfold fires
  rw [h, Bool.false_and, Bool.false_and]

/-- The `304` has no content (RFC 9110 §15.4.5). -/
theorem notModified_no_body : notModifiedResp.body = [] := rfl

/-- The `304` carries the date validator (RFC 9110 §13.1.3). -/
theorem notModified_carries_validator :
    (lmName, lmVal) ∈ notModifiedResp.headers := List.mem_singleton.mpr rfl

theorem notModified_status : notModifiedResp.status = 304 := rfl

/-! ## The `Last-Modified` stamp -/

/-- Does a header list already carry a `Last-Modified` (case-insensitive)? -/
def hasLm (hs : List (Bytes × Bytes)) : Bool :=
  hs.any (fun nv => lower nv.1 == lmNameLower)

/-- **The `Last-Modified` stamp.** On the response phase: a static-`GET` `200`
that does not already carry the validator gains it; everything else is the
identity. The request phase always passes. -/
def lmStampStage : Stage where
  name := "last-modified"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    if b.acc.status == 200 && isStaticGet c && !hasLm b.acc.headers then
      b.addHeader (lmName, lmVal)
    else b

theorem lmStamp_statusStable : Stage.statusStable lmStampStage := by
  intro c b
  show ((if b.acc.status == 200 && isStaticGet c && !hasLm b.acc.headers
         then b.addHeader (lmName, lmVal) else b).build).status = b.build.status
  split <;> rfl

/-- The stamp fires on the un-stamped static `200` — the validator lands in the
BUILT headers. -/
theorem lmStamp_effect (c : Ctx) (b : ResponseBuilder)
    (h200 : b.acc.status = 200) (hst : isStaticGet c = true)
    (hno : hasLm b.acc.headers = false) :
    (lmStampStage.onResponse c b).build
      = { b.build with headers := b.build.headers ++ [(lmName, lmVal)] } := by
  show (if b.acc.status == 200 && isStaticGet c && !hasLm b.acc.headers
        then b.addHeader (lmName, lmVal) else b).build = _
  rw [h200, hst, hno]
  rfl

/-- Off the static surface the stamp is the identity ON THE BUILDER. -/
theorem lmStamp_noop_nonstatic (c : Ctx) (b : ResponseBuilder)
    (hns : isStaticGet c = false) :
    lmStampStage.onResponse c b = b := by
  show (if b.acc.status == 200 && isStaticGet c && !hasLm b.acc.headers
        then b.addHeader (lmName, lmVal) else b) = b
  rw [hns, Bool.and_false, Bool.false_and]
  rfl

/-- Never a second validator: an already-stamped response is the identity. -/
theorem lmStamp_no_double (c : Ctx) (b : ResponseBuilder)
    (h : hasLm b.acc.headers = true) :
    lmStampStage.onResponse c b = b := by
  show (if b.acc.status == 200 && isStaticGet c && !hasLm b.acc.headers
        then b.addHeader (lmName, lmVal) else b) = b
  rw [h, Bool.not_true, Bool.and_false]
  rfl

/-! ## Non-vacuity (kernel `decide` on concrete bytes, through
`isStaticGet_lit`) -/

/-- `GET /static/app.js` with the exact validator — the gate fires.
(`If-Modified-Since` = `[73,102,45,…]`.) -/
def imsCtx : Ctx :=
  { input := []
    req := { method := [71, 69, 84]
             target := [47, 115, 116, 97, 116, 105, 99, 47, 97, 112, 112, 46,
                        106, 115]
             version := []
             headers := [([73, 102, 45, 77, 111, 100, 105, 102, 105, 101, 100,
               45, 83, 105, 110, 99, 101], lmVal)] }
    attrs := [] }

example : fires imsCtx = true := by
  unfold fires
  rw [isStaticGet_lit]
  decide

/-- The same request carrying `If-None-Match` too — §13.1.3 precedence: the
date gate stands down (`If-None-Match` = `[73,102,45,78,…]`, value `"x"`). -/
def imsInmCtx : Ctx :=
  { imsCtx with
    req := { imsCtx.req with
      headers := ([73, 102, 45, 78, 111, 110, 101, 45, 77, 97, 116, 99, 104],
          [34, 120, 34])
        :: imsCtx.req.headers } }

example : fires imsInmCtx = false := by
  unfold fires
  rw [isStaticGet_lit]
  decide

/-- A DIFFERENT date (`Tue, 02 Jan …`) — exact-match semantics: the full
response is served. -/
def imsOtherCtx : Ctx :=
  { imsCtx with
    req := { imsCtx.req with
      headers := [([73, 102, 45, 77, 111, 100, 105, 102, 105, 101, 100, 45,
        83, 105, 110, 99, 101],
        [84, 117, 101, 44, 32, 48, 50, 32, 74, 97, 110, 32, 50, 48, 50, 52,
         32, 48, 48, 58, 48, 48, 58, 48, 48, 32, 71, 77, 84])] } }

example : fires imsOtherCtx = false := by
  unfold fires
  rw [isStaticGet_lit]
  decide

/-- Off the static surface (the same header on `/bulk`): never fires. -/
def imsBulkCtx : Ctx :=
  { imsCtx with
    req := { imsCtx.req with target := [47, 98, 117, 108, 107] } }

example : fires imsBulkCtx = false := by
  unfold fires
  rw [isStaticGet_lit]
  decide

end Reactor.Stage.ModifiedSince

#print axioms Reactor.Stage.ModifiedSince.msGate_fires
#print axioms Reactor.Stage.ModifiedSince.lmStamp_effect
#print axioms Reactor.Stage.ModifiedSince.lmStamp_noop_nonstatic
#print axioms Reactor.Stage.ModifiedSince.isStaticGet_lit
