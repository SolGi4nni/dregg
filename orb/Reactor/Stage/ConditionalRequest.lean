import Reactor.Stage.FramingValidation

/-!
# Reactor.Stage.ConditionalRequest — the precondition finisher (If-None-Match / If-Match)

The wave-5 EXTENDED RFC conformance probe (`docs/engine/review/CONFORMANCE-EXT.md`,
`conformance/rfc_conformance_ext.py`) found the deployed serve advertises an `ETag`
validator (H0 PASS) but acts on NO precondition — four RFC 7232 MUSTs violated, all
at the RESPONSE funnel (the ETag is already computed by `inner`; this stage compares
it against the request's precondition headers and rewrites the status):

* **H1 — If-None-Match matches ⇒ 304 (RFC 7232 §3.2, MUST).** A `GET`/`HEAD` whose
  `If-None-Match` lists the current representation's `ETag` MUST get `304 Not
  Modified` (the revalidation win — no re-shipping the body). Deployed: `200`.
* **H2 — 304 MUST NOT carry a body (RFC 7232 §4.1, MUST).** A produced `304` strips
  the body octets. Deployed: `200` full body (H2 had nothing to hold because no
  `304` was ever produced; producing one with an empty body satisfies both).
* **H3 — If-None-Match: * ⇒ 304 (RFC 7232 §3.2, MUST).** `*` matches ANY current
  representation (here: the resource exists ⇔ the response carries an `ETag`).
* **H5 — If-Match non-matching ⇒ 412 (RFC 7232 §3.1, MUST).** A `If-Match` whose
  listed tags do NOT include the current `ETag` MUST get `412 Precondition Failed`
  (optimistic-concurrency contract). Deployed: `200`.

**H4 stays correct (non-vacuously).** `If-Match` that DOES match proceeds with the
method → `200` (never `304`). The probe's H4 asserts exactly this; this stage keeps
it — `ifMatchFails = false` on a match, so the `412` branch is skipped, and with no
`If-None-Match` the response passes through `200`.

## Placement (funnel finisher, guarded)

Runs on the RESPONSE phase (like `Reactor.Stage.DateHeader`): `onRequest` passes,
`onResponse` rewrites the built response via one affine `mapResp`. It only fires on
a **`200`** response that **carries an `ETag`** — so a `4xx/5xx` gate short-circuit
(a `400`/`404`/`417` from `RequestValidation`/`FramingValidation`) flows through
UNTOUCHED (`conditionalRewrite` returns it unchanged), and a `200` with no validator
is untouched too. That guard is what makes it safe to place anywhere in the onion.

## What is proven (headline, non-vacuous on concrete witnesses)

* `conditionalRewrite_ifNoneMatch` — `200` + ETag + `If-None-Match` match ⇒ the
  `304` (status `304`, body `[]` — H1 + H2 in one).
* `conditionalRewrite_ifMatchFails` — `200` + ETag + `If-Match` no-match ⇒ the `412`.
* `conditionalRewrite_passes` — `200` + ETag, preconditions satisfied ⇒ unchanged.
* `conditionalRewrite_not200` / `conditionalRewrite_noEtag` — the guard: a non-`200`
  or validator-less response is returned verbatim (safety over gate short-circuits).
* `conditionalStage_effect` — the pipeline hook: the built output is
  `conditionalRewrite c.req` of the inner pipeline's built response, for ANY tail.
* Concrete witnesses on the probe's exact bytes (`ETag: "9e983f35"`,
  `If-None-Match: "9e983f35"` / `*`, `If-Match: "00000000"` / matching): `304`+empty,
  `412`, and the H4 `200` pass-through — each a `by decide` on explicit bytes.

Every guard fact is `by decide` on explicit ASCII byte lists (no `native_decide`).
-/

namespace Reactor.Stage.ConditionalRequest

open Reactor.Pipeline
open Proto (Bytes Request)
open Reactor.Stage.RequestValidation (strBytes)
open Reactor.Stage.FramingValidation (lowerBytes trimOWS splitOn bCOMMA)

/-! ## Tokens (lowercase field-names + the wildcard) -/

/-- `etag` (lowercase — the response validator field-name, matched case-insensitively). -/
def etagNameLower : Bytes := [101, 116, 97, 103]
/-- `if-none-match` (lowercase). -/
def ifNoneMatchNameLower : Bytes :=
  [105, 102, 45, 110, 111, 110, 101, 45, 109, 97, 116, 99, 104]
/-- `if-match` (lowercase). -/
def ifMatchNameLower : Bytes := [105, 102, 45, 109, 97, 116, 99, 104]
/-- `*` — the any-representation wildcard. -/
def star : Bytes := [42]
/-- `W/` — the weak-validator prefix (RFC 7232 §2.3). -/
def weakPrefix : Bytes := [87, 47]

/-! ## Reading the validators -/

/-- The (OWS-trimmed) value of the first header whose name lower-cases to `nameLower`. -/
def headerVal (nameLower : Bytes) (hs : List (Bytes × Bytes)) : Option Bytes :=
  (hs.find? (fun kv => lowerBytes kv.1 == nameLower)).map (fun kv => trimOWS kv.2)

/-- The current representation's `ETag` (from the response), OWS-trimmed. -/
def respETag (resp : Response) : Option Bytes := headerVal etagNameLower resp.headers

/-- Strip a leading `W/` weak marker (RFC 7232 §2.3.2). The response ETag here is
strong; stripping is harmless and lets a `W/`-prefixed request tag compare. -/
def stripWeak (t : Bytes) : Bytes :=
  if weakPrefix.isPrefixOf t then t.drop 2 else t

/-- One precondition entity-tag matches the current `ETag`: the `*` wildcard, or a
byte-equal tag (weak marker stripped from both sides). -/
def tagMatches (etag t : Bytes) : Bool :=
  t == star || stripWeak t == stripWeak etag

/-- Split a precondition header value into its list of OWS-trimmed entity-tags. -/
def condTags (v : Bytes) : List Bytes := (splitOn bCOMMA v).map trimOWS

/-- **If-None-Match matches** (H1/H3): the header is present and some listed tag (or
`*`) matches the current `ETag`. Absent ⇒ not a match (the precondition is vacuously
true and the method proceeds). -/
def ifNoneMatchMatches (req : Request) (etag : Bytes) : Bool :=
  match headerVal ifNoneMatchNameLower req.headers with
  | none => false
  | some v => (condTags v).any (fun t => tagMatches etag t)

/-- **If-Match fails** (H5): the header is present and NONE of its listed tags (nor
`*`) matches the current `ETag`. Absent ⇒ does not fail (method proceeds). -/
def ifMatchFails (req : Request) (etag : Bytes) : Bool :=
  match headerVal ifMatchNameLower req.headers with
  | none => false
  | some v => !((condTags v).any (fun t => tagMatches etag t))

/-! ## The precondition responses -/

/-- `304 Not Modified` — keeps the representation-metadata headers (ETag, …), strips
the body (H2: a `304` MUST NOT carry a message body, RFC 7232 §4.1). -/
def notModifiedOf (resp : Response) : Response :=
  { resp with status := 304, reason := strBytes "Not Modified", body := [] }

/-- `412 Precondition Failed` — the `If-Match` refusal (H5, RFC 7232 §4.2). -/
def preconditionFailedOf (resp : Response) : Response :=
  { status := 412, reason := strBytes "Precondition Failed"
    headers := resp.headers, body := strBytes "precondition failed\n" }

theorem notModifiedOf_status (resp : Response) : (notModifiedOf resp).status = 304 := rfl
theorem notModifiedOf_body (resp : Response) : (notModifiedOf resp).body = [] := rfl
theorem preconditionFailedOf_status (resp : Response) :
    (preconditionFailedOf resp).status = 412 := rfl

/-! ## The rewrite -/

/-- **The precondition rewrite.** Only a `200` response CARRYING an `ETag` is
conditioned; `If-Match` is evaluated first (`412` on failure), then `If-None-Match`
(`304` on match, body stripped). Anything else (non-`200`, no validator, no
precondition, or a satisfied precondition) is returned VERBATIM — so this is safe to
run over a gate short-circuit or an unconditioned `200`. -/
def conditionalRewrite (req : Request) (resp : Response) : Response :=
  if resp.status == 200 then
    match respETag resp with
    | none => resp
    | some etag =>
        if ifMatchFails req etag then preconditionFailedOf resp
        else if ifNoneMatchMatches req etag then notModifiedOf resp
        else resp
  else resp

/-! ## The stage -/

/-- **The conditional-request finisher.** Passes the request phase; on the response
phase applies `conditionalRewrite` to the built response via one affine `mapResp`. -/
def conditionalStage : Stage where
  name := "conditional-request"
  onRequest := fun c => .continue c
  onResponse := fun c b => b.mapResp (conditionalRewrite c.req)

/-! ## Rewrite theorems (general, then witnessed) -/

/-- **Guard — non-`200`.** A non-`200` response passes through unchanged (a gate
short-circuit — `400`/`404`/`417` — is untouched). -/
theorem conditionalRewrite_not200 (req : Request) (resp : Response)
    (h : (resp.status == 200) = false) : conditionalRewrite req resp = resp := by
  show (if resp.status == 200 then _ else resp) = _
  rw [h]; simp only [Bool.false_eq_true, if_false]

/-- **Guard — no validator.** A `200` with no `ETag` passes through unchanged. -/
theorem conditionalRewrite_noEtag (req : Request) (resp : Response)
    (h200 : (resp.status == 200) = true) (he : respETag resp = none) :
    conditionalRewrite req resp = resp := by
  show (if resp.status == 200 then
          (match respETag resp with | none => resp | some etag => _)
        else resp) = _
  rw [h200, he]; simp only [if_true]

/-- **H5.** `200` + ETag + `If-Match` non-matching ⇒ the `412`. -/
theorem conditionalRewrite_ifMatchFails (req : Request) (resp : Response) (etag : Bytes)
    (h200 : (resp.status == 200) = true) (he : respETag resp = some etag)
    (hm : ifMatchFails req etag = true) :
    conditionalRewrite req resp = preconditionFailedOf resp := by
  simp only [conditionalRewrite, h200, he, hm, if_true]

/-- **H1 / H3.** `200` + ETag + `If-Match` NOT failing + `If-None-Match` matching ⇒
the `304` (status `304`, body `[]`). -/
theorem conditionalRewrite_ifNoneMatch (req : Request) (resp : Response) (etag : Bytes)
    (h200 : (resp.status == 200) = true) (he : respETag resp = some etag)
    (hm : ifMatchFails req etag = false) (hn : ifNoneMatchMatches req etag = true) :
    conditionalRewrite req resp = notModifiedOf resp := by
  simp only [conditionalRewrite, h200, he, hm, hn, Bool.false_eq_true, if_false, if_true]

/-- **H4 pass-through.** `200` + ETag with a satisfied `If-Match` (not failing) and no
`If-None-Match` match ⇒ the `200` passes unchanged (H4: a matching `If-Match`
proceeds, never `304`). -/
theorem conditionalRewrite_passes (req : Request) (resp : Response) (etag : Bytes)
    (h200 : (resp.status == 200) = true) (he : respETag resp = some etag)
    (hm : ifMatchFails req etag = false) (hn : ifNoneMatchMatches req etag = false) :
    conditionalRewrite req resp = resp := by
  simp only [conditionalRewrite, h200, he, hm, hn, Bool.false_eq_true, if_false, if_true]

/-! ## The pipeline hook -/

/-- **The response-effect hook.** `conditionalStage` always passes, so the built
pipeline output is `conditionalRewrite c.req` applied to the inner pipeline's built
response — for ANY tail and handler. A concrete precondition rewrite (`304`/`412`)
composed with a concrete inner response then follows from the rewrite theorems. -/
theorem conditionalStage_effect (rest : List Stage) (handler : Ctx → Response) (c : Ctx) :
    ((runPipeline (conditionalStage :: rest) handler c).build)
      = conditionalRewrite c.req ((runPipeline rest handler c).build) := by
  rw [pipeline_stage_effect conditionalStage rest handler c c rfl]
  show ((runPipeline rest handler c).mapResp (conditionalRewrite c.req)).build = _
  rw [build_mapResp]

/-! ## Concrete non-vacuity witnesses (the probe's exact bytes) -/

/-- `/health`-style origin target. -/ def hpath : Bytes := [47, 104, 101, 97, 108, 116, 104]
/-- `HTTP/1.1`. -/ def v11 : Bytes := [72, 84, 84, 80, 47, 49, 46, 49]
/-- `GET`. -/ def mGET : Bytes := [71, 69, 84]
/-- `Host`. -/ def hostName : Bytes := [72, 111, 115, 116]

/-- `ETag` (response field-name, as emitted). -/
def etagNameWire : Bytes := [69, 84, 97, 103]
/-- `If-None-Match` (request field-name, as sent). -/
def ifNoneMatchWire : Bytes := [73, 102, 45, 78, 111, 110, 101, 45, 77, 97, 116, 99, 104]
/-- `If-Match` (request field-name, as sent). -/
def ifMatchWire : Bytes := [73, 102, 45, 77, 97, 116, 99, 104]

/-- The static asset's live validator `"9e983f35"` (the probe's exact ETag bytes,
quotes included). -/
def etag9e : Bytes := [34, 57, 101, 57, 56, 51, 102, 51, 53, 34]
/-- A non-matching validator `"00000000"` (the probe's H5 If-Match value). -/
def etag00 : Bytes := [34, 48, 48, 48, 48, 48, 48, 48, 48, 34]

/-- The inner serve's `200` static response carrying the `ETag` validator. -/
def base200 : Response :=
  { status := 200, reason := strBytes "OK"
    headers := [(etagNameWire, etag9e)], body := strBytes "hello, world\n" }

/-- The same representation returned with a `404` (a gate short-circuit shape — no
`200`, so the finisher must leave it alone). -/
def base404 : Response :=
  { status := 404, reason := strBytes "Not Found"
    headers := [(etagNameWire, etag9e)], body := strBytes "not found\n" }

/-- **H1 request.** `If-None-Match: "9e983f35"` (matches). -/
def reqINM : Request :=
  { method := mGET, target := hpath, version := v11
    headers := [(hostName, [120]), (ifNoneMatchWire, etag9e)] }

/-- **H3 request.** `If-None-Match: *`. -/
def reqINMStar : Request :=
  { method := mGET, target := hpath, version := v11
    headers := [(hostName, [120]), (ifNoneMatchWire, star)] }

/-- **H5 request.** `If-Match: "00000000"` (non-matching). -/
def reqIMno : Request :=
  { method := mGET, target := hpath, version := v11
    headers := [(hostName, [120]), (ifMatchWire, etag00)] }

/-- **H4 request.** `If-Match: "9e983f35"` (matching — must proceed 200). -/
def reqIMyes : Request :=
  { method := mGET, target := hpath, version := v11
    headers := [(hostName, [120]), (ifMatchWire, etag9e)] }

/-- A plain conditional-free request (must pass 200 unchanged). -/
def reqPlain : Request :=
  { method := mGET, target := hpath, version := v11, headers := [(hostName, [120])] }

/-! ### The guard facts (`decide` — reduces on explicit bytes) -/

theorem base200_status : (base200.status == 200) = true := by decide
theorem base404_status : (base404.status == 200) = false := by decide
theorem base200_etag : respETag base200 = some etag9e := by decide

theorem reqINM_inm : ifNoneMatchMatches reqINM etag9e = true := by decide
theorem reqINM_im_ok : ifMatchFails reqINM etag9e = false := by decide
theorem reqStar_inm : ifNoneMatchMatches reqINMStar etag9e = true := by decide
theorem reqStar_im_ok : ifMatchFails reqINMStar etag9e = false := by decide
theorem reqIMno_fails : ifMatchFails reqIMno etag9e = true := by decide
theorem reqIMyes_ok : ifMatchFails reqIMyes etag9e = false := by decide
theorem reqIMyes_inm_no : ifNoneMatchMatches reqIMyes etag9e = false := by decide
theorem reqPlain_im_ok : ifMatchFails reqPlain etag9e = false := by decide
theorem reqPlain_inm_no : ifNoneMatchMatches reqPlain etag9e = false := by decide

/-! ### The rewrite genuinely fires on each witness -/

/-- **H1 + H2.** `If-None-Match: "9e983f35"` on the `200`/ETag response ⇒ `304`,
body stripped. -/
theorem reqINM_304 : conditionalRewrite reqINM base200 = notModifiedOf base200 :=
  conditionalRewrite_ifNoneMatch reqINM base200 etag9e base200_status base200_etag
    reqINM_im_ok reqINM_inm

/-- **H3.** `If-None-Match: *` ⇒ `304`. -/
theorem reqStar_304 : conditionalRewrite reqINMStar base200 = notModifiedOf base200 :=
  conditionalRewrite_ifNoneMatch reqINMStar base200 etag9e base200_status base200_etag
    reqStar_im_ok reqStar_inm

/-- **H5.** `If-Match: "00000000"` (no match) ⇒ `412`. -/
theorem reqIMno_412 : conditionalRewrite reqIMno base200 = preconditionFailedOf base200 :=
  conditionalRewrite_ifMatchFails reqIMno base200 etag9e base200_status base200_etag reqIMno_fails

/-- **H4.** `If-Match: "9e983f35"` (match) ⇒ the `200` proceeds unchanged (never `304`). -/
theorem reqIMyes_200 : conditionalRewrite reqIMyes base200 = base200 :=
  conditionalRewrite_passes reqIMyes base200 etag9e base200_status base200_etag
    reqIMyes_ok reqIMyes_inm_no

/-- A conditional-free request passes through `200` unchanged. -/
theorem reqPlain_200 : conditionalRewrite reqPlain base200 = base200 :=
  conditionalRewrite_passes reqPlain base200 etag9e base200_status base200_etag
    reqPlain_im_ok reqPlain_inm_no

/-- **Safety.** The SAME matching `If-None-Match` over a `404` (gate short-circuit)
leaves it untouched — the finisher never turns a refusal into a `304`. -/
theorem reqINM_over_404_untouched : conditionalRewrite reqINM base404 = base404 :=
  conditionalRewrite_not200 reqINM base404 base404_status

/-- **Non-vacuity contrast.** The same finisher answers `304` / `412` on the
matching-INM / failing-IM requests but `200` on the plain one — it discriminates. -/
theorem finisher_discriminates :
    ((conditionalRewrite reqINM base200).status = 304)
    ∧ ((conditionalRewrite reqINM base200).body = [])
    ∧ ((conditionalRewrite reqIMno base200).status = 412)
    ∧ ((conditionalRewrite reqIMyes base200).status = 200)
    ∧ ((conditionalRewrite reqPlain base200).status = 200) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### Executable sanity checks (evaluate on real bytes) -/

#guard (conditionalRewrite reqINM base200).status == 304
#guard (conditionalRewrite reqINM base200).body == []
#guard (conditionalRewrite reqINMStar base200).status == 304
#guard (conditionalRewrite reqIMno base200).status == 412
#guard (conditionalRewrite reqIMyes base200).status == 200
#guard (conditionalRewrite reqPlain base200).status == 200
#guard (conditionalRewrite reqINM base404).status == 404

/-! ## Axiom audit -/

#print axioms conditionalRewrite_not200
#print axioms conditionalRewrite_noEtag
#print axioms conditionalRewrite_ifMatchFails
#print axioms conditionalRewrite_ifNoneMatch
#print axioms conditionalRewrite_passes
#print axioms conditionalStage_effect
#print axioms reqINM_304
#print axioms reqStar_304
#print axioms reqIMno_412
#print axioms reqIMyes_200
#print axioms reqINM_over_404_untouched
#print axioms finisher_discriminates

end Reactor.Stage.ConditionalRequest
