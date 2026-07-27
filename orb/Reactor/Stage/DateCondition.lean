import Reactor.Pipeline
import Reactor.Stage.ConditionalRequest
import Reactor.Stage.HttpDateOrder

/-!
# Reactor.Stage.DateCondition — the date conditionals by TOTAL ORDER
(RFC 9110 §13.1.3 / §13.1.4)

The full RFC battery holds two date-conditional MUSTs the deployed serve
violates even once a `Last-Modified` stamp exists:

* **J09 — `If-Modified-Since` at/after the representation's date ⇒ `304`
  (§13.1.3 MUST).** An exact-byte revalidation (the stamp stage's named
  residual) only answers a client that echoes the served date verbatim; the
  RFC verdict is an HTTP-date ORDER comparison — `Sat, 01 Jan 2050 …` after a
  2024 representation date is `304`, whatever bytes the server once served.
* **J11 — `If-Unmodified-Since` before the representation's date ⇒ `412`
  (§13.1.4 MUST).** Not implemented at all.

This stage closes both through `Reactor.Stage.HttpDateOrder`'s total-order
scalar, and takes the representation's date FROM THE RESPONSE — it parses the
finalized response's own `Last-Modified` header (stamped by the inner fold),
so the comparison date and the wire date can never disagree, and the stage
composes over ANY fold that stamps a date (no constant duplicated here).

## Precedence (§13.2.2, proven by construction)

* `If-Unmodified-Since` is evaluated only when NO `If-Match` is present.
* `If-Modified-Since` is evaluated only when NO `If-None-Match` is present
  (J12: a non-matching `If-None-Match` beats a far-future IMS ⇒ `200`).
* Both fire only on a `200` whose `Last-Modified` parses as an IMF-fixdate;
  a malformed request date parses to `none` and never fires (§13.1.3
  MUST-ignore). Everything else — gate refusals, an inner `304`/`412`, an
  undated or obsolete-dated response — passes through VERBATIM.
* Requests carrying NEITHER date conditional are builder-identical BY
  CONSTRUCTION (`dateCond_offHeaders_id` — the dense-arm collapse hook).

## What is proven (pure kernel; no `native_decide`)

* `dcRewrite_ius_412` / `dcRewrite_ims_304` — the two verdicts, general.
* `ims_precedence_inm` / `ius_precedence_ifmatch` — §13.2.2 by construction.
* `dcRewrite_not200` / `dcRewrite_undated` / `dateCond_offHeaders_id` — the
  guards.
* Concrete witnesses on the probe's exact bytes against the deployed stamp
  date (`Mon, 01 Jan 2024 00:00:00 GMT`): IMS 2050 ⇒ `304`; IMS 1970 ⇒ pass
  (J10); IUS 1970 ⇒ `412`; INM+IMS-2050 ⇒ pass (J12).
-/

namespace Reactor.Stage.DateCondition

open Reactor.Pipeline
open Reactor (Response)
open Proto (Bytes)
open Reactor.Stage.ConditionalRequest (headerVal ifMatchNameLower
  ifNoneMatchNameLower notModifiedOf preconditionFailedOf)
open Reactor.Stage.HttpDateOrder (dateVal encode)

/-! ## Tokens -/

/-- `if-modified-since` (lowercase). -/
def imsNameLower : Bytes :=
  [105, 102, 45, 109, 111, 100, 105, 102, 105, 101, 100, 45, 115, 105, 110,
   99, 101]

/-- `if-unmodified-since` (lowercase). -/
def iusNameLower : Bytes :=
  [105, 102, 45, 117, 110, 109, 111, 100, 105, 102, 105, 101, 100, 45, 115,
   105, 110, 99, 101]

/-- `last-modified` (lowercase — the response-side validator this stage
compares against). -/
def lastModifiedNameLower : Bytes :=
  [108, 97, 115, 116, 45, 109, 111, 100, 105, 102, 105, 101, 100]

/-! ## The verdicts -/

/-- The response's own representation date, as the order scalar: its
`Last-Modified` header parsed as an IMF-fixdate (`none` if absent or not a
fixdate — fail-closed, no verdict fires). -/
def respLastModScalar (resp : Response) : Option Nat :=
  (headerVal lastModifiedNameLower resp.headers).bind dateVal

/-- **§13.1.4 — `If-Unmodified-Since` fails** against the representation date
`lm`: no `If-Match` present (§13.2.2 step 1 owns the decision otherwise), the
header parses as an HTTP-date, and the representation was modified AFTER it. -/
def iusFails (req : Proto.Request) (lm : Nat) : Bool :=
  (headerVal ifMatchNameLower req.headers).isNone
    && match (headerVal iusNameLower req.headers).bind dateVal with
       | some t => decide (t < lm)
       | none => false

/-- **§13.1.3 — `If-Modified-Since` says unmodified**: no `If-None-Match`
present (§13.2.2 step 3 owns the decision otherwise), the header parses, and
the representation has NOT been modified since (`lm ≤ ims` in the total
order). -/
def imsUnmodified (req : Proto.Request) (lm : Nat) : Bool :=
  (headerVal ifNoneMatchNameLower req.headers).isNone
    && match (headerVal imsNameLower req.headers).bind dateVal with
       | some t => decide (lm ≤ t)
       | none => false

/-- The request carries at least one date conditional (the stage's scope —
everything else is builder-identical by construction). -/
def hasDateCond (req : Proto.Request) : Bool :=
  (headerVal imsNameLower req.headers).isSome
    || (headerVal iusNameLower req.headers).isSome

/-! ## The rewrite -/

/-- **The date-conditional rewrite.** Only a dated `200` is conditioned: IUS
first (§13.2.2 evaluates step 2 before step 4), then IMS, else verbatim. -/
def dcRewrite (req : Proto.Request) (resp : Response) : Response :=
  if resp.status == 200 then
    match respLastModScalar resp with
    | some lm =>
      if iusFails req lm then preconditionFailedOf resp
      else if imsUnmodified req lm then notModifiedOf resp
      else resp
    | none => resp
  else resp

/-! ## The stage -/

/-- **The date-conditional stage.** Passes the request phase; on the response
phase applies `dcRewrite` — scoped BY CONSTRUCTION to requests carrying a
date conditional (everything else is builder-identical). -/
def dateCondStage : Stage where
  name := "date-condition"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    if hasDateCond c.req then b.mapResp (dcRewrite c.req) else b

/-! ## Rewrite theorems -/

/-- Guard — a non-`200` (gate refusal, inner `304`/`412`) is untouched. -/
theorem dcRewrite_not200 (req : Proto.Request) (resp : Response)
    (h : (resp.status == 200) = false) : dcRewrite req resp = resp := by
  unfold dcRewrite
  rw [h]
  simp

/-- Guard — a `200` with no (parseable) `Last-Modified` is untouched. -/
theorem dcRewrite_undated (req : Proto.Request) (resp : Response)
    (h200 : (resp.status == 200) = true) (hd : respLastModScalar resp = none) :
    dcRewrite req resp = resp := by
  unfold dcRewrite
  rw [h200, hd]
  simp

/-- **J11 (§13.1.4 MUST).** A failing `If-Unmodified-Since` on a dated `200`
⇒ the `412 Precondition Failed`. -/
theorem dcRewrite_ius_412 (req : Proto.Request) (resp : Response) (lm : Nat)
    (h200 : (resp.status == 200) = true) (hd : respLastModScalar resp = some lm)
    (hf : iusFails req lm = true) :
    dcRewrite req resp = preconditionFailedOf resp := by
  unfold dcRewrite
  rw [h200, hd]
  simp [hf]

/-- **J09 (§13.1.3 MUST).** An at-or-after `If-Modified-Since` on a dated
`200` (IUS not failing) ⇒ the `304`, body stripped, validators kept. -/
theorem dcRewrite_ims_304 (req : Proto.Request) (resp : Response) (lm : Nat)
    (h200 : (resp.status == 200) = true) (hd : respLastModScalar resp = some lm)
    (hi : iusFails req lm = false) (hm : imsUnmodified req lm = true) :
    dcRewrite req resp = notModifiedOf resp := by
  unfold dcRewrite
  rw [h200, hd]
  simp [hi, hm]

/-- The pass branch: neither verdict fires ⇒ the `200` verbatim. -/
theorem dcRewrite_passes (req : Proto.Request) (resp : Response) (lm : Nat)
    (h200 : (resp.status == 200) = true) (hd : respLastModScalar resp = some lm)
    (hi : iusFails req lm = false) (hm : imsUnmodified req lm = false) :
    dcRewrite req resp = resp := by
  unfold dcRewrite
  rw [h200, hd]
  simp [hi, hm]

/-- **J12 (§13.2.2 MUST) — precedence by construction.** ANY request carrying
an `If-None-Match` has IMS disabled (the entity-tag verdict — owned by
`ConditionalRequest` — decides alone). -/
theorem ims_precedence_inm (req : Proto.Request) (lm : Nat)
    (h : (headerVal ifNoneMatchNameLower req.headers).isNone = false) :
    imsUnmodified req lm = false := by
  unfold imsUnmodified
  rw [h]
  simp

/-- §13.2.2 step 1 over step 2: `If-Match` presence disables IUS. -/
theorem ius_precedence_ifmatch (req : Proto.Request) (lm : Nat)
    (h : (headerVal ifMatchNameLower req.headers).isNone = false) :
    iusFails req lm = false := by
  unfold iusFails
  rw [h]
  simp

/-! ## Stage guards (the collapse hooks) -/

/-- A request with NEITHER date conditional passes the response phase
builder-IDENTICALLY (the dense-arm hook — head-sized, decidable). -/
theorem dateCond_offHeaders_id (c : Ctx) (b : ResponseBuilder)
    (h : hasDateCond c.req = false) : dateCondStage.onResponse c b = b := by
  show (if hasDateCond c.req then b.mapResp (dcRewrite c.req) else b) = b
  rw [h]
  simp

/-- The request phase always passes, context untouched. -/
theorem dateCond_onRequest (c : Ctx) :
    dateCondStage.onRequest c = StageStep.continue c := rfl

/-! ## Concrete wire witnesses (the probe's exact bytes, against the deployed
stamp date `Mon, 01 Jan 2024 00:00:00 GMT` — explicit ASCII, kernel-reduced) -/

/-- `If-Modified-Since` (wire case). -/
def imsWireName : Bytes :=
  [73, 102, 45, 77, 111, 100, 105, 102, 105, 101, 100, 45, 83, 105, 110, 99, 101]

/-- `If-Unmodified-Since` (wire case). -/
def iusWireName : Bytes :=
  [73, 102, 45, 85, 110, 109, 111, 100, 105, 102, 105, 101, 100, 45, 83,
   105, 110, 99, 101]

/-- `If-None-Match` (wire case). -/
def inmWireName : Bytes := [73, 102, 45, 78, 111, 110, 101, 45, 77, 97, 116, 99, 104]

/-- `Mon, 01 Jan 2024 00:00:00 GMT` — the deployed stamp's exact bytes. -/
def wireLm : Bytes :=
  [77, 111, 110, 44, 32, 48, 49, 32, 74, 97, 110, 32, 50, 48, 50, 52, 32,
   48, 48, 58, 48, 48, 58, 48, 48, 32, 71, 77, 84]

/-- The stamp date's scalar (the parse round-trips). -/
theorem wireLm_parses : dateVal wireLm = some (encode 2024 1 1 0 0 0) := by
  decide

/-- IMS 2050 against the 2024 representation ⇒ the `304` verdict fires. -/
theorem witness_ims_future :
    imsUnmodified { headers :=
      [(imsWireName, Reactor.Stage.HttpDateOrder.wireFuture)] }
      (encode 2024 1 1 0 0 0) = true := by
  decide

/-- IMS 1970 ⇒ no verdict (J10: the body is served). -/
theorem witness_ims_past :
    imsUnmodified { headers :=
      [(imsWireName, Reactor.Stage.HttpDateOrder.wirePast)] }
      (encode 2024 1 1 0 0 0) = false := by
  decide

/-- IUS 1970 against the 2024 representation ⇒ the `412` verdict fires. -/
theorem witness_ius_past :
    iusFails { headers :=
      [(iusWireName, Reactor.Stage.HttpDateOrder.wirePast)] }
      (encode 2024 1 1 0 0 0) = true := by
  decide

/-- J12's exact shape: `If-None-Match: "deadbeef"` + IMS 2050 ⇒ IMS DISABLED
(the non-matching entity-tag verdict alone decides ⇒ `200`). -/
theorem witness_inm_over_ims :
    imsUnmodified { headers :=
      [(inmWireName, [34, 100, 101, 97, 100, 98, 101, 101, 102, 34]),
       (imsWireName, Reactor.Stage.HttpDateOrder.wireFuture)] }
      (encode 2024 1 1 0 0 0) = false := by
  decide

/-- The whole rewrite on a concrete dated `200`: IMS 2050 ⇒ `304` + empty
body; IUS 1970 ⇒ `412` (definitional — the full decision path reduces). -/
theorem witness_rewrite :
    (dcRewrite { headers := [(imsWireName, Reactor.Stage.HttpDateOrder.wireFuture)] }
      { status := 200, reason := [79, 75],
        headers := [([76, 97, 115, 116, 45, 77, 111, 100, 105, 102, 105, 101, 100],
                     wireLm)],
        body := [104, 105] }).status = 304
    ∧ (dcRewrite { headers := [(imsWireName, Reactor.Stage.HttpDateOrder.wireFuture)] }
        { status := 200, reason := [79, 75],
          headers := [([76, 97, 115, 116, 45, 77, 111, 100, 105, 102, 105, 101, 100],
                       wireLm)],
          body := [104, 105] }).body = []
    ∧ (dcRewrite { headers := [(iusWireName, Reactor.Stage.HttpDateOrder.wirePast)] }
        { status := 200, reason := [79, 75],
          headers := [([76, 97, 115, 116, 45, 77, 111, 100, 105, 102, 105, 101, 100],
                       wireLm)],
          body := [104, 105] }).status = 412 := by
  decide

end Reactor.Stage.DateCondition

#print axioms Reactor.Stage.DateCondition.dcRewrite_ius_412
#print axioms Reactor.Stage.DateCondition.dcRewrite_ims_304
#print axioms Reactor.Stage.DateCondition.ims_precedence_inm
#print axioms Reactor.Stage.DateCondition.dateCond_offHeaders_id
#print axioms Reactor.Stage.DateCondition.witness_ims_future
#print axioms Reactor.Stage.DateCondition.witness_ius_past
#print axioms Reactor.Stage.DateCondition.witness_inm_over_ims
#print axioms Reactor.Stage.DateCondition.witness_rewrite
