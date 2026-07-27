import Reactor.Stage.FramingValidation

/-!
# Reactor.Stage.ContentLanguage — deployed language negotiation (the i18n surface)

The engine had NO internationalization surface: no route negotiated
`Accept-Language`, no response ever carried `Content-Language`, and no `Vary`
told a cache the answer was language-keyed. This module builds the missing
feature as two stages over a REAL RFC 9110 negotiation:

* `welcomeGateStage` — a request-phase gate: `GET /welcome` (method + target
  scoped) is answered `200` whose body is the representation in the NEGOTIATED
  language. Everything else passes through.
* `langStampStage` — a response-phase stamp: on `GET /welcome`, push
  `Content-Language: <negotiated-tag>` and `Vary: Accept-Language` (the
  cache-correctness pair RFC 9110 §12.5.4 demands of a negotiated resource).
  Placed OUTSIDE the deployed rewrite onion so the pair reaches the wire.

## The negotiation (RFC 9110 §12.4.2 / §12.5.4)

`negotiate` parses every `Accept-Language` header: list items split on commas,
each item's language-range lowercased and OWS-trimmed, its `q` parameter parsed
to thousandths (`q=0.75` ⇒ 750; absent ⇒ 1000; `q=0` ⇒ excluded; a malformed
qvalue ⇒ 0, fail-closed). A range matches a served tag exactly, as the `*`
wildcard, or as a region-extended range whose primary subtag is the served tag
(`de-DE` accepts the served `de`). The FIRST matching list item supplies the
tag's q. The served language maximizes q over the supported set
{`en`, `de`, `fr`} (ties resolve `en` ≻ `de` ≻ `fr`); no header ⇒ `en`.

## What is proven (pure kernel — no `native_decide`)

* `negotiate_default` — no `Accept-Language` ⇒ the `en` default.
* `negotiate_maximal` — NO supported language outscores the negotiated one —
  the general argmax fact for ANY request, not a witness.
* `welcomeGate_fires` / `welcomeGate_passes`, `langStamp_effect` /
  `langStamp_noop`, status-stability of both stages.
* Concrete kernel-decided witnesses: plain `de`; max-q wins (`en;q=0.1,
  de;q=0.9` ⇒ `de`); `q=0` excludes + region-range accepted (`de-DE, fr;q=0`
  ⇒ `de`); wildcard and absent header fall to the default.

Named residuals (honest): all-unacceptable (every q = 0) serves the `en`
default rather than a `406`; the region match is primary-subtag lenient
(a `de-DE`-only request accepts the served `de`).
-/

namespace Reactor.Stage.ContentLanguage

open Reactor.Pipeline
open Proto (Bytes Request)
open Reactor.Stage.FramingValidation (lowerBytes trimOWS splitOn bCOMMA)

/-! ## ASCII tokens (explicit, kernel-reducible) -/

/-- `;` -/ def bSEMI : UInt8 := 59
/-- `*` -/ def bSTAR : UInt8 := 42
/-- `-` -/ def bDASH : UInt8 := 45
/-- `=` -/ def bEQ : UInt8 := 61
/-- `q` -/ def bQ : UInt8 := 113
/-- `.` -/ def bDOT : UInt8 := 46

/-- `accept-language` (lowercase). -/
def alNameLower : Bytes :=
  [97, 99, 99, 101, 112, 116, 45, 108, 97, 110, 103, 117, 97, 103, 101]

/-! ## The supported languages -/

/-- The languages the deployed representation exists in. -/
inductive Lang
  | en
  | de
  | fr
deriving DecidableEq, Repr

/-- The BCP-47 primary tag of a supported language. -/
def tagOf : Lang → Bytes
  | .en => [101, 110]
  | .de => [100, 101]
  | .fr => [102, 114]

/-- The localized representation body. -/
def bodyOf : Lang → Bytes
  | .en => "Welcome!\n".toUTF8.toList
  | .de => "Willkommen!\n".toUTF8.toList
  | .fr => "Bienvenue !\n".toUTF8.toList

/-! ## The Accept-Language parse -/

/-- Is the request carrying any `Accept-Language` header (case-insensitive)? -/
def hasAl (req : Request) : Bool :=
  req.headers.any (fun kv => lowerBytes kv.1 == alNameLower)

/-- All `Accept-Language` list items: every AL header's value split on commas,
each item OWS-trimmed and lowercased, in header/list order (RFC 9110 §12.5.4
list syntax; §5.3 reads a repeated field as one list). -/
def alItems (req : Request) : List Bytes :=
  (req.headers.filter (fun kv => lowerBytes kv.1 == alNameLower)).flatMap
    (fun kv => (splitOn bCOMMA kv.2).map (fun t => lowerBytes (trimOWS t)))

/-- The language-range of one list item: everything before the first `;`,
OWS-trimmed (the item is already lowercased). -/
def rangeOfItem (item : Bytes) : Bytes :=
  trimOWS (item.takeWhile (fun b => b != bSEMI))

/-- The parameter parts of one list item (everything after the first `;`). -/
def paramsOfItem (item : Bytes) : List Bytes :=
  (splitOn bSEMI item).drop 1

/-- ASCII digit probe. -/
def isDigitB (b : UInt8) : Bool :=
  decide (48 ≤ b.toNat) && decide (b.toNat ≤ 57)

/-- Digit value. -/
def digitVal (b : UInt8) : Nat := b.toNat - 48

/-- Up-to-three fraction digits read as thousandths (`5` ⇒ 500, `75` ⇒ 750,
`755` ⇒ 755). -/
def fracMillis : Bytes → Nat
  | [] => 0
  | [d1] => digitVal d1 * 100
  | [d1, d2] => digitVal d1 * 100 + digitVal d2 * 10
  | d1 :: d2 :: d3 :: _ => digitVal d1 * 100 + digitVal d2 * 10 + digitVal d3

/-- A qvalue (RFC 9110 §12.4.2) in thousandths: `1` (with any fraction) ⇒
1000, `0[.ddd]` ⇒ the fraction, anything malformed ⇒ 0 (fail-closed). -/
def qMillis : Bytes → Nat
  | [] => 0
  | b :: rest =>
    if b == 49 then 1000
    else if b == 48 then
      match rest with
      | [] => 0
      | dot :: ds =>
        if dot == bDOT && ds.all isDigitB && decide (ds.length ≤ 3) then
          fracMillis ds
        else 0
    else 0

/-- The `q` parameter of an item's parameter list (first `q=…` part wins;
absent ⇒ 1000, the RFC default weight). -/
def qOfParams : List Bytes → Nat
  | [] => 1000
  | p :: rest =>
    match lowerBytes (trimOWS p) with
    | q :: e :: v => if q == bQ && e == bEQ then qMillis v else qOfParams rest
    | _ => qOfParams rest

/-- Does a client language-range accept a served tag? Exact match, the `*`
wildcard, or a region-extended range whose primary subtag is the served tag
(`de-de` accepts `de` — the lenient primary-subtag reading, named residual). -/
def rangeMatches (range tag : Bytes) : Bool :=
  range == tag || range == [bSTAR]
    || (tag ++ [bDASH]) == range.take (tag.length + 1)

/-- The q the request assigns to a served tag: the FIRST matching list item's
q (no matching item ⇒ 0 = unacceptable). -/
def qFor (req : Request) (tag : Bytes) : Nat :=
  match (alItems req).find? (fun item => rangeMatches (rangeOfItem item) tag) with
  | some item => qOfParams (paramsOfItem item)
  | none => 0

/-- **The negotiated language.** No `Accept-Language` ⇒ the `en` default; else
the maximal-q supported language, ties resolving `en` ≻ `de` ≻ `fr`. -/
def negotiate (req : Request) : Lang :=
  if hasAl req then
    if qFor req (tagOf .en) < qFor req (tagOf .de)
        ∧ qFor req (tagOf .fr) ≤ qFor req (tagOf .de) then .de
    else if qFor req (tagOf .en) < qFor req (tagOf .fr)
        ∧ qFor req (tagOf .de) < qFor req (tagOf .fr) then .fr
    else .en
  else .en

/-! ## The negotiation theorems -/

/-- No `Accept-Language` ⇒ the default representation. -/
theorem negotiate_default (req : Request) (h : hasAl req = false) :
    negotiate req = .en := by
  unfold negotiate
  rw [h]
  rfl

/-- With no `Accept-Language` header every tag scores 0 (no list items). -/
theorem qFor_of_no_al (req : Request) (tag : Bytes) (h : hasAl req = false) :
    qFor req tag = 0 := by
  have hfil : req.headers.filter (fun kv => lowerBytes kv.1 == alNameLower)
      = [] := by
    rw [List.filter_eq_nil_iff]
    intro kv hkv hpred
    have hany : hasAl req = true := by
      unfold hasAl
      exact List.any_eq_true.mpr ⟨kv, hkv, hpred⟩
    rw [h] at hany
    exact Bool.false_ne_true hany
  have hitems : alItems req = [] := by
    unfold alItems
    rw [hfil]
    rfl
  unfold qFor
  rw [hitems]
  rfl

/-- **Maximality.** No supported language outscores the negotiated one — the
general argmax fact over the whole supported set, for ANY request. -/
theorem negotiate_maximal (req : Request) (l : Lang) :
    qFor req (tagOf l) ≤ qFor req (tagOf (negotiate req)) := by
  by_cases hal : hasAl req = true
  · unfold negotiate
    rw [hal, if_pos rfl]
    by_cases h1 : qFor req (tagOf .en) < qFor req (tagOf .de)
        ∧ qFor req (tagOf .fr) ≤ qFor req (tagOf .de)
    · rw [if_pos h1]
      cases l <;> omega
    · rw [if_neg h1]
      by_cases h2 : qFor req (tagOf .en) < qFor req (tagOf .fr)
          ∧ qFor req (tagOf .de) < qFor req (tagOf .fr)
      · rw [if_pos h2]
        cases l <;> omega
      · rw [if_neg h2]
        cases l <;> omega
  · have hal' : hasAl req = false := by
      cases h : hasAl req
      · rfl
      · exact absurd h hal
    rw [negotiate_default req hal', qFor_of_no_al req (tagOf l) hal']
    exact Nat.zero_le _

/-! ## The stages -/

/-- ASCII `"GET"`. -/
def getBytes : Bytes := [71, 69, 84]

/-- ASCII `"/welcome"` — the negotiated route. -/
def welcomeTarget : Bytes := [47, 119, 101, 108, 99, 111, 109, 101]

/-- ASCII `"OK"`. -/
def okReason : Bytes := [79, 75]

/-- The route's guard: method `GET`, target `/welcome`. -/
def inScope (c : Ctx) : Bool :=
  c.req.method == getBytes && c.req.target == welcomeTarget

/-- The negotiated route's bare response: header-LESS (the pair is stamped by
`langStampStage` outside the rewrite onion; a header-less seed keeps the
deployed content-type-gated body rewrite a passthrough), body the negotiated
representation. -/
def welcomeRespOf (c : Ctx) : Reactor.Response :=
  { status := 200, reason := okReason, headers := []
    body := bodyOf (negotiate c.req) }

/-- **The negotiated-welcome gate.** Answers `GET /welcome` with the negotiated
`200`; passes everything else through untouched. -/
def welcomeGateStage : Stage where
  name := "welcome-i18n"
  onRequest := fun c =>
    if inScope c then .respond (welcomeRespOf c) else .continue c
  onResponse := fun _ b => b

/-- ASCII `"Content-Language"`. -/
def clHdrName : Bytes :=
  [67, 111, 110, 116, 101, 110, 116, 45, 76, 97, 110, 103, 117, 97, 103, 101]

/-- ASCII `"Vary"`. -/
def varyName : Bytes := [86, 97, 114, 121]

/-- ASCII `"Accept-Language"` (the `Vary` value, wire-cased). -/
def varyVal : Bytes :=
  [65, 99, 99, 101, 112, 116, 45, 76, 97, 110, 103, 117, 97, 103, 101]

/-- **The negotiation stamp.** Response phase: on `GET /welcome`, push
`Content-Language: <negotiated>` then `Vary: Accept-Language`; identity
elsewhere. -/
def langStampStage : Stage where
  name := "content-language-stamp"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    if inScope c then
      (b.addHeader (clHdrName, tagOf (negotiate c.req))).addHeader
        (varyName, varyVal)
    else b

/-! ## The guard -/

theorem inScope_true (c : Ctx) (hm : c.req.method = getBytes)
    (ht : c.req.target = welcomeTarget) : inScope c = true := by
  unfold inScope
  rw [hm, ht]
  rfl

theorem inScope_false_of_target (c : Ctx) (h : ¬ c.req.target = welcomeTarget) :
    inScope c = false := by
  unfold inScope
  have hf : (c.req.target == welcomeTarget) = false := by
    cases hb : c.req.target == welcomeTarget
    · rfl
    · exact absurd (eq_of_beq hb) h
  rw [hf, Bool.and_false]

/-! ## Gate behaviour -/

/-- The gate fires on `GET /welcome` with the NEGOTIATED representation. -/
theorem welcomeGate_fires (c : Ctx) (hm : c.req.method = getBytes)
    (ht : c.req.target = welcomeTarget) :
    welcomeGateStage.onRequest c = .respond (welcomeRespOf c) := by
  show (if inScope c then StageStep.respond (welcomeRespOf c)
        else StageStep.continue c) = _
  rw [inScope_true c hm ht]
  rfl

/-- The gate passes any non-welcome target through untouched. -/
theorem welcomeGate_passes (c : Ctx) (h : ¬ c.req.target = welcomeTarget) :
    welcomeGateStage.onRequest c = .continue c := by
  show (if inScope c then StageStep.respond (welcomeRespOf c)
        else StageStep.continue c) = _
  rw [inScope_false_of_target c h]
  rfl

theorem welcomeGate_statusStable : Stage.statusStable welcomeGateStage :=
  fun _ _ => rfl

/-! ## Stamp behaviour -/

/-- **The stamp's byte-effect.** On `GET /welcome` the finalized pipeline is the
tail's with the negotiated `Content-Language` and `Vary: Accept-Language`
appended — for ANY tail/handler. -/
theorem langStamp_effect (rest : List Stage) (h : Ctx → Reactor.Response)
    (c : Ctx) (hm : c.req.method = getBytes) (ht : c.req.target = welcomeTarget) :
    runPipeline (langStampStage :: rest) h c
      = ((runPipeline rest h c).addHeader
          (clHdrName, tagOf (negotiate c.req))).addHeader (varyName, varyVal) := by
  rw [pipeline_stage_effect langStampStage rest h c c rfl]
  show (if inScope c then
          ((runPipeline rest h c).addHeader
            (clHdrName, tagOf (negotiate c.req))).addHeader (varyName, varyVal)
        else runPipeline rest h c) = _
  rw [inScope_true c hm ht]
  rfl

/-- Off the welcome target the stamp is the identity. -/
theorem langStamp_noop (rest : List Stage) (h : Ctx → Reactor.Response)
    (c : Ctx) (ht : ¬ c.req.target = welcomeTarget) :
    runPipeline (langStampStage :: rest) h c = runPipeline rest h c := by
  rw [pipeline_stage_effect langStampStage rest h c c rfl]
  show (if inScope c then
          ((runPipeline rest h c).addHeader
            (clHdrName, tagOf (negotiate c.req))).addHeader (varyName, varyVal)
        else runPipeline rest h c) = _
  rw [inScope_false_of_target c ht]
  rfl

/-- The stamp never changes the built status (either branch). -/
theorem langStamp_statusStable : Stage.statusStable langStampStage := by
  intro c b
  show ((if inScope c then
          (b.addHeader (clHdrName, tagOf (negotiate c.req))).addHeader
            (varyName, varyVal)
        else b).build).status = b.build.status
  by_cases h : inScope c = true
  · rw [if_pos h]; rfl
  · rw [if_neg h]

/-! ## Concrete negotiation witnesses (kernel-decided on explicit bytes) -/

/-- A `GET /welcome` request carrying one `Accept-Language` value. -/
def reqWith (v : Bytes) : Request :=
  { method := getBytes, target := welcomeTarget, version := []
    headers := [(varyVal, v)] }

/-- `Accept-Language: de` ⇒ `de`. -/
theorem witness_de : negotiate (reqWith [100, 101]) = .de := by decide

/-- `Accept-Language: en;q=0.1, de;q=0.9` ⇒ the max-q `de` (weights beat
order). -/
theorem witness_max_q :
    negotiate (reqWith
      [101, 110, 59, 113, 61, 48, 46, 49, 44, 32,
       100, 101, 59, 113, 61, 48, 46, 57]) = .de := by decide

/-- `Accept-Language: fr, de;q=0.5` ⇒ `fr` (default weight 1 beats 0.5). -/
theorem witness_fr :
    negotiate (reqWith
      [102, 114, 44, 32, 100, 101, 59, 113, 61, 48, 46, 53]) = .fr := by decide

/-- `Accept-Language: de-DE, fr;q=0` ⇒ `de`: the region range accepts the
served primary tag, and `q=0` EXCLUDES `fr`. -/
theorem witness_region_and_exclusion :
    negotiate (reqWith
      [100, 101, 45, 68, 69, 44, 32, 102, 114, 59, 113, 61, 48]) = .de := by
  decide

/-- `Accept-Language: *` ⇒ the `en` default (the wildcard accepts everything;
ties resolve to the default). -/
theorem witness_wildcard : negotiate (reqWith [42]) = .en := by decide

/-- No `Accept-Language` at all ⇒ the `en` default. -/
theorem witness_absent :
    negotiate { method := getBytes, target := welcomeTarget, version := []
                headers := [] } = .en := by decide

end Reactor.Stage.ContentLanguage

#print axioms Reactor.Stage.ContentLanguage.negotiate_default
#print axioms Reactor.Stage.ContentLanguage.negotiate_maximal
#print axioms Reactor.Stage.ContentLanguage.welcomeGate_fires
#print axioms Reactor.Stage.ContentLanguage.langStamp_effect
#print axioms Reactor.Stage.ContentLanguage.witness_max_q
#print axioms Reactor.Stage.ContentLanguage.witness_region_and_exclusion
