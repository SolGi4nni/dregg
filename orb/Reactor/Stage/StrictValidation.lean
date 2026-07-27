import Reactor.Pipeline
import Reactor.Stage.RequestValidation
import Reactor.Stage.FramingValidation
import Reactor.Stage.MaxForwards
import Reactor.Stage.RequestHeadLimit

/-!
# Reactor.Stage.StrictValidation — request-line/field SYNTAX + method-SEMANTICS gate

The full RFC battery (`conformance/rfc_conformance_full.py`) found a cluster of
request-line, field-syntax, and method-semantics MUSTs the deployed serve
violates — all at the EDGE of the verified core (the wrapper's front gates),
none in the core itself:

* **O03 (RFC 9112 §3, MUST)** — a malformed request-line (method not a token)
  was answered by the VERSION gate (`505`), not `400`.
* **C05/C06 (RFC 9112 §3.2, MUST/SHOULD)** — an empty or bare-relative
  request-target was routed (`404`/`200`) instead of rejected `400`.
* **E03/E06/E07 (RFC 9110 §5, MUST ×3)** — an empty field-name, a bare CR in a
  field value, and a NUL octet in a field value were all forwarded to the inner
  serve (mis-routed `404`s) instead of rejected `400`.
* **E04 (RFC 9110 §5.1, MUST)** — field names are case-insensitive, but the
  Host discipline counted only the exact-case `Host`, rejecting `hOsT: x` with
  `400`.
* **D04 (RFC 9110 §4.2 / 3986 §3.2.2, SHOULD)** — a `Host` whose authority
  carries an embedded space was accepted.
* **E08 (RFC 9110 §5 / 6585, SHOULD)** — the inner serve mis-routes a request
  with more than 64 header fields (empirically: 64 fields serve, 65 mis-route
  to `404`); the bound existed but was NOT enforced deterministically.
* **B10/B11/B08 (RFC 9110 §9.3.8/§9.3.6/§9.3.7)** — `TRACE` and `CONNECT` were
  served as if `GET` (method-blind routing; the gap
  `Proto.TraceMaxForwardsProven` documents), and a `2xx` `OPTIONS` answer
  carried no `Allow`.

This stage is the missing gate. It COMPOSES with (does not modify) the proven
`Reactor.Stage.RequestValidation.validationStage`:

1. **Syntax first** (`syntaxCheck`): method token, target form (origin-form
   `/…`, asterisk-form `*` for `OPTIONS`, absolute-form `…://…`,
   authority-form only for `CONNECT`), field-name tokens, field-value octets
   (no CTL other than HTAB), `Host` authority octets, and the ≤ 64
   header-field bound. First violation ⇒ `400` (`431` for the field bound).
2. **The proven validation gate** on the HOST-CANONICALIZED request
   (`canonReq` rewrites any case-variant `Host` field name to the canonical
   `Host`, making the existing exact-case Host discipline case-insensitive
   without touching its proofs). Its `400/501/505` answers pass through.
3. **Method semantics last** (`semanticsCheck`, only on a request that cleared
   version/method/Host): `TRACE` ⇒ `405` + `Allow` (not implemented by this
   origin; the `Allow` set is the deployed surface's), `CONNECT` ⇒ `501` (this
   origin is not a tunnel), `OPTIONS` without `Max-Forwards` ⇒ the SAME proven
   `204` + `Allow` the deployed hop-limit gate answers
   (`Reactor.Stage.MaxForwards.optionsResp`). An `OPTIONS` WITH `Max-Forwards`
   is passed through so the deployed `mfStage` keeps its proven §7.6.2
   behavior (zero ⇒ answered by that hop, else decrement-and-forward).

Everything is a pure decision on the parsed request; every guard fact below is
`by decide` / `rfl` on explicit ASCII bytes (no `native_decide`, no
`String.toUTF8` in a decided position).
-/

namespace Reactor.Stage.StrictValidation

open Reactor.Pipeline
open Proto (Bytes Request)
open Reactor.Stage.RequestValidation
  (validationStage validationStage_passes_valid badRequestResp notImplementedResp
   strBytes hostName httpV11 mGET mOPTIONS mTRACE mCONNECT afterSubstr)
open Reactor.Stage.FramingValidation (lowerBytes trimOWS)
open Reactor.Stage.MaxForwards (optionsResp allowName allowVal mfNameLower)
open Reactor.Stage.RequestHeadLimit (requestHeaderFieldsTooLargeResp)

/-! ## Byte-class decisions (RFC 9110 §5.6.2 / §5.5) -/

/-- `tchar` (RFC 9110 §5.6.2): DIGIT / ALPHA / `!#$%&'*+-.^_`|~`. -/
def isTchar (b : UInt8) : Bool :=
  (48 ≤ b && b ≤ 57) || (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122) ||
  b == 33 || b == 35 || b == 36 || b == 37 || b == 38 || b == 39 ||
  b == 42 || b == 43 || b == 45 || b == 46 || b == 94 || b == 95 ||
  b == 96 || b == 124 || b == 126

/-- A non-empty all-`tchar` token (method names, field names). -/
def tokenOk (bs : Bytes) : Bool := !bs.isEmpty && bs.all isTchar

/-- A field-value octet (RFC 9110 §5.5): HTAB, or SP/VCHAR/obs-text — i.e.
anything but a control octet. Rejects bare CR (E06), bare LF, NUL (E07), DEL. -/
def fieldByteOk (b : UInt8) : Bool := b == 9 || (32 ≤ b && b != 127)

/-- A whole field value: every octet a valid field-value octet. -/
def valueOk (bs : Bytes) : Bool := bs.all fieldByteOk

/-! ## Request-target form (RFC 9112 §3.2) -/

/-- Whether the target contains a `://` — the absolute-form shape the proven
`normalizeTarget` rewrites to origin-form. -/
def hasSchemeSep (t : Bytes) : Bool := (afterSubstr [58, 47, 47] t).isSome

/-- **The request-target discipline.** `CONNECT` takes authority-form (any
non-empty target — the method itself is answered `501` downstream); everything
else must be origin-form (leading `/`), asterisk-form (`*`, `OPTIONS` only), or
absolute-form (`…://…`). An empty target (C05) or a bare relative target (C06)
is malformed. -/
def targetFormOk (m t : Bytes) : Bool :=
  if m == mCONNECT then !t.isEmpty
  else
    match t with
    | [] => false
    | b :: _ => b == 47 || (t == [42] && m == mOPTIONS) || hasSchemeSep t

/-! ## Host canonicalization (E04) + Host authority octets (D04) -/

/-- `host` (lowercase). -/
def hostLower : Bytes := [104, 111, 115, 116]

/-- Whether a field name is `Host` in ANY case (field names are
case-insensitive, RFC 9110 §5.1). -/
def isHostName (n : Bytes) : Bool := lowerBytes n == hostLower

/-- Rewrite a case-variant `Host` field name to the canonical `Host`; leave
every other name untouched. -/
def canonName (n : Bytes) : Bytes := if isHostName n then hostName else n

/-- Canonicalize every header's name (values untouched, order preserved). -/
def canonHeaders (hs : List (Bytes × Bytes)) : List (Bytes × Bytes) :=
  hs.map (fun kv => (canonName kv.1, kv.2))

/-- The request with its `Host` field name(s) canonicalized — what the proven
exact-case Host discipline (`hostOk`) is run on, making it case-insensitive
WITHOUT touching its proofs. Method/target/version untouched. -/
def canonReq (req : Request) : Request :=
  { req with headers := canonHeaders req.headers }

/-- A `Host` value is a plausible authority after OWS-trimming: every remaining
octet printable and not SP (RFC 9110 §4.2 — an authority has no spaces; D04). -/
def hostValueOk (v : Bytes) : Bool :=
  (trimOWS v).all (fun b => 32 < b && b != 127)

/-! ## The header-field bound (E08)

The deployed inner serve handles at most 64 header fields; the 65th mis-routes
(empirically pinned: 64 fields answer `200`, 65 answer the mis-routed `404`).
Enforce that bound HERE, deterministically: more than 64 fields ⇒ `431 Request
Header Fields Too Large` (RFC 6585 §5), so the inner's cliff is unreachable. -/
def maxHeaderFields : Nat := 64

/-! ## The two decision layers -/

/-- **The syntax gate** (first violation wins): method token, target form,
field-name tokens, field-value octets, `Host` authority octets, field bound. -/
def syntaxCheck (req : Request) : Option Reactor.Response :=
  if !tokenOk req.method then some badRequestResp
  else if !targetFormOk req.method req.target then some badRequestResp
  else if !req.headers.all (fun kv => tokenOk kv.1) then some badRequestResp
  else if !req.headers.all (fun kv => valueOk kv.2) then some badRequestResp
  else if !req.headers.all (fun kv => !isHostName kv.1 || hostValueOk kv.2) then
    some badRequestResp
  else if maxHeaderFields < req.headers.length then
    some requestHeaderFieldsTooLargeResp
  else none

/-- `405 Method Not Allowed` + the §10.2.1-required `Allow` (RFC 9110 §15.5.6)
— the `TRACE` answer: recognized, not supported by this origin. -/
def methodNotAllowedResp : Reactor.Response :=
  { status := 405, reason := strBytes "Method Not Allowed"
    headers := [(allowName, allowVal)]
    body := strBytes "method not allowed\n" }

/-- Whether the request carries a `Max-Forwards` field (case-insensitive) — if
so, `OPTIONS` is left to the deployed hop-limit gate (`mfStage`), preserving
its proven §7.6.2 behavior. -/
def hasMaxForwards (req : Request) : Bool :=
  req.headers.any (fun kv => lowerBytes kv.1 == mfNameLower)

/-- **The method-semantics gate** (run only on a request that cleared
version/method/Host): `TRACE` ⇒ `405`+`Allow` (§9.3.8: not enabled — never a
generic `200` page), `CONNECT` ⇒ `501` (§9.3.6: this origin is not a tunnel),
`OPTIONS` without `Max-Forwards` ⇒ the proven `204`+`Allow` (§9.3.7/§10.2.1). -/
def semanticsCheck (req : Request) : Option Reactor.Response :=
  if req.method == mTRACE then some methodNotAllowedResp
  else if req.method == mCONNECT then some notImplementedResp
  else if req.method == mOPTIONS && !hasMaxForwards req then some optionsResp
  else none

/-! ## The stage -/

/-- **The strict validation gate**: syntax ⇒ the proven `validationStage` on
the Host-canonicalized request ⇒ method semantics. A request clearing all
three `.continue`s with the validation gate's context (canonical `Host`,
origin-form-normalized target). Response phase transparent. -/
def strictStage : Stage where
  name := "strict-validation"
  onRequest := fun c =>
    match syntaxCheck c.req with
    | some r => .respond r
    | none =>
      match validationStage.onRequest { c with req := canonReq c.req } with
      | .respond r => .respond r
      | .continue c' =>
        match semanticsCheck c'.req with
        | some r => .respond r
        | none => .continue c'
  onResponse := fun _ b => b

theorem strictStage_statusStable : Stage.statusStable strictStage := fun _ _ => rfl

/-- The definitional unfolding (pinned once; every gate lemma rewrites it). -/
theorem strictStage_onRequest (c : Ctx) :
    strictStage.onRequest c
      = match syntaxCheck c.req with
        | some r => .respond r
        | none =>
          match validationStage.onRequest { c with req := canonReq c.req } with
          | .respond r => .respond r
          | .continue c' =>
            match semanticsCheck c'.req with
            | some r => .respond r
            | none => .continue c' := rfl

/-! ## Gate lemmas -/

/-- A syntax violation short-circuits with its `400`/`431`. -/
theorem strictStage_syntax_reject (c : Ctx) (r : Reactor.Response)
    (h : syntaxCheck c.req = some r) :
    strictStage.onRequest c = .respond r := by
  rw [strictStage_onRequest, h]

/-- A validation rejection (bad version/method/Host on the canonicalized
request) passes through with its `4xx/5xx`. -/
theorem strictStage_validation_reject (c : Ctx) (r : Reactor.Response)
    (hs : syntaxCheck c.req = none)
    (hv : validationStage.onRequest { c with req := canonReq c.req } = .respond r) :
    strictStage.onRequest c = .respond r := by
  rw [strictStage_onRequest, hs, hv]

/-- A semantics rejection (`TRACE`/`CONNECT`/plain `OPTIONS` past a passed
validation gate) short-circuits with its answer. -/
theorem strictStage_semantics_reject (c c' : Ctx) (r : Reactor.Response)
    (hs : syntaxCheck c.req = none)
    (hv : validationStage.onRequest { c with req := canonReq c.req } = .continue c')
    (hm : semanticsCheck c'.req = some r) :
    strictStage.onRequest c = .respond r := by
  rw [strictStage_onRequest, hs, hv]
  show (match semanticsCheck c'.req with
        | some r => StageStep.respond r
        | none => StageStep.continue c') = StageStep.respond r
  rw [hm]

/-- A request clearing all three layers `.continue`s with the validation
gate's context. -/
theorem strictStage_passes (c c' : Ctx)
    (hs : syntaxCheck c.req = none)
    (hv : validationStage.onRequest { c with req := canonReq c.req } = .continue c')
    (hm : semanticsCheck c'.req = none) :
    strictStage.onRequest c = .continue c' := by
  rw [strictStage_onRequest, hs, hv]
  show (match semanticsCheck c'.req with
        | some r => StageStep.respond r
        | none => StageStep.continue c') = StageStep.continue c'
  rw [hm]

/-! ## Decision facts (explicit bytes; `by decide` / `rfl` — no `native_decide`) -/

/-- **O03.** `!@#$` is not a method token (`@` is not a `tchar`). -/
theorem badToken_rejected : tokenOk [33, 64, 35, 36] = false := by decide

/-- `GET` / `get` / `FROBNICATE` ARE tokens — the token discipline never
shadows the (case-sensitive) method registry decisions downstream. -/
theorem known_tokens_ok :
    tokenOk mGET = true ∧ tokenOk [103, 101, 116] = true
      ∧ tokenOk [70, 82, 79, 66] = true := by
  refine ⟨by decide, by decide, by decide⟩

/-- **C05.** The empty request-target is malformed. -/
theorem emptyTarget_rejected : targetFormOk mGET [] = false := by decide

/-- **C06.** A bare relative target (`health`) is malformed for a `GET`. -/
theorem relativeTarget_rejected :
    targetFormOk mGET [104, 101, 97, 108, 116, 104] = false := by decide

/-- Origin-form (`/health`), absolute-form (`http://x/health`), asterisk-form
(`*` for `OPTIONS`), and `CONNECT` authority-form (`x:80`) all pass. -/
theorem good_targets_ok :
    targetFormOk mGET [47, 104, 101, 97, 108, 116, 104] = true
  ∧ targetFormOk mGET
      [104, 116, 116, 112, 58, 47, 47, 120, 47, 104, 101, 97, 108, 116, 104] = true
  ∧ targetFormOk mOPTIONS [42] = true
  ∧ targetFormOk mCONNECT [120, 58, 56, 48] = true := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- …but asterisk-form is NOT valid for a `GET`, and authority-form is NOT
valid outside `CONNECT` (C02). -/
theorem bad_target_forms_rejected :
    targetFormOk mGET [42] = false
  ∧ targetFormOk mGET [120, 58, 56, 48] = false := by
  refine ⟨by decide, by decide⟩

/-- **E03.** The empty field-name is not a token. -/
theorem emptyName_rejected : tokenOk [] = false := by decide

/-- **E06/E07.** A bare CR / a NUL octet in a field value is rejected; ordinary
SP-carrying values pass. -/
theorem ctl_values_rejected :
    valueOk [97, 13, 98] = false ∧ valueOk [97, 0, 98] = false
      ∧ valueOk [97, 32, 98] = true := by
  refine ⟨by decide, by decide, by decide⟩

/-- **D04.** `bad host` is not an authority (embedded SP); an OWS-padded plain
host (`   x   `, what the value parse yields for `Host:    x   `) still is. -/
theorem hostValue_discipline :
    hostValueOk [98, 97, 100, 32, 104, 111, 115, 116] = false
  ∧ hostValueOk [32, 32, 32, 120, 32, 32, 32] = true := by
  refine ⟨by decide, by decide⟩

/-- **E04.** `hOsT` is recognized as the Host field and canonicalized. -/
theorem hostCase_canonicalized :
    canonHeaders [([104, 79, 115, 84], [120])] = [(hostName, [120])] := by decide

/-! ## Concrete non-vacuity witnesses (request level) -/

/-- A well-formed `GET /health` (one `Host: x`) — clears every layer. -/
def okReq : Request :=
  { method := mGET, target := [47, 104, 101, 97, 108, 116, 104]
    version := httpV11, headers := [(hostName, [120])] }

def okCtx : Ctx := { input := [], req := okReq }

/-- `TRACE /health` (one `Host: x`) — gate-valid, answered `405`+`Allow`. -/
def traceReq : Request := { okReq with method := mTRACE }
def traceCtx : Ctx := { input := [], req := traceReq }

/-- `CONNECT x:80` (one `Host: x`) — authority-form, answered `501`. -/
def connectReq : Request :=
  { okReq with method := mCONNECT, target := [120, 58, 56, 48] }
def connectCtx : Ctx := { input := [], req := connectReq }

/-- `OPTIONS /health` (one `Host: x`, no `Max-Forwards`) — answered
`204`+`Allow` by this gate. -/
def optionsReq : Request := { okReq with method := mOPTIONS }
def optionsCtx : Ctx := { input := [], req := optionsReq }

/-- `OPTIONS /health` WITH `Max-Forwards: 0` — passed through to the deployed
`mfStage` (which answers its proven `204`+`Allow` at hop zero). -/
def optionsMfReq : Request :=
  { optionsReq with
    headers := optionsReq.headers
      ++ [([77, 97, 120, 45, 70, 111, 114, 119, 97, 114, 100, 115], [48])] }

/-- `GET /health` with the case-variant `hOsT: x` — repaired, not rejected. -/
def hostCaseReq : Request :=
  { okReq with headers := [([104, 79, 115, 84], [120])] }
def hostCaseCtx : Ctx := { input := [], req := hostCaseReq }

/-- 65 header fields (all syntactically valid) — one over the deployed bound. -/
def manyHeadersReq : Request :=
  { okReq with headers := List.replicate 65 (([88, 45, 72], [118])) }  -- `X-H: v`

/-! ### The decisions on the witnesses -/

theorem okReq_syntax_ok : syntaxCheck okReq = none := rfl
theorem okReq_semantics_ok : semanticsCheck okReq = none := rfl

/-- **B10.** `TRACE` is answered the `Allow`-carrying `405`. -/
theorem trace_semantics : semanticsCheck traceReq = some methodNotAllowedResp := rfl

/-- **B11.** `CONNECT` is answered `501`. -/
theorem connect_semantics : semanticsCheck connectReq = some notImplementedResp := rfl

/-- **B08.** A plain `OPTIONS` is answered the proven `Allow`-carrying `204`. -/
theorem options_semantics : semanticsCheck optionsReq = some optionsResp := rfl

/-- **§7.6.2 preserved.** An `OPTIONS` with `Max-Forwards` is NOT intercepted
(the deployed `mfStage` keeps its proven hop-limit behavior). -/
theorem optionsMf_passthrough : semanticsCheck optionsMfReq = none := rfl

theorem methodNotAllowedResp_status : methodNotAllowedResp.status = 405 := rfl
theorem methodNotAllowedResp_has_allow :
    (allowName, allowVal) ∈ methodNotAllowedResp.headers :=
  List.mem_singleton.mpr rfl

/-- **E08.** 65 fields trip the bound (`431`); the 64-field `okReq`-shaped
requests do not (`okReq_syntax_ok`). -/
theorem manyHeaders_rejected :
    syntaxCheck manyHeadersReq = some requestHeaderFieldsTooLargeResp := rfl

/-- **E04, the repair.** The exact-case Host discipline FAILS the raw `hOsT`
request but PASSES its canonicalization — the gate genuinely repairs rather
than rejects. -/
theorem hostCase_repaired :
    Reactor.Stage.RequestValidation.hostOk hostCaseReq = false
  ∧ Reactor.Stage.RequestValidation.hostOk (canonReq hostCaseReq) = true := by
  refine ⟨by decide, by decide⟩

/-! ### End-to-end stage witnesses -/

/-- **B10, end to end.** The gate answers a real `TRACE /health` with the
`405` (+`Allow`) — it never reaches the method-blind inner routing. -/
theorem trace_rejected_405 :
    strictStage.onRequest traceCtx = .respond methodNotAllowedResp := by
  refine strictStage_semantics_reject traceCtx _ _ rfl
    (validationStage_passes_valid _ (by decide) (by decide) (by decide)) rfl

/-- **B11, end to end.** The gate answers a real `CONNECT x:80` with the `501`. -/
theorem connect_rejected_501 :
    strictStage.onRequest connectCtx = .respond notImplementedResp := by
  refine strictStage_semantics_reject connectCtx _ _ rfl
    (validationStage_passes_valid _ (by decide) (by decide) (by decide)) rfl

/-- **B08, end to end.** The gate answers a real plain `OPTIONS /health` with
the proven `Allow`-carrying `204`. -/
theorem options_answered :
    strictStage.onRequest optionsCtx = .respond optionsResp := by
  refine strictStage_semantics_reject optionsCtx _ _ rfl
    (validationStage_passes_valid _ (by decide) (by decide) (by decide)) rfl

/-- **E04, end to end.** The case-variant `hOsT: x` request CONTINUES (into the
inner serve) instead of being rejected `400`. -/
theorem hostCase_continues :
    ∃ c', strictStage.onRequest hostCaseCtx = .continue c' := by
  refine ⟨_, strictStage_passes hostCaseCtx _ rfl
    (validationStage_passes_valid _ (by decide) (by decide) (by decide)) rfl⟩

/-- **Non-vacuity contrast.** The same gate `.continue`s the well-formed `GET`
— it genuinely discriminates. -/
theorem gate_discriminates :
    (∃ c', strictStage.onRequest okCtx = .continue c')
    ∧ strictStage.onRequest traceCtx = .respond methodNotAllowedResp := by
  refine ⟨⟨_, strictStage_passes okCtx _ rfl
    (validationStage_passes_valid _ (by decide) (by decide) (by decide)) rfl⟩,
    trace_rejected_405⟩

/-! ### Executable sanity checks -/

def stepStatus : StageStep → Nat
  | .respond r => r.status
  | .continue _ => 0

#guard stepStatus (strictStage.onRequest traceCtx) == 405
#guard stepStatus (strictStage.onRequest connectCtx) == 501
#guard stepStatus (strictStage.onRequest optionsCtx) == 204
#guard stepStatus (strictStage.onRequest hostCaseCtx) == 0
#guard stepStatus (strictStage.onRequest okCtx) == 0
#guard stepStatus (strictStage.onRequest { input := [], req := manyHeadersReq }) == 431
#guard stepStatus (strictStage.onRequest
  { input := [], req := { okReq with method := [33, 64, 35, 36] } }) == 400
#guard stepStatus (strictStage.onRequest
  { input := [], req := { okReq with target := [] } }) == 400
#guard stepStatus (strictStage.onRequest
  { input := [], req := { okReq with target := [104, 101, 97, 108, 116, 104] } }) == 400
#guard stepStatus (strictStage.onRequest
  { input := [], req := { okReq with
      headers := [(hostName, [120]), ([88, 45, 66], [97, 13, 98])] } }) == 400
#guard stepStatus (strictStage.onRequest
  { input := [], req := { okReq with
      headers := [(hostName, [98, 97, 100, 32, 104, 111, 115, 116])] } }) == 400
-- missing Host still rejected THROUGH the composed validation gate
#guard stepStatus (strictStage.onRequest
  { input := [], req := { okReq with headers := [] } }) == 400
-- unknown method still 501 through the composed validation gate
#guard stepStatus (strictStage.onRequest
  { input := [], req := { okReq with method := [70, 82, 79, 66] } }) == 501
-- bad version still 505 through the composed validation gate
#guard stepStatus (strictStage.onRequest
  { input := [], req := { okReq with version := [72, 84, 84, 80, 47, 57, 46, 57] } }) == 505

/-! ## Axiom audit -/

#print axioms strictStage_syntax_reject
#print axioms strictStage_validation_reject
#print axioms strictStage_semantics_reject
#print axioms strictStage_passes
#print axioms trace_rejected_405
#print axioms connect_rejected_501
#print axioms options_answered
#print axioms hostCase_continues
#print axioms manyHeaders_rejected
#print axioms hostCase_repaired
#print axioms gate_discriminates

end Reactor.Stage.StrictValidation
