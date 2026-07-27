/-
  Pancake/StageYetMore.lean — SEVEN MORE real serve stages expressed in the `StageProg`
  DSL, denoted to their DEPLOYED serve semantics, and compiled by the GENUINE
  per-constructor compiler `compile2` (StageCompile.lean), proven by the induction
  keystone `compile2_correct`.

  This file is ADDITIVE over StageCompile.lean / StageMore.lean / StageEvenMore.lean:
  it introduces NO new compiler and NO new keystone.

  WHY THESE SEVEN. Every stage here is a VERIFIED MEMBER of the deployed registry
  `deployPipelineStages` — the flat, ordered stage list the running default folds
  (`deployPipelineStages_length : deployPipelineStages.length = 52`). Each stage's
  status code, reason phrase, header names/values and body prose below are read OFF
  the deployed stage's own definition, not re-specified from prose:

   * `jwtAdminGate`     — the `/admin` bearer gate. Refusal: `401`, reason
                          `Unauthorized`, header `WWW-Authenticate: Bearer`, body
                          `invalid or missing bearer token` (NO trailing newline).
   * `ipFilterGate`     — the CIDR admission gate. Refusal: `403`, reason
                          `Forbidden`, body `forbidden: ip not admitted` (NO trailing
                          newline — the deployed gate's own constant, distinct from
                          the sibling deploy-side 403 which DOES carry one).
   * `rateGate`         — the token-bucket limit gate. Refusal: `429`, reason
                          `Too Many Requests`, body `rate limit exceeded\n`.
   * `traversalGate`    — the `..`-escape block. Refusal: `404`, reason `Not Found`,
                          body `traversal blocked\n`.
   * `policyGate`       — the declared-surface admission gate. Refusal: `403`, reason
                          `Forbidden`, body `policy: undeclared surface\n`.
   * `gzipStage`        — the response-phase gzip transform: when the request advertises
                          gzip, rewrite the body to its gzip container and stamp
                          `Content-Encoding: gzip`; otherwise pass untouched.
   * `htmlRewriteStage` — the response-phase markup strip: on an HTML content-type the
                          body is tag-stripped; otherwise passed untouched.

  THE SHAPE OF A DEPLOYED GATE, AND THE ONE THING THE DSL CANNOT SAY. A deployed
  gate's request phase answers `.respond r`, and the pipeline SEEDS a fresh builder
  from `r` — so `r` REPLACES the handler's response wholesale, headers included (the
  four refusal constants above are built with `headers := []`). `StageProg` has no
  header-clearing constructor: `addHeader` only appends, and `denote` folds over
  `ctx.base`. So the faithful `denote` equation for a fired gate is

      { status := code, reason := reason, headers := ctx.base.headers, body := body }

  which is the deployed refusal EXACTLY WHEN `ctx.base.headers = []`. That hypothesis
  is carried EXPLICITLY on each `_pins_deployed` theorem below rather than hidden —
  and the missing constructor is named as residual (R1) at the foot of this header.

  WHAT IS PROVEN, per stage:
   * a general `denote_<stage>_*` equation (fires / passes) — no hypothesis beyond the
     stage's own decision bit;
   * a `<stage>_pins_deployed` corollary pinning the fired denotation to a LITERAL
     mirror of the deployed refusal constant (under the `headers = []` hypothesis);
   * `#guard` non-vacuity: distinct concrete status codes / bodies / header counts, and
     the stages' serializations distinct from the base and from each other;
   * a `<stage>_compile2_correct` specialization of the induction keystone: from any
     `CoreEnc` of the base fold-state, `compile2 <stage>` lands the `CoreEnc` of the
     reference `denoteStep`. The GENUINE per-constructor compiler (`condR` → real
     `Cond`, `gate` → nested `If` + halt-set, `setStatus` → guarded status store,
     `rewriteBody` → guarded body-length store, `addHeader` → guarded count bump).

  RESIDUALS (named, not hidden):
   * (R1) NO header-clear constructor: a deployed `.respond` replaces the header block;
     `StageProg` can only append to `ctx.base.headers`. Every `_pins_deployed` theorem
     therefore carries `ctx.base.headers = []`. Closing this needs a `clearHeaders` (or
     `setHeaders`) constructor in the DSL + its `compile2` fragment (a store of `0` to
     the header-count slot) — a genuine DSL extension, deliberately NOT smuggled in
     here as a fake.
   * (R2) PREDICATES READ THE CONTEXT, NOT THE ACCUMULATED RESPONSE. `ReqPred = Ctx →
     Bool`, evaluated at the fixed `ctx`. Two deployed stages here gate on the
     RESPONSE-so-far: the markup strip keys on the built response's `Content-Type`, and
     the deployed gzip/CL-style stamps key on `b.acc.status`. Modelling those as `Ctx`
     predicates over `ctx.base` is faithful only when no earlier op in the fold moved
     the field they read. Named, and true of the single-stage denotations proven here.
   * (R3) COMPUTED BODIES ARE FIXED-CONTEXT PARAMETERS. The deployed gzip body is
     `gzipStored r.body` and the strip is `rewriteBytes r.body` — functions of the
     CURRENT body. `rewriteBody (.replace b)` takes a FIXED `b`, so each is carried as
     the stage's `Bytes` parameter at a fixed context (the same move `corsStage`'s
     `acaoVal` already makes). The compressor/tokenizer itself is upstream of this DSL.
   * (R4) A GATE'S HALT IS THE REQUEST-PHASE SKIP ONLY. `denote`'s `halted` absorbs
     every LATER op; the deployed short-circuit skips the handler and every later
     stage's REQUEST phase, but the inner stages' RESPONSE phases still run over the
     refusal (`runResp rest`). So these single-stage denotations are faithful; a
     WHOLE-CHAIN denotation would need the onion's two phases, which this DSL's single
     linear fold does not distinguish.
   * (R5) The scalar-skeleton residual of StageCompile.lean is inherited unchanged:
     `compile2` tracks `(status, |headers|, |body|, halted)`; the variable-length byte
     content (reason phrases, header values, bodies) is the outer write loop's job.
-/
import Pancake.StageCompile

namespace Pancake.StageYetMore

open Pancake Pancake.SerializeCompile Pancake.StageProg Pancake.StageCompile

variable {σ : Type}

/-! ## 1. The refusal-gate combinator

The four headerless deployed gates (ip-filter / rate / traversal / policy) share ONE
shape: on the decision bit, set the refusal status + reason, replace the body with the
gate's fixed prose, and HALT (the request-phase short-circuit); off it, pass through.
It is a combinator, so the four instantiations below are the SAME proven term at four
different real byte-constants — not four copy-pasted proofs. -/

/-- **The refusal-gate combinator.** `fires` is the pre-decided refusal bit. Fired →
`setStatus code reason`, `rewriteBody (.replace body)`, then `gate fires code` (which
re-affirms the status and SETS THE HALT FLAG — the deployed `.respond` short-circuit).
Not fired → a body-identity no-op (the deployed `.continue c`). -/
def refusalGate (code : Nat) (reason body : Bytes) (fires : ReqPred) : StageProg :=
  .condR fires
    (.seq (.setStatus code reason)
      (.seq (.rewriteBody (.replace body))
        (.gate fires code)))
    (.rewriteBody .identity)

/-- **`denote_refusalGate_fires`.** A fired refusal gate lands the gate's status, reason
and fixed body over the base's header block — the deployed refusal response modulo the
header block the DSL cannot clear (residual R1; see `_pins_deployed` below). -/
theorem denote_refusalGate_fires (code : Nat) (reason body : Bytes) (fires : ReqPred)
    (ctx : Ctx) (h : fires ctx = true) :
    denote (refusalGate code reason body fires) ctx
      = { status := code, reason := reason, headers := ctx.base.headers, body := body } := by
  show (denoteStep ctx (.condR fires
          (.seq (.setStatus code reason)
            (.seq (.rewriteBody (.replace body)) (.gate fires code)))
          (.rewriteBody .identity)) { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, h, if_true, Bool.false_eq_true, if_false, runBody]

/-- **`denote_refusalGate_passes`.** An unfired refusal gate passes the base response
through untouched — the deployed gate's `.continue c` with an identity response phase. -/
theorem denote_refusalGate_passes (code : Nat) (reason body : Bytes) (fires : ReqPred)
    (ctx : Ctx) (h : fires ctx = false) :
    denote (refusalGate code reason body fires) ctx = ctx.base := by
  show (denoteStep ctx (.condR fires
          (.seq (.setStatus code reason)
            (.seq (.rewriteBody (.replace body)) (.gate fires code)))
          (.rewriteBody .identity)) { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, h, Bool.false_eq_true, if_false, runBody]

/-- **`denote_refusalGate_halts`.** A fired refusal gate SETS THE HALT FLAG — the
short-circuit that skips the handler and every later stage's request phase. This is the
load-bearing half of a gate (the `compile2` fragment stores `1` to the halt slot), so it
is stated separately from the response equation. -/
theorem denote_refusalGate_halts (code : Nat) (reason body : Bytes) (fires : ReqPred)
    (ctx : Ctx) (h : fires ctx = true) :
    (denoteStep ctx (refusalGate code reason body fires)
      { resp := ctx.base, halted := false }).halted = true := by
  show (denoteStep ctx (.condR fires
          (.seq (.setStatus code reason)
            (.seq (.rewriteBody (.replace body)) (.gate fires code)))
          (.rewriteBody .identity)) { resp := ctx.base, halted := false }).halted = _
  simp only [denoteStep, h, if_true, Bool.false_eq_true, if_false]

/-! ## 2. The four headerless deployed gates, at their REAL byte-constants

Each `<stage>Resp` below is a LITERAL MIRROR of the deployed refusal constant (the
deployed repo is a separate tree, so there is no import to hang an equation on: the
grounding is the byte-for-byte mirror of the cited constant, and the `_pins_deployed`
theorem is what ties the DSL term to it). -/

/-! ### 2.1 The traversal gate — a `..`-escaping target is blocked -/

/-- The deployed traversal refusal reason (`Not Found`). -/
def notFoundReason : Bytes := str "Not Found"
/-- The deployed traversal refusal body — fixed prose, independent of the target, so no
resolved file bytes can flow. -/
def traversalBody : Bytes := str "traversal blocked\n"

/-- A literal mirror of the deployed traversal refusal: `404`, `Not Found`, no headers,
fixed body. -/
def traversalBlocked404 : Response :=
  { status := 404, reason := notFoundReason, headers := [], body := traversalBody }

/-- **The traversal gate.** `escapes` is the pre-decided `..`-escape bit. -/
def traversalGate (escapes : ReqPred) : StageProg :=
  refusalGate 404 notFoundReason traversalBody escapes

/-- **`traversalGate_pins_deployed`.** On a headerless base, the fired traversal gate's
denotation IS the deployed `404` refusal constant, byte for byte. -/
theorem traversalGate_pins_deployed (escapes : ReqPred) (ctx : Ctx)
    (h : escapes ctx = true) (hb : ctx.base.headers = []) :
    denote (traversalGate escapes) ctx = traversalBlocked404 := by
  rw [traversalGate, denote_refusalGate_fires _ _ _ _ ctx h, hb]
  rfl

/-! ### 2.2 The policy gate — an undeclared, reserved surface is refused -/

/-- The deployed policy refusal reason (`Forbidden`). -/
def forbiddenReason : Bytes := str "Forbidden"
/-- The deployed policy refusal body — fixed policy prose; the application handler body
is never reached. -/
def policyBody : Bytes := str "policy: undeclared surface\n"

/-- A literal mirror of the deployed policy refusal: `403`, `Forbidden`, no headers. -/
def forbidden403 : Response :=
  { status := 403, reason := forbiddenReason, headers := [], body := policyBody }

/-- **The policy gate.** `reserved` is the pre-decided "undeclared AND reserved" bit. -/
def policyGate (reserved : ReqPred) : StageProg :=
  refusalGate 403 forbiddenReason policyBody reserved

/-- **`policyGate_pins_deployed`.** On a headerless base, the fired policy gate's
denotation IS the deployed `403` refusal constant. -/
theorem policyGate_pins_deployed (reserved : ReqPred) (ctx : Ctx)
    (h : reserved ctx = true) (hb : ctx.base.headers = []) :
    denote (policyGate reserved) ctx = forbidden403 := by
  rw [policyGate, denote_refusalGate_fires _ _ _ _ ctx h, hb]
  rfl

/-! ### 2.3 The IP-filter gate — a denied client address is refused

NOTE the byte-level distinction, read off the deployed sources and NOT smoothed over:
the IP-filter gate's own `forbiddenBody` has **no trailing newline**, while the sibling
deploy-side ip-403 constant does. The deployed registry wires the FORMER (the stage's
own constant), so that is what is mirrored here. -/

/-- The deployed IP-filter refusal body — NO trailing newline (the stage's own constant). -/
def ipFilterBody : Bytes := str "forbidden: ip not admitted"

/-- A literal mirror of the deployed IP-filter refusal: `403`, `Forbidden`, no headers. -/
def ipForbidden403 : Response :=
  { status := 403, reason := forbiddenReason, headers := [], body := ipFilterBody }

/-- **The IP-filter gate.** `denied` is the pre-decided deny-precedence bit. -/
def ipFilterGate (denied : ReqPred) : StageProg :=
  refusalGate 403 forbiddenReason ipFilterBody denied

/-- **`ipFilterGate_pins_deployed`.** On a headerless base, the fired IP-filter gate's
denotation IS the deployed `403` refusal constant. -/
theorem ipFilterGate_pins_deployed (denied : ReqPred) (ctx : Ctx)
    (h : denied ctx = true) (hb : ctx.base.headers = []) :
    denote (ipFilterGate denied) ctx = ipForbidden403 := by
  rw [ipFilterGate, denote_refusalGate_fires _ _ _ _ ctx h, hb]
  rfl

-- The two deployed 403s are genuinely DISTINCT responses (same status and reason,
-- different body prose) — the mirror preserves the distinction rather than collapsing
-- it. Stated as `#guard` (elaborator-evaluated), not a theorem: `decide` cannot kernel-
-- reduce a `str`-built constant (`String.toUTF8` is opaque to the kernel), and a stuck
-- `decide` is not a proof. The wire-level distinctness is `#guard`ed again in §6.
#guard ipForbidden403.body ≠ forbidden403.body
#guard ipForbidden403.status = forbidden403.status

/-! ### 2.4 The rate gate — an over-limit token bucket is refused -/

/-- The deployed rate refusal reason (`Too Many Requests`). -/
def tooManyReason : Bytes := str "Too Many Requests"
/-- The deployed rate refusal body. -/
def tooManyBody : Bytes := str "rate limit exceeded\n"

/-- A literal mirror of the deployed rate refusal: `429`, `Too Many Requests`, no
headers. -/
def resp429 : Response :=
  { status := 429, reason := tooManyReason, headers := [], body := tooManyBody }

/-- **The rate gate.** `over` is the pre-decided over-limit bit (the standing bucket
being empty). -/
def rateGate (over : ReqPred) : StageProg :=
  refusalGate 429 tooManyReason tooManyBody over

/-- **`rateGate_pins_deployed`.** On a headerless base, the fired rate gate's denotation
IS the deployed `429` refusal constant. -/
theorem rateGate_pins_deployed (over : ReqPred) (ctx : Ctx)
    (h : over ctx = true) (hb : ctx.base.headers = []) :
    denote (rateGate over) ctx = resp429 := by
  rw [rateGate, denote_refusalGate_fires _ _ _ _ ctx h, hb]
  rfl

/-! ## 3. `jwtAdminGate` — the `/admin` bearer gate (a refusal WITH a challenge header)

The one deployed gate here whose refusal is NOT headerless: it carries the RFC 7235
§4.1 `WWW-Authenticate: Bearer` challenge. So it does not factor through `refusalGate`;
the challenge is an `addHeader` between the body replace and the halt. -/

/-- The deployed JWT refusal reason (`Unauthorized`). -/
def unauthorizedReason : Bytes := str "Unauthorized"
/-- The `WWW-Authenticate` challenge header name (RFC 7235 §4.1). -/
def wwwAuthName : Bytes := str "WWW-Authenticate"
/-- The challenge value the deployed gate emits. -/
def wwwAuthVal : Bytes := str "Bearer"
/-- The deployed JWT refusal body — NO trailing newline. -/
def unauthorizedBody : Bytes := str "invalid or missing bearer token"

/-- A literal mirror of the deployed JWT refusal: `401`, `Unauthorized`, the
`WWW-Authenticate: Bearer` challenge, the diagnostic body. -/
def unauthorized401 : Response :=
  { status := 401, reason := unauthorizedReason,
    headers := [(wwwAuthName, wwwAuthVal)], body := unauthorizedBody }

/-- **The admin bearer gate.** `rejected` is the pre-decided bit for "the target is
under `/admin` AND the bearer decision rejects". Fired → the `401` status + reason, the
diagnostic body, the `WWW-Authenticate: Bearer` challenge, then HALT. Not fired → pass
(so non-`/admin` targets are never gated). -/
def jwtAdminGate (rejected : ReqPred) : StageProg :=
  .condR rejected
    (.seq (.setStatus 401 unauthorizedReason)
      (.seq (.rewriteBody (.replace unauthorizedBody))
        (.seq (.addHeader wwwAuthName wwwAuthVal)
          (.gate rejected 401))))
    (.rewriteBody .identity)

/-- **`denote_jwtAdminGate_rejects`.** A rejected bearer lands `401` + reason + the
challenge header appended + the diagnostic body, and halts. -/
theorem denote_jwtAdminGate_rejects (rejected : ReqPred) (ctx : Ctx)
    (h : rejected ctx = true) :
    denote (jwtAdminGate rejected) ctx
      = { status := 401, reason := unauthorizedReason,
          headers := ctx.base.headers ++ [(wwwAuthName, wwwAuthVal)],
          body := unauthorizedBody } := by
  show (denoteStep ctx (.condR rejected
          (.seq (.setStatus 401 unauthorizedReason)
            (.seq (.rewriteBody (.replace unauthorizedBody))
              (.seq (.addHeader wwwAuthName wwwAuthVal) (.gate rejected 401))))
          (.rewriteBody .identity)) { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, h, if_true, Bool.false_eq_true, if_false, runBody]

/-- **`denote_jwtAdminGate_admits`.** An admitted (or non-`/admin`) request passes
untouched. -/
theorem denote_jwtAdminGate_admits (rejected : ReqPred) (ctx : Ctx)
    (h : rejected ctx = false) :
    denote (jwtAdminGate rejected) ctx = ctx.base := by
  show (denoteStep ctx (.condR rejected
          (.seq (.setStatus 401 unauthorizedReason)
            (.seq (.rewriteBody (.replace unauthorizedBody))
              (.seq (.addHeader wwwAuthName wwwAuthVal) (.gate rejected 401))))
          (.rewriteBody .identity)) { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, h, Bool.false_eq_true, if_false, runBody]

/-- **`jwtAdminGate_halts`.** The rejected arm SETS THE HALT FLAG. -/
theorem jwtAdminGate_halts (rejected : ReqPred) (ctx : Ctx) (h : rejected ctx = true) :
    (denoteStep ctx (jwtAdminGate rejected) { resp := ctx.base, halted := false }).halted = true := by
  show (denoteStep ctx (.condR rejected
          (.seq (.setStatus 401 unauthorizedReason)
            (.seq (.rewriteBody (.replace unauthorizedBody))
              (.seq (.addHeader wwwAuthName wwwAuthVal) (.gate rejected 401))))
          (.rewriteBody .identity)) { resp := ctx.base, halted := false }).halted = _
  simp only [denoteStep, h, if_true, Bool.false_eq_true, if_false]

/-- **`jwtAdminGate_pins_deployed`.** On a headerless base, the rejected gate's
denotation IS the deployed `401` challenge response, byte for byte — status, reason,
the `WWW-Authenticate: Bearer` header, and body. -/
theorem jwtAdminGate_pins_deployed (rejected : ReqPred) (ctx : Ctx)
    (h : rejected ctx = true) (hb : ctx.base.headers = []) :
    denote (jwtAdminGate rejected) ctx = unauthorized401 := by
  rw [denote_jwtAdminGate_rejects _ ctx h, hb]
  rfl

/-! ## 4. `gzipStage` — the deployed response-phase gzip transform

The deployed stage always passes the request phase; on the response phase, when the
request advertises `Accept-Encoding: gzip`, it rewrites the body to its real gzip
container and THEN stamps `Content-Encoding: gzip` (that order), otherwise threads the
builder untouched. `gz` is the gzip container at this fixed context (residual R3). -/

/-- The `Content-Encoding` field name. -/
def ceName : Bytes := str "Content-Encoding"
/-- The stamped encoding token (`gzip`). -/
def gzipVal : Bytes := str "gzip"

/-- **The gzip stage.** `accepts` is the pre-decided "request advertises gzip" bit; `gz`
is the gzip container of the base body at this context. Accepts → body replace THEN the
`Content-Encoding` stamp (the deployed order); otherwise a body-identity no-op. -/
def gzipStage (accepts : ReqPred) (gz : Bytes) : StageProg :=
  .condR accepts
    (.seq (.rewriteBody (.replace gz)) (.addHeader ceName gzipVal))
    (.rewriteBody .identity)

/-- **`denote_gzip_accepts`.** A gzip-advertising request gets the compressed body and
the `Content-Encoding: gzip` stamp appended — the deployed `mapResp`-then-`addHeader`. -/
theorem denote_gzip_accepts (accepts : ReqPred) (gz : Bytes) (ctx : Ctx)
    (h : accepts ctx = true) :
    denote (gzipStage accepts gz) ctx
      = { ctx.base with body := gz, headers := ctx.base.headers ++ [(ceName, gzipVal)] } := by
  show (denoteStep ctx (.condR accepts
          (.seq (.rewriteBody (.replace gz)) (.addHeader ceName gzipVal))
          (.rewriteBody .identity)) { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, h, if_true, Bool.false_eq_true, if_false, runBody]

/-- **`denote_gzip_declines`.** A request that does not advertise gzip passes untouched —
no body rewrite, no encoding stamp. -/
theorem denote_gzip_declines (accepts : ReqPred) (gz : Bytes) (ctx : Ctx)
    (h : accepts ctx = false) :
    denote (gzipStage accepts gz) ctx = ctx.base := by
  show (denoteStep ctx (.condR accepts
          (.seq (.rewriteBody (.replace gz)) (.addHeader ceName gzipVal))
          (.rewriteBody .identity)) { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, h, Bool.false_eq_true, if_false, runBody]

/-! ## 5. `htmlRewriteStage` — the deployed response-phase markup strip

The deployed stage always passes the request phase; its response phase applies the
CONTENT-TYPE-GATED transform: on an HTML content-type the body is tag-stripped, on
anything else the response is returned untouched (running the strip unconditionally
would corrupt non-HTML payloads). `stripped` is the tag-stripped body at this fixed
context (R3); the gate reads the response's content-type, modelled here as a context
predicate over the base (R2). -/

/-- **The markup-strip stage.** `isHtml` is the pre-decided "the response declares an
HTML content-type" bit; `stripped` is the tag-stripped body at this context. HTML →
replace the body with the strip; otherwise a body-identity no-op. -/
def htmlRewriteStage (isHtml : ReqPred) (stripped : Bytes) : StageProg :=
  .condR isHtml (.rewriteBody (.replace stripped)) (.rewriteBody .identity)

/-- **`denote_htmlRewrite_html`.** An HTML response has its body replaced by the
tag-stripped bytes; status, reason and headers are untouched. -/
theorem denote_htmlRewrite_html (isHtml : ReqPred) (stripped : Bytes) (ctx : Ctx)
    (h : isHtml ctx = true) :
    denote (htmlRewriteStage isHtml stripped) ctx = { ctx.base with body := stripped } := by
  show (denoteStep ctx (.condR isHtml (.rewriteBody (.replace stripped))
          (.rewriteBody .identity)) { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, h, if_true, Bool.false_eq_true, if_false, runBody]

/-- **`denote_htmlRewrite_other`.** A non-HTML response passes untouched — the gate that
keeps the strip from corrupting non-markup payloads. -/
theorem denote_htmlRewrite_other (isHtml : ReqPred) (stripped : Bytes) (ctx : Ctx)
    (h : isHtml ctx = false) :
    denote (htmlRewriteStage isHtml stripped) ctx = ctx.base := by
  show (denoteStep ctx (.condR isHtml (.rewriteBody (.replace stripped))
          (.rewriteBody .identity)) { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, h, Bool.false_eq_true, if_false, runBody]

/-! ### 5.1 The EMITTED code is the real per-constructor lowering (structurally pinned)

The strongest available check that these stages go through the GENUINE compiler and not
the copy-stub: pin the emitted Pancake fragment STRUCTURALLY, by `rfl`. A refusal gate
compiles to a real `Cond` on the decision local whose fired arm is a `Seq` of a guarded
status store, a guarded body-length store, and the nested `If` that re-stores the status
and SETS THE HALT SLOT — and whose unfired arm is `Skip`. The stub (`compile _ :=
copyWhile`) could not satisfy any of these. -/

/-- The refusal gate's emitted fragment, pinned constructor for constructor. -/
example (nm : ReqPred → String) (aStat aCnt aBody aHalt : Word)
    (code : Nat) (reason body : Bytes) (fires : ReqPred) :
    compile2 nm aStat aCnt aBody aHalt (refusalGate code reason body fires)
      = .cond (.var (nm fires))
          (.seq (guarded aHalt (stC aStat (BitVec.ofNat 64 code)))
            (.seq (guarded aHalt (stC aBody (BitVec.ofNat 64 body.length)))
              (guarded aHalt
                (.cond (.var (nm fires))
                  (.seq (stC aStat (BitVec.ofNat 64 code)) (stC aHalt 1))
                  .skip))))
          .skip := rfl

/-- The admin gate's emitted fragment additionally carries the guarded HEADER-COUNT bump
that lowers the `WWW-Authenticate` challenge — the `addHeader` constructor's own
fragment, distinct from every other. -/
example (nm : ReqPred → String) (aStat aCnt aBody aHalt : Word) (rejected : ReqPred) :
    compile2 nm aStat aCnt aBody aHalt (jwtAdminGate rejected)
      = .cond (.var (nm rejected))
          (.seq (guarded aHalt (stC aStat (BitVec.ofNat 64 401)))
            (.seq (guarded aHalt (stC aBody (BitVec.ofNat 64 unauthorizedBody.length)))
              (.seq (guarded aHalt (.store (.const aCnt)
                      (.op .add (.loadWord (.const aCnt)) (.const (BitVec.ofNat 64 1)))))
                (guarded aHalt
                  (.cond (.var (nm rejected))
                    (.seq (stC aStat (BitVec.ofNat 64 401)) (stC aHalt 1))
                    .skip)))))
          .skip := rfl

/-- The gzip stage emits a real `Cond` whose accepting arm is a body-length store THEN a
header-count bump, and whose declining arm is the `identity` body-rewrite's `Skip` —
three DIFFERENT constructors lowering to three different fragments in one term. -/
example (nm : ReqPred → String) (aStat aCnt aBody aHalt : Word)
    (accepts : ReqPred) (gz : Bytes) :
    compile2 nm aStat aCnt aBody aHalt (gzipStage accepts gz)
      = .cond (.var (nm accepts))
          (.seq (guarded aHalt (stC aBody (BitVec.ofNat 64 gz.length)))
            (guarded aHalt (.store (.const aCnt)
              (.op .add (.loadWord (.const aCnt)) (.const (BitVec.ofNat 64 1))))))
          .skip := rfl

/-- A refusal gate's emitted fragment is NOT the `Skip` that an identity body-rewrite
emits — so the lowering genuinely dispatches on the constructor (the stub emits the same
`copyWhile` for both). -/
example (nm : ReqPred → String) (aStat aCnt aBody aHalt : Word) (fires : ReqPred) :
    compile2 nm aStat aCnt aBody aHalt (traversalGate fires)
      ≠ compile2 nm aStat aCnt aBody aHalt (.rewriteBody .identity) := by
  intro h
  exact PancakeProg.noConfusion h

/-! ## 6. Non-vacuity: concrete, distinct, REAL deployed wire bytes -/

/-- A `200 OK` base with body `hi` and NO headers (the seed a gate replaces). -/
def baseOk : Response := ok200 (str "hi")

/-- Always-fires / never-fires decision bits. -/
def pTrue  : ReqPred := fun _ => true
def pFalse : ReqPred := fun _ => false

/-- A headerless `200` context (so the `_pins_deployed` hypothesis holds). -/
def ctx0 : Ctx := { req := {}, base := baseOk }

-- the base really is headerless (the `_pins_deployed` side condition, discharged):
#guard ctx0.base.headers = []

-- each gate genuinely drives ITS OWN deployed status (404 / 403 / 403 / 429 / 401),
-- not a shared placeholder:
#guard (denote (traversalGate pTrue) ctx0).status = 404
#guard (denote (policyGate    pTrue) ctx0).status = 403
#guard (denote (ipFilterGate  pTrue) ctx0).status = 403
#guard (denote (rateGate      pTrue) ctx0).status = 429
#guard (denote (jwtAdminGate  pTrue) ctx0).status = 401

-- every fired gate HALTS (the request-phase short-circuit):
#guard (denoteStep ctx0 (traversalGate pTrue) { resp := ctx0.base, halted := false }).halted = true
#guard (denoteStep ctx0 (policyGate    pTrue) { resp := ctx0.base, halted := false }).halted = true
#guard (denoteStep ctx0 (ipFilterGate  pTrue) { resp := ctx0.base, halted := false }).halted = true
#guard (denoteStep ctx0 (rateGate      pTrue) { resp := ctx0.base, halted := false }).halted = true
#guard (denoteStep ctx0 (jwtAdminGate  pTrue) { resp := ctx0.base, halted := false }).halted = true

-- an UNFIRED gate neither halts nor moves the status off the base 200:
#guard (denoteStep ctx0 (rateGate pFalse) { resp := ctx0.base, halted := false }).halted = false
#guard (denote (rateGate pFalse) ctx0).status = 200
#guard (denote (jwtAdminGate pFalse) ctx0).status = 200

-- the gate bodies are the REAL deployed prose, and genuinely replace the base body:
#guard (denote (traversalGate pTrue) ctx0).body = str "traversal blocked\n"
#guard (denote (policyGate    pTrue) ctx0).body = str "policy: undeclared surface\n"
#guard (denote (ipFilterGate  pTrue) ctx0).body = str "forbidden: ip not admitted"
#guard (denote (rateGate      pTrue) ctx0).body = str "rate limit exceeded\n"
#guard (denote (jwtAdminGate  pTrue) ctx0).body = str "invalid or missing bearer token"

-- the JWT gate is the only one carrying a challenge header (count 0 → 1); the four
-- headerless gates leave the (empty) header block alone:
#guard (denote (jwtAdminGate pTrue) ctx0).headers.length = 1
#guard (denote (traversalGate pTrue) ctx0).headers.length = 0
#guard (denote (rateGate pTrue) ctx0).headers.length = 0

-- the two 403s share a status but are DISTINCT on the wire (distinct body prose):
#guard (denote (ipFilterGate pTrue) ctx0).status = (denote (policyGate pTrue) ctx0).status
#guard serialize (denote (ipFilterGate pTrue) ctx0) ≠ serialize (denote (policyGate pTrue) ctx0)

-- the fired denotations ARE the deployed refusal constants (the `_pins_deployed` claims,
-- checked concretely as well as proven generally):
#guard serialize (denote (traversalGate pTrue) ctx0) = serialize traversalBlocked404
#guard serialize (denote (policyGate pTrue) ctx0) = serialize forbidden403
#guard serialize (denote (ipFilterGate pTrue) ctx0) = serialize ipForbidden403
#guard serialize (denote (rateGate pTrue) ctx0) = serialize resp429
#guard serialize (denote (jwtAdminGate pTrue) ctx0) = serialize unauthorized401

-- gzip genuinely replaces the body AND stamps the encoding (count 0 → 1); declining
-- leaves both alone:
#guard (denote (gzipStage pTrue (str "GZ")) ctx0).body = str "GZ"
#guard (denote (gzipStage pTrue (str "GZ")) ctx0).headers.length = 1
#guard (denote (gzipStage pFalse (str "GZ")) ctx0).body = str "hi"
#guard (denote (gzipStage pFalse (str "GZ")) ctx0).headers.length = 0

-- the markup strip genuinely replaces the body and adds NO header; non-HTML is untouched:
#guard (denote (htmlRewriteStage pTrue (str "x")) ctx0).body = str "x"
#guard (denote (htmlRewriteStage pTrue (str "x")) ctx0).headers.length = 0
#guard (denote (htmlRewriteStage pFalse (str "x")) ctx0).body = str "hi"

-- every stage's serialization differs from the bare base, and the five refusals are
-- five genuinely distinct wire responses:
#guard serialize (denote (traversalGate pTrue) ctx0) ≠ serialize baseOk
#guard serialize (denote (gzipStage pTrue (str "GZ")) ctx0) ≠ serialize baseOk
#guard serialize (denote (htmlRewriteStage pTrue (str "x")) ctx0) ≠ serialize baseOk
#guard serialize (denote (traversalGate pTrue) ctx0) ≠ serialize (denote (policyGate pTrue) ctx0)
#guard serialize (denote (rateGate pTrue) ctx0) ≠ serialize (denote (jwtAdminGate pTrue) ctx0)
#guard serialize (denote (ipFilterGate pTrue) ctx0) ≠ serialize (denote (rateGate pTrue) ctx0)

/-! ## 7. Keystone instantiations — the GENUINE per-constructor compiler at each stage

Each is `compile2_correct` (the induction keystone) specialized to the stage: from any
`CoreEnc` of the base fold-state, running the emitted per-constructor control flow lands
the `CoreEnc` of the reference `denoteStep` — the tracked skeleton (status /
header-count / body-length / halt) of the deployed response. -/

/-- **`refusalGate_compile2_correct`.** The combinator's keystone: `compile2` of a
refusal gate — a real `Cond` on the decision bit whose fired arm is a guarded status
store, a guarded body-length store, and the nested `If` that re-stores the status and
SETS THE HALT SLOT — lands the reference refusal skeleton. The four deployed gates below
are this ONE theorem at four real byte-constants. -/
theorem refusalGate_compile2_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (code : Nat) (reason body : Bytes) (fires : ReqPred)
    (ctx : Ctx) (hd : Distinct aStat aCnt aBody aHalt) (st : PancakeState σ)
    (hEnc : CoreEnc aStat aCnt aBody aHalt st { resp := ctx.base, halted := false })
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt
        (refusalGate code reason body fires)) st = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st'
        (denoteStep ctx (refusalGate code reason body fires)
          { resp := ctx.base, halted := false }) := by
  obtain ⟨st', hrun, henc, _, _, _⟩ :=
    compile2_correct o nm aStat aCnt aBody aHalt ctx hd (refusalGate code reason body fires)
      { resp := ctx.base, halted := false } st hEnc hDec
  exact ⟨st', hrun, henc⟩

/-- **`traversalGate_compile2_correct`.** The deployed traversal gate compiled: the
emitted control flow lands the `404` refusal skeleton (status `404`, the fixed body's
length, halt set) on the escape bit. -/
theorem traversalGate_compile2_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (escapes : ReqPred) (ctx : Ctx)
    (hd : Distinct aStat aCnt aBody aHalt) (st : PancakeState σ)
    (hEnc : CoreEnc aStat aCnt aBody aHalt st { resp := ctx.base, halted := false })
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt (traversalGate escapes)) st
        = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st'
        (denoteStep ctx (traversalGate escapes) { resp := ctx.base, halted := false }) :=
  refusalGate_compile2_correct o nm aStat aCnt aBody aHalt 404 notFoundReason traversalBody
    escapes ctx hd st hEnc hDec

/-- **`policyGate_compile2_correct`.** The deployed policy gate compiled: the `403`
refusal skeleton on the reserved-surface bit. -/
theorem policyGate_compile2_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (reserved : ReqPred) (ctx : Ctx)
    (hd : Distinct aStat aCnt aBody aHalt) (st : PancakeState σ)
    (hEnc : CoreEnc aStat aCnt aBody aHalt st { resp := ctx.base, halted := false })
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt (policyGate reserved)) st
        = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st'
        (denoteStep ctx (policyGate reserved) { resp := ctx.base, halted := false }) :=
  refusalGate_compile2_correct o nm aStat aCnt aBody aHalt 403 forbiddenReason policyBody
    reserved ctx hd st hEnc hDec

/-- **`ipFilterGate_compile2_correct`.** The deployed IP-filter gate compiled: the `403`
refusal skeleton on the deny-precedence bit. -/
theorem ipFilterGate_compile2_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (denied : ReqPred) (ctx : Ctx)
    (hd : Distinct aStat aCnt aBody aHalt) (st : PancakeState σ)
    (hEnc : CoreEnc aStat aCnt aBody aHalt st { resp := ctx.base, halted := false })
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt (ipFilterGate denied)) st
        = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st'
        (denoteStep ctx (ipFilterGate denied) { resp := ctx.base, halted := false }) :=
  refusalGate_compile2_correct o nm aStat aCnt aBody aHalt 403 forbiddenReason ipFilterBody
    denied ctx hd st hEnc hDec

/-- **`rateGate_compile2_correct`.** The deployed rate gate compiled: the `429` refusal
skeleton on the over-limit bit. -/
theorem rateGate_compile2_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (over : ReqPred) (ctx : Ctx)
    (hd : Distinct aStat aCnt aBody aHalt) (st : PancakeState σ)
    (hEnc : CoreEnc aStat aCnt aBody aHalt st { resp := ctx.base, halted := false })
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt (rateGate over)) st
        = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st'
        (denoteStep ctx (rateGate over) { resp := ctx.base, halted := false }) :=
  refusalGate_compile2_correct o nm aStat aCnt aBody aHalt 429 tooManyReason tooManyBody
    over ctx hd st hEnc hDec

/-- **`jwtAdminGate_compile2_correct`.** The deployed admin bearer gate compiled: a real
`Cond` whose rejected arm is a guarded status store, a guarded body-length store, a
guarded header-count bump (the challenge), and the nested `If` that sets the halt slot —
landing the `401` challenge skeleton. -/
theorem jwtAdminGate_compile2_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (rejected : ReqPred) (ctx : Ctx)
    (hd : Distinct aStat aCnt aBody aHalt) (st : PancakeState σ)
    (hEnc : CoreEnc aStat aCnt aBody aHalt st { resp := ctx.base, halted := false })
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt (jwtAdminGate rejected)) st
        = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st'
        (denoteStep ctx (jwtAdminGate rejected) { resp := ctx.base, halted := false }) := by
  obtain ⟨st', hrun, henc, _, _, _⟩ :=
    compile2_correct o nm aStat aCnt aBody aHalt ctx hd (jwtAdminGate rejected)
      { resp := ctx.base, halted := false } st hEnc hDec
  exact ⟨st', hrun, henc⟩

/-- **`gzipStage_compile2_correct`.** The deployed gzip transform compiled: a real `Cond`
over a guarded body-length store composed with a guarded header-count bump (the
`Content-Encoding` stamp) and a body-identity `Skip` — landing the reference skeleton. -/
theorem gzipStage_compile2_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (accepts : ReqPred) (gz : Bytes) (ctx : Ctx)
    (hd : Distinct aStat aCnt aBody aHalt) (st : PancakeState σ)
    (hEnc : CoreEnc aStat aCnt aBody aHalt st { resp := ctx.base, halted := false })
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt (gzipStage accepts gz)) st
        = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st'
        (denoteStep ctx (gzipStage accepts gz) { resp := ctx.base, halted := false }) := by
  obtain ⟨st', hrun, henc, _, _, _⟩ :=
    compile2_correct o nm aStat aCnt aBody aHalt ctx hd (gzipStage accepts gz)
      { resp := ctx.base, halted := false } st hEnc hDec
  exact ⟨st', hrun, henc⟩

/-- **`htmlRewriteStage_compile2_correct`.** The deployed markup strip compiled: a real
`Cond` over a guarded body-length store and a body-identity `Skip` — landing the
reference skeleton (the stripped body's length on the HTML arm, the base's otherwise). -/
theorem htmlRewriteStage_compile2_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (isHtml : ReqPred) (stripped : Bytes) (ctx : Ctx)
    (hd : Distinct aStat aCnt aBody aHalt) (st : PancakeState σ)
    (hEnc : CoreEnc aStat aCnt aBody aHalt st { resp := ctx.base, halted := false })
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt (htmlRewriteStage isHtml stripped)) st
        = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st'
        (denoteStep ctx (htmlRewriteStage isHtml stripped) { resp := ctx.base, halted := false }) := by
  obtain ⟨st', hrun, henc, _, _, _⟩ :=
    compile2_correct o nm aStat aCnt aBody aHalt ctx hd (htmlRewriteStage isHtml stripped)
      { resp := ctx.base, halted := false } st hEnc hDec
  exact ⟨st', hrun, henc⟩

/-! ### 7.1 CONCRETE skeletons the keystones land (non-vacuous right-hand sides)

The keystones' right-hand sides are the REAL `denoteStep`, so at concrete decision bits
they compute the deployed refusal skeletons — five DIFFERENT ones. A `P → P` tautology
could not produce these numbers. -/

-- the five fired gates land five distinct (status, header-count, body-length, halt)
-- skeletons — the exact scalar image `compile2`'s emitted fragments write:
#guard (denoteStep ctx0 (traversalGate pTrue) { resp := ctx0.base, halted := false }).resp.status = 404
#guard (denoteStep ctx0 (traversalGate pTrue) { resp := ctx0.base, halted := false }).resp.body.length = 18
#guard (denoteStep ctx0 (policyGate pTrue) { resp := ctx0.base, halted := false }).resp.status = 403
#guard (denoteStep ctx0 (policyGate pTrue) { resp := ctx0.base, halted := false }).resp.body.length = 27
#guard (denoteStep ctx0 (ipFilterGate pTrue) { resp := ctx0.base, halted := false }).resp.body.length = 26
#guard (denoteStep ctx0 (rateGate pTrue) { resp := ctx0.base, halted := false }).resp.status = 429
#guard (denoteStep ctx0 (rateGate pTrue) { resp := ctx0.base, halted := false }).resp.body.length = 20
#guard (denoteStep ctx0 (jwtAdminGate pTrue) { resp := ctx0.base, halted := false }).resp.status = 401
#guard (denoteStep ctx0 (jwtAdminGate pTrue) { resp := ctx0.base, halted := false }).resp.headers.length = 1
#guard (denoteStep ctx0 (jwtAdminGate pTrue) { resp := ctx0.base, halted := false }).resp.body.length = 31

-- gzip lands body-length 2 and header-count 1 on the accepting arm:
#guard (denoteStep ctx0 (gzipStage pTrue (str "GZ")) { resp := ctx0.base, halted := false }).resp.body.length = 2
#guard (denoteStep ctx0 (gzipStage pTrue (str "GZ")) { resp := ctx0.base, halted := false }).resp.headers.length = 1
#guard (denoteStep ctx0 (gzipStage pTrue (str "GZ")) { resp := ctx0.base, halted := false }).halted = false

-- the markup strip lands body-length 1 and leaves the header count and halt alone:
#guard (denoteStep ctx0 (htmlRewriteStage pTrue (str "x")) { resp := ctx0.base, halted := false }).resp.body.length = 1
#guard (denoteStep ctx0 (htmlRewriteStage pTrue (str "x")) { resp := ctx0.base, halted := false }).halted = false

/-! ## 8. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms denote_refusalGate_fires
#print axioms denote_refusalGate_passes
#print axioms denote_refusalGate_halts
#print axioms traversalGate_pins_deployed
#print axioms policyGate_pins_deployed
#print axioms ipFilterGate_pins_deployed
#print axioms rateGate_pins_deployed
#print axioms denote_jwtAdminGate_rejects
#print axioms denote_jwtAdminGate_admits
#print axioms jwtAdminGate_halts
#print axioms jwtAdminGate_pins_deployed
#print axioms denote_gzip_accepts
#print axioms denote_gzip_declines
#print axioms denote_htmlRewrite_html
#print axioms denote_htmlRewrite_other
#print axioms refusalGate_compile2_correct
#print axioms traversalGate_compile2_correct
#print axioms policyGate_compile2_correct
#print axioms ipFilterGate_compile2_correct
#print axioms rateGate_compile2_correct
#print axioms jwtAdminGate_compile2_correct
#print axioms gzipStage_compile2_correct
#print axioms htmlRewriteStage_compile2_correct

end Pancake.StageYetMore
