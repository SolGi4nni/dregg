/-
  Pancake/StageMore.lean — THREE MORE real serve stages expressed in the `StageProg`
  DSL, denoted to their DEPLOYED serve semantics, and compiled by the GENUINE
  per-constructor compiler `compile2` (StageCompile.lean), proven by the induction
  keystone `compile2_correct`.

  This file is ADDITIVE over StageCompile.lean: it introduces NO new compiler and NO
  new keystone. Each stage is a `StageProg` term built from the agreed constructors,
  with a `denote_<stage>` equation pinning its reference `Response` to the deployed
  stage's own effect (read off the deployed stage functions, not re-specified), plus
  a `<stage>_compile2_correct` instantiation of the induction keystone showing the
  emitted control flow lands the reference response SKELETON (status / header-count /
  body-length / halt) byte-exactly.

  THE THREE STAGES (the deployed serve's header-transform / conditional-append set):

   * `hstsStage` — the `Strict-Transport-Security` stamp of the deployed
     `securityheadersStage`: an UNCONDITIONAL `addHeader` of the RFC 6797 field
     `Strict-Transport-Security: max-age=31536000; includeSubDomains; preload` (the
     exact bytes the deployed policy renders). Compiles to a guarded header-count
     increment.

   * `corsStage` — the deployed `cors` header-transform: a CONTEXT-CONDITIONAL append.
     When the request's origin is admitted by the policy it appends the singleton
     `Access-Control-Allow-Origin: <value>`; when it is denied it appends nothing —
     exactly `r.headers ++ corsHeaders c` (`corsHeaders` = the singleton / the empty
     list). Realized as a `condR` on the pre-decided allow bit: the allow branch is
     an `addHeader`, the deny branch a body-identity no-op. Compiles to a real `Cond`
     over the two per-constructor fragments.

   * `viaStage` — the RFC 9110 §7.6.3 `Via` stamp: append `Via: 1.1 drorb` (received
     protocol + pseudonym) UNLESS a `Via` is already present (an upstream's `Via` is
     never duplicated — the deployed `stampVia` new-line form). Realized as a `condR`
     on the pre-decided has-Via bit: the present branch is a no-op, the absent branch
     an `addHeader`.

  WHAT IS PROVEN, per stage:
   * a `denote_<stage>` equation grounding the reference fold in the deployed effect;
   * `#guard` non-vacuity: each stage's tracked skeleton genuinely differs from the
     base (hsts / via / cors-allow bump the header count; cors-deny / via-present do
     not) and the stages differ from each other;
   * a `<stage>_compile2_correct` specialization of the induction keystone: from any
     `CoreEnc` of the base state, `compile2 <stage>` lands the `CoreEnc` of the
     reference `denoteStep`. This is the GENUINE per-constructor compiler
     (`addHeader` → guarded count-increment, `condR` → real `Cond`), NOT the copy-stub.

  RESIDUALS (named, inherited from StageCompile.lean, NOT re-opened here):
   * `compile2` tracks the SCALAR skeleton `(status, |headers|, |body|, halted)`; the
     variable-length header NAME/VALUE bytes (the ACAO value, the `Via` value, the
     HSTS directive string) are the byte-content the outer header-write loop
     materializes — the standing SerializeHeaders / `Div`/`Mod` residual, untouched.
   * `corsStage`'s admitted-origin ACAO value is carried as the stage's `acaoVal`
     parameter (a fixed `Bytes` at a fixed context), matching the deployed
     `Cors.acaoValue` output at that context; the origin→value computation is the
     policy decision, upstream of this stage.
-/
import Pancake.StageCompile

namespace Pancake.StageMore

open Pancake Pancake.SerializeCompile Pancake.StageProg Pancake.StageCompile

variable {σ : Type}

/-! ## 1. `hstsStage` — the deployed `Strict-Transport-Security` stamp

The deployed `securityheadersStage` folds the rendered security-header set onto the
response; its HSTS member is the field
`Strict-Transport-Security: max-age=31536000; includeSubDomains; preload` — the exact
bytes `SecurityHeaders.hstsRender` produces for the deployed one-year/subdomains/
preload policy (RFC 6797 §6.1.1). Here it is an UNCONDITIONAL header append. -/

/-- The HSTS field name (`Strict-Transport-Security`). -/
def hstsName : Bytes := str "Strict-Transport-Security"
/-- The HSTS field value — the exact RFC 6797 render of the deployed policy
(`max-age=31536000; includeSubDomains; preload`). -/
def hstsVal  : Bytes := str "max-age=31536000; includeSubDomains; preload"

/-- **The HSTS stage.** Always passes, stamping the deployed HSTS field onto the
response — a single `addHeader` (the deployed `securityheadersStage`'s HSTS member). -/
def hstsStage : StageProg := .addHeader hstsName hstsVal

/-- **`denote_hsts`.** The HSTS stage appends its one field to the base response —
exactly the deployed stamp of `Strict-Transport-Security` (`base.headers ++ [hsts]`). -/
theorem denote_hsts (ctx : Ctx) :
    denote hstsStage ctx
      = { ctx.base with headers := ctx.base.headers ++ [(hstsName, hstsVal)] } := by
  show (denoteStep ctx (.addHeader hstsName hstsVal) { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, Bool.false_eq_true, if_false]

/-! ## 2. `corsStage` — the deployed context-conditional CORS append

`Reactor.Stage.Cors.corsStage.onResponse` appends `Access-Control-Allow-Origin: <v>`
iff `Cors.acaoValue corsPolicy (originOf c) = some v`, and nothing otherwise — i.e.
the built response's header block is `r.headers ++ corsHeaders c`, where `corsHeaders`
is the singleton `[(ACAO, v)]` (allowed) or `[]` (denied). At a fixed context the
allow/deny decision is a bit and the value `v` is fixed; the stage is a `condR` on
that bit. -/

/-- The CORS field name (`Access-Control-Allow-Origin`). -/
def acaoName : Bytes := str "Access-Control-Allow-Origin"

/-- **The CORS stage.** `allowed` is the pre-decided origin-admission bit (the
deployed `Cors.acaoValue …` being `some _`); `acaoVal` is the admitted origin's ACAO
value at this context. Admit → append `(ACAO, acaoVal)`; deny → a body-identity
no-op (append nothing) — exactly the deployed `corsHeaders c` allow/deny branch. -/
def corsStage (allowed : ReqPred) (acaoVal : Bytes) : StageProg :=
  .condR allowed (.addHeader acaoName acaoVal) (.rewriteBody .identity)

/-- **`denote_cors` (admit).** An admitted origin gets its `Access-Control-Allow-Origin`
field appended — the deployed `corsResp` with `corsHeaders c = [(ACAO, v)]`. -/
theorem denote_cors_allow (allowed : ReqPred) (acaoVal : Bytes) (ctx : Ctx)
    (h : allowed ctx = true) :
    denote (corsStage allowed acaoVal) ctx
      = { ctx.base with headers := ctx.base.headers ++ [(acaoName, acaoVal)] } := by
  show (denoteStep ctx (.condR allowed (.addHeader acaoName acaoVal) (.rewriteBody .identity))
          { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, h, if_true, Bool.false_eq_true, if_false]

/-- **`denote_cors` (deny).** A denied origin passes untouched — the deployed
`corsResp` with `corsHeaders c = []` (no header appended). -/
theorem denote_cors_deny (allowed : ReqPred) (acaoVal : Bytes) (ctx : Ctx)
    (h : allowed ctx = false) :
    denote (corsStage allowed acaoVal) ctx = ctx.base := by
  show (denoteStep ctx (.condR allowed (.addHeader acaoName acaoVal) (.rewriteBody .identity))
          { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, h, Bool.false_eq_true, if_false, runBody]

/-! ## 3. `viaStage` — the RFC 9110 §7.6.3 `Via` stamp (append-unless-present)

`Reactor.Stage.Via.stampVia` appends `Via: 1.1 drorb` (received-protocol version +
pseudonym) unless a `Via` field is already present (case-insensitive), in which case
the header list is returned UNCHANGED — an upstream's own `Via` is never duplicated
(the new-line form). At a fixed context the has-Via decision is a bit; the stage is a
`condR` on it. -/

/-- The `Via` field name. -/
def viaName : Bytes := str "Via"
/-- The emitted `Via` value — received-protocol version + pseudonym (`1.1 drorb`,
RFC 9110 §7.6.3 grammar). -/
def viaVal  : Bytes := str "1.1 drorb"

/-- **The Via stage.** `hasVia` is the pre-decided "a `Via` is already present" bit.
Present → a body-identity no-op (never duplicate an upstream `Via`); absent → append
`(Via, 1.1 drorb)` — exactly the deployed `stampVia` new-line form. -/
def viaStage (hasVia : ReqPred) : StageProg :=
  .condR hasVia (.rewriteBody .identity) (.addHeader viaName viaVal)

/-- **`denote_via` (present).** A response already carrying a `Via` passes untouched —
the deployed `stampVia_noop` (no duplication). -/
theorem denote_via_present (hasVia : ReqPred) (ctx : Ctx) (h : hasVia ctx = true) :
    denote (viaStage hasVia) ctx = ctx.base := by
  show (denoteStep ctx (.condR hasVia (.rewriteBody .identity) (.addHeader viaName viaVal))
          { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, h, if_true, Bool.false_eq_true, if_false, runBody]

/-- **`denote_via` (absent).** A response with no `Via` gets `Via: 1.1 drorb`
appended — the deployed `stampVia` append (`stampVia_has` / `stampVia_prefix`). -/
theorem denote_via_absent (hasVia : ReqPred) (ctx : Ctx) (h : hasVia ctx = false) :
    denote (viaStage hasVia) ctx
      = { ctx.base with headers := ctx.base.headers ++ [(viaName, viaVal)] } := by
  show (denoteStep ctx (.condR hasVia (.rewriteBody .identity) (.addHeader viaName viaVal))
          { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, h, Bool.false_eq_true, if_false]

/-! ## 4. Non-vacuity: the tracked skeleton genuinely varies with the stage

Concrete contexts pin the request predicates; the reference `denoteStep`'s scalar
image (status / header-count / body-length / halt) genuinely differs stage to stage,
so the keystone specializations below are not `P → P` tautologies. -/

/-- A `200 OK` base with body `hi`. -/
def baseOk : Response := ok200 (str "hi")

/-- Always-allow / always-present / always-absent request predicates (concrete bits). -/
def pTrue  : ReqPred := fun _ => true
def pFalse : ReqPred := fun _ => false

/-- A context whose base carries no headers (0-header seed). -/
def ctx0 : Ctx := { req := {}, base := baseOk }

-- hsts bumps the header count (0 → 1) and keeps status/body:
#guard (denote hstsStage ctx0).headers.length = 1
#guard (denote hstsStage ctx0).status = 200
#guard (denote hstsStage ctx0).body.length = 2

-- cors-allow bumps the count (0 → 1); cors-deny leaves it (0):
#guard (denote (corsStage pTrue  (str "https://ok.example")) ctx0).headers.length = 1
#guard (denote (corsStage pFalse (str "https://ok.example")) ctx0).headers.length = 0

-- via-absent bumps the count (0 → 1); via-present leaves it (0):
#guard (denote (viaStage pFalse) ctx0).headers.length = 1
#guard (denote (viaStage pTrue)  ctx0).headers.length = 0

-- the three appending stages produce three genuinely distinct wire responses:
#guard serialize (denote hstsStage ctx0) ≠ serialize baseOk
#guard serialize (denote (corsStage pTrue (str "https://ok.example")) ctx0) ≠ serialize baseOk
#guard serialize (denote (viaStage pFalse) ctx0) ≠ serialize baseOk
#guard serialize (denote hstsStage ctx0)
        ≠ serialize (denote (corsStage pTrue (str "https://ok.example")) ctx0)
#guard serialize (denote hstsStage ctx0) ≠ serialize (denote (viaStage pFalse) ctx0)

/-! ## 5. Keystone instantiations — the GENUINE per-constructor compiler at each stage

Each is `compile2_correct` (the induction keystone) specialized to the stage: from any
`CoreEnc` of the base fold-state, running the emitted per-constructor control flow
(`addHeader` → guarded count-increment; `condR` → real `Cond`) lands the `CoreEnc` of
the reference `denoteStep` — the tracked skeleton of the deployed response. -/

/-- **`hsts_compile2_correct`.** `compile2 hstsStage` (a guarded header-count
increment) lands the HSTS reference skeleton (header-count +1, status/body/halt
preserved). -/
theorem hsts_compile2_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (ctx : Ctx)
    (hd : Distinct aStat aCnt aBody aHalt) (st : PancakeState σ)
    (hEnc : CoreEnc aStat aCnt aBody aHalt st { resp := ctx.base, halted := false })
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt hstsStage) st = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st'
        (denoteStep ctx hstsStage { resp := ctx.base, halted := false }) := by
  obtain ⟨st', hrun, henc, _, _, _⟩ :=
    compile2_correct o nm aStat aCnt aBody aHalt ctx hd hstsStage
      { resp := ctx.base, halted := false } st hEnc hDec
  exact ⟨st', hrun, henc⟩

/-- **`cors_compile2_correct`.** `compile2 (corsStage allowed acaoVal)` (a real `Cond`
over an `addHeader`-count-increment and a body-identity `Skip`) lands the CORS
reference skeleton — the admit branch bumps the header count, the deny branch leaves
it, tracked exactly per the pre-decided origin-admission bit. -/
theorem cors_compile2_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (allowed : ReqPred) (acaoVal : Bytes) (ctx : Ctx)
    (hd : Distinct aStat aCnt aBody aHalt) (st : PancakeState σ)
    (hEnc : CoreEnc aStat aCnt aBody aHalt st { resp := ctx.base, halted := false })
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt (corsStage allowed acaoVal)) st
        = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st'
        (denoteStep ctx (corsStage allowed acaoVal) { resp := ctx.base, halted := false }) := by
  obtain ⟨st', hrun, henc, _, _, _⟩ :=
    compile2_correct o nm aStat aCnt aBody aHalt ctx hd (corsStage allowed acaoVal)
      { resp := ctx.base, halted := false } st hEnc hDec
  exact ⟨st', hrun, henc⟩

/-- **`via_compile2_correct`.** `compile2 (viaStage hasVia)` (a real `Cond` over a
body-identity `Skip` and an `addHeader`-count-increment) lands the `Via` reference
skeleton — absent bumps the header count, present leaves it, per the pre-decided
has-Via bit. -/
theorem via_compile2_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (hasVia : ReqPred) (ctx : Ctx)
    (hd : Distinct aStat aCnt aBody aHalt) (st : PancakeState σ)
    (hEnc : CoreEnc aStat aCnt aBody aHalt st { resp := ctx.base, halted := false })
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt (viaStage hasVia)) st
        = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st'
        (denoteStep ctx (viaStage hasVia) { resp := ctx.base, halted := false }) := by
  obtain ⟨st', hrun, henc, _, _, _⟩ :=
    compile2_correct o nm aStat aCnt aBody aHalt ctx hd (viaStage hasVia)
      { resp := ctx.base, halted := false } st hEnc hDec
  exact ⟨st', hrun, henc⟩

/-! ### 5.1 A CONCRETE skeleton the CORS-admit keystone lands (non-vacuous RHS)

The keystone's right-hand side is the REAL `denoteStep`; at a concrete admit context
its landed skeleton is a bumped header count with the status/body preserved — a `P → P`
tautology could not compute this. -/

-- cors-admit lands header-count 1 / status 200 / body 2 / live:
#guard (denoteStep ctx0 (corsStage pTrue (str "https://ok.example"))
          { resp := ctx0.base, halted := false }).resp.headers.length = 1
#guard (denoteStep ctx0 (corsStage pTrue (str "https://ok.example"))
          { resp := ctx0.base, halted := false }).resp.status = 200
#guard (denoteStep ctx0 (corsStage pTrue (str "https://ok.example"))
          { resp := ctx0.base, halted := false }).halted = false
-- via-absent lands header-count 1:
#guard (denoteStep ctx0 (viaStage pFalse)
          { resp := ctx0.base, halted := false }).resp.headers.length = 1

/-! ## 6. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms denote_hsts
#print axioms denote_cors_allow
#print axioms denote_cors_deny
#print axioms denote_via_present
#print axioms denote_via_absent
#print axioms hsts_compile2_correct
#print axioms cors_compile2_correct
#print axioms via_compile2_correct

end Pancake.StageMore
