/-
  Pancake/StageEvenMore.lean — FOUR MORE real serve stages expressed in the `StageProg`
  DSL, denoted to their DEPLOYED serve semantics, and compiled by the GENUINE
  per-constructor compiler `compile2` (StageCompile.lean), proven by the induction
  keystone `compile2_correct`.

  This file is ADDITIVE over StageCompile.lean / StageMore.lean: it introduces NO new
  compiler and NO new keystone. Each stage is a `StageProg` term built from the agreed
  constructors, with a `denote_<stage>` equation pinning its reference `Response` to the
  deployed stage's own effect, plus a `<stage>_compile2_correct` instantiation of the
  induction keystone showing the emitted per-constructor control flow lands the
  reference response SKELETON (status / header-count / body-length / halt) byte-exactly.

  THE FOUR STAGES (the deployed serve's header-transform / conditional / gate set):

   * `contentLocationStage` — the RFC 9110 §8.7 `Content-Location` stamp: an
     UNCONDITIONAL `addHeader` of `Content-Location: /canonical/resource` (the
     canonical-URI the deployed representation-metadata stage renders). Compiles to a
     guarded header-count increment.

   * `referrerPolicyStage` — the W3C Referrer-Policy stamp of the deployed
     security-header set: an UNCONDITIONAL `addHeader` of
     `Referrer-Policy: strict-origin-when-cross-origin` (the deployed policy's default).
     Compiles to a guarded header-count increment.

   * `cacheControlStaticStage` — the deployed static-asset cache directive: a
     CONTEXT-CONDITIONAL append. A static asset gets
     `Cache-Control: public, max-age=31536000, immutable`; a dynamic response is left
     to its own handler (append nothing) — a `condR` on the pre-decided is-static bit,
     the static branch an `addHeader`, the dynamic branch a body-identity no-op.
     Compiles to a real `Cond` over the two per-constructor fragments.

   * `preconditionGate` — the RFC 9110 §13.1.2 `If-None-Match` precondition: when the
     validator matches, short-circuit with `304 Not Modified` (skip the body render and
     every later stage) — the deployed conditional-request gate's `.respond` decision.
     Realized as a `gate` on the pre-decided validator-match bit; compiles to the real
     nested `If` that writes the status and SETS THE HALT FLAG.

  WHAT IS PROVEN, per stage:
   * a `denote_<stage>` equation grounding the reference fold in the deployed effect;
   * `#guard` non-vacuity: each stage's tracked skeleton genuinely differs from the
     base (content-location / referrer-policy / cache-static-asset bump the header
     count; cache-dynamic does not; the precondition match flips the status to 304 and
     halts) and the stages differ from each other;
   * a `<stage>_compile2_correct` specialization of the induction keystone: from any
     `CoreEnc` of the base state, `compile2 <stage>` lands the `CoreEnc` of the
     reference `denoteStep`. This is the GENUINE per-constructor compiler
     (`addHeader` → guarded count-increment, `condR` → real `Cond`, `gate` → nested
     `If` + halt-set), NOT the copy-stub.

  RESIDUALS (named, inherited from StageCompile.lean, NOT re-opened here):
   * `compile2` tracks the SCALAR skeleton `(status, |headers|, |body|, halted)`; the
     variable-length header NAME/VALUE bytes (the `Content-Location` URI, the
     `Referrer-Policy` token, the `Cache-Control` directive string) are the byte-content
     the outer header-write loop materializes — the standing SerializeHeaders /
     `Div`/`Mod` residual, untouched.
   * `preconditionGate` carries the bare `304` status; the validator that decides the
     match (the `ETag`/`If-None-Match` comparison) is the policy decision, upstream of
     this stage and modelled by the pre-decided request predicate.
-/
import Pancake.StageCompile

namespace Pancake.StageEvenMore

open Pancake Pancake.SerializeCompile Pancake.StageProg Pancake.StageCompile

variable {σ : Type}

/-! ## 1. `contentLocationStage` — the RFC 9110 §8.7 `Content-Location` stamp -/

/-- The `Content-Location` field name. -/
def contentLocationName : Bytes := str "Content-Location"
/-- The `Content-Location` value — the canonical-URI the deployed
representation-metadata stage renders. -/
def contentLocationVal  : Bytes := str "/canonical/resource"

/-- **The Content-Location stage.** Always passes, stamping the canonical URI onto the
response — a single `addHeader` (the deployed representation-metadata stamp). -/
def contentLocationStage : StageProg := .addHeader contentLocationName contentLocationVal

/-- **`denote_contentLocation`.** The stage appends its one field to the base response —
exactly the deployed stamp of `Content-Location` (`base.headers ++ [cl]`). -/
theorem denote_contentLocation (ctx : Ctx) :
    denote contentLocationStage ctx
      = { ctx.base with headers := ctx.base.headers ++ [(contentLocationName, contentLocationVal)] } := by
  show (denoteStep ctx (.addHeader contentLocationName contentLocationVal)
          { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, Bool.false_eq_true, if_false]

/-! ## 2. `referrerPolicyStage` — the deployed `Referrer-Policy` stamp -/

/-- The `Referrer-Policy` field name. -/
def referrerPolicyName : Bytes := str "Referrer-Policy"
/-- The `Referrer-Policy` value — the deployed security policy's default
(`strict-origin-when-cross-origin`). -/
def referrerPolicyVal  : Bytes := str "strict-origin-when-cross-origin"

/-- **The Referrer-Policy stage.** Always passes, stamping the deployed
`Referrer-Policy` default onto the response — a single `addHeader`. -/
def referrerPolicyStage : StageProg := .addHeader referrerPolicyName referrerPolicyVal

/-- **`denote_referrerPolicy`.** The stage appends its one field to the base response —
exactly the deployed stamp of `Referrer-Policy` (`base.headers ++ [rp]`). -/
theorem denote_referrerPolicy (ctx : Ctx) :
    denote referrerPolicyStage ctx
      = { ctx.base with headers := ctx.base.headers ++ [(referrerPolicyName, referrerPolicyVal)] } := by
  show (denoteStep ctx (.addHeader referrerPolicyName referrerPolicyVal)
          { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, Bool.false_eq_true, if_false]

/-! ## 3. `cacheControlStaticStage` — the deployed static-asset cache directive

A static asset gets a long-lived immutable cache directive; a dynamic response is left
to its own handler (no directive appended) — the deployed static-serve's conditional
`Cache-Control` stamp. At a fixed context the is-static decision is a bit; the stage is
a `condR` on it. -/

/-- The `Cache-Control` field name. -/
def cacheControlName : Bytes := str "Cache-Control"
/-- The static-asset `Cache-Control` value — a one-year immutable public cache
directive (the deployed static-serve policy). -/
def cacheControlStaticVal : Bytes := str "public, max-age=31536000, immutable"

/-- **The static-cache stage.** `isStatic` is the pre-decided is-static-asset bit.
Static → append `(Cache-Control, immutable)`; dynamic → a body-identity no-op (append
nothing) — exactly the deployed static-serve's conditional cache stamp. -/
def cacheControlStaticStage (isStatic : ReqPred) : StageProg :=
  .condR isStatic (.addHeader cacheControlName cacheControlStaticVal) (.rewriteBody .identity)

/-- **`denote_cacheStatic` (asset).** A static asset gets its `Cache-Control` directive
appended — the deployed static-serve stamp (`base.headers ++ [cc]`). -/
theorem denote_cacheStatic_asset (isStatic : ReqPred) (ctx : Ctx) (h : isStatic ctx = true) :
    denote (cacheControlStaticStage isStatic) ctx
      = { ctx.base with headers := ctx.base.headers ++ [(cacheControlName, cacheControlStaticVal)] } := by
  show (denoteStep ctx (.condR isStatic (.addHeader cacheControlName cacheControlStaticVal)
          (.rewriteBody .identity)) { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, h, if_true, Bool.false_eq_true, if_false]

/-- **`denote_cacheStatic` (dynamic).** A dynamic response passes untouched — no
`Cache-Control` directive appended (left to the handler). -/
theorem denote_cacheStatic_dynamic (isStatic : ReqPred) (ctx : Ctx) (h : isStatic ctx = false) :
    denote (cacheControlStaticStage isStatic) ctx = ctx.base := by
  show (denoteStep ctx (.condR isStatic (.addHeader cacheControlName cacheControlStaticVal)
          (.rewriteBody .identity)) { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, h, Bool.false_eq_true, if_false, runBody]

/-! ## 4. `preconditionGate` — the RFC 9110 §13.1.2 `If-None-Match` precondition

When the validator matches (the cached representation is still fresh), short-circuit
with `304 Not Modified`: skip the body render and every later stage — the deployed
conditional-request gate's `.respond` decision. At a fixed context the validator-match
decision is a bit; the stage is a `gate` on it. -/

/-- **The precondition gate.** `matched` is the pre-decided validator-match bit. When it
fires, short-circuit with `304 Not Modified` — the deployed `If-None-Match` gate. -/
def preconditionGate (matched : ReqPred) : StageProg := .gate matched 304

/-- **`denote_precondition` (match).** A matched validator short-circuits the response
to status `304` — the deployed conditional-request decision (a `304` on the wire). -/
theorem denote_precondition_match (matched : ReqPred) (ctx : Ctx) (h : matched ctx = true) :
    denote (preconditionGate matched) ctx = { ctx.base with status := 304 } := by
  show (denoteStep ctx (.gate matched 304) { resp := ctx.base, halted := false }).resp = _
  rw [denoteStep_gate_fires ctx _ 304 _ rfl h]

/-- **`denote_precondition` (no match).** A stale validator passes untouched — the
handler's base response is returned unchanged. -/
theorem denote_precondition_nomatch (matched : ReqPred) (ctx : Ctx) (h : matched ctx = false) :
    denote (preconditionGate matched) ctx = ctx.base := by
  show (denoteStep ctx (.gate matched 304) { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, Bool.false_eq_true, if_false, h]

/-! ## 5. Non-vacuity: the tracked skeleton genuinely varies with the stage

Concrete contexts pin the request predicates; the reference `denoteStep`'s scalar
image (status / header-count / body-length / halt) genuinely differs stage to stage,
so the keystone specializations below are not `P → P` tautologies. -/

/-- A `200 OK` base with body `hi`. -/
def baseOk : Response := ok200 (str "hi")

/-- Always-true / always-false request predicates (concrete bits). -/
def pTrue  : ReqPred := fun _ => true
def pFalse : ReqPred := fun _ => false

/-- A context whose base carries no headers (0-header seed). -/
def ctx0 : Ctx := { req := {}, base := baseOk }

-- content-location bumps the header count (0 → 1) and keeps status/body:
#guard (denote contentLocationStage ctx0).headers.length = 1
#guard (denote contentLocationStage ctx0).status = 200
#guard (denote contentLocationStage ctx0).body.length = 2

-- referrer-policy bumps the header count (0 → 1):
#guard (denote referrerPolicyStage ctx0).headers.length = 1

-- cache-static-asset bumps the count (0 → 1); cache-dynamic leaves it (0):
#guard (denote (cacheControlStaticStage pTrue)  ctx0).headers.length = 1
#guard (denote (cacheControlStaticStage pFalse) ctx0).headers.length = 0

-- the precondition MATCH short-circuits to 304 AND halts; NO-MATCH passes at 200:
#guard (denoteStep ctx0 (preconditionGate pTrue)
          { resp := ctx0.base, halted := false }).resp.status = 304
#guard (denoteStep ctx0 (preconditionGate pTrue)
          { resp := ctx0.base, halted := false }).halted = true
#guard (denote (preconditionGate pFalse) ctx0).status = 200
-- the gate keeps the body (a 304 body-drop is a serializer concern, not the gate's
-- status decision), so the tracked body length is preserved through the short-circuit:
#guard (denoteStep ctx0 (preconditionGate pTrue)
          { resp := ctx0.base, halted := false }).resp.body.length = 2

-- the four stages produce genuinely distinct wire responses (vs the base and each other):
#guard serialize (denote contentLocationStage ctx0) ≠ serialize baseOk
#guard serialize (denote referrerPolicyStage ctx0) ≠ serialize baseOk
#guard serialize (denote (cacheControlStaticStage pTrue) ctx0) ≠ serialize baseOk
#guard serialize (denote (preconditionGate pTrue) ctx0) ≠ serialize baseOk
#guard serialize (denote contentLocationStage ctx0)
        ≠ serialize (denote referrerPolicyStage ctx0)
#guard serialize (denote contentLocationStage ctx0)
        ≠ serialize (denote (cacheControlStaticStage pTrue) ctx0)
#guard serialize (denote (preconditionGate pTrue) ctx0)
        ≠ serialize (denote contentLocationStage ctx0)

/-! ## 6. Keystone instantiations — the GENUINE per-constructor compiler at each stage

Each is `compile2_correct` (the induction keystone) specialized to the stage: from any
`CoreEnc` of the base fold-state, running the emitted per-constructor control flow
lands the `CoreEnc` of the reference `denoteStep` — the tracked skeleton of the
deployed response. -/

/-- **`contentLocation_compile2_correct`.** `compile2 contentLocationStage` (a guarded
header-count increment) lands the Content-Location reference skeleton (header-count +1,
status/body/halt preserved). -/
theorem contentLocation_compile2_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (ctx : Ctx)
    (hd : Distinct aStat aCnt aBody aHalt) (st : PancakeState σ)
    (hEnc : CoreEnc aStat aCnt aBody aHalt st { resp := ctx.base, halted := false })
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt contentLocationStage) st = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st'
        (denoteStep ctx contentLocationStage { resp := ctx.base, halted := false }) := by
  obtain ⟨st', hrun, henc, _, _, _⟩ :=
    compile2_correct o nm aStat aCnt aBody aHalt ctx hd contentLocationStage
      { resp := ctx.base, halted := false } st hEnc hDec
  exact ⟨st', hrun, henc⟩

/-- **`referrerPolicy_compile2_correct`.** `compile2 referrerPolicyStage` (a guarded
header-count increment) lands the Referrer-Policy reference skeleton. -/
theorem referrerPolicy_compile2_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (ctx : Ctx)
    (hd : Distinct aStat aCnt aBody aHalt) (st : PancakeState σ)
    (hEnc : CoreEnc aStat aCnt aBody aHalt st { resp := ctx.base, halted := false })
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt referrerPolicyStage) st = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st'
        (denoteStep ctx referrerPolicyStage { resp := ctx.base, halted := false }) := by
  obtain ⟨st', hrun, henc, _, _, _⟩ :=
    compile2_correct o nm aStat aCnt aBody aHalt ctx hd referrerPolicyStage
      { resp := ctx.base, halted := false } st hEnc hDec
  exact ⟨st', hrun, henc⟩

/-- **`cacheStatic_compile2_correct`.** `compile2 (cacheControlStaticStage isStatic)` (a
real `Cond` over an `addHeader`-count-increment and a body-identity `Skip`) lands the
static-cache reference skeleton — the asset branch bumps the header count, the dynamic
branch leaves it, tracked exactly per the pre-decided is-static bit. -/
theorem cacheStatic_compile2_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (isStatic : ReqPred) (ctx : Ctx)
    (hd : Distinct aStat aCnt aBody aHalt) (st : PancakeState σ)
    (hEnc : CoreEnc aStat aCnt aBody aHalt st { resp := ctx.base, halted := false })
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt (cacheControlStaticStage isStatic)) st
        = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st'
        (denoteStep ctx (cacheControlStaticStage isStatic) { resp := ctx.base, halted := false }) := by
  obtain ⟨st', hrun, henc, _, _, _⟩ :=
    compile2_correct o nm aStat aCnt aBody aHalt ctx hd (cacheControlStaticStage isStatic)
      { resp := ctx.base, halted := false } st hEnc hDec
  exact ⟨st', hrun, henc⟩

/-- **`precondition_compile2_correct`.** `compile2 (preconditionGate matched)` (a real
nested `If` that, when the validator matches, writes `304` and SETS THE HALT FLAG)
lands the precondition reference skeleton — a match flips the status to 304 and halts,
a stale validator leaves the skeleton, tracked per the pre-decided match bit. -/
theorem precondition_compile2_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (matched : ReqPred) (ctx : Ctx)
    (hd : Distinct aStat aCnt aBody aHalt) (st : PancakeState σ)
    (hEnc : CoreEnc aStat aCnt aBody aHalt st { resp := ctx.base, halted := false })
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt (preconditionGate matched)) st
        = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st'
        (denoteStep ctx (preconditionGate matched) { resp := ctx.base, halted := false }) := by
  obtain ⟨st', hrun, henc, _, _, _⟩ :=
    compile2_correct o nm aStat aCnt aBody aHalt ctx hd (preconditionGate matched)
      { resp := ctx.base, halted := false } st hEnc hDec
  exact ⟨st', hrun, henc⟩

/-! ### 6.1 A CONCRETE skeleton the precondition-match keystone lands (non-vacuous RHS)

The keystone's right-hand side is the REAL `denoteStep`; at a concrete match context its
landed skeleton is status 304 with the halt flag set — a `P → P` tautology could not
compute this. -/

-- precondition-match lands status 304 / halted / body preserved:
#guard (denoteStep ctx0 (preconditionGate pTrue)
          { resp := ctx0.base, halted := false }).resp.status = 304
#guard (denoteStep ctx0 (preconditionGate pTrue)
          { resp := ctx0.base, halted := false }).halted = true
-- cache-static-asset lands header-count 1 / status 200 / live:
#guard (denoteStep ctx0 (cacheControlStaticStage pTrue)
          { resp := ctx0.base, halted := false }).resp.headers.length = 1
#guard (denoteStep ctx0 (cacheControlStaticStage pTrue)
          { resp := ctx0.base, halted := false }).halted = false

/-! ## 7. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms denote_contentLocation
#print axioms denote_referrerPolicy
#print axioms denote_cacheStatic_asset
#print axioms denote_cacheStatic_dynamic
#print axioms denote_precondition_match
#print axioms denote_precondition_nomatch
#print axioms contentLocation_compile2_correct
#print axioms referrerPolicy_compile2_correct
#print axioms cacheStatic_compile2_correct
#print axioms precondition_compile2_correct

end Pancake.StageEvenMore
