/-
  Pancake/CondRespProto.lean — A PROTOTYPE for `condResp` (response-decided
  branching), the extension that unblocks the response-decided stamps.

  STATUS: a standalone PROTOTYPE. It edits NOTHING (imports the two-phase onion
  chain read-only). It is the design study for a later, careful fold-in of
  `condResp` into the response algebra of the onion DSL — NOT the fold-in itself.

  THE RESIDUAL THIS ADDRESSES. The response algebra `RespProg` has only a
  request-decided conditional (`condR : ReqPred = Ctx → Bool`). It CANNOT read the
  response threaded up from the inner onion. The deployed stamps whose decision
  keys on the ARRIVING response — `r.status == 200`, `!hasX r.headers`,
  `isTransformed r.headers` — are therefore not expressible, and pinning them at
  `ctx.base` would assert a serve the deployed stage does not perform. They were
  left blocked on a `condResp` constructor whose shape was specified but not built.

  WHAT THIS FILE BUILDS (all against the CORRECT interpreter — `denoteR`/`runChain`
  of the onion, which carries response phases onto a refusal):

   1. The RESPONSE-DECIDED branch. Because the existing `RespProg`/`denoteR` are
      fixed (this file edits nothing), the extension is prototyped as a NEW algebra
      `RespProgR` that EMBEDS `RespProg` (`.base`) and adds
        * `condResp (c : Ctx → Response → Bool)` — the general response-decided
          branch, whose denotation applies `c` to the ARRIVING `r` (§1);
        * `condStatus (k : Nat)` — the STATUS-KEYED specialization, the tractable
          slice that compiles to one `.cond` on the `aStat` cell (§1, §7).
      `denoteRR` stays a PLAIN fold (no halt flag, no gate) — `condResp` is a
      response transform, so the gate/response split of the onion is preserved and
      `runChain`/`respFold` need no change (§3).

   2. IT COMPOSES WITH THE ONION. `runChainR`/`respFoldR` transliterate the onion
      over `RespProgR` stages, and the five composition laws + the whole-chain gate
      keystone hold verbatim (§3) — a response-decided branch runs in the ONRESP
      phase. The witness `condRespStamp_carries_on_gate_refusal` (§4) shows a
      response-decided stamp OUTSIDE a firing gate deciding on the gate's REFUSAL
      (the inner result) — the exact capability `condR` lacked.

   3. THE STATUS-KEYED COMPILE FRAGMENT. `compileRR` lowers `.condStatus k a b` to
      `.cond (aStat == k) (…) (…)` — one comparison against the live status cell —
      and `compileRR_correct` (§7) proves it lands `Enc3 (denoteRR …)`, EXACT under
      the well-formedness invariant `status < 2^64` threaded through `Enc3`
      (`ofNat64_inj`). The general `condResp` node is NOT compiled (it needs a
      machine-side header representation) — `compileRR_correct` is gated on
      `Lowerable`, which excludes it, so nothing false is claimed.

   4. THE 8 STATUS-KEYED STAMPS, PINNED THROUGH `condResp` (§5): warning, link,
      cache-control, expires, immutable, last-modified, retry-after,
      content-location. Each gets a `denoteRR` pin (= the deployed conditional
      append `stampFnR`) and a `runChainR` pin (the single-stage serve). The
      decisions read the response (status and/or headers); they are opaque
      parameters named for what the deployed stage computes.

  WHAT STILL NEEDS MORE THAN `condResp` (the honest residual, §8 note):
   * The header-LIST-reading decisions (`!hasLink`/`!hasLm`/`!hasWarning`/
     `isTransformed r.headers`, and the whole unless-present family) DENOTE through
     `condResp` but do NOT compile: `Enc3` carries only the header COUNT (`aCnt`),
     not the list. They wait on a machine-side header representation.
   * cache-status additionally needs a response-READING VALUE (`addHeaderOf :
     Ctx → Response → Bytes`) — strictly beyond `condResp`.
   * retry-after's `needsRetryAfter r.status` is a status SET, not one equality; it
     compiles as a NEST of `condStatus` equalities (an easy extension of the single
     comparison proven here).

  Axiom audit at the end: expect ⊆ {propext, Classical.choice, Quot.sound}, 0 sorryAx.
-/
import Pancake.StageLift2

namespace Pancake.CondRespProto

open Pancake Pancake.SerializeCompile Pancake.StageProg Pancake.StageCompile
open Pancake.StageOnion Pancake.StageLift2
open Pancake.EmitCorrectCompose (sem_cond)
open Pancake.StructModel (wordAt eval_loadWord_of_wordAt eval_op_add eval_var)

variable {σ : Type}

/-! ## 1. `RespProgR` — the response algebra EXTENDED with a response-decided branch

`RespProgR` embeds the gate-free algebra (`.base`) and adds a response-decided
conditional. `denoteRR` is still a PLAIN fold: `condResp`'s predicate is applied to
the ARRIVING `r` (the `denoteRR` argument), which under the onion is the inner
result — exactly what `condR : Ctx → Bool` could not see. -/

/-- The extended response-transform algebra:
* `base p`        — embed the existing gate-free `RespProg`;
* `seqR a b`      — sequencing (kept explicit so the extension is self-contained);
* `condResp c a b`— the GENERAL response-decided branch (`c : Ctx → Response → Bool`);
* `condStatus k a b` — the STATUS-KEYED specialization that COMPILES (§7). -/
inductive RespProgR
  | base       (p : RespProg)
  | seqR       (a b : RespProgR)
  | condResp   (c : Ctx → Response → Bool) (a b : RespProgR)
  | condStatus (k : Nat) (a b : RespProgR)

/-- **The extended denotation — still a plain fold.** The `condResp` clause applies
`c` to the ARRIVING `r` (never to `ctx.base`): that is the whole content of the
extension — the decision sees the inner onion's result. No `halted` flag, no gate:
`condResp`/`condStatus` are response TRANSFORMS, so the onion's gate/response split
is untouched. -/
def denoteRR (ctx : Ctx) : RespProgR → Response → Response
  | .base p, r        => denoteR ctx p r
  | .seqR a b, r      => denoteRR ctx b (denoteRR ctx a r)
  | .condResp c a b, r => if c ctx r then denoteRR ctx a r else denoteRR ctx b r
  | .condStatus k a b, r => if r.status = k then denoteRR ctx a r else denoteRR ctx b r

/-- `condStatus` is exactly the `condResp` instance keyed on `r.status = k`: the
compilable slice is a genuine special case of the general branch, not an ad-hoc
addition. -/
theorem denoteRR_condStatus_eq (ctx : Ctx) (k : Nat) (a b : RespProgR) (r : Response) :
    denoteRR ctx (.condStatus k a b) r
      = denoteRR ctx (.condResp (fun _ r => decide (r.status = k)) a b) r := by
  show (if r.status = k then denoteRR ctx a r else denoteRR ctx b r)
     = (if (decide (r.status = k) = true) then denoteRR ctx a r else denoteRR ctx b r)
  by_cases h : r.status = k
  · rw [if_pos h, if_pos (show decide (r.status = k) = true by simp [h])]
  · rw [if_neg h, if_neg (show ¬ (decide (r.status = k) = true) by simp [h])]

/-! ## 2. `StageSpecR` + the onion fold over the extended algebra

The two-phase stage, with the response phase now a `RespProgR`. The REFUSAL stays a
gate-free `RespProg` (a refusal is written by the stage, not read off the response),
so it keeps `denoteR`; only `onResp` gains the response-decided power. -/

/-- A two-phase stage whose response phase may branch on the response. -/
structure StageSpecR where
  guard   : ReqPred
  refusal : RespProg
  onResp  : RespProgR

/-- The response-only fold over `RespProgR` stages (drorb's `runResp`). -/
def respFoldR (ctx : Ctx) : List StageSpecR → Response → Response
  | [], r => r
  | s :: rest, r => denoteRR ctx s.onResp (respFoldR ctx rest r)

/-- **The onion fold over the extended algebra** — identical shape to `runChain`;
the refusal uses `denoteR` (unchanged), the response phases use `denoteRR`. -/
def runChainR (ctx : Ctx) (handler : Ctx → Response) : List StageSpecR → Response
  | [] => handler ctx
  | s :: rest =>
    if s.guard ctx then respFoldR ctx rest (denoteR ctx s.refusal blankResp)
    else denoteRR ctx s.onResp (runChainR ctx handler rest)

/-! ## 3. The composition calculus — the onion laws, verbatim over `RespProgR`

`denoteRR` is a fold like `denoteR`, and the fold structure of `runChainR` is
identical to `runChain`, so every onion law ports 1:1. This is the proof that a
response-decided branch changes NOTHING about how the two phases compose. -/

theorem runChainR_nil (ctx : Ctx) (h : Ctx → Response) : runChainR ctx h [] = h ctx := rfl

theorem runChainR_cons (ctx : Ctx) (h : Ctx → Response) (s : StageSpecR) (rest : List StageSpecR) :
    runChainR ctx h (s :: rest)
      = if s.guard ctx then respFoldR ctx rest (denoteR ctx s.refusal blankResp)
        else denoteRR ctx s.onResp (runChainR ctx h rest) := rfl

theorem respFoldR_cons (ctx : Ctx) (s : StageSpecR) (rest : List StageSpecR) (r : Response) :
    respFoldR ctx (s :: rest) r = denoteRR ctx s.onResp (respFoldR ctx rest r) := rfl

theorem runChainR_gate_short_circuits (ctx : Ctx) (h : Ctx → Response)
    (s : StageSpecR) (rest : List StageSpecR) (hg : s.guard ctx = true) :
    runChainR ctx h (s :: rest) = respFoldR ctx rest (denoteR ctx s.refusal blankResp) := by
  rw [runChainR_cons, hg, if_pos rfl]

theorem runChainR_stage_effect (ctx : Ctx) (h : Ctx → Response)
    (s : StageSpecR) (rest : List StageSpecR) (hs : s.guard ctx = false) :
    runChainR ctx h (s :: rest) = denoteRR ctx s.onResp (runChainR ctx h rest) := by
  rw [runChainR_cons, hs, if_neg (show ¬ ((false : Bool) = true) by decide)]

theorem respFoldR_append (ctx : Ctx) (xs ys : List StageSpecR) (r : Response) :
    respFoldR ctx (xs ++ ys) r = respFoldR ctx xs (respFoldR ctx ys r) := by
  induction xs with
  | nil => rfl
  | cons s ss ih =>
    show denoteRR ctx s.onResp (respFoldR ctx (ss ++ ys) r)
      = denoteRR ctx s.onResp (respFoldR ctx ss (respFoldR ctx ys r))
    rw [ih]

/-- **The whole-chain gate keystone, over `RespProgR`.** A fired gate at arbitrary
depth erases the handler and every inner request phase, yet EVERY other stage's
response phase (passed prefix AND skipped tail) still runs over the refusal — now
including response-decided branches, which read the refusal. -/
theorem runChainR_gate_keystone (ctx : Ctx) (handler : Ctx → Response)
    (pre : List StageSpecR) (g : StageSpecR) (rest : List StageSpecR)
    (hpre : ∀ s ∈ pre, s.guard ctx = false) (hg : g.guard ctx = true) :
    runChainR ctx handler (pre ++ g :: rest)
      = respFoldR ctx (pre ++ rest) (denoteR ctx g.refusal blankResp) := by
  induction pre with
  | nil =>
    show runChainR ctx handler (g :: rest) = respFoldR ctx rest (denoteR ctx g.refusal blankResp)
    exact runChainR_gate_short_circuits ctx handler g rest hg
  | cons s ss ih =>
    have hs : s.guard ctx = false := hpre s (by simp)
    have hss : ∀ t ∈ ss, t.guard ctx = false := fun t ht => hpre t (by simp [ht])
    show runChainR ctx handler (s :: (ss ++ g :: rest))
      = denoteRR ctx s.onResp (respFoldR ctx (ss ++ rest) (denoteR ctx g.refusal blankResp))
    rw [runChainR_stage_effect ctx handler s _ hs, ih hss]

/-! ## 4. The response-decided stamp — the capability `condR` lacked

A response-decided stamp: pass the request, then append `(name,val)` under a
decision that reads the ARRIVING response. `stampProgR` builds it as
`condResp c (addHeader name val) skip`. -/

/-- The deployed response-decided stamp's functional effect: append `(name,val)`
exactly when `c` fires at this context AND arriving response. -/
def stampFnR (c : Ctx → Response → Bool) (name val : Bytes) (ctx : Ctx) (r : Response) : Response :=
  if c ctx r then { r with headers := r.headers ++ [(name, val)] } else r

/-- The response-decided stamp program. -/
def stampProgR (c : Ctx → Response → Bool) (name val : Bytes) : RespProgR :=
  .condResp c (.base (.addHeader name val)) (.base .skip)

/-- **`denoteRR_stampProgR` — THE `condResp` STAMP LIFT.** For ANY response-decided
decision `c`, name, value, context and ARRIVING response `r`, the stamp denotes to
the deployed conditional append `stampFnR`. Both branches discharged (not vacuous),
and `r` is the true inner result — the whole point of `condResp`. -/
theorem denoteRR_stampProgR (c : Ctx → Response → Bool) (name val : Bytes)
    (ctx : Ctx) (r : Response) :
    denoteRR ctx (stampProgR c name val) r = stampFnR c name val ctx r := by
  show (if c ctx r then denoteRR ctx (.base (.addHeader name val)) r else denoteRR ctx (.base .skip) r)
      = stampFnR c name val ctx r
  unfold stampFnR
  cases h : c ctx r with
  | true => rfl
  | false => rfl

/-- The response-decided stamp STAGE — passes, then stamps under its decision. -/
def stampSpecR (c : Ctx → Response → Bool) (name val : Bytes) : StageSpecR :=
  { guard := fun _ => false, refusal := .skip, onResp := stampProgR c name val }

/-- **`runChainR_stampSpecR`** — a single response-decided stamp over a handler
passes to the handler and stamps under its decision on the HANDLER's response. -/
theorem runChainR_stampSpecR (c : Ctx → Response → Bool) (name val : Bytes)
    (handler : Ctx → Response) (ctx : Ctx) :
    runChainR ctx handler [stampSpecR c name val] = stampFnR c name val ctx (handler ctx) := by
  rw [runChainR_stage_effect ctx handler (stampSpecR c name val) [] rfl, runChainR_nil]
  show denoteRR ctx (stampProgR c name val) (handler ctx) = _
  rw [denoteRR_stampProgR]

/-- The gate stage over the extended algebra (refusal built over `blankResp`). -/
def gateSpecR (fire : ReqPred) (r : Response) : StageSpecR :=
  { guard := fire, refusal := refusalProg r, onResp := .base .skip }

/-- **`condRespStamp_carries_on_gate_refusal` — THE NEW CAPABILITY.** A response-
decided stamp OUTSIDE a firing gate decides on the gate's REFUSAL — the inner
result the stamp actually sees — and carries (or withholds) its header accordingly.
This is exactly what `condR : Ctx → Bool` could not express: the decision is a
function of the arriving refusal, not of `ctx`. For ANY handler (never runs). -/
theorem condRespStamp_carries_on_gate_refusal (c : Ctx → Response → Bool) (name val : Bytes)
    (fire : ReqPred) (refuseR : Response) (handler : Ctx → Response) (ctx : Ctx)
    (hfire : fire ctx = true) :
    runChainR ctx handler [stampSpecR c name val, gateSpecR fire refuseR]
      = stampFnR c name val ctx refuseR := by
  have hpre : ∀ s ∈ [stampSpecR c name val], s.guard ctx = false := by
    intro s hs; simp at hs; rw [hs]; rfl
  have hg : (gateSpecR fire refuseR).guard ctx = true := hfire
  rw [show ([stampSpecR c name val, gateSpecR fire refuseR] : List StageSpecR)
        = [stampSpecR c name val] ++ gateSpecR fire refuseR :: [] from rfl,
      runChainR_gate_keystone ctx handler [stampSpecR c name val] (gateSpecR fire refuseR) []
        hpre hg]
  show denoteRR ctx (stampProgR c name val) (denoteR ctx (refusalProg refuseR) blankResp) = _
  rw [denoteR_refusalProg, denoteRR_stampProgR]

/-! ## 5. THE 8 STATUS-KEYED STAMPS — pinned through `condResp`

Each deployed response-decided stamp: a decision that reads the arriving response
(status and/or headers) and, when it fires, appends one header. The decisions are
opaque parameters named for what the deployed stage computes (`isStaticGet`,
`hasLink`, `needsRetryAfter`, …). Each gets a `denoteRR` pin (the response phase over
ANY arriving `r`) and a `runChainR` pin (the single-stage serve), both one line
through `denoteRR_stampProgR` / `runChainR_stampSpecR`. -/

def warnName  : Bytes := str "Warning"
def linkName  : Bytes := str "Link"
def ccName    : Bytes := str "Cache-Control"
def expiresName : Bytes := str "Expires"
def lmName    : Bytes := str "Last-Modified"
def retryName : Bytes := str "Retry-After"
def clocName  : Bytes := str "Content-Location"

/-- 8. warning — `isTransformed r.headers && !hasWarning r.headers` (header-decided). -/
def warningDec (isTransformed hasWarning : List (Bytes × Bytes) → Bool) : Ctx → Response → Bool :=
  fun _ r => isTransformed r.headers && ! hasWarning r.headers
def warningSpecR (isTransformed hasWarning : List (Bytes × Bytes) → Bool) (val : Bytes) : StageSpecR :=
  stampSpecR (warningDec isTransformed hasWarning) warnName val
theorem denoteRR_warning (isTransformed hasWarning : List (Bytes × Bytes) → Bool)
    (val : Bytes) (ctx : Ctx) (r : Response) :
    denoteRR ctx (warningSpecR isTransformed hasWarning val).onResp r
      = stampFnR (warningDec isTransformed hasWarning) warnName val ctx r :=
  denoteRR_stampProgR _ warnName val ctx r
theorem runChainR_warning (isTransformed hasWarning : List (Bytes × Bytes) → Bool)
    (val : Bytes) (handler : Ctx → Response) (ctx : Ctx) :
    runChainR ctx handler [warningSpecR isTransformed hasWarning val]
      = stampFnR (warningDec isTransformed hasWarning) warnName val ctx (handler ctx) :=
  runChainR_stampSpecR _ warnName val handler ctx

/-- 9. link-preload — `r.status == 200 && !hasLink r.headers`. -/
def linkDec (hasLink : List (Bytes × Bytes) → Bool) : Ctx → Response → Bool :=
  fun _ r => decide (r.status = 200) && ! hasLink r.headers
def linkSpecR (hasLink : List (Bytes × Bytes) → Bool) (val : Bytes) : StageSpecR :=
  stampSpecR (linkDec hasLink) linkName val
theorem denoteRR_link (hasLink : List (Bytes × Bytes) → Bool) (val : Bytes) (ctx : Ctx) (r : Response) :
    denoteRR ctx (linkSpecR hasLink val).onResp r = stampFnR (linkDec hasLink) linkName val ctx r :=
  denoteRR_stampProgR _ linkName val ctx r
theorem runChainR_link (hasLink : List (Bytes × Bytes) → Bool) (val : Bytes)
    (handler : Ctx → Response) (ctx : Ctx) :
    runChainR ctx handler [linkSpecR hasLink val]
      = stampFnR (linkDec hasLink) linkName val ctx (handler ctx) :=
  runChainR_stampSpecR _ linkName val handler ctx

/-- 11. cache-control — `r.status == 200 && isStaticGet c`. -/
def cacheControlDec (isStaticGet : ReqPred) : Ctx → Response → Bool :=
  fun c r => decide (r.status = 200) && isStaticGet c
def cacheControlSpecR (isStaticGet : ReqPred) (val : Bytes) : StageSpecR :=
  stampSpecR (cacheControlDec isStaticGet) ccName val
theorem denoteRR_cacheControl (isStaticGet : ReqPred) (val : Bytes) (ctx : Ctx) (r : Response) :
    denoteRR ctx (cacheControlSpecR isStaticGet val).onResp r
      = stampFnR (cacheControlDec isStaticGet) ccName val ctx r :=
  denoteRR_stampProgR _ ccName val ctx r
theorem runChainR_cacheControl (isStaticGet : ReqPred) (val : Bytes)
    (handler : Ctx → Response) (ctx : Ctx) :
    runChainR ctx handler [cacheControlSpecR isStaticGet val]
      = stampFnR (cacheControlDec isStaticGet) ccName val ctx (handler ctx) :=
  runChainR_stampSpecR _ ccName val handler ctx

/-- 12. asset-expires — same decision (`r.status == 200 && isStaticGet c`). -/
def expiresSpecR (isStaticGet : ReqPred) (val : Bytes) : StageSpecR :=
  stampSpecR (cacheControlDec isStaticGet) expiresName val
theorem denoteRR_expires (isStaticGet : ReqPred) (val : Bytes) (ctx : Ctx) (r : Response) :
    denoteRR ctx (expiresSpecR isStaticGet val).onResp r
      = stampFnR (cacheControlDec isStaticGet) expiresName val ctx r :=
  denoteRR_stampProgR _ expiresName val ctx r
theorem runChainR_expires (isStaticGet : ReqPred) (val : Bytes)
    (handler : Ctx → Response) (ctx : Ctx) :
    runChainR ctx handler [expiresSpecR isStaticGet val]
      = stampFnR (cacheControlDec isStaticGet) expiresName val ctx (handler ctx) :=
  runChainR_stampSpecR _ expiresName val handler ctx

/-- 13. asset-immutable — same decision, `Cache-Control` name. -/
def immutableSpecR (isStaticGet : ReqPred) (val : Bytes) : StageSpecR :=
  stampSpecR (cacheControlDec isStaticGet) ccName val
theorem denoteRR_immutable (isStaticGet : ReqPred) (val : Bytes) (ctx : Ctx) (r : Response) :
    denoteRR ctx (immutableSpecR isStaticGet val).onResp r
      = stampFnR (cacheControlDec isStaticGet) ccName val ctx r :=
  denoteRR_stampProgR _ ccName val ctx r
theorem runChainR_immutable (isStaticGet : ReqPred) (val : Bytes)
    (handler : Ctx → Response) (ctx : Ctx) :
    runChainR ctx handler [immutableSpecR isStaticGet val]
      = stampFnR (cacheControlDec isStaticGet) ccName val ctx (handler ctx) :=
  runChainR_stampSpecR _ ccName val handler ctx

/-- 14. last-modified — `r.status == 200 && isStaticGet c && !hasLm r.headers`. -/
def lastModifiedDec (isStaticGet : ReqPred) (hasLm : List (Bytes × Bytes) → Bool) :
    Ctx → Response → Bool :=
  fun c r => decide (r.status = 200) && isStaticGet c && ! hasLm r.headers
def lastModifiedSpecR (isStaticGet : ReqPred) (hasLm : List (Bytes × Bytes) → Bool) (val : Bytes) :
    StageSpecR := stampSpecR (lastModifiedDec isStaticGet hasLm) lmName val
theorem denoteRR_lastModified (isStaticGet : ReqPred) (hasLm : List (Bytes × Bytes) → Bool)
    (val : Bytes) (ctx : Ctx) (r : Response) :
    denoteRR ctx (lastModifiedSpecR isStaticGet hasLm val).onResp r
      = stampFnR (lastModifiedDec isStaticGet hasLm) lmName val ctx r :=
  denoteRR_stampProgR _ lmName val ctx r
theorem runChainR_lastModified (isStaticGet : ReqPred) (hasLm : List (Bytes × Bytes) → Bool)
    (val : Bytes) (handler : Ctx → Response) (ctx : Ctx) :
    runChainR ctx handler [lastModifiedSpecR isStaticGet hasLm val]
      = stampFnR (lastModifiedDec isStaticGet hasLm) lmName val ctx (handler ctx) :=
  runChainR_stampSpecR _ lmName val handler ctx

/-- 15. retry-after — `needsRetryAfter r.status` (a status SET). -/
def retryAfterDec (needsRetryAfter : Nat → Bool) : Ctx → Response → Bool :=
  fun _ r => needsRetryAfter r.status
def retryAfterSpecR (needsRetryAfter : Nat → Bool) (val : Bytes) : StageSpecR :=
  stampSpecR (retryAfterDec needsRetryAfter) retryName val
theorem denoteRR_retryAfter (needsRetryAfter : Nat → Bool) (val : Bytes) (ctx : Ctx) (r : Response) :
    denoteRR ctx (retryAfterSpecR needsRetryAfter val).onResp r
      = stampFnR (retryAfterDec needsRetryAfter) retryName val ctx r :=
  denoteRR_stampProgR _ retryName val ctx r
theorem runChainR_retryAfter (needsRetryAfter : Nat → Bool) (val : Bytes)
    (handler : Ctx → Response) (ctx : Ctx) :
    runChainR ctx handler [retryAfterSpecR needsRetryAfter val]
      = stampFnR (retryAfterDec needsRetryAfter) retryName val ctx (handler ctx) :=
  runChainR_stampSpecR _ retryName val handler ctx

/-- 16. content-location — `r.status == 200 && isStaticGet c` (value is ctx-only). -/
def contentLocationSpecR (isStaticGet : ReqPred) (val : Bytes) : StageSpecR :=
  stampSpecR (cacheControlDec isStaticGet) clocName val
theorem denoteRR_contentLocation (isStaticGet : ReqPred) (val : Bytes) (ctx : Ctx) (r : Response) :
    denoteRR ctx (contentLocationSpecR isStaticGet val).onResp r
      = stampFnR (cacheControlDec isStaticGet) clocName val ctx r :=
  denoteRR_stampProgR _ clocName val ctx r
theorem runChainR_contentLocation (isStaticGet : ReqPred) (val : Bytes)
    (handler : Ctx → Response) (ctx : Ctx) :
    runChainR ctx handler [contentLocationSpecR isStaticGet val]
      = stampFnR (cacheControlDec isStaticGet) clocName val ctx (handler ctx) :=
  runChainR_stampSpecR _ clocName val handler ctx

/-! ## 6. Non-vacuity — the response-decided branch genuinely reads the response

Concrete kernel `#guard`s at real field bytes. A status-500 handler and a
status-200 handler flip a status-keyed decision; a status-500 REFUSAL and a
status-200 refusal flip it under a fired gate (the crux — the decision reads the
inner result). -/

/-- A `500` response, to drive the response-decided branches off. -/
def resp500 : Response :=
  { status := 500, reason := str "Internal Server Error", headers := [], body := [] }

-- the general condResp stamp fires exactly when its decision does (both branches live):
#guard (denoteRR ctxGet (stampProgR (fun _ _ => true) (str "N") (str "V")) baseOk).headers
        = baseOk.headers ++ [(str "N", str "V")]
#guard (denoteRR ctxGet (stampProgR (fun _ _ => false) (str "N") (str "V")) baseOk).headers
        = baseOk.headers
-- the decision READS the arriving response's status — 200 fires, 500 does not:
#guard (denoteRR ctxGet (stampProgR (fun _ r => decide (r.status = 200)) (str "N") (str "V")) baseOk).headers
        = baseOk.headers ++ [(str "N", str "V")]
#guard (denoteRR ctxGet (stampProgR (fun _ r => decide (r.status = 200)) (str "N") (str "V")) resp500).headers
        = resp500.headers

/-- The concrete response-decided stamp used in the fired-gate witnesses. -/
def statusStampSpecR (k : Nat) (name val : Bytes) : StageSpecR :=
  stampSpecR (fun _ r => decide (r.status = k)) name val

-- THE CRUX: outside a FIRED gate, the stamp decides on the gate's REFUSAL. A 200
-- refusal gets the header; a 500 refusal does not — the decision reads the inner
-- result, the exact capability `condR : Ctx → Bool` lacks:
#guard (runChainR ctxPost (fun _ => baseOk)
          [statusStampSpecR 200 (str "N") (str "V"), gateSpecR (fun _ => true) baseOk]).headers
        = [(str "N", str "V")]
#guard (runChainR ctxPost (fun _ => baseOk)
          [statusStampSpecR 200 (str "N") (str "V"), gateSpecR (fun _ => true) resp500]).headers
        = []
-- and the refusal record stays fresh underneath (a real 500 refusal reaches the wire):
#guard (runChainR ctxPost (fun _ => baseOk)
          [statusStampSpecR 200 (str "N") (str "V"), gateSpecR (fun _ => true) resp500]).status = 500

-- a deployed status-keyed stamp (cache-control) fires on 200-static, not on 500:
#guard (runChainR ctxGet (fun _ => baseOk) [cacheControlSpecR (fun _ => true) (str "no-cache")]).headers
        = baseOk.headers ++ [(ccName, str "no-cache")]
#guard (runChainR ctxGet (fun _ => resp500) [cacheControlSpecR (fun _ => true) (str "no-cache")]).headers
        = resp500.headers
-- retry-after keys purely on status (a status set), here firing on 500:
#guard (runChainR ctxGet (fun _ => resp500) [retryAfterSpecR (fun s => decide (s = 500)) (str "5")]).headers
        = resp500.headers ++ [(retryName, str "5")]
#guard (runChainR ctxGet (fun _ => baseOk) [retryAfterSpecR (fun s => decide (s = 500)) (str "5")]).headers
        = baseOk.headers

/-! ## 7. THE STATUS-KEYED COMPILE FRAGMENT — one `.cond` on the `aStat` cell

`condStatus k` lowers to a single comparison against the live status cell (`aStat`
in `Enc3`). Exact under a `status < 2^64` well-formedness invariant. The general
`condResp` node is NOT lowered (the header list is not in `Enc3`); `compileRR_correct`
is gated on `Lowerable`, which excludes it — nothing false is claimed for it. -/

/-- `BitVec.ofNat 64` is injective on the `< 2^64` window — what lets the machine
recover `r.status = k` from the encoded cell comparison. -/
theorem ofNat64_inj {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x = BitVec.ofNat 64 y) ↔ x = y := by
  constructor
  · intro h
    have h2 := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h2
    exact h2
  · intro h; rw [h]

/-- No `setStatus` inside a `RespProg` — so its `denoteR` leaves `status` fixed
(the status-keyed stamps only append headers).

NOTE (post-fold): `condResp`/`condStatus` now live in `RespProg` itself (they were
folded into the onion DSL). This prototype embeds only the ORIGINAL gate-free ops at
`.base` — its OWN `RespProgR.condResp`/`.condStatus` carry the response-decided
branches — so the two folded-in constructors are excluded here. -/
def noSetStatus : RespProg → Prop
  | .skip => True
  | .addHeader _ _ => True
  | .setStatus _ _ => False
  | .rewriteBody _ => True
  | .seq a b => noSetStatus a ∧ noSetStatus b
  | .condR _ a b => noSetStatus a ∧ noSetStatus b
  | .condResp _ _ _ => False
  | .condStatus _ _ _ => False

/-- The `.base` fragment (the original gate-free ops, no `setStatus`) is `Compilable`
in the folded algebra — what lets the base case below delegate to the folded
`StageOnion.compileR_correct`, which is now gated on `Compilable`. -/
theorem noSetStatus_compilable : ∀ p : RespProg, noSetStatus p → Compilable p := by
  intro p
  induction p with
  | skip => intro _; trivial
  | addHeader n v => intro _; trivial
  | setStatus code reason => intro h; exact h.elim
  | rewriteBody t => intro _; trivial
  | seq a b iha ihb => intro h; exact ⟨iha h.1, ihb h.2⟩
  | condR c a b iha ihb => intro h; exact ⟨iha h.1, ihb h.2⟩
  | condResp c a b _ _ => intro h; exact h.elim
  | condStatus k a b _ _ => intro h; exact h.elim

theorem denoteR_preserves_status (ctx : Ctx) :
    ∀ (p : RespProg) (r : Response), noSetStatus p → (denoteR ctx p r).status = r.status := by
  intro p
  induction p with
  | skip => intro r _; rfl
  | addHeader n v => intro r _; rfl
  | setStatus code reason => intro r h; exact h.elim
  | rewriteBody t => intro r _; rfl
  | seq a b iha ihb =>
    intro r h; obtain ⟨ha, hb⟩ := h
    show (denoteR ctx b (denoteR ctx a r)).status = r.status
    rw [ihb (denoteR ctx a r) hb, iha r ha]
  | condR c a b iha ihb =>
    intro r h; obtain ⟨ha, hb⟩ := h
    show (if c ctx then denoteR ctx a r else denoteR ctx b r).status = r.status
    cases hc : c ctx with
    | true => exact iha r ha
    | false => exact ihb r hb
  -- the folded-in branches are excluded from this prototype's `.base` fragment:
  | condResp c a b _ _ => intro r h; exact h.elim
  | condStatus k a b _ _ => intro r h; exact h.elim

/-- The compilable fragment of `RespProgR`: `base` (no `setStatus`), `seqR`,
`condStatus` (key `< 2^64`); the general `condResp` is EXCLUDED. -/
def Lowerable : RespProgR → Prop
  | .base p => noSetStatus p
  | .seqR a b => Lowerable a ∧ Lowerable b
  | .condStatus k a b => k < 2 ^ 64 ∧ Lowerable a ∧ Lowerable b
  | .condResp _ _ _ => False

theorem denoteRR_preserves_status (ctx : Ctx) :
    ∀ (p : RespProgR) (r : Response), Lowerable p → (denoteRR ctx p r).status = r.status := by
  intro p
  induction p with
  | base p => intro r h; exact denoteR_preserves_status ctx p r h
  | seqR a b iha ihb =>
    intro r h; obtain ⟨ha, hb⟩ := h
    show (denoteRR ctx b (denoteRR ctx a r)).status = r.status
    rw [ihb (denoteRR ctx a r) hb, iha r ha]
  | condResp c a b _ _ => intro r h; exact h.elim
  | condStatus k a b iha ihb =>
    intro r h; obtain ⟨_, ha, hb⟩ := h
    show (if r.status = k then denoteRR ctx a r else denoteRR ctx b r).status = r.status
    by_cases hk : r.status = k
    · rw [if_pos hk]; exact iha r ha
    · rw [if_neg hk]; exact ihb r hb

/-- **`compileRR` — the extended lowering.** `base`/`seqR` as before; `condStatus k`
emits ONE `.cond` comparing the live `aStat` cell to `k`; `condResp` has NO faithful
lowering (placeholder `.skip`, never certified — see `compileRR_correct`'s `Lowerable`
gate). -/
def compileRR (nm : ReqPred → String) (aStat aCnt aBody : Word) : RespProgR → PancakeProg
  | .base p => compileR nm aStat aCnt aBody p
  | .seqR a b => .seq (compileRR nm aStat aCnt aBody a) (compileRR nm aStat aCnt aBody b)
  | .condStatus k a b =>
      .cond (.cmp .equal (.loadWord (.const aStat)) (.const (BitVec.ofNat 64 k)))
        (compileRR nm aStat aCnt aBody a) (compileRR nm aStat aCnt aBody b)
  | .condResp _ _ _ => .skip

/-- **`compileRR_correct` — the status-keyed compile fragment, proven.** For a
`Lowerable` program, from any state encoding a well-formed `r` (`status < 2^64`),
`compileRR` lands a state encoding `denoteRR ctx p r`. The `condStatus` case is the
new content: one comparison against the `aStat` cell, decoded through `ofNat64_inj`
under the status bound (re-established for sub-terms by `denoteRR_preserves_status`,
since the fragment never rewrites the status). -/
theorem compileRR_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody : Word) (ctx : Ctx) (hd : Distinct3 aStat aCnt aBody) :
    ∀ (p : RespProgR) (r : Response) (st : PancakeState σ),
      Lowerable p → r.status < 2 ^ 64 →
      Enc3 aStat aCnt aBody st r →
      (∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) →
      ∃ st', PancakeSem o (compileRR nm aStat aCnt aBody p) st = (none, st') ∧
        Enc3 aStat aCnt aBody st' (denoteRR ctx p r) ∧
        st'.locals = st.locals ∧
        (∀ x, st'.memaddrs x = st.memaddrs x) ∧
        st'.clock = st.clock := by
  obtain ⟨d_sc, d_sb, d_cb⟩ := hd
  intro p
  induction p with
  | base p =>
    intro r st hL hwf hEnc hDec
    exact compileR_correct o nm aStat aCnt aBody ctx ⟨d_sc, d_sb, d_cb⟩ p r st
      (noSetStatus_compilable p hL) hEnc hDec
  | seqR a b iha ihb =>
    intro r st hL hwf hEnc hDec
    obtain ⟨hLa, hLb⟩ := hL
    obtain ⟨st1, h1, hEnc1, hl1, hm1, hk1⟩ := iha r st hLa hwf hEnc hDec
    have hwf1 : (denoteRR ctx a r).status < 2 ^ 64 := by
      rw [denoteRR_preserves_status ctx a r hLa]; exact hwf
    have hDec1 : ∀ c, st1.locals (nm c) = some (if c ctx then (1 : Word) else 0) := by
      intro c; rw [hl1]; exact hDec c
    obtain ⟨st2, h2, hEnc2, hl2, hm2, hk2⟩ := ihb (denoteRR ctx a r) st1 hLb hwf1 hEnc1 hDec1
    refine ⟨st2, sem_seq_frames o h1 hk1 h2, hEnc2, ?_, ?_, ?_⟩
    · rw [hl2, hl1]
    · intro x; rw [hm2, hm1]
    · rw [hk2, hk1]
  | condResp c a b _ _ =>
    intro r st hL hwf hEnc hDec; exact hL.elim
  | condStatus k a b iha ihb =>
    intro r st hL hwf hEnc hDec
    obtain ⟨hk, hLa, hLb⟩ := hL
    have hS := hEnc.1
    have hload : eval st (.loadWord (.const aStat)) = some (BitVec.ofNat 64 r.status) :=
      eval_loadWord_of_wordAt (eval_const aStat) hS
    have heval : eval st (.cmp .equal (.loadWord (.const aStat)) (.const (BitVec.ofNat 64 k)))
        = some (if BitVec.ofNat 64 r.status = BitVec.ofNat 64 k then (1 : Word) else 0) :=
      eval_equal st hload (eval_const (BitVec.ofNat 64 k))
    by_cases h : r.status = k
    · have hbv : BitVec.ofNat 64 r.status = BitVec.ofNat 64 k := by rw [h]
      obtain ⟨st', hsem, hE, hl, hm, hkk⟩ := iha r st hLa hwf hEnc hDec
      refine ⟨st', ?_, ?_, hl, hm, hkk⟩
      · show PancakeSem o (.cond (.cmp .equal (.loadWord (.const aStat)) (.const (BitVec.ofNat 64 k)))
              (compileRR nm aStat aCnt aBody a) (compileRR nm aStat aCnt aBody b)) st = (none, st')
        rw [sem_cond o heval, hbv, if_pos rfl,
            if_pos (show (1 : Word) ≠ 0 from word_one_ne_zero)]
        exact hsem
      · show Enc3 aStat aCnt aBody st' (if r.status = k then denoteRR ctx a r else denoteRR ctx b r)
        rw [if_pos h]; exact hE
    · have hbv : ¬ (BitVec.ofNat 64 r.status = BitVec.ofNat 64 k) :=
        fun hh => h ((ofNat64_inj hwf hk).mp hh)
      obtain ⟨st', hsem, hE, hl, hm, hkk⟩ := ihb r st hLb hwf hEnc hDec
      refine ⟨st', ?_, ?_, hl, hm, hkk⟩
      · show PancakeSem o (.cond (.cmp .equal (.loadWord (.const aStat)) (.const (BitVec.ofNat 64 k)))
              (compileRR nm aStat aCnt aBody a) (compileRR nm aStat aCnt aBody b)) st = (none, st')
        rw [sem_cond o heval, if_neg hbv,
            if_neg (show ¬ ((0 : Word) ≠ 0) from fun hh => hh rfl)]
        exact hsem
      · show Enc3 aStat aCnt aBody st' (if r.status = k then denoteRR ctx a r else denoteRR ctx b r)
        rw [if_neg h]; exact hE

/-! ### 7.1 The compilable status-keyed stamps — end-to-end (denote → machine)

The status-keyed stamps whose decision reads ONLY the status (plus a ctx conjunct
via the inner `condR`) close end-to-end: their `condStatus`/`condR` form is
`Lowerable`, so `compileRR_correct` lands the machine skeleton of their denotation.
The ctx conjunct nests as an inner `condR` (already compiled by `compileR`). -/

/-- A pure status-keyed stamp (retry-after's single-status shape): append on
`r.status = k`. -/
def statusStampS (k : Nat) (name val : Bytes) : RespProgR :=
  .condStatus k (.base (.addHeader name val)) (.base .skip)

/-- A status-AND-ctx stamp (cache-control / expires / immutable / content-location):
append on `r.status = 200 && d ctx`, the `d` conjunct an inner `condR`. -/
def staticStatusStampS (d : ReqPred) (name val : Bytes) : RespProgR :=
  .condStatus 200 (.base (.condR d (.addHeader name val) .skip)) (.base .skip)

theorem lowerable_statusStampS (k : Nat) (name val : Bytes) (hk : k < 2 ^ 64) :
    Lowerable (statusStampS k name val) := ⟨hk, trivial, trivial⟩

/-- `200 < 2^64`, established without evaluating `2^64` in the kernel. -/
theorem status200_wf : (200 : Nat) < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (by decide : (200 : Nat) < 2 ^ 8)
    (Nat.pow_le_pow_right (by decide) (by decide))

theorem lowerable_staticStatusStampS (d : ReqPred) (name val : Bytes) :
    Lowerable (staticStatusStampS d name val) :=
  ⟨status200_wf, ⟨trivial, trivial⟩, trivial⟩

/-- **`compile_statusStamp` — the pure status-keyed stamp compiles.** -/
theorem compile_statusStamp (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody : Word) (ctx : Ctx) (hd : Distinct3 aStat aCnt aBody)
    (k : Nat) (name val : Bytes) (hk : k < 2 ^ 64) (r : Response) (st : PancakeState σ)
    (hwf : r.status < 2 ^ 64) (hEnc : Enc3 aStat aCnt aBody st r)
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compileRR nm aStat aCnt aBody (statusStampS k name val)) st = (none, st') ∧
      Enc3 aStat aCnt aBody st' (denoteRR ctx (statusStampS k name val) r) :=
  let ⟨st', h1, h2, _, _, _⟩ :=
    compileRR_correct o nm aStat aCnt aBody ctx hd (statusStampS k name val) r st
      (lowerable_statusStampS k name val hk) hwf hEnc hDec
  ⟨st', h1, h2⟩

/-- **`compile_staticStatusStamp` — the status-AND-ctx stamp compiles.** The status
test is one `.cond` on `aStat`; the ctx conjunct is the inner `condR` `compileR`
already lowers. -/
theorem compile_staticStatusStamp (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody : Word) (ctx : Ctx) (hd : Distinct3 aStat aCnt aBody)
    (d : ReqPred) (name val : Bytes) (r : Response) (st : PancakeState σ)
    (hwf : r.status < 2 ^ 64) (hEnc : Enc3 aStat aCnt aBody st r)
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compileRR nm aStat aCnt aBody (staticStatusStampS d name val)) st
        = (none, st') ∧
      Enc3 aStat aCnt aBody st' (denoteRR ctx (staticStatusStampS d name val) r) :=
  let ⟨st', h1, h2, _, _, _⟩ :=
    compileRR_correct o nm aStat aCnt aBody ctx hd (staticStatusStampS d name val) r st
      (lowerable_staticStatusStampS d name val) hwf hEnc hDec
  ⟨st', h1, h2⟩

-- the compilable forms denote to the deployed conditional append (both branches
-- live), matching the `condResp` `&&` decisions above on concrete data:
#guard (denoteRR ctxGet (statusStampS 200 (str "N") (str "V")) baseOk).headers
        = baseOk.headers ++ [(str "N", str "V")]
#guard (denoteRR ctxGet (statusStampS 200 (str "N") (str "V")) resp500).headers = resp500.headers
#guard (denoteRR ctxGet (staticStatusStampS (fun _ => true) (str "N") (str "V")) baseOk).headers
        = [(str "N", str "V")]
#guard (denoteRR ctxGet (staticStatusStampS (fun _ => false) (str "N") (str "V")) baseOk).headers = []
-- the `condStatus` form and the `condResp` `&&` form agree on concrete data:
#guard (denoteRR ctxGet (staticStatusStampS (fun _ => true) (str "N") (str "V")) baseOk).headers
        = (denoteRR ctxGet (stampProgR (cacheControlDec (fun _ => true)) (str "N") (str "V")) baseOk).headers

/-! ## 8. DESIGN NOTE — what the fold-in adds, and what stays blocked

FOLD-IN (into the onion DSL, when done carefully — this file is the study, not the
edit):
 * Add `condResp (c : Ctx → Response → Bool) (a b)` to `RespProg`, with denotation
   `| .condResp c a b, r => if c ctx r then denoteR ctx a r else denoteR ctx b r`.
   `denoteR` STAYS a fold; `runChain`/`respFold`/the keystone need NO change (proven
   here for the mirror `runChainR`). `condR` becomes derivable
   (`condR c = condResp (fun ctx _ => c ctx)`), so the extension is conservative.
 * On the compiler: add the `condStatus`-style clause — a `.cond` comparing the
   `aStat` cell to a constant — under a `status < 2^64` invariant threaded through
   `Enc3` (proven here as `compileRR_correct`'s `condStatus` case + `ofNat64_inj`).

UNBLOCKED by `condResp` (denotationally, all 8; §5): warning, link, cache-control,
expires, immutable, last-modified, retry-after, content-location.

COMPILES end-to-end today (status-only decisions; §7.1): cache-control, expires,
immutable, content-location (`status = 200 && ctx`), and the single-status shape of
retry-after. Their `condStatus`/`condR` forms are `Lowerable`.

STILL BLOCKED, and on WHAT (not `condResp`'s fault):
 * HEADER-LIST reads — the unless-present family (alt-svc, permissions-policy,
   resource-policy, timing-allow, via, vary-encoding, vary-excluded), plus warning's
   `isTransformed`/`!hasWarning`, link's `!hasLink`, last-modified's `!hasLm`. These
   DENOTE through `condResp` but do NOT compile: `Enc3` holds only the header COUNT
   (`aCnt`), not the list, so `!hasX r.headers` has nothing to read. They need a
   MACHINE-SIDE HEADER REPRESENTATION first (a separate, larger piece — do not
   smuggle it in with `condResp`).
 * retry-after's `needsRetryAfter r.status` is a status SET; it compiles as a NEST of
   `condStatus` equalities (a disjunction), a straightforward extension of the single
   comparison proven here.
 * cache-status (item 10, NOT among the 8): needs BOTH a header read (`!hasCS
   r.headers`) AND a response-READING VALUE (`isHit r.headers`) — the latter is
   `addHeaderOf : Ctx → Response → Bytes`, strictly beyond `condResp`
   (`addHeader`'s constant `val` cannot express it). Doubly blocked.
-/

/-! ## 9. Axiom audit — expect ⊆ {propext, Classical.choice, Quot.sound}, 0 sorryAx. -/

#print axioms denoteRR_condStatus_eq
#print axioms runChainR_gate_keystone
#print axioms denoteRR_stampProgR
#print axioms runChainR_stampSpecR
#print axioms condRespStamp_carries_on_gate_refusal
#print axioms denoteRR_warning
#print axioms denoteRR_link
#print axioms denoteRR_cacheControl
#print axioms denoteRR_expires
#print axioms denoteRR_immutable
#print axioms denoteRR_lastModified
#print axioms denoteRR_retryAfter
#print axioms denoteRR_contentLocation
#print axioms ofNat64_inj
#print axioms compileRR_correct
#print axioms compile_statusStamp
#print axioms compile_staticStatusStamp

end Pancake.CondRespProto
