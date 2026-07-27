/-
  Pancake/StageLift2Cond.lean — THE RESPONSE-DECIDED STAMP INSTANTIATIONS.

  WHY THIS FILE EXISTS. `StageLift2Inst.lean` re-instantiated the deployed stages on
  the two-phase onion and split them honestly: the CTX-decided stamps ported exactly
  (§3 there), the gates all ported (§4–§5), and the RESPONSE-DECIDED stamps were
  listed, counted, and LEFT BLOCKED (§6 there) on a `condResp` constructor that did
  not exist. `RespProg.condR`'s predicate is `ReqPred = Ctx → Bool`; it cannot read
  the response threaded up from the inner onion, and pinning those stamps at
  `ctx.base` would have asserted a serve the deployed stage does not perform.

  `condResp` is now FOLDED INTO the onion DSL (`StageProg2` §1): `RespProg` carries
  the general response-decided branch `condResp (c : Ctx → Response → Bool)` and its
  compilable status-keyed slice `condStatus (k : Nat)`. This file spends that
  extension — it instantiates the 8 status-keyed response-decided stamps through it.

  THE POINT: these stamps are now `StageSpec`s in the SAME algebra as the other 27, so
  they compose in the SAME `runChain` — no mirror algebra, no second interpreter. The
  decision reads the ARRIVING response, which under the onion is the INNER result: if
  an inner gate fired, it is the REFUSAL, not the handler's response at all. §2's
  `condRespStamp_carries_on_gate_refusal` witnesses exactly that — the capability
  `condR` lacked.

  WHAT IS PINNED HERE (§3) — the 8, each with a `denoteR` pin (the response phase over
  ANY arriving `r`) and a `runChain` pin (the single-stage serve over ANY handler):
    warning, link-preload, cache-control, asset-expires, asset-immutable,
    last-modified, retry-after, content-location.
  The decisions are opaque parameters named for what the deployed stage computes
  (`isStaticGet`, `hasLink`, `needsRetryAfter`, …) — the pins hold for the REAL
  decision, whatever it computes.

  WHAT COMPILES (§4) — the status-only decisions close end-to-end to the machine
  through `condStatus` + `compileR_condStatus_correct`: cache-control, expires,
  immutable, content-location (`status = 200 && ctx`), and the single-status shape of
  retry-after. The status IS the `aStat` cell, so the machine can read it.

  THE RESPONSE-DECIDED RESIDUAL (§5, named not hidden). The HEADER-LIST-reading
  decisions (`!hasLink`/`!hasLm`/`!hasWarning`/`isTransformed r.headers`, and the whole
  unless-present family) DENOTE through `condResp` but do NOT compile: `Enc3` carries
  only the header COUNT (`aCnt`), not the list. They wait on a machine-side header
  representation — a separate, larger piece, deliberately not smuggled in here.

  Own file. Imports the chain through `StageLift2Inst` and edits nothing.
  Axiom audit at the end: expect ⊆ {propext, Classical.choice, Quot.sound}, 0 sorryAx.
-/
import Pancake.StageLift2Inst

namespace Pancake.StageLift2Cond

open Pancake Pancake.SerializeCompile Pancake.StageProg Pancake.StageOnion
open Pancake.StageLift2 Pancake.StageLift2Inst

variable {σ : Type}

/-! ## 1. THE RESPONSE-DECIDED STAMP SHAPE — a conditional append that reads `r`

The deployed response-decided stamp passes the request untouched and, in its response
phase, appends one `(name, val)` under a decision that reads the ARRIVING response.
With the affine builder erased, that effect is `stampFnR`. `stampProgR` is the
`RespProg` that computes it — now expressible, as `condResp c (addHeader name val) skip`. -/

/-- **The deployed response-decided stamp's functional effect**: append `(name, val)`
exactly when `c` fires at this context AND this ARRIVING response. -/
def stampFnR (c : Ctx → Response → Bool) (name val : Bytes) (ctx : Ctx) (r : Response) : Response :=
  if c ctx r then { r with headers := r.headers ++ [(name, val)] } else r

/-- **The response-decided stamp program** — `condResp c (addHeader name val) skip`. -/
def stampProgR (c : Ctx → Response → Bool) (name val : Bytes) : RespProg :=
  .condResp c (.addHeader name val) .skip

/-- **`denoteR_stampProgR` — THE `condResp` STAMP LIFT.** For ANY response-decided
decision `c`, name, value, context and ARRIVING response `r`, the stamp denotes to the
deployed conditional append `stampFnR`. Both branches discharged (not vacuous), and `r`
is the true inner result — the whole point of `condResp`. -/
theorem denoteR_stampProgR (c : Ctx → Response → Bool) (name val : Bytes)
    (ctx : Ctx) (r : Response) :
    denoteR ctx (stampProgR c name val) r = stampFnR c name val ctx r := by
  show (if c ctx r then denoteR ctx (.addHeader name val) r else denoteR ctx .skip r)
      = stampFnR c name val ctx r
  unfold stampFnR
  cases h : c ctx r with
  | true => rfl
  | false => rfl

/-- **The response-decided stamp STAGE** — a pure transform stage (never gates) whose
response phase decides on the arriving response. -/
def stampSpecR (c : Ctx → Response → Bool) (name val : Bytes) : StageSpec :=
  { guard := fun _ => false, refusal := .skip, onResp := stampProgR c name val }

/-- **`runChain_stampSpecR`** — a single response-decided stamp over a handler passes to
the handler and stamps under its decision on the HANDLER's response. -/
theorem runChain_stampSpecR (c : Ctx → Response → Bool) (name val : Bytes)
    (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [stampSpecR c name val] = stampFnR c name val ctx (handler ctx) := by
  rw [runChain_stage_effect ctx handler (stampSpecR c name val) [] rfl, runChain_nil]
  show denoteR ctx (stampProgR c name val) (handler ctx) = _
  rw [denoteR_stampProgR]

/-! ## 2. THE NEW CAPABILITY — a response-decided stamp deciding on a gate's REFUSAL

This is what `condR : Ctx → Bool` could not express, and it is why pinning these stamps
at `ctx.base` would have been false: under the onion the arriving response is the INNER
result, and when an inner gate fires that is the REFUSAL. -/

/-- **`condRespStamp_carries_on_gate_refusal` — THE NEW CAPABILITY.** A response-decided
stamp OUTSIDE a firing gate decides on the gate's REFUSAL — the inner result the stamp
actually sees — and carries (or withholds) its header accordingly. The decision is a
function of the arriving refusal, not of `ctx`. For ANY handler (which never runs).
Proven through the REAL onion keystone (`runChain_gate_keystone`). -/
theorem condRespStamp_carries_on_gate_refusal (c : Ctx → Response → Bool) (name val : Bytes)
    (fire : ReqPred) (refuseR : Response) (handler : Ctx → Response) (ctx : Ctx)
    (hfire : fire ctx = true) :
    runChain ctx handler [stampSpecR c name val, gateSpec fire refuseR]
      = stampFnR c name val ctx refuseR := by
  have hpre : ∀ s ∈ [stampSpecR c name val], s.guard ctx = false := by
    intro s hs; simp at hs; rw [hs]; rfl
  have hg : (gateSpec fire refuseR).guard ctx = true := hfire
  rw [show ([stampSpecR c name val, gateSpec fire refuseR] : List StageSpec)
        = [stampSpecR c name val] ++ gateSpec fire refuseR :: [] from rfl,
      runChain_gate_keystone ctx handler [stampSpecR c name val] (gateSpec fire refuseR) []
        hpre hg]
  show denoteR ctx (stampProgR c name val) (denoteR ctx (refusalProg refuseR) blankResp) = _
  rw [denoteR_refusalProg, denoteR_stampProgR]

/-! ## 3. THE 8 STATUS-KEYED RESPONSE-DECIDED STAMPS — pinned through `condResp`

Each deployed stamp: a decision that reads the arriving response (status and/or
headers) and, when it fires, appends one header. Each gets a `denoteR` pin (the
response phase over ANY arriving `r` — the onion-composable statement) and a `runChain`
pin (the single-stage serve over ANY handler), both one line through
`denoteR_stampProgR` / `runChain_stampSpecR`. -/

/-- `Warning` field name. -/
def warnName  : Bytes := str "Warning"
/-- `Link` field name. -/
def linkName  : Bytes := str "Link"
/-- `Cache-Control` field name. -/
def ccName    : Bytes := str "Cache-Control"
/-- `Expires` field name. -/
def expiresName : Bytes := str "Expires"
/-- `Last-Modified` field name. -/
def lmName    : Bytes := str "Last-Modified"
/-- `Retry-After` field name. -/
def retryName : Bytes := str "Retry-After"
/-- `Content-Location` field name. -/
def clocName  : Bytes := str "Content-Location"

/-! ### 3.1 warning — `isTransformed r.headers && !hasWarning r.headers` -/

/-- The warning stage's decision: the response was transformed and carries no warning
yet. Reads the arriving response's HEADERS. -/
def warningDec (isTransformed hasWarning : List (Bytes × Bytes) → Bool) : Ctx → Response → Bool :=
  fun _ r => isTransformed r.headers && ! hasWarning r.headers

/-- **The warning stage.** -/
def warningSpecR (isTransformed hasWarning : List (Bytes × Bytes) → Bool) (val : Bytes) : StageSpec :=
  stampSpecR (warningDec isTransformed hasWarning) warnName val

/-- **`denoteR_warning`** — the response phase, over ANY arriving response. -/
theorem denoteR_warning (isTransformed hasWarning : List (Bytes × Bytes) → Bool)
    (val : Bytes) (ctx : Ctx) (r : Response) :
    denoteR ctx (warningSpecR isTransformed hasWarning val).onResp r
      = stampFnR (warningDec isTransformed hasWarning) warnName val ctx r :=
  denoteR_stampProgR _ warnName val ctx r

/-- **`runChain_warning`** — the single-stage serve, over ANY handler. -/
theorem runChain_warning (isTransformed hasWarning : List (Bytes × Bytes) → Bool)
    (val : Bytes) (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [warningSpecR isTransformed hasWarning val]
      = stampFnR (warningDec isTransformed hasWarning) warnName val ctx (handler ctx) :=
  runChain_stampSpecR _ warnName val handler ctx

/-! ### 3.2 link-preload — `r.status == 200 && !hasLink r.headers` -/

/-- The link-preload stage's decision: a `200` with no `Link` yet. -/
def linkDec (hasLink : List (Bytes × Bytes) → Bool) : Ctx → Response → Bool :=
  fun _ r => decide (r.status = 200) && ! hasLink r.headers

/-- **The link-preload stage.** -/
def linkSpecR (hasLink : List (Bytes × Bytes) → Bool) (val : Bytes) : StageSpec :=
  stampSpecR (linkDec hasLink) linkName val

/-- **`denoteR_link`** — the response phase, over ANY arriving response. -/
theorem denoteR_link (hasLink : List (Bytes × Bytes) → Bool) (val : Bytes)
    (ctx : Ctx) (r : Response) :
    denoteR ctx (linkSpecR hasLink val).onResp r = stampFnR (linkDec hasLink) linkName val ctx r :=
  denoteR_stampProgR _ linkName val ctx r

/-- **`runChain_link`** — the single-stage serve, over ANY handler. -/
theorem runChain_link (hasLink : List (Bytes × Bytes) → Bool) (val : Bytes)
    (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [linkSpecR hasLink val]
      = stampFnR (linkDec hasLink) linkName val ctx (handler ctx) :=
  runChain_stampSpecR _ linkName val handler ctx

/-! ### 3.3 cache-control / asset-expires / asset-immutable / content-location

All four share the decision `r.status == 200 && isStaticGet c` — a STATUS read and a
CTX conjunct. This is the compilable family (§4). -/

/-- The shared static-asset decision: a `200` on a static-asset route. -/
def cacheControlDec (isStaticGet : ReqPred) : Ctx → Response → Bool :=
  fun c r => decide (r.status = 200) && isStaticGet c

/-- **The cache-control stage.** -/
def cacheControlSpecR (isStaticGet : ReqPred) (val : Bytes) : StageSpec :=
  stampSpecR (cacheControlDec isStaticGet) ccName val

/-- **`denoteR_cacheControl`** — the response phase, over ANY arriving response. -/
theorem denoteR_cacheControl (isStaticGet : ReqPred) (val : Bytes) (ctx : Ctx) (r : Response) :
    denoteR ctx (cacheControlSpecR isStaticGet val).onResp r
      = stampFnR (cacheControlDec isStaticGet) ccName val ctx r :=
  denoteR_stampProgR _ ccName val ctx r

/-- **`runChain_cacheControl`** — the single-stage serve, over ANY handler. -/
theorem runChain_cacheControl (isStaticGet : ReqPred) (val : Bytes)
    (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [cacheControlSpecR isStaticGet val]
      = stampFnR (cacheControlDec isStaticGet) ccName val ctx (handler ctx) :=
  runChain_stampSpecR _ ccName val handler ctx

/-- **The asset-expires stage** — same decision, `Expires` name. -/
def expiresSpecR (isStaticGet : ReqPred) (val : Bytes) : StageSpec :=
  stampSpecR (cacheControlDec isStaticGet) expiresName val

/-- **`denoteR_expires`** — the response phase, over ANY arriving response. -/
theorem denoteR_expires (isStaticGet : ReqPred) (val : Bytes) (ctx : Ctx) (r : Response) :
    denoteR ctx (expiresSpecR isStaticGet val).onResp r
      = stampFnR (cacheControlDec isStaticGet) expiresName val ctx r :=
  denoteR_stampProgR _ expiresName val ctx r

/-- **`runChain_expires`** — the single-stage serve, over ANY handler. -/
theorem runChain_expires (isStaticGet : ReqPred) (val : Bytes)
    (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [expiresSpecR isStaticGet val]
      = stampFnR (cacheControlDec isStaticGet) expiresName val ctx (handler ctx) :=
  runChain_stampSpecR _ expiresName val handler ctx

/-- **The asset-immutable stage** — same decision, `Cache-Control` name. -/
def immutableSpecR (isStaticGet : ReqPred) (val : Bytes) : StageSpec :=
  stampSpecR (cacheControlDec isStaticGet) ccName val

/-- **`denoteR_immutable`** — the response phase, over ANY arriving response. -/
theorem denoteR_immutable (isStaticGet : ReqPred) (val : Bytes) (ctx : Ctx) (r : Response) :
    denoteR ctx (immutableSpecR isStaticGet val).onResp r
      = stampFnR (cacheControlDec isStaticGet) ccName val ctx r :=
  denoteR_stampProgR _ ccName val ctx r

/-- **`runChain_immutable`** — the single-stage serve, over ANY handler. -/
theorem runChain_immutable (isStaticGet : ReqPred) (val : Bytes)
    (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [immutableSpecR isStaticGet val]
      = stampFnR (cacheControlDec isStaticGet) ccName val ctx (handler ctx) :=
  runChain_stampSpecR _ ccName val handler ctx

/-- **The content-location stage** — same decision; its VALUE is ctx-only, so only the
decision ever blocked it. -/
def contentLocationSpecR (isStaticGet : ReqPred) (val : Bytes) : StageSpec :=
  stampSpecR (cacheControlDec isStaticGet) clocName val

/-- **`denoteR_contentLocation`** — the response phase, over ANY arriving response. -/
theorem denoteR_contentLocation (isStaticGet : ReqPred) (val : Bytes) (ctx : Ctx) (r : Response) :
    denoteR ctx (contentLocationSpecR isStaticGet val).onResp r
      = stampFnR (cacheControlDec isStaticGet) clocName val ctx r :=
  denoteR_stampProgR _ clocName val ctx r

/-- **`runChain_contentLocation`** — the single-stage serve, over ANY handler. -/
theorem runChain_contentLocation (isStaticGet : ReqPred) (val : Bytes)
    (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [contentLocationSpecR isStaticGet val]
      = stampFnR (cacheControlDec isStaticGet) clocName val ctx (handler ctx) :=
  runChain_stampSpecR _ clocName val handler ctx

/-! ### 3.4 last-modified — `r.status == 200 && isStaticGet c && !hasLm r.headers` -/

/-- The last-modified stage's decision: a `200` static asset with no validator yet. -/
def lastModifiedDec (isStaticGet : ReqPred) (hasLm : List (Bytes × Bytes) → Bool) :
    Ctx → Response → Bool :=
  fun c r => decide (r.status = 200) && isStaticGet c && ! hasLm r.headers

/-- **The last-modified stage.** -/
def lastModifiedSpecR (isStaticGet : ReqPred) (hasLm : List (Bytes × Bytes) → Bool)
    (val : Bytes) : StageSpec := stampSpecR (lastModifiedDec isStaticGet hasLm) lmName val

/-- **`denoteR_lastModified`** — the response phase, over ANY arriving response. -/
theorem denoteR_lastModified (isStaticGet : ReqPred) (hasLm : List (Bytes × Bytes) → Bool)
    (val : Bytes) (ctx : Ctx) (r : Response) :
    denoteR ctx (lastModifiedSpecR isStaticGet hasLm val).onResp r
      = stampFnR (lastModifiedDec isStaticGet hasLm) lmName val ctx r :=
  denoteR_stampProgR _ lmName val ctx r

/-- **`runChain_lastModified`** — the single-stage serve, over ANY handler. -/
theorem runChain_lastModified (isStaticGet : ReqPred) (hasLm : List (Bytes × Bytes) → Bool)
    (val : Bytes) (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [lastModifiedSpecR isStaticGet hasLm val]
      = stampFnR (lastModifiedDec isStaticGet hasLm) lmName val ctx (handler ctx) :=
  runChain_stampSpecR _ lmName val handler ctx

/-! ### 3.5 retry-after — `needsRetryAfter r.status` (a status SET) -/

/-- The retry-after stage's decision: reads the arriving status ALONE (a status set). -/
def retryAfterDec (needsRetryAfter : Nat → Bool) : Ctx → Response → Bool :=
  fun _ r => needsRetryAfter r.status

/-- **The retry-after stage.** -/
def retryAfterSpecR (needsRetryAfter : Nat → Bool) (val : Bytes) : StageSpec :=
  stampSpecR (retryAfterDec needsRetryAfter) retryName val

/-- **`denoteR_retryAfter`** — the response phase, over ANY arriving response. -/
theorem denoteR_retryAfter (needsRetryAfter : Nat → Bool) (val : Bytes)
    (ctx : Ctx) (r : Response) :
    denoteR ctx (retryAfterSpecR needsRetryAfter val).onResp r
      = stampFnR (retryAfterDec needsRetryAfter) retryName val ctx r :=
  denoteR_stampProgR _ retryName val ctx r

/-- **`runChain_retryAfter`** — the single-stage serve, over ANY handler. -/
theorem runChain_retryAfter (needsRetryAfter : Nat → Bool) (val : Bytes)
    (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [retryAfterSpecR needsRetryAfter val]
      = stampFnR (retryAfterDec needsRetryAfter) retryName val ctx (handler ctx) :=
  runChain_stampSpecR _ retryName val handler ctx

/-! ## 4. THE COMPILABLE SLICE — status-only decisions close to the machine

The stamps whose decision reads ONLY the status (plus a ctx conjunct via an inner
`condR`) lower end-to-end through `condStatus`: one `.cond` on the live `aStat` cell,
certified by `compileR_condStatus_correct` under the `status < 2^64` invariant. -/

/-- A pure status-keyed stamp (retry-after's single-status shape): append on
`r.status = k`. -/
def statusStampS (k : Nat) (name val : Bytes) : RespProg :=
  .condStatus k (.addHeader name val) .skip

/-- A status-AND-ctx stamp (cache-control / expires / immutable / content-location):
append on `r.status = 200 && d ctx`, the `d` conjunct an inner `condR`. -/
def staticStatusStampS (d : ReqPred) (name val : Bytes) : RespProg :=
  .condStatus 200 (.condR d (.addHeader name val) .skip) .skip

/-- The pure status-keyed stamp is in the compilable fragment. -/
theorem lowerableS_statusStampS (k : Nat) (name val : Bytes) (hk : k < 2 ^ 64) :
    LowerableS (statusStampS k name val) := ⟨hk, trivial, trivial⟩

/-- `200 < 2^64`, established without evaluating `2^64` in the kernel. -/
theorem status200_wf : (200 : Nat) < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (by decide : (200 : Nat) < 2 ^ 8)
    (Nat.pow_le_pow_right (by decide) (by decide))

/-- The status-AND-ctx stamp is in the compilable fragment. -/
theorem lowerableS_staticStatusStampS (d : ReqPred) (name val : Bytes) :
    LowerableS (staticStatusStampS d name val) :=
  ⟨status200_wf, ⟨trivial, trivial⟩, trivial⟩

/-- **`compile_statusStamp` — the pure status-keyed stamp compiles.** From any state
encoding a well-formed `r`, the machine lands the skeleton of the stamp's denotation. -/
theorem compile_statusStamp (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody : Word) (ctx : Ctx) (hd : Distinct3 aStat aCnt aBody)
    (k : Nat) (name val : Bytes) (hk : k < 2 ^ 64) (r : Response) (st : PancakeState σ)
    (hwf : r.status < 2 ^ 64) (hEnc : Enc3 aStat aCnt aBody st r)
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compileR nm aStat aCnt aBody (statusStampS k name val)) st = (none, st') ∧
      Enc3 aStat aCnt aBody st' (denoteR ctx (statusStampS k name val) r) :=
  let ⟨st', h1, h2, _, _, _⟩ :=
    compileR_condStatus_correct o nm aStat aCnt aBody ctx hd (statusStampS k name val) r st
      (lowerableS_statusStampS k name val hk) hwf hEnc hDec
  ⟨st', h1, h2⟩

/-- **`compile_staticStatusStamp` — the status-AND-ctx stamp compiles.** The status test
is one `.cond` on `aStat`; the ctx conjunct is the inner `condR` `compileR` already
lowers. This is cache-control / expires / immutable / content-location, end-to-end. -/
theorem compile_staticStatusStamp (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody : Word) (ctx : Ctx) (hd : Distinct3 aStat aCnt aBody)
    (d : ReqPred) (name val : Bytes) (r : Response) (st : PancakeState σ)
    (hwf : r.status < 2 ^ 64) (hEnc : Enc3 aStat aCnt aBody st r)
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compileR nm aStat aCnt aBody (staticStatusStampS d name val)) st
        = (none, st') ∧
      Enc3 aStat aCnt aBody st' (denoteR ctx (staticStatusStampS d name val) r) :=
  let ⟨st', h1, h2, _, _, _⟩ :=
    compileR_condStatus_correct o nm aStat aCnt aBody ctx hd (staticStatusStampS d name val) r st
      (lowerableS_staticStatusStampS d name val) hwf hEnc hDec
  ⟨st', h1, h2⟩

/-! ## 5. Non-vacuity — the decisions genuinely READ the arriving response

Concrete kernel `#guard`s at real field bytes. A status-500 response and a status-200
response flip the decisions; a status-500 REFUSAL and a status-200 refusal flip them
under a FIRED gate — the crux, since there the decision reads the inner result. -/

/-- A `500` response, to drive the response-decided branches off. -/
def resp500 : Response :=
  { status := 500, reason := str "Internal Server Error", headers := [], body := [] }

-- the general condResp stamp fires exactly when its decision does (both branches live):
#guard (denoteR ctxGet (stampProgR (fun _ _ => true) (str "N") (str "V")) baseOk).headers
        = baseOk.headers ++ [(str "N", str "V")]
#guard (denoteR ctxGet (stampProgR (fun _ _ => false) (str "N") (str "V")) baseOk).headers
        = baseOk.headers
-- the decision READS the arriving response's status — 200 fires, 500 does not:
#guard (denoteR ctxGet (stampProgR (fun _ r => decide (r.status = 200)) (str "N") (str "V"))
          baseOk).headers = baseOk.headers ++ [(str "N", str "V")]
#guard (denoteR ctxGet (stampProgR (fun _ r => decide (r.status = 200)) (str "N") (str "V"))
          resp500).headers = resp500.headers

/-- The concrete response-decided stamp used in the fired-gate witnesses. -/
def statusStampSpecR (k : Nat) (name val : Bytes) : StageSpec :=
  stampSpecR (fun _ r => decide (r.status = k)) name val

-- THE CRUX: outside a FIRED gate, the stamp decides on the gate's REFUSAL. A 200
-- refusal gets the header; a 500 refusal does not — the decision reads the inner
-- result, the exact capability `condR : Ctx → Bool` lacks:
#guard (runChain ctxPost (fun _ => baseOk)
          [statusStampSpecR 200 (str "N") (str "V"), gateSpec (fun _ => true) baseOk]).headers
        = [(str "N", str "V")]
#guard (runChain ctxPost (fun _ => baseOk)
          [statusStampSpecR 200 (str "N") (str "V"), gateSpec (fun _ => true) resp500]).headers
        = []
-- and the refusal record stays fresh underneath (a real 500 refusal reaches the wire):
#guard (runChain ctxPost (fun _ => baseOk)
          [statusStampSpecR 200 (str "N") (str "V"), gateSpec (fun _ => true) resp500]).status = 500

-- the deployed stamps fire on their real decisions, and not otherwise:
#guard (runChain ctxGet (fun _ => baseOk) [cacheControlSpecR (fun _ => true) (str "no-cache")]).headers
        = baseOk.headers ++ [(ccName, str "no-cache")]
#guard (runChain ctxGet (fun _ => resp500) [cacheControlSpecR (fun _ => true) (str "no-cache")]).headers
        = resp500.headers
-- the ctx conjunct genuinely gates it too (a 200 off-route does NOT get the header):
#guard (runChain ctxGet (fun _ => baseOk) [cacheControlSpecR (fun _ => false) (str "no-cache")]).headers
        = baseOk.headers
-- retry-after keys purely on status (a status set), here firing on 500 and not on 200:
#guard (runChain ctxGet (fun _ => resp500) [retryAfterSpecR (fun s => decide (s = 500)) (str "5")]).headers
        = resp500.headers ++ [(retryName, str "5")]
#guard (runChain ctxGet (fun _ => baseOk) [retryAfterSpecR (fun s => decide (s = 500)) (str "5")]).headers
        = baseOk.headers
-- the header-LIST-reading decisions denote too (link fires on a 200 with no Link):
#guard (runChain ctxGet (fun _ => baseOk) [linkSpecR (fun _ => false) (str "</s.css>")]).headers
        = baseOk.headers ++ [(linkName, str "</s.css>")]
#guard (runChain ctxGet (fun _ => baseOk) [linkSpecR (fun _ => true) (str "</s.css>")]).headers
        = baseOk.headers

-- the compilable forms denote to the deployed conditional append (both branches live):
#guard (denoteR ctxGet (statusStampS 200 (str "N") (str "V")) baseOk).headers
        = baseOk.headers ++ [(str "N", str "V")]
#guard (denoteR ctxGet (statusStampS 200 (str "N") (str "V")) resp500).headers = resp500.headers
#guard (denoteR ctxGet (staticStatusStampS (fun _ => true) (str "N") (str "V")) baseOk).headers
        = [(str "N", str "V")]
#guard (denoteR ctxGet (staticStatusStampS (fun _ => false) (str "N") (str "V")) baseOk).headers = []
-- the `condStatus` (compilable) form and the `condResp` (general) form AGREE on concrete data:
#guard (denoteR ctxGet (staticStatusStampS (fun _ => true) (str "N") (str "V")) baseOk).headers
        = (denoteR ctxGet (stampProgR (cacheControlDec (fun _ => true)) (str "N") (str "V"))
            baseOk).headers

/-! ## 6. THE RESPONSE-DECIDED RESIDUAL — what `condResp` did NOT buy

UNBLOCKED here, denotationally (all 8, §3): warning, link-preload, cache-control,
asset-expires, asset-immutable, last-modified, retry-after, content-location. Each is a
`StageSpec` in the SAME algebra as the other 27 stages, composing in the SAME `runChain`.

COMPILES end-to-end today (§4): cache-control, expires, immutable, content-location
(`status = 200 && ctx`), and the single-status shape of retry-after — their
`condStatus`/`condR` forms are `LowerableS`.

STILL BLOCKED, and on WHAT (not `condResp`'s fault):
 * HEADER-LIST reads — the unless-present family (alt-svc, permissions-policy,
   resource-policy, timing-allow, via, vary-encoding, vary-excluded), plus warning's
   `isTransformed`/`!hasWarning`, link's `!hasLink`, last-modified's `!hasLm`. These
   DENOTE through `condResp` (§3 pins them) but do NOT compile: `Enc3` holds only the
   header COUNT (`aCnt`), not the list, so `!hasX r.headers` has nothing to read. They
   need a MACHINE-SIDE HEADER REPRESENTATION first — a separate, larger piece; do not
   smuggle it in with `condResp`.
 * retry-after's `needsRetryAfter r.status` is a status SET; it compiles as a NEST of
   `condStatus` equalities (a disjunction), a straightforward extension of the single
   comparison proven here.
 * cache-status (NOT among the 8) needs BOTH a header read (`!hasCS r.headers`) AND a
   response-READING VALUE (`isHit r.headers`) — the latter is
   `addHeaderOf : Ctx → Response → Bytes`, strictly beyond `condResp` (`addHeader`'s
   constant `val` cannot express it). Doubly blocked.
 * Chain-level COMPILATION of a `condResp` stamp: `compileChain_correct` is gated on
   `Compilable`, which excludes `condResp`. A chain containing a general response-decided
   stamp therefore has NO machine theorem — correct, since it has no faithful lowering.
   The status-keyed forms (§4) are the ones that reach the machine. -/

/-! ## 7. Axiom audit — expect ⊆ {propext, Classical.choice, Quot.sound}, 0 sorryAx. -/

#print axioms denoteR_stampProgR
#print axioms runChain_stampSpecR
#print axioms condRespStamp_carries_on_gate_refusal
-- the 8 stamps, denoteR pins:
#print axioms denoteR_warning
#print axioms denoteR_link
#print axioms denoteR_cacheControl
#print axioms denoteR_expires
#print axioms denoteR_immutable
#print axioms denoteR_lastModified
#print axioms denoteR_retryAfter
#print axioms denoteR_contentLocation
-- the 8 stamps, runChain pins:
#print axioms runChain_warning
#print axioms runChain_link
#print axioms runChain_cacheControl
#print axioms runChain_expires
#print axioms runChain_immutable
#print axioms runChain_lastModified
#print axioms runChain_retryAfter
#print axioms runChain_contentLocation
-- the compilable slice:
#print axioms compile_statusStamp
#print axioms compile_staticStatusStamp

end Pancake.StageLift2Cond
