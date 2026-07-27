/-
  Pancake/StageLiftHeader.lean — THE HEADER-STAMP LIFT. ONE general theorem for the
  `addHeader` shape, then every stamp-shaped deployed stage is a ONE-LINE
  instantiation.

  WHY THIS FILE EXISTS. StageProg.lean / StageMore.lean / StageEvenMore.lean each
  express a deployed stage by HAND: a bespoke `StageProg` term plus a bespoke
  `denote_<stage>` pin, three or four per wave. That does not scale and, worse, it
  accumulates SAMPLES instead of proving the THING. The deployed response-stamp
  stages are not 26 different animals: they are 26 instances of ONE shape. This file
  proves the shape ONCE (§4–§7, universally quantified over the field name, the
  value, the decision, the context and the builder) and instantiates it (§8).

  THE SHAPE (read off the deployed stage functions, not re-specified from prose).
  Every stamp-shaped deployed stage has
      onRequest  := fun c => .continue c          -- pass, untouched
      onResponse := fun c b => <append one (name, val) at the END of b's headers,
                                under the stage's own decision>
  and the deployed source writes that in exactly three surface forms:

   (F1) UNCONDITIONAL append — `fun _ b => b.addHeader (name, val)`
        (`DateHeader.dateStage`).

   (F2) CONDITIONAL append — `fun c b => if <cond> then b.addHeader (name, val) else b`
        (`CacheControl.cacheControlStage`, `AssetExpires.assetExpiresStage`,
        `AssetImmutable.assetImmutableStage`, `ContentLocation.contentLocationStage`,
        `ModifiedSince.lmStampStage`, `Dashboard.dashTypeStage`, `SseServe.sseHeadStage`,
        `SpaServe.spaTypeStage`, `SessionCookie.setCookieStage`,
        `RetryAfter.retryAfterStage`, `RequestId.ridStage`, `ProxyProtocol.proxyProtoStage`,
        `Cors.corsStage`).

   (F3) `mapResp` GUARDED STAMP — `fun _ b => b.mapResp (fun r => { r with headers :=
        stampX r.headers })` where the deployed `stampX` is, uniformly,
        `if hasX hs then hs else hs ++ [(name, val)]` (append-unless-present) or its
        positive twin `if <cond> hs then hs ++ [(name, val)] else hs`
        (`AltSvc.stampAlt`, `PermissionsPolicy.stampPP`,
        `CrossOriginResource.stampCorp`, `TimingAllowOrigin.stampTAO`, `Via.stampVia`,
        `VaryEncoding.stampVary`, `CacheStatus.stampCS`, `WarningTransform.stampWarn`,
        `LinkPreload.stampLink`).

  F1/F2/F3 are the SAME operation. §2 states it once as `stampOn` — an append of
  `(name, valOf c r)` under a decision `P c r` over the context and the response cell
  — and §4/§5/§6/§7 prove the DSL's `denote` computes it, for all parameters. F3's
  `mapResp` surface is bridged to the `addHeader` surface by a real lemma (§6), not
  assumed.

  WHAT IS PROVEN
   * §4  `denote_addHeader_stamp` — the F1 lift. `∀ nm name val ctx b, b.acc = ctx.base →
         denote (.addHeader name val) ctx = ((alwaysStamp nm name val).onResponse ctx b).build`.
   * §5  `denote_stampProg` — **THE LIFT**, the F2 general theorem, `∀ nm P name valOf
         val ctx b`, with the decision `P` and the value function `valOf` ABSTRACT: the
         DSL's `condR`-guarded `addHeader` denotes to the deployed conditional append,
         whatever the stage's decision and value are.
   * §6  `denote_stampUnless` / `denote_stampField` — the F3 lifts, over the deployed
         `mapResp`+`stampX` surface in its two branch polarities.
   * §6.1 `denote_stampExcluded` — the exclusion-wrapper lift (`DeployPlus8.varyGate8`'s
         `if isBulkTarget c then b else varyStage.onResponse c b`).
   * §7  `denote_stampSeq` — the multi-header lift: a `seq` of `addHeader`s denotes to
         the deployed `foldl ResponseBuilder.addHeader` (`SecurityHeaders`'s whole
         policy set, `ContentLanguage.langStampStage`'s pair), for ANY header list.
   * §8  TWENTY-TWO deployed stages instantiated, each a one-line term + a one-line pin
         through the lift. No stage gets a bespoke proof.

  THE MODEL CORRESPONDENCE (named, not hidden). This package (`pancake`) has no
  `require` on the deployed package, so §1 TRANSCRIBES the deployed
  `StageStep`/`ResponseBuilder`/`Stage` definitions verbatim from the deployed source
  rather than importing them; the transcription is byte-for-byte the deployed text and
  the deployed `Response` record (`status`/`reason`/`headers`/`body`) is already
  definitionally the one this package's serializer renders. The deployed `Ctx` carries
  request attributes and the raw input this package's `Ctx` does not model; that is why
  every decision enters the lift as an ABSTRACT `P : Ctx → Response → Bool` and every
  computed value as an ABSTRACT `valOf : Ctx → Response → Bytes` — the lift is proven
  for ALL of them, so a stage's own decision instantiates it whatever it reads. A
  cross-package `rfl` against the deployed constant is not available without a shared
  build; that is the residual, and it is the only one the lift adds.

  RESIDUALS (named)
   * The transcription/import gap above.
   * The lift pins the stage's RESPONSE phase at its own boundary: `ctx.base` is the
     response arriving at the stage (the builder the inner onion hands outward), which
     is what `b.acc = ctx.base` says. Composing the 52-stage onion end-to-end is
     `runResp`/`runPipeline`, not this file.
   * A stage whose response phase is NOT a header append (a per-header `map`, a
     whole-response rewrite, a body transform) is OUT of this shape by construction;
     §9 lists each such deployed stage and why it does not fit. They are not forced.
-/
import Pancake.StageProg

namespace Pancake.StageLiftHeader

open Pancake Pancake.SerializeCompile Pancake.StageProg

/-! ## 1. The deployed stage model — TRANSCRIBED

Verbatim from the deployed `Pipeline.lean`. `Response` is already this package's
serializer input (`SerializeCompile.Response`: `status`/`reason`/`headers`/`body`),
definitionally the deployed record. -/

/-- The request-phase result: gate with a response now, or pass through. (Deployed
`StageStep`.) -/
inductive StageStep where
  /-- Gate: answer now with `r`; the handler and every later stage are skipped. -/
  | respond (r : Response)
  /-- Pass through to the next stage with context `c`. -/
  | continue (c : Ctx)

/-- The affine response builder: a single accumulating response cell, mutated in
place by the response phase. (Deployed `ResponseBuilder`.) -/
structure ResponseBuilder where
  /-- The accumulating response — the single reused cell. -/
  acc : Response

/-- Acquire the cell, seeded with a base response. (Deployed `ofResponse`.) -/
def ResponseBuilder.ofResponse (r : Response) : ResponseBuilder := ⟨r⟩

/-- Finalize the builder to its accumulated `Response`. (Deployed `build`.) -/
def ResponseBuilder.build (b : ResponseBuilder) : Response := b.acc

/-- Push a header onto the cell — append at the END, matching `r.headers ++ [nv]`.
(Deployed `addHeader`.) -/
def ResponseBuilder.addHeader (b : ResponseBuilder) (nv : Bytes × Bytes) : ResponseBuilder :=
  ⟨{ b.acc with headers := b.acc.headers ++ [nv] }⟩

/-- Apply a whole-`Response` transform to the cell in place. (Deployed `mapResp` —
the surface every `stampX` stage writes its header transform through.) -/
def ResponseBuilder.mapResp (b : ResponseBuilder) (f : Response → Response) : ResponseBuilder :=
  ⟨f b.acc⟩

/-- A pipeline stage: a named request-phase transform (which may gate) and a
response-phase transform threading the affine builder. (Deployed `Stage`.) -/
structure Stage where
  /-- A human name for the stage (diagnostics; not load-bearing). -/
  name : String
  /-- Request phase (run in list order): gate or pass through. -/
  onRequest : Ctx → StageStep
  /-- Response phase (run in REVERSE list order — the onion). -/
  onResponse : Ctx → ResponseBuilder → ResponseBuilder

/-! ## 2. The GENERIC deployed stamp — the one shape F1/F2/F3 all are

`stampOn P name valOf` is the deployed response-stamp operation with the stage's own
decision `P` and value `valOf` left abstract: append `(name, valOf c r)` at the end of
the cell's header list exactly when `P c r` fires, otherwise leave the cell alone.

Instantiating `P := fun _ _ => true` gives F1; a stage's `if <cond>` gives F2; a
deployed `stampX`'s presence guard gives F3 (§6 does that bridge). -/

/-- **The generic deployed response-stamp.** One conditional header append on the
affine cell — the operation every stamp-shaped deployed stage's `onResponse` performs. -/
def stampOn (P : Ctx → Response → Bool) (name : Bytes) (valOf : Ctx → Response → Bytes)
    (c : Ctx) (b : ResponseBuilder) : ResponseBuilder :=
  if P c b.acc then b.addHeader (name, valOf c b.acc) else b

/-- **The generic deployed stamp stage.** Passes the request untouched; stamps the
response under its own decision. Every stage of §8 IS this, at its own `P`/`valOf`. -/
def stampStage (nm : String) (P : Ctx → Response → Bool) (name : Bytes)
    (valOf : Ctx → Response → Bytes) : Stage where
  name := nm
  onRequest := fun c => .continue c
  onResponse := stampOn P name valOf

/-- The unconditional stamp stage (F1): `onResponse := fun _ b => b.addHeader (name, val)`. -/
def alwaysStamp (nm : String) (name val : Bytes) : Stage :=
  stampStage nm (fun _ _ => true) name (fun _ _ => val)

/-- The unconditional stamp stage really is the bare deployed `addHeader` surface —
`fun _ b => b.addHeader (name, val)`, the literal `DateHeader.dateStage` response
phase. (So §4's pin is against the deployed text, not against `stampOn`.) -/
theorem alwaysStamp_onResponse (nm : String) (name val : Bytes) (c : Ctx) (b : ResponseBuilder) :
    (alwaysStamp nm name val).onResponse c b = b.addHeader (name, val) := rfl

/-! ## 3. The DSL side — the stamp program

The `StageProg` term shape for a stamp: a `condR` on the stage's decision, appending
on the fire branch and doing nothing (`rewriteBody .identity`, the DSL's no-op) on the
other. The unconditional stamp is the bare `addHeader`. -/

/-- **The stamp program.** `condR p (addHeader name val) (no-op)` — the DSL term every
conditional stamp stage compiles from. -/
def stampProg (p : ReqPred) (name val : Bytes) : StageProg :=
  .condR p (.addHeader name val) (.rewriteBody .identity)

/-! ## 4. THE F1 LIFT — the unconditional stamp

`∀ nm name val ctx b`, with `b` the cell arriving at the stage. -/

/-- **`denote_addHeader_stamp` — the F1 lift.** For ALL field names, values, contexts
and arriving cells, the DSL's `addHeader` denotes to exactly the response the deployed
UNCONDITIONAL stamp stage builds (`fun _ b => b.addHeader (name, val)`, the literal
`DateHeader.dateStage` response phase). -/
theorem denote_addHeader_stamp (nm : String) (name val : Bytes) (ctx : Ctx)
    (b : ResponseBuilder) (hb : b.acc = ctx.base) :
    denote (.addHeader name val) ctx = ((alwaysStamp nm name val).onResponse ctx b).build := by
  obtain ⟨acc⟩ := b
  subst hb
  show (denoteStep ctx (.addHeader name val) { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, Bool.false_eq_true, if_false]
  rfl

/-! ## 5. THE LIFT — the general conditional stamp (F2)

**This is the theorem the file exists for.** Universally quantified over the stage
name, the DECISION `P`, the field name, the VALUE FUNCTION `valOf`, the stamped value,
the context and the arriving cell: the DSL's `condR`-guarded `addHeader` denotes to
exactly the response the deployed conditional-append stage builds. Every stamp stage
of §8 follows from THIS by instantiation — none gets its own proof. -/

/-- **`denote_stampProg` — THE LIFT.** For ALL `nm P name valOf val ctx b` with `b` the
cell arriving at the stage (`b.acc = ctx.base`) and `val` the value the stage's own
`valOf` computes at this context (`valOf ctx ctx.base = val`):

    denote (stampProg (fun c => P c c.base) name val) ctx
      = ((stampStage nm P name valOf).onResponse ctx b).build

The decision `P` and the value function `valOf` are ABSTRACT — the deployed stage's own
`if b.acc.status == 200 && isStaticGet c`, `if inScope c`, `if needsRetryAfter b.acc.status`,
`!hasX b.acc.headers`, `canonicalResourcePath c.req.target`, … all instantiate it. The
right-hand side genuinely runs the deployed `onResponse`, so this is not a tautology:
both branches of the stage's decision are discharged against the real builder ops. -/
theorem denote_stampProg (nm : String) (P : Ctx → Response → Bool) (name : Bytes)
    (valOf : Ctx → Response → Bytes) (val : Bytes) (ctx : Ctx) (b : ResponseBuilder)
    (hb : b.acc = ctx.base) (hval : valOf ctx ctx.base = val) :
    denote (stampProg (fun c => P c c.base) name val) ctx
      = ((stampStage nm P name valOf).onResponse ctx b).build := by
  obtain ⟨acc⟩ := b
  subst hb
  subst hval
  show (denoteStep ctx (.condR (fun c => P c c.base) (.addHeader name (valOf ctx ctx.base))
          (.rewriteBody .identity)) { resp := ctx.base, halted := false }).resp
      = (stampOn P name valOf ctx ⟨ctx.base⟩).build
  by_cases h : P ctx ctx.base = true
  · simp only [denoteStep, h, if_true, Bool.false_eq_true, if_false]
    show ({ ctx.base with headers := ctx.base.headers ++ [(name, valOf ctx ctx.base)] } : Response) = _
    unfold stampOn
    simp only [h, if_true]
    rfl
  · simp only [Bool.not_eq_true] at h
    simp only [denoteStep, h, Bool.false_eq_true, if_false, runBody]
    unfold stampOn
    simp only [h, Bool.false_eq_true, if_false]
    rfl

/-- **The decision is read only AT the context.** A stamp program's denotation depends
on its request-predicate only through its value at `ctx` — so two decisions agreeing
there denote alike. (The composition tool §6.1's wrapper needs; `denoteStep`'s `condR`
evaluates `c ctx` and nothing else.) -/
theorem denote_stampProg_pred (p q : ReqPred) (name val : Bytes) (ctx : Ctx)
    (h : p ctx = q ctx) :
    denote (stampProg p name val) ctx = denote (stampProg q name val) ctx := by
  show (denoteStep ctx (.condR p (.addHeader name val) (.rewriteBody .identity))
          { resp := ctx.base, halted := false }).resp
      = (denoteStep ctx (.condR q (.addHeader name val) (.rewriteBody .identity))
          { resp := ctx.base, halted := false }).resp
  simp only [denoteStep, h]

/-! ## 6. THE F3 LIFTS — the `mapResp` guarded-stamp surface

The deployed stamp stages of the `mapResp` family write their append through a header
transform `stampX : List (Bytes × Bytes) → List (Bytes × Bytes)` which is, uniformly,
an append guarded by a decision on the header list — in one of two branch polarities:

  * APPEND-UNLESS-PRESENT (`stampAlt`/`stampPP`/`stampCorp`/`stampTAO`/`stampVia`/
    `stampVary`):  `if hasX hs then hs else hs ++ [(name, val)]`
  * APPEND-WHEN (`stampWarn`/`stampLink`):  `if Q hs then hs ++ [(name, val)] else hs`

Both are stated below in the deployed text's own form and lifted. This is a real
bridge — the `mapResp`-of-an-`if` surface is proven equal to the `if`-of-an-`addHeader`
surface; it is not assumed. -/

/-- The deployed APPEND-UNLESS-PRESENT header transform, generically — the literal
shape of `stampAlt`/`stampPP`/`stampCorp`/`stampTAO`/`stampVia`/`stampVary`. -/
def stampUnless (hasX : List (Bytes × Bytes) → Bool) (name val : Bytes)
    (hs : List (Bytes × Bytes)) : List (Bytes × Bytes) :=
  if hasX hs then hs else hs ++ [(name, val)]

/-- The deployed APPEND-WHEN header transform, generically — the literal shape of
`stampWarn` and (with the status folded into `Q`) `stampLink`. -/
def stampField (Q : List (Bytes × Bytes) → Bool) (name val : Bytes)
    (hs : List (Bytes × Bytes)) : List (Bytes × Bytes) :=
  if Q hs then hs ++ [(name, val)] else hs

/-- **The `mapResp` bridge (unless-present).** The deployed `mapResp`+`stampUnless`
response phase IS the generic conditional stamp at decision `!hasX r.headers` — for ANY
guard, name, value, context and cell. Both surfaces, proven equal. -/
theorem mapResp_stampUnless_eq (nm : String) (hasX : List (Bytes × Bytes) → Bool)
    (name val : Bytes) (c : Ctx) (b : ResponseBuilder) :
    b.mapResp (fun r => { r with headers := stampUnless hasX name val r.headers })
      = (stampStage nm (fun _ r => !hasX r.headers) name (fun _ _ => val)).onResponse c b := by
  obtain ⟨acc⟩ := b
  show (⟨{ acc with headers := stampUnless hasX name val acc.headers }⟩ : ResponseBuilder)
      = stampOn (fun _ r => !hasX r.headers) name (fun _ _ => val) c ⟨acc⟩
  unfold stampUnless stampOn
  by_cases h : hasX acc.headers = true
  · simp only [h, if_true, Bool.not_true, Bool.false_eq_true, if_false]
  · simp only [Bool.not_eq_true] at h
    simp only [h, Bool.false_eq_true, if_false, Bool.not_false, if_true]
    rfl

/-- **The `mapResp` bridge (append-when).** The deployed `mapResp`+`stampField` response
phase IS the generic conditional stamp at decision `Q r.headers`. -/
theorem mapResp_stampField_eq (nm : String) (Q : List (Bytes × Bytes) → Bool)
    (name val : Bytes) (c : Ctx) (b : ResponseBuilder) :
    b.mapResp (fun r => { r with headers := stampField Q name val r.headers })
      = (stampStage nm (fun _ r => Q r.headers) name (fun _ _ => val)).onResponse c b := by
  obtain ⟨acc⟩ := b
  show (⟨{ acc with headers := stampField Q name val acc.headers }⟩ : ResponseBuilder)
      = stampOn (fun _ r => Q r.headers) name (fun _ _ => val) c ⟨acc⟩
  unfold stampField stampOn
  by_cases h : Q acc.headers = true
  · simp only [h, if_true]
    rfl
  · simp only [Bool.not_eq_true] at h
    simp only [h, Bool.false_eq_true, if_false]

/-- **`denote_stampUnless` — the F3 lift (unless-present).** For ALL guards, names,
values, contexts and arriving cells, the DSL stamp program denotes to exactly the
response the deployed `mapResp (fun r => { r with headers := stampUnless … r.headers })`
stage builds — the LITERAL deployed `stampAlt`/`stampPP`/`stampCorp`/`stampTAO`/
`stampVia`/`stampVary` response phase. -/
theorem denote_stampUnless (hasX : List (Bytes × Bytes) → Bool) (name val : Bytes)
    (ctx : Ctx) (b : ResponseBuilder) (hb : b.acc = ctx.base) :
    denote (stampProg (fun c => !hasX c.base.headers) name val) ctx
      = (b.mapResp (fun r => { r with headers := stampUnless hasX name val r.headers })).build := by
  rw [mapResp_stampUnless_eq "stamp" hasX name val ctx b]
  exact denote_stampProg "stamp" (fun _ r => !hasX r.headers) name (fun _ _ => val) val ctx b hb rfl

/-- **`denote_stampField` — the F3 lift (append-when).** As above for the positive
branch polarity — the LITERAL deployed `stampWarn` / `stampLink` response phase. -/
theorem denote_stampField (Q : List (Bytes × Bytes) → Bool) (name val : Bytes)
    (ctx : Ctx) (b : ResponseBuilder) (hb : b.acc = ctx.base) :
    denote (stampProg (fun c => Q c.base.headers) name val) ctx
      = (b.mapResp (fun r => { r with headers := stampField Q name val r.headers })).build := by
  rw [mapResp_stampField_eq "stamp" Q name val ctx b]
  exact denote_stampProg "stamp" (fun _ r => Q r.headers) name (fun _ _ => val) val ctx b hb rfl

/-! ### 6.1 The exclusion wrapper

`DeployPlus8.varyGate8` wraps a stamp stage in a route exclusion:
`onResponse := fun c b => if isBulkTarget c then b else varyStage.onResponse c b`. That
is again the generic stamp, at the CONJOINED decision — so it lifts too, no new proof. -/

/-- The deployed exclusion-wrapped stamp response phase, generically. -/
def stampExcluded (excl : Ctx → Bool) (inner : Ctx → ResponseBuilder → ResponseBuilder)
    (c : Ctx) (b : ResponseBuilder) : ResponseBuilder :=
  if excl c then b else inner c b

/-- **`denote_stampExcluded` — the exclusion-wrapper lift.** For ALL exclusions,
guards, names, values, contexts and cells: the DSL stamp program at the conjoined
decision denotes to exactly the response the deployed exclusion-wrapped
`mapResp`+`stampUnless` stage builds (the literal `varyGate8` response phase over
`VaryEncoding.varyStage`). -/
theorem denote_stampExcluded (excl : Ctx → Bool) (hasX : List (Bytes × Bytes) → Bool)
    (name val : Bytes) (ctx : Ctx) (b : ResponseBuilder) (hb : b.acc = ctx.base) :
    denote (stampProg (fun c => !excl c && !hasX c.base.headers) name val) ctx
      = (stampExcluded excl
          (fun _ bb => bb.mapResp (fun r => { r with headers := stampUnless hasX name val r.headers }))
          ctx b).build := by
  obtain ⟨acc⟩ := b
  subst hb
  unfold stampExcluded
  by_cases he : excl ctx = true
  · rw [if_pos he,
      denote_stampProg_pred (fun c => !excl c && !hasX c.base.headers) (fun _ => false)
        name val ctx (by simp only [he, Bool.not_true, Bool.false_and])]
    show (denoteStep ctx (.condR (fun _ => false) (.addHeader name val)
            (.rewriteBody .identity)) { resp := ctx.base, halted := false }).resp = _
    simp only [denoteStep, Bool.false_eq_true, if_false, runBody]
    rfl
  · simp only [Bool.not_eq_true] at he
    rw [if_neg (by simp only [he]; exact Bool.false_ne_true),
      denote_stampProg_pred (fun c => !excl c && !hasX c.base.headers)
        (fun c => !hasX c.base.headers) name val ctx
        (by simp only [he, Bool.not_false, Bool.true_and])]
    exact denote_stampUnless hasX name val ctx ⟨ctx.base⟩ rfl

/-! ## 7. The multi-header lift — a `seq` of appends IS the deployed `foldl addHeader`

`SecurityHeaders.securityheadersStage`'s response phase is
`fun _ b => (wireHeaders policy).foldl ResponseBuilder.addHeader b` — the WHOLE policy
header set folded onto the cell — and `ContentLanguage.langStampStage` chains two
appends. Both are the DSL's `seq` of `addHeader`s. Proven by induction on the header
list, so it covers a set of ANY size. -/

/-- The DSL term for a header SET: a `seq` chain of `addHeader`s, in list order (the
empty set is the DSL no-op). -/
def stampSeq : List (Bytes × Bytes) → StageProg
  | []        => .rewriteBody .identity
  | nv :: rest => .seq (.addHeader nv.1 nv.2) (stampSeq rest)

/-- The generic multi-header deployed stamp stage (`foldl addHeader` — the literal
`SecurityHeaders.securityheadersStage` response phase). -/
def stampSetStage (nm : String) (nvs : List (Bytes × Bytes)) : Stage where
  name := nm
  onRequest := fun c => .continue c
  onResponse := fun _ b => nvs.foldl ResponseBuilder.addHeader b

/-- The fold-step law (deployed `build_addHeaders`): building after a whole sequence of
`addHeader`s yields the base with all of them appended, in order. Induction on the set. -/
theorem build_addHeaders (b : ResponseBuilder) (nvs : List (Bytes × Bytes)) :
    (nvs.foldl ResponseBuilder.addHeader b).build
      = { b.build with headers := b.build.headers ++ nvs } := by
  induction nvs generalizing b with
  | nil =>
    show b.build = { b.build with headers := b.build.headers ++ [] }
    rw [List.append_nil]
  | cons nv rest ih =>
    rw [List.foldl_cons, ih]
    show ({ (b.addHeader nv).build with headers := (b.addHeader nv).build.headers ++ rest } : Response)
        = _
    show ({ b.acc with headers := (b.acc.headers ++ [nv]) ++ rest } : Response) = _
    rw [List.append_assoc]
    rfl

/-- The DSL `seq` chain folds to the same append (induction on the set, threading the
un-halted state). -/
theorem denoteStep_stampSeq (ctx : Ctx) :
    ∀ (nvs : List (Bytes × Bytes)) (r : Response),
      denoteStep ctx (stampSeq nvs) { resp := r, halted := false }
        = { resp := { r with headers := r.headers ++ nvs }, halted := false } := by
  intro nvs
  induction nvs with
  | nil =>
    intro r
    show denoteStep ctx (.rewriteBody .identity) { resp := r, halted := false } = _
    simp only [denoteStep, Bool.false_eq_true, if_false, runBody]
    rw [List.append_nil]
  | cons nv rest ih =>
    intro r
    show denoteStep ctx (stampSeq rest)
        (denoteStep ctx (.addHeader nv.1 nv.2) { resp := r, halted := false }) = _
    have hstep : denoteStep ctx (.addHeader nv.1 nv.2) { resp := r, halted := false }
        = { resp := { r with headers := r.headers ++ [(nv.1, nv.2)] }, halted := false } := by
      simp only [denoteStep, Bool.false_eq_true, if_false]
    rw [hstep, ih]
    show ({ resp := { r with headers := (r.headers ++ [(nv.1, nv.2)]) ++ rest },
            halted := false } : DState) = _
    rw [List.append_assoc]
    rfl

/-- **`denote_stampSeq` — the multi-header lift.** For ANY header set, context and
arriving cell, the DSL's `seq` chain of `addHeader`s denotes to exactly the response the
deployed `foldl ResponseBuilder.addHeader` stage builds — the literal
`SecurityHeaders.securityheadersStage` response phase, at ANY policy size. -/
theorem denote_stampSeq (nm : String) (nvs : List (Bytes × Bytes)) (ctx : Ctx)
    (b : ResponseBuilder) (hb : b.acc = ctx.base) :
    denote (stampSeq nvs) ctx = ((stampSetStage nm nvs).onResponse ctx b).build := by
  obtain ⟨acc⟩ := b
  subst hb
  show (denoteStep ctx (stampSeq nvs) { resp := ctx.base, halted := false }).resp
      = (nvs.foldl ResponseBuilder.addHeader ⟨ctx.base⟩).build
  rw [denoteStep_stampSeq ctx nvs ctx.base, build_addHeaders ⟨ctx.base⟩ nvs]
  rfl

/-! ## 8. THE INSTANTIATIONS — every stamp-shaped deployed stage, one line each

Each stage below is: a one-line `StageProg` term (the lift's `stampProg`/`stampSeq` at
the stage's field bytes) and a one-line pin (`denote_…` applied). The deployed decision
enters as a parameter named for the deployed function it is (`hasAlt`, `isStaticGet`,
`inScope`, …), so the pin holds for the REAL decision whatever it computes — this
package cannot import it (§ the model correspondence).

Field names/values are the exact ASCII the deployed stages render. -/

/-! ### 8.1 The `mapResp` append-unless-present family (F3) -/

/-- `Alt-Svc` field name / value (deployed `AltSvc.altName`/`altVal`). -/
def altName : Bytes := str "Alt-Svc"
/-- The deployed advertised alternative service. -/
def altVal : Bytes := str "h3=\":443\"; ma=86400"

/-- **`altProg`** — the deployed `AltSvc.altStage`, in the DSL. One line. -/
def altProg (hasAlt : List (Bytes × Bytes) → Bool) : StageProg :=
  stampProg (fun c => !hasAlt c.base.headers) altName altVal

/-- **`denote_alt`** — pinned to the deployed `altStage.onResponse`
(`b.mapResp (fun r => { r with headers := stampAlt r.headers })`, `stampAlt hs =
if hasAlt hs then hs else hs ++ [(altName, altVal)]`). One line, via the lift. -/
theorem denote_alt (hasAlt : List (Bytes × Bytes) → Bool) (ctx : Ctx) (b : ResponseBuilder)
    (hb : b.acc = ctx.base) :
    denote (altProg hasAlt) ctx
      = (b.mapResp (fun r => { r with headers := stampUnless hasAlt altName altVal r.headers })).build :=
  denote_stampUnless hasAlt altName altVal ctx b hb

/-- `Permissions-Policy` field name / the deployed deny-all value. -/
def ppName : Bytes := str "Permissions-Policy"
/-- The deployed deny-all permissions policy. -/
def ppVal : Bytes := str "geolocation=(), camera=(), microphone=()"

/-- **`ppProg`** — the deployed `PermissionsPolicy.ppStage`, in the DSL. -/
def ppProg (hasPP : List (Bytes × Bytes) → Bool) : StageProg :=
  stampProg (fun c => !hasPP c.base.headers) ppName ppVal

/-- **`denote_pp`** — pinned to the deployed `ppStage.onResponse` (`stampPP`). -/
theorem denote_pp (hasPP : List (Bytes × Bytes) → Bool) (ctx : Ctx) (b : ResponseBuilder)
    (hb : b.acc = ctx.base) :
    denote (ppProg hasPP) ctx
      = (b.mapResp (fun r => { r with headers := stampUnless hasPP ppName ppVal r.headers })).build :=
  denote_stampUnless hasPP ppName ppVal ctx b hb

/-- `Cross-Origin-Resource-Policy` field name / the deployed `same-origin` value. -/
def corpName : Bytes := str "Cross-Origin-Resource-Policy"
/-- The deployed CORP value. -/
def corpVal : Bytes := str "same-origin"

/-- **`corpProg`** — the deployed `CrossOriginResource.corpStage`, in the DSL. -/
def corpProg (hasCorp : List (Bytes × Bytes) → Bool) : StageProg :=
  stampProg (fun c => !hasCorp c.base.headers) corpName corpVal

/-- **`denote_corp`** — pinned to the deployed `corpStage.onResponse` (`stampCorp`). -/
theorem denote_corp (hasCorp : List (Bytes × Bytes) → Bool) (ctx : Ctx) (b : ResponseBuilder)
    (hb : b.acc = ctx.base) :
    denote (corpProg hasCorp) ctx
      = (b.mapResp (fun r => { r with headers := stampUnless hasCorp corpName corpVal r.headers })).build :=
  denote_stampUnless hasCorp corpName corpVal ctx b hb

/-- `Timing-Allow-Origin` field name / the deployed value. -/
def taoName : Bytes := str "Timing-Allow-Origin"
/-- The deployed TAO value. -/
def taoVal : Bytes := str "*"

/-- **`taoProg`** — the deployed `TimingAllowOrigin.taoStage`, in the DSL. -/
def taoProg (hasTAO : List (Bytes × Bytes) → Bool) : StageProg :=
  stampProg (fun c => !hasTAO c.base.headers) taoName taoVal

/-- **`denote_tao`** — pinned to the deployed `taoStage.onResponse` (`stampTAO`). -/
theorem denote_tao (hasTAO : List (Bytes × Bytes) → Bool) (ctx : Ctx) (b : ResponseBuilder)
    (hb : b.acc = ctx.base) :
    denote (taoProg hasTAO) ctx
      = (b.mapResp (fun r => { r with headers := stampUnless hasTAO taoName taoVal r.headers })).build :=
  denote_stampUnless hasTAO taoName taoVal ctx b hb

/-- `Via` field name / the deployed received-protocol + pseudonym value. -/
def viaName : Bytes := str "Via"
/-- The deployed `Via` value (RFC 9110 §7.6.3). -/
def viaVal : Bytes := str "1.1 edge"

/-- **`viaProg`** — the deployed `Via.viaStage`, in the DSL. -/
def viaProg (hasVia : List (Bytes × Bytes) → Bool) : StageProg :=
  stampProg (fun c => !hasVia c.base.headers) viaName viaVal

/-- **`denote_via`** — pinned to the deployed `viaStage.onResponse` (`stampVia`). -/
theorem denote_via (hasVia : List (Bytes × Bytes) → Bool) (ctx : Ctx) (b : ResponseBuilder)
    (hb : b.acc = ctx.base) :
    denote (viaProg hasVia) ctx
      = (b.mapResp (fun r => { r with headers := stampUnless hasVia viaName viaVal r.headers })).build :=
  denote_stampUnless hasVia viaName viaVal ctx b hb

/-- `Vary` field name / the deployed `Accept-Encoding` value. -/
def varyName : Bytes := str "Vary"
/-- The deployed negotiation cache key. -/
def varyVal : Bytes := str "Accept-Encoding"

/-- **`varyProg`** — the deployed `VaryEncoding.varyStage`, in the DSL. -/
def varyProg (hasVary : List (Bytes × Bytes) → Bool) : StageProg :=
  stampProg (fun c => !hasVary c.base.headers) varyName varyVal

/-- **`denote_vary`** — pinned to the deployed `varyStage.onResponse` (`stampVary`). -/
theorem denote_vary (hasVary : List (Bytes × Bytes) → Bool) (ctx : Ctx) (b : ResponseBuilder)
    (hb : b.acc = ctx.base) :
    denote (varyProg hasVary) ctx
      = (b.mapResp (fun r => { r with headers := stampUnless hasVary varyName varyVal r.headers })).build :=
  denote_stampUnless hasVary varyName varyVal ctx b hb

/-- **`varyGate8Prog`** — the deployed `DeployPlus8.varyGate8`: the `Vary` stamp with the
`/bulk` datapath excluded. In the DSL, one line, at the conjoined decision. -/
def varyGate8Prog (isBulkTarget : Ctx → Bool) (hasVary : List (Bytes × Bytes) → Bool) : StageProg :=
  stampProg (fun c => !isBulkTarget c && !hasVary c.base.headers) varyName varyVal

/-- **`denote_varyGate8`** — pinned to the deployed `varyGate8.onResponse`
(`fun c b => if isBulkTarget c then b else varyStage.onResponse c b`). -/
theorem denote_varyGate8 (isBulkTarget : Ctx → Bool) (hasVary : List (Bytes × Bytes) → Bool)
    (ctx : Ctx) (b : ResponseBuilder) (hb : b.acc = ctx.base) :
    denote (varyGate8Prog isBulkTarget hasVary) ctx
      = (stampExcluded isBulkTarget
          (fun _ bb => bb.mapResp (fun r =>
            { r with headers := stampUnless hasVary varyName varyVal r.headers })) ctx b).build :=
  denote_stampExcluded isBulkTarget hasVary varyName varyVal ctx b hb

/-! ### 8.2 The `mapResp` append-when family (F3, positive polarity) -/

/-- `Warning` field name / the deployed `214 Transformation Applied` value. -/
def warningName : Bytes := str "Warning"
/-- The deployed RFC 7234 §5.5.6 warn-code 214 value. -/
def warn214Val : Bytes := str "214 - \"Transformation Applied\""

/-- **`warningProg`** — the deployed `WarningTransform.warningStage`, in the DSL. Its
decision is the deployed `isTransformed hs && !hasWarning hs`, passed as one guard. -/
def warningProg (Q : List (Bytes × Bytes) → Bool) : StageProg :=
  stampProg (fun c => Q c.base.headers) warningName warn214Val

/-- **`denote_warning`** — pinned to the deployed `warningStage.onResponse` (`stampWarn
hs = if isTransformed hs && !hasWarning hs then hs ++ [(warningName, warn214Val)] else hs`,
i.e. `stampField` at `Q := fun hs => isTransformed hs && !hasWarning hs`). -/
theorem denote_warning (Q : List (Bytes × Bytes) → Bool) (ctx : Ctx) (b : ResponseBuilder)
    (hb : b.acc = ctx.base) :
    denote (warningProg Q) ctx
      = (b.mapResp (fun r => { r with headers := stampField Q warningName warn214Val r.headers })).build :=
  denote_stampField Q warningName warn214Val ctx b hb

/-- `Link` field name / the deployed preload value. -/
def linkName : Bytes := str "Link"
/-- The deployed preload link value. -/
def linkVal : Bytes := str "</style.css>; rel=preload; as=style"

/-- **`linkProg`** — the deployed `LinkPreload.linkStage`, in the DSL. Its decision is
status-keyed (`stampLink status hs = if status == 200 && !hasLink hs then …`), so it
enters through the LIFT's full `P : Ctx → Response → Bool` — the status is read off the
response cell, not the header list. -/
def linkProg (P : Ctx → Response → Bool) : StageProg :=
  stampProg (fun c => P c c.base) linkName linkVal

/-- **`denote_link`** — pinned to the deployed `linkStage.onResponse` (`b.mapResp (fun r
=> { r with headers := stampLink r.status r.headers })`, expressed as the generic stamp
at the status-keyed decision `P c r = (r.status == 200 && !hasLink r.headers)`). -/
theorem denote_link (P : Ctx → Response → Bool) (ctx : Ctx) (b : ResponseBuilder)
    (hb : b.acc = ctx.base) :
    denote (linkProg P) ctx
      = ((stampStage "linkpreload" P linkName (fun _ _ => linkVal)).onResponse ctx b).build :=
  denote_stampProg "linkpreload" P linkName (fun _ _ => linkVal) linkVal ctx b hb rfl

/-- `Cache-Status` field name (deployed `CacheStatus.csName`). -/
def csName : Bytes := str "Cache-Status"

/-- **`csProg`** — the deployed `CacheStatus.csStage`, in the DSL. `stampCS hs = if hasCS
hs then hs else hs ++ [(csName, if isHit hs then hitVal else missVal)]` — an
unless-present append whose VALUE is computed from the header list, so it enters through
the LIFT's `valOf`. -/
def csProg (hasCS : List (Bytes × Bytes) → Bool) (val : Bytes) : StageProg :=
  stampProg (fun c => !hasCS c.base.headers) csName val

/-- **`denote_cs`** — pinned to the deployed `csStage.onResponse` at the stage's own
computed value: `hval` says `val` is what the deployed `fun _ r => if isHit r.headers
then hitVal else missVal` yields at this context. -/
theorem denote_cs (hasCS : List (Bytes × Bytes) → Bool) (valOf : Ctx → Response → Bytes)
    (val : Bytes) (ctx : Ctx) (b : ResponseBuilder)
    (hb : b.acc = ctx.base) (hval : valOf ctx ctx.base = val) :
    denote (csProg hasCS val) ctx
      = ((stampStage "cachestatus" (fun _ r => !hasCS r.headers) csName valOf).onResponse ctx b).build :=
  denote_stampProg "cachestatus" (fun _ r => !hasCS r.headers) csName valOf val ctx b hb hval

/-! ### 8.3 The conditional-append family (F2) -/

/-- `Cache-Control` field name / the deployed static-asset value. -/
def cacheControlName : Bytes := str "Cache-Control"
/-- The deployed static-asset freshness value. -/
def cacheControlVal : Bytes := str "public, max-age=3600"

/-- **`cacheControlProg`** — the deployed `CacheControl.cacheControlStage`, in the DSL.
Decision: the deployed `b.acc.status == 200 && isStaticGet c`. -/
def cacheControlProg (P : Ctx → Response → Bool) : StageProg :=
  stampProg (fun c => P c c.base) cacheControlName cacheControlVal

/-- **`denote_cacheControl`** — pinned to the deployed `cacheControlStage.onResponse`
(`fun c b => if b.acc.status == 200 && isStaticGet c then b.addHeader (cacheControlName,
cacheControlVal) else b`). -/
theorem denote_cacheControl (P : Ctx → Response → Bool) (ctx : Ctx) (b : ResponseBuilder)
    (hb : b.acc = ctx.base) :
    denote (cacheControlProg P) ctx
      = ((stampStage "cache-control" P cacheControlName (fun _ _ => cacheControlVal)).onResponse ctx b).build :=
  denote_stampProg "cache-control" P cacheControlName _ cacheControlVal ctx b hb rfl

/-- `Expires` field name / the deployed static-asset value. -/
def expiresName : Bytes := str "Expires"
/-- The deployed `Expires` value. -/
def expiresVal : Bytes := str "Thu, 31 Dec 2026 23:59:59 GMT"

/-- **`assetExpiresProg`** — the deployed `AssetExpires.assetExpiresStage`, in the DSL. -/
def assetExpiresProg (P : Ctx → Response → Bool) : StageProg :=
  stampProg (fun c => P c c.base) expiresName expiresVal

/-- **`denote_assetExpires`** — pinned to the deployed `assetExpiresStage.onResponse`
(same `status == 200 && isStaticGet` decision). -/
theorem denote_assetExpires (P : Ctx → Response → Bool) (ctx : Ctx) (b : ResponseBuilder)
    (hb : b.acc = ctx.base) :
    denote (assetExpiresProg P) ctx
      = ((stampStage "asset-expires" P expiresName (fun _ _ => expiresVal)).onResponse ctx b).build :=
  denote_stampProg "asset-expires" P expiresName _ expiresVal ctx b hb rfl

/-- The deployed immutable-asset field name / value. -/
def immutableName : Bytes := str "Cache-Control"
/-- The deployed immutable-asset value. -/
def immutableVal : Bytes := str "public, max-age=31536000, immutable"

/-- **`assetImmutableProg`** — the deployed `AssetImmutable.assetImmutableStage`. -/
def assetImmutableProg (P : Ctx → Response → Bool) : StageProg :=
  stampProg (fun c => P c c.base) immutableName immutableVal

/-- **`denote_assetImmutable`** — pinned to the deployed `assetImmutableStage.onResponse`. -/
theorem denote_assetImmutable (P : Ctx → Response → Bool) (ctx : Ctx) (b : ResponseBuilder)
    (hb : b.acc = ctx.base) :
    denote (assetImmutableProg P) ctx
      = ((stampStage "asset-immutable" P immutableName (fun _ _ => immutableVal)).onResponse ctx b).build :=
  denote_stampProg "asset-immutable" P immutableName _ immutableVal ctx b hb rfl

/-- `Last-Modified` field name / the deployed value. -/
def lmName : Bytes := str "Last-Modified"
/-- The deployed `Last-Modified` value. -/
def lmVal : Bytes := str "Wed, 01 Jul 2026 00:00:00 GMT"

/-- **`lmStampProg`** — the deployed `ModifiedSince.lmStampStage`, in the DSL. Decision:
the deployed `b.acc.status == 200 && isStaticGet c && !hasLm b.acc.headers` — reads BOTH
the context and the cell, so it enters through the full `P`. -/
def lmStampProg (P : Ctx → Response → Bool) : StageProg :=
  stampProg (fun c => P c c.base) lmName lmVal

/-- **`denote_lmStamp`** — pinned to the deployed `lmStampStage.onResponse`. -/
theorem denote_lmStamp (P : Ctx → Response → Bool) (ctx : Ctx) (b : ResponseBuilder)
    (hb : b.acc = ctx.base) :
    denote (lmStampProg P) ctx
      = ((stampStage "last-modified" P lmName (fun _ _ => lmVal)).onResponse ctx b).build :=
  denote_stampProg "last-modified" P lmName _ lmVal ctx b hb rfl

/-- `Content-Type` field name (deployed `ctName`). -/
def ctName : Bytes := str "Content-Type"
/-- The deployed HTML media type. -/
def htmlVal : Bytes := str "text/html"
/-- The deployed SSE media type. -/
def sseVal : Bytes := str "text/event-stream"

/-- **`dashTypeProg`** — the deployed `Dashboard.dashTypeStage` (`if inScope c then
b.addHeader (ctName, htmlVal) else b`). -/
def dashTypeProg (inScope : Ctx → Bool) : StageProg :=
  stampProg (fun c => inScope c) ctName htmlVal

/-- **`denote_dashType`** — pinned to the deployed `dashTypeStage.onResponse`. -/
theorem denote_dashType (inScope : Ctx → Bool) (ctx : Ctx) (b : ResponseBuilder)
    (hb : b.acc = ctx.base) :
    denote (dashTypeProg inScope) ctx
      = ((stampStage "dashboard-type" (fun c _ => inScope c) ctName (fun _ _ => htmlVal)).onResponse ctx b).build :=
  denote_stampProg "dashboard-type" (fun c _ => inScope c) ctName _ htmlVal ctx b hb rfl

/-- **`spaTypeProg`** — the deployed `SpaServe.spaTypeStage` (`if inScope c then
b.addHeader (ctName, htmlVal) else b`). -/
def spaTypeProg (inScope : Ctx → Bool) : StageProg :=
  stampProg (fun c => inScope c) ctName htmlVal

/-- **`denote_spaType`** — pinned to the deployed `spaTypeStage.onResponse`. -/
theorem denote_spaType (inScope : Ctx → Bool) (ctx : Ctx) (b : ResponseBuilder)
    (hb : b.acc = ctx.base) :
    denote (spaTypeProg inScope) ctx
      = ((stampStage "spa-head" (fun c _ => inScope c) ctName (fun _ _ => htmlVal)).onResponse ctx b).build :=
  denote_stampProg "spa-head" (fun c _ => inScope c) ctName _ htmlVal ctx b hb rfl

/-- **`sseHeadProg`** — the deployed `SseServe.sseHeadStage` (`if inScope c then
b.addHeader (ctName, ctVal) else b`). -/
def sseHeadProg (inScope : Ctx → Bool) : StageProg :=
  stampProg (fun c => inScope c) ctName sseVal

/-- **`denote_sseHead`** — pinned to the deployed `sseHeadStage.onResponse`. -/
theorem denote_sseHead (inScope : Ctx → Bool) (ctx : Ctx) (b : ResponseBuilder)
    (hb : b.acc = ctx.base) :
    denote (sseHeadProg inScope) ctx
      = ((stampStage "sse-head" (fun c _ => inScope c) ctName (fun _ _ => sseVal)).onResponse ctx b).build :=
  denote_stampProg "sse-head" (fun c _ => inScope c) ctName _ sseVal ctx b hb rfl

/-- `Set-Cookie` field name (deployed `setCookieName`). -/
def setCookieName : Bytes := str "Set-Cookie"
/-- The deployed session cookie value. -/
def sessionCookieVal : Bytes := str "sid=1; Path=/"

/-- **`setCookieProg`** — the deployed `SessionCookie.setCookieStage` (`if inScope c then
b.addHeader (setCookieName, weakCookie) else b`). -/
def setCookieProg (inScope : Ctx → Bool) : StageProg :=
  stampProg (fun c => inScope c) setCookieName sessionCookieVal

/-- **`denote_setCookie`** — pinned to the deployed `setCookieStage.onResponse`. -/
theorem denote_setCookie (inScope : Ctx → Bool) (ctx : Ctx) (b : ResponseBuilder)
    (hb : b.acc = ctx.base) :
    denote (setCookieProg inScope) ctx
      = ((stampStage "session-cookie-stamp" (fun c _ => inScope c) setCookieName
            (fun _ _ => sessionCookieVal)).onResponse ctx b).build :=
  denote_stampProg "session-cookie-stamp" (fun c _ => inScope c) setCookieName _
    sessionCookieVal ctx b hb rfl

/-- `Retry-After` field name / the deployed value. -/
def retryAfterName : Bytes := str "Retry-After"
/-- The deployed `Retry-After` value. -/
def retryAfterVal : Bytes := str "120"

/-- **`retryAfterProg`** — the deployed `RetryAfter.retryAfterStage` (`if
needsRetryAfter b.acc.status then b.addHeader … else b`) — a STATUS-keyed decision. -/
def retryAfterProg (P : Ctx → Response → Bool) : StageProg :=
  stampProg (fun c => P c c.base) retryAfterName retryAfterVal

/-- **`denote_retryAfter`** — pinned to the deployed `retryAfterStage.onResponse`. -/
theorem denote_retryAfter (P : Ctx → Response → Bool) (ctx : Ctx) (b : ResponseBuilder)
    (hb : b.acc = ctx.base) :
    denote (retryAfterProg P) ctx
      = ((stampStage "retry-after" P retryAfterName (fun _ _ => retryAfterVal)).onResponse ctx b).build :=
  denote_stampProg "retry-after" P retryAfterName _ retryAfterVal ctx b hb rfl

/-- `Content-Location` field name (deployed `contentLocationName`). -/
def contentLocationName : Bytes := str "Content-Location"

/-- **`contentLocationProg`** — the deployed `ContentLocation.contentLocationStage`
(`if b.acc.status == 200 && isStaticGet c then b.addHeader (contentLocationName,
canonicalResourcePath c.req.target) else b`) — a decision AND a computed value. -/
def contentLocationProg (P : Ctx → Response → Bool) (val : Bytes) : StageProg :=
  stampProg (fun c => P c c.base) contentLocationName val

/-- **`denote_contentLocation`** — pinned to the deployed `contentLocationStage.onResponse`
at the stage's own computed value (`hval`: `val` is what the deployed
`canonicalResourcePath c.req.target` yields at this context). -/
theorem denote_contentLocation (P : Ctx → Response → Bool) (valOf : Ctx → Response → Bytes)
    (val : Bytes) (ctx : Ctx) (b : ResponseBuilder)
    (hb : b.acc = ctx.base) (hval : valOf ctx ctx.base = val) :
    denote (contentLocationProg P val) ctx
      = ((stampStage "content-location" P contentLocationName valOf).onResponse ctx b).build :=
  denote_stampProg "content-location" P contentLocationName valOf val ctx b hb hval

/-- `X-Request-Id` field name (deployed `ridName`). -/
def ridName : Bytes := str "X-Request-Id"

/-- **`ridProg`** — the deployed `RequestId.ridStage`. Its response phase appends on BOTH
branches (`| some p => b.addHeader (ridName, p.2) | none => b.addHeader (ridName, ctxId
c)`) — i.e. an UNCONDITIONAL append whose value is the correlation id chosen by the
attribute lookup, so it enters through the lift at `P := true` and the stage's `valOf`. -/
def ridProg (val : Bytes) : StageProg :=
  stampProg (fun _ => true) ridName val

/-- **`denote_rid`** — pinned to the deployed `ridStage.onResponse` at the stage's own
chosen id (`hval`: `val` is what the deployed attribute lookup yields at this context). -/
theorem denote_rid (valOf : Ctx → Response → Bytes) (val : Bytes) (ctx : Ctx)
    (b : ResponseBuilder) (hb : b.acc = ctx.base) (hval : valOf ctx ctx.base = val) :
    denote (ridProg val) ctx
      = ((stampStage "request-id" (fun _ _ => true) ridName valOf).onResponse ctx b).build :=
  denote_stampProg "request-id" (fun _ _ => true) ridName valOf val ctx b hb hval

/-- `X-Forwarded-For` field name (deployed `ProxyProtocol.xffName`). -/
def xffName : Bytes := str "X-Forwarded-For"

/-- **`proxyProtoProg`** — the deployed `ProxyProtocol.proxyProtoStage` (`match
c.attrs.find? … | some p => b.addHeader (xffName, p.2) | none => b`) — a conditional
append (the recovered client address is present or it is not) with a computed value. -/
def proxyProtoProg (P : Ctx → Response → Bool) (val : Bytes) : StageProg :=
  stampProg (fun c => P c c.base) xffName val

/-- **`denote_proxyProto`** — pinned to the deployed `proxyProtoStage.onResponse`. -/
theorem denote_proxyProto (P : Ctx → Response → Bool) (valOf : Ctx → Response → Bytes)
    (val : Bytes) (ctx : Ctx) (b : ResponseBuilder)
    (hb : b.acc = ctx.base) (hval : valOf ctx ctx.base = val) :
    denote (proxyProtoProg P val) ctx
      = ((stampStage "proxy-protocol" P xffName valOf).onResponse ctx b).build :=
  denote_stampProg "proxy-protocol" P xffName valOf val ctx b hb hval

/-- `Access-Control-Allow-Origin` field name (deployed `acaoName`). -/
def acaoName : Bytes := str "Access-Control-Allow-Origin"

/-- **`corsProg`** — the deployed `Cors.corsStage` / `Deploy.deployCorsStage` (`match
acaoValue policy (originOf c) with | some v => b.addHeader (acaoName, strBytes v) | none
=> b`) — a conditional append with the policy-computed value. -/
def corsProg (P : Ctx → Response → Bool) (val : Bytes) : StageProg :=
  stampProg (fun c => P c c.base) acaoName val

/-- **`denote_cors`** — pinned to the deployed `corsStage.onResponse` at the policy's own
admitted value. -/
theorem denote_cors (P : Ctx → Response → Bool) (valOf : Ctx → Response → Bytes)
    (val : Bytes) (ctx : Ctx) (b : ResponseBuilder)
    (hb : b.acc = ctx.base) (hval : valOf ctx ctx.base = val) :
    denote (corsProg P val) ctx
      = ((stampStage "cors" P acaoName valOf).onResponse ctx b).build :=
  denote_stampProg "cors" P acaoName valOf val ctx b hb hval

/-! ### 8.4 The unconditional family (F1) -/

/-- `Date` field name (deployed `dateName`). -/
def dateName : Bytes := str "Date"

/-- **`dateProg`** — the deployed `DateHeader.dateStage now` (`fun _ b => b.addHeader
(dateName, now)`) — the bare unconditional append. -/
def dateProg (now : Bytes) : StageProg := .addHeader dateName now

/-- **`denote_date`** — pinned to the deployed `dateStage.onResponse`, via the F1 lift. -/
theorem denote_date (now : Bytes) (ctx : Ctx) (b : ResponseBuilder) (hb : b.acc = ctx.base) :
    denote (dateProg now) ctx = ((alwaysStamp "date" dateName now).onResponse ctx b).build :=
  denote_addHeader_stamp "date" dateName now ctx b hb

/-! ### 8.5 The multi-header family -/

/-- **`securityHeadersProg`** — the deployed `SecurityHeaders.securityheadersStage`
(`fun _ b => (wireHeaders policy).foldl ResponseBuilder.addHeader b`) — the WHOLE
rendered policy set, at ANY size, in one DSL term. -/
def securityHeadersProg (wireHeaders : List (Bytes × Bytes)) : StageProg := stampSeq wireHeaders

/-- **`denote_securityHeaders`** — pinned to the deployed `securityheadersStage.onResponse`
for ANY rendered policy set, via the multi-header lift. -/
theorem denote_securityHeaders (wireHeaders : List (Bytes × Bytes)) (ctx : Ctx)
    (b : ResponseBuilder) (hb : b.acc = ctx.base) :
    denote (securityHeadersProg wireHeaders) ctx
      = ((stampSetStage "securityheaders" wireHeaders).onResponse ctx b).build :=
  denote_stampSeq "securityheaders" wireHeaders ctx b hb

/-- `Content-Language` field name (deployed `clHdrName`). -/
def clHdrName : Bytes := str "Content-Language"
/-- The deployed language-negotiation `Vary` value. -/
def langVaryVal : Bytes := str "Accept-Language"

/-- **`langStampProg`** — the deployed `ContentLanguage.langStampStage` (`if inScope c
then (b.addHeader (clHdrName, tagOf (negotiate c.req))).addHeader (varyName, varyVal)
else b`) — a CONDITIONAL PAIR of appends: a `condR` over the two-element `stampSeq`. -/
def langStampProg (inScope : ReqPred) (tag : Bytes) : StageProg :=
  .condR inScope (stampSeq [(clHdrName, tag), (varyName, langVaryVal)]) (.rewriteBody .identity)

/-- **`denote_langStamp` (in scope).** Pinned to the deployed `langStampStage.onResponse`
fire branch — the chained pair of appends, at the negotiated tag (`htag`). One line via
the multi-header lift. -/
theorem denote_langStamp_inScope (inScope : ReqPred) (tagOf : Ctx → Bytes) (tag : Bytes)
    (ctx : Ctx) (b : ResponseBuilder) (hb : b.acc = ctx.base) (hs : inScope ctx = true)
    (htag : tagOf ctx = tag) :
    denote (langStampProg inScope tag) ctx
      = (((b.addHeader (clHdrName, tagOf ctx)).addHeader (varyName, langVaryVal))).build := by
  subst htag
  obtain ⟨acc⟩ := b
  subst hb
  show (if inScope ctx then
          denoteStep ctx (stampSeq [(clHdrName, tagOf ctx), (varyName, langVaryVal)])
            { resp := ctx.base, halted := false }
        else denoteStep ctx (.rewriteBody .identity)
            { resp := ctx.base, halted := false }).resp = _
  rw [if_pos hs, denoteStep_stampSeq ctx [(clHdrName, tagOf ctx), (varyName, langVaryVal)] ctx.base]
  show ({ ctx.base with headers :=
      ctx.base.headers ++ [(clHdrName, tagOf ctx), (varyName, langVaryVal)] } : Response) = _
  show _ = ({ ctx.base with headers :=
      (ctx.base.headers ++ [(clHdrName, tagOf ctx)]) ++ [(varyName, langVaryVal)] } : Response)
  rw [List.append_assoc]
  rfl

/-- **`denote_langStamp` (out of scope).** Off the stage's route the response passes
untouched — the deployed `else b` branch. -/
theorem denote_langStamp_out (inScope : ReqPred) (tag : Bytes) (ctx : Ctx)
    (b : ResponseBuilder) (hb : b.acc = ctx.base) (hs : inScope ctx = false) :
    denote (langStampProg inScope tag) ctx = b.build := by
  obtain ⟨acc⟩ := b
  subst hb
  show (if inScope ctx then
          denoteStep ctx (stampSeq [(clHdrName, tag), (varyName, langVaryVal)])
            { resp := ctx.base, halted := false }
        else denoteStep ctx (.rewriteBody .identity)
            { resp := ctx.base, halted := false }).resp = _
  rw [if_neg (by simp only [hs]; exact Bool.false_ne_true)]
  simp only [denoteStep, Bool.false_eq_true, if_false, runBody]
  rfl

/-! ## 9. THE MISFITS — deployed stages whose response phase is NOT a header append

These are listed, not forced. Each one's `onResponse` does something the `addHeader`
shape cannot express, so each genuinely needs its own treatment (a different shape
lemma, or the DSL's `rewriteBody`/`gate`):

 * `CookieSecure.cookieSecureStage` — `b.mapResp (fun r => { r with headers :=
   r.headers.map hardenHeader })`. A per-header MAP over the existing list (rewriting
   every `Set-Cookie` in place), not an append. Needs a MAP shape lemma.
 * `Header.headerStage` — `b.mapResp rewriteResp`: a header-map PROGRAM (strip
   hop-by-hop + set several fields). A multi-op rewrite, not one append.
 * `HtmlRewrite.htmlrewriteStage` — `b.mapResp gatedHtmlTransformResp`: a BODY
   transform. The DSL's `rewriteBody`, not `addHeader`.
 * `Gzip.gzipStage` / `CompressExt.compressStage` — `(b.mapResp gzipBody).addHeader
   (ceName, gzipVal)`: a body transform AND an append. A COMPOSITE (`seq` of
   `rewriteBody` and `addHeader`); the append half lifts, the body half does not.
 * `StaleWhileRevalidate.swrStage` — `b.mapResp applyCc`: rewrites an EXISTING
   `Cache-Control` value in place rather than appending a field.
 * `ConditionalRequest.conditionalStage`, `MultiRange.multiRangeStage`,
   `DateCondition.dateCondStage`, `ErrorPage.errorStage`, `RangeUnveil.rangeUnveilStage`,
   `DateHeader.headStripStage` — whole-response rewrites (status + body + headers
   together), not stamps.
 * The ~36 pure GATE stages (`MethodFilter`, `IpFilter`, `Rate`, `Jwt`, `BasicAuth`,
   `BodyLimit`, `ConnLimit`, `Slowloris`, `Redirect`, …) all have `onResponse := fun _ b
   => b` — their content is entirely in `onRequest`. That is the `gate` shape, a
   separate lift (not this file).

## 10. Non-vacuity — the lift genuinely computes, both branches

Concrete instantiations: the shape theorems' right-hand sides run the REAL deployed
builder ops, so they compute concrete header lists. A `P → P` tautology could not. -/

/-- A `200 OK` base with body `hi` and no headers. -/
def baseOk : Response := ok200 (str "hi")
/-- A 0-header context. -/
def ctx0 : Ctx := { req := {}, base := baseOk }
/-- The cell arriving at a stage, seeded from `ctx0`'s base. -/
def b0 : ResponseBuilder := ResponseBuilder.ofResponse ctx0.base

-- the F1 lift's RHS genuinely appends (0 → 1 headers), and carries the real bytes:
#guard ((alwaysStamp "date" dateName (str "Wed, 01 Jul 2026 00:00:00 GMT")).onResponse ctx0 b0).build.headers.length = 1
#guard ((alwaysStamp "date" dateName (str "Wed, 01 Jul 2026 00:00:00 GMT")).onResponse ctx0 b0).build.headers
        = [(dateName, str "Wed, 01 Jul 2026 00:00:00 GMT")]
#guard (denote (dateProg (str "Wed, 01 Jul 2026 00:00:00 GMT")) ctx0).headers.length = 1

-- THE LIFT's decision genuinely drives BOTH branches (fire appends, pass does not):
#guard (denote (altProg (fun _ => false)) ctx0).headers = [(altName, altVal)]
#guard (denote (altProg (fun _ => true))  ctx0).headers = []
#guard (denote (dashTypeProg (fun _ => true))  ctx0).headers = [(ctName, htmlVal)]
#guard (denote (dashTypeProg (fun _ => false)) ctx0).headers = []

-- the deployed `mapResp`+`stampUnless` RHS computes the SAME concrete list (the bridge
-- is not vacuous — both surfaces land the real bytes):
#guard (b0.mapResp (fun r => { r with headers := stampUnless (fun _ => false) altName altVal r.headers })).build.headers
        = [(altName, altVal)]
#guard (b0.mapResp (fun r => { r with headers := stampUnless (fun _ => true) altName altVal r.headers })).build.headers
        = []

-- the exclusion wrapper genuinely excludes:
#guard (denote (varyGate8Prog (fun _ => true)  (fun _ => false)) ctx0).headers = []
#guard (denote (varyGate8Prog (fun _ => false) (fun _ => false)) ctx0).headers = [(varyName, varyVal)]

-- the multi-header lift genuinely appends a whole set, in order, at ANY size:
#guard (denote (securityHeadersProg [(str "A", str "1"), (str "B", str "2"), (str "C", str "3")]) ctx0).headers
        = [(str "A", str "1"), (str "B", str "2"), (str "C", str "3")]
#guard ((stampSetStage "securityheaders" [(str "A", str "1"), (str "B", str "2")]).onResponse ctx0 b0).build.headers
        = [(str "A", str "1"), (str "B", str "2")]
#guard (denote (securityHeadersProg []) ctx0).headers = []

-- the lang pair genuinely stamps two fields on its route and nothing off it:
#guard (denote (langStampProg (fun _ => true) (str "en")) ctx0).headers
        = [(clHdrName, str "en"), (varyName, langVaryVal)]
#guard (denote (langStampProg (fun _ => false) (str "en")) ctx0).headers = []

-- distinct stages produce distinct wire responses (the stamps are not interchangeable):
#guard serialize (denote (altProg (fun _ => false)) ctx0) ≠ serialize baseOk
#guard serialize (denote (altProg (fun _ => false)) ctx0)
        ≠ serialize (denote (ppProg (fun _ => false)) ctx0)
#guard serialize (denote (viaProg (fun _ => false)) ctx0)
        ≠ serialize (denote (taoProg (fun _ => false)) ctx0)

/-! ## 11. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms denote_addHeader_stamp
#print axioms denote_stampProg
#print axioms mapResp_stampUnless_eq
#print axioms mapResp_stampField_eq
#print axioms denote_stampUnless
#print axioms denote_stampField
#print axioms denote_stampExcluded
#print axioms build_addHeaders
#print axioms denoteStep_stampSeq
#print axioms denote_stampSeq

#print axioms denote_alt
#print axioms denote_pp
#print axioms denote_corp
#print axioms denote_tao
#print axioms denote_via
#print axioms denote_vary
#print axioms denote_varyGate8
#print axioms denote_warning
#print axioms denote_link
#print axioms denote_cs
#print axioms denote_cacheControl
#print axioms denote_assetExpires
#print axioms denote_assetImmutable
#print axioms denote_lmStamp
#print axioms denote_dashType
#print axioms denote_spaType
#print axioms denote_sseHead
#print axioms denote_setCookie
#print axioms denote_retryAfter
#print axioms denote_contentLocation
#print axioms denote_rid
#print axioms denote_proxyProto
#print axioms denote_cors
#print axioms denote_date
#print axioms denote_securityHeaders
#print axioms denote_langStamp_inScope
#print axioms denote_langStamp_out

end Pancake.StageLiftHeader
