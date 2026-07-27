/-
  Pancake/StageProg2.lean — THE TWO-PHASE ONION DSL (the StageProg redesign).

  WHY. The deployed drorb serve (`Reactor.Pipeline.runPipeline`) is a TWO-PHASE
  ONION over a `List Stage`: each stage has an `onRequest` phase (walked
  outer→inner; a gate may short-circuit with a refusal response) and an
  `onResponse` phase (walked inner→outer over the result). Critically, when a
  gate short-circuits the request phase, the OTHER stages' response phases STILL
  RUN over the refusal (`runResp rest` over the seeded refusal + the passed outer
  stages' `onResponse` wraps) — a 405/403 still carries the security headers.
  The old flat `StageProg` (StageProg.lean) linearizes this into ONE op sequence
  with an absorbing `halted` flag, so a fired gate ABSORBS every later op — the
  deployed whole-chain semantics is NOT EXPRESSIBLE there (and its gate also
  KEPT the base response's body, where the deployed `.respond r` replaces it).

  THE REDESIGN — three moves:

  (1) SPLIT THE GATE OUT OF THE RESPONSE ALGEBRA. `RespProg` is the gate-FREE
      response-transform algebra (what a deployed `onResponse` / a refusal
      builder does): `addHeader / setStatus / rewriteBody / seq / condR / skip`.
      With no gate inside it, its denotation `denoteR : RespProg → Response →
      Response` is a plain fold — NO halted flag anywhere.

  (2) A STAGE IS A GUARD + TWO PHASE PROGRAMS. `StageSpec = { guard : ReqPred,
      refusal : RespProg, onResp : RespProg }` — the deployed
      `onRequest`'s decision (gate or pass) as `guard`+`refusal` (the refusal
      built over a FRESH `blankResp`, matching the deployed `.respond r`), and
      the deployed `onResponse` as `onResp`.

  (3) THE PIPELINE IS THE REAL ONION FOLD. `runChain` transliterates the deployed
      `runPipeline` (with drorb's affine `ResponseBuilder` erased through its own
      faithfulness theorems `build_*`):

        runChain ctx h []          = h ctx
        runChain ctx h (s :: rest) =
          if s.guard ctx then respFold ctx rest (denoteR ctx s.refusal blankResp)
          else denoteR ctx s.onResp (runChain ctx h rest)

      `respFold` is drorb's `runResp` (the response-only inner onion). The five
      drorb composition laws (`pipeline_empty/cons/gate_short_circuits/
      stage_effect/onion_order`) hold verbatim (§3).

  THE KEYSTONE (§4, `runChain_gate_keystone`) — the theorem the flat DSL could
  not even STATE: for ANY passed prefix `pre`, ANY firing gate `g`, ANY inner
  tail `rest`, ANY handler:

        runChain ctx h (pre ++ g :: rest)
          = respFold ctx (pre ++ rest) (denoteR ctx g.refusal blankResp)

  i.e. a fired gate erases the HANDLER and every inner REQUEST phase, yet EVERY
  other stage's RESPONSE phase (the passed outer `pre` AND the skipped inner
  `rest`) still runs over the refusal. Corollaries: handler-irrelevance under a
  fire, and the concrete witness `secHeaders_on_refusal` — a 405 refusal that
  genuinely carries an outer stage's security headers (the exact semantics the
  flat DSL's absorbing gate destroys; see the OLD-vs-NEW `#guard` contrast, §4.3).

  THE COMPILER (§5–§6) — `compile2`'s per-constructor induction EXTENDS:
   * `compileR` lowers `RespProg` per constructor exactly as StageCompile's
     `compile2` lowers the flat ops — but with NO halt guard (there is no halt
     flag to guard on: gate-freeness of the algebra deleted it). Three word
     slots (`Enc3`: status / header-count / body-length) instead of four.
   * `compileChain` lowers the ONION: a fired guard's short-circuit is the
     `.cond` BRANCH STRUCTURE itself — the fire arm emits the refusal + the
     inner stages' response fragments; the pass arm emits the inner chain then
     this stage's response fragment (the onion wrap as instruction order).
     The absorbing flag the flat compiler needed is gone: CONTROL FLOW is the
     short-circuit.
   * `compileR_correct` (structural induction on `RespProg`) and
     `compileChain_correct` (structural induction on the stage list,
     parametrized over a proven handler fragment) close the simulation:
     the machine slots land `Enc3 st' (runChain ctx handler stages)`.
   * `compileChain_gate_keystone` is the machine-level keystone: gate fires ⇒
     the slots hold the refusal-with-all-other-response-phases image.

  RESIDUALS (named, not hidden):
   * `Enc3` tracks the SCALAR skeleton (status, |headers|, |body|) — same
     residual as StageCompile: byte materialization is the SerializeHeaders
     `segWhile` / `copyWhile` assembly step, unchanged by this redesign.
   * Response-predicated conditionals: DONE — folded in as `condResp` (the general
     response-decided branch, §1) + `condStatus` (the status-keyed slice). The
     general branch DENOTES but does not compile (the header LIST is not in `Enc3`,
     only its count) — `Compilable` (§5) excludes it, so nothing false is claimed.
     The status-keyed slice DOES compile, to one `.cond` on the `aStat` cell, exact
     under a `status < 2^64` invariant threaded through `Enc3` (§5.1,
     `compileR_condStatus_correct`). The remaining response-decided residual is the
     HEADER-LIST-reading decisions (`!hasX r.headers`), which need a machine-side
     header representation — a separate, larger piece, deliberately not smuggled in
     here.
   * Context TRANSFORMS (`.continue c'` with `c' ≠ c` — the attr-stashing
     stages) are not modelled: `ctx` is fixed through the walk. Extension =
     a third phase algebra writing attr slots (doc §5).
   * Request-byte-dependent response BYTES (CORS echo) need a byte-copy
     constructor; the scalar skeleton carries only lengths today (doc §5).
   * The refusal is built over the fixed `blankResp` — refusals whose bytes
     depend on ctx beyond predicate branching share the CORS-echo residual.

  Own file; imports the existing chain, edits nothing.
  Axiom audit at the end: expect ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Pancake.StageCompile

namespace Pancake.StageOnion

open Pancake Pancake.SerializeCompile Pancake.StageProg Pancake.StageCompile
open Pancake.EmitCorrect (sem_seq_none)
open Pancake.EmitCorrectCompose (sem_cond)
open Pancake.StructModel (wordAt eval_loadWord_of_wordAt eval_op_add eval_var)

variable {σ : Type}

/-! ## 1. `RespProg` — the gate-free response-transform algebra

What a deployed `onResponse` (or a gate's refusal builder) does. NO gate
constructor — that is the whole point: the short-circuit lives in the PIPELINE
structure (§2), not in the op stream, so no `halted` flag exists. -/

/-- The response-phase ops: the flat DSL's transform vocabulary
(`addHeader`/`setStatus`/`rewriteBody`/`seq`/`condR`), plus `skip`, MINUS `gate`,
PLUS the two response-decided branches folded in from the `condResp` prototype:

* `condResp (c : Ctx → Response → Bool)` — the GENERAL response-decided branch. Its
  decision reads the ARRIVING response `r` (the inner onion's result), which `condR`'s
  `ReqPred = Ctx → Bool` cannot see. This is what makes the status/header-keyed stamps
  (`r.status == 200`, `!hasX r.headers`, `isTransformed r.headers`) EXPRESSIBLE. It
  DENOTES (a plain fold, §denoteR) but the general form does NOT compile — the header
  list is not in `Enc3` (only its count) — so `compileR` maps it to a `.skip`
  placeholder and the machine-correctness theorems EXCLUDE it (`Compilable`, §5). A
  proven "no" on the compile side, not a false pin.
* `condStatus (k : Nat)` — the STATUS-KEYED specialization (the `condResp` instance keyed
  on `r.status = k`). This one DOES compile: to ONE `.cond` comparing the live status
  cell (`aStat`) to `k`, exact under a `status < 2^64` well-formedness invariant
  (§5.1, `compileR_condStatus_correct`). It is the tractable slice — the status IS in
  `Enc3`, so the machine can read it. -/
inductive RespProg
  | skip
  | addHeader   (name val : Bytes)
  | setStatus   (code : Nat) (reason : Bytes)
  | rewriteBody (t : BodyLoop)
  | seq         (a b : RespProg)
  | condR       (c : ReqPred) (a b : RespProg)
  | condResp    (c : Ctx → Response → Bool) (a b : RespProg)
  | condStatus  (k : Nat) (a b : RespProg)

/-- The response-transform denotation: a PLAIN fold over `Response` — no
short-circuit state. Mirrors the deployed `onResponse` acting on the built
response (drorb's `build_addHeader`/`build_setStatus`/… faithfulness equations
erase the affine builder to exactly these functional updates). -/
def denoteR (ctx : Ctx) : RespProg → Response → Response
  | .skip, r => r
  | .addHeader n v, r => { r with headers := r.headers ++ [(n, v)] }
  | .setStatus code reason, r => { r with status := code, reason := reason }
  | .rewriteBody t, r => { r with body := runBody t r.body }
  | .seq a b, r => denoteR ctx b (denoteR ctx a r)
  | .condR c a b, r => if c ctx then denoteR ctx a r else denoteR ctx b r
  -- the GENERAL response-decided branch: the decision reads the ARRIVING `r` (the
  -- inner onion result), never `ctx.base` — the whole content of the extension. Still
  -- a plain fold: no `halted` flag, no gate, so `runChain`/`respFold` are untouched.
  | .condResp c a b, r => if c ctx r then denoteR ctx a r else denoteR ctx b r
  -- the STATUS-KEYED slice: `condResp` instance keyed on `r.status = k` (the compilable one).
  | .condStatus k a b, r => if r.status = k then denoteR ctx a r else denoteR ctx b r

/-! ## 2. `StageSpec` + the onion fold — the deployed two-phase pipeline -/

/-- **A two-phase stage** — the deep embedding of a deployed `Reactor.Pipeline.Stage`:
* `guard`   — the `onRequest` gate decision (`true` ⇒ `.respond`, the short-circuit);
* `refusal` — the short-circuit response, BUILT OVER `blankResp` (the deployed
  `.respond r` hands back a FRESH response, not a mutation of the base — the old
  flat gate got this wrong by keeping the base body);
* `onResp`  — the `onResponse` response transform.
A pure transform stage has `guard := fun _ => false`. -/
structure StageSpec where
  guard   : ReqPred
  refusal : RespProg
  onResp  : RespProg

/-- The blank seed a refusal is built over (a bare `200 OK`, no headers, no
body — every real refusal overwrites the status line). -/
def blankResp : Response := { status := 200, reason := str "OK", headers := [], body := [] }

/-- **The response-only fold** — drorb's `runResp`, builder-erased: thread the
response back OUTWARD through the stages' `onResp` phases in reverse list order
(head outermost, applied last). This is what runs over a gate's refusal. -/
def respFold (ctx : Ctx) : List StageSpec → Response → Response
  | [], r => r
  | s :: rest, r => denoteR ctx s.onResp (respFold ctx rest r)

/-- **THE ONION FOLD** — drorb's `runPipeline`, builder-erased (its shape is the
transliteration of `Reactor.Pipeline.runPipeline` through the `build_*`
faithfulness equations):
* no stages: the handler answers;
* a FIRING stage: seed the refusal and run the INNER stages' response phases
  over it (`respFold rest`) — the handler and every inner REQUEST phase are
  skipped, but the response onion still runs (a refusal carries the transform
  headers). The passed OUTER stages' `onResp`s then wrap via the recursion.
* a PASSING stage: run the inner pipeline, then wrap with this stage's
  `onResp` (the onion: outermost sees the response last). -/
def runChain (ctx : Ctx) (handler : Ctx → Response) : List StageSpec → Response
  | [] => handler ctx
  | s :: rest =>
    if s.guard ctx then respFold ctx rest (denoteR ctx s.refusal blankResp)
    else denoteR ctx s.onResp (runChain ctx handler rest)

/-! ## 3. The composition calculus — drorb's five pipeline laws, verbatim

These are `Reactor.Pipeline`'s `pipeline_empty` / `pipeline_cons` /
`pipeline_gate_short_circuits` / `pipeline_stage_effect` / `pipeline_onion_order`,
restated 1:1 on the deep embedding (the shape witness that `runChain` IS the
deployed fold). -/

/-- drorb `pipeline_empty`: no stages, the bare handler. -/
theorem runChain_nil (ctx : Ctx) (h : Ctx → Response) : runChain ctx h [] = h ctx := rfl

/-- drorb `pipeline_cons`: the defining head/tail factoring. -/
theorem runChain_cons (ctx : Ctx) (h : Ctx → Response) (s : StageSpec) (rest : List StageSpec) :
    runChain ctx h (s :: rest)
      = if s.guard ctx then respFold ctx rest (denoteR ctx s.refusal blankResp)
        else denoteR ctx s.onResp (runChain ctx h rest) := rfl

/-- drorb `runResp_cons`: the outer stage's response phase wraps the inner fold. -/
theorem respFold_cons (ctx : Ctx) (s : StageSpec) (rest : List StageSpec) (r : Response) :
    respFold ctx (s :: rest) r = denoteR ctx s.onResp (respFold ctx rest r) := rfl

/-- drorb `pipeline_gate_short_circuits`: a fired gate seeds its refusal and the
INNER stages' response phases run over it — handler skipped, onion kept. -/
theorem runChain_gate_short_circuits (ctx : Ctx) (h : Ctx → Response)
    (s : StageSpec) (rest : List StageSpec) (hg : s.guard ctx = true) :
    runChain ctx h (s :: rest) = respFold ctx rest (denoteR ctx s.refusal blankResp) := by
  rw [runChain_cons, hg, if_pos rfl]

/-- drorb `pipeline_stage_effect`: a passing stage's `onResp` wraps the tail —
THE hook a per-stage byte-effect theorem instantiates. -/
theorem runChain_stage_effect (ctx : Ctx) (h : Ctx → Response)
    (s : StageSpec) (rest : List StageSpec) (hs : s.guard ctx = false) :
    runChain ctx h (s :: rest) = denoteR ctx s.onResp (runChain ctx h rest) := by
  rw [runChain_cons, hs, if_neg (show ¬ ((false : Bool) = true) by decide)]

/-- drorb `pipeline_onion_order`: with two passing stages the response phase runs
in the exact REVERSE of the request phase (s₂ inner first, s₁ outer last). -/
theorem runChain_onion_order (ctx : Ctx) (h : Ctx → Response) (s₁ s₂ : StageSpec)
    (h1 : s₁.guard ctx = false) (h2 : s₂.guard ctx = false) :
    runChain ctx h [s₁, s₂]
      = denoteR ctx s₁.onResp (denoteR ctx s₂.onResp (h ctx)) := by
  rw [runChain_stage_effect ctx h s₁ [s₂] h1, runChain_stage_effect ctx h s₂ [] h2,
      runChain_nil]

/-! ## 4. THE KEYSTONE — the whole-chain gate law the flat DSL cannot state -/

/-- `respFold` splits over append (the outer prefix wraps the inner fold). -/
theorem respFold_append (ctx : Ctx) (xs ys : List StageSpec) (r : Response) :
    respFold ctx (xs ++ ys) r = respFold ctx xs (respFold ctx ys r) := by
  induction xs with
  | nil => rfl
  | cons s ss ih =>
    show denoteR ctx s.onResp (respFold ctx (ss ++ ys) r)
      = denoteR ctx s.onResp (respFold ctx ss (respFold ctx ys r))
    rw [ih]

/-- **THE KEYSTONE — `runChain_gate_keystone`.** For ANY passed outer prefix
`pre` (every guard `false`), ANY firing gate `g`, ANY inner tail `rest`, and ANY
handler: the whole serve is the response onion of ALL OTHER stages — the passed
`pre` AND the skipped `rest` — folded over the gate's refusal. The handler is
GONE from the right-hand side (it provably never ran), every inner REQUEST phase
is gone, yet every RESPONSE phase still fires over the refusal.

This is exactly the deployed short-circuit semantics (`runResp rest` over the
seeded refusal, wrapped by the passed stages' `onResponse`s) — the semantics the
flat DSL's absorbing `halted` flag destroys (there, a fired gate makes every
later op a no-op, and no earlier op can run "after" it at all). -/
theorem runChain_gate_keystone (ctx : Ctx) (handler : Ctx → Response)
    (pre : List StageSpec) (g : StageSpec) (rest : List StageSpec)
    (hpre : ∀ s ∈ pre, s.guard ctx = false) (hg : g.guard ctx = true) :
    runChain ctx handler (pre ++ g :: rest)
      = respFold ctx (pre ++ rest) (denoteR ctx g.refusal blankResp) := by
  induction pre with
  | nil =>
    show runChain ctx handler (g :: rest) = respFold ctx rest (denoteR ctx g.refusal blankResp)
    exact runChain_gate_short_circuits ctx handler g rest hg
  | cons s ss ih =>
    have hs : s.guard ctx = false := hpre s (by simp)
    have hss : ∀ t ∈ ss, t.guard ctx = false := fun t ht => hpre t (by simp [ht])
    show runChain ctx handler (s :: (ss ++ g :: rest))
      = denoteR ctx s.onResp (respFold ctx (ss ++ rest) (denoteR ctx g.refusal blankResp))
    rw [runChain_stage_effect ctx handler s _ hs, ih hss]

/-- **Handler-irrelevance under a fire.** When a gate fires anywhere along a
passed prefix, swapping the handler changes NOTHING — the machine-checked form
of "the handler never ran", now through a whole passed prefix (the flat DSL's
`pipeline_gate_ignores_handler` only had the head-gate case; here the gate sits
at arbitrary depth). -/
theorem runChain_gate_ignores_handler (ctx : Ctx) (h h' : Ctx → Response)
    (pre : List StageSpec) (g : StageSpec) (rest : List StageSpec)
    (hpre : ∀ s ∈ pre, s.guard ctx = false) (hg : g.guard ctx = true) :
    runChain ctx h (pre ++ g :: rest) = runChain ctx h' (pre ++ g :: rest) := by
  rw [runChain_gate_keystone ctx h pre g rest hpre hg,
      runChain_gate_keystone ctx h' pre g rest hpre hg]

/-! ### 4.2 The concrete witness — security headers on a 405 refusal -/

/-- The security-header TRANSFORM stage (always passes; response phase pushes
the two deployed security headers — `securityheadersStage`'s shape). -/
def secStage : StageSpec :=
  { guard := fun _ => false, refusal := .skip,
    onResp := .seq (.addHeader xfoName xfoVal) (.addHeader noSniffName noSniffVal) }

/-- The 405 reason phrase. -/
def mnaReason : Bytes := str "Method Not Allowed"

/-- The method-filter GATE stage (fires on a disallowed method; refusal = a fresh
405 — `methodFilter`'s decision, now with the deployed fresh-response semantics). -/
def gate405 : StageSpec :=
  { guard := fun ctx => ! isAllowed ctx.req.method,
    refusal := .setStatus 405 mnaReason, onResp := .skip }

/-- **`secHeaders_on_refusal` — the two-phase semantics, witnessed.** With the
security-header stage OUTSIDE the method gate, a disallowed method's 405 refusal
still carries both security headers — for ANY handler (which never runs). The
flat DSL cannot produce this response at all: its fired gate absorbs the header
pushes (see the `#guard` contrast below). -/
theorem secHeaders_on_refusal (handler : Ctx → Response) (ctx : Ctx)
    (h : isAllowed ctx.req.method = false) :
    runChain ctx handler [secStage, gate405]
      = { status := 405, reason := mnaReason,
          headers := [(xfoName, xfoVal), (noSniffName, noSniffVal)], body := [] } := by
  have hg : gate405.guard ctx = true := by
    show (! isAllowed ctx.req.method) = true
    rw [h]; rfl
  have hpre : ∀ s ∈ [secStage], s.guard ctx = false := by
    intro s hs
    simp at hs
    rw [hs]; rfl
  rw [show ([secStage, gate405] : List StageSpec) = [secStage] ++ gate405 :: [] from rfl,
      runChain_gate_keystone ctx handler [secStage] gate405 [] hpre hg]
  rfl

/-! ### 4.3 Non-vacuity + the OLD-vs-NEW semantic contrast

The SAME serve intent — "method gate + security headers" — under the flat DSL's
absorbing gate versus the onion. The old fold DROPS the headers from the
refusal; the onion carries them. This is the whole-serve semantics the redesign
makes expressible. -/

-- OLD flat DSL: gate fires, the later header ops are ABSORBED — the 405 goes out bare:
#guard (StageProg.denote (.seq methodFilter securityHeaders) ctxPost).headers = []
-- NEW onion: the SAME 405 refusal carries both security headers (outer-transform form):
#guard (runChain ctxPost (fun _ => baseOk) [secStage, gate405]).headers
        = [(xfoName, xfoVal), (noSniffName, noSniffVal)]
#guard (runChain ctxPost (fun _ => baseOk) [secStage, gate405]).status = 405
-- and in the DEPLOYED order too (gate OUTER, security-headers INNER — `runResp rest`):
#guard (runChain ctxPost (fun _ => baseOk) [gate405, secStage]).headers
        = [(xfoName, xfoVal), (noSniffName, noSniffVal)]
-- the refusal is FRESH (deployed `.respond r`): no base body leaks into the 405
-- (the old flat gate kept the 2-byte base body — a fidelity bug, fixed here):
#guard (runChain ctxPost (fun _ => baseOk) [secStage, gate405]).body = []
#guard (StageProg.denote methodFilter ctxPost).body.length = 2
-- an allowed method passes: the handler answers, wrapped by the onion:
#guard (runChain ctxGet (fun c => c.base) [secStage, gate405]).status = 200
#guard (runChain ctxGet (fun c => c.base) [secStage, gate405]).headers
        = [(xfoName, xfoVal), (noSniffName, noSniffVal)]
-- and the handler genuinely matters when no gate fires:
#guard (runChain ctxGet (fun _ => ok200 (str "AAAA")) [secStage, gate405]).body.length = 4

/-! ## 5. `compileR` — the per-constructor lowering, halt-guard-free

`compile2`'s per-constructor scheme extends verbatim; gate-freeness DELETES the
halt guard and the fourth slot. Three word slots (`Enc3`): status, header count,
body length. -/

/-- The three slot addresses are pairwise distinct. -/
def Distinct3 (aStat aCnt aBody : Word) : Prop :=
  aStat ≠ aCnt ∧ aStat ≠ aBody ∧ aCnt ≠ aBody

/-- `Enc3 aStat aCnt aBody st r`: the three word slots hold `r`'s scalar skeleton
(status / header count / body length, as `ofNat 64` words). -/
def Enc3 (aStat aCnt aBody : Word) (st : PancakeState σ) (r : Response) : Prop :=
  wordAt st aStat (BitVec.ofNat 64 r.status) ∧
  wordAt st aCnt  (BitVec.ofNat 64 r.headers.length) ∧
  wordAt st aBody (BitVec.ofNat 64 r.body.length)

/-- **`compileR` — the per-constructor `RespProg` lowering.** Each constructor
emits its own fragment, UNGUARDED (no halt flag exists to guard on); the
request predicates are the same pre-decided boolean locals `compile2` uses. -/
def compileR (nm : ReqPred → String) (aStat aCnt aBody : Word) : RespProg → PancakeProg
  | .skip => .skip
  | .addHeader _ _ =>
      .store (.const aCnt) (.op .add (.loadWord (.const aCnt)) (.const (BitVec.ofNat 64 1)))
  | .setStatus code _ => stC aStat (BitVec.ofNat 64 code)
  | .rewriteBody .identity => .skip
  | .rewriteBody (.replace r) => stC aBody (BitVec.ofNat 64 r.length)
  | .rewriteBody (.append e) =>
      .store (.const aBody) (.op .add (.loadWord (.const aBody)) (.const (BitVec.ofNat 64 e.length)))
  | .seq a b => .seq (compileR nm aStat aCnt aBody a) (compileR nm aStat aCnt aBody b)
  | .condR c a b =>
      .cond (.var (nm c)) (compileR nm aStat aCnt aBody a) (compileR nm aStat aCnt aBody b)
  -- STATUS-KEYED branch: ONE comparison against the live status cell `aStat`. Exact
  -- under a `status < 2^64` invariant (`compileR_condStatus_correct`, §5.1).
  | .condStatus k a b =>
      .cond (.cmp .equal (.loadWord (.const aStat)) (.const (BitVec.ofNat 64 k)))
        (compileR nm aStat aCnt aBody a) (compileR nm aStat aCnt aBody b)
  -- GENERAL response-decided branch: no faithful lowering (the header list is not in
  -- `Enc3`). Placeholder `.skip`, NEVER certified — `Compilable` (§5) excludes it, so
  -- no machine-correctness theorem ever claims anything false about it.
  | .condResp _ _ _ => .skip

/-- Sequencing two clock-preserving, non-failing runs (the `sem_seq_none` clock
clamp discharged once, for every composition below). -/
theorem sem_seq_frames (o : Oracle σ) {c1 c2 : PancakeProg} {st st1 st2 : PancakeState σ}
    (h1 : PancakeSem o c1 st = (none, st1)) (hclk : st1.clock = st.clock)
    (h2 : PancakeSem o c2 st1 = (none, st2)) :
    PancakeSem o (.seq c1 c2) st = (none, st2) := by
  rw [sem_seq_none h1]
  have hcl : ({ st1 with clock := min st.clock st1.clock } : PancakeState σ) = st1 := by
    rw [hclk, Nat.min_self, ← hclk]
  rw [hcl]; exact h2

/-- **The fragment `compileR_correct` certifies.** Everything EXCEPT the two
response-decided branches: `setStatus` is INCLUDED (refusals overwrite the status
line, and this case never reads the status back), `seq`/`condR` are conjunctive; the
two folded-in branches are EXCLUDED — `condResp` has no faithful lowering (its
placeholder `.skip` is never certified), and `condStatus` compiles but its comparison
needs the `status < 2^64` invariant, certified SEPARATELY (§5.1). Every deployed stage
program (refusals, ctx-decided stamps' `onResp`) is `Compilable`; only the new
response-decided stamps are not — the honest boundary of the scalar-skeleton machine. -/
def Compilable : RespProg → Prop
  | .skip => True
  | .addHeader _ _ => True
  | .setStatus _ _ => True
  | .rewriteBody _ => True
  | .seq a b => Compilable a ∧ Compilable b
  | .condR _ a b => Compilable a ∧ Compilable b
  | .condResp _ _ _ => False
  | .condStatus _ _ _ => False

/-- **`compileR_correct` — structural induction on `RespProg`.** For a `Compilable`
program, from any state encoding `r` (`Enc3`) with the predicate decisions in locals,
`compileR p` lands a state encoding `denoteR ctx p r`, framing locals/memaddrs/clock.
The same induction shape as `compile2_correct`, minus every `halted` case split; the
`Compilable` gate discharges the two response-decided branches (they are not certified
here — `condResp` is never lowerable, `condStatus` is certified in §5.1). -/
theorem compileR_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody : Word) (ctx : Ctx) (hd : Distinct3 aStat aCnt aBody) :
    ∀ (p : RespProg) (r : Response) (st : PancakeState σ),
      Compilable p →
      Enc3 aStat aCnt aBody st r →
      (∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) →
      ∃ st', PancakeSem o (compileR nm aStat aCnt aBody p) st = (none, st') ∧
        Enc3 aStat aCnt aBody st' (denoteR ctx p r) ∧
        st'.locals = st.locals ∧
        (∀ x, st'.memaddrs x = st.memaddrs x) ∧
        st'.clock = st.clock := by
  obtain ⟨d_sc, d_sb, d_cb⟩ := hd
  intro p
  induction p with
  | skip =>
    intro r st _ hEnc hDec
    exact ⟨st, sem_skip o st, hEnc, rfl, fun _ => rfl, rfl⟩
  | addHeader n v =>
    intro r st _ hEnc hDec
    obtain ⟨hS, hC, hB⟩ := hEnc
    have hval : eval st (.op .add (.loadWord (.const aCnt)) (.const (BitVec.ofNat 64 1)))
        = some (BitVec.ofNat 64 (r.headers.length + 1)) := by
      rw [eval_op_add (eval_loadWord_of_wordAt (eval_const aCnt) hC)
            (eval_const (BitVec.ofNat 64 1)), ofNat_add_unc]
    have hin : st.memaddrs aCnt = true := hC.1
    refine ⟨_, Pancake.SerializeCompile.sem_store o (eval_const aCnt) hval hin,
            ?_, rfl, fun _ => rfl, rfl⟩
    show Enc3 _ _ _ _ { r with headers := r.headers ++ [(n, v)] }
    refine ⟨wordAt_frame hS d_sc, ?_, wordAt_frame hB (Ne.symm d_cb)⟩
    show wordAt _ aCnt (BitVec.ofNat 64 (r.headers ++ [(n, v)]).length)
    rw [List.length_append]
    simpa using wordAt_hit hin
  | setStatus code reason =>
    intro r st _ hEnc hDec
    obtain ⟨hS, hC, hB⟩ := hEnc
    have hin : st.memaddrs aStat = true := hS.1
    refine ⟨_, sem_stC (v := BitVec.ofNat 64 code) o hin, ?_, rfl, fun _ => rfl, rfl⟩
    show Enc3 _ _ _ _ { r with status := code, reason := reason }
    exact ⟨wordAt_hit hin, wordAt_frame hC (Ne.symm d_sc), wordAt_frame hB (Ne.symm d_sb)⟩
  | rewriteBody t =>
    intro r st _ hEnc hDec
    obtain ⟨hS, hC, hB⟩ := hEnc
    cases t with
    | identity =>
      exact ⟨st, sem_skip o st, ⟨hS, hC, hB⟩, rfl, fun _ => rfl, rfl⟩
    | replace rb =>
      have hin : st.memaddrs aBody = true := hB.1
      refine ⟨_, sem_stC (v := BitVec.ofNat 64 rb.length) o hin, ?_, rfl, fun _ => rfl, rfl⟩
      show Enc3 _ _ _ _ { r with body := runBody (.replace rb) r.body }
      refine ⟨wordAt_frame hS d_sb, wordAt_frame hC d_cb, ?_⟩
      show wordAt _ aBody (BitVec.ofNat 64 rb.length)
      exact wordAt_hit hin
    | append e =>
      have hval : eval st (.op .add (.loadWord (.const aBody)) (.const (BitVec.ofNat 64 e.length)))
          = some (BitVec.ofNat 64 (r.body.length + e.length)) := by
        rw [eval_op_add (eval_loadWord_of_wordAt (eval_const aBody) hB)
              (eval_const (BitVec.ofNat 64 e.length)), ofNat_add_unc]
      have hin : st.memaddrs aBody = true := hB.1
      refine ⟨_, Pancake.SerializeCompile.sem_store o (eval_const aBody) hval hin,
              ?_, rfl, fun _ => rfl, rfl⟩
      show Enc3 _ _ _ _ { r with body := runBody (.append e) r.body }
      refine ⟨wordAt_frame hS d_sb, wordAt_frame hC d_cb, ?_⟩
      show wordAt _ aBody (BitVec.ofNat 64 (r.body ++ e).length)
      rw [List.length_append]
      exact wordAt_hit hin
  | seq a b iha ihb =>
    intro r st hC hEnc hDec
    obtain ⟨hCa, hCb⟩ := hC
    obtain ⟨st1, h1, hEnc1, hl1, hm1, hk1⟩ := iha r st hCa hEnc hDec
    have hDec1 : ∀ c, st1.locals (nm c) = some (if c ctx then (1 : Word) else 0) := by
      intro c; rw [hl1]; exact hDec c
    obtain ⟨st2, h2, hEnc2, hl2, hm2, hk2⟩ := ihb (denoteR ctx a r) st1 hCb hEnc1 hDec1
    refine ⟨st2, sem_seq_frames o h1 hk1 h2, hEnc2, ?_, ?_, ?_⟩
    · rw [hl2, hl1]
    · intro x; rw [hm2, hm1]
    · rw [hk2, hk1]
  | condR c a b iha ihb =>
    intro r st hC hEnc hDec
    obtain ⟨hCa, hCb⟩ := hC
    cases hc : c ctx with
    | true =>
      obtain ⟨st', h1, h2, h3, h4, h5⟩ := iha r st hCa hEnc hDec
      refine ⟨st', ?_, ?_, h3, h4, h5⟩
      · show PancakeSem o (.cond (.var (nm c)) _ _) st = (none, st')
        rw [sem_cond o (eval_var (hDec c)), hc,
            if_pos (show (if (true : Bool) then (1 : Word) else 0) ≠ 0 from word_one_ne_zero)]
        exact h1
      · show Enc3 _ _ _ _ (if c ctx then denoteR ctx a r else denoteR ctx b r)
        rw [hc, if_pos rfl]; exact h2
    | false =>
      obtain ⟨st', h1, h2, h3, h4, h5⟩ := ihb r st hCb hEnc hDec
      refine ⟨st', ?_, ?_, h3, h4, h5⟩
      · show PancakeSem o (.cond (.var (nm c)) _ _) st = (none, st')
        rw [sem_cond o (eval_var (hDec c)), hc,
            if_neg (show ¬ ((if (false : Bool) then (1 : Word) else 0) ≠ 0) from fun h => h rfl)]
        exact h1
      · show Enc3 _ _ _ _ (if c ctx then denoteR ctx a r else denoteR ctx b r)
        rw [hc, if_neg (show ¬ ((false : Bool) = true) by decide)]; exact h2
  | condResp c a b _ _ =>
    -- excluded from `Compilable` — the general branch is never certified here.
    intro r st hC _ _; exact hC.elim
  | condStatus k a b _ _ =>
    -- excluded from `Compilable` — certified separately in §5.1 under the wf invariant.
    intro r st hC _ _; exact hC.elim

/-! ### 5.1 THE STATUS-KEYED COMPILE FRAGMENT — `condStatus` lowers to ONE `.cond`

The folded-in `condStatus k` compiles to a single comparison against the LIVE status
cell (`aStat` in `Enc3`) — the tractable slice of the response-decided branch, because
the status IS on the machine (the header LIST is not). It is EXACT under a
`status < 2^64` well-formedness invariant, decoded through `ofNat64_inj`.

The fragment `LowerableS` excludes two things, for two different reasons:
* `setStatus` — the invariant is threaded by keeping the status STABLE across
  sub-terms (`denoteR_preserves_status`); a program that rewrites the status would
  need its new code bounded too. (`compileR_correct` above compiles `setStatus`
  fine — it just never reads the status back.)
* `condResp` — the GENERAL branch has no faithful lowering at all.

So the two compile theorems cover complementary fragments, and neither claims
anything about `condResp`. -/

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

/-- The status-keyed compilable fragment: the base ops WITHOUT `setStatus` (so the
status cell is stable), `seq`/`condR`, and `condStatus` at a bounded key. The general
`condResp` is EXCLUDED. -/
def LowerableS : RespProg → Prop
  | .skip => True
  | .addHeader _ _ => True
  | .setStatus _ _ => False
  | .rewriteBody _ => True
  | .seq a b => LowerableS a ∧ LowerableS b
  | .condR _ a b => LowerableS a ∧ LowerableS b
  | .condResp _ _ _ => False
  | .condStatus k a b => k < 2 ^ 64 ∧ LowerableS a ∧ LowerableS b

/-- On the `LowerableS` fragment the denotation never touches the status, so the
`< 2^64` invariant is re-established for every sub-term — exactly what `condStatus`'s
comparison needs to decode. -/
theorem denoteR_preserves_status (ctx : Ctx) :
    ∀ (p : RespProg) (r : Response), LowerableS p → (denoteR ctx p r).status = r.status := by
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
  | condResp c a b _ _ => intro r h; exact h.elim
  | condStatus k a b iha ihb =>
    intro r h; obtain ⟨_, ha, hb⟩ := h
    show (if r.status = k then denoteR ctx a r else denoteR ctx b r).status = r.status
    by_cases hk : r.status = k
    · rw [if_pos hk]; exact iha r ha
    · rw [if_neg hk]; exact ihb r hb

/-- **`compileR_condStatus_correct` — the status-keyed fragment, proven.** For a
`LowerableS` program, from any state encoding a well-formed `r` (`status < 2^64`),
`compileR` lands a state encoding `denoteR ctx p r`. The `condStatus` case is the new
content: ONE comparison against the `aStat` cell, decoded through `ofNat64_inj` under
the status bound (re-established for sub-terms by `denoteR_preserves_status`, since
the fragment never rewrites the status). The `condResp` case is discharged by the
fragment gate — never certified. -/
theorem compileR_condStatus_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody : Word) (ctx : Ctx) (hd : Distinct3 aStat aCnt aBody) :
    ∀ (p : RespProg) (r : Response) (st : PancakeState σ),
      LowerableS p → r.status < 2 ^ 64 →
      Enc3 aStat aCnt aBody st r →
      (∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) →
      ∃ st', PancakeSem o (compileR nm aStat aCnt aBody p) st = (none, st') ∧
        Enc3 aStat aCnt aBody st' (denoteR ctx p r) ∧
        st'.locals = st.locals ∧
        (∀ x, st'.memaddrs x = st.memaddrs x) ∧
        st'.clock = st.clock := by
  intro p
  induction p with
  | skip =>
    intro r st _ _ hEnc hDec
    exact compileR_correct o nm aStat aCnt aBody ctx hd .skip r st trivial hEnc hDec
  | addHeader n v =>
    intro r st _ _ hEnc hDec
    exact compileR_correct o nm aStat aCnt aBody ctx hd (.addHeader n v) r st trivial hEnc hDec
  | setStatus code reason =>
    intro r st hL _ _ _; exact hL.elim
  | rewriteBody t =>
    intro r st _ _ hEnc hDec
    exact compileR_correct o nm aStat aCnt aBody ctx hd (.rewriteBody t) r st trivial hEnc hDec
  | seq a b iha ihb =>
    intro r st hL hwf hEnc hDec
    obtain ⟨hLa, hLb⟩ := hL
    obtain ⟨st1, h1, hEnc1, hl1, hm1, hk1⟩ := iha r st hLa hwf hEnc hDec
    have hwf1 : (denoteR ctx a r).status < 2 ^ 64 := by
      rw [denoteR_preserves_status ctx a r hLa]; exact hwf
    have hDec1 : ∀ c, st1.locals (nm c) = some (if c ctx then (1 : Word) else 0) := by
      intro c; rw [hl1]; exact hDec c
    obtain ⟨st2, h2, hEnc2, hl2, hm2, hk2⟩ := ihb (denoteR ctx a r) st1 hLb hwf1 hEnc1 hDec1
    refine ⟨st2, sem_seq_frames o h1 hk1 h2, hEnc2, ?_, ?_, ?_⟩
    · rw [hl2, hl1]
    · intro x; rw [hm2, hm1]
    · rw [hk2, hk1]
  | condR c a b iha ihb =>
    intro r st hL hwf hEnc hDec
    obtain ⟨hLa, hLb⟩ := hL
    cases hc : c ctx with
    | true =>
      obtain ⟨st', h1, h2, h3, h4, h5⟩ := iha r st hLa hwf hEnc hDec
      refine ⟨st', ?_, ?_, h3, h4, h5⟩
      · show PancakeSem o (.cond (.var (nm c)) _ _) st = (none, st')
        rw [sem_cond o (eval_var (hDec c)), hc,
            if_pos (show (if (true : Bool) then (1 : Word) else 0) ≠ 0 from word_one_ne_zero)]
        exact h1
      · show Enc3 _ _ _ _ (if c ctx then denoteR ctx a r else denoteR ctx b r)
        rw [hc, if_pos rfl]; exact h2
    | false =>
      obtain ⟨st', h1, h2, h3, h4, h5⟩ := ihb r st hLb hwf hEnc hDec
      refine ⟨st', ?_, ?_, h3, h4, h5⟩
      · show PancakeSem o (.cond (.var (nm c)) _ _) st = (none, st')
        rw [sem_cond o (eval_var (hDec c)), hc,
            if_neg (show ¬ ((if (false : Bool) then (1 : Word) else 0) ≠ 0) from fun h => h rfl)]
        exact h1
      · show Enc3 _ _ _ _ (if c ctx then denoteR ctx a r else denoteR ctx b r)
        rw [hc, if_neg (show ¬ ((false : Bool) = true) by decide)]; exact h2
  | condResp c a b _ _ =>
    intro r st hL _ _ _; exact hL.elim
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
              (compileR nm aStat aCnt aBody a) (compileR nm aStat aCnt aBody b)) st = (none, st')
        rw [sem_cond o heval, hbv, if_pos rfl,
            if_pos (show (1 : Word) ≠ 0 from word_one_ne_zero)]
        exact hsem
      · show Enc3 aStat aCnt aBody st' (if r.status = k then denoteR ctx a r else denoteR ctx b r)
        rw [if_pos h]; exact hE
    · have hbv : ¬ (BitVec.ofNat 64 r.status = BitVec.ofNat 64 k) :=
        fun hh => h ((ofNat64_inj hwf hk).mp hh)
      obtain ⟨st', hsem, hE, hl, hm, hkk⟩ := ihb r st hLb hwf hEnc hDec
      refine ⟨st', ?_, ?_, hl, hm, hkk⟩
      · show PancakeSem o (.cond (.cmp .equal (.loadWord (.const aStat)) (.const (BitVec.ofNat 64 k)))
              (compileR nm aStat aCnt aBody a) (compileR nm aStat aCnt aBody b)) st = (none, st')
        rw [sem_cond o heval, if_neg hbv,
            if_neg (show ¬ ((0 : Word) ≠ 0) from fun hh => hh rfl)]
        exact hsem
      · show Enc3 aStat aCnt aBody st' (if r.status = k then denoteR ctx a r else denoteR ctx b r)
        rw [if_neg h]; exact hE

/-- `condStatus k` IS the `condResp` instance keyed on `r.status = k`: the compilable
slice is a genuine special case of the general branch, not an ad-hoc addition. -/
theorem denoteR_condStatus_eq (ctx : Ctx) (k : Nat) (a b : RespProg) (r : Response) :
    denoteR ctx (.condStatus k a b) r
      = denoteR ctx (.condResp (fun _ r => decide (r.status = k)) a b) r := by
  show (if r.status = k then denoteR ctx a r else denoteR ctx b r)
     = (if (decide (r.status = k) = true) then denoteR ctx a r else denoteR ctx b r)
  by_cases h : r.status = k
  · rw [if_pos h, if_pos (show decide (r.status = k) = true by simp [h])]
  · rw [if_neg h, if_neg (show ¬ (decide (r.status = k) = true) by simp [h])]

/-! ## 6. `compileChain` — the onion compiler: control flow IS the short-circuit

No halt flag. A stage lowers to ONE `.cond` on its pre-decided guard bit:
* FIRE arm — emit the blank seed, the refusal fragment, then the INNER stages'
  response fragments (innermost first — `respFold`'s application order as
  instruction order);
* PASS arm — the compiled inner chain, THEN this stage's response fragment
  (the onion wrap: outer's `onResp` runs after everything inside).
A fire deep inside the pass-arm nesting naturally falls out through every
enclosing pass arm's trailing `onResp` fragment — exactly `runChain`'s
recursion, with the branch structure realizing the skip. -/

/-- The inner response onion, lowered: innermost stage's fragment first. -/
def respFoldProg (nm : ReqPred → String) (aStat aCnt aBody : Word) :
    List StageSpec → PancakeProg
  | [] => .skip
  | s :: rest => .seq (respFoldProg nm aStat aCnt aBody rest)
                      (compileR nm aStat aCnt aBody s.onResp)

/-- Seed the three slots with `blankResp`'s skeleton (status 200, no headers,
empty body) — the machine `ofResponse blankResp`. -/
def emitBlank (aStat aCnt aBody : Word) : PancakeProg :=
  .seq (stC aStat (BitVec.ofNat 64 200))
    (.seq (stC aCnt (BitVec.ofNat 64 0)) (stC aBody (BitVec.ofNat 64 0)))

/-- **`compileChain` — the onion, lowered.** Parametrized over the compiled
handler fragment `hFrag` (the innermost core the full chain wraps). -/
def compileChain (nm : ReqPred → String) (aStat aCnt aBody : Word)
    (hFrag : PancakeProg) : List StageSpec → PancakeProg
  | [] => hFrag
  | s :: rest =>
    .cond (.var (nm s.guard))
      (.seq (emitBlank aStat aCnt aBody)
        (.seq (compileR nm aStat aCnt aBody s.refusal)
              (respFoldProg nm aStat aCnt aBody rest)))
      (.seq (compileChain nm aStat aCnt aBody hFrag rest)
            (compileR nm aStat aCnt aBody s.onResp))

/-- `emitBlank` lands `Enc3 blankResp` from mere slot addressability. -/
theorem emitBlank_correct (o : Oracle σ) {aStat aCnt aBody : Word}
    (hd : Distinct3 aStat aCnt aBody) (st : PancakeState σ)
    (hS : st.memaddrs aStat = true) (hC : st.memaddrs aCnt = true)
    (hB : st.memaddrs aBody = true) :
    ∃ st', PancakeSem o (emitBlank aStat aCnt aBody) st = (none, st') ∧
      Enc3 aStat aCnt aBody st' blankResp ∧
      st'.locals = st.locals ∧
      (∀ x, st'.memaddrs x = st.memaddrs x) ∧
      st'.clock = st.clock := by
  obtain ⟨d_sc, d_sb, d_cb⟩ := hd
  -- st1: status := 200
  obtain ⟨st1, hst1⟩ : ∃ s : PancakeState σ,
      s = { st with memory := fun k => if k = aStat then BitVec.ofNat 64 200 else st.memory k } :=
    ⟨_, rfl⟩
  have h1 : PancakeSem o (stC aStat (BitVec.ofNat 64 200)) st = (none, st1) := by
    rw [hst1]; exact sem_stC o hS
  -- st2: count := 0
  have hC1 : st1.memaddrs aCnt = true := by rw [hst1]; exact hC
  obtain ⟨st2, hst2⟩ : ∃ s : PancakeState σ,
      s = { st1 with memory := fun k => if k = aCnt then BitVec.ofNat 64 0 else st1.memory k } :=
    ⟨_, rfl⟩
  have h2 : PancakeSem o (stC aCnt (BitVec.ofNat 64 0)) st1 = (none, st2) := by
    rw [hst2]; exact sem_stC o hC1
  -- st3: body := 0
  have hB2 : st2.memaddrs aBody = true := by rw [hst2, hst1]; exact hB
  obtain ⟨st3, hst3⟩ : ∃ s : PancakeState σ,
      s = { st2 with memory := fun k => if k = aBody then BitVec.ofNat 64 0 else st2.memory k } :=
    ⟨_, rfl⟩
  have h3 : PancakeSem o (stC aBody (BitVec.ofNat 64 0)) st2 = (none, st3) := by
    rw [hst3]; exact sem_stC o hB2
  have hk1 : st1.clock = st.clock := by rw [hst1]
  have hk2 : st2.clock = st1.clock := by rw [hst2]
  refine ⟨st3, sem_seq_frames o h1 hk1 (sem_seq_frames o h2 hk2 h3), ?_, ?_, ?_, ?_⟩
  · show Enc3 _ _ _ st3 blankResp
    refine ⟨?_, ?_, ?_⟩
    · show wordAt st3 aStat (BitVec.ofNat 64 200)
      rw [hst3]; refine wordAt_frame ?_ d_sb
      rw [hst2]; refine wordAt_frame ?_ d_sc
      rw [hst1]; exact wordAt_hit hS
    · show wordAt st3 aCnt (BitVec.ofNat 64 0)
      rw [hst3]; refine wordAt_frame ?_ d_cb
      rw [hst2]; exact wordAt_hit hC1
    · show wordAt st3 aBody (BitVec.ofNat 64 0)
      rw [hst3]; exact wordAt_hit hB2
  · rw [hst3, hst2, hst1]
  · intro x; rw [hst3, hst2, hst1]
  · rw [hst3, hst2, hst1]

/-- The lowered inner response onion is correct: from a state encoding `r`,
`respFoldProg stages` lands the encoding of `respFold ctx stages r`. Induction
on the stage list; each step is one `compileR_correct`. -/
theorem respFoldProg_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody : Word) (ctx : Ctx) (hd : Distinct3 aStat aCnt aBody) :
    ∀ (stages : List StageSpec) (r : Response) (st : PancakeState σ),
      (∀ s ∈ stages, Compilable s.onResp) →
      Enc3 aStat aCnt aBody st r →
      (∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) →
      ∃ st', PancakeSem o (respFoldProg nm aStat aCnt aBody stages) st = (none, st') ∧
        Enc3 aStat aCnt aBody st' (respFold ctx stages r) ∧
        st'.locals = st.locals ∧
        (∀ x, st'.memaddrs x = st.memaddrs x) ∧
        st'.clock = st.clock := by
  intro stages
  induction stages with
  | nil =>
    intro r st _ hEnc hDec
    exact ⟨st, sem_skip o st, hEnc, rfl, fun _ => rfl, rfl⟩
  | cons s rest ih =>
    intro r st hCs hEnc hDec
    have hCsRest : ∀ t ∈ rest, Compilable t.onResp := fun t ht => hCs t (by simp [ht])
    have hCsHead : Compilable s.onResp := hCs s (by simp)
    obtain ⟨st1, h1, hEnc1, hl1, hm1, hk1⟩ := ih r st hCsRest hEnc hDec
    have hDec1 : ∀ c, st1.locals (nm c) = some (if c ctx then (1 : Word) else 0) := by
      intro c; rw [hl1]; exact hDec c
    obtain ⟨st2, h2, hEnc2, hl2, hm2, hk2⟩ :=
      compileR_correct o nm aStat aCnt aBody ctx hd s.onResp (respFold ctx rest r) st1
        hCsHead hEnc1 hDec1
    refine ⟨st2, sem_seq_frames o h1 hk1 h2, hEnc2, ?_, ?_, ?_⟩
    · rw [hl2, hl1]
    · intro x; rw [hm2, hm1]
    · rw [hk2, hk1]

/-- **`compileChain_correct` — THE MACHINE ONION, by induction on the stage
list.** Parametrized over the handler fragment `hFrag` and its correctness `hH`
(from addressable slots + decisions, `hFrag` lands `Enc3 (handler ctx)` with
frames). From any state encoding any seed `r`, the compiled chain lands the
skeleton of the REAL onion denotation `runChain ctx handler stages`:
* a fired guard takes the `.cond` fire arm — blank seed, refusal, inner
  response fragments (NO halt flag: the untaken pass arm is the "skip");
* a passing guard takes the pass arm — inner chain (IH), then this stage's
  `onResp` fragment (the onion wrap). -/
theorem compileChain_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody : Word) (ctx : Ctx) (hd : Distinct3 aStat aCnt aBody)
    (handler : Ctx → Response) (hFrag : PancakeProg)
    (hH : ∀ st : PancakeState σ,
      st.memaddrs aStat = true → st.memaddrs aCnt = true → st.memaddrs aBody = true →
      (∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) →
      ∃ st', PancakeSem o hFrag st = (none, st') ∧
        Enc3 aStat aCnt aBody st' (handler ctx) ∧
        st'.locals = st.locals ∧ (∀ x, st'.memaddrs x = st.memaddrs x) ∧
        st'.clock = st.clock) :
    ∀ (stages : List StageSpec) (r : Response) (st : PancakeState σ),
      (∀ s ∈ stages, Compilable s.refusal ∧ Compilable s.onResp) →
      Enc3 aStat aCnt aBody st r →
      (∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) →
      ∃ st', PancakeSem o (compileChain nm aStat aCnt aBody hFrag stages) st = (none, st') ∧
        Enc3 aStat aCnt aBody st' (runChain ctx handler stages) ∧
        st'.locals = st.locals ∧
        (∀ x, st'.memaddrs x = st.memaddrs x) ∧
        st'.clock = st.clock := by
  intro stages
  induction stages with
  | nil =>
    intro r st _ hEnc hDec
    exact hH st hEnc.1.1 hEnc.2.1.1 hEnc.2.2.1 hDec
  | cons s rest ih =>
    intro r st hCs hEnc hDec
    have hCsHead : Compilable s.refusal ∧ Compilable s.onResp := hCs s (by simp)
    have hCsRest : ∀ t ∈ rest, Compilable t.refusal ∧ Compilable t.onResp :=
      fun t ht => hCs t (by simp [ht])
    cases hg : s.guard ctx with
    | true =>
      -- FIRE: blank seed → refusal fragment → inner response fragments
      obtain ⟨st1, h1, hEnc1, hl1, hm1, hk1⟩ :=
        emitBlank_correct o hd st hEnc.1.1 hEnc.2.1.1 hEnc.2.2.1
      have hDec1 : ∀ c, st1.locals (nm c) = some (if c ctx then (1 : Word) else 0) := by
        intro c; rw [hl1]; exact hDec c
      obtain ⟨st2, h2, hEnc2, hl2, hm2, hk2⟩ :=
        compileR_correct o nm aStat aCnt aBody ctx hd s.refusal blankResp st1
          hCsHead.1 hEnc1 hDec1
      have hDec2 : ∀ c, st2.locals (nm c) = some (if c ctx then (1 : Word) else 0) := by
        intro c; rw [hl2]; exact hDec1 c
      obtain ⟨st3, h3, hEnc3, hl3, hm3, hk3⟩ :=
        respFoldProg_correct o nm aStat aCnt aBody ctx hd rest
          (denoteR ctx s.refusal blankResp) st2 (fun t ht => (hCsRest t ht).2) hEnc2 hDec2
      refine ⟨st3, ?_, ?_, ?_, ?_, ?_⟩
      · show PancakeSem o (.cond (.var (nm s.guard)) _ _) st = (none, st3)
        rw [sem_cond o (eval_var (hDec s.guard)), hg,
            if_pos (show (if (true : Bool) then (1 : Word) else 0) ≠ 0 from word_one_ne_zero)]
        exact sem_seq_frames o h1 hk1 (sem_seq_frames o h2 hk2 h3)
      · show Enc3 _ _ _ _ (runChain ctx handler (s :: rest))
        rw [runChain_cons, hg, if_pos rfl]
        exact hEnc3
      · rw [hl3, hl2, hl1]
      · intro x; rw [hm3, hm2, hm1]
      · rw [hk3, hk2, hk1]
    | false =>
      -- PASS: inner chain (IH), then this stage's onResp wrap
      obtain ⟨st1, h1, hEnc1, hl1, hm1, hk1⟩ := ih r st hCsRest hEnc hDec
      have hDec1 : ∀ c, st1.locals (nm c) = some (if c ctx then (1 : Word) else 0) := by
        intro c; rw [hl1]; exact hDec c
      obtain ⟨st2, h2, hEnc2, hl2, hm2, hk2⟩ :=
        compileR_correct o nm aStat aCnt aBody ctx hd s.onResp
          (runChain ctx handler rest) st1 hCsHead.2 hEnc1 hDec1
      refine ⟨st2, ?_, ?_, ?_, ?_, ?_⟩
      · show PancakeSem o (.cond (.var (nm s.guard)) _ _) st = (none, st2)
        rw [sem_cond o (eval_var (hDec s.guard)), hg,
            if_neg (show ¬ ((if (false : Bool) then (1 : Word) else 0) ≠ 0) from fun h => h rfl)]
        exact sem_seq_frames o h1 hk1 h2
      · show Enc3 _ _ _ _ (runChain ctx handler (s :: rest))
        rw [runChain_cons, hg, if_neg (show ¬ ((false : Bool) = true) by decide)]
        exact hEnc2
      · rw [hl2, hl1]
      · intro x; rw [hm2, hm1]
      · rw [hk2, hk1]

/-! ### 6.1 A closed instantiation — the handler as a `RespProg` core -/

/-- A closed handler fragment: seed blank, run the handler's own `RespProg`. -/
def handlerFrag (nm : ReqPred → String) (aStat aCnt aBody : Word) (hprog : RespProg) :
    PancakeProg :=
  .seq (emitBlank aStat aCnt aBody) (compileR nm aStat aCnt aBody hprog)

/-- The closed handler fragment satisfies `compileChain_correct`'s handler
hypothesis, for the handler `fun c => denoteR c hprog blankResp`. -/
theorem handlerFrag_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody : Word) (ctx : Ctx) (hd : Distinct3 aStat aCnt aBody)
    (hprog : RespProg) (hCp : Compilable hprog) (st : PancakeState σ)
    (hS : st.memaddrs aStat = true) (hC : st.memaddrs aCnt = true)
    (hB : st.memaddrs aBody = true)
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (handlerFrag nm aStat aCnt aBody hprog) st = (none, st') ∧
      Enc3 aStat aCnt aBody st' (denoteR ctx hprog blankResp) ∧
      st'.locals = st.locals ∧ (∀ x, st'.memaddrs x = st.memaddrs x) ∧
      st'.clock = st.clock := by
  obtain ⟨st1, h1, hEnc1, hl1, hm1, hk1⟩ := emitBlank_correct o hd st hS hC hB
  have hDec1 : ∀ c, st1.locals (nm c) = some (if c ctx then (1 : Word) else 0) := by
    intro c; rw [hl1]; exact hDec c
  obtain ⟨st2, h2, hEnc2, hl2, hm2, hk2⟩ :=
    compileR_correct o nm aStat aCnt aBody ctx hd hprog blankResp st1 hCp hEnc1 hDec1
  refine ⟨st2, sem_seq_frames o h1 hk1 h2, hEnc2, ?_, ?_, ?_⟩
  · rw [hl2, hl1]
  · intro x; rw [hm2, hm1]
  · rw [hk2, hk1]

/-- **The CLOSED whole-chain compile theorem** — no hypotheses about any
fragment: chain + handler are both compiled from the deep embedding, and the
machine lands the skeleton of the full two-phase onion denotation. -/
theorem compileChain_closed_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody : Word) (ctx : Ctx) (hd : Distinct3 aStat aCnt aBody)
    (hprog : RespProg) (hCp : Compilable hprog)
    (stages : List StageSpec) (hCs : ∀ s ∈ stages, Compilable s.refusal ∧ Compilable s.onResp)
    (r : Response) (st : PancakeState σ)
    (hEnc : Enc3 aStat aCnt aBody st r)
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o
        (compileChain nm aStat aCnt aBody (handlerFrag nm aStat aCnt aBody hprog) stages) st
        = (none, st') ∧
      Enc3 aStat aCnt aBody st'
        (runChain ctx (fun c => denoteR c hprog blankResp) stages) := by
  obtain ⟨st', h1, h2, _, _, _⟩ :=
    compileChain_correct o nm aStat aCnt aBody ctx hd
      (fun c => denoteR c hprog blankResp) (handlerFrag nm aStat aCnt aBody hprog)
      (fun s hS hC hB hDec' =>
        handlerFrag_correct o nm aStat aCnt aBody ctx hd hprog hCp s hS hC hB hDec')
      stages r st hCs hEnc hDec
  exact ⟨st', h1, h2⟩

/-! ### 6.2 The machine-level keystone -/

/-- **`compileChain_gate_keystone`.** The denotational keystone carried to the
machine: when the gate at depth `|pre|` fires (everything before passes), the
compiled chain lands the skeleton of the refusal AS TRANSFORMED BY EVERY OTHER
STAGE'S RESPONSE PHASE — outer wraps and inner folds alike — with the handler
provably absent from the result. -/
theorem compileChain_gate_keystone (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody : Word) (ctx : Ctx) (hd : Distinct3 aStat aCnt aBody)
    (hprog : RespProg) (hCp : Compilable hprog)
    (pre : List StageSpec) (g : StageSpec) (rest : List StageSpec)
    (hCs : ∀ s ∈ pre ++ g :: rest, Compilable s.refusal ∧ Compilable s.onResp)
    (r : Response) (st : PancakeState σ)
    (hpre : ∀ s ∈ pre, s.guard ctx = false) (hg : g.guard ctx = true)
    (hEnc : Enc3 aStat aCnt aBody st r)
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o
        (compileChain nm aStat aCnt aBody (handlerFrag nm aStat aCnt aBody hprog)
          (pre ++ g :: rest)) st = (none, st') ∧
      Enc3 aStat aCnt aBody st'
        (respFold ctx (pre ++ rest) (denoteR ctx g.refusal blankResp)) := by
  obtain ⟨st', h1, h2⟩ :=
    compileChain_closed_correct o nm aStat aCnt aBody ctx hd hprog hCp
      (pre ++ g :: rest) hCs r st hEnc hDec
  refine ⟨st', h1, ?_⟩
  rw [← runChain_gate_keystone ctx (fun c => denoteR c hprog blankResp) pre g rest hpre hg]
  exact h2

/-! ## 7. Non-vacuity of the compiled semantics

The keystone's right-hand side genuinely varies with the program: the
security-headers-on-405 refusal has a DIFFERENT skeleton than the bare refusal
(2 headers vs 0), the passing path lands the handler's skeleton, and the old
flat denotation of the "same" serve differs. -/

#guard (respFold ctxPost [secStage] (denoteR ctxPost gate405.refusal blankResp)).headers.length = 2
#guard (denoteR ctxPost gate405.refusal blankResp).headers.length = 0
#guard (respFold ctxPost [secStage] (denoteR ctxPost gate405.refusal blankResp)).status = 405
#guard (runChain ctxGet (fun c => c.base) [secStage, gate405]).body.length = 2

/-! ## 8. Axiom audit — expect ⊆ {propext, Classical.choice, Quot.sound}, 0 sorryAx. -/

#print axioms runChain_gate_keystone
#print axioms runChain_gate_ignores_handler
#print axioms secHeaders_on_refusal
#print axioms compileR_correct
#print axioms compileChain_correct
#print axioms compileChain_closed_correct
#print axioms compileChain_gate_keystone
-- the folded-in response-decided branch (§1, §5.1):
#print axioms denoteR_condStatus_eq
#print axioms denoteR_preserves_status
#print axioms ofNat64_inj
#print axioms compileR_condStatus_correct

end Pancake.StageOnion
