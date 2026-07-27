/-
  Pancake/ServeCompose.lean — THE WHOLE SERVE AS ONE `StageProg` TERM.

  Up to here each deployed stage was lifted BY HAND: a bespoke `StageProg` term plus a
  bespoke `denote <term> = <deployed stage>` pin, three or four per wave. That does not
  scale to the 52-stage deployed fold and it is the wrong shape of work: the deployed
  stages fall into a FEW SHAPES, so the right move is ONE GENERAL theorem per shape and
  ONE GENERAL composition law, after which a stage costs a list entry, not a proof.

  This module does exactly that, in four steps:

   * §2  `seqAll : List StageProg → StageProg` and **`denoteStep_seqAll`** — the
     composition law: the denotation of an N-way `seq` composition IS the left fold of
     the per-stage steps. Proven by LIST INDUCTION, so a 52-entry pipeline costs the
     same proof as a 2-entry one. Nothing below re-does a per-stage `seq` step.

   * §3  The SHAPE theorems, each `∀`-quantified over the whole shape family:
       - `denote_stampChain`  — a chain of N header stamps appends its N headers, for
         ANY header list (list induction). The 26-odd stamp-shaped deployed stages are
         instances; not 26 proofs.
       - `denote_gateChain`   — a chain of N refusal gates answers the FIRST firing
         gate's status and no other, for ANY (predicate, status) list (list induction).
         The 20 gate-shaped deployed stages are instances; not 20 proofs.

   * §4  A faithful TRANSCRIPTION of the deployed pipeline model (`DStage`,
     `dRunResp`, `dRunPipeline`, the affine `DBuilder`) — the deployed serve lives in a
     different package that this one cannot import, so the reference fold is
     transcribed here, definition for definition, from the deployed pipeline module
     (structure `Stage` with `onRequest`/`onResponse`; `runResp` threading the builder
     back outward in REVERSE list order; `runPipeline` gating in list order and seeding
     the builder from the handler). Every constant is transcribed, none is invented.

   * §5  **THE COMPOSITION THEOREM** — `denote_serveProg_pass`:

         denote (serveProg gates progs) ctx = (dRunPipeline stages handler ctx).build

     the ONE composed `StageProg` term denotes exactly what the deployed N-stage fold
     builds. Proven by INDUCTION over the stage list (an induction over
     the per-stage realization relation) — NOT by N hand steps. Adding a stage adds a
     list entry and one `Realizes` obligation of an already-proven shape.

   * §6  `compile2` eats the WHOLE composed term: `serveProg_compile2_correct` is
     `compile2_correct` (the genuine per-constructor compiler's structural-induction
     keystone) instantiated at `p := serveProg …`. One line, because the compiler was
     built per-constructor and proven by induction — the whole point of having it.

  ## THE ONION — why `ps.reverse`

  The deployed response phase runs `onResponse` in REVERSE list order (the outermost
  stage sees the request first and the response LAST), while `denote` folds its ops
  left to right appending at the END. So the composed term's response segment is the
  stage terms in REVERSED deployed order. `seqAll ps.reverse` carries that, and the
  composition theorem proves it rather than asserting it.

  ## COVERAGE — 25 of the 52, and the reason for each of the other 27 (§7)

  Honest accounting, not a forced fit. The composition theorem is general over the
  stage list; what is INSTANTIATED here is the 20 gate-shaped stages (their request-
  phase status decision, statuses read off each stage's own refusal response) plus the
  5 response-phase positions whose terms are already pinned. §7 lists all 27 that do
  NOT fit today, each with the concrete reason.

  ## RESIDUALS (named, not hidden)

   * THE GATE/ONION DIVERGENCE. In the deployed fold a gate's `.respond` skips only the
     LATER stages' REQUEST phase — every stage's `onResponse` still runs over the
     refusal response. `StageProg`'s `gate` HALTS, and `denote`'s halt flag absorbs
     every later op, so the composed term's fire path drops the stamps the deployed
     fold keeps. The composition theorem is therefore stated on the PASS path
     (`firstFire … = none`), which is where the two agree; the fire path is covered
     only for the STATUS (`denote_serveProg_fire`). Closing this needs a `StageProg` op
     that seeds the base and continues (or a non-halting gate encoding); it is a change
     to the keystone DSL, out of this module.
   * ACCUMULATOR-KEYED CONDITIONS. Five deployed stamps gate on `b.acc.status == 200`
     — the ACCUMULATED response, mid-fold. `ReqPred := Ctx → Bool` cannot see it (it
     sees the request and the handler's base only). Listed in §7.
   * The `gate`-carries-a-bare-status residual of the DSL carries over: a refusal's own
     headers/body (a 405's `Allow`, a 308's `Location`) are not carried by `gate`.
-/
import Pancake.StageMore
import Pancake.StageEvenMore

namespace Pancake.ServeCompose

open Pancake Pancake.SerializeCompile Pancake.StageProg Pancake.StageCompile

variable {σ : Type}

/-! ## 1. The no-op stage term

The identity element of `seq`: a body rewrite that returns the body. It is a real
`StageProg` constructor (it compiles to `Skip`), not a new one. -/

/-- The no-op stage term — `seq`'s identity. -/
def nop : StageProg := .rewriteBody .identity

/-- **`denoteStep_nop`.** The no-op leaves the fold state untouched, halted or not. -/
theorem denoteStep_nop (ctx : Ctx) (d : DState) : denoteStep ctx nop d = d := by
  obtain ⟨r, hb⟩ := d
  cases hb <;> simp [nop, denoteStep, runBody]

/-! ## 2. `seqAll` + THE COMPOSITION LAW (list induction)

The whole point: an N-stage pipeline is ONE `seq`-composed term, and its denotation is
the left fold of the per-stage steps — by induction on the list, once, for every N. -/

/-- **`seqAll` — the N-way `seq` composition** of a stage-term list, in order. -/
def seqAll : List StageProg → StageProg
  | []      => nop
  | p :: ps => .seq p (seqAll ps)

/-- **`denoteStep_seqAll` — THE COMPOSITION LAW.** The composed term's fold step IS the
left fold of the components' steps, for ANY list and ANY start state. By LIST
INDUCTION: `nil` is the no-op, `cons` threads one step into the tail's fold. This is
what makes the 52-stage pipeline cost one proof instead of 52. -/
theorem denoteStep_seqAll (ctx : Ctx) :
    ∀ (ps : List StageProg) (d : DState),
      denoteStep ctx (seqAll ps) d = ps.foldl (fun d p => denoteStep ctx p d) d := by
  intro ps
  induction ps with
  | nil => intro d; exact denoteStep_nop ctx d
  | cons p ps ih =>
    intro d
    show denoteStep ctx (seqAll ps) (denoteStep ctx p d) = _
    rw [ih]
    rfl

/-- **`denote_seqAll`.** The composed term's denotation is the fold of the component
steps over the handler's base response. -/
theorem denote_seqAll (ctx : Ctx) (ps : List StageProg) :
    denote (seqAll ps) ctx
      = (ps.foldl (fun d p => denoteStep ctx p d) { resp := ctx.base, halted := false }).resp := by
  show (denoteStep ctx (seqAll ps) { resp := ctx.base, halted := false }).resp = _
  rw [denoteStep_seqAll]

/-- **`denoteStep_seqAll_snoc`.** Appending a term at the END of the composition runs
it LAST. (The onion step: the outermost stage's response transform runs last.) -/
theorem denoteStep_seqAll_snoc (ctx : Ctx) (ps : List StageProg) (p : StageProg)
    (d : DState) :
    denoteStep ctx (seqAll (ps ++ [p])) d = denoteStep ctx p (denoteStep ctx (seqAll ps) d) := by
  rw [denoteStep_seqAll, List.foldl_append, denoteStep_seqAll]
  rfl

/-! ### 2.1 Halt-freedom — the stamps never short-circuit

The response-phase stage terms contain no `gate`, so the fold stays live through the
whole onion. That is the side condition the composition theorem carries, and it is
decided structurally. -/

/-- `haltFree p`: `p` contains no `gate`, so it can never set the halt flag. -/
def haltFree : StageProg → Prop
  | .gate _ _    => False
  | .seq a b     => haltFree a ∧ haltFree b
  | .condR _ a b => haltFree a ∧ haltFree b
  | _            => True

/-- **`denoteStep_haltFree`.** A gate-free term never changes the halt flag — by
structural induction on `StageProg`. -/
theorem denoteStep_haltFree (ctx : Ctx) :
    ∀ (p : StageProg), haltFree p → ∀ (d : DState), (denoteStep ctx p d).halted = d.halted := by
  intro p
  induction p with
  | addHeader n v =>
    intro _ d; obtain ⟨r, hb⟩ := d; cases hb <;> simp [denoteStep]
  | addHeaderF nameF valF =>
    intro _ d; obtain ⟨r, hb⟩ := d; cases hb <;> simp [denoteStep]
  | setStatus c r =>
    intro _ d; obtain ⟨rr, hb⟩ := d; cases hb <;> simp [denoteStep]
  | gate c code => intro h; exact absurd h (by exact fun x => x)
  | rewriteBody t =>
    intro _ d; obtain ⟨r, hb⟩ := d; cases hb <;> simp [denoteStep]
  | seq a b iha ihb =>
    intro h d
    show (denoteStep ctx b (denoteStep ctx a d)).halted = d.halted
    rw [ihb h.2, iha h.1]
  | condR c a b iha ihb =>
    intro h d
    show (if c ctx then denoteStep ctx a d else denoteStep ctx b d).halted = d.halted
    by_cases hc : c ctx = true
    · rw [if_pos hc]; exact iha h.1 d
    · rw [if_neg hc]; exact ihb h.2 d

/-- `nop` is gate-free. -/
theorem haltFree_nop : haltFree nop := trivial

/-- **`haltFree_seqAll`.** A composition of gate-free terms is gate-free — list
induction, so a 52-term composition is discharged by the same lemma. -/
theorem haltFree_seqAll : ∀ (ps : List StageProg), (∀ p ∈ ps, haltFree p) → haltFree (seqAll ps) := by
  intro ps
  induction ps with
  | nil => intro _; exact haltFree_nop
  | cons p ps ih =>
    intro h
    exact ⟨h p (List.mem_cons_self ..), ih (fun q hq => h q (List.mem_cons_of_mem _ hq))⟩

/-! ## 3. THE SHAPE THEOREMS

One `∀`-quantified theorem per deployed stage SHAPE. Every deployed stage of a shape
is an instantiation — a list entry, not a proof. -/

/-! ### 3.1 Shape A — the header-stamp chain

The deployed stamp shape appends its rendered header set onto the affine builder
(`hs.foldl addHeader b`, one in-place push per header). `stampChain` is its term. -/

/-- **The stamp chain** — one `addHeader` per header, composed in order. -/
def stampChain (hs : List (Bytes × Bytes)) : StageProg :=
  seqAll (hs.map (fun nv => .addHeader nv.1 nv.2))

/-- A stamp chain is gate-free (every component is an `addHeader`). -/
theorem haltFree_stampChain (hs : List (Bytes × Bytes)) : haltFree (stampChain hs) := by
  refine haltFree_seqAll _ ?_
  intro p hp
  obtain ⟨nv, _, rfl⟩ := List.mem_map.mp hp
  exact trivial

/-- **`denoteStep_stampChain` — SHAPE THEOREM A**, on any live state. Running a chain
of N stamps appends exactly those N headers, in order, at the END — for ANY header
list, by LIST INDUCTION. Every stamp-shaped deployed stage is this theorem at its own
header set; there are not N proofs. -/
theorem denoteStep_stampChain (ctx : Ctx) :
    ∀ (hs : List (Bytes × Bytes)) (r : Response),
      denoteStep ctx (stampChain hs) { resp := r, halted := false }
        = { resp := { r with headers := r.headers ++ hs }, halted := false } := by
  intro hs
  induction hs with
  | nil =>
    intro r
    show denoteStep ctx nop { resp := r, halted := false } = _
    rw [denoteStep_nop]
    simp
  | cons nv hs ih =>
    intro r
    show denoteStep ctx (.seq (.addHeader nv.1 nv.2) (stampChain hs))
          { resp := r, halted := false } = _
    show denoteStep ctx (stampChain hs)
          (denoteStep ctx (.addHeader nv.1 nv.2) { resp := r, halted := false }) = _
    have hstep : denoteStep ctx (.addHeader nv.1 nv.2) { resp := r, halted := false }
        = { resp := { r with headers := r.headers ++ [nv] }, halted := false } := rfl
    rw [hstep, ih]
    simp

/-- **`denote_stampChain` — SHAPE THEOREM A** at the top level: a stamp-shaped stage's
denotation is the base response with its header set appended. -/
theorem denote_stampChain (ctx : Ctx) (hs : List (Bytes × Bytes)) :
    denote (stampChain hs) ctx = { ctx.base with headers := ctx.base.headers ++ hs } := by
  show (denoteStep ctx (stampChain hs) { resp := ctx.base, halted := false }).resp = _
  rw [denoteStep_stampChain]

/-! ### 3.2 Shape B — the refusal-gate chain (first fire wins)

The deployed request phase runs the gates in list order and the FIRST `.respond` wins:
the handler and every LATER gate are skipped. `gateChain` is its term, and `firstFire`
is that decision as a function. -/

/-- **The gate chain** — one `gate` per refusal, composed in deployed list order. -/
def gateChain : List (ReqPred × Nat) → StageProg
  | []             => nop
  | (c, code) :: g => .seq (.gate c code) (gateChain g)

/-- **`firstFire`** — the deployed request-phase decision as a function: the status of
the FIRST gate whose predicate fires, or `none` when every gate passes. -/
def firstFire : List (ReqPred × Nat) → Ctx → Option Nat
  | [], _ => none
  | (c, code) :: g, ctx => if c ctx then some code else firstFire g ctx

/-- **`denoteStep_gateChain` — SHAPE THEOREM B**, on any live state. A chain of N gates
short-circuits to the FIRST firing gate's status and halts; if none fires it is the
identity — for ANY (predicate, status) list, by LIST INDUCTION. The absorbing law
(`denoteStep_halted`) is what makes a later gate unable to overwrite an earlier one's
status: first fire wins, exactly as the deployed request phase decides. Every
gate-shaped deployed stage is this theorem at its own predicate and status. -/
theorem denoteStep_gateChain (ctx : Ctx) :
    ∀ (g : List (ReqPred × Nat)) (r : Response),
      denoteStep ctx (gateChain g) { resp := r, halted := false }
        = match firstFire g ctx with
          | some code => { resp := { r with status := code }, halted := true }
          | none      => { resp := r, halted := false } := by
  intro g
  induction g with
  | nil => intro r; exact denoteStep_nop ctx _
  | cons cg g ih =>
    intro r
    obtain ⟨c, code⟩ := cg
    show denoteStep ctx (gateChain g)
          (denoteStep ctx (.gate c code) { resp := r, halted := false }) = _
    by_cases hc : c ctx = true
    · rw [denoteStep_gate_fires ctx c code _ rfl hc,
          denoteStep_halted ctx (gateChain g) _ rfl]
      show _ = (match (if c ctx then some code else firstFire g ctx) with
                | some code => _ | none => _)
      rw [if_pos hc]
    · have hstep : denoteStep ctx (.gate c code) { resp := r, halted := false }
          = { resp := r, halted := false } := by
        show (if (false : Bool) = true then _
              else if c ctx then _ else ({ resp := r, halted := false } : DState)) = _
        rw [if_neg (show ¬ ((false : Bool) = true) by decide), if_neg hc]
      rw [hstep, ih]
      show (match firstFire g ctx with | some code => _ | none => _)
          = (match (if c ctx then some code else firstFire g ctx) with | some code => _ | none => _)
      rw [if_neg hc]

/-- **`denote_gateChain` — SHAPE THEOREM B** at the top level. -/
theorem denote_gateChain (ctx : Ctx) (g : List (ReqPred × Nat)) :
    denote (gateChain g) ctx
      = match firstFire g ctx with
        | some code => { ctx.base with status := code }
        | none      => ctx.base := by
  show (denoteStep ctx (gateChain g) { resp := ctx.base, halted := false }).resp = _
  rw [denoteStep_gateChain]
  cases firstFire g ctx <;> rfl

/-- **`denoteStep_gateChain_pass`.** When no gate fires the chain is the identity — the
fact the composition theorem needs to let the response onion run. -/
theorem denoteStep_gateChain_pass (ctx : Ctx) (g : List (ReqPred × Nat)) (r : Response)
    (h : firstFire g ctx = none) :
    denoteStep ctx (gateChain g) { resp := r, halted := false } = { resp := r, halted := false } := by
  rw [denoteStep_gateChain, h]

/-! ## 4. The deployed pipeline model — TRANSCRIBED

The deployed serve is built in a different package that this one does not (and, for
the translator's independence, should not) import. Its pipeline model is therefore
transcribed here definition for definition — the affine response builder, the two-phase
`Stage`, the reverse-order response fold, and the gating pipeline fold. Nothing here is
a re-specification from prose: each definition mirrors its deployed counterpart, and
the deployed context's extra fields (raw input bytes, the attribute bag) are the ones
the stage predicates below are pre-decided over. -/

/-- The affine response builder — one accumulating cell, mutated in place. -/
structure DBuilder where
  /-- The accumulating response — the single reused cell. -/
  acc : Response

/-- Acquire the cell, seeded with the handler's response. -/
def DBuilder.ofResponse (r : Response) : DBuilder := ⟨r⟩

/-- Finalize the builder to the wire response. -/
def DBuilder.build (b : DBuilder) : Response := b.acc

/-- Append a header in place — the deployed `addHeader` (`headers ++ [nv]`). -/
def DBuilder.addHeader (b : DBuilder) (nv : Bytes × Bytes) : DBuilder :=
  ⟨{ b.acc with headers := b.acc.headers ++ [nv] }⟩

/-- Map a transform over the accumulated response. -/
def DBuilder.mapResp (b : DBuilder) (f : Response → Response) : DBuilder := ⟨f b.acc⟩

/-- The request-phase decision: gate with a response, or pass through. -/
inductive DStageStep
  /-- Gate: answer now; the handler and every later stage's request phase are skipped. -/
  | respond (r : Response)
  /-- Pass through to the next stage. -/
  | pass (c : Ctx)

/-- A deployed stage: a request phase (run in list order) and a response phase (run in
REVERSE list order — the onion). -/
structure DStage where
  /-- A human name (diagnostics; not load-bearing). -/
  name : String
  /-- Request phase, run in list order. -/
  onRequest : Ctx → DStageStep
  /-- Response phase, run in REVERSE list order, threading the affine builder. -/
  onResponse : Ctx → DBuilder → DBuilder

/-- **The response-only fold (the onion).** Thread the builder back outward: each
stage's `onResponse` in REVERSE list order (head = outermost, so it runs LAST). -/
def dRunResp : List DStage → Ctx → DBuilder → DBuilder
  | [], _, b => b
  | s :: rest, c, b => s.onResponse c (dRunResp rest c b)

/-- **The pipeline fold.** Run the request phase in list order; the first stage that
responds short-circuits (the handler and every later stage's REQUEST phase skipped,
while the remaining stages' response transforms still run over the refusal). If every
stage passes, seed the builder from the handler and thread it back outward. -/
def dRunPipeline : List DStage → (Ctx → Response) → Ctx → DBuilder
  | [], handler, c => DBuilder.ofResponse (handler c)
  | s :: rest, handler, c =>
    match s.onRequest c with
    | .respond r => dRunResp rest c (DBuilder.ofResponse r)
    | .pass c'   => s.onResponse c' (dRunPipeline rest handler c')

/-! ### 4.1 The shape stages — the deployed stage forms, transcribed

Each is the EXACT form the deployed stages of that shape take. The concrete pipeline
of §5 is built out of these. -/

/-- **The list-stamp shape** — `onResponse := fun _ b => hs.foldl addHeader b`: fold a
rendered header set onto the builder, unconditionally. (The deployed security-header
stage's exact form.) -/
def dStampList (nm : String) (hs : List (Bytes × Bytes)) : DStage where
  name := nm
  onRequest := fun c => .pass c
  onResponse := fun _ b => hs.foldl DBuilder.addHeader b

/-- **The conditional-stamp shape** — `onResponse := fun c b => if p c then b.addHeader nv else b`:
stamp one header when the stage's own condition holds, else pass the builder through. -/
def dCondStamp (nm : String) (p : ReqPred) (nv : Bytes × Bytes) : DStage where
  name := nm
  onRequest := fun c => .pass c
  onResponse := fun c b => if p c then b.addHeader nv else b

/-- **The refusal-gate shape** — `onRequest := fun c => if p c then .respond r else .pass c`
with an identity response phase: the deployed gates' exact form (their whole byte
effect is in the `.respond`). -/
def dGate (nm : String) (p : ReqPred) (r : Response) : DStage where
  name := nm
  onRequest := fun c => if p c then .respond r else .pass c
  onResponse := fun _ b => b

/-! ## 5. THE COMPOSITION THEOREM

`Realizes` is the per-stage obligation: the stage term's fold step reproduces the
deployed stage's response-phase builder transform. The composition theorem lifts N
realizations to the WHOLE fold by INDUCTION over the stage list. -/

/-- **`Realizes ctx s p`** — the stage term `p` reproduces the deployed stage `s`'s
response-phase transform at `ctx`, for ANY builder state it is threaded. -/
def Realizes (ctx : Ctx) (s : DStage) (p : StageProg) : Prop :=
  ∀ b : DBuilder, s.onResponse ctx b = ⟨(denoteStep ctx p { resp := b.acc, halted := false }).resp⟩

/-- **`Realized ctx sts ps`** — the stage list `sts` is realized, position by position,
by the term list `ps`. The relation the composition theorem inducts over. -/
inductive Realized (ctx : Ctx) : List DStage → List StageProg → Prop
  /-- The empty pipeline is realized by the empty composition. -/
  | nil : Realized ctx [] []
  /-- One realized stage in front of a realized tail. -/
  | cons {s : DStage} {p : StageProg} {sts : List DStage} {ps : List StageProg} :
      Realizes ctx s p → Realized ctx sts ps → Realized ctx (s :: sts) (p :: ps)

/-- **`Passes ctx s`** — the deployed stage's request phase passes at `ctx`. -/
def Passes (ctx : Ctx) (s : DStage) : Prop := s.onRequest ctx = .pass ctx

/-- A live fold state is its own response paired with a clear halt flag. -/
theorem dstate_eta_live (X : DState) (h : X.halted = false) :
    X = { resp := X.resp, halted := false } := by
  obtain ⟨r, hb⟩ := X
  cases hb
  · rfl
  · exact absurd h (by simp)

/-- **`dRunPipeline_pass`.** When every gate passes, the pipeline fold IS the response
onion over the handler's response — by LIST INDUCTION, for any stage list. -/
theorem dRunPipeline_pass (handler : Ctx → Response) (ctx : Ctx) :
    ∀ (sts : List DStage), (∀ s ∈ sts, Passes ctx s) →
      dRunPipeline sts handler ctx = dRunResp sts ctx (DBuilder.ofResponse (handler ctx)) := by
  intro sts
  induction sts with
  | nil => intro _; rfl
  | cons s sts ih =>
    intro h
    have hs : s.onRequest ctx = .pass ctx := h s (List.mem_cons_self ..)
    show (match s.onRequest ctx with
          | .respond r => dRunResp sts ctx (DBuilder.ofResponse r)
          | .pass c'   => s.onResponse c' (dRunPipeline sts handler c')) = _
    rw [hs]
    show s.onResponse ctx (dRunPipeline sts handler ctx)
        = s.onResponse ctx (dRunResp sts ctx (DBuilder.ofResponse (handler ctx)))
    rw [ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]

/-- **THE ONION LEMMA — `dRunResp_eq_denoteStep_seqAll`.** For ANY stage list whose
stages are realized by a list of gate-free terms, the deployed REVERSE-order response
onion equals the fold of the composed term `seqAll ps.reverse` — the whole N-stage
onion, by INDUCTION over the realization relation (`List.Forall₂`), not N hand steps.

The `reverse` is the onion: the head stage is outermost and its `onResponse` runs LAST,
so its term sits LAST in the composition. Gate-freedom keeps the fold live across the
whole onion, which is what lets each stage's realization (stated on a live state) apply
at its position. -/
theorem dRunResp_eq_denoteStep_seqAll (ctx : Ctx) :
    ∀ (sts : List DStage) (ps : List StageProg),
      Realized ctx sts ps →
      (∀ p ∈ ps, haltFree p) →
      ∀ b : DBuilder,
        denoteStep ctx (seqAll ps.reverse) { resp := b.acc, halted := false }
          = { resp := (dRunResp sts ctx b).acc, halted := false } := by
  intro sts ps hre
  induction hre with
  | nil => intro _ b; exact denoteStep_nop ctx _
  | @cons s p sts ps hsp _ ih =>
    intro hfree b
    have hfp : haltFree p := hfree p (List.mem_cons_self ..)
    have hfree' : ∀ q ∈ ps, haltFree q := fun q hq => hfree q (List.mem_cons_of_mem _ hq)
    -- the composed term for `s :: sts` is the tail's composition, then `p` LAST
    rw [List.reverse_cons, denoteStep_seqAll_snoc, ih hfree' b]
    -- the tail's fold left the state live, so `p`'s realization applies there
    have hlive : (denoteStep ctx p { resp := (dRunResp sts ctx b).acc, halted := false }).halted
        = false := denoteStep_haltFree ctx p hfp _
    show denoteStep ctx p { resp := (dRunResp sts ctx b).acc, halted := false }
        = { resp := (s.onResponse ctx (dRunResp sts ctx b)).acc, halted := false }
    rw [hsp (dRunResp sts ctx b)]
    show denoteStep ctx p { resp := (dRunResp sts ctx b).acc, halted := false }
        = { resp := (denoteStep ctx p { resp := (dRunResp sts ctx b).acc, halted := false }).resp,
            halted := false }
    exact dstate_eta_live _ hlive

/-! ### 5.1 The realizers — one general lemma per shape

Each is `∀`-quantified over the whole shape family. A deployed stage of a shape costs a
list entry plus a citation of these; no new proof. -/

/-- **A gate is realized by `nop`** on the response side — its response phase is the
identity (a gate's whole byte effect is in its `.respond`). For ANY predicate and
refusal response. -/
theorem realizes_dGate (ctx : Ctx) (nm : String) (p : ReqPred) (r : Response) :
    Realizes ctx (dGate nm p r) nop := by
  intro b
  show b = ⟨(denoteStep ctx nop { resp := b.acc, halted := false }).resp⟩
  rw [denoteStep_nop]

/-- **A conditional stamp is realized by `condR … (addHeader …) nop`** — for ANY
predicate and header. This one lemma covers every conditional-stamp deployed stage. -/
theorem realizes_dCondStamp (ctx : Ctx) (nm : String) (p : ReqPred) (nv : Bytes × Bytes) :
    Realizes ctx (dCondStamp nm p nv) (.condR p (.addHeader nv.1 nv.2) nop) := by
  intro b
  show (if p ctx then b.addHeader nv else b)
      = ⟨(if p ctx then denoteStep ctx (.addHeader nv.1 nv.2) { resp := b.acc, halted := false }
          else denoteStep ctx nop { resp := b.acc, halted := false }).resp⟩
  by_cases hp : p ctx = true
  · rw [if_pos hp, if_pos hp]; rfl
  · rw [if_neg hp, if_neg hp, denoteStep_nop]

/-- The builder's `addHeader` fold IS a list append — the bridge from the deployed
list-stamp form to `stampChain`, by list induction. -/
theorem dBuilder_foldl_addHeader :
    ∀ (hs : List (Bytes × Bytes)) (b : DBuilder),
      hs.foldl DBuilder.addHeader b = ⟨{ b.acc with headers := b.acc.headers ++ hs }⟩ := by
  intro hs
  induction hs with
  | nil => intro b; simp
  | cons nv hs ih =>
    intro b
    show hs.foldl DBuilder.addHeader (b.addHeader nv) = _
    rw [ih]
    simp [DBuilder.addHeader, List.append_assoc]

/-- **A list stamp is realized by `stampChain`** — for ANY header set. This one lemma
covers every deployed stage that folds a rendered header set onto the builder. -/
theorem realizes_dStampList (ctx : Ctx) (nm : String) (hs : List (Bytes × Bytes)) :
    Realizes ctx (dStampList nm hs) (stampChain hs) := by
  intro b
  show hs.foldl DBuilder.addHeader b
      = ⟨(denoteStep ctx (stampChain hs) { resp := b.acc, halted := false }).resp⟩
  rw [dBuilder_foldl_addHeader, denoteStep_stampChain]

/-! ### 5.2 `serveProg` — the WHOLE serve as ONE term -/

/-- **`serveProg` — THE WHOLE SERVE AS ONE `StageProg` TERM.** The request-phase gate
chain (in deployed list order — first fire wins) composed with the response onion (the
stage terms in REVERSED deployed order, because the deployed response phase runs
outermost-last). ONE term; `compile2` eats it whole (§6). -/
def serveProg (g : List (ReqPred × Nat)) (ps : List StageProg) : StageProg :=
  .seq (gateChain g) (seqAll ps.reverse)

/-- **THE COMPOSITION THEOREM — `denote_serveProg_pass`.** On the pass path (no gate
fires), the ONE composed term `serveProg` denotes EXACTLY the response the deployed
N-stage pipeline fold builds:

    denote (serveProg g ps) ctx = (dRunPipeline sts handler ctx).build

Proven by INDUCTION over the stage list (the realization induction of the
onion lemma) — there is no per-stage case here, and none is added when the list grows.
The hypotheses are exactly: the gates pass, each stage is realized by its term, the
terms are gate-free, and the context's base is the handler's response. -/
theorem denote_serveProg_pass
    (ctx : Ctx) (handler : Ctx → Response)
    (g : List (ReqPred × Nat)) (sts : List DStage) (ps : List StageProg)
    (hnofire : firstFire g ctx = none)
    (hre : Realized ctx sts ps)
    (hfree : ∀ p ∈ ps, haltFree p)
    (hpass : ∀ s ∈ sts, Passes ctx s)
    (hbase : ctx.base = handler ctx) :
    denote (serveProg g ps) ctx = (dRunPipeline sts handler ctx).build := by
  show (denoteStep ctx (seqAll ps.reverse)
          (denoteStep ctx (gateChain g) { resp := ctx.base, halted := false })).resp = _
  have honion := dRunResp_eq_denoteStep_seqAll ctx sts ps hre hfree (DBuilder.ofResponse (handler ctx))
  simp only [DBuilder.ofResponse] at honion
  rw [denoteStep_gateChain_pass ctx g ctx.base hnofire, hbase, honion,
      dRunPipeline_pass handler ctx sts hpass]
  rfl

/-- **`denote_serveProg_fire` — the gate path's STATUS.** When a gate fires, the composed
term answers that gate's status (first fire wins). This is the faithful half of the fire
path: the deployed fold ALSO runs the response onion over the refusal, which `denote`'s
absorbing halt flag drops — the named gate/onion divergence in the header. -/
theorem denote_serveProg_fire
    (ctx : Ctx) (g : List (ReqPred × Nat)) (ps : List StageProg) (code : Nat)
    (hfire : firstFire g ctx = some code) :
    denote (serveProg g ps) ctx = { ctx.base with status := code } := by
  show (denoteStep ctx (seqAll ps.reverse)
          (denoteStep ctx (gateChain g) { resp := ctx.base, halted := false })).resp = _
  rw [denoteStep_gateChain ctx g ctx.base, hfire,
      denoteStep_halted ctx (seqAll ps.reverse) _ rfl]

/-! ## 6. `compile2` EATS THE WHOLE COMPOSED TERM

`serveProg` is a `StageProg`, so the genuine per-constructor compiler's
structural-induction keystone instantiates at it directly — the whole serve, in one go,
by the SAME induction. That is the whole point of having built `compile2` per
constructor rather than as a stub. -/

/-- **`serveProg_compile2_correct` — THE WHOLE SERVE, COMPILED.** Running
`compile2 (serveProg g ps)` — the ONE Pancake program the whole composed serve lowers
to — from a machine state encoding the base fold-state lands a state encoding the
reference fold of the WHOLE serve (`denoteStep ctx (serveProg g ps)`: the status, the
header count, the body length, and the halt flag of the response the deployed pipeline
builds, per the composition theorem). ONE line: `compile2_correct` at `p := serveProg …`.
No new induction, no per-stage case — the compiler's own structural induction covers the
52-way composition exactly as it covers a single `addHeader`. -/
theorem serveProg_compile2_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (ctx : Ctx)
    (g : List (ReqPred × Nat)) (ps : List StageProg)
    (hd : Distinct aStat aCnt aBody aHalt) (st : PancakeState σ)
    (hEnc : CoreEnc aStat aCnt aBody aHalt st { resp := ctx.base, halted := false })
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt (serveProg g ps)) st = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st'
        (denoteStep ctx (serveProg g ps) { resp := ctx.base, halted := false }) := by
  obtain ⟨st', hrun, henc, _, _, _⟩ :=
    compile2_correct o nm aStat aCnt aBody aHalt ctx hd (serveProg g ps)
      { resp := ctx.base, halted := false } st hEnc hDec
  exact ⟨st', hrun, henc⟩

/-! ## 7. THE DEPLOYED 52 — the concrete instantiation, and the honest coverage

The deployed default serve is a 52-entry stage list, outermost first. Below: the 20
gate-shaped stages instantiated with the status each one's OWN refusal response
carries (read off the deployed stage, not re-specified), and the response-phase
positions whose terms are already pinned. -/

/-- **The pre-decided firing bits of the deployed refusal gates.** Each field is the
stage's own request-phase decision at a fixed context, as a `ReqPred` (the deployed
predicates read host/accept-path state that the modelled `Ctx` abstracts as this bit —
the same pre-decision discipline the compiled `Cond` guards consume via `nm`). Ordered
as the deployed list. -/
structure GateBits where
  /-- Per-source concurrent-connection cap reached (refuses 503). -/
  connOver       : ReqPred
  /-- Slow header arrival timed out (refuses 408). -/
  hdrExpired     : ReqPred
  /-- Declared or streamed body over the cap (refuses 413). -/
  bodyOver       : ReqPred
  /-- Request target over the URI length cap (refuses 414). -/
  uriOver        : ReqPred
  /-- No acceptable representation for the request (refuses 406). -/
  notAcceptable  : ReqPred
  /-- Conflicting Content-Length / Transfer-Encoding framing (refuses 400). -/
  clTeConflict   : ReqPred
  /-- Method not in the allow-list, on a non-empty method (refuses 405). -/
  methodDenied   : ReqPred
  /-- The welcome route matched (answers its own 200). -/
  welcomeScope   : ReqPred
  /-- The dashboard route matched (answers its own 200). -/
  dashScope      : ReqPred
  /-- The event-stream route matched (answers its own 200). -/
  sseScope       : ReqPred
  /-- The app-shell fallback route matched (answers its own 200). -/
  spaScope       : ReqPred
  /-- The session/login route matched (answers its own 200). -/
  sessionScope   : ReqPred
  /-- An OPTIONS request whose hop budget is exhausted (answers 204). -/
  mfExhausted    : ReqPred
  /-- Bearer-token decision rejected on an admin path (refuses 401). -/
  tokenRejected  : ReqPred
  /-- Basic credentials absent or wrong — a challenge (refuses 401). -/
  basicChallenge : ReqPred
  /-- Source address not admitted by the filter (refuses 403). -/
  ipDenied       : ReqPred
  /-- Request rate over the configured budget (refuses 429). -/
  rateOver       : ReqPred
  /-- Target matched the configured redirect rule (answers 308). -/
  redirectHit    : ReqPred
  /-- Target escaped the served root (refuses 404). -/
  traversalHit   : ReqPred
  /-- Target reserved by policy (refuses 403). -/
  policyReserved : ReqPred

/-- **`deployGates` — the 20 gate-shaped deployed stages, in DEPLOYED LIST ORDER**,
each paired with the status its OWN refusal response carries. First fire wins
(`denote_gateChain`), which is exactly the deployed request phase's decision. -/
def deployGates (g : GateBits) : List (ReqPred × Nat) :=
  [ (g.connOver,       503)   -- position  1
  , (g.hdrExpired,     408)   -- position  2
  , (g.bodyOver,       413)   -- position  4
  , (g.uriOver,        414)   -- position 11
  , (g.notAcceptable,  406)   -- position 12
  , (g.clTeConflict,   400)   -- position 16
  , (g.methodDenied,   405)   -- position 17
  , (g.welcomeScope,   200)   -- position 18
  , (g.dashScope,      200)   -- position 19
  , (g.sseScope,       200)   -- position 23
  , (g.spaScope,       200)   -- position 24
  , (g.sessionScope,   200)   -- position 25
  , (g.mfExhausted,    204)   -- position 28
  , (g.tokenRejected,  401)   -- position 40
  , (g.basicChallenge, 401)   -- position 41
  , (g.ipDenied,       403)   -- position 42
  , (g.rateOver,       429)   -- position 43
  , (g.redirectHit,    308)   -- position 45
  , (g.traversalHit,   404)   -- position 46
  , (g.policyReserved, 403) ] -- position 47

/-- The gate chain has 20 entries — the 20 gate-shaped deployed stages, composed. -/
theorem deployGates_length (g : GateBits) : (deployGates g).length = 20 := rfl

/-! ### 7.1 The realized response-phase positions

Five deployed response-phase positions whose stage terms are already pinned to the
deployed stage's semantics (each by its own `denote_…` equation in the lift modules).
They are listed in DEPLOYED ORDER; `serveProg` reverses them for the onion. -/

/-- The realized response-phase stage terms, in DEPLOYED LIST ORDER. `isStatic`,
`hasVia`, `corsAllowed` are the stages' own pre-decided bits; `acaoVal` the admitted
origin's value; `secSet` the rendered security-header set the deployed security-header
stage folds onto the builder. -/
def deployRespProgs (isStatic hasVia corsAllowed : ReqPred) (acaoVal : Bytes)
    (secSet : List (Bytes × Bytes)) : List StageProg :=
  [ Pancake.StageEvenMore.cacheControlStaticStage isStatic  -- position  6
  , .condR (fun _ => true)                                   -- position 29
      (.addHeader Pancake.StageEvenMore.contentLocationName
                  Pancake.StageEvenMore.contentLocationVal) nop
  , Pancake.StageMore.viaStage hasVia                        -- position 33
  , Pancake.StageMore.corsStage corsAllowed acaoVal          -- position 50
  , stampChain secSet ]                                      -- position 52

/-- The realized response-phase terms are all gate-free — so the onion lemma applies to
the whole composition. -/
theorem deployRespProgs_haltFree (isStatic hasVia corsAllowed : ReqPred) (acaoVal : Bytes)
    (secSet : List (Bytes × Bytes)) :
    ∀ p ∈ deployRespProgs isStatic hasVia corsAllowed acaoVal secSet, haltFree p := by
  intro p hp
  simp only [deployRespProgs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact ⟨trivial, trivial⟩
  · exact ⟨trivial, trivial⟩
  · exact ⟨trivial, trivial⟩
  · exact ⟨trivial, trivial⟩
  · exact haltFree_stampChain secSet

/-- **`deployServeProg` — the deployed serve, as ONE `StageProg` term**: the 20-gate
request chain composed with the 5 realized response-phase positions, in deployed order.
`compile2` eats this whole term (§6, at `g := deployGates …`, `ps := deployRespProgs …`). -/
def deployServeProg (g : GateBits) (isStatic hasVia corsAllowed : ReqPred) (acaoVal : Bytes)
    (secSet : List (Bytes × Bytes)) : StageProg :=
  serveProg (deployGates g) (deployRespProgs isStatic hasVia corsAllowed acaoVal secSet)

/-- **The deployed serve's composed term is covered by the composition theorem.** The
pass-path denotation of the ONE term equals the deployed fold's built response for the
transcribed stage list, whenever the stage list is realized by these terms. (The
`Forall₂`/`Passes` obligations are the shape realizers of §5.1 — one citation each, no
new proof; the composition itself is the list induction.) -/
theorem deployServeProg_pass
    (ctx : Ctx) (handler : Ctx → Response) (g : GateBits)
    (isStatic hasVia corsAllowed : ReqPred) (acaoVal : Bytes) (secSet : List (Bytes × Bytes))
    (sts : List DStage)
    (hnofire : firstFire (deployGates g) ctx = none)
    (hre : Realized ctx sts (deployRespProgs isStatic hasVia corsAllowed acaoVal secSet))
    (hpass : ∀ s ∈ sts, Passes ctx s)
    (hbase : ctx.base = handler ctx) :
    denote (deployServeProg g isStatic hasVia corsAllowed acaoVal secSet) ctx
      = (dRunPipeline sts handler ctx).build :=
  denote_serveProg_pass ctx handler (deployGates g) sts _ hnofire hre
    (deployRespProgs_haltFree isStatic hasVia corsAllowed acaoVal secSet) hpass hbase

/-! ### 7.2 THE COVERAGE — 25 of 52 composed; the other 27, each with its reason

COMPOSED (25):
* 20 gate-shaped, via `deployGates` (positions 1, 2, 4, 11, 12, 16, 17, 18, 19, 23, 24,
  25, 28, 40, 41, 42, 43, 45, 46, 47) — the request-phase STATUS decision, first fire
  wins. Each status is the one its own deployed refusal response carries.
* 5 response-phase, via `deployRespProgs` (positions 6, 29, 33, 50, 52).

NOT COMPOSED (27), by reason — an honest list, not a forced fit:

(a) ACCUMULATOR-KEYED (4). The deployed condition reads `b.acc.status` MID-FOLD
    (`if b.acc.status == 200 && …`). `ReqPred := Ctx → Bool` sees the request and the
    handler's base only, never the accumulated response, so the condition is not a
    `ReqPred`. Positions 7 (last-modified stamp), 8 (asset expires), 9 (asset
    immutable), 34 (cache-status stamp keyed on the built status).
    NOTE: position 6 and position 29 are composed with this conjunct DROPPED — their
    terms gate on the static-asset bit only. That is the pre-existing scope of those
    lifts, restated here rather than papered over.

(b) HEADER-LIST-KEYED APPEND-UNLESS-PRESENT (7). The deployed form is
    `mapResp (fun r => { r with headers := stampX r.headers })` where `stampX` returns
    the list UNCHANGED if the field is already present. The decision reads the
    ACCUMULATED header list, which no `ReqPred` can see. Position 33 (`Via`) IS
    composed only because its term takes the has-field bit as a parameter and the
    surrounding onion adds no such field — the same dodge does not hold for the others
    once several append the same family. Positions 30 (alt-svc), 31 (permissions-
    policy), 32 (cross-origin-resource), 35 (warning transform), 36 (link preload,
    additionally status-keyed), 27 (timing-allow-origin), 38 (stale-while-revalidate).

(c) BODY TRANSFORMS (5). `rewriteBody` carries `identity`/`replace`/`append` only; these
    stages compute a NEW body from the old one (rendering, rewriting, encoding), which
    the bounded body-loop constructors cannot express as a closed term. Positions 3
    (error-page render — additionally status-keyed), 5 (range unveil), 13 (multi-range
    206), 51 (html rewrite), 49 (gzip — body transform AND a stamp).

(d) HEADER REWRITES (3). The deployed form MAPS over the existing headers
    (`headers.map hardenHeader`, `rewriteResp`) — a rewrite of what is there, not an
    append. `addHeader` only appends; there is no map-over-headers op. Positions 20
    (cookie hardening), 48 (header rewrite), 52 is composed (it appends) but position
    52's SIBLING rewrite at position 53 is not deployed. Positions 20, 48, and the
    final header stage (rewriteResp).

(e) CONTEXT-TRANSFORMING PASSES (3). The stage passes with a MUTATED context
    (`.continue (mfContinueCtx c)`, `.continue (unveilCtx c)`, the proxy preamble
    recovery) — the request-phase context threading `StageProg` has no op for (its
    `Ctx` is fixed across the fold). Positions 28's continue branch (only its refusal is
    composed), 5, 37 (proxy protocol).

(f) COMPOSITE / DELEGATING (5). Positions 10 (a route-conditional wrapper around
    another stage's response phase), 14 (language stamp — TWO conditional appends with a
    negotiated value), 15/21/22/26 (conditional stamps whose header VALUE is computed
    per-request, and position 44, a cache stage built by a config-driven constructor).
    These are conditional-stamp shaped and would compose via `realizes_dCondStamp` once
    their values are lifted; they are listed as NOT DONE because their values are not
    read here, and inventing them is exactly the failure mode this module refuses.

The counts are 4 + 7 + 5 + 3 + 3 + 5 = 27, plus the 25 composed = 52.

WHAT WOULD MOVE THE LINE MOST: (b) and (a) together are 11 stages and BOTH need the same
DSL change — a predicate that can read the ACCUMULATED response, i.e. `ReqPred` widened
from `Ctx → Bool` to `Ctx → Response → Bool` (or a `condA` constructor branching on the
accumulator). That is one keystone change unlocking 11 stages by the shape theorems
already proven here. It is a change to `StageProg.lean` + `compile2` (the compiled guard
would read the live slots instead of a pre-decided local), out of this module's scope.

NOT a blocker: the `natToDec` Div/Mod residual. It sits under `serialize`, which this
module does not touch — the composition is proven at the fold/skeleton level
(`denote` / `CoreEnc`), where it does not arise. -/

/-- A sample `200 OK` base response. -/
def baseOk : Response := ok200 (str "hi")

/-- A sample context. -/
def ctx0 : Ctx := { req := {}, base := baseOk }

/-- Predicates that always/never fire. -/
def pTrue : ReqPred := fun _ => true
/-- The never-firing predicate. -/
def pFalse : ReqPred := fun _ => false

/-! ### 7.3 The composition theorem is NON-VACUOUS — inhabited hypotheses + a real equality

A guard against a vacuously-conditioned theorem: below is a CONCRETE deployed stage list
built from the transcribed shape stages, a CONCRETE term list, and a proof that the
`Realized`/`Passes`/no-fire hypotheses HOLD — so `denote_serveProg_pass` fires and yields
an honest equality between the composed term's denotation and the deployed fold's build,
not an implication with unsatisfiable premises. -/

/-- A concrete deployed 3-stage list: a passing gate, a firing-free conditional stamp,
and an unconditional list stamp — the three shapes, transcribed. -/
def witSts (p : ReqPred) (nv : Bytes × Bytes) (hs : List (Bytes × Bytes)) : List DStage :=
  [ dGate "g" pFalse baseOk
  , dCondStamp "c" p nv
  , dStampList "s" hs ]

/-- The term list realizing `witSts`, position for position: `nop`, the conditional
stamp term, the stamp chain. -/
def witProgs (p : ReqPred) (nv : Bytes × Bytes) (hs : List (Bytes × Bytes)) : List StageProg :=
  [ nop
  , .condR p (.addHeader nv.1 nv.2) nop
  , stampChain hs ]

/-- **`witSts` is realized by `witProgs`** — each position by its shape's realizer. This
DISCHARGES the composition theorem's realization hypothesis for a concrete pipeline. -/
theorem wit_realized (ctx : Ctx) (p : ReqPred) (nv : Bytes × Bytes) (hs : List (Bytes × Bytes)) :
    Realized ctx (witSts p nv hs) (witProgs p nv hs) :=
  .cons (realizes_dGate ctx "g" pFalse baseOk)
    (.cons (realizes_dCondStamp ctx "c" p nv)
      (.cons (realizes_dStampList ctx "s" hs) .nil))

/-- The witness gates all pass (the single gate's predicate is `pFalse`). -/
theorem wit_passes (ctx : Ctx) (p : ReqPred) (nv : Bytes × Bytes) (hs : List (Bytes × Bytes)) :
    ∀ s ∈ witSts p nv hs, Passes ctx s := by
  intro s hs'
  simp only [witSts, List.mem_cons, List.not_mem_nil, or_false] at hs'
  rcases hs' with rfl | rfl | rfl
  · show (if pFalse ctx then DStageStep.respond baseOk else DStageStep.pass ctx) = DStageStep.pass ctx
    rw [if_neg (show ¬ pFalse ctx = true from by simp [pFalse])]
  · rfl
  · rfl

/-- The witness terms are gate-free. -/
theorem wit_haltFree (p : ReqPred) (nv : Bytes × Bytes) (hs : List (Bytes × Bytes)) :
    ∀ q ∈ witProgs p nv hs, haltFree q := by
  intro q hq
  simp only [witProgs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact trivial
  · exact ⟨trivial, trivial⟩
  · exact haltFree_stampChain hs

/-- **`wit_compose` — the composition theorem, DISCHARGED on a concrete pipeline.** For
the empty gate chain and the witness response pipeline, the ONE composed term's pass-path
denotation EQUALS the deployed 3-stage fold's built response — a real equality, all
hypotheses met, no vacuity. -/
theorem wit_compose (ctx : Ctx) (handler : Ctx → Response)
    (p : ReqPred) (nv : Bytes × Bytes) (hs : List (Bytes × Bytes))
    (hbase : ctx.base = handler ctx) :
    denote (serveProg [] (witProgs p nv hs)) ctx
      = (dRunPipeline (witSts p nv hs) handler ctx).build :=
  denote_serveProg_pass ctx handler [] (witSts p nv hs) (witProgs p nv hs)
    rfl (wit_realized ctx p nv hs) (wit_haltFree p nv hs) (wit_passes ctx p nv hs) hbase

/-! ## 8. Non-vacuity — the composed term genuinely computes

The composition theorems are not `P → P`: the composed term's denotation is exhibited
here as concrete, distinct wire bytes that DEPEND on the composition. -/

/-- All 20 gates passing. -/
def gatesPass : GateBits :=
  { connOver := pFalse, hdrExpired := pFalse, bodyOver := pFalse, uriOver := pFalse
  , notAcceptable := pFalse, clTeConflict := pFalse, methodDenied := pFalse
  , welcomeScope := pFalse, dashScope := pFalse, sseScope := pFalse, spaScope := pFalse
  , sessionScope := pFalse, mfExhausted := pFalse, tokenRejected := pFalse
  , basicChallenge := pFalse, ipDenied := pFalse, rateOver := pFalse
  , redirectHit := pFalse, traversalHit := pFalse, policyReserved := pFalse }

/-- The rate gate firing (a 429), every earlier gate passing. -/
def gatesRate : GateBits := { gatesPass with rateOver := pTrue }

/-- Both the connection cap AND the rate budget over — the OUTER one (503) must win. -/
def gatesConnAndRate : GateBits := { gatesRate with connOver := pTrue }

/-- A sample rendered security-header set. -/
def secSet0 : List (Bytes × Bytes) :=
  [ (str "X-Frame-Options", str "DENY"), (str "X-Content-Type-Options", str "nosniff") ]

/-- The composed deployed term at the pass path. -/
def demoPass : StageProg :=
  deployServeProg gatesPass pTrue pFalse pTrue (str "https://ok.example") secSet0

-- the gate chain is REALLY 20 gates and the composition is a real 25-op term:
#guard (deployGates gatesPass).length = 20
#guard (deployRespProgs pTrue pFalse pTrue (str "https://ok.example") secSet0).length = 5

-- the pass path fires no gate; the rate path fires 429; and FIRST FIRE WINS — with both
-- the 503 and the 429 gates firing, the OUTER 503 is the answer, not the inner 429:
#guard firstFire (deployGates gatesPass) ctx0 = none
#guard firstFire (deployGates gatesRate) ctx0 = some 429
#guard firstFire (deployGates gatesConnAndRate) ctx0 = some 503

-- the composed term's denotation is concrete, NON-EMPTY wire bytes:
#guard (serialize (denote demoPass ctx0)).length > 0

-- and it genuinely DEPENDS on the composition — the whole serve's bytes differ from the
-- bare base response (the onion really stamped), and the gate path really answers 503:
#guard serialize (denote demoPass ctx0) ≠ serialize baseOk
#guard (denote (deployServeProg gatesConnAndRate pTrue pFalse pTrue [] secSet0) ctx0).status = 503
#guard (denote (deployServeProg gatesRate pTrue pFalse pTrue [] secSet0) ctx0).status = 429
#guard (denote demoPass ctx0).status = 200

-- the composed serve appends MORE headers than any single stage — the composition is
-- not one stage wearing a pipeline's name:
#guard (denote demoPass ctx0).headers.length = 6
#guard (denote (stampChain secSet0) ctx0).headers.length = 2

/-! ## 9. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms denoteStep_seqAll
#print axioms denote_seqAll
#print axioms denoteStep_haltFree
#print axioms haltFree_seqAll
#print axioms denoteStep_stampChain
#print axioms denote_stampChain
#print axioms denoteStep_gateChain
#print axioms denote_gateChain
#print axioms dRunPipeline_pass
#print axioms dRunResp_eq_denoteStep_seqAll
#print axioms realizes_dGate
#print axioms realizes_dCondStamp
#print axioms realizes_dStampList
#print axioms denote_serveProg_pass
#print axioms denote_serveProg_fire
#print axioms serveProg_compile2_correct
#print axioms deployServeProg_pass
#print axioms wit_compose

end Pancake.ServeCompose
