/-
  Pancake/ProofProducing.lean — make Stack L a GENUINE PROOF-PRODUCING TRANSLATOR
  over the loop-free serve-stage grammar (Gate-A plan steps P1 + P2), ADDITIVELY
  over Pancake/EmitCorrectCompose.lean (nothing there is modified or re-proven).

  BACKGROUND. `EmitCorrectCompose.emit_correct_generic` is the once-and-for-all
  compile-correctness theorem `∀ st, WF o st → Refines o (emit st) (denote st)`
  over the loop-free grammar `{prim(skip/assign/store), seq, cond}`. It is the
  PROOF-PRODUCING SHAPE, but `WF` was discharged BY HAND per stage (see
  `demoServe_emit_correct`, which hand-threads `refines_store`/`refines_assign`).
  That makes it "emitter + separate hand proofs", not yet "run the translator, get
  code + a machine-checked certificate".

  THIS FILE closes P2 (automate WF) and P1 (the proof-producing wrapper):

   * P2 — `wf_auto`, a tactic that DISCHARGES the `WF` side-condition for a
     CONCRETE stage with NO hand input: it structurally decomposes every `seq`/
     `cond` node, applies the §1 leaf-refinement lemmas (`wf_skip`/`wf_assign`/
     `wf_store`) at the leaves, and closes the residual `eval` side-conditions
     (closed expressions by `rfl`/`decide`; bound-local reads by the enclosing
     input-scoping fact in context). Built on SMART CONSTRUCTORS (`assignPrim`,
     `storePrim`, `skipPrim`) so each leaf's shape — hence its matching §1 lemma —
     is recognised syntactically.

   * P1 — `translateCert` / `emitServe` + `emitServe_correct`: the proof-producing
     wrapper. `translateCert o st (by wf_auto)` RETURNS the emitted `PancakeProg`
     PAIRED WITH its `Refines`-certificate; for a concrete loop-free stage the WF
     hypothesis is produced by `wf_auto` with zero hand lines — so translating the
     stage PRODUCES its certificate.

   * DEMONSTRATION on a REAL loop-free serve stage — `redirectStatusStage`, the
     `Redirect.Code.status` RFC-9110 §15.4 status pick that is position 6 of
     drorb's `deployStagesFull2` (`~/dev/drorb/Reactor/Stage/Redirect.lean`,
     `Redirect.Code.status`; compiled to machine code in isolation by the HOL4
     C17 probe). It is genuinely loop-free (a total 4-way branch, no `While`). Its
     certificate is AUTO-PRODUCED by `wf_auto`, given ONE named input-scoping
     precondition (the `code` local is bound — exactly C17's `redirectRel`
     hypothesis / the A0 input contract), which is DATA, not a hand proof.

  HONEST SCOPE. `WF`'s leaf/guard obligations have the form `∀ s, eval s e =
  some (…)`. For CLOSED expressions this is unconditionally `decide`-able and
  `wf_auto` closes it with zero hypotheses (`closedDemo`). For a data-dependent
  guard that READS a local (the real redirect reads `code`), the obligation
  CANNOT hold for states where that local is unbound (`eval` returns `none`),
  so it needs the input-scoping precondition as an explicit hypothesis — this is
  NOT a decidability failure but the irreducible A0/input contract, named exactly
  as the deployed HOL4 proof names it. `wf_auto` discharges everything ELSE, and
  reduces to that single named fact. See §4 for the precise statement.

  Loop-free ONLY (`While` is excluded from the grammar, per §6 of
  EmitCorrectCompose). This is Stack L (the Lean model of Pancake) — NO byte
  claims here (P5/Rung-2 is later).

  ASSURANCE. `#print axioms` on every new theorem is ⊆ {propext, Quot.sound,
  Classical.choice}, 0 `sorry`. Build: `Pancake/build_proofproducing.sh`.
-/
import Pancake.EmitCorrectCompose
import Pancake.EmitCorrectClock

namespace Pancake.ProofProducing

open Pancake Pancake.EmitCorrect Pancake.EmitCorrectCompose

variable {σ : Type}

/-! ## 1. Smart constructors for verified primitive leaves

Each smart constructor builds a `Prim` whose `prog` and `den` are in the exact
shape the matching §1 refinement lemma concludes — so a `wf_*` lemma applies to
`WF o (.prim (…Prim …))` by syntactic unification, with the residual `eval`
side-conditions as the ONLY new goals. This is what lets `wf_auto` recognise a
leaf's kind from its head constructor. -/

/-- SKIP leaf: the identity stage. -/
def skipPrim : Prim σ := { prog := .skip, den := fun s => s }

/-- ASSIGN leaf: `x := e`, where `e` evaluates to `f s` in every (in-scope)
state. `den` is the local-update transformer — the shape `refines_assign`
concludes. -/
def assignPrim (x : String) (e : PancakeExp) (f : PancakeState σ → Value) : Prim σ :=
  { prog := .assign x e
    den  := fun s => { s with locals := setLocal s.locals x (f s) } }

/-- STORE leaf: `st dst, src`, writing the word `val s` at address `addr s`. -/
def storePrim (dst src : PancakeExp) (addr val : PancakeState σ → Word) : Prim σ :=
  { prog := .store dst src
    den  := fun s => { s with memory := fun k => if k = addr s then val s else s.memory k } }

/-- The memory after a single ALIGNED byte-store (the `some` branch of
`mem_store_byte`): overwrite the low-8-bit byte `b` at the byte position of `adr`
inside the aligned word `byteAlign adr`, every other word unchanged. This is
exactly the `memStoreByte` success image. -/
def putByteMem (m : Word → Word) (be : Bool) (adr : Word) (b : BitVec 8) : Word → Word :=
  fun k => if k = byteAlign adr then setByte adr b (m (byteAlign adr)) be else m k

/-- STORE-BYTE leaf: `st8 dst, src`, writing the LOW BYTE (`setWidth 8`) of the
source word `val s` at the destination address `adr s` via `mem_store_byte`. The
byte-write analog of `storePrim`; its extra obligation is the ALIGNED
memory-domain precondition (`byteAlign (adr s) ∈ memaddrs`) rather than the raw
address, since `mem_store_byte` writes into the aligned word. -/
def storeBytePrim (dst src : PancakeExp) (adr val : PancakeState σ → Word) : Prim σ :=
  { prog := .storeByte dst src
    den  := fun s =>
      { s with memory := putByteMem s.memory s.be (adr s) ((val s).setWidth 8) } }

/-! ## 2. Per-constructor WF lemmas (the leaf refinements, once)

`WF o (.prim p)` unfolds to `Refines o p.prog p.den`. For each smart constructor
that is DEFINITIONALLY the corresponding §1 lemma's conclusion, so the lemma IS
the WF proof — no new metatheory. These are the building blocks `wf_auto` fires. -/

theorem wf_skip (o : Oracle σ) : WF o (.prim (skipPrim (σ := σ))) :=
  refines_skip o

theorem wf_assign (o : Oracle σ) (x : String) (e : PancakeExp) (f : PancakeState σ → Value)
    (hf : ∀ s, eval s e = some (f s)) :
    WF o (.prim (assignPrim x e f)) :=
  refines_assign o x e f hf

theorem wf_store (o : Oracle σ) (dst src : PancakeExp) (addr val : PancakeState σ → Word)
    (haddr : ∀ s, eval s dst = some (addr s)) (hval : ∀ s, eval s src = some (val s))
    (hin : ∀ s : PancakeState σ, s.memaddrs (addr s) = true) :
    WF o (.prim (storePrim dst src addr val)) :=
  refines_store o dst src addr val haddr hval hin

/-- WF for a BYTE-STORE leaf: given the address and source evaluate and the
ALIGNED destination is in the model's address domain, the emitted `StoreByte`
refines the single aligned byte-update `putByteMem`. This is `refines_store`'s
byte analog; the `hin` premise is the per-slot memory-domain precondition that
`wf_auto` must discharge for every byte of a write region. NON-VACUOUS: the
post-state's memory is pinned to the `mem_store_byte` image (`evaluate_storeByte`
threads `w2w = setWidth 8`), not a tautology. -/
theorem wf_storeByte (o : Oracle σ) (dst src : PancakeExp) (adr val : PancakeState σ → Word)
    (haddr : ∀ s, eval s dst = some (adr s)) (hval : ∀ s, eval s src = some (val s))
    (hin : ∀ s : PancakeState σ, s.memaddrs (byteAlign (adr s)) = true) :
    WF o (.prim (storeBytePrim dst src adr val)) := by
  intro s
  refine ⟨?_, rfl⟩
  have hm : memStoreByte s.memory s.memaddrs s.be (adr s) ((val s).setWidth 8)
      = some (putByteMem s.memory s.be (adr s) ((val s).setWidth 8)) := by
    unfold memStoreByte putByteMem; rw [if_pos (hin s)]
  exact evaluate_storeByte o s (haddr s) (hval s) hm

/-- REGION → SLOT: from a single base-region-in-domain fact
`∀ s k, k < N → byteAlign (base s + k) ∈ memaddrs` and a proof the concrete slot
`i` is in range (`i < N`), the aligned address of slot `i` is in the domain. This
is the lemma `wf_auto` fires on each `StoreByte` leaf's memory-domain goal: `apply
memaddrs_of_region` unifies `base`/`i` from the goal, leaving the region fact
(closed by `assumption`) and `i < N` (closed by `omega`) — so a whole byte-write
region's per-slot domain obligations reduce to the ONE region hypothesis with no
hand steps. -/
theorem memaddrs_of_region {base : PancakeState σ → Word} {N i : Nat}
    (s : PancakeState σ)
    (hR : ∀ (s : PancakeState σ) (k : Nat), k < N →
        s.memaddrs (byteAlign (base s + BitVec.ofNat 64 k)) = true)
    (hi : i < N) :
    s.memaddrs (byteAlign (base s + BitVec.ofNat 64 i)) = true :=
  hR s i hi

/-! ## 3. `wf_auto` — the WF decision/automation tactic (P2)

Phase 1 (`repeat'`): decompose the stage tree. A `cond` node's `WF` is the
3-tuple `⟨guard, WF s1, WF s2⟩`; a `seq` node's is the pair `⟨WF s1, WF s2⟩`;
leaves fire `wf_skip`/`wf_assign`/`wf_store`, which leave their `eval`
side-conditions open.

Phase 2 (`all_goals`): close every residual `∀ s, eval s e = some (…)`
obligation. Closed expressions reduce by `rfl`/`decide`; a bound-local read is
closed by `simp_all` picking up the input-scoping fact from context (the A0
contract). `simp_all` also discharges word-`memaddrs` in-range side-conditions
from a context hypothesis when present.

STORE-BYTE leaves (`apply wf_storeByte`) additionally emit an ALIGNED per-slot
memory-domain goal `∀ s, s.memaddrs (byteAlign (base s + i)) = true`. Phase 2
closes it from a SINGLE base-region-in-domain hypothesis on the stage, of shape
`∀ s k, k < N → s.memaddrs (byteAlign (base s + BitVec.ofNat 64 k)) = true`, via
`memaddrs_of_region` chained on each concrete literal slot `i` (the `i < N`
side-condition reduced by `omega`). The region hypothesis is DATA (the
buffer-fits contract), not a hand proof. -/

macro "wf_auto" : tactic =>
  `(tactic|
    ((repeat' first
        | exact wf_skip _
        | refine ⟨?_, ?_, ?_⟩
        | refine ⟨?_, ?_⟩
        | apply wf_assign
        | apply wf_storeByte
        | apply wf_store);
     all_goals
       (intro s;
        first
        | rfl
        | (simp only [eval, signedLt, skipPrim, assignPrim, storePrim,
              storeBytePrim, Option.getD]; done)
        | (simp only [eval, signedLt]; decide)
        | (apply memaddrs_of_region <;> (first | assumption | omega))
        | simp_all [eval, signedLt, skipPrim, assignPrim, storePrim,
              storeBytePrim, Option.getD])))

/-! ## 4. P1 — the proof-producing wrapper

`emitServe` is the translator (= the structural `emit`); `emitServe_correct` is
`emit_correct_generic` under its intended name. `translateCert` is the genuine
proof-producing form: given a stage and its (auto-produced) `WF`, it RETURNS the
emitted program PAIRED WITH the machine-checked certificate that it refines the
stage's denotation. -/

/-- The whole-serve translator over the loop-free grammar. -/
def emitServe : Stage σ → PancakeProg := emit

/-- `emitServe` is emit-correct — this IS `emit_correct_generic`, re-exported as
the translator's correctness contract. -/
theorem emitServe_correct (o : Oracle σ) (st : Stage σ) (h : WF o st) :
    Refines o (emitServe st) (denote st) :=
  emit_correct_generic o st h

/-- PROOF-PRODUCING TRANSLATION: translating a stage returns the emitted program
together with its certificate. With `wf_auto` producing `h`, a concrete
loop-free stage yields `⟨code, proof⟩` with zero hand lines. -/
def translateCert (o : Oracle σ) (st : Stage σ) (h : WF o st) :
    { p : PancakeProg // Refines o p (denote st) } :=
  ⟨emitServe st, emitServe_correct o st h⟩

/-! ## 5. DEMO A — a closed loop-free stage, certificate produced with ZERO hyps

A genuine non-identity transform: choose branch `a := 42` (guard `0 < 1`, always
taken), then publish `b := 7`. All expressions are closed, so `wf_auto` closes
`WF` with NO hypotheses and NO hand lines. This shows the automation is real and
non-vacuous (the denotation writes two distinct locals). -/

def closedDemo : Stage σ :=
  .seq
    (.cond (.cmp .less (.const 0) (.const 1)) (fun _ => true)
       (.prim (assignPrim "a" (.const 42) (fun _ => 42)))
       (.prim (assignPrim "a" (.const 99) (fun _ => 99))))
    (.prim (assignPrim "b" (.const 7) (fun _ => 7)))

/-- `wf_auto` closes the closed stage's `WF` with zero hypotheses. -/
theorem closedDemo_wf (o : Oracle σ) : WF o (closedDemo (σ := σ)) := by wf_auto

/-- Certificate AUTO-PRODUCED: `emit closedDemo` refines `denote closedDemo`,
WF discharged by `wf_auto`, no hand proof. -/
theorem closedDemo_cert (o : Oracle σ) :
    Refines o (emit (closedDemo (σ := σ))) (denote (closedDemo (σ := σ))) :=
  emit_correct_generic o _ (by wf_auto)

/-- The proof-producing form: translating `closedDemo` returns code + certificate. -/
def closedDemo_translated (o : Oracle σ) :
    { p : PancakeProg // Refines o p (denote (closedDemo (σ := σ))) } :=
  translateCert o closedDemo (by wf_auto)

/-! ## 6. DEMO B — the REAL redirect status stage (`Redirect.Code.status`)

`Redirect.Code.status : Code → Nat`  (drorb `Redirect.lean`, position 6 of
`deployStagesFull2`) is the RFC-9110 §15.4 status pick
`moved301 ↦ 301, found302 ↦ 302, temp307 ↦ 307, perm308 ↦ 308`, encoded by the
tag `code ∈ {0,1,2,3}`. The HOL4 C17 probe compiled it in isolation as an
equality dispatch. The `Code` enum has exactly four constructors and its tags
are the increasing `0<1<2<3`, so on the ACTUAL domain the status pick is
equivalently the `<`-cascade below (the C15-style lowering), which uses only the
modelled `Cmp Less` (the Lean `PancakeSem` subset has no `Cmp Equal`). Off-domain
both agree at `308`; the domain is `{0,1,2,3}` since `Code` has 4 constructors.

`codeVal s` is the current code word (the value the `code` local holds). The
guard `code < k` is data-dependent, so its obligation needs the input-scoping
fact `hcode : ∀ s, s.locals "code" = some (codeVal s)` — the A0 input contract,
the same hypothesis C17's `redirectRel` carries. Given it, `wf_auto` produces the
whole certificate. -/

/-- The redirect status stage, in the loop-free grammar: nested `cond` over
`code < 1 / < 2 / < 3` with the four status-constant `assign` leaves. The guard
`fun s => signedLt (codeVal s) k` is `code < k` on the current code word. Denotes
exactly `Redirect.Code.status` (via the tag encoding) into the `result` local. -/
def redirectStatusStage (codeVal : PancakeState σ → Word) : Stage σ :=
  .cond (.cmp .less (.var "code") (.const 1)) (fun s => signedLt (codeVal s) 1)
    (.prim (assignPrim "result" (.const 301) (fun _ => 301)))
    (.cond (.cmp .less (.var "code") (.const 2)) (fun s => signedLt (codeVal s) 2)
      (.prim (assignPrim "result" (.const 302) (fun _ => 302)))
      (.cond (.cmp .less (.var "code") (.const 3)) (fun s => signedLt (codeVal s) 3)
        (.prim (assignPrim "result" (.const 307) (fun _ => 307)))
        (.prim (assignPrim "result" (.const 308) (fun _ => 308)))))

/-- `wf_auto` discharges the real stage's `WF` given ONLY the input-scoping
precondition (the `code` local is bound — the A0 contract). No hand proof. -/
theorem redirectStatusStage_wf (o : Oracle σ) (codeVal : PancakeState σ → Word)
    (hcode : ∀ s : PancakeState σ, s.locals "code" = some (codeVal s)) :
    WF o (redirectStatusStage codeVal) := by
  wf_auto

/-- CERTIFICATE, AUTO-PRODUCED for the real redirect stage: `emit` refines
`denote`, WF discharged by `wf_auto` modulo the single named input contract. -/
theorem redirectStatusStage_cert (o : Oracle σ) (codeVal : PancakeState σ → Word)
    (hcode : ∀ s : PancakeState σ, s.locals "code" = some (codeVal s)) :
    Refines o (emit (redirectStatusStage codeVal)) (denote (redirectStatusStage codeVal)) :=
  emit_correct_generic o _ (redirectStatusStage_wf o codeVal hcode)

/-- The proof-producing form on the real stage: translating returns code +
certificate, WF auto-produced. -/
def redirectStatusStage_translated (o : Oracle σ) (codeVal : PancakeState σ → Word)
    (hcode : ∀ s : PancakeState σ, s.locals "code" = some (codeVal s)) :
    { p : PancakeProg // Refines o p (denote (redirectStatusStage codeVal)) } :=
  translateCert o (redirectStatusStage codeVal) (redirectStatusStage_wf o codeVal hcode)

/-! ### The emitted Pancake AST (Stack L target = `Sem.PancakeProg`)

`emit (redirectStatusStage codeVal)` is the concrete emitted program. It is a
nested `If (Cmp Less (Var "code") (Const k)) …` of `Assign "result" (Const …)`
leaves — the same shape as C17's `redirectCore`, over the Lean model's AST. -/

section EmitWitness
/-- A concrete `codeVal` projection (read the `code` local, default 0) so the
emitted program is a closed term to inspect. -/
def sampleCodeVal : PancakeState σ → Word := fun s => (s.locals "code").getD 0
end EmitWitness

#eval reprStr (emit (redirectStatusStage (σ := Unit) sampleCodeVal))

/-! ## 7. LOOP-BEARING automation — the clocked-stage translator + `wf_auto_clk`

`wf_auto` (§3) discharges the LOOP-FREE `WF` grammar automatically, but a
loop-bearing stage falls outside the total, clock-preserving `Refines` predicate:
its transformer is defined only under an invariant + iteration budget (§6 of
EmitCorrectCompose). Such stages were previously certified by BESPOKE hand
induction (`while_inv_cond_clk` applied by hand) and BESPOKE hand composition
(`refinesClk_seq`/`refinesClk_dec` threaded by hand, as in
`EmitCorrectClock.refinesClk_scan_publish` / `region_via_clock`).

This section makes that automatic. A CLOCKED STAGE (`SClk`) is the loop-bearing
grammar the clock-accounting translator compiles; each node bundles exactly the
annotation the matching `RefinesClk` rule consumes, and its precondition/relation
are INDICES so a well-typed term already carries a checked Hoare contract. The
translator `refinesClkOf` (the clock analog of `emit_correct_generic`) recurses
over that grammar and, at a `loop` node, applies `while_inv_cond_clk`
AUTOMATICALLY from the node's INVARIANT ANNOTATION — no hand induction, no hand
composition. `wf_auto_clk s` is its one-line tactic front-end.

ANNOTATION-CHECKING, NOT SYNTHESIS. The `loop` node carries the loop INVARIANT
`I : Nat → State → Prop` (indexed by remaining iterations — the MEASURE), the
guard-tracks-index fact, the one-iteration step fact, and the entry budget `m`.
The translator CHECKS these compose into a `RefinesClk` stage; it does NOT
SYNTHESISE the invariant nor prove the guard/step facts (those are the
irreducible per-loop obligations — the residual named in §8). -/

open Pancake.EmitCorrectLoop Pancake.EmitCorrectClock

/-- A CLOCKED STAGE: the loop-bearing translator grammar, indexed by its
precondition `P` and its entry→exit relation `Q` (both DETERMINED by the node).
Each constructor bundles the annotation the matching §clock rule consumes:
 * `line`  — a straight-line `Refines` stage embedded (`P = True`);
 * `frame` — a CONDITIONAL assign whose RHS evaluates only under `P` (the
             post-loop publish frame);
 * `loop`  — an annotated bounded `While`: the loop INVARIANT `I` (indexed by the
             remaining-iteration MEASURE), the guard-tracks-index fact `hguard`,
             the one-iteration step fact `hstep`, and the entry budget `m`. THIS
             is the loop annotation `wf_auto_clk` checks and feeds to the rule.
 * `seqA`  — sequential composition with the link `P₁ ∧ Q₁ → P₂`. -/
inductive SClk {σ : Type} (o : Oracle σ) :
    (PancakeState σ → Prop) → (PancakeState σ → PancakeState σ → Prop) → Type
  | line {φ : PancakeState σ → PancakeState σ} (p : PancakeProg) (h : Refines o p φ) :
      SClk o (fun _ => True) (fun s s' => s' = φ s)
  | frame {P : PancakeState σ → Prop} {f : PancakeState σ → Value}
      (x : String) (e : PancakeExp) (hf : ∀ s, P s → eval s e = some (f s)) :
      SClk o P (fun s s' => s' = { s with locals := setLocal s.locals x (f s) })
  | loop {I : Nat → PancakeState σ → Prop}
      (e : PancakeExp) (body : PancakeProg)
      (hguard : ∀ n s, I n s → eval s e = some (if n = 0 then (0 : Word) else 1))
      (hstep  : ∀ n s, I (n + 1) s →
        ∃ s2, PancakeSem o body (decClock s) = (none, s2) ∧ I n s2 ∧ s2.clock = s.clock - 1)
      (m : Nat) :
      SClk o (fun s => I m s ∧ m ≤ s.clock) (fun _ s' => I 0 s')
  | seqA {P1 P2 : PancakeState σ → Prop}
      {Q1 Q2 : PancakeState σ → PancakeState σ → Prop}
      (s1 : SClk o P1 Q1) (s2 : SClk o P2 Q2)
      (hlink : ∀ s s1', P1 s → Q1 s s1' → P2 s1') :
      SClk o P1 (fun s s' => ∃ s1', Q1 s s1' ∧ Q2 s1' s')

/-- The clocked-stage emitter (the loop-bearing translator target program). -/
def emitClk {σ : Type} {o : Oracle σ} :
    ∀ {P : PancakeState σ → Prop} {Q : PancakeState σ → PancakeState σ → Prop},
      SClk o P Q → PancakeProg
  | _, _, .line p _          => p
  | _, _, .frame x e _       => .assign x e
  | _, _, .loop e body _ _ _ => .while_ e body
  | _, _, .seqA s1 s2 _      => .seq (emitClk s1) (emitClk s2)

/-- THE LOOP-BEARING TRANSLATOR, PROOF-PRODUCING. Every clocked stage's emitted
program `RefinesClk`-refines its carried contract, assembled STRUCTURALLY by the
clock-accounting compose rules — the `loop` node discharged by
`while_inv_cond_clk` AUTOMATICALLY (no hand induction) from its invariant
annotation, the `seqA` node by `refinesClk_seq` (no hand composition). This is
the clock analog of `emit_correct_generic`: running the translator over a
loop-bearing stage PRODUCES its certificate. -/
def refinesClkOf {σ : Type} {o : Oracle σ} :
    ∀ {P : PancakeState σ → Prop} {Q : PancakeState σ → PancakeState σ → Prop}
      (st : SClk o P Q), RefinesClk o (emitClk st) P Q
  | _, _, .line _ h              => refinesClk_of_refines o h
  | _, _, .frame x e hf          => refinesClk_assign o x e _ _ hf
  | _, _, .loop e body hg hs m   =>
      fun s hP => while_inv_cond_clk o e body _ hg hs m s hP.1 hP.2
  | _, _, .seqA s1 s2 hlink      => refinesClk_seq o (refinesClkOf s1) (refinesClkOf s2) hlink

/-- `wf_auto_clk st` — the tactic front-end: discharge a `RefinesClk` goal by
running the loop-bearing translator over the clocked stage `st`. The whole
certificate (loop induction + composition) is produced by `refinesClkOf`; the
tactic just checks the stage's emitted program is the goal's program. -/
macro "wf_auto_clk " st:term : tactic => `(tactic| exact refinesClkOf $st)

/-! ### DEMO C — the scan-publish LOOP stage, AUTO-COMPILED

`scanWhile ; result := acc` (the rolling-digest loop then the publish) is a
genuinely loop-bearing stage. As an `SClk` term (`scanPublishStage`) its `loop`
node carries `scanInv` as the invariant annotation, with the already-proven
`scan_guard`/`scan_step` as its guard/step facts and `len` as the entry measure;
its `frame` node is the CONDITIONAL publish (its `acc` is bound only by the loop's
postcondition). `refinesClkOf` compiles the whole thing — the SAME statement
`EmitCorrectClock.refinesClk_scan_publish` proves BY HAND, now produced by the
automated translator. NON-VACUOUS: `Q` states the post-state's `result` local is
`some` of the Lean digest word `scanFrom a off len 0`. -/

/-- The scan-publish stage as a CLOCKED STAGE — the term the loop-bearing
translator compiles. All annotations (invariant, guard fact, step fact, measure,
publish-eval fact) are DATA supplied to the nodes; no proof is threaded by hand. -/
def scanPublishStage (o : Oracle σ) (a : List (BitVec 8)) (buf : Word) (off len : Nat)
    (hlen63 : len < 2 ^ 63) :
    SClk o
      (fun s => scanInv a buf off len len s ∧ len ≤ s.clock)
      (fun _ s' => ∃ s1, scanInv a buf off len 0 s1 ∧
        s' = { s1 with locals := setLocal s1.locals "result" (BitVec.ofNat 64 (scanFrom a off len 0)) }) :=
  .seqA
    (.loop (.cmp .less (.var "i") (.var "len")) scanBody
       (scan_guard a buf off len hlen63) (scan_step o a buf off len hlen63) len)
    (.frame (P := fun s => scanInv a buf off len 0 s)
       (f := fun _ => BitVec.ofNat 64 (scanFrom a off len 0))
       "result" (.var "acc")
       (fun s hI => by
          obtain ⟨k, hk, hacc, _⟩ := hI
          have hkl : k = len := by omega
          subst hkl; exact hacc))
    (fun _ _ _ hq => hq)

/-- THE LOOP STAGE, AUTO-COMPILED. Discharged by the automated translator
`refinesClkOf` (equivalently `wf_auto_clk`), NOT by hand induction/composition.
Its statement is identical to `EmitCorrectClock.refinesClk_scan_publish`. -/
theorem scanPublish_auto (o : Oracle σ) (a : List (BitVec 8)) (buf : Word) (off len : Nat)
    (hlen63 : len < 2 ^ 63) :
    RefinesClk o (.seq scanWhile (.assign "result" (.var "acc")))
      (fun s => scanInv a buf off len len s ∧ len ≤ s.clock)
      (fun _ s' => ∃ s1, scanInv a buf off len 0 s1 ∧
        s' = { s1 with locals := setLocal s1.locals "result" (BitVec.ofNat 64 (scanFrom a off len 0)) }) := by
  wf_auto_clk (scanPublishStage o a buf off len hlen63)

/-! ### §8. RESIDUAL

`refinesClkOf` performs ANNOTATION-CHECKING: given a `loop` node's invariant `I`,
guard fact, step fact and measure `m`, it CHECKS they assemble (via
`while_inv_cond_clk` + the compose rules) into a `RefinesClk` stage, with zero
hand steps. It does NOT (a) SYNTHESISE the invariant `I`, nor (b) prove the
guard/step facts — those remain the irreducible per-loop obligations (the analog
of the loop-free A0 input contract for the straight-line case). Full invariant
SYNTHESIS (deriving `I`/`m` from the loop text) is out of scope; the annotation
comes from the stage, exactly as specified. -/

/-! ## 9. BYTE-WRITE REGIONS — the store-leaf domain discharge, AUTO-COMPILED

A BYTE-WRITE stage stamps a constant byte list `bs` into a buffer at successive
slots `base + 0, base + 1, …`. As a `Stage` it is a right-nested `seq` of
`StoreByte` leaves (`byteRegion`). Each leaf's obligation over an ASSIGN is the
per-slot ALIGNED memory-domain fact `byteAlign (base s + i) ∈ memaddrs` — one per
byte. Threading those by hand was the residual the real-stages lane flagged.

`byteRegion_wf` closes ALL of them from a SINGLE base-region-in-domain hypothesis
`∀ s k, k < off + bs.length → byteAlign (base s + k) ∈ memaddrs`: it recurses over
`bs`, firing `wf_storeByte` at each leaf and discharging that leaf's domain goal
by `memaddrs_of_region` (instantiate `k := i`, bound by `omega`). No per-slot hand
step. The `wf_auto` tactic (§3, extended) does the same on a CONCRETE byte-write
stage tree — see `crlfStamp_wf`, closed by a bare `wf_auto`. -/

/-- One byte-write leaf: `st8 (baseE + off), byte`. Its address VALUE is
`base s + off` (the model add), its stored byte the low 8 bits of the constant
`b`. Reusing `storeBytePrim`, so `wf_storeByte` recognises it. -/
def byteLeaf (base : PancakeState σ → Word) (baseE : PancakeExp) (off : Nat) (b : Word) :
    Stage σ :=
  .prim (storeBytePrim
    (.op .add baseE (.const (BitVec.ofNat 64 off)))
    (.const b)
    (fun s => base s + BitVec.ofNat 64 off)
    (fun _ => b))

/-- A byte-write REGION: the seq-of-`StoreByte`-leaves that stamps `bs` into the
buffer at `base + off, base + off + 1, …`. Empty list ↦ the identity (`skip`). -/
def byteRegion (base : PancakeState σ → Word) (baseE : PancakeExp) :
    Nat → List Word → Stage σ
  | _,   []      => .prim skipPrim
  | off, b :: bs => .seq (byteLeaf base baseE off b) (byteRegion base baseE (off + 1) bs)

/-- THE STORE-LEAF AUTOMATION: a whole byte-write region's WF is discharged from
the base-scoping fact `hbase` (the buffer base evaluates — the A0 input contract)
and ONE base-region-in-domain hypothesis. Recurses over `bs`; at every leaf,
`wf_storeByte` reduces to the slot's domain goal, closed by `memaddrs_of_region`
against the region hypothesis (bound by `omega`). ZERO per-slot hand steps —
supplying the region fact compiles the whole region. -/
theorem byteRegion_wf (o : Oracle σ) (base : PancakeState σ → Word) (baseE : PancakeExp)
    (hbase : ∀ s : PancakeState σ, eval s baseE = some (base s)) :
    ∀ (off : Nat) (bs : List Word),
      (∀ (s : PancakeState σ) (k : Nat), k < off + bs.length →
          s.memaddrs (byteAlign (base s + BitVec.ofNat 64 k)) = true) →
      WF o (byteRegion base baseE off bs)
  | _,   [],      _       => wf_skip o
  | off, b :: bs, hregion => by
      refine ⟨?_, ?_⟩
      · apply wf_storeByte
        · intro s; simp only [eval, hbase s]
        · intro s; rfl
        · intro s
          exact memaddrs_of_region s hregion (by simp only [List.length_cons]; omega)
      · exact byteRegion_wf o base baseE hbase (off + 1) bs
          (fun s k hk => hregion s k (by simp only [List.length_cons]; omega))

/-! ### NON-VACUITY: the region's denotation genuinely writes the bytes

`byteLeaf`'s denotation writes the low byte of `b` at the ALIGNED slot address
via `setByte` — the `mem_store_byte` image, NOT the identity. With the certificate
(`… _cert`), the COMPILED machine run at that slot equals this Lean byte-write. -/
theorem byteLeaf_writes (base : PancakeState σ → Word) (baseE : PancakeExp)
    (off : Nat) (b : Word) (s : PancakeState σ) :
    (denote (byteLeaf base baseE off b) s).memory (byteAlign (base s + BitVec.ofNat 64 off))
      = setByte (base s + BitVec.ofNat 64 off) (b.setWidth 8)
          (s.memory (byteAlign (base s + BitVec.ofNat 64 off))) s.be := by
  simp only [byteLeaf, denote, storeBytePrim, putByteMem, if_pos]

/-! ### DEMO D — `httpStamp`, a 4-byte-write stage AUTO-COMPILED via the region

`httpStamp` stamps the ASCII bytes of `"HTTP"` into `buf[0..3]`. `httpStamp_wf`
produces its WF with the region discharger — no hand steps, one region hypothesis
— and `httpStamp_cert` is the AUTO-PRODUCED certificate that the emitted 4×
`StoreByte` program refines the 4-fold byte-write denotation. NON-VACUOUS:
`denote` is the concrete `putByteMem` chain (`byteLeaf_writes`), and the cert pins
the compiled run to it. -/

/-- "HTTP": the 4-byte constant marker (ASCII `H T T P`). -/
def httpBytes : List Word := [0x48, 0x54, 0x54, 0x50]

/-- A concrete BYTE-WRITE stage: stamp `httpBytes` into `buf[0..3]`. -/
def httpStamp (bufVal : PancakeState σ → Word) : Stage σ :=
  byteRegion bufVal (.var "buf") 0 httpBytes

/-- WF AUTO-DISCHARGED: given the buffer base is bound (`hbuf`, the A0 contract)
and the 4-slot region is in the memory domain (`hregion`), the whole byte-write
stage compiles — no per-slot hand step. -/
theorem httpStamp_wf (o : Oracle σ) (bufVal : PancakeState σ → Word)
    (hbuf : ∀ s : PancakeState σ, s.locals "buf" = some (bufVal s))
    (hregion : ∀ (s : PancakeState σ) (k : Nat), k < 4 →
        s.memaddrs (byteAlign (bufVal s + BitVec.ofNat 64 k)) = true) :
    WF o (httpStamp bufVal) :=
  byteRegion_wf o bufVal (.var "buf")
    (fun s => by simp only [eval, hbuf s]) 0 httpBytes
    (fun s k hk => hregion s k hk)

/-- CERTIFICATE, AUTO-PRODUCED for the byte-write stage: the emitted 4× `StoreByte`
program refines the 4-fold byte-write denotation, WF via the region discharger. -/
theorem httpStamp_cert (o : Oracle σ) (bufVal : PancakeState σ → Word)
    (hbuf : ∀ s : PancakeState σ, s.locals "buf" = some (bufVal s))
    (hregion : ∀ (s : PancakeState σ) (k : Nat), k < 4 →
        s.memaddrs (byteAlign (bufVal s + BitVec.ofNat 64 k)) = true) :
    Refines o (emit (httpStamp bufVal)) (denote (httpStamp bufVal)) :=
  emit_correct_generic o _ (httpStamp_wf o bufVal hbuf hregion)

/-- The proof-producing form: translating the byte-write stage returns code +
certificate, WF auto-produced from the two data hypotheses. -/
def httpStamp_translated (o : Oracle σ) (bufVal : PancakeState σ → Word)
    (hbuf : ∀ s : PancakeState σ, s.locals "buf" = some (bufVal s))
    (hregion : ∀ (s : PancakeState σ) (k : Nat), k < 4 →
        s.memaddrs (byteAlign (bufVal s + BitVec.ofNat 64 k)) = true) :
    { p : PancakeProg // Refines o p (denote (httpStamp bufVal)) } :=
  translateCert o (httpStamp bufVal) (httpStamp_wf o bufVal hbuf hregion)

/-! ### DEMO E — the `wf_auto` TACTIC on a concrete byte-write stage

To exercise the EXTENDED `wf_auto` (§3) end-to-end, `crlfStamp` is a 2-byte-write
stage written as an explicit `seq` tree. `wf_auto` decomposes it, fires
`wf_storeByte` at each leaf, and discharges each slot's domain goal via the new
`memaddrs_of_region` branch — a bare `wf_auto`, no hand steps. -/

/-- A concrete 2-byte-write stage: stamp CRLF (`0x0D 0x0A`) into `buf[0..1]`. -/
def crlfStamp (bufVal : PancakeState σ → Word) : Stage σ :=
  .seq (byteLeaf bufVal (.var "buf") 0 0x0D)
       (byteLeaf bufVal (.var "buf") 1 0x0A)

/-- WF closed by a BARE `wf_auto` — the extended tactic auto-discharges both
byte-store leaves' domain goals from the region hypothesis. -/
theorem crlfStamp_wf (o : Oracle σ) (bufVal : PancakeState σ → Word)
    (hbuf : ∀ s : PancakeState σ, s.locals "buf" = some (bufVal s))
    (hregion : ∀ (s : PancakeState σ) (k : Nat), k < 2 →
        s.memaddrs (byteAlign (bufVal s + BitVec.ofNat 64 k)) = true) :
    WF o (crlfStamp bufVal) := by
  wf_auto

/-- Certificate for the tactic-compiled byte-write stage. -/
theorem crlfStamp_cert (o : Oracle σ) (bufVal : PancakeState σ → Word)
    (hbuf : ∀ s : PancakeState σ, s.locals "buf" = some (bufVal s))
    (hregion : ∀ (s : PancakeState σ) (k : Nat), k < 2 →
        s.memaddrs (byteAlign (bufVal s + BitVec.ofNat 64 k)) = true) :
    Refines o (emit (crlfStamp bufVal)) (denote (crlfStamp bufVal)) :=
  emit_correct_generic o _ (crlfStamp_wf o bufVal hbuf hregion)

section ByteWitness
/-- A concrete `bufVal` projection so the emitted byte-write program is closed. -/
def sampleBufVal : PancakeState σ → Word := fun s => (s.locals "buf").getD 0
end ByteWitness

#eval reprStr (emit (httpStamp (σ := Unit) sampleBufVal))

/-! ### §10. RESIDUAL (byte-write automation)

`byteRegion_wf` / the extended `wf_auto` discharge the per-slot memory-DOMAIN
precondition automatically from ONE base-region-in-domain hypothesis. What
remains DATA (not a hand proof, exactly as the loop-free A0 contract):
 * `hbase`  — the buffer base local is bound (the input contract), and
 * `hregion` — the write region fits in the memory domain (the buffer-size
   contract the caller supplies).
Neither is synthesised here; both are the irreducible external contracts. The
region is a CONSTANT byte list (`bs : List Word`); a DATA-DEPENDENT byte source
(reading each byte from another buffer) reuses the same leaves with a per-slot
`hval` eval fact and is a straight-line extension. -/


end Pancake.ProofProducing
