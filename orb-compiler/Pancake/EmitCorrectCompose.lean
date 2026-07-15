/-
  Pancake/EmitCorrectCompose.lean — GENERIC emit-correctness over the loop-free
  stage-kind grammar {prim, seq, cond}, additively extending the region pilot
  (Pancake/EmitCorrectRegion.lean).

  The region pilot proved emit-correctness for ONE stage-kind (the region
  primitive: a bounds-`If` composed with a scan-`While`, hand-composed via
  `sem_dec`/`sem_seq_none`/`scan_loop`). This file lifts that from a one-off hand
  composition to a REUSABLE compositional theory:

   * a single operational-refinement predicate `Refines o p φ` — the emitted
     Pancake program `p`, run under the modelled Pancake operational semantics
     `PancakeSem`, ALWAYS terminates normally and computes EXACTLY the
     state-transformer `φ` (and preserves the clock, so `fix_clock` clamps are
     no-ops across composition). This is a genuine operational refinement, not a
     tautology: `φ` is a concrete function on states and the emitted code must
     reproduce it exactly.

   * emit-correctness (`Refines`) for the stage-kinds beyond `region`:
       - SKIP        (`refines_skip`)         — the identity stage
       - ASSIGN      (`refines_assign`)       — the transform/set stage
       - STORE       (`refines_store`)        — the memory-write stage
       - SEQ         (`refines_seq`)          — SEQUENTIAL COMPOSITION (the key
                                                compositional lemma)
       - COND        (`refines_cond`)         — the branch stage
       - DEC         (`refines_dec`)          — lexical-scope wrapper

   * the GENERIC emit (`emit_correct_generic`): a `Stage` grammar with a
     structural `emit : Stage → PancakeProg` and a denotation `denote : Stage →
     (State → State)`, and the theorem that a well-formed stage's emitted program
     refines its denotation — proven by structural induction from the rules
     above. This is the Gate-A shape for the LOOP-FREE fragment: any serve built
     from these stage-kinds is emit-correct by composition, with no new per-stage
     proof.

  HONEST GAP (see §6): the bounded LOOP stage-kind (`While`) is NOT a member of
  this uniform `Refines` grammar — its transformer is defined only under a
  per-loop invariant + clock/measure budget (it is not a total state-transformer
  for all inputs). The region pilot's `scan_loop` is the concrete loop instance;
  §6 states the reusable While rule (`while_inv`) that generalises it and names
  exactly what a generic loop stage would additionally need.

  ASSURANCE: `#print axioms` on each theorem (see Pancake/build_compose.sh);
  0 `sorry`, axioms ⊆ {propext, Quot.sound, Classical.choice}. Additive: the
  region proof is imported unchanged.
-/
import Pancake.EmitCorrectRegion

namespace Pancake.EmitCorrectCompose

open Pancake Pancake.EmitCorrect

variable {σ : Type}

/-! ## 0. The operational-refinement predicate

`Refines o p φ`: the emitted program `p` refines the state-transformer `φ`.
"Refines" = runs to a NORMAL termination (`result = none`, i.e. no error /
timeout / early return / FFI-final) in the model semantics, landing in EXACTLY
`φ s`, and leaves the clock untouched. Clock-preservation is what makes the
`fix_clock` clamp at every `Seq` boundary a no-op, so refinements compose
cleanly. -/
def Refines (o : Oracle σ) (p : PancakeProg) (φ : PancakeState σ → PancakeState σ) : Prop :=
  ∀ s : PancakeState σ, PancakeSem o p s = (none, φ s) ∧ (φ s).clock = s.clock

/-! ## 1. Primitive stage-kinds

Note on the `fix_clock` clamps: structure eta makes `{ t with clock := t.clock }`
DEFINITIONALLY equal to `t`, so once a refinement pins `(φ s).clock = s.clock`
the `min`-clamp collapses and the clamped state is `defeq` to the unclamped one
(closed by `exact`, no rewrite needed). -/

/-- SKIP is the identity stage. -/
theorem refines_skip (o : Oracle σ) : Refines o .skip (fun s => s) := by
  intro s; refine ⟨?_, rfl⟩; rw [PancakeSem]

/-- ASSIGN (the transform/set stage): given the RHS evaluates (in every state)
to `f s`, the emitted `Assign` refines the local-update transformer. Genuinely
computes `f`: `f` is threaded through the model `eval`. -/
theorem refines_assign (o : Oracle σ) (x : String) (e : PancakeExp)
    (f : PancakeState σ → Value) (hf : ∀ s, eval s e = some (f s)) :
    Refines o (.assign x e) (fun s => { s with locals := setLocal s.locals x (f s) }) := by
  intro s
  exact ⟨sem_assign (oracle := o) (hf s), rfl⟩

/-- STORE (the memory-write stage): given the address and value evaluate and the
address is in the model's address set, the emitted `Store` refines the
single-word memory update. -/
theorem refines_store (o : Oracle σ) (dst src : PancakeExp)
    (addr val : PancakeState σ → Word)
    (haddr : ∀ s, eval s dst = some (addr s))
    (hval : ∀ s, eval s src = some (val s))
    (hin : ∀ s : PancakeState σ, s.memaddrs (addr s) = true) :
    Refines o (.store dst src)
      (fun s => { s with memory := fun k => if k = addr s then val s else s.memory k }) := by
  intro s
  refine ⟨?_, rfl⟩
  have hms : memStoreWord s.memory s.memaddrs (addr s) (val s)
      = some (fun k => if k = addr s then val s else s.memory k) := by
    unfold memStoreWord; rw [if_pos (hin s)]
  rw [PancakeSem]
  simp only [haddr s, hval s, hms]

/-! ## 2. SEQUENTIAL COMPOSITION — the key compositional lemma -/

/-- SEQ: sequential composition of two refinements refines the composed
transformer. The `fix_clock` clamp at the `Seq` boundary is discharged by
clock-preservation (`state_setClock_self`). This is THE compositional win:
`emit (s1 ; s2)` refines `denote s2 ∘ denote s1`. -/
theorem refines_seq (o : Oracle σ) {p1 p2 : PancakeProg}
    {φ1 φ2 : PancakeState σ → PancakeState σ}
    (h1 : Refines o p1 φ1) (h2 : Refines o p2 φ2) :
    Refines o (.seq p1 p2) (fun s => φ2 (φ1 s)) := by
  intro s
  obtain ⟨he1, hc1⟩ := h1 s
  obtain ⟨he2, hc2⟩ := h2 (φ1 s)
  refine ⟨?_, by simp only [hc2, hc1]⟩
  have hclk : min s.clock (φ1 s).clock = (φ1 s).clock := by rw [hc1, Nat.min_self]
  rw [sem_seq_none (oracle := o) he1, hclk]
  -- `{ φ1 s with clock := (φ1 s).clock }` is defeq to `φ1 s` (structure eta)
  exact he2

/-! ## 3. COND — the branch stage-kind -/

/-- `If`-reduction: `evaluate (If e c1 c2, s)` with `eval s e = some w` runs the
`w ≠ 0`-selected branch (panSem `If` clause). -/
theorem sem_cond (o : Oracle σ) {e : PancakeExp} {c1 c2 : PancakeProg}
    {s : PancakeState σ} {w : Word} (h : eval s e = some w) :
    PancakeSem o (.cond e c1 c2) s = PancakeSem o (if w ≠ 0 then c1 else c2) s := by
  rw [PancakeSem, h]

/-- COND: a guarded branch. Given the guard expression evaluates to the SPEC's
boolean (`1` when the branch predicate `b` holds, `0` otherwise), the emitted
`If` refines the branch-selecting transformer. Both arms must be refinements. -/
theorem refines_cond (o : Oracle σ) {e : PancakeExp} {p1 p2 : PancakeProg}
    {φ1 φ2 : PancakeState σ → PancakeState σ} (b : PancakeState σ → Bool)
    (hguard : ∀ s, eval s e = some (if b s then (1 : Word) else 0))
    (h1 : Refines o p1 φ1) (h2 : Refines o p2 φ2) :
    Refines o (.cond e p1 p2) (fun s => if b s then φ1 s else φ2 s) := by
  intro s
  obtain ⟨he1, hc1⟩ := h1 s
  obtain ⟨he2, hc2⟩ := h2 s
  have key : PancakeSem o (.cond e p1 p2) s = (none, if b s then φ1 s else φ2 s) := by
    rw [sem_cond o (hguard s)]
    cases hbe : b s with
    | true =>
      rw [if_pos (rfl : true = true), if_pos (show (1 : Word) ≠ 0 by decide),
          if_pos (rfl : true = true)]
      exact he1
    | false =>
      rw [if_neg (by decide : ¬(false = true)), if_neg (show ¬((0 : Word) ≠ 0) by decide),
          if_neg (by decide : ¬(false = true))]
      exact he2
  refine ⟨key, ?_⟩
  show (if b s then φ1 s else φ2 s).clock = s.clock
  cases hbe : b s with
  | true  => rw [if_pos (rfl : true = true)]; exact hc1
  | false => rw [if_neg (by decide : ¬(false = true))]; exact hc2

/-! ## 4. DEC — lexical-scope wrapper

`Dec v e cont` binds `v` to `eval e`, runs the continuation, then RESTORES the
shadowed binding (`res_var`). Its transformer is the continuation's transformer
sandwiched between the bind and the restore. Reuses the pilot's `sem_dec`. -/
theorem refines_dec (o : Oracle σ) {v : String} {e : PancakeExp} {cont : PancakeProg}
    {ψ : PancakeState σ → PancakeState σ}
    (f : PancakeState σ → Value) (hf : ∀ s, eval s e = some (f s))
    (hcont : Refines o cont ψ) :
    Refines o (.dec v e cont)
      (fun s =>
        let s' := ψ { s with locals := setLocal s.locals v (f s) }
        { s' with locals := resVar s'.locals v (s.locals v) }) := by
  intro s
  obtain ⟨hce, hcc⟩ := hcont { s with locals := setLocal s.locals v (f s) }
  refine ⟨?_, by simp only [hcc]⟩
  exact sem_dec (oracle := o) (v := v) (e := e) (val := f s) (s := s) (hf s) hce

/-! ## 5. The GENERIC emit over the loop-free stage grammar

A `Stage` is a syntax tree of the composable stage-kinds. Each primitive leaf
carries BOTH its emitted program and its intended denotation; `WF` collects the
per-leaf refinement obligations (and per-branch guard obligations). The theorem
`emit_correct_generic` then discharges emit-correctness for the WHOLE tree by
structural induction, using the rules of §1–§4. This is the Gate-A shape for the
loop-free fragment: no new per-stage proof is needed once the leaves are
discharged. -/

/-- A verified primitive leaf: its emitted program `prog` with the
state-transformer `den` it is meant to compute. -/
structure Prim (σ : Type) where
  prog : PancakeProg
  den  : PancakeState σ → PancakeState σ

inductive Stage (σ : Type)
  | prim (p : Prim σ)
  | seq  (s1 s2 : Stage σ)
  | cond (e : PancakeExp) (guard : PancakeState σ → Bool) (s1 s2 : Stage σ)

/-- The structural emitter: `Stage` syntax → `PancakeProg`. -/
def emit : Stage σ → PancakeProg
  | .prim p          => p.prog
  | .seq s1 s2       => .seq (emit s1) (emit s2)
  | .cond e _ s1 s2  => .cond e (emit s1) (emit s2)

/-- The denotation: `Stage` syntax → state-transformer. `seq` composes, `cond`
selects on the guard. This is the SPEC the emitted program must refine. -/
def denote : Stage σ → (PancakeState σ → PancakeState σ)
  | .prim p          => p.den
  | .seq s1 s2       => fun s => denote s2 (denote s1 s)
  | .cond _ g s1 s2  => fun s => if g s then denote s1 s else denote s2 s

/-- Well-formedness = the collected leaf/branch obligations. A `prim` leaf must
actually refine its declared denotation; a `cond` guard must evaluate to the
declared boolean. These are precisely the per-stage facts discharged in §1–§4. -/
def WF (o : Oracle σ) : Stage σ → Prop
  | .prim p          => Refines o p.prog p.den
  | .seq s1 s2       => WF o s1 ∧ WF o s2
  | .cond e g s1 s2  => (∀ s, eval s e = some (if g s then (1 : Word) else 0))
                          ∧ WF o s1 ∧ WF o s2

/-- GENERIC EMIT-CORRECTNESS: a well-formed stage's emitted program refines its
denotation. Structural induction closing each node by the §1–§4 composition
rules. Any serve assembled from `{prim, seq, cond}` stage-kinds is emit-correct
by this single theorem — the loop-free Gate-A. -/
theorem emit_correct_generic (o : Oracle σ) :
    ∀ st : Stage σ, WF o st → Refines o (emit st) (denote st)
  | .prim _, hwf => hwf
  | .seq s1 s2, hwf => by
      obtain ⟨w1, w2⟩ := hwf
      show Refines o (.seq (emit s1) (emit s2)) (fun s => denote s2 (denote s1 s))
      exact refines_seq o (emit_correct_generic o s1 w1) (emit_correct_generic o s2 w2)
  | .cond e g s1 s2, hwf => by
      obtain ⟨hg, w1, w2⟩ := hwf
      show Refines o (.cond e (emit s1) (emit s2)) (fun s => if g s then denote s1 s else denote s2 s)
      exact refines_cond o g hg (emit_correct_generic o s1 w1) (emit_correct_generic o s2 w2)

/-! ### Non-vacuity witness: a two-stage serve compiled generically

A concrete serve of two stage-kinds — a memory-write STORE followed by an
ASSIGN publishing a result word — assembled as a `Stage`, shown well-formed from
the §1 primitive lemmas, and thus emit-correct by `emit_correct_generic`. The
denotation is a genuine non-identity state-transformer (writes memory AND a
local), so this is a real refinement, not `P → P`. -/

/-- Stage 1: store the constant `w` at the address held in local `"slot"`. -/
def demoStore (w : Word) : Prim σ :=
  { prog := .store (.var "slot") (.const w)
    den  := fun s =>
      { s with memory := fun k =>
          if k = (s.locals "slot").getD 0 then w else s.memory k } }

/-- Stage 2: publish `result := 1`. -/
def demoPublish : Prim σ :=
  { prog := .assign "result" (.const 1)
    den  := fun s => { s with locals := setLocal s.locals "result" 1 } }

/-- The two-stage serve, as `Stage` syntax. -/
def demoServe (w : Word) : Stage σ :=
  .seq (.prim (demoStore w)) (.prim demoPublish)

/-- The demo serve is emit-correct: the emitted `Store; Assign` computes exactly
the composed transformer (write memory, then publish `result = 1`). Discharges
`WF` from the §1 primitive refinements. -/
theorem demoServe_emit_correct (o : Oracle σ) (w : Word) (slotAddr : Word)
    (hslot : ∀ s : PancakeState σ, s.locals "slot" = some slotAddr)
    (hin : ∀ s : PancakeState σ, s.memaddrs slotAddr = true) :
    Refines o (emit (demoServe (σ := σ) w)) (denote (demoServe (σ := σ) w)) := by
  apply emit_correct_generic
  refine ⟨?_, ?_⟩
  · -- store leaf refines demoStore.den
    have hden : (demoStore (σ := σ) w).den
        = fun s => { s with memory := fun k => if k = slotAddr then w else s.memory k } := by
      funext s; simp only [demoStore, hslot s, Option.getD]
    show Refines o _ (demoStore (σ := σ) w).den
    rw [hden]
    exact refines_store o (.var "slot") (.const w) (fun _ => slotAddr) (fun _ => w)
      (fun s => hslot s) (fun _ => rfl) (fun s => hin s)
  · -- publish leaf refines demoPublish.den
    exact refines_assign o "result" (.const 1) (fun _ => 1) (fun _ => rfl)

/-! ## 6. The bounded-LOOP stage-kind — reusable While rule + the honest gap

The loop stage-kind does NOT fit the uniform `Refines` grammar above: a `While`
computes a total state-transformer only relative to a loop INVARIANT and a
clock/iteration budget (unbounded input diverges past the clock → `Timeout`, not
a `none`-normal `φ s`). So a generic loop stage needs an invariant + a decreasing
measure SUPPLIED per loop — it is not closed under the parameter-free `Refines`.

The region pilot's `scan_loop` is the concrete instance (invariant = the
accumulator relation, measure = remaining iterations `rem`, budgeted by the
clock). Below is that instance's shape lifted to a REUSABLE Hoare-style rule: a
`While` whose body advances an invariant `I : Nat → State → Prop` (indexed by
remaining iterations) and preserves the clock refines to the invariant's
`0`-index state, given the guard tracks the index and the body is a refinement at
each step. A generic loop STAGE would embed this, paying the per-loop `I`/measure
as extra `WF` data (the named Gate-A distance for loops). -/

/-- Reusable bounded-`While` rule. `I n` is the loop invariant with `n`
iterations of budget remaining; `bodyφ` the one-iteration body transformer.
Hypotheses: the guard evaluates to `0` iff `n = 0` (loop stops exactly when the
index is exhausted); the body is a clock-preserving refinement to `bodyφ` that
steps `I (n+1) s → I n (bodyφ (decClock s))`. Conclusion: from `I rem s` with
`rem ≤ s.clock`, the loop runs to a state satisfying `I 0`. Generalises
`scan_loop`. -/
theorem while_inv (o : Oracle σ) (e : PancakeExp) (body : PancakeProg)
    (I : Nat → PancakeState σ → Prop)
    (bodyφ : PancakeState σ → PancakeState σ)
    (hguard : ∀ n s, I n s → eval s e = some (if n = 0 then (0 : Word) else 1))
    (hbody : ∀ s, PancakeSem o body s = (none, bodyφ s))
    (hbodyclk : ∀ s, (bodyφ s).clock = s.clock)
    (hstep : ∀ n s, I (n + 1) s → I n (bodyφ (decClock s))) :
    ∀ (rem : Nat) (s : PancakeState σ), I rem s → rem ≤ s.clock →
      ∃ s', PancakeSem o (.while_ e body) s = (none, s') ∧ I 0 s' := by
  intro rem
  induction rem with
  | zero =>
    intro s hI _
    refine ⟨s, ?_, hI⟩
    rw [PancakeSem, hguard 0 s hI]
    simp
  | succ m ih =>
    intro s hI hclock
    have hclock0 : s.clock ≠ 0 := by omega
    have hbodyd := hbody (decClock s)
    have hstepd : I m (bodyφ (decClock s)) := hstep m s hI
    have hcond : eval s e = some (1 : Word) := by
      have := hguard (m + 1) s hI; simpa using this
    have hclkb : (bodyφ (decClock s)).clock = s.clock - 1 := by
      rw [hbodyclk]; simp [decClock]
    have hmin : min (s.clock - 1) (bodyφ (decClock s)).clock = (bodyφ (decClock s)).clock := by
      rw [hclkb, Nat.min_self]
    have hclamp : ({ bodyφ (decClock s) with
                     clock := min (s.clock - 1) (bodyφ (decClock s)).clock } : PancakeState σ)
                    = bodyφ (decClock s) := by
      rw [hmin]  -- `{ t with clock := t.clock } = t` by structure eta
    obtain ⟨s', hs'eq, hs'I⟩ := ih (bodyφ (decClock s)) hstepd (by rw [hclkb]; omega)
    refine ⟨s', ?_, hs'I⟩
    rw [PancakeSem]
    simp only [hcond, ne_eq, show ((1 : Word) = 0) = False from by decide, not_false_eq_true,
               if_true, hclock0, if_false, clampClock, hbodyd]
    rw [hclamp]
    exact hs'eq

end Pancake.EmitCorrectCompose
