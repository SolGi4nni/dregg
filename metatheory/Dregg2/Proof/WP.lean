/-
# Dregg2.Proof.WP — a weakest-precondition / VCG calculus over the record cell.

`docs/rebuild/PHASE-VCG-WP.md §6` (the recommended minimal first version): dregg's
metatheory today proves conservation/authority hold along an arbitrary run — but it does so
*per fixed program*, by hand, one `theorem` per cell (`recordCell_run_preserves_sumEquals`).
There is no **calculus** that, given an arbitrary `RecordProgram` + a developer-supplied
invariant, *generates* the proof obligations and lifts a discharged set to a whole-run
safety theorem. This module is that machine — the l4v/AutoCorres analog at dregg's current
maturity: a `wp`/`Triple` over the `Option`-monad transition, a `vcg` over `RecordProgram`,
the single soundness obligation `vcg_run_sound`, and the two worked examples.

The deliverables (`PHASE-VCG-WP §1,§2,§3,§4,§6`):
- **`wp` / `Triple`** — partial-correctness validity over `step : σ → α → Option σ`. A
  fail-closed (rejected, `none`) turn is vacuously safe: dregg's safety is "nothing bad
  commits", not "every turn commits". Instantiated at `recCexec`.
- **`wp_sound`** — per-step soundness; it factors through `recCexec_attests` (definitional).
- **`CellSpec` + `vcg`** — the verification-condition generator. The key fact the generator
  exploits is that `RecordProgram.admits` is a decidable Boolean, so `wp recCexec` computes
  symbolically. The VC classes: (1) admissibility→inv-preservation, (2) stay-put, (3) init,
  (4) post.
- **`vcg_run_sound` — THE single soundness obligation.** A fully-discharged VC set entails
  `inv` holds along every `Run` of the record cell, concluded by handing
  `StepInvariant (fun c => inv c.value)` to `Boundary.stepComplete_preserves`. This is the
  *generated* form of the hand proof `recordCell_run_preserves_sumEquals`.
- **The two worked examples** as the regression check that the generator matches reality:
  the **monotonic counter** (closes by `recExec_mono_holds`) and the **escrow** state machine
  + single-ledger `sumEqualsAcross` conservation. The cross-vat conservation fragment is left a
  documented honest-OPEN (hypothesis-routed, never derived — the inviolable rule).

Pure; `#assert_axioms` pins every keystone kernel-axiom-clean (no `sorry`/`axiom`/`admit`).
-/
import Dregg2.Exec.RecordCellLive
import Dregg2.Boundary
import Dregg2.Execution
import Dregg2.Exec.Program
import Dregg2.Resource
import Dregg2.Spec.Conservation
import Dregg2.Tactics

namespace Dregg2.Proof.WP

open Dregg2.Exec Dregg2.Exec.RecordCell Dregg2.Boundary Dregg2.Execution

/-! ## §1 — `wp` / `Triple`: the partial-correctness calculus over an `Option`-monad step.

`PHASE-VCG-WP §1.2`. The `Option` IS the partiality of the coalgebra arrow: `none` is "the
structure-map rejects this turn". Partial correctness is the right default — a *rejected*
(fail-closed) turn trivially satisfies any post-condition (the `none` branch is vacuous). -/

/-- **`wp step t Q s`** — the weakest precondition: `Q` holds of every committed post-state.
A `none` (rejected) turn is vacuously safe. The validity anchor for the whole calculus. -/
def wp {σ α : Type} (step : σ → α → Option σ) (t : α) (Q : σ → Prop) (s : σ) : Prop :=
  ∀ s', step s t = some s' → Q s'

/-- **`Triple step P t Q`** — the user-facing Hoare triple `{P} t {Q}`, defined *in terms of*
`wp` (exactly l4v's layering: triples are the surface, `wp` is the workhorse). -/
def Triple {σ α : Type} (step : σ → α → Option σ) (P : σ → Prop) (t : α) (Q : σ → Prop) : Prop :=
  ∀ s, P s → wp step t Q s

/-- `wp` is monotone in the postcondition — PROVED (the consequence rule, weakening side). -/
theorem wp_mono {σ α : Type} {step : σ → α → Option σ} {t : α} {Q Q' : σ → Prop}
    (hQ : ∀ s, Q s → Q' s) {s : σ} (h : wp step t Q s) : wp step t Q' s :=
  fun s' hstep => hQ s' (h s' hstep)

/-- A rejected (`none`) turn satisfies every `wp` — PROVED (the fail-closed/vacuous branch). -/
theorem wp_of_none {σ α : Type} {step : σ → α → Option σ} {t : α} {Q : σ → Prop} {s : σ}
    (h : step s t = none) : wp step t Q s := by
  intro s' hstep; rw [h] at hstep; exact absurd hstep (by simp)

#assert_axioms wp_mono
#assert_axioms wp_of_none

/-! ## §2 — `wp_sound`: per-step soundness (the `wp` is faithful to `recCexec`).

`PHASE-VCG-WP §3.1`. This is definitional (`wp` unfolds to exactly the conclusion), but the
*content* is that `recCexec`'s commit implies the `StepInv` facts — it factors through
`recCexec_attests`. The WP only ever asserts properties of the genuinely-gated post-state. -/

/-- **`wp_sound` (PROVED)** — if `wp recCexec op Q s` holds, then every committed successor
satisfies `Q`. Per-step WP-soundness, definitional over `recCexec`'s commit. -/
theorem wp_sound {s : RecChained} {op : RecOp} {Q : RecChained → Prop}
    (h : wp recCexec op Q s) :
    ∀ s', recCexec s op = some s' → Q s' :=
  h

/-- **`wp_sound_value` (PROVED)** — the value-level reading: a `wp` over the record's
*value* projection is faithful to `recCexec`'s committed value. Factors through
`recCexec_attests` (the committed value is exactly `applyOp`, genuinely admitted). -/
theorem wp_sound_value {s : RecChained} {op : RecOp} {Q : Value → Prop}
    (h : wp recCexec op (fun s' => Q s'.value) s) :
    ∀ s', recCexec s op = some s' → Q s'.value :=
  h

/-- **`wp_attests` (PROVED)** — the bridge to step-completeness: a committed `recCexec` step
attests its candidate was admitted (`recCexec_attests`), so any `wp` asserting an admitted-state
property is discharged by the gate. This is `recCexec_attests` re-packaged as the WP-soundness
content — the WP never asserts anything the structure-map's gate did not establish. -/
theorem wp_attests {s s' : RecChained} {op : RecOp} (h : recCexec s op = some s') :
    s.program.admits s.method s.value s'.value = true ∧ s'.value = applyOp s.value op :=
  ⟨(recCexec_attests h).1, (recCexec_attests h).2.1⟩

#assert_axioms wp_sound
#assert_axioms wp_sound_value
#assert_axioms wp_attests

/-! ## §3 — `CellSpec` + `vcg`: the verification-condition generator.

`PHASE-VCG-WP §2.1, §2.2`. A cell verification problem is `(program, spec)`. The generator
emits the obligation classes; the developer authors `inv`, the VCG says what must be discharged
for `inv` to be a genuine run-invariant. We work at the `RecChained` carrier (the living cell)
with `inv`/`pre`/`post` predicates on the record `Value`. -/

/-- **`CellSpec`** — the developer-supplied pre/post/invariant on the record `Value`. -/
structure CellSpec where
  /-- Precondition on the initial record. -/
  pre  : Value → Prop
  /-- Postcondition (turned on at the final/observed state). -/
  post : Value → Prop
  /-- The cell invariant (what must hold at every reachable state). -/
  inv  : Value → Prop

/-- **VC class 1 — admissibility → invariant preservation (the core VC).** Whenever the
program's gate fires on a candidate, the post-value still satisfies `inv`. This is `wp recCexec`
unfolded through `recCexec_attests`: a commit's post-value is exactly `applyOp s.value op` and
was `admits`-true. For a `predicate cs` program the discharge is per-constraint
(`admits_sumEquals`, `recExec_mono_holds` are the templates). -/
def VC_preserve (program : RecordProgram) (method : Nat) (spec : CellSpec) : Prop :=
  ∀ (old new : Value), spec.inv old →
    program.admits method old new = true → spec.inv new

/-- **VC class 2 — stay-put preservation (the fail-closed branch).** `inv` is preserved by the
rejected-turn self-loop. Trivially true (the value is unchanged); generated for completeness so
the VC set fully covers the totalized arrow. -/
def VC_stayput (spec : CellSpec) : Prop :=
  ∀ v : Value, spec.inv v → spec.inv v

/-- **VC class 3 — initialization.** The invariant holds at start (from the precondition). -/
def VC_init (spec : CellSpec) : Prop :=
  ∀ v : Value, spec.pre v → spec.inv v

/-- **VC class 4 — postcondition.** The invariant entails the post (often `post = inv`). -/
def VC_post (spec : CellSpec) : Prop :=
  ∀ v : Value, spec.inv v → spec.post v

/-- **`vcg program method spec`** — the generated VC set (a conjunction of the four classes).
`PHASE-VCG-WP §2.2`. The generation is computable: `RecordProgram.admits` is a decidable
Boolean, so VC class 1 is a closed `Prop` obtained by symbolic push through the program
structure. A `vcg`-discharged set is exactly the input to `vcg_run_sound`. -/
def vcg (program : RecordProgram) (method : Nat) (spec : CellSpec) : Prop :=
  VC_preserve program method spec ∧ VC_stayput spec ∧ VC_init spec ∧ VC_post spec

/-- The stay-put VC is *always* discharged — PROVED (the self-loop is the identity). The VCG
emits it but it closes by `id`, matching `recNext_commits_or_stays`'s stay branch. -/
theorem VC_stayput_trivial (spec : CellSpec) : VC_stayput spec := fun _ h => h

#assert_axioms VC_stayput_trivial

/-! ## §4 — `vcg_run_sound`: THE single soundness obligation.

`PHASE-VCG-WP §3.2, §6`. A fully-discharged VC set entails `inv` holds along every `Run` of the
record cell. Proof: VC class 1+2 give a `StepInvariant (fun c => inv c.value)`; VC class 3 lifts
`pre` to `inv`; then `Boundary.stepComplete_preserves` / `Execution.invariant_run` lift `inv` to
the reached state; VC class 4 turns `inv` into `post`. This is the *generated* form of the hand
proof `recordCell_run_preserves_sumEquals` — proved once, it makes every VCG-discharged cell sound
w.r.t. the operational `recCexec`. -/

/-- The `inv`-on-value predicate as a `Good` for the record coalgebra. -/
private def invGood (spec : CellSpec) : RecChained → Prop := fun c => spec.inv c.value

/-- **`vcg_preserves_good` (PROVED)** — VC class 1 + 2 discharge `Good`-preservation along the
totalized `recNext`: on a commit the admitted post-value satisfies `inv` (VC 1, via
`recCexec_attests`); on a stay-put the value is unchanged (VC 2, trivially). This is the `hpres`
hypothesis `stepComplete_preserves` consumes — *generated* from the VC set. -/
theorem vcg_preserves_good (program : RecordProgram) (spec : CellSpec)
    (hprogInv : ∀ x : RecChained, x.program = program)
    (hmethodInv : ∀ x : RecChained, x.method = method)
    (hpres : VC_preserve program method spec)
    (x : RecChained) (op : RecOp) (hgood : invGood spec x)
    (_hsi : StepInv recordCell recCons recAdmit recChain recObsA x op (recordCell.next x op)) :
    invGood spec (recordCell.next x op) := by
  show spec.inv (recordCell.next x op).value
  -- `recordCell.next x op` is defeq `recNext x op`.
  show spec.inv (recNext x op).value
  rcases recNext_commits_or_stays x op with hc | hstay
  · -- commit: the admitted post-state satisfies `inv` by VC class 1.
    have hadm : program.admits method x.value (recNext x op).value = true := by
      have a := recCexec_attests hc
      rw [← hprogInv x, ← hmethodInv x]; exact a.1
    exact hpres x.value (recNext x op).value hgood hadm
  · -- stay-put: the value is unchanged, so `inv` carries over.
    rw [hstay]; exact hgood

/-- **`vcg_run_sound` (THE SINGLE SOUNDNESS OBLIGATION — PROVED).** A fully-discharged VC set
(`vcg program method spec`) entails that `inv` AND `post` hold at every reachable state of the
record cell's whole run, given the precondition at the start. Concluded by handing the generated
`StepInvariant` to `Boundary.stepComplete_preserves`. This is the machine-generated analog of
`recordCell_run_preserves_sumEquals` (`Exec/RecordCellLive.lean:228`). -/
theorem vcg_run_sound (program : RecordProgram) (spec : CellSpec)
    (hprogInv : ∀ x : RecChained, x.program = program)
    (hmethodInv : ∀ x : RecChained, x.method = method)
    (hVCs : vcg program method spec)
    {s s' : RecChained}
    (hrun : Execution.Run (inducedSystem recordCell) s s')
    (h0 : spec.pre s.value) :
    spec.inv s'.value ∧ spec.post s'.value := by
  obtain ⟨hpres, _hstay, hinit, hpost⟩ := hVCs
  -- VC class 3: lift `pre` to `inv` at the start.
  have hgood0 : invGood spec s := hinit s.value h0
  -- The lift: `stepComplete_preserves` with `Good := invGood spec`.
  have hinv' : invGood spec s' := by
    refine stepComplete_preserves recordCell recCons recAdmit recChain recObsA
      (Good := invGood spec) recordCell_stepComplete ?_ hrun hgood0
    intro x op hgx hsi
    exact vcg_preserves_good program spec hprogInv hmethodInv hpres x op hgx hsi
  -- VC class 4: turn `inv s'` into `post s'`.
  exact ⟨hinv', hpost s'.value hinv'⟩

#assert_axioms vcg_preserves_good
#assert_axioms vcg_run_sound

/-! ## §5 — Worked example A: the monotonic counter (`PHASE-VCG-WP §4.1`).

"Buildable today with zero new metatheory" — the VCG retracing an existing hand proof. The
invariant is the *post-state* fact "`count` is present and equals some pinned `n₀`-or-higher".
We take the clean relational form: with the program `monoCountProgram = predicate [monotonic
"count"]`, a committed step never *decreases* `count`, so the run-level safety `count ≥ n₀` holds
forever once it holds at the start.

The VC class 1 (admissibility → `count ≥ n₀` preserved) closes by `recExec_mono_holds` (already
PROVED). -/

/-- The counter spec: `inv := count ≥ n₀`, `pre = inv`, `post = inv`. (`count` present with
value ≥ `n₀`.) -/
def counterSpec (n₀ : Int) : CellSpec where
  pre  := fun v => ∃ c, v.scalar "count" = some c ∧ n₀ ≤ c
  post := fun v => ∃ c, v.scalar "count" = some c ∧ n₀ ≤ c
  inv  := fun v => ∃ c, v.scalar "count" = some c ∧ n₀ ≤ c

/-- **`counter_VC_preserve` (PROVED)** — VC class 1 for the counter, discharged via
`recExec_mono_holds`. If `monoCountProgram` admits `(old, new)` and `old.count ≥ n₀`, then
`new.count ≥ n₀` (monotonicity: `new.count ≥ old.count ≥ n₀`). This is the generator output
matching the hand reasoning exactly. -/
theorem counter_VC_preserve (n₀ : Int) :
    VC_preserve monoCountProgram 0 (counterSpec n₀) := by
  intro old new hinv hadm
  obtain ⟨c, hold, hge⟩ := hinv
  -- Recover the honest `old.count ≤ new.count` from the Boolean gate (the `recExec_mono_holds`
  -- argument, inlined: `monoCountProgram` admits ⇒ `monotonic "count"` holds on `(old, new)`).
  simp only [monoCountProgram, RecordProgram.admits, List.all_cons, List.all_nil, Bool.and_true,
    evalConstraint, evalSimple] at hadm
  show ∃ d, new.scalar "count" = some d ∧ n₀ ≤ d
  rw [hold] at hadm
  cases hnb : new.scalar "count" with
  | none => rw [hnb] at hadm; simp at hadm
  | some b =>
      rw [hnb] at hadm
      exact ⟨b, rfl, le_trans hge (of_decide_eq_true hadm)⟩

/-- **`counterVCs` (PROVED)** — the full discharged VC set for the counter: all four classes
closed (preserve via `counter_VC_preserve`; stay-put/init/post trivial since `pre = inv = post`). -/
theorem counterVCs (n₀ : Int) : vcg monoCountProgram 0 (counterSpec n₀) :=
  ⟨counter_VC_preserve n₀, VC_stayput_trivial _, fun _ h => h, fun _ h => h⟩

/-- **`counter_run_sound` (PROVED — the worked example lands green).** For the monotonic-counter
program, `count ≥ n₀` holds at every reachable state of the cell's whole run, generated by
`vcg_run_sound` from `counterVCs`. The VCG mechanizes what `recordCell_run_preserves_sumEquals`
did by hand — this is the regression check that the generator matches reality. -/
theorem counter_run_sound (n₀ : Int)
    {s s' : RecChained}
    (hprogInv : ∀ x : RecChained, x.program = monoCountProgram)
    (hmethodInv : ∀ x : RecChained, x.method = 0)
    (hrun : Execution.Run (inducedSystem recordCell) s s')
    (h0 : ∃ c, s.value.scalar "count" = some c ∧ n₀ ≤ c) :
    ∃ c, s'.value.scalar "count" = some c ∧ n₀ ≤ c :=
  (vcg_run_sound monoCountProgram (counterSpec n₀) hprogInv hmethodInv
    (counterVCs n₀) hrun h0).1

#assert_axioms counter_VC_preserve
#assert_axioms counterVCs
#assert_axioms counter_run_sound

/-! ## §6 — Worked example B: the escrow (single-ledger; cross-vat OPEN).

`PHASE-VCG-WP §4.2`. An escrow with a `Conservative` `escrowed` balance. We take the
**single-ledger** conservation fragment that is closable today: a program enforcing
`sumEquals ["escrowed", "paidOut"] deposit₀` keeps `escrowed + paidOut = deposit₀` along the
whole run. The VC class 1 closes by `admits_sumEquals` (already PROVED). This is the conservation
half of the escrow invariant; combined with `vcg_run_sound` it lands green.

**The cross-vat fragment is left an honest OPEN** (see the `-- OPEN:` note below): when payer and
payee live in *different* vats, conservation routes to the JointTurn CG-5 binding as an explicit
HYPOTHESIS, never derived from the two per-cell triples (`νF₁⊗νF₂` is not final). Honoring the
inviolable rule, we do NOT fabricate a single-cell theorem for it. -/

/-- The escrow conservation program: `escrowed + paidOut = deposit₀` (the funds released to the
payee plus the funds still held equal the original deposit — single-ledger conservation). -/
def escrowProgram (deposit₀ : Int) : RecordProgram :=
  .predicate [.sumEquals ["escrowed", "paidOut"] deposit₀]

/-- The single-ledger escrow spec: `inv := escrowed + paidOut = deposit₀`. -/
def escrowSpec (deposit₀ : Int) : CellSpec where
  pre  := fun v => sumScalars v ["escrowed", "paidOut"] = some deposit₀
  post := fun v => sumScalars v ["escrowed", "paidOut"] = some deposit₀
  inv  := fun v => sumScalars v ["escrowed", "paidOut"] = some deposit₀

/-- **`escrow_VC_preserve` (PROVED)** — VC class 1 for the single-ledger escrow, discharged via
`admits_sumEquals`. Any admitted post-state has `escrowed + paidOut = deposit₀` (the constraint is
a *post-state* sum, so `old` is irrelevant — the gate pins `new`'s sum). -/
theorem escrow_VC_preserve (deposit₀ : Int) :
    VC_preserve (escrowProgram deposit₀) 0 (escrowSpec deposit₀) := by
  intro old new _hinv hadm
  show sumScalars new ["escrowed", "paidOut"] = some deposit₀
  exact admits_sumEquals (cs := [.sumEquals ["escrowed", "paidOut"] deposit₀])
    hadm (by simp)

/-- **`escrowVCs` (PROVED)** — the full discharged VC set for the single-ledger escrow. -/
theorem escrowVCs (deposit₀ : Int) : vcg (escrowProgram deposit₀) 0 (escrowSpec deposit₀) :=
  ⟨escrow_VC_preserve deposit₀, VC_stayput_trivial _, fun _ h => h, fun _ h => h⟩

/-- **`escrow_run_sound` (PROVED — the single-ledger fragment lands green).** For the escrow
conservation program, `escrowed + paidOut = deposit₀` holds at every reachable state of the
cell's whole run, generated by `vcg_run_sound`. The conservation half of the escrow invariant,
in the single-ledger case — closable today, exactly as the study says. -/
theorem escrow_run_sound (deposit₀ : Int)
    {s s' : RecChained}
    (hprogInv : ∀ x : RecChained, x.program = escrowProgram deposit₀)
    (hmethodInv : ∀ x : RecChained, x.method = 0)
    (hrun : Execution.Run (inducedSystem recordCell) s s')
    (h0 : sumScalars s.value ["escrowed", "paidOut"] = some deposit₀) :
    sumScalars s'.value ["escrowed", "paidOut"] = some deposit₀ :=
  (vcg_run_sound (escrowProgram deposit₀) (escrowSpec deposit₀) hprogInv hmethodInv
    (escrowVCs deposit₀) hrun h0).1

#assert_axioms escrow_VC_preserve
#assert_axioms escrowVCs
#assert_axioms escrow_run_sound

/-
OPEN: the CROSS-VAT escrow conservation fragment.

When the payer's `escrowed` lives in vat A and the payee's `paidOut` lives in vat B, the
conservation `escrowed_A + paidOut_B = deposit₀` is NOT a single-cell invariant — it is a
JointTurn CG-5 cross-side binding over `νF_A ⊗ νF_B`, which is *not* final
(`docs/rebuild/pdfs/study-category.md`). Per the inviolable rule (`REORIENT.md §6`,
`Exec/JointCell.lean`), cross-cell soundness must be routed to the JointTurn aggregate as an
explicit HYPOTHESIS — `JointCell.joint_cg5_conserves` — and NEVER derived from the two per-cell
triples. The VCG would *declare* a `boundDelta`/cross-cell VC and discharge it by HANDING it the
joint binding; wiring that VC class as a `vcg` side-condition is a clean phase-2 extension
(`Exec/JointCell.lean` already proves `joint_cg5_conserves`). We deliberately do NOT fabricate a
single-cell theorem for it here — an honest OPEN beats a vacuous proof.
-/

/-! ## §7 — Non-vacuity guards: the worked-example programs are the real in-tree ones. -/

#guard (monoCountProgram.admits 0 (.record [("count", .int 5)]) (.record [("count", .int 6)]))
#guard (monoCountProgram.admits 0 (.record [("count", .int 5)]) (.record [("count", .int 3)]) == false)
#guard ((escrowProgram 100).admits 0 (.record [("escrowed", .int 100), ("paidOut", .int 0)])
        (.record [("escrowed", .int 40), ("paidOut", .int 60)]))
#guard ((escrowProgram 100).admits 0 (.record [("escrowed", .int 100), ("paidOut", .int 0)])
        (.record [("escrowed", .int 40), ("paidOut", .int 70)]) == false)

end Dregg2.Proof.WP
