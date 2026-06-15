/-
# Dregg2.Deos.FlowRefine — the flow/policy-refinement DECISION PROCEDURE (the right-skew payoff).

Companion of `Dregg2.Deos.FlowAlgebra` (`docs/FLOW-COMPOSITION-ALGEBRA.md` §Payoff). `FlowAlgebra` pinned
the PRECONDITION of the payoff as a machine-checked theorem: dregg's flow algebra is right-skewed
(RSKA_d⊓ — `flow_choice_right_skewed`), and its order `≤ᶠ` is ONLINE step-by-step SIMULATION, NOT trace
language. Pradic's Theorem 1.4 then says `e ≤ f` is characterized by a finite-graph SIMULATION GAME
(`SG(∅ | {e} ⊢ f)`, Duplicator-win), hence DECIDABLE. THIS module makes that decidability CONSTRUCTIVE
for dregg's `≤ᶠ`: a sound+complete `decideRefines : Flow → Flow → Bool` and a `Decidable (A ≤ᶠ B)` instance.

THE PAYOFF (this module, constructive). The ARGUS "refines" bar — *does flow / caveat-policy A refine B?*
— is `A ≤ᶠ B`, a refinement question over exactly the right-skewed algebra. We deliver:

  * §1 the σ-FREE transition `PStep` — the `Proc`-only projection of `FlowAlgebra.Step`. The linchpin
    observation (proved §3): no `Step` rule's LETTER or SUCCESSOR-`Proc` is gated by the threaded state —
    the state only THREADS (through `setField`), it never decides a move. So the transition graph projects
    to a purely syntactic, finite-branching, ITERATION-FREE relation, on which `procSize` strictly
    decreases (`pstep_decreases`) — the WELL-FOUNDEDNESS that collapses Pradic's Büchi acceptance to a
    finite reachability game.

  * §2 the SIMULATION GAME `DupSim` (the dregg analogue of Pradic's SG): Duplicator wins from `(p, q)` iff
    there is a `PStep`-SIMULATION relating them — `DupSim P Q := ∃ Rel, PSim Rel ∧ Rel P Q`. A Duplicator
    winning strategy IS a simulation relation (the Theorem-1.4 shape). (`DupSim` is a `def` over the
    simulation existential — NOT a nested inductive, which the kernel rejects through `Exists`.)

  * §3 the σ-UNIFORMITY linchpin (`step_to_pstep` / `pstep_to_step`, `dupSim_iff_simFrom`): the projected
    graph is INDEPENDENT of the threaded `Value`, so `SimFrom (P, σ) (Q, σ)` ⟺ `DupSim P Q` for EVERY σ —
    the `∀ σ` of `≤ᶠ` collapses to ONE σ-free game (`dupSim_iff_sim`). This is what lets a `Bool` decision
    be SOUND+COMPLETE against the infinite-state `≤ᶠ`.

  * §4 the DECIDABLE refinement check `decideRefines : Proc → Proc → Bool` (the deliverable), with
    `decideRefines_iff` : `decideRefines A B = true ↔ A ≤ᶠ B` (sound + complete, LAW #1), and the full
    `Decidable (A ≤ᶠ B)` instance (`instDecidableSim`). It runs a FUEL-bounded greatest-simulation check
    `decideFuel` on the FINITE σ-free move-graph (`moves`, sound+complete for `PStep`), structurally
    recursive in the fuel ⟹ KERNEL-REDUCIBLE (so `#guard`/`decide` evaluate it; no `native_decide`), with
    fuel `procSize + 1` always sufficient (the simulated side strictly shrinks).

  * §5 NON-VACUITY (`#guard`): a REAL refine that HOLDS (`decideRefines (early) (late) = true`, the half —
    `flow_choice_halfdistrib` decided) AND a non-refine that is REJECTED (`decideRefines (late) (early) =
    false`, the right-skew — `flow_choice_right_skewed` decided). The check AGREES with the hand proofs of
    `FlowAlgebra` on its own counterexample, on BOTH polarities — so it is not vacuous (it accepts neither
    everything nor nothing), and it MECHANICALLY recomputes the right-skew.

LAW #1: the proof is the spec — `decideRefines_iff` IS the specification of the decision procedure.
Reuses `FlowAlgebra`'s `≤ᶠ` / `Flow.Sim` / `SimFrom` / `IsSim` / `Proc` / `Step` denotation UNCHANGED
(1 umbrella import; does NOT redefine them). Axiom-clean (`#assert_all_clean`), no `sorry`, no
`native_decide`. `lake build Dregg2.Deos.FlowRefine` green (LOCAL). Additive: a NEW module, touches NO
existing proof.
-/
import Dregg2.Deos.FlowAlgebra

namespace Dregg2.Deos.FlowRefine

open Dregg2.Exec (Value)
open Dregg2.Deos.FlowAlgebra

set_option linter.dupNamespace false

/-! ## §1 — The σ-FREE transition `PStep` (the `Proc`-only projection of `Step`).

The decision procedure must reason about the transition GRAPH, which `FlowAlgebra.Step` threads a `Value`
through. The linchpin observation (proved §3): no `Step` rule's LETTER or SUCCESSOR-`Proc` depends on the
state value — `emit`/`wr`/`ch`/`seqp` all fire a letter and move to a successor determined by the `Proc`
SYNTAX; the state only THREADS (through `setField`), it never gates a move. So the graph projects to a
purely syntactic `PStep : Proc → Letter → Proc → Prop`, finite-branching and ITERATION-FREE (every move
strictly shrinks the `Proc`). The game §2 lives on `PStep`; §3 transports it back to `Step` for every σ.

`PStep` mirrors `Step` rule-for-rule, dropping the value. -/

/-- **`PStep p ℓ p'`** — the σ-free labelled transition: `p` fires letter `ℓ` and becomes `p'`, ignoring
state. The syntactic shadow of `FlowAlgebra.Step`. -/
inductive PStep : Proc → Letter → Proc → Prop where
  /-- `emit ℓ` fires `ℓ`, halts. -/
  | emit (ℓ : Letter) : PStep (.emit ℓ) ℓ .done
  /-- `wr ℓ f v` fires its output letter `ℓ`, halts (the write is invisible to the PROJECTED graph). -/
  | wr (ℓ : Letter) (f : Dregg2.Exec.FieldName) (v : Int) : PStep (.wr ℓ f v) ℓ .done
  /-- BRANCH left: take `p`'s first move. -/
  | chL {p q p' : Proc} {ℓ : Letter} (h : PStep p ℓ p') : PStep (.ch p q) ℓ p'
  /-- BRANCH right: take `q`'s first move. -/
  | chR {p q q' : Proc} {ℓ : Letter} (h : PStep q ℓ q') : PStep (.ch p q) ℓ q'
  /-- SEQ: the right factor `r` takes a non-halting step; stay in the sequence. -/
  | seqR {p r r' : Proc} {ℓ : Letter} (h : PStep r ℓ r') : PStep (.seqp p r) ℓ (.seqp p r')
  /-- SEQ hand-off: `r = done`; fire `p`'s first move. -/
  | seqDone {p p' : Proc} {ℓ : Letter} (h : PStep p ℓ p') : PStep (.seqp p .done) ℓ p'

/-! ## §1a — `PStep` STRICTLY SHRINKS a structural measure (so the game is WELL-FOUNDED).

The measure `procSize` counts constructors (ignoring the `Nat`/`Int` payloads, and sending the halted
process to `0` so a leaf-fire `emit ℓ → done` strictly decreases); every `PStep` move strictly decreases
it. This is what makes dregg's simulation game terminating WITHOUT Pradic's Büchi condition: there are no
infinite plays because there is no iteration `(−)°`, so a strictly-decreasing measure exists. The decision
procedure §4 recurses on this measure. -/

/-- `procSize p` — the payload-free node-count of `p`, with `procSize done = 0` (the well-founded measure
for the game / the decision recursion). -/
def procSize : Proc → Nat
  | .done       => 0
  | .emit _     => 1
  | .wr _ _ _   => 1
  | .ch p q     => 1 + procSize p + procSize q
  | .seqp p r   => 1 + procSize p + procSize r

/-- **Every `PStep` move strictly shrinks `procSize`.** The graph is well-founded ⟹ all plays terminate
⟹ the game (and the decision recursion) is well-defined without a Büchi/fixpoint condition. -/
theorem pstep_decreases {p : Proc} {ℓ : Letter} {p' : Proc} (h : PStep p ℓ p') :
    procSize p' < procSize p := by
  induction h with
  | emit ℓ => simp [procSize]
  | wr ℓ f v => simp [procSize]
  | chL h ih => simp only [procSize]; omega
  | chR h ih => simp only [procSize]; omega
  | seqR h ih => simp only [procSize]; omega
  | seqDone h ih => simp only [procSize]; omega

/-! ## §2 — The SIMULATION GAME `DupSim` (the dregg analogue of Pradic's SG; Theorem 1.4).

The simulation game `SG(∅ | {p} ⊢ q)`: Spoiler (controlling the SIMULATED side `p`) picks a letter-move
`p →ℓ p₁`; Duplicator (controlling the SIMULATOR `q`) must answer with a SAME-letter move `q →ℓ q₁`; play
continues from `(p₁, q₁)`. Duplicator WINS iff she can answer FOREVER — but `pstep_decreases` makes every
play FINITE, so "answer forever" = "answer at every reachable pair until the simulated side is stuck".

A DUPLICATOR WINNING STRATEGY is precisely a `PStep`-SIMULATION relation containing the start pair. We
encode this DIRECTLY as the simulation existential (a `def`, NOT a nested inductive — Lean's kernel
rejects an inductive that recurses through `Exists`). This is exactly the largest-simulation / Theorem-1.4
characterization, specialized to the iteration-free fragment where the Büchi condition is vacuous. -/

/-- **`PSim Rel`** — `Rel` is a σ-free simulation: every Spoiler `PStep` of the left side is matched by a
SAME-letter `PStep` of the right side, preserving `Rel`. (The `Step`-level `IsSim`, projected to `Proc`.) -/
def PSim (Rel : Proc → Proc → Prop) : Prop :=
  ∀ p q, Rel p q → ∀ ℓ p', PStep p ℓ p' → ∃ q', PStep q ℓ q' ∧ Rel p' q'

/-- **`DupSim P Q`** — Duplicator wins the dregg simulation game `SG(∅ | {P} ⊢ Q)`: there is a winning
strategy = a `PStep`-simulation `Rel` (`PSim`) containing `(P, Q)`. The dregg SG (Theorem-1.4 shape). -/
def DupSim (P Q : Proc) : Prop := ∃ Rel, PSim Rel ∧ Rel P Q

/-! ## §3 — The σ-UNIFORMITY linchpin: `PStep` ≅ `Step`, and `SimFrom` is state-uniform.

Two transports tie the σ-free game to the σ-threaded `Step`:

  * `step_to_pstep` — every `Step (p, σ) ℓ (p', σ')` PROJECTS to `PStep p ℓ p'` (forget the state).
  * `pstep_to_step` — every `PStep p ℓ p'` LIFTS to a `Step (p, σ) ℓ (p', σ')` from ANY σ (the state
    threads to SOME σ', which we recover). The successor σ' is determined, but the LETTER and successor
    `Proc` are not gated by σ.

Together: the reachable letters/successor-`Proc`s are state-independent. Hence `SimFrom (P, σ) (Q, σ)` is
equivalent to `DupSim P Q` for EVERY σ — the `∀ σ` of `≤ᶠ` collapses (`dupSim_iff_simFrom`). -/

/-- Forget the state: a `Step` is a `PStep` on the same letter + successor `Proc`. -/
theorem step_to_pstep {p p' : Proc} {σ σ' : Value} {ℓ : Letter}
    (h : Step (p, σ) ℓ (p', σ')) : PStep p ℓ p' := by
  generalize hc : (p, σ) = c at h
  generalize hd : (p', σ') = d at h
  induction h generalizing p σ p' σ' with
  | emit ℓ σ₀ => cases hc; cases hd; exact PStep.emit ℓ
  | wr ℓ f v σ₀ => cases hc; cases hd; exact PStep.wr ℓ f v
  | chL pp qq pp' σ₀ σ₀' ℓ₀ hstep ih => cases hc; cases hd; exact PStep.chL (ih rfl rfl)
  | chR pp qq qq' σ₀ σ₀' ℓ₀ hstep ih => cases hc; cases hd; exact PStep.chR (ih rfl rfl)
  | seqR pp rr rr' σ₀ σ₀' ℓ₀ hstep ih => cases hc; cases hd; exact PStep.seqR (ih rfl rfl)
  | seqDone pp pp' σ₀ σ₀' ℓ₀ hstep ih => cases hc; cases hd; exact PStep.seqDone (ih rfl rfl)

/-- Lift to the state: a `PStep` realizes as a `Step` from ANY σ (to a determined σ'). The LETTER and
successor `Proc` are exactly the `PStep`'s — the state only threads. -/
theorem pstep_to_step {p p' : Proc} {ℓ : Letter} (h : PStep p ℓ p') (σ : Value) :
    ∃ σ', Step (p, σ) ℓ (p', σ') := by
  induction h generalizing σ with
  | emit ℓ => exact ⟨σ, Step.emit ℓ σ⟩
  | wr ℓ f v => exact ⟨setField σ f v, Step.wr ℓ f v σ⟩
  | chL h ih => obtain ⟨σ', hs⟩ := ih σ; exact ⟨σ', Step.chL _ _ _ σ σ' _ hs⟩
  | chR h ih => obtain ⟨σ', hs⟩ := ih σ; exact ⟨σ', Step.chR _ _ _ σ σ' _ hs⟩
  | seqR h ih => obtain ⟨σ', hs⟩ := ih σ; exact ⟨σ', Step.seqR _ _ _ σ σ' _ hs⟩
  | seqDone h ih => obtain ⟨σ', hs⟩ := ih σ; exact ⟨σ', Step.seqDone _ _ σ σ' _ hs⟩

/-- **`DupSim → SimFrom`** at every σ. The winning Duplicator relation, transported to states: relate
`(p, σp)` ↦ `(q, σq)` whenever `Rel p q` (states FREE). It is a `Step`-simulation by `step_to_pstep`
(Spoiler's `Step` projects to a `PStep`) + the `PSim` answer + `pstep_to_step` (Duplicator's `PStep` answer
lifts to a `Step`). -/
theorem dupSim_to_simFrom {P Q : Proc} (h : DupSim P Q) (σ : Value) :
    SimFrom (P, σ) (Q, σ) := by
  obtain ⟨Rel, hsim, hPQ⟩ := h
  refine ⟨fun c c' => Rel c.1 c'.1, ?_, hPQ⟩
  rintro ⟨p, σp⟩ ⟨q, σq⟩ hpq ℓ ⟨p', σp'⟩ hstep
  have hp : PStep p ℓ p' := step_to_pstep hstep
  obtain ⟨q', hpq', hrel'⟩ := hsim p q hpq ℓ p' hp
  obtain ⟨σq', hqstep⟩ := pstep_to_step hpq' σq
  exact ⟨(q', σq'), hqstep, hrel'⟩

/-- The Duplicator strategy extracted from a `Step`-simulation `Rel`: the σ-free relation "`p ~ q` whenever
some states relate them under `Rel`" is a `PSim`. Spoiler's `PStep` lifts to a `Step` (`pstep_to_step`),
`Rel` answers with a `Step` (its simulation property), the answer projects to a `PStep` (`step_to_pstep`),
and the targets stay related — so the projected relation is `PSim`-closed. -/
theorem psim_of_step_sim {Rel : (Proc × Value) → (Proc × Value) → Prop} (hsim : IsSim Rel) :
    PSim (fun p q => ∃ σp σq, Rel (p, σp) (q, σq)) := by
  rintro p q ⟨σp, σq, hrel⟩ ℓ p' hpstep
  obtain ⟨σp', hstepP⟩ := pstep_to_step hpstep σp
  obtain ⟨⟨q', σq'⟩, hstepQ, hrel'⟩ := hsim (p, σp) (q, σq) hrel ℓ (p', σp') hstepP
  exact ⟨q', step_to_pstep hstepQ, σp', σq', hrel'⟩

/-- **`SimFrom → DupSim`** (from any single σ). The σ-free projection of the simulation witnessing
`SimFrom` is a winning Duplicator strategy. -/
theorem simFrom_to_dupSim {P Q : Proc} {σ : Value} (h : SimFrom (P, σ) (Q, σ)) :
    DupSim P Q := by
  obtain ⟨Rel, hsim, hPQ⟩ := h
  exact ⟨fun p q => ∃ σp σq, Rel (p, σp) (q, σq), psim_of_step_sim hsim, σ, σ, hPQ⟩

/-- **`dupSim_iff_simFrom` — the Theorem-1.4 shape (the SG characterization).** Duplicator wins the
simulation game `SG(∅ | {P} ⊢ Q)` IFF `Q` step-by-step `Step`-simulates `P` from σ — for EVERY σ, since
the game is σ-free. The right-hand side is `≤ᶠ`'s per-state obligation; the left is a finite, decidable
game (§4). This is the dregg analogue of Pradic's Theorem 1.4 `(2 ⇔ 3)`. -/
theorem dupSim_iff_simFrom {P Q : Proc} (σ : Value) :
    DupSim P Q ↔ SimFrom (P, σ) (Q, σ) :=
  ⟨fun h => dupSim_to_simFrom h σ, fun h => simFrom_to_dupSim h⟩

/-- **`dupSim_iff_sim` — the SG game decides the flow order `≤ᶠ`.** `P ≤ᶠ Q` (online simulation at EVERY
start state) IFF Duplicator wins the single σ-free game `SG(∅ | {P} ⊢ Q)`. The `∀ σ` of `≤ᶠ` collapses to
ONE game: state-uniformity (`dupSim_iff_simFrom`) makes the game's verdict state-independent. THIS is the
reduction of refinement to a finite simulation game. -/
theorem dupSim_iff_sim {P Q : Proc} : DupSim P Q ↔ P ≤ᶠ Q := by
  constructor
  · intro h σ; exact dupSim_to_simFrom h σ
  · intro h; exact simFrom_to_dupSim (h (.record []))

/-! ## §4 — The DECIDABLE refinement check `decideRefines` (the deliverable).

`moves` enumerates the σ-free game's out-edges (a finite list, sound+complete for `PStep`). The decision
runs a FUEL-bounded greatest-simulation check `decideFuel` on it: at each round, every Spoiler move of the
left side must have a SAME-letter Duplicator answer continuing to simulate (one fewer round). It is
STRUCTURALLY recursive in the fuel ⟹ the kernel REDUCES it (`#guard`/`decide` evaluate; no `native_decide`),
matching letters by `==` on `Nat` (so NO `DecidableEq Value` is needed — the states never enter the game).
Fuel `procSize P + 1` always suffices (`pstep_decreases`), which §4b pins as EXACTLY `DupSim`. -/

/-- The finite list of `(letter, successor)` moves of a `Proc` under `PStep` — the game's out-edges. The
`seqp p r` clause mirrors the two `seqp` `PStep` rules: `seqp p done` hands off to `p`'s moves; a steppable
`r` threads first, wrapping each of `r`'s moves under `seqp p ·`. (`done` cannot move, so the two are
exclusive — exactly the rule side-conditions.) -/
def moves : Proc → List (Letter × Proc)
  | .done       => []
  | .emit ℓ     => [(ℓ, .done)]
  | .wr ℓ _ _   => [(ℓ, .done)]
  | .ch p q     => moves p ++ moves q
  | .seqp p .done => moves p
  | .seqp p r   => (moves r).map (fun m => (m.1, .seqp p m.2))

/-- `moves` is SOUND for `PStep`: every listed move is a real `PStep`. -/
theorem moves_sound : ∀ (p : Proc) (ℓ : Letter) (p' : Proc),
    (ℓ, p') ∈ moves p → PStep p ℓ p' := by
  intro p
  induction p with
  | done => intro ℓ p' h; simp [moves] at h
  | emit l => intro ℓ p' h; simp only [moves, List.mem_singleton, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h; exact PStep.emit _
  | wr l f v => intro ℓ p' h; simp only [moves, List.mem_singleton, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h; exact PStep.wr _ _ _
  | ch p q ihp ihq =>
      intro ℓ p' h; simp only [moves, List.mem_append] at h
      rcases h with h | h
      · exact PStep.chL (ihp ℓ p' h)
      · exact PStep.chR (ihq ℓ p' h)
  | seqp p r ihp ihr =>
      intro ℓ p' h
      cases r with
      | done => simp only [moves] at h; exact PStep.seqDone (ihp ℓ p' h)
      | emit l => simp only [moves, List.mem_map] at h
                  obtain ⟨m, hm, heq⟩ := h; rw [Prod.mk.injEq] at heq
                  obtain ⟨rfl, rfl⟩ := heq; exact PStep.seqR (ihr m.1 m.2 hm)
      | wr l f v => simp only [moves, List.mem_map] at h
                    obtain ⟨m, hm, heq⟩ := h; rw [Prod.mk.injEq] at heq
                    obtain ⟨rfl, rfl⟩ := heq; exact PStep.seqR (ihr m.1 m.2 hm)
      | ch a b => simp only [moves, List.mem_map] at h
                  obtain ⟨m, hm, heq⟩ := h; rw [Prod.mk.injEq] at heq
                  obtain ⟨rfl, rfl⟩ := heq; exact PStep.seqR (ihr m.1 m.2 hm)
      | seqp a b => simp only [moves, List.mem_map] at h
                    obtain ⟨m, hm, heq⟩ := h; rw [Prod.mk.injEq] at heq
                    obtain ⟨rfl, rfl⟩ := heq; exact PStep.seqR (ihr m.1 m.2 hm)

/-- `moves` is COMPLETE for `PStep`: every real `PStep` is listed. -/
theorem moves_complete {p : Proc} {ℓ : Letter} {p' : Proc} (h : PStep p ℓ p') :
    (ℓ, p') ∈ moves p := by
  induction h with
  | emit ℓ => simp [moves]
  | wr ℓ f v => simp [moves]
  | chL h ih => simp only [moves, List.mem_append]; exact Or.inl ih
  | chR h ih => simp only [moves, List.mem_append]; exact Or.inr ih
  | seqR h ih =>
      rename_i p r r' ℓ'
      cases r with
      | done => cases h
      | emit l => simp only [moves, List.mem_map]; exact ⟨(ℓ', r'), ih, rfl⟩
      | wr l f v => simp only [moves, List.mem_map]; exact ⟨(ℓ', r'), ih, rfl⟩
      | ch a b => simp only [moves, List.mem_map]; exact ⟨(ℓ', r'), ih, rfl⟩
      | seqp a b => simp only [moves, List.mem_map]; exact ⟨(ℓ', r'), ih, rfl⟩
  | seqDone h ih => simp only [moves]; exact ih

/-- **`decideFuel n p q`** — does `q` simulate `p` within `n` rounds (bounded greatest simulation on the
σ-free graph)? Structurally recursive in `n` ⟹ kernel-reducible. -/
def decideFuel : Nat → Proc → Proc → Bool
  | 0, _, _ => false
  | n + 1, p, q =>
      (moves p).all (fun m =>
        (moves q).any (fun m' => m.1 == m'.1 && decideFuel n m.2 m'.2))

/-- More fuel never hurts (one step). -/
theorem decideFuel_mono : ∀ (n : Nat) (p q : Proc),
    decideFuel n p q = true → decideFuel (n + 1) p q = true := by
  intro n
  induction n with
  | zero => intro p q h; simp [decideFuel] at h
  | succ k ih =>
      intro p q h
      simp only [decideFuel, List.all_eq_true, List.any_eq_true] at h ⊢
      intro m hm
      obtain ⟨m', hm', hcond⟩ := h m hm
      refine ⟨m', hm', ?_⟩
      rw [Bool.and_eq_true] at hcond ⊢
      exact ⟨hcond.1, ih _ _ hcond.2⟩

/-- More fuel never hurts (any increase). -/
theorem decideFuel_mono_le {n m : Nat} {p q : Proc}
    (hle : n ≤ m) (h : decideFuel n p q = true) : decideFuel m p q = true := by
  induction hle with
  | refl => exact h
  | step _ ih => exact decideFuel_mono _ _ _ ih

/-- **`decideFuel` SOUND** — a `true` bounded check is a real `DupSim`. Witness relation:
`fun a b => ∃ k, decideFuel k a b = true`. -/
theorem decideFuel_sound (n : Nat) (p q : Proc) (h : decideFuel n p q = true) : DupSim p q := by
  refine ⟨fun a b => ∃ k, decideFuel k a b = true, ?_, n, h⟩
  rintro a b ⟨k, hk⟩ ℓ a' hstep
  cases k with
  | zero => simp [decideFuel] at hk
  | succ j =>
      simp only [decideFuel, List.all_eq_true, List.any_eq_true] at hk
      obtain ⟨m', hm', hcond⟩ := hk (ℓ, a') (moves_complete hstep)
      rw [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨hℓ, hrec⟩ := hcond
      subst hℓ
      exact ⟨m'.2, moves_sound b m'.1 m'.2 hm', j, hrec⟩

/-- **`decideFuel` COMPLETE** — a real `DupSim` is detected with `procSize p + 1` fuel. Strong induction on
`procSize p` (the simulated side shrinks each round, `pstep_decreases`). -/
theorem decideFuel_complete : ∀ (p q : Proc), DupSim p q → decideFuel (procSize p + 1) p q = true := by
  intro p
  induction hwf : procSize p using Nat.strong_induction_on generalizing p with
  | _ N IH =>
    intro q hsim
    obtain ⟨Rel, hRelSim, hRel⟩ := hsim
    subst hwf
    simp only [decideFuel, List.all_eq_true, List.any_eq_true]
    intro m hm
    obtain ⟨ℓ, p'⟩ := m
    have hstep : PStep p ℓ p' := moves_sound p ℓ p' hm
    obtain ⟨q', hqstep, hrel'⟩ := hRelSim p q hRel ℓ p' hstep
    refine ⟨(ℓ, q'), moves_complete hqstep, ?_⟩
    rw [Bool.and_eq_true]
    refine ⟨by simp, ?_⟩
    have hlt : procSize p' < procSize p := pstep_decreases hstep
    exact decideFuel_mono_le (by omega) (IH (procSize p') hlt p' rfl q' ⟨Rel, hRelSim, hrel'⟩)

/-- **`decideRefines A B` — the refinement DECISION PROCEDURE (the deliverable).** Returns `true` iff `A`
refines `B` in the online simulation order `≤ᶠ`. Computed as the σ-free SG game's bounded verdict at the
canonical (always-sufficient) fuel `procSize A + 1` — kernel-reducible. -/
def decideRefines (A B : Proc) : Bool := decideFuel (procSize A + 1) A B

/-- **`decideRefines_dupSim_iff`** — the decision function decides the σ-free game: `decideRefines A B =
true ↔ DupSim A B`. (`→` is `decideFuel_sound`; `←` is `decideFuel_complete`.) -/
theorem decideRefines_dupSim_iff (A B : Proc) : decideRefines A B = true ↔ DupSim A B :=
  ⟨decideFuel_sound _ A B, decideFuel_complete A B⟩

/-- **`decideRefines_iff` — SOUND + COMPLETE (the spec; LAW #1).** `decideRefines A B = true` IFF
`A ≤ᶠ B`. Soundness (`→`): a `true` verdict yields a Duplicator strategy, which IS a simulation at every σ
(σ-uniformity). Completeness (`←`): a refinement yields a simulation at the canonical state, projected to a
strategy — so the procedure NEVER misses a real refinement and NEVER accepts a non-refinement. This single
`↔` IS the specification of the decision procedure. -/
theorem decideRefines_iff (A B : Proc) : decideRefines A B = true ↔ A ≤ᶠ B :=
  (decideRefines_dupSim_iff A B).trans dupSim_iff_sim

/-- **`instDecidableSim` — `Decidable (A ≤ᶠ B)`.** The refinement relation `≤ᶠ` (online simulation at every
start state) is DECIDABLE: run `decideRefines` and read off `decideRefines_iff`. So `A ≤ᶠ B` is a checkable
proposition — the ARGUS "refines" bar is a decision, not a hope. The `∀ σ` over the infinite state space is
discharged by σ-uniformity (the game is σ-free), so ONE finite check settles it. -/
instance instDecidableSim (A B : Proc) : Decidable (A ≤ᶠ B) :=
  decidable_of_iff (decideRefines A B = true) (decideRefines_iff A B)

/-- **`instDecidableDupSim`** — who wins the dregg simulation game is computable. -/
instance instDecidableDupSim (A B : Proc) : Decidable (DupSim A B) :=
  decidable_of_iff (decideRefines A B = true) (decideRefines_dupSim_iff A B)

/-! ## §5 — NON-VACUITY (`#guard`): the procedure decides `FlowAlgebra`'s OWN counterexample, BOTH ways.

A decision procedure that returned `true` always (or `false` always) would be vacuous. We pin it against
the two headline facts of `FlowAlgebra`, on the SAME concrete flows (`Pf := fire 1`, `Qf := fire 2`,
`Rr := run 0 "b" 1`):

  * THE HALF holds → `decideRefines (early) (late) = true` (agrees with `flow_choice_halfdistrib`).
  * THE RIGHT-SKEW (converse fails) → `decideRefines (late) (early) = false` (agrees with
    `flow_choice_right_skewed`).

Both are `#guard`-checked by KERNEL reduction of the structurally-recursive `decideFuel` (NOT
`native_decide`). The procedure DISTINGUISHES the two directions — exactly the right-skew, MECHANICALLY
decided — so it is not vacuous. -/

open Dregg2.Deos.FlowAlgebra (Pf Qf Rr)

/-- The EARLY side `(P ⋆ R) ⊔ (Q ⋆ R)` of `FlowAlgebra`'s counterexample. -/
def earlyEx : Proc := (Pf ⋆ᶠ Rr) ⊔ᶠ (Qf ⋆ᶠ Rr)

/-- The LATE side `(P ⊔ Q) ⋆ R` of `FlowAlgebra`'s counterexample. -/
def lateEx : Proc := (Pf ⊔ᶠ Qf) ⋆ᶠ Rr

-- NON-VACUITY, both polarities, kernel-evaluated:
#guard decideRefines earlyEx lateEx == true    -- a real refine ACCEPTED (the half)
#guard decideRefines lateEx earlyEx == false   -- a non-refine REJECTED (the right-skew)
#guard decideRefines earlyEx earlyEx == true   -- reflexive: a flow refines itself
#guard decideRefines (Flow.fire 1) (Flow.fire 2) == false  -- distinct letters: fire 1 ⋠ fire 2

/-- **`decideRefines_half` — the decision AGREES with `flow_choice_halfdistrib` (as a PROPOSITION).** The
half is decided `true`, and that verdict IS the real `≤ᶠ` (via the spec `decideRefines_iff`). Two
independent witnesses — the recursive decider and the hand-built `halfRel` simulation — agree. -/
theorem decideRefines_half : decideRefines earlyEx lateEx = true := by
  rw [decideRefines_iff]; exact flow_choice_halfdistrib Pf Qf Rr

/-- **`decideRefines_rightskew` — the decision AGREES with `flow_choice_right_skewed`.** The right-skew is
decided `false`: the procedure rejects EXACTLY what the headline proves is not a refinement
(`decideRefines = false ↔ ¬ ≤ᶠ`, via the spec). The COMPUTED rejection and the PROVED non-refinement are
the same fact — the decision procedure recomputes the right-skew. -/
theorem decideRefines_rightskew : decideRefines lateEx earlyEx = false := by
  rw [← Bool.not_eq_true, decideRefines_iff]
  exact flow_choice_right_skewed

/-! ## §7 — THE `@[export]` BOUNDARY: `dregg_decide_refines` (the deploy gate runs the PROVED procedure).

`dregg-deploy/src/refine.rs` decides its safe-upgrade / intent-conformance gates by `A ≤ᶠ B` — exactly
`decideRefines`. Until now it ran a *Rust mirror* of `decideRefines` (faithful, but a re-implementation
the Rust cannot re-prove). This section exposes `decideRefines` itself as a C-ABI `String → String`
entry the linked Lean archive runs, so the deploy gate computes its verdict FROM the proven procedure —
the same `@[export]`-bridge discipline as `FinalityGate.dregg_blocklace_finalize` / `dregg_tau_order`.

The wire is a PREORDER (Polish-prefix) token stream of the σ-free `Proc` — the fragment the deploy
side ever builds (`done` / `emit` / `ch` / `seqp`; `wr` never appears in a lowered deploy flow, and
even if it did it would project to its `emit ℓ` since `moves (wr ℓ _ _) = moves (emit ℓ)`). Each node
emits ONE space-separated token, its children following in order (fixed arity per token ⇒ unambiguous):

    PTOK  := "d"            -- done            (arity 0)
           | "e" Nat        -- emit ℓ          (arity 0)
           | "c"            -- ch  a b         (arity 2: a then b follow)
           | "s"            -- seqp a b        (arity 2: a then b follow)
    PROCW := PTOK (" " PTOK)*          -- the preorder traversal
    INPUT := "A=" PROCW ";B=" PROCW   -- the two flows to compare
    OUTPUT:= "1" | "0" | "ERR"        -- A ≤ᶠ B  |  A ⋠ B  |  malformed wire (fail-closed)

`decideRefines` is σ-free and `decideFuel` is structurally recursive in its fuel, so the gate's body
is KERNEL-reducible — the §7 `#guard`s evaluate it with `decide`/`#guard` (no `native_decide`). -/

/-- Parse a `Nat` strictly: the body must be non-empty ASCII digits. Fail-closed. (A local copy of the
`FinalityGate` codec helper — `FlowRefine` imports only `FlowAlgebra`, so the wire codec is
self-contained.) -/
def parseNat? (s : String) : Option Nat :=
  if s.isEmpty then none else
    if s.all (fun c => c.isDigit) then s.toNat? else none

/-- Strip a required `prefix` from `s`, returning the remainder, or `none` if absent. (Local copy; see
`parseNat?`.) -/
def stripReq? (pfx s : String) : Option String :=
  if s.startsWith pfx then some (String.ofList (s.toList.drop pfx.length)) else none

/-- Encode a σ-free `Proc` as its preorder token list (the `PROCW` body, pre-`intercalate`). `wr`
folds to its `emit ℓ` token (state-free: `moves` treats them identically), so the codec covers the
whole `Proc` even though deploy flows only ever use `done`/`emit`/`ch`/`seqp`. -/
def encodeProcToks : Proc → List String
  | .done       => ["d"]
  | .emit ℓ     => ["e" ++ toString ℓ]
  | .wr ℓ _ _   => ["e" ++ toString ℓ]        -- σ-free: same move-set as `emit ℓ`
  | .ch p q     => "c" :: (encodeProcToks p ++ encodeProcToks q)
  | .seqp p r   => "s" :: (encodeProcToks p ++ encodeProcToks r)

/-- **`encodeProc`** — the `PROCW` wire form (space-joined preorder tokens). -/
def encodeProc (p : Proc) : String := String.intercalate " " (encodeProcToks p)

-- `Proc` (decidable) equality — needed for the codec's `decode ∘ encode = id` `#guard`s (which compare
-- `Option Proc` / `Option (Proc × Proc)` via `==`). Derivable: every payload (`Letter = Nat`,
-- `FieldName = String`, `Int`) has both. `deriving instance` takes no doc comment, hence this `--`.
deriving instance DecidableEq, BEq for Proc

/-- Parse ONE `Proc` off the front of a token list, returning it paired with the UNCONSUMED tail.
Structurally recursive in an explicit `fuel : Nat` (seeded to the token-list length by `decodeProc`,
always sufficient: each node consumes ≥ 1 token so the parse depth is ≤ the token count) ⇒ kernel
reducible (the `#guard`s `decide`-evaluate it; no `native_decide`). Fail-closed: out of fuel, a
malformed token, or a `c`/`s` whose children run off the end all yield `none`. -/
def parseProcFuel : Nat → List String → Option (Proc × List String)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, t :: rest =>
    if t == "d" then some (.done, rest)
    else if t.startsWith "e" then
      match parseNat? (String.ofList (t.toList.drop 1)) with
      | some n => some (.emit n, rest)
      | none   => none
    else if t == "c" then
      match parseProcFuel fuel rest with
      | some (a, rest₁) =>
        match parseProcFuel fuel rest₁ with
        | some (b, rest₂) => some (.ch a b, rest₂)
        | none => none
      | none => none
    else if t == "s" then
      match parseProcFuel fuel rest with
      | some (a, rest₁) =>
        match parseProcFuel fuel rest₁ with
        | some (b, rest₂) => some (.seqp a b, rest₂)
        | none => none
      | none => none
    else none

/-- **`decodeProc`** — parse a `PROCW` body into a `Proc`. Fail-closed: the token stream must parse to
EXACTLY one `Proc` with NO leftover tokens (a trailing token is a malformed wire). Fuel = token count
(always sufficient — every `Proc` node consumes at least its own token). -/
def decodeProc (s : String) : Option Proc :=
  let toks := s.splitOn " "
  match parseProcFuel toks.length toks with
  | some (p, []) => some p
  | _ => none

/-- **`decodeRefineWire`** — parse the full `INPUT` grammar into the pair `(A, B)` to compare.
Fail-closed on any deviation (missing `A=`/`;B=`, a malformed sub-`Proc`, or leftover tokens). -/
def decodeRefineWire (s : String) : Option (Proc × Proc) := do
  let body ← stripReq? "A=" s
  match body.splitOn ";B=" with
  | [aS, bS] => do
      let a ← decodeProc aS
      let b ← decodeProc bS
      pure (a, b)
  | _ => none

/-- **`decideRefinesGate`** — THE GATE BODY. Decode the wire `(A, B)`, run the PROVED `decideRefines`,
and return `"1"` (refines) / `"0"` (does not) / `"ERR"` (fail-closed on a malformed wire). This is
EXACTLY the decision procedure §4, exposed as the `String → String` the linked Lean archive runs at
the deploy gate. -/
def decideRefinesGate (s : String) : String :=
  match decodeRefineWire s with
  | some (a, b) => if decideRefines a b then "1" else "0"
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_decide_refines]` — the C-ABI entry `dregg-deploy`'s FFI bridge
(`dregg-lean-ffi`) calls. Same `String → String` shape as `dregg_blocklace_finalize` (the C shim
wraps it): the deploy gate passes the two wire-encoded flows and reads back the verified verdict. -/
@[export dregg_decide_refines]
def dregg_decide_refines (s : String) : String := decideRefinesGate s

/-! ### §7a — THE EXPORT CARRIES THE PROOF: gating on `dregg_decide_refines` IS gating on `≤ᶠ`.

The two soundness teeth — the export's `"1"` IS the proven `decideRefines = true` (hence `A ≤ᶠ B`),
and its `"0"` IS `decideRefines = false` (hence `A ⋠ B`). So the deploy gate, gated on a `"1"` from
this export, is gated on the verified refinement relation BY CONSTRUCTION (not "agreement-checked"). -/

/-- **`gate_one_iff_decideRefines`.** For any wire decoding to `(A, B)`, the gate returns `"1"` IFF the
PROVED `decideRefines A B = true`. The string verdict IS the decision procedure's verdict. -/
theorem gate_one_iff_decideRefines (s : String) (a b : Proc)
    (h : decodeRefineWire s = some (a, b)) :
    decideRefinesGate s = "1" ↔ decideRefines a b = true := by
  unfold decideRefinesGate
  rw [h]
  by_cases hd : decideRefines a b = true <;> simp [hd]

/-- **`gate_one_iff_sim` (the soundness crown).** For any wire decoding to `(A, B)`, the gate returns
`"1"` IFF `A ≤ᶠ B` — the verified online-simulation refinement order. Composing
`gate_one_iff_decideRefines` with the spec `decideRefines_iff`: the deploy gate admitting an upgrade
(`"1"`) ⟺ the new flow genuinely refines the running one. The live deploy gate is gated on the
VERIFIED relation, by construction. -/
theorem gate_one_iff_sim (s : String) (a b : Proc)
    (h : decodeRefineWire s = some (a, b)) :
    decideRefinesGate s = "1" ↔ a ≤ᶠ b :=
  (gate_one_iff_decideRefines s a b h).trans (decideRefines_iff a b)

/-- **`gate_zero_iff_not_sim` (the no-fail-open tooth).** For any wire decoding to `(A, B)`, the gate
returns `"0"` IFF `¬ (A ≤ᶠ B)` — a non-refinement is REJECTED. So the gate never reports `"1"` for an
upgrade that widens behavior (the dual of `gate_one_iff_sim`). -/
theorem gate_zero_iff_not_sim (s : String) (a b : Proc)
    (h : decodeRefineWire s = some (a, b)) :
    decideRefinesGate s = "0" ↔ ¬ (a ≤ᶠ b) := by
  unfold decideRefinesGate
  rw [h, ← decideRefines_iff]
  by_cases hd : decideRefines a b = true <;> simp [hd]

/-- **`gate_deterministic`.** The gate is a deterministic function of the wire — two calls on the same
wire return the same string (so the Rust differential's FFI verdict is reproducible). -/
theorem gate_deterministic (s : String) (o₁ o₂ : String)
    (h₁ : decideRefinesGate s = o₁) (h₂ : decideRefinesGate s = o₂) : o₁ = o₂ := by
  rw [← h₁, ← h₂]

/-! ### §7b — WIRE ROUND-TRIP + NON-VACUITY `#guard`s (the export reproduces §5, on the wire).

The codec round-trips the σ-free `Proc` (`decode ∘ encode = id`), and the EXPORT reproduces the §5
non-vacuity facts THROUGH the wire: the half is admitted (`"1"`), the right-skew is rejected (`"0"`),
reflexivity holds, distinct letters do not refine, and a malformed wire is fail-closed (`"ERR"`).
Kernel-evaluated (`decideRefines` is σ-free + fuel-structural), so these are `#guard`s, not
`native_decide` — a false `#guard` is a build error. -/

-- The σ-free PROJECTIONS of the counterexample (the `R`-write replaced by its `emit 0` shadow — the
-- exact fragment a lowered deploy flow lives in: `done`/`emit`/`ch`/`seqp`, no `wr`). The codec is
-- σ-free, so it round-trips EXACTLY on this fragment; `decideRefines` gives the SAME verdict on these
-- as on `earlyEx`/`lateEx` (same move-graph — that is the point of §3 σ-uniformity), witnessed below.
def earlyProj : Proc := (Pf ⋆ᶠ Flow.fire 0) ⊔ᶠ (Qf ⋆ᶠ Flow.fire 0)
def lateProj  : Proc := (Pf ⊔ᶠ Qf) ⋆ᶠ Flow.fire 0

-- the codec round-trips EXACTLY on the σ-free fragment (Rust-encoder ⟷ Lean-decoder grammar agree).
#guard decodeProc (encodeProc earlyProj) == some earlyProj
#guard decodeProc (encodeProc lateProj) == some lateProj
#guard decodeProc (encodeProc Proc.done) == some Proc.done
#guard decodeProc (encodeProc (Flow.fire 7)) == some (Flow.fire 7)
-- the full INPUT wire round-trips to the pair `(earlyProj, lateProj)`.
#guard decodeRefineWire ("A=" ++ encodeProc earlyProj ++ ";B=" ++ encodeProc lateProj)
        == some (earlyProj, lateProj)
-- the gate agrees on the projection (σ-uniformity): the half still holds through the wire on the proj.
#guard dregg_decide_refines ("A=" ++ encodeProc earlyProj ++ ";B=" ++ encodeProc lateProj) == "1"
#guard dregg_decide_refines ("A=" ++ encodeProc lateProj ++ ";B=" ++ encodeProc earlyProj) == "0"

-- THE HALF, through the export: early ≤ᶠ late ⟹ the gate says "1" (agrees with `decideRefines_half`).
#guard dregg_decide_refines ("A=" ++ encodeProc earlyEx ++ ";B=" ++ encodeProc lateEx) == "1"
-- THE RIGHT-SKEW, through the export: late ⋠ early ⟹ the gate says "0" (agrees with `decideRefines_rightskew`).
#guard dregg_decide_refines ("A=" ++ encodeProc lateEx ++ ";B=" ++ encodeProc earlyEx) == "0"
-- reflexive: a flow refines itself ⟹ "1".
#guard dregg_decide_refines ("A=" ++ encodeProc earlyEx ++ ";B=" ++ encodeProc earlyEx) == "1"
-- distinct single letters: `fire 1 ⋠ fire 2` ⟹ "0".
#guard dregg_decide_refines ("A=" ++ encodeProc (Flow.fire 1) ++ ";B=" ++ encodeProc (Flow.fire 2)) == "0"
-- a strict narrowing: `fire 1 ≤ᶠ (fire 1 ⊔ fire 2)` ⟹ "1" (the choice offers the 1-move).
#guard dregg_decide_refines
        ("A=" ++ encodeProc (Flow.fire 1) ++ ";B=" ++ encodeProc (Flow.fire 1 ⊔ᶠ Flow.fire 2)) == "1"
-- the no-widening direction: `(fire 1 ⊔ fire 2) ⋠ fire 1` ⟹ "0".
#guard dregg_decide_refines
        ("A=" ++ encodeProc (Flow.fire 1 ⊔ᶠ Flow.fire 2) ++ ";B=" ++ encodeProc (Flow.fire 1)) == "0"
-- a malformed wire is FAIL-CLOSED to the ERR sentinel (the deploy gate treats ERR as "do not admit").
#guard dregg_decide_refines "not a wire" == "ERR"
#guard dregg_decide_refines "A=e1;B=e2 e3" == "ERR"   -- leftover token on the B side
#guard dregg_decide_refines "A=c e1;B=e2" == "ERR"     -- `c` missing its second child

/-! ## §8 — Axiom hygiene. -/

#assert_all_clean [
  pstep_decreases,
  step_to_pstep,
  pstep_to_step,
  dupSim_to_simFrom,
  psim_of_step_sim,
  simFrom_to_dupSim,
  dupSim_iff_simFrom,
  dupSim_iff_sim,
  moves_sound,
  moves_complete,
  decideFuel_mono,
  decideFuel_mono_le,
  decideFuel_sound,
  decideFuel_complete,
  decideRefines_dupSim_iff,
  decideRefines_iff,
  decideRefines_half,
  decideRefines_rightskew,
  gate_one_iff_decideRefines,
  gate_one_iff_sim,
  gate_zero_iff_not_sim,
  gate_deterministic
]

end Dregg2.Deos.FlowRefine
