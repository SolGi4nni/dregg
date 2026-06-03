/-
# Dregg2.Boundary — coinductive soundness: the ▶-guarded bisimulation module.

A cell is live codata — an element of the final coalgebra `νF`, `F X = Obs × (AdmissibleTurn ⇒ X)`.
Soundness is a statement over unbounded time, not induction over a finite turn list.

The guard `▶` buys productivity, not soundness by itself; soundness requires each step
to be contractive in `StepInv = Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance`.
The well-posed keystone (`stepComplete_preserves`) states this as a safety invariant
preserved along the whole execution, proved via `Execution.invariant_run`.

`Sound`/`IsBisim` capture behavioural equivalence between coalgebras; their genuine
basic fact is reflexivity (`sound_refl`). The earlier step-completeness ⇔ bisimilarity
claim was false as stated (refuted by `Spec.Carrier = Empty`) and is removed.

§8 caveat: crypto-soundness of `Verify P w` (binding/extractability) is a circuit
obligation and is NEVER merged into this Lean law; `Verify` is a decidable oracle here.
-/
import Dregg2.Core
import Dregg2.Laws
import Dregg2.Authority.Positional
import Dregg2.Execution

namespace Dregg2.Boundary

open Dregg2.Laws Dregg2.Authority

universe u

/-! ## The functor `F X = Obs × (AdmissibleTurn ⇒ X)` and its final coalgebra -/

/- The externally-visible, attested projection of a cell (its committed head, public
`FieldVisibility` fields, lifecycle phase, facet). `Obs` is what crosses a vat
boundary — the "badge". Kept abstract; instantiated by the real PI surface. -/
variable {Obs : Type u}

/- The *dependent* input alphabet: not every turn is admissible from every state.
Admissibility is exactly step-completeness (carries a `StepProof` discharging the full
`StepInv`); modelled abstractly here. -/
variable {AdmissibleTurn : Type u}

/- The abstract cell-object state (the l4v `ko`/`ko'`), as in `Authority.Positional`.
The integrity relation in `BoundaryRespecting` is stated over `KO`; cells decode to it
via `decode`. -/
variable {KO : Type u}

/-- The behaviour functor `F X = Obs × (AdmissibleTurn → X)` (a Moore/DFA coalgebra:
output-on-state, transition-on-input). The partial, witness-guarded transition `⇒` is
where the verifier (the TCB) lives. -/
abbrev F (Obs AdmissibleTurn : Type u) (X : Type u) : Type u :=
  Obs × (AdmissibleTurn → X)

/-- **`TurnCoalg` — a coalgebra structure map `c : X → F X`** for the cell behaviour
functor. An element of the carrier `X` is a (point of a) live cell; `c` unfolds it
into its current observation together with its admissible-turn-indexed successors.
The final coalgebra `νF` is the type of cells; we work with an arbitrary coalgebra and
its anamorphism into behaviours. -/
structure TurnCoalg (Obs AdmissibleTurn : Type u) where
  /-- The carrier (the state space of cells). -/
  Carrier : Type u
  /-- The structure map `c : X → Obs × (AdmissibleTurn → X)`. -/
  step    : Carrier → F Obs AdmissibleTurn Carrier

/-- The observation emitted at a cell (the `Obs` component of `step`). -/
def TurnCoalg.obs (T : TurnCoalg Obs AdmissibleTurn) (x : T.Carrier) : Obs :=
  (T.step x).1

/-- The successor cell reached by an admissible turn (the transition component). The
codomain is *again* the carrier — codata: a cell transitions to another live cell,
never to a "final state". -/
def TurnCoalg.next (T : TurnCoalg Obs AdmissibleTurn)
    (x : T.Carrier) (t : AdmissibleTurn) : T.Carrier :=
  (T.step x).2 t

/-! ## `▶` ("later") — the guard, typed off `previous_receipt_hash`

We model the guard abstractly: a successor is "guarded" when it is reached through a
real admissible turn whose `previous_receipt_hash` links it to the current head. In a
guarded-type-theory backend (e.g. `Clocked`/`▷`), `Later` would be the `▷` modality;
here it is a `Prop`-level placeholder so the bisimulation can refer to "the tail,
available later". -/

/-- `Later P` — `P` holds "one ▶-step from now". The chain-link receipt hash is the
guard: the head observation is available now; the tail (the rest of the unfold) is
available later. Productivity ⇒ the corecursive `Sound`/`IsBisim` definitions below
are uniquely solved. -/
def Later (Q : Prop) : Prop := Q

/-! ## Soundness as a ▶-guarded bisimulation to the golden-oracle Spec -/

/- The Lean golden-oracle specification coalgebra. Kept abstract: its observations and
admissible turns are the spec's, and `Sound`/`IsBisim` relate an implementation coalgebra
to it. -/
variable (Spec : TurnCoalg Obs AdmissibleTurn)

/-- **`IsBisim` — a ▶-guarded bisimulation relation** between an implementation
coalgebra `Impl` and the spec `Spec`. `R` is a bisimulation iff related states emit
equal observations *now* and, for every admissible turn, their successors are related
*later* (`▶`). Coinductive in spirit (the `Later` guards the recursive occurrence);
stated as the closure property a witness relation must satisfy. -/
structure IsBisim
    (Impl Spec : TurnCoalg Obs AdmissibleTurn)
    (R : Impl.Carrier → Spec.Carrier → Prop) : Prop where
  /-- Related states agree on the observation emitted now. -/
  obs_eq   : ∀ x y, R x y → Impl.obs x = Spec.obs y
  /-- For every admissible turn, the successors are related later (the `▶` guard). -/
  step_rel : ∀ x y, R x y → ∀ t : AdmissibleTurn,
                Later (R (Impl.next x t) (Spec.next y t))

/-- **`Sound` — a cell (state of `Impl`) is sound** iff it is bisimilar to some
spec-state: there exists a ▶-guarded bisimulation relating them. This is the
coinductive soundness predicate; "forever correct" collapses to "one guarded step,
forever" via the bisimulation. -/
def Sound (Impl Spec : TurnCoalg Obs AdmissibleTurn) (x : Impl.Carrier) : Prop :=
  ∃ (R : Impl.Carrier → Spec.Carrier → Prop) (y : Spec.Carrier),
    IsBisim Impl Spec R ∧ R x y

/-! ## Step-completeness ⇒ soundness (the keystone) -/

/-- **`StepInv`** — the per-step invariant the turn proof must attest, abstractly the
conjunction `Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance`. A turn is
*admissible* exactly when it carries a `StepProof` discharging this. Modelled as a
predicate over a transition `(x, t, x')` of the implementation coalgebra. -/
def StepInv (Impl : TurnCoalg Obs AdmissibleTurn)
    (conservation authority chainLink obsAdvance :
      Impl.Carrier → AdmissibleTurn → Impl.Carrier → Prop)
    (x : Impl.Carrier) (t : AdmissibleTurn) (x' : Impl.Carrier) : Prop :=
  conservation x t x' ∧ authority x t x' ∧ chainLink x t x' ∧ obsAdvance x t x'

/-- **`StepComplete`** — every reachable transition of `Impl` attests the *full*
`StepInv`. This is *contractivity in `StepInv`*: a step that locally type-checks but
omits a conjunct (e.g. leaks `Σ_k`) is exactly a non-contractive step, the
"drifting-future" failure mode. -/
def StepComplete (Impl : TurnCoalg Obs AdmissibleTurn)
    (conservation authority chainLink obsAdvance :
      Impl.Carrier → AdmissibleTurn → Impl.Carrier → Prop) : Prop :=
  ∀ (x : Impl.Carrier) (t : AdmissibleTurn),
    StepInv Impl conservation authority chainLink obsAdvance x t (Impl.next x t)

/-! ### Step-completeness ⇒ whole-execution safety (the well-posed keystone)

A state-predicate `Good` preserved by every `StepInv`-respecting transition holds along
the entire execution. Proved via `Execution.invariant_run`. -/

/-- The transition system a cell-coalgebra induces: `Step x x'` iff some admissible turn
sends `x` to `x'`. A cell's life is a `Run` of this system. -/
def inducedSystem (Impl : TurnCoalg Obs AdmissibleTurn) : Execution.System where
  Config := Impl.Carrier
  Step x x' := ∃ t : AdmissibleTurn, x' = Impl.next x t

/-- **`stepComplete_preserves` — the well-posed, PROVED keystone.** If `Impl` is
step-complete and a state-predicate `Good` is preserved by every `StepInv`-respecting
transition, then `Good` holds at every reachable configuration of the whole execution
(`Execution.invariant_run`). This is the honest content of "step-completeness buys
soundness": no drifting future, stated as a safety invariant rather than the ill-posed
bisimulation-to-an-arbitrary-`Spec`. -/
theorem stepComplete_preserves (Impl : TurnCoalg Obs AdmissibleTurn)
    (conservation authority chainLink obsAdvance :
      Impl.Carrier → AdmissibleTurn → Impl.Carrier → Prop)
    (Good : Impl.Carrier → Prop)
    (hsc : StepComplete Impl conservation authority chainLink obsAdvance)
    (hpres : ∀ x t, Good x →
        StepInv Impl conservation authority chainLink obsAdvance x t (Impl.next x t) →
        Good (Impl.next x t))
    {x y : Impl.Carrier}
    (hrun : Execution.Run (inducedSystem Impl) x y) (hx : Good x) : Good y := by
  refine Execution.invariant_run (S := inducedSystem Impl) (I := Good) ?_ hrun hx
  intro s t hs hstep
  obtain ⟨τ, rfl⟩ := hstep
  exact hpres s τ hs (hsc s τ)

/-! ### `Sound`/`IsBisim` — behavioural equivalence, not the soundness keystone.

`Sound`/`IsBisim` capture behavioural equivalence between coalgebras. The
step-completeness ⇒ soundness content lives in `stepComplete_preserves`. -/

/-- **Equality is a bisimulation (reflexivity) — PROVED.** -/
theorem bisim_eq (Impl : TurnCoalg Obs AdmissibleTurn) :
    IsBisim Impl Impl (fun a b => a = b) where
  obs_eq := fun x y h => by subst h; rfl
  step_rel := fun x y h t => by subst h; rfl

/-- Every cell is `Sound` relative to itself — `Sound` is reflexive as a behavioural
equivalence relation. The soundness-from-step-completeness result is
`stepComplete_preserves`. -/
theorem sound_refl (Impl : TurnCoalg Obs AdmissibleTurn) (x : Impl.Carrier) :
    Sound Impl Impl x :=
  ⟨(fun a b => a = b), x, bisim_eq Impl, rfl⟩


/-! ## `BoundaryRespecting` — the coinductive vat-boundary law

Lift of `Authority.Integrity` to the coinductive setting: a cell respects the boundary
when, forever, every admissible turn is intra-vat (trivial witness) or cross-vat
(discharged witness), and the successor again respects the boundary (`▶`-guarded). -/

/-- **`BoundaryRespecting`** — coinductive `BoundaryRespecting` predicate over cells.
Stated as the closure property an invariant set `S` must satisfy to be a
boundary-respecting invariant: every member emits an admissible-by-`Integrity`
transition whose successor is later again in `S`. (`Verifiable P W` supplies the
decidable cross-vat check; `owner`/`subjects`/`p` come from the integrity relation.) -/
structure BoundaryRespecting
    {P W : Type u} [Verifiable P W]
    (Impl : TurnCoalg Obs AdmissibleTurn)
    (owner : Label) (subjects : List Label)
    (decode : Impl.Carrier → KO) (p : KO → KO → P)
    (S : Impl.Carrier → Prop) : Prop where
  /-- Each turn from an `S`-state lands in the integrity relation (intra trivial /
  cross discharged). -/
  admissible : ∀ x, S x → ∀ t : AdmissibleTurn,
      Integrity (P := P) (W := W) owner subjects p (decode x) (decode (Impl.next x t))
  /-- ...and the successor is later again boundary-respecting (the `▶` guard). -/
  closed     : ∀ x, S x → ∀ t : AdmissibleTurn, Later (S (Impl.next x t))

/-- **A boundary-respecting cell is sound w.r.t. the boundary law** (corollary linking
this module to `Authority.boundary_law`): if `S` is boundary-respecting and `x ∈ S`,
then every reachable transition respects `Integrity`. Stated `sorry`. -/
theorem boundary_respecting_sound
    {P W : Type u} [Verifiable P W]
    (Impl : TurnCoalg Obs AdmissibleTurn)
    (owner : Label) (subjects : List Label)
    (decode : Impl.Carrier → KO) (p : KO → KO → P)
    (S : Impl.Carrier → Prop)
    (hbr : BoundaryRespecting (P := P) (W := W) Impl owner subjects decode p S)
    (x : Impl.Carrier) (hx : S x) (t : AdmissibleTurn) :
    Integrity (P := P) (W := W) owner subjects p (decode x) (decode (Impl.next x t)) := by
  exact hbr.admissible x hx t

end Dregg2.Boundary
