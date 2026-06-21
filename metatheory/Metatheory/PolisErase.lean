/-
# Metatheory.PolisErase — the causally-closed counterfactual A-erasure (gpt5.5's architecture, §3).

The counterfactual heart of relational domination ("B was viable WITHOUT A's public contribution,
but not WITH it"): given a public configuration, remove the dominator A's causal influence and
compare. gpt5.5's polarity correction is load-bearing — you must NOT "remove A's events and
down-close" (that leaves non-A events whose causal past needed a removed A-event — an INVALID
config). The right counterfactual is the **maximal subconfiguration whose events have NO A-event in
their causal past** — causally closed by construction.

Abstract over a public causal order here; instantiated on the deployed blocklace
(`Dregg2.Authority.Blocklace.{Block, precedes}`: `actor := creator`, `le := precedes∪=`). Pure
Lean 4 core (imports the import-free `Metatheory.Polis`); no `sorry`.
-/
import Metatheory.Polis

namespace Metatheory.PolisErase

variable {Event Agent : Type}

/-- A public **causal structure**: each event has a public actor and a causal order `le e f`
("`e` is a cause of `f`", reflexive-transitive). No interior. (Deployed: `actor := Block.creator`,
`le := Blocklace.precedes` reflexively closed.) -/
structure Causal (Event Agent : Type) where
  actor : Event → Agent
  le : Event → Event → Prop
  le_refl : ∀ e, le e e
  le_trans : ∀ {e f g}, le e f → le f g → le e g

variable (Cz : Causal Event Agent)

/-- A **configuration**: a causally down-closed set of public events. -/
structure Config (Cz : Causal Event Agent) where
  mem : Event → Prop
  downClosed : ∀ {e f}, Cz.le e f → mem f → mem e

/-- `e` is **A-independent**: no event by `A` lies in its causal past. -/
def AIndep (A : Agent) (e : Event) : Prop := ∀ d, Cz.le d e → Cz.actor d ≠ A

/-- **`eraseAgent`** — the counterfactual: the maximal subconfiguration whose events are
A-independent (KEEP the events with no A-event in their causal past). Causally closed BY
CONSTRUCTION (an A-independent event's causes are A-independent), so the result is a genuine
`Config`. -/
def eraseAgent (A : Agent) (C : Config Cz) : Config Cz where
  mem e := C.mem e ∧ AIndep Cz A e
  downClosed := fun {e f} hef => fun ⟨hf, hAf⟩ =>
    ⟨C.downClosed hef hf, fun d hde => hAf d (Cz.le_trans hde hef)⟩

/-- The erasure is a SUBconfiguration of the actual. -/
theorem eraseAgent_subset (A : Agent) (C : Config Cz) (e : Event) :
    (eraseAgent Cz A C).mem e → C.mem e := fun h => h.1

/-- The erasure contains NO A-event — A's public contribution is gone. -/
theorem eraseAgent_no_A (A : Agent) (C : Config Cz) (e : Event) :
    (eraseAgent Cz A C).mem e → Cz.actor e ≠ A := fun h => h.2 e (Cz.le_refl e)

/-- … and it is MAXIMAL: every A-independent subconfiguration of `C` sits inside the erasure — so
the counterfactual keeps *all* of `C` that did not depend on `A` (no spurious removal). -/
theorem eraseAgent_maximal (A : Agent) (C D : Config Cz)
    (hsub : ∀ e, D.mem e → C.mem e) (hindep : ∀ e, D.mem e → AIndep Cz A e) (e : Event) :
    D.mem e → (eraseAgent Cz A C).mem e := fun h => ⟨hsub e h, hindep e h⟩

/-- Erasing an agent that never acted in `C` changes nothing — the counterfactual is trivial when
the "dominator" made no public contribution (a sanity / non-spuriousness check). -/
theorem eraseAgent_eq_of_absent (A : Agent) (C : Config Cz)
    (hAbsent : ∀ e, C.mem e → Cz.actor e ≠ A) (e : Event) :
    (eraseAgent Cz A C).mem e ↔ C.mem e :=
  ⟨fun h => h.1, fun h => ⟨h, fun d hde hd => hAbsent d (C.downClosed hde h) hd⟩⟩

/-! ### Non-vacuity: a discriminating causal model (2 events, B causally after A). -/

/-- A tiny causal world: event `0` by agent `0` (= "A"), event `1` by agent `1`, with `0 ≤ 1`
(event 1 causally depends on event 0). -/
def demoCausal : Causal Nat Nat where
  actor e := e            -- event n is by agent n
  le e f := e = f ∨ (e = 0 ∧ f = 1)
  le_refl e := Or.inl rfl
  le_trans := by
    intro e f g hef hfg
    rcases hef with h | ⟨h1, h2⟩ <;> rcases hfg with h' | ⟨h1', h2'⟩
    · exact Or.inl (h.trans h')
    · exact h ▸ Or.inr ⟨h1', h2'⟩
    · exact h' ▸ Or.inr ⟨h1, h2⟩
    · omega

/-- The full config {0,1}. -/
def demoFull : Config demoCausal where
  mem e := e = 0 ∨ e = 1
  downClosed := by
    intro e f hef hf
    rcases hef with h | ⟨h1, _⟩
    · exact h ▸ hf
    · exact Or.inl h1

/-- Erasing agent `0` (= A): event 1, whose causal past contains event 0 (by A), is REMOVED — its
viability/structure was A-dependent. (Event 0 itself is also removed: it is by A.) -/
example : ¬ (eraseAgent demoCausal 0 demoFull).mem 1 := by
  rintro ⟨_, hindep⟩
  exact hindep 0 (Or.inr ⟨rfl, rfl⟩) rfl
/-- … and nothing survives (both events are A-dependent or A-authored): the counterfactual is the
empty config here. -/
example : ¬ (eraseAgent demoCausal 0 demoFull).mem 0 :=
  fun h => eraseAgent_no_A demoCausal 0 demoFull 0 h rfl

end Metatheory.PolisErase
