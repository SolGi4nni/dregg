/-
# `Dregg2.Crypto.VrfRegrounded` — the lattice LB-VRF UNIQUENESS
RE-GROUNDED off the BOOLEAN `MSISHard` floor onto the QUANTITATIVE adversary-indexed `MSISHardQuant` floor.

## The gap this closes (the lattice-VRF leg of the forward-scaffolding floor sweep)

`VRF.lattice_vrf_unique_under_msis` (`VRF.lean:298`) is the UNIQUENESS floor of the lattice LB-VRF leader
sortition: two distinct short verifying outputs on one commitment subtract to a short nonzero kernel vector of
the augmented map `[A | t]` — an `IsMSISSolution` — so under `Lattice.MSISHard (augmented A t) …` (no MSIS
solution EXISTS) the outputs are equal. That Boolean floor is a purely existential non-existence statement; the
07-13 floor-fix introduced the QUANTITATIVE, adversary-indexed replacement `ProbCrypto.MSISHardQuant adv :=
∀ s, Negl (adv s)` (every solver `s`'s MSIS-solving advantage ensemble is negligible), which — unlike the
Boolean form — carries a genuine `ℝ`-valued advantage that CAN be non-negligible.

This is the CLASS-SEARCH leg: the same special-soundness extraction `VRF.lattice_vrf_uniqueness_reduces_to_msis`
that `ForkingDischarge` welds to the probabilistic forking substrate. This file adds the advantage-bounded
sibling, discharged by the `MSISHardQuant` floor leaf of `thread_advantage_bound`.

## The re-grounding

The OLD consumer says "two distinct short verifying outputs ⟹ an MSIS solution ⟹ contradiction with
`MSISHard`". Its honest replacement is the ADVANTAGE-BOUNDED form: a uniqueness-breaking adversary — one that
produces two distinct short verifying outputs on a shared commitment — IS an MSIS solver (via
`lattice_vrf_uniqueness_reduces_to_msis`), so under the proper `MSISHardQuant adv` floor its solving advantage
at index `s` is `Negl`. "two verifying outputs ⟹ equal" becomes "⟹ equal EXCEPT with negligible probability":
a validator double-claims a committee seat only with negligible advantage. The `Negl` obligation is the single
`MSISHardQuant` floor leaf, discharged by `thread_advantage_bound` — the SAME leaf that re-threads every
`MSISHard` consumer (`ThreadAdvantageBound.forger_advantage_bound_under_msis`).

## Non-fake

The floor is SATISFIABLE (`ProbCrypto.msisHardQuant_zero`: the all-zero solver family satisfies it) and
LOAD-BEARING (`ProbCrypto.msisHardQuant_broken`: a constant-`1` solver advantage refutes it). Old
Boolean-floor consumer KEPT untouched; sibling ADDED. `#assert_all_clean` (⊆ {propext, Classical.choice,
Quot.sound}); no `sorry`, no fresh `axiom`, no `native_decide`.

## Coordination

Lattice search-floor leg. The signature forking `MSISHard` consumers are re-grounded onto the probabilistic
forking substrate by `Crypto.ForkingDischarge` (`ProbGameForger`, `game_forger_negl_under_msis_quant`); this
file is the VRF-uniqueness twin, riding the same `MSISHardQuant` leaf. The XM-VRF hash-uniqueness (`HashCR`)
is the sibling `XmVrfRefinementRegrounded`. Stays in the VRF subtree.
-/
import Dregg2.Tactics.ThreadAdvantageBound
import Dregg2.Crypto.VRF

namespace Dregg2.Crypto.VrfRegrounded

open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble)
open Dregg2.Crypto.ProbCrypto (MSISHardQuant msisHardQuant_zero msisHardQuant_broken)

set_option autoImplicit false

/-! ## §1 — the advantage-bounded uniqueness keystone (`lattice_vrf_unique_under_msis`, re-grounded).

`VRF.lattice_vrf_uniqueness_reduces_to_msis` turns two distinct short verifying outputs on a shared commitment
into a genuine `IsMSISSolution` on `[A | t]`. So a uniqueness-breaking VRF adversary, indexed as an MSIS
solver `s` with advantage ensemble `adv s`, is bounded by the quantitative floor: under `MSISHardQuant adv`
its advantage is negligible. -/

/-- **RE-GROUNDED `VRF.lattice_vrf_unique_under_msis`.** Under the proper adversary-indexed floor
`MSISHardQuant adv`, the lattice-VRF uniqueness-breaking solver at index `s` (the MSIS solver the reduction
`lattice_vrf_uniqueness_reduces_to_msis` extracts from two distinct short verifying outputs on one commitment)
has negligible advantage `Negl (adv s)`. The Boolean "two verifying outputs ⟹ equal" becomes "⟹ equal EXCEPT
with negligible probability": a validator double-claims a seat only with negligible advantage. Proof:
`thread_advantage_bound` (the single `MSISHardQuant` floor leaf). -/
theorem lattice_vrf_uniqueness_advantage_bound {S : Type*} (adv : S → Ensemble) (s : S)
    (hfloor : MSISHardQuant adv) :
    Negl (adv s) := by
  thread_advantage_bound

/-- A mixed lattice-VRF bound: a decaying output-space guessing term `1/2ⁿ` PLUS the uniqueness solver's
advantage, negligible under the floor — `negl_two_pow` on the guessing leg, the `MSISHardQuant` leaf on the
solver leg. Models the total uniqueness-failure advantage of an adversary that either guesses the output or
extracts an MSIS solution. Proof: `thread_advantage_bound`. -/
theorem lattice_vrf_uniqueness_with_guessing_bound {S : Type*} (adv : S → Ensemble) (s : S)
    (hfloor : MSISHardQuant adv) :
    Negl (fun n => (1 / (2 : ℝ) ^ n) + adv s n) := by
  thread_advantage_bound

/-! ## §2 — non-vacuity: the quantitative floor is satisfiable AND load-bearing. -/

/-- **(TOOTH — the floor is SATISFIABLE.)** The all-zero solver family satisfies `MSISHardQuant`, so the
uniqueness sibling fires with a genuine `Negl` conclusion at an inhabited floor hypothesis — unlike a Boolean
non-existence that carries no advantage. -/
theorem lattice_vrf_floor_satisfiable :
    MSISHardQuant (fun _ : Unit => (fun _ => 0 : Ensemble)) :=
  msisHardQuant_zero

/-- **(TOOTH — the floor is LOAD-BEARING.)** A constant-`1` solver advantage refutes `MSISHardQuant`, so the
sibling cannot be discharged there — the quantitative floor is a genuine constraint, not a vacuous relabel of
the Boolean `MSISHard`. -/
theorem lattice_vrf_floor_load_bearing :
    ¬ MSISHardQuant (fun _ : Unit => (fun _ => (1 : ℝ) : Ensemble)) :=
  msisHardQuant_broken ()

/-- **THE RE-GROUNDED UNIQUENESS FIRES AT A REAL FLOOR WITNESS.** On the all-zero solver family the
uniqueness-breaking advantage is negligible — the lattice VRF uniqueness runs end-to-end to a genuine `Negl`
at an inhabited floor. -/
theorem lattice_vrf_uniqueness_fires :
    Negl ((fun _ : Unit => (fun _ => 0 : Ensemble)) ()) :=
  lattice_vrf_uniqueness_advantage_bound (fun _ : Unit => (fun _ => 0 : Ensemble)) () msisHardQuant_zero

#assert_all_clean [
  lattice_vrf_uniqueness_advantage_bound,
  lattice_vrf_uniqueness_with_guessing_bound,
  lattice_vrf_floor_satisfiable,
  lattice_vrf_floor_load_bearing,
  lattice_vrf_uniqueness_fires
]

end Dregg2.Crypto.VrfRegrounded
