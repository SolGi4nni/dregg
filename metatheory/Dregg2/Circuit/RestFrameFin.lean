/-
# `Dregg2.Circuit.RestFrameFin` — the FINITE-SUPPORT rest-frame obligation, and the whole-kernel
binding RE-SEATED on it.

⚑ Substrate, said plainly: LEAN-AUTHORED metatheory over `Dregg2.Circuit.StateCommit`'s commitment
surface. `RestHashIffFrame` is a `Prop`-valued hypothesis carried by binding THEOREMS about the AIR
the Lean side emits; nothing here is a Rust AIR, a hand-written `Builder` gadget, or an
`air_accepts` predicate.

## What this file is for

`RestFrameCardinalityFloor.restHashIffFrame_false_by_cardinality` refutes `RestHashIffFrame RH` for
EVERY `RH : RecordKernelState → ℤ` at EVERY width, by Cantor — `bal : CellId → AssetId → ℤ` is a
function space over an infinite index and `ℤ` is countable. Everything that consumed it is therefore
vacuous, `CircuitSoundness.CommitSurface` (which carries it as its fifth FIELD) included.

`Verify.RestFrameFiniteSupportSuccessor` stated the repair — restrict the biconditional to the
`denote`-image of `Circuit.FinKernelState` — and checked it SATISFIABLE / REFUTABLE / NOT PROVABLE.
It could not, however, be the home of the definition: it sits ABOVE `CircuitSoundness` in the import
graph (`FinBindsKernel → Freshness → CrossTurnFreshness → CircuitSoundness`), so nothing on the apex
path could ever depend on it. This module is the same obligation placed BELOW `StateCommit` (it
imports only `Circuit.FinKernelState`), so `StateCommit.recStateCommit_binds_kernel` and the surface
bundle can carry it — which is what re-inhabits the bundle.

`RestHashIffFrameFin` and `FiniteRepresentable` are DEFINED HERE and nowhere else;
`Verify.RestFrameFiniteSupportSuccessor` now `export`s these rather than declaring its own copies
(two shapes that agree today are two shapes that will disagree later).

## Where the successor is CONSUMED

`StateCommit.recStateCommit_binds_kernel` was REWRITTEN IN PLACE (not twinned) to take
`RestHashIffFrameFin RH` plus `FiniteRepresentable` on both states. In place, because a fresh
`_finrep` sibling would be (a) a second shape that drifts, and (b) a NEW `#floor_ratchet` carrier —
the gate hard-errors on any new declaration taking a refuted floor, and it is right to. The
`FiniteRepresentable` side conditions sit exactly where `AccountsWF` already sits: a per-call
structural obligation, never a field of the commitment bundle (a bundle of FUNCTIONS has no business
quantifying over STATES).

⚑ **What that costs, said at current resolution.** The binding no longer holds for an arbitrary
`RecordKernelState`; it holds for states with finite per-cell support.
`not_finiteRepresentable_of_lifecycle_ne_zero` below exhibits an `AccountsWF` state that is NOT
finitely representable, so the restriction is REAL and the theorem is genuinely narrower than the
(vacuous, because `CommitSurface` had no inhabitant) one it replaces. Whether every state the
executor actually reaches is finitely representable is `FinKernelState.denote_surjective_on_reachable`,
which is still gated on the per-effect commuting square `hpres` — undischarged for every effect
today. That gap is NAMED here and not papered over.

No `sorry`, no `axiom`, no `native_decide`.
-/
import Dregg2.Circuit.FinKernelState
import Mathlib.Data.Set.Finite.Basic

namespace Dregg2.Circuit.RestFrameFin

open Dregg2.Exec (CellId Value Turn RecordKernelState)
open Dregg2.Circuit.FinKernelState (FinKernelState denote denote_injective finInit CanonMap SortedMap
  mem_of_lookupList_eq_some)

set_option autoImplicit false

/-! ## §1 — the finite-support domain. -/

/-- **`FiniteRepresentable k`** — `k` is the `denote`-image of some `FinKernelState`: every
per-cell/per-label side-table (`bal`, `caps`, `slotCaveats`, `lifecycle`, `deathCert`, `delegate`,
`delegations`, `delegationEpoch`, `delegationEpochAt`, `heaps`) has FINITE support, sorted-nodup
encoded. This is the touched-row `Finset` view `Verify.InjSpelledFloors` prescribes, stated as
membership in the image of the already-proved data refinement rather than as a fresh invariant. -/
def FiniteRepresentable (k : RecordKernelState) : Prop := ∃ f : FinKernelState, denote f = k

/-- **POSITIVE POLE.** Every `denote` image is finitely representable, by definition. -/
theorem finiteRepresentable_of_denote (f : FinKernelState) : FiniteRepresentable (denote f) :=
  ⟨f, rfl⟩

/-- The unique finite representative of a finitely-representable state (`denote_injective`). -/
theorem finiteRepresentable_unique {k : RecordKernelState} {f f' : FinKernelState}
    (h : denote f = k) (h' : denote f' = k) : f = f' :=
  denote_injective (h.trans h'.symm)

/-! ### ⚑ NEGATIVE POLE — the restriction is REAL: an `AccountsWF` state that is NOT representable.

Without this the whole file could be `FiniteRepresentable = True` in disguise and every theorem below
would be exactly as vacuous as the one it replaces, one level down. `denote f`'s `lifecycle` reads a
`CanonMap CellId Nat 0` — absent keys read the default `0` — so a state stamping EVERY cell with a
non-zero lifecycle would need infinitely many stored keys in a `List`. -/

/-- **⚑ NOT EVERY KERNEL IS FINITELY REPRESENTABLE.** A state whose `lifecycle` is non-zero at every
cell has infinite `lifecycle`-support, and a `FinKernelState` stores its lifecycle rows in a `List`.
So `FiniteRepresentable` is not the constant `True` and the domain restriction below has teeth. -/
theorem not_finiteRepresentable_of_lifecycle_ne_zero (k : RecordKernelState)
    (h : ∀ c, k.lifecycle c ≠ 0) : ¬ FiniteRepresentable k := by
  rintro ⟨f, rfl⟩
  -- every cell must be a STORED key of `f.lifecycle` (an absent key reads the default `0`).
  have hkey : ∀ c : CellId, c ∈ (f.lifecycle.toMap.entries.map Prod.fst) := by
    intro c
    have hc : (denote f).lifecycle c ≠ 0 := h c
    cases hl : Dregg2.Circuit.FinKernelState.lookupList c f.lifecycle.toMap.entries with
    | none =>
        exact absurd (show (denote f).lifecycle c = 0 by
          simp only [denote, CanonMap.get, SortedMap.get, SortedMap.lookup, hl, Option.getD_none]) hc
    | some v =>
        exact List.mem_map.mpr ⟨(c, v), mem_of_lookupList_eq_some hl, rfl⟩
  -- a `List`'s key set is finite; `CellId` is not.
  exact Set.infinite_univ
    (Set.Finite.subset (List.finite_toSet _) (fun c _ => hkey c))

/-! ## §2 — the successor obligation. -/

/-- **`RestHashIffFrameFin RH` — the FINITE-SUPPORT rest-frame obligation.** Token-for-token
`StateCommit.RestHashIffFrame`'s 18-conjunct body (same order, same direction, same
`∀ k k' : RecordKernelState` binder — so a call site changes by ADDING two hypotheses, never by
changing shape), gated on both states being `FiniteRepresentable`.

⚑ Unlike `RestHashIffFrame`, this one HAS INSTANCES — see
`Verify.RestFrameFiniteSupportSuccessor.restHashIffFrameFin_satisfiable`, a CLOSED proof (no carried
hypothesis) at `FinFrameHash.RH_fin Reference.refSponge`, and the NAMED closed surface built on it,
`Verify.ClosureSurfaceApplicable.S_liveRef`. (The older ANONYMOUS `example : CommitSurface` in
`RestFrameFiniteSupportSuccessor` §6 is kept; it was left unnamed because a declaration mentioning
`CommitSurface` was then a `#floor_ratchet` `bundle-user` carrier. It is not one since the bundle's
four injectivity fields were deleted 2026-08-01, which is why `S_liveRef` may be named.)

⚠ **AND "HAS INSTANCES" MEANS AT THE UNBOUNDED REFERENCE SPONGE, NOT AT DEPLOYED WIDTH.**
`restHashIffFrameFin_false_babyBear` (2026-08-02) refutes this predicate for EVERY rest-hash whose
values lie in the BabyBear window, by the same pigeonhole that killed the four injectivity fields: the
`denote`-image is infinite and a bounded `RH` is not. So `CommitSurface` still has no deployed
inhabitant, and NO GATE SAYS SO — this body is `Iff`-headed, so `#floor_ratchet`'s shape-derived
floor set (`FloorCensus.injShape`/`injShapeAnd`) can never contain it. ~120 binder sites, ZERO
baseline rows. -/
def RestHashIffFrameFin (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, FiniteRepresentable k → FiniteRepresentable k' →
    (RH k = RH k' ↔
      (k'.accounts = k.accounts ∧ k'.caps = k.caps ∧ k'.bal = k.bal
        ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked ∧ k'.commitments = k.commitments
        ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
        ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
        ∧ k'.delegationEpoch = k.delegationEpoch ∧ k'.delegationEpochAt = k.delegationEpochAt
        ∧ k'.heaps = k.heaps ∧ k'.nullifierRoot = k.nullifierRoot ∧ k'.revokedRoot = k.revokedRoot
        ∧ k'.commitmentsRoot = k.commitmentsRoot))

#assert_axioms not_finiteRepresentable_of_lifecycle_ne_zero
#assert_axioms finiteRepresentable_of_denote
#assert_axioms finiteRepresentable_unique

end Dregg2.Circuit.RestFrameFin
