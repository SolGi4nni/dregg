/-
# Dregg2.Verify.InjSpelledFloors — the WHOLE-FUNCTION DIGEST floors, REFUTED.

## What this file refutes, and why it is worse than the named floors

`Circuit/EffectCommit2.funcComponent` commits a whole state COMPONENT with one field element:

```
def funcComponent {St Args β : Type}
    (read : RecordKernelState → β) (D : β → ℤ) (hD : Function.Injective D) …
```

and its ~600 call sites instantiate `β` at a FUNCTION SPACE — `CellId → AssetId → ℤ` (the whole
per-asset ledger), `Caps = Label → List Cap` (the whole capability table), `CellId → Value`,
`CellId → Option CellId`, `BornEmptySideTables` (seven such fields at once). Its doc-comment calls
the hypothesis "realizable — a Poseidon Merkle over the field's canonical serialization, the same
CR bar as `cellLeafInjective`".

It is NOT the same bar. `cellLeafInjective`/`Poseidon2SpongeCR` are refuted at DEPLOYED BabyBear
parameters: the domain (`List ℤ`) is countable, injections into `ℤ` exist in the abstract, and the
refutation needs the deployed range bound `0 ≤ h x < p` (`HashFloorHonesty`, `§1`). The
whole-function digests are refuted with NO deployed hypothesis at all: `CellId → AssetId → ℤ` is
UNCOUNTABLE (`2^ℵ₀` — one real number per ledger) and `ℤ` is countable, so **no injection exists,
at any parameters, for any hash, in any field**. `Function.Injective D` at these types is not an
optimistic assumption about Poseidon2; it is a cardinality impossibility.

Every declaration binding one is therefore VACUOUS, and it was invisible to `#floor_ratchet`
because it is spelled INLINE (`Function.Injective D`) rather than as a named floor constant. This
file makes the refutations exist in-tree, which is what ARMS the gate: `Verify/InjSpelling`
derives its gated signature set from `¬ Function.Injective`-concluding theorems whose function is
universally quantified and unconstrained — exactly the shape below.

## The counting core

`§1` is three lemmas and no cryptography:

  * `uncountable_set_of_infinite` — `Set I` is uncountable for infinite `I` (Cantor: a countable
    `Set I` would inject into `ℕ`, hence into `I`).
  * `uncountable_pi_of_infinite` — a function space with an infinite index and two distinct values
    is uncountable (subset indicators are distinct elements).
  * `not_injective_of_uncountable_domain` — Mathlib's `not_injective_uncountable_countable`, named
    here so the specializations read as one argument.

`§2` specializes to each signature the tree actually binds. Each is one line, and each is a REAL
theorem about the deployed system: the digest that circuit soundness rests on cannot exist.

## What this does NOT claim

Nothing here says the deployed system is broken — it says a HYPOTHESIS the proofs take is false,
so the proofs conditioned on it say nothing. The honest replacement is the one `HashFloorHonesty`
§2/§3 already builds: a keyed family with a negligible collision-finding advantage, and binding
restated as an advantage bound. Additionally, for a whole-function component the fix is
STRUCTURAL, not cryptographic — commit the FINITE support (the `accounts : Finset CellId` rows
actually touched), never the whole function; a digest of a finite restriction has a countable
domain and is back at the ordinary (deployed-parameter) CR bar.
-/
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Set.Countable
import Dregg2.Circuit.BornEmptyCommit
import Dregg2.Tactics

set_option autoImplicit false

namespace Dregg2.Verify.InjSpelledFloors

open Dregg2.Authority (Cap Caps Label)
open Dregg2.Exec (CellId AssetId Value SlotCaveat RecordKernelState)
open Dregg2.Circuit.BornEmptyCommit
  (SpawnCreateLeg BornEmptyCellMeta BornEmptySideTables BornEmptyAuthorityTables)

/-! ## §1 — the counting core. Pure cardinality; no hash, no parameters. -/

/-- `Set I` is UNCOUNTABLE whenever `I` is infinite. If it were countable it would inject into `ℕ`,
and `ℕ` injects into an infinite `I`, giving an injection `Set I → I` — Cantor's diagonal forbids
exactly that. -/
theorem uncountable_set_of_infinite (I : Type) [Infinite I] : Uncountable (Set I) := by
  rw [← not_countable_iff]
  intro hc
  haveI := hc
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat (Set I)
  exact Function.cantor_injective (fun s => Infinite.natEmbedding I (g s))
    (fun a b h => hg ((Infinite.natEmbedding I).injective h))

/-- A FUNCTION SPACE with an INFINITE index and at least two distinct values is UNCOUNTABLE: the
indicator `fun i => if i ∈ s then v else w` is a distinct element of `I → V` for every `s : Set I`.
This is the fact that separates a whole-function digest from an ordinary hash — the domain is not
merely infinite, it is bigger than any digest space can ever be. -/
theorem uncountable_pi_of_infinite {I V : Type} [Infinite I] {v w : V} (hvw : v ≠ w) :
    Uncountable (I → V) := by
  classical
  haveI := uncountable_set_of_infinite I
  refine Function.Injective.uncountable (f := fun (s : Set I) (i : I) => if i ∈ s then v else w) ?_
  intro s t hst
  ext i
  have hi := congrFun hst i
  by_cases hs : i ∈ s
  · by_cases ht : i ∈ t
    · simp [hs, ht]
    · simp [hs, ht] at hi; exact absurd hi hvw
  · by_cases ht : i ∈ t
    · simp [hs, ht] at hi; exact absurd hi.symm hvw
    · simp [hs, ht]

/-- **THE TOOTH.** No function from an UNCOUNTABLE domain into a COUNTABLE codomain is injective —
an injection would make the domain countable. Unlike the range-bound teeth of `HashFloorHonesty`,
this needs no hypothesis about the hash at all. -/
theorem not_injective_of_uncountable_domain {A B : Type} [Uncountable A] [Countable B]
    (f : A → B) : ¬ Function.Injective f :=
  not_injective_uncountable_countable f

/-! ## §2 — the deployed signatures.

Each `Uncountable` instance below is a one-line specialization of `uncountable_pi_of_infinite`, and
each refutation is `not_injective_of_uncountable_domain`. `CellId = AssetId = Label = ℕ` is
infinite; every value type carried by a state component has two distinct inhabitants.

⚑ These are stated as `∀ D, ¬ Function.Injective D` with the function UNIVERSALLY QUANTIFIED and
UNCONSTRAINED — no side hypothesis touches `D`. That shape is what `Verify/InjSpelling` reads as
"no function of this signature is injective", so the gate covers the inline spelling of exactly
these signatures and nothing else. -/

/-- The per-asset ledger `bal : CellId → AssetId → ℤ` — uncountably many ledgers. -/
instance uncountable_bal : Uncountable (CellId → AssetId → ℤ) :=
  uncountable_pi_of_infinite (I := CellId) (V := AssetId → ℤ)
    (v := fun _ => (0 : ℤ)) (w := fun _ => (1 : ℤ))
    (by intro h; have := congrFun h 0; simp at this)

/-- The capability table `Caps = Label → List Cap`. -/
instance uncountable_caps : Uncountable Caps :=
  uncountable_pi_of_infinite (I := Label) (V := List Cap)
    (v := []) (w := [Cap.null]) (by simp)

/-- Any `CellId`-indexed ℕ table (`lifecycle`, `deathCert`, `epoch`, …). -/
instance uncountable_cellNat : Uncountable (CellId → Nat) :=
  uncountable_pi_of_infinite (I := CellId) (V := Nat) (v := 0) (w := 1) (by simp)

/-- The per-cell record table `cell : CellId → Value`. -/
instance uncountable_cellValue : Uncountable (CellId → Value) :=
  uncountable_pi_of_infinite (I := CellId) (V := Value)
    (v := Value.int 0) (w := Value.int 1) (by simp)

/-- The delegation table `delegate : CellId → Option CellId`. -/
instance uncountable_cellOptCell : Uncountable (CellId → Option CellId) :=
  uncountable_pi_of_infinite (I := CellId) (V := Option CellId)
    (v := none) (w := some 0) (by simp)

/-- The per-cell cap lists (`delegations`). -/
instance uncountable_cellCapList : Uncountable (CellId → List Cap) :=
  uncountable_pi_of_infinite (I := CellId) (V := List Cap)
    (v := []) (w := [Cap.null]) (by simp)

/-- The per-cell slot-caveat table. -/
instance uncountable_cellSlotCaveats : Uncountable (CellId → List SlotCaveat) :=
  uncountable_pi_of_infinite (I := CellId) (V := List SlotCaveat)
    (v := []) (w := [SlotCaveat.immutable ""]) (by simp)

/-- The per-cell felt heaps (`FeltHeap = List (ℤ × ℤ)`). -/
instance uncountable_cellHeaps : Uncountable (CellId → Dregg2.Substrate.Heap.FeltHeap) :=
  uncountable_pi_of_infinite (I := CellId) (V := Dregg2.Substrate.Heap.FeltHeap)
    (v := []) (w := [(0, 0)]) (by simp)

/-- `SpawnCreateLeg` carries the whole ledger as a field, so it is uncountable too. -/
instance uncountable_spawnCreateLeg : Uncountable SpawnCreateLeg :=
  Function.Injective.uncountable
    (f := fun b : CellId → AssetId → ℤ =>
      ({ bal := b
       , cellMeta := ⟨fun _ => default, fun _ => [], fun _ => 0, fun _ => 0⟩ } : SpawnCreateLeg))
    (fun _ _ h => congrArg SpawnCreateLeg.bal h)

/-- `BornEmptySideTables` carries seven function-space fields. -/
instance uncountable_bornEmptySide : Uncountable BornEmptySideTables :=
  Function.Injective.uncountable
    (f := fun c : Caps =>
      ({ cell := fun _ => default, caps := c, delegate := fun _ => none
       , delegations := fun _ => [], slotCaveats := fun _ => []
       , lifecycle := fun _ => 0, deathCert := fun _ => 0 } : BornEmptySideTables))
    (fun _ _ h => congrArg BornEmptySideTables.caps h)

/-- `BornEmptyAuthorityTables` likewise. -/
instance uncountable_bornEmptyAuthority : Uncountable BornEmptyAuthorityTables :=
  Function.Injective.uncountable
    (f := fun c : Caps =>
      ({ caps := c, lifecycle := fun _ => 0, deathCert := fun _ => 0
       , delegate := fun _ => none, delegations := fun _ => [] } : BornEmptyAuthorityTables))
    (fun _ _ h => congrArg BornEmptyAuthorityTables.caps h)

/-- The whole record-kernel state (its `bal`/`caps`/`cell` fields are function spaces). -/
instance uncountable_recordKernelState : Uncountable RecordKernelState :=
  Function.Injective.uncountable
    (f := fun b : CellId → AssetId → ℤ =>
      ({ accounts := ∅, cell := fun _ => default, caps := fun _ => [], bal := b } :
        RecordKernelState))
    (fun _ _ h => congrArg RecordKernelState.bal h)

/-! ### The refutations.

One per signature the tree binds inline. Each says: **no** function of this type is injective. -/

/-- The `bal` whole-ledger digest CANNOT be injective. -/
theorem balDigest_not_injective (D : (CellId → AssetId → ℤ) → ℤ) : ¬ Function.Injective D :=
  not_injective_of_uncountable_domain D

/-- The capability-table digest CANNOT be injective. -/
theorem capsDigest_not_injective (D : Caps → ℤ) : ¬ Function.Injective D :=
  not_injective_of_uncountable_domain D

/-- Any `CellId → Nat` table digest (lifecycle / deathCert / epoch) CANNOT be injective. -/
theorem cellNatDigest_not_injective (D : (CellId → Nat) → ℤ) : ¬ Function.Injective D :=
  not_injective_of_uncountable_domain D

/-- The per-cell record digest CANNOT be injective. -/
theorem cellValueDigest_not_injective (D : (CellId → Value) → ℤ) : ¬ Function.Injective D :=
  not_injective_of_uncountable_domain D

/-- The delegation-table digest CANNOT be injective. -/
theorem cellOptCellDigest_not_injective (D : (CellId → Option CellId) → ℤ) :
    ¬ Function.Injective D :=
  not_injective_of_uncountable_domain D

/-- The per-cell cap-list digest CANNOT be injective. -/
theorem cellCapListDigest_not_injective (D : (CellId → List Cap) → ℤ) : ¬ Function.Injective D :=
  not_injective_of_uncountable_domain D

/-- The slot-caveat-table digest CANNOT be injective. -/
theorem cellSlotCaveatDigest_not_injective (D : (CellId → List SlotCaveat) → ℤ) :
    ¬ Function.Injective D :=
  not_injective_of_uncountable_domain D

/-- The felt-heap-table digest CANNOT be injective. -/
theorem cellHeapDigest_not_injective (D : (CellId → Dregg2.Substrate.Heap.FeltHeap) → ℤ) :
    ¬ Function.Injective D :=
  not_injective_of_uncountable_domain D

/-- The `(caps, lifecycle)` PAIR digest CANNOT be injective (a product with an uncountable
factor is uncountable). -/
theorem capsNatPairDigest_not_injective (D : ((CellId → List Cap) × (CellId → Nat)) → ℤ) :
    ¬ Function.Injective D :=
  not_injective_of_uncountable_domain D

/-- The `(lifecycle, caps, deathCert)` TRIPLE digest CANNOT be injective. -/
theorem natCapsNatTripleDigest_not_injective
    (D : ((CellId → Nat) × (CellId → List Cap) × (CellId → Nat)) → ℤ) :
    ¬ Function.Injective D :=
  not_injective_of_uncountable_domain D

/-- The `SpawnCreateLeg` leg digest CANNOT be injective. -/
theorem spawnCreateLegDigest_not_injective (D : SpawnCreateLeg → ℤ) : ¬ Function.Injective D :=
  not_injective_of_uncountable_domain D

/-- The born-empty SIDE-TABLE digest CANNOT be injective. -/
theorem bornEmptySideDigest_not_injective (D : BornEmptySideTables → ℤ) :
    ¬ Function.Injective D :=
  not_injective_of_uncountable_domain D

/-- The born-empty AUTHORITY-TABLE digest CANNOT be injective. -/
theorem bornEmptyAuthorityDigest_not_injective (D : BornEmptyAuthorityTables → ℤ) :
    ¬ Function.Injective D :=
  not_injective_of_uncountable_domain D

/-- The whole-record-kernel-state digest CANNOT be injective. -/
theorem recordKernelStateDigest_not_injective (D : RecordKernelState → Int) :
    ¬ Function.Injective D :=
  not_injective_of_uncountable_domain D

/-! ### Axiom hygiene.

Every refutation above is pinned kernel-clean (`propext`, `Classical.choice`, `Quot.sound` only).
No `sorry`, no fresh `axiom`, no `native_decide`, no `decide` on an opaque predicate — the whole
argument is counting, and it must be checkable as such. -/

#assert_all_clean [
  uncountable_set_of_infinite, uncountable_pi_of_infinite, not_injective_of_uncountable_domain,
  balDigest_not_injective, capsDigest_not_injective, cellNatDigest_not_injective,
  cellValueDigest_not_injective, cellOptCellDigest_not_injective, cellCapListDigest_not_injective,
  cellSlotCaveatDigest_not_injective, cellHeapDigest_not_injective, capsNatPairDigest_not_injective,
  natCapsNatTripleDigest_not_injective, spawnCreateLegDigest_not_injective,
  bornEmptySideDigest_not_injective, bornEmptyAuthorityDigest_not_injective,
  recordKernelStateDigest_not_injective]

end Dregg2.Verify.InjSpelledFloors
