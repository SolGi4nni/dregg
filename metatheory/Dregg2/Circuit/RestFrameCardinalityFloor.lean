/-
# `Dregg2.Circuit.RestFrameCardinalityFloor` — `RestHashIffFrame` is FALSE, at every width, for
every rest-hash. The floor both vacuity instruments were blind to.

`StateCommit.RestHashIffFrame RH` says the kernel's rest-hash is INJECTIVE on the non-`cell`
components:

    ∀ k k', RH k = RH k' ↔ (k'.accounts = k.accounts ∧ k'.caps = k.caps ∧ k'.bal = k.bal ∧ … )

It is the fifth field of `CircuitSoundness.CommitSurface` (beside the four gated CR carriers), it is
a hypothesis in 234 binder positions across 85 modules, and the whole state-commitment binding chain
(`recStateCommit_binds_kernel`, `commit_binds`, and the `_orBreak` REGROUNDED twins that were built
precisely to be valid at a real hash) rests on it.

⚑ **AND IT IS UNSATISFIABLE BY CARDINALITY.** Two of the components it must separate are FUNCTION
SPACES — `bal : CellId → AssetId → ℤ` and `caps : Caps = Label → List Cap`, with
`CellId = AssetId = Label = ℕ` — so `RH` would have to be injective on a domain of size at least
`2 ^ ℵ₀`, landing in the countable `ℤ`. `restHashIffFrame_false_by_cardinality` proves that by
Cantor: the `Set ℕ`-indexed family of kernels that differ only in `bal` would give an injection
`Set ℕ → ℕ`, which `Function.cantor_injective` refutes.

This is STRONGER than every other refutation in the campaign, and the difference matters. The gated
floors (`Poseidon2SpongeCR`, `compressNInjective`, `cellLeafInjective`, `logHashInjective`, …) are
false *at deployed BabyBear width* — true of a hypothetical unbounded hash, false of the one we ship,
which is why the honest repair is a per-instance non-collision side condition at the pair the proof
actually uses. `RestHashIffFrame` has no such repair: it is false for EVERY `RH : RecordKernelState →
ℤ`, at any width, on any machine. There is no instance to be per-instance at.

## Why neither instrument saw it

* `scripts/binding_surface_complete.py` tier A is a BINDER-POSITION test over a hand-checked list of
  refuted floors. `RestHashIffFrame` is not on that list (nothing in the tree refuted it until now),
  and its `CommitSurface` occurrence is a structure FIELD, which the ruler documents as a known
  false-negative.
* `#floor_ratchet` DERIVES its floor set instead of listing it, which is the better design — but the
  derivation requires the floor to be injectivity-SHAPED (`FloorCensus.injShape` / `injShapeAnd`:
  the telescoped body must be an fvar equation, or a conjunction of them). `RestHashIffFrame`'s body
  is an ∀-IFF over a 17-fold conjunction of component equalities, so it does not match, and it is not
  a named sentinel. Landing this refutation therefore does NOT promote it — checked against both
  shape tests before writing — and the tree does not turn red. That is a gap in the derivation, not
  a reason to widen it blindly: the honest statement is that the gate defends the floors it can
  recognise, and this one has to be recognised by a human.

## What it means for the repair

`CommitSurface` cannot be re-inhabited by shedding its four gated CR fields alone — the exact
"shed one floor of a multi-floor declaration and the metric moves by zero" failure, one level deeper.
`restFrame` must go in the SAME pass. The structural repair is the one this class always wants and
`Verify/InjSpelledFloors` already names: digest the FINITE support actually touched — the
`accounts : Finset CellId` rows — never the whole function. A finitely-supported rest-view has a
genuine injective encoding, and the resulting side condition is a per-instance non-collision at the
two encoded row-lists, exactly like every other cut-over endpoint in the campaign.

No `sorry`, no `axiom`, no `native_decide`.
-/
import Dregg2.Circuit.StateCommit

namespace Dregg2.Circuit.RestFrameCardinalityFloor

open Dregg2.Circuit.StateCommit (RestHashIffFrame kS0)
open Dregg2.Exec (RecordKernelState)

set_option autoImplicit false

/-! ## §1 — the separating family.

One kernel per SET of cells, differing from `kS0` only in the per-asset ledger `bal`: cell `c` holds
one unit of every asset iff `c ∈ s`. Nothing about this family is exotic — it is a set of perfectly
ordinary ledgers, which is the point: `RestHashIffFrame` claims to tell all of them apart. -/

/-- The `Set ℕ`-indexed ledger family: `bal c a = 1` iff `c ∈ s`. -/
noncomputable def balFam (s : Set Nat) : RecordKernelState :=
  { kS0 with bal := fun c _ => s.indicator (fun _ => (1 : ℤ)) c }

/-- The family really is indexed by the set: the ledger reads back the membership. (Non-degeneracy —
without this the Cantor step below could be riding a constant family.) -/
theorem balFam_bal_mem {s : Set Nat} {c : Nat} (h : c ∈ s) (a : Nat) :
    (balFam s).bal c a = 1 := by
  simp [balFam, Set.indicator_of_mem h]

/-- …and off the set it reads back `0`. -/
theorem balFam_bal_notMem {s : Set Nat} {c : Nat} (h : c ∉ s) (a : Nat) :
    (balFam s).bal c a = 0 := by
  simp [balFam, Set.indicator_of_notMem h]

/-! ## §2 — ⚑ THE REFUTATION. -/

/-- **⚑ `RestHashIffFrame RH` is FALSE for EVERY rest-hash, at EVERY width.**

Not "false at deployed BabyBear parameters" — false, period, by CARDINALITY. The predicate demands
that `RH : RecordKernelState → ℤ` separate any two kernels differing in `bal : CellId → AssetId → ℤ`
(or in `caps : Label → List Cap`). Composing the `Set ℕ`-indexed family `balFam` with `RH` and with
`Encodable.encode : ℤ → ℕ` would therefore be an INJECTION `Set ℕ → ℕ`, and `Function.cantor_injective`
says no such thing exists.

So every declaration carrying `RestHashIffFrame` as a hypothesis (234 binder positions in 85 modules
at the time of writing) is VACUOUS, and `CircuitSoundness.CommitSurface` — which carries it as its
fifth FIELD, beside the four gated CR carriers — has no inhabitant at all. -/
theorem restHashIffFrame_false_by_cardinality (RH : RecordKernelState → ℤ) :
    ¬ RestHashIffFrame RH := by
  intro hRest
  -- An injection `Set ℕ → ℕ`, which Cantor refutes.
  refine Function.cantor_injective (fun s : Set Nat => Encodable.encode (RH (balFam s))) ?_
  intro s t h
  have hR : RH (balFam s) = RH (balFam t) := Encodable.encode_injective h
  -- the `bal` conjunct of the frame readout
  have hbal : (balFam t).bal = (balFam s).bal := (((hRest (balFam s) (balFam t)).mp hR).2.2.1)
  have key : ∀ c : Nat, Set.indicator t (fun _ => (1 : ℤ)) c
      = Set.indicator s (fun _ => (1 : ℤ)) c := fun c => congrFun (congrFun hbal c) 0
  ext c
  have hc := key c
  constructor
  · intro hs
    by_contra ht
    rw [Set.indicator_of_notMem ht, Set.indicator_of_mem hs] at hc
    exact absurd hc (by norm_num)
  · intro ht
    by_contra hs
    rw [Set.indicator_of_mem ht, Set.indicator_of_notMem hs] at hc
    exact absurd hc (by norm_num)

/-! ## §3 — the same statement at the deployed shape, so no one reads §2 as an abstract curiosity.

`RH` above is universally quantified, so this already covers the real Poseidon2 rest-hash. Spelled
out at the deployed range bound for the reader who expects the campaign's usual
`…_false_babyBear` form: the bound is IRRELEVANT here, and saying so is the content. -/

/-- **The BabyBear window is not what breaks this one.** Even granted the deployed range bound, the
refutation is the SAME theorem — the width hypothesis is discharged and unused, because the
obstruction is the domain, not the codomain. Any future "widen the digest to 8 felts" repair (the
answer for the CR floors) does NOTHING here. -/
theorem restHashIffFrame_false_at_babyBear (RH : RecordKernelState → ℤ)
    (_hb : ∀ k, 0 ≤ RH k ∧ RH k < (2013265921 : ℤ)) : ¬ RestHashIffFrame RH :=
  restHashIffFrame_false_by_cardinality RH

#assert_axioms restHashIffFrame_false_by_cardinality
#assert_axioms restHashIffFrame_false_at_babyBear
#assert_axioms balFam_bal_mem

end Dregg2.Circuit.RestFrameCardinalityFloor
