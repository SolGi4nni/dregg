/-
# `Dregg2.Circuit.VacuitySweepTeeth` — TEETH for the 2026-07-16 VACUITY SWEEP.

Two findings, both PROVED here rather than asserted. Neither is a soundness hole; both are places
where a `Prop`'s name/docstring claims more than the `Prop` carries, which is the defect class that
produced `CoCurvilinearity` and `Arity8FiberBound`.

## §1 — the injective-hash floor class is BIGGER than the four `HashFloorHonesty` flagged.

`HashFloorHonesty` (2026-07) proved FOUR injectivity floors FALSE for any range-bounded hash —
`Poseidon2SpongeCR`, `StateCommit.compressNInjective`, `StateCommit.compressInjective`,
`HermineHintMLWE.HashCR` — and doc-marked them BROKEN in place. That pass did not sweep the class: a
census of `metatheory/Dregg2` on 2026-07-16 finds **~20 more carriers with the identical predicate
shape**, still doc-marked "REALIZABLE", none pointing at the teeth:

  `Poseidon2WideCR` (Emit/EffectVmEmitRotationR), `compress4Injective` (CommitDifferential),
  `cellLeafInjective` / `logHashInjective` (StateCommit, the SAME FILE as two flagged siblings),
  `HashInjective` (Exec/Factory), `Compress8CR` (DeployedCapTree), `Compress1CR`
  (Crypto/CommitmentBinding), `RootCR` / `LeafCR` / `PairCR` / `LenBindCR` (Apps/QueueRoot),
  `KeySetCR` (Apps/PreRotation), `RosterCR` (CouncilCommit), `CommitTreeInjective`
  (Spike/EffectVmConstraints2), `CompressInjective` (FriVerifier), `FloorDigestBinds`
  (Deos/InAirAuthorityDigestGadget), `Blake3NoCollision` (Blake3FloorReduce), `BindingHashCR`
  (Authority/MacaroonDischarge), `HonestSlotCR` (Crypto/RandomnessBeacon), `CompressionCR`
  (Crypto/SpongeReduction), `DomainSeparatedCR` (Poseidon2KeyedBridge).

§1 proves the representative — `Poseidon2WideCR`, the most load-bearing of the unflagged set (7
hypothesis uses) — FALSE at range-bounded parameters, by the SAME counting core. It is the sharpest
case because its own docstring says it is "the EXACT analogue of `Poseidon2SpongeCR`" — which
`HashFloorHonesty.poseidon2SpongeCR_false_babyBear` had already proved FALSE. The analogy was exact;
the conclusion did not travel. This is the `#assert_axioms`-is-blind-to-hypotheses point again: every
consumer is axiom-clean and every consumer is conditioned on a hypothesis that a real Poseidon2
refutes.

The honest replacement already exists and is unused by these carriers:
`HashFloorHonesty.CollisionResistant` (keyed family, negligible finding advantage).

## §2 — `MembersAt` / `MembersAt8`: the DEPTH is in the docstring, not in the `Prop`.

`DeployedCapTree.lean`'s header and the `cap_root.rs` twin pin `CAP_TREE_DEPTH = 16`
(`DeployedCapOpen.DEPTH := 16`). The membership carrier quantifies over a path with **no length
constraint**:

    def MembersAt8 (root : Digest8) (leaf : CapLeaf) : Prop :=
      ∃ path : List (CapMerkleGeneric.StepG Digest8),
        recomposeUp8 S8 (capLeafDigest8 S8 leaf) path = root

and `recomposeUp8 S8 cur [] = cur`, so a DEPTH-0 opening is a "membership". §2 proves it:
`membersAt8_at_own_digest` is `⟨[], rfl⟩`. The tree already leans on this —
`CircuitCompletenessAuthorityConstruct.lean:108` is literally `⟨[], rfl⟩` against an
`authConstructedRoot` defined AS the leaf digest.

**⚑ HONEST SCOPE — this is NOT a soundness hole, and the sweep says so.** Unlike `CoCurvilinearity`,
`MembersAt8` is NOT vacuous: `root` is a PARAMETER, not chosen by the existential, so for a real
committed root no short path is available and the carrier has genuine content
(`membersAt8_not_vacuous_general` proves exactly this — there is a `root`/`leaf` pair at which it is
FALSE). The defect is FAITHFULNESS, and it is polarity-dependent:

  * In NEGATIVE position (`DeployedFaithfulEff8.backed`, `DeployedFaithful8.backed`) an over-broad
    `MembersAt8` makes the ASSUMPTION STRONGER — those structures demand backing for depth-0
    openings the depth-16 circuit never emits. Assumes more than deployed; does not falsify anything.
  * In POSITIVE position (`deployedCapOpen_implies_authorizedEffB`'s `hopen`) the degenerate witness
    is available, so "membership" there is weaker than the deployed circuit's membership.

Either way no theorem in the tree is WRONG; the model is coarser than the circuit. Naming it is the
work. The repair (NOT applied here — it re-opens `CircuitCompletenessAuthorityConstruct`'s minimal
opening, which would need a genuine 16-step padded path, and touches 153 references across 20 files;
scoped in `docs/deos/VACUITY-SWEEP.md`) is to carry `path.length = DEPTH`, or to carry
`MembershipDepthGeneralRung2.LeafNodeSep` alongside and prove the cross-depth leg as that file
already does for the depth-4 fold.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`. Every
verdict PROVED.
-/
import Dregg2.Circuit.HashFloorHonesty
import Dregg2.Circuit.DeployedCapTree
import Dregg2.Circuit.Emit.EffectVmEmitRotationR
import Dregg2.Tactics

namespace Dregg2.Circuit.VacuitySweepTeeth

open Dregg2.Circuit.HashFloorHonesty (not_injective_of_finite_range)
open Dregg2.Circuit.DeployedCapTree
open Dregg2.Circuit.Emit.EffectVmEmitRotationR (Poseidon2WideCR Poseidon2Width8)

set_option autoImplicit false

/-- The BabyBear prime `p = 2³¹ − 2²⁷ + 1` — the deployed field the lanes live in. -/
def babyBearP : ℤ := 2013265921

/-! ## §1 — `Poseidon2WideCR` is FALSE for a range-bounded wide permutation.

`Poseidon2WideCR permW := ∀ xs ys, permW xs = permW ys → xs = ys` is `Function.Injective permW` on
the INFINITE `List ℤ`. The deployed `permW` (Rust `poseidon2::single_perm_compress`) squeezes exactly
8 BabyBear lanes (`Poseidon2Width8`), so its range is FINITE — and the counting core fires. -/

/-- **TOOTH 1 — `Poseidon2WideCR` is FALSE for any range-bounded wide permutation.** Literally
`not_injective_of_finite_range`: the floor IS injectivity on `List ℤ`, which is infinite. Stated in
the same shape as the flagged siblings' teeth (`poseidon2SpongeCR_false_of_finite_range`). -/
theorem poseidon2WideCR_false_of_finite_range
    (permW : List ℤ → List ℤ) (hfin : (Set.range permW).Finite) :
    ¬ Poseidon2WideCR permW :=
  not_injective_of_finite_range permW hfin

/-- The set of length-`8` lists whose entries all lie in `Set.Ico 0 q` is FINITE — it is the image of
the finite box `∏ Fin 8, Ico 0 q` under `List.ofFn`. This is what "the wide squeeze is 8 BabyBear
lanes" means as a set. -/
theorem finite_width8_bounded (q : ℤ) :
    {l : List ℤ | l.length = 8 ∧ ∀ x ∈ l, x ∈ Set.Ico (0 : ℤ) q}.Finite := by
  have hsub : {l : List ℤ | l.length = 8 ∧ ∀ x ∈ l, x ∈ Set.Ico (0 : ℤ) q} ⊆
      (fun f : Fin 8 → ℤ => List.ofFn f) '' Set.pi Set.univ (fun _ : Fin 8 => Set.Ico (0 : ℤ) q) := by
    rintro l ⟨hlen, hmem⟩
    refine ⟨fun i => l.get (Fin.cast hlen.symm i), ?_, ?_⟩
    · intro i _; exact hmem _ (List.get_mem _ _)
    · apply List.ext_getElem (by simp [hlen])
      intro n h1 h2
      rw [hlen] at h2
      interval_cases n <;> simp
  exact Set.Finite.subset (Set.Finite.image _ (Set.Finite.pi (fun _ => Set.finite_Ico (0 : ℤ) q))) hsub

/-- **TOOTH 1′ (deployed form) — `Poseidon2WideCR` is FALSE at the REAL BabyBear parameters.** A wide
permutation that squeezes exactly 8 lanes, each a genuine BabyBear field element (`0 ≤ · < p`) — i.e.
the deployed `single_perm_compress` — REFUTES the floor its own docstring calls "the EXACT analogue of
`Poseidon2SpongeCR`". The analogue is exact: that one is false too
(`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`). Every consumer of `Poseidon2WideCR` is
conditioned on a hypothesis the deployed hash refutes. -/
theorem poseidon2WideCR_false_babyBear (permW : List ℤ → List ℤ)
    (hw : Poseidon2Width8 permW)
    (hb : ∀ xs, ∀ x ∈ permW xs, 0 ≤ x ∧ x < babyBearP) :
    ¬ Poseidon2WideCR permW := by
  refine poseidon2WideCR_false_of_finite_range permW ?_
  refine Set.Finite.subset (finite_width8_bounded babyBearP) ?_
  rintro _ ⟨xs, rfl⟩
  exact ⟨hw xs, fun x hx => ⟨(hb xs x hx).1, (hb xs x hx).2⟩⟩

/-! ### The same tooth on `Compress8CR` — the floor the WHOLE native-8-felt cap tree rides.

`Compress8CR f := ∀ a b : List ℤ, f a = f b → a = b` (`DeployedCapTree.lean:630`) is the crypto
carrier inside the `Cap8Scheme` structure itself (`chip8CR`), so EVERY 8-felt cap-tree theorem
carries it. Its docstring argues non-triviality by exhibiting an injective `Reference8` and a
colliding `badChip8` — which is precisely the FALSE COMFORT `HashFloorHonesty`'s header already
named: "they satisfy the floor with a toy injective sponge, while the REAL compressing Poseidon2
refutes it." Toy witness satisfiable; real instantiation false. -/

/-- The set of 8-felt digests with all lanes in `Set.Ico 0 q` is FINITE (a box in `Fin 8 → ℤ`). -/
theorem finite_digest8_bounded (q : ℤ) :
    {d : Digest8 | ∀ i, d i ∈ Set.Ico (0 : ℤ) q}.Finite := by
  have hs : {d : Digest8 | ∀ i, d i ∈ Set.Ico (0 : ℤ) q}
      = Set.pi Set.univ (fun _ : Fin 8 => Set.Ico (0 : ℤ) q) := by
    ext d; simp [Set.mem_pi]
  rw [hs]
  exact Set.Finite.pi (fun _ => Set.finite_Ico (0 : ℤ) q)

/-- **TOOTH 1″ — `Compress8CR` is FALSE at the REAL BabyBear parameters.** The arity-16 chip absorb
compresses the infinite `List ℤ` into 8 bounded lanes, so it is not injective. Since `chip8CR` is a
FIELD of `Cap8Scheme`, a real deployed `Cap8Scheme` value cannot exist — every 8-felt cap-tree
theorem is conditioned on a structure the deployed Poseidon2 refutes. -/
theorem compress8CR_false_babyBear (f : List ℤ → Digest8)
    (hb : ∀ xs i, 0 ≤ f xs i ∧ f xs i < babyBearP) :
    ¬ Compress8CR f := by
  refine not_injective_of_finite_range f ?_
  refine Set.Finite.subset (finite_digest8_bounded babyBearP) ?_
  rintro _ ⟨xs, rfl⟩
  exact fun i => ⟨(hb xs i).1, (hb xs i).2⟩

/-! ## §2 — `MembersAt8`: the depth-16 claim is not carried; a depth-0 opening is a "membership". -/

/-- **TOOTH 2 — a DEPTH-0 opening satisfies `MembersAt8`.** The empty path recomposes to the held
digest (`recomposeUp8 S8 cur [] = cur`), so every leaf is a "member" of the root that equals its own
digest — at depth `0`, while `DeployedCapOpen.DEPTH = 16`. The `∃ path` has no length clause; the
depth lives only in the docstring and the Rust twin. `⟨[], rfl⟩` — the same witness
`CircuitCompletenessAuthorityConstruct.lean:108` already uses. -/
theorem membersAt8_at_own_digest (S8 : Cap8Scheme) (leaf : CapLeaf) :
    Cap8Scheme.MembersAt8 S8 (Cap8Scheme.capLeafDigest8 S8 leaf) leaf :=
  ⟨[], rfl⟩

/-- **TOOTH 2′ — the 1-felt twin has the identical hole.** Same `⟨[], rfl⟩`. -/
theorem membersAt_at_own_digest {State : Type} (S : CapHashScheme State) (leaf : CapLeaf) :
    CapHashScheme.MembersAt S (CapHashScheme.capLeafDigest S leaf) leaf :=
  ⟨[], rfl⟩

/-! ### The counter-tooth: `MembersAt8` is NOT vacuous — and that distinction is the finding.

`CoCurvilinearity` was VACUOUS because the existential chose its own witness against an unconstrained
target. `MembersAt8` does NOT have that defect: `root` is a PARAMETER. §2's teeth show the carrier
admits DEPTH-0 openings (a faithfulness gap against a depth-16 circuit), not that it is free. Proving
the difference is what keeps this sweep honest — a clean carrier reported as broken is as bad as the
reverse. -/

/-- **TOOTH 2″ — `MembersAt8` has genuine content: it is refutable.** Any `root` unreachable from
`leaf`'s digest by ANY fold refutes it, so the existential is doing real work and the §2 finding is
about DEPTH, not about vacuity. -/
theorem membersAt8_not_vacuous_general (S8 : Cap8Scheme) (root : Digest8) (leaf : CapLeaf)
    (hno : ∀ path : List (Dregg2.Circuit.CapMerkleGeneric.StepG Digest8),
        Cap8Scheme.recomposeUp8 S8 (Cap8Scheme.capLeafDigest8 S8 leaf) path ≠ root) :
    ¬ Cap8Scheme.MembersAt8 S8 root leaf := by
  rintro ⟨path, hpath⟩
  exact hno path hpath

/-! ## §3 — axiom-hygiene tripwires. -/

#assert_axioms poseidon2WideCR_false_of_finite_range
#assert_axioms finite_width8_bounded
#assert_axioms poseidon2WideCR_false_babyBear
#assert_axioms finite_digest8_bounded
#assert_axioms compress8CR_false_babyBear
#assert_axioms membersAt8_at_own_digest
#assert_axioms membersAt_at_own_digest
#assert_axioms membersAt8_not_vacuous_general

end Dregg2.Circuit.VacuitySweepTeeth
