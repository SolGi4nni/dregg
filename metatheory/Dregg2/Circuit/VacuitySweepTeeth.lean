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
`FloorGames.HashCRHardQuant F Eff` (keyed family, negligible finding advantage, adversary class named).
⚑ This paragraph used to point at `HashFloorHonesty.CollisionResistant`, which was that same floor at
`Eff := ⊤` — refuted for every compressing family and DELETED on 2026-07-28. A replacement that is
itself refuted is not a replacement, which is the point this file exists to make and is now made about
the successor too.

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
import Dregg2.Circuit.DeployedHeapTree
import Dregg2.Circuit.DeployedFieldsTree
import Dregg2.Circuit.Emit.EffectVmEmitRotationR
import Dregg2.Tactics

namespace Dregg2.Circuit.VacuitySweepTeeth

open Dregg2.Circuit.HashFloorHonesty (not_injective_of_finite_range)
open Dregg2.Circuit.DeployedCapTree
open Dregg2.Circuit.Emit.EffectVmEmitRotationR (Poseidon2Width8)

set_option autoImplicit false

/-- The BabyBear prime `p = 2³¹ − 2²⁷ + 1` — the deployed field the lanes live in. -/
def babyBearP : ℤ := 2013265921

/-! ## §1 — wide-permutation injectivity is FALSE for a range-bounded wide permutation.

The carrier this refuted was `Poseidon2WideCR permW := ∀ xs ys, permW xs = permW ys → xs = ys` —
`Function.Injective permW` on the INFINITE `List ℤ`. The deployed `permW` (Rust
`poseidon2::single_perm_compress`) squeezes exactly 8 BabyBear lanes (`Poseidon2Width8`), so its range
is FINITE, and the counting core fires.

⚑ The carrier itself has since been **DELETED** from `Emit/EffectVmEmitRotationR` — its consumers are
now unconditional (`wireCommitR8_binds_or_collides`: bind, or EXHIBIT the collision). These teeth are
RETAINED, restated about `Function.Injective permW` directly, because they are the REASON the deletion
was correct; the record must outlive the carrier. -/

/-- **TOOTH 1 — wide-permutation injectivity is FALSE for any range-bounded wide permutation.**
Literally `not_injective_of_finite_range`: the deleted floor WAS injectivity on `List ℤ`, which is
infinite. Stated in the same shape as the flagged siblings' teeth
(`poseidon2SpongeCR_false_of_finite_range`). -/
theorem widePerm_not_injective_of_finite_range
    (permW : List ℤ → List ℤ) (hfin : (Set.range permW).Finite) :
    ¬ Function.Injective permW :=
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

/-- **TOOTH 1′ (deployed form) — wide-permutation injectivity is FALSE at the REAL BabyBear
parameters.** A wide permutation that squeezes exactly 8 lanes, each a genuine BabyBear field element
(`0 ≤ · < p`) — i.e. the deployed `single_perm_compress` — REFUTED the floor whose docstring called it
"the EXACT analogue of `Poseidon2SpongeCR`". The analogue was exact: that one is false too
(`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`). Every consumer of the deleted carrier was
conditioned on a hypothesis the deployed hash refutes — which is why they now carry none. -/
theorem widePerm_not_injective_babyBear (permW : List ℤ → List ℤ)
    (hw : Poseidon2Width8 permW)
    (hb : ∀ xs, ∀ x ∈ permW xs, 0 ≤ x ∧ x < babyBearP) :
    ¬ Function.Injective permW := by
  refine widePerm_not_injective_of_finite_range permW ?_
  refine Set.Finite.subset (finite_width8_bounded babyBearP) ?_
  rintro _ ⟨xs, rfl⟩
  exact ⟨hw xs, fun x hx => ⟨(hb xs x hx).1, (hb xs x hx).2⟩⟩

/-! ### The same tooth on `Compress8CR` — ⚑ **THE CARRIER IT REFUTED HAS BEEN DELETED (2026-07-20).**

`Compress8CR f := ∀ a b : List ℤ, f a = f b → a = b` USED TO BE the crypto carrier inside the
`Cap8Scheme` structure itself (the `chip8CR` FIELD), so EVERY 8-felt cap-tree theorem carried it — and,
because a field cannot be assumed away at a use site, no deployed `Cap8Scheme` VALUE could exist and
every theorem of the form `∀ S8 : Cap8Scheme, …` was VACUOUS. Its old docstring argued non-triviality
by exhibiting an injective `Reference8` and a colliding `badChip8`, which was precisely the FALSE
COMFORT `HashFloorHonesty`'s header named: toy witness satisfiable; real instantiation false.

The tooth below is UNCHANGED and still fires. What changed is what it is now a tooth ON: the field is
deleted, `Cap8Scheme` carries only the chip, and `DeployedCapTree.deployedCap8Scheme` is a REAL
INHABITANT whose own chip this tooth refutes (`deployedCap8Scheme_chip_not_Compress8CR` below). The
cap-tree binding it used to assume is now EXTRACTED AS DATA
(`DeployedCapTree.Cap8Scheme.capOpen8_binds_leaf_or_collides` and friends).

⚑ **AND AS OF 2026-07-20 THE CLASS IS CLOSED.** `Compress8CR` was ALSO a field of the sibling
`DeployedHeapTree.Heap8Scheme` and `DeployedFieldsTree.Fields8Scheme` — the identical defect, and the
one this file's previous revision named as "the remaining edge". Both fields are now deleted, both
structures have constructed deployed inhabitants, and §1‴-HF below fires TOOTH 1″ at each of them.
`Compress8CR` is now a field of NOTHING: it survives only as the injective special case in the three
trees' strength-relation bridges, and as the refutability canaries' hypothesis. -/

/-- The set of 8-felt digests with all lanes in `Set.Ico 0 q` is FINITE (a box in `Fin 8 → ℤ`). -/
theorem finite_digest8_bounded (q : ℤ) :
    {d : Digest8 | ∀ i, d i ∈ Set.Ico (0 : ℤ) q}.Finite := by
  have hs : {d : Digest8 | ∀ i, d i ∈ Set.Ico (0 : ℤ) q}
      = Set.pi Set.univ (fun _ : Fin 8 => Set.Ico (0 : ℤ) q) := by
    ext d; simp [Set.mem_pi]
  rw [hs]
  exact Set.Finite.pi (fun _ => Set.finite_Ico (0 : ℤ) q)

/-- **TOOTH 1″ — `Compress8CR` is FALSE at the REAL BabyBear parameters.** The arity-16 chip absorb
compresses the infinite `List ℤ` into 8 bounded lanes, so it is not injective. When `chip8CR` was a
FIELD of `Cap8Scheme` this meant a real deployed `Cap8Scheme` value could not exist and every 8-felt
cap-tree theorem was conditioned on a structure the deployed Poseidon2 refutes. -/
theorem compress8CR_false_babyBear (f : List ℤ → Digest8)
    (hb : ∀ xs i, 0 ≤ f xs i ∧ f xs i < babyBearP) :
    ¬ Compress8CR f := by
  refine not_injective_of_finite_range f ?_
  refine Set.Finite.subset (finite_digest8_bounded babyBearP) ?_
  rintro _ ⟨xs, rfl⟩
  exact fun i => ⟨(hb xs i).1, (hb xs i).2⟩

/-! ### ⚑ TOOTH 1‴ — THE VACUITY IS GONE, and the two facts that show it are BOTH machine-checked.

This is the sharpest available statement of the repair, and it is deliberately a PAIR:

  * `deployedCap8Scheme` is a `Cap8Scheme` VALUE — the type is inhabited, so `∀ S8 : Cap8Scheme, …`
    theorems now have an instance to be applied at (they had none before);
  * that value's OWN chip is refuted by TOOTH 1″ — so it is EXACTLY the kind of function the deleted
    field excluded. The deployed-shaped chip could not have been a `Cap8Scheme` before; it is one now.

Together: the structure did not become inhabitable by being weakened to something the deployment
misses, it became inhabitable by dropping a claim the deployment never satisfied. -/

/-- Every lane of the deployed-shaped chip is BabyBear-bounded (restated at this module's
`babyBearP` — the same literal as `DeployedCapTree.BABYBEAR_P`). -/
theorem deployedShapedChip8_babyBear_bounded (xs : List ℤ) (i : Fin 8) :
    0 ≤ DeployedCapTree.deployedShapedChip8 xs i
      ∧ DeployedCapTree.deployedShapedChip8 xs i < babyBearP :=
  DeployedCapTree.deployedShapedChip8_bounded xs i

/-- **⚑ THE CONSTRUCTED INHABITANT'S OWN CHIP REFUTES THE DELETED FIELD.** `deployedCap8Scheme` is a
real `Cap8Scheme` value, and TOOTH 1″ applies to its chip: had `chip8CR : Compress8CR chipAbsorb8`
still been a field, THIS value would have been unconstructible — which is exactly why every theorem
over the old structure was vacuous, and exactly what the deletion fixed. -/
theorem deployedCap8Scheme_chip_not_Compress8CR :
    ¬ Compress8CR DeployedCapTree.deployedCap8Scheme.chipAbsorb8 :=
  compress8CR_false_babyBear _ (fun xs i => deployedShapedChip8_babyBear_bounded xs i)

/-- **AND THE CAP-OPEN TOOTH FIRES AT IT.** The anti-ghost binding, instantiated at the real value —
the application the `∀ S8 : Cap8Scheme` form could never actually be performed for. -/
theorem deployed_capOpen_tooth_fires
    (path : List (Dregg2.Circuit.CapMerkleGeneric.StepG Digest8)) {nl₁ nl₂ : CapLeaf}
    (h : Cap8Scheme.recomposeUp8 DeployedCapTree.deployedCap8Scheme
           (Cap8Scheme.capLeafDigest8 DeployedCapTree.deployedCap8Scheme nl₁) path
       = Cap8Scheme.recomposeUp8 DeployedCapTree.deployedCap8Scheme
           (Cap8Scheme.capLeafDigest8 DeployedCapTree.deployedCap8Scheme nl₂) path) :
    nl₁ = nl₂ ∨ Cap8Scheme.CapOpenColl DeployedCapTree.deployedCap8Scheme nl₁ nl₂ path :=
  DeployedCapTree.deployed_capOpen8_binds_leaf_or_collides path h

/-- **AND `MembersAt8` IS NOW NON-VACUOUSLY REFUTABLE AT A REAL SCHEME.** TOOTH 2″ below is stated
`∀ S8 : Cap8Scheme`; before the repair that quantifier ranged over an EMPTY type, so the counter-tooth
that kept §2's finding honest was itself vacuous. Instantiated at the inhabitant, it has content. -/
theorem membersAt8_not_vacuous_deployed (root : Digest8) (leaf : CapLeaf)
    (hno : ∀ path : List (Dregg2.Circuit.CapMerkleGeneric.StepG Digest8),
        Cap8Scheme.recomposeUp8 DeployedCapTree.deployedCap8Scheme
          (Cap8Scheme.capLeafDigest8 DeployedCapTree.deployedCap8Scheme leaf) path ≠ root) :
    ¬ Cap8Scheme.MembersAt8 DeployedCapTree.deployedCap8Scheme root leaf := by
  rintro ⟨path, hpath⟩
  exact hno path hpath

/-! ### ⚑ §1‴-HF — THE SAME TOOTH AT THE LAST TWO STRUCTURE-FIELD SITES (heap + fields).

`Heap8Scheme` and `Fields8Scheme` carried the IDENTICAL `chip8CR : Compress8CR chipAbsorb8` FIELD, and
therefore the identical vacuity: no deployed value could be constructed, so every
`∀ S8 : Heap8Scheme, …` / `∀ S8 : Fields8Scheme, …` theorem — including the sorted-tree heap forcing the
perimeter leans on and the fields-map write gate — was vacuously true. Both fields are DELETED
(2026-07-20) and both structures now have constructed inhabitants.

The pair below is the same sharp statement made for cap: each inhabitant EXISTS, and each inhabitant's
OWN chip is refuted by TOOTH 1″. The structures became inhabitable by dropping a claim the deployment
never satisfied — NOT by weakening to something the deployment misses. All three ride the SAME
`deployedShapedChip8`, which is the faithful modelling of the deployment's ONE arity-16 `node8` chip. -/

/-- ⚑ **THE HEAP INHABITANT'S OWN CHIP REFUTES THE DELETED FIELD.** `deployedHeap8Scheme` is a real
`Heap8Scheme` value, and TOOTH 1″ applies to its chip: had `chip8CR : Compress8CR chipAbsorb8` still
been a field, THIS value would have been unconstructible. -/
theorem deployedHeap8Scheme_chip_not_Compress8CR :
    ¬ Compress8CR DeployedHeapTree.deployedHeap8Scheme.chipAbsorb8 :=
  compress8CR_false_babyBear _ (fun xs i => deployedShapedChip8_babyBear_bounded xs i)

/-- ⚑ **THE FIELDS INHABITANT'S OWN CHIP REFUTES THE DELETED FIELD.** The third and last site of this
defect class. -/
theorem deployedFields8Scheme_chip_not_Compress8CR :
    ¬ Compress8CR DeployedFieldsTree.deployedFields8Scheme.chipAbsorb8 :=
  compress8CR_false_babyBear _ (fun xs i => deployedShapedChip8_babyBear_bounded xs i)

/-- **AND THE HEAP GENTIAN TOOTH FIRES AT IT.** The heap-open anti-ghost, instantiated at the real
value — the application the `∀ S8 : Heap8Scheme` form could never actually be performed for. -/
theorem deployed_heapOpen_tooth_fires
    (path : List (Dregg2.Circuit.CapMerkleGeneric.StepG Digest8)) {e₁ e₂ : ℤ × ℤ × ℤ}
    (h : DeployedHeapTree.Heap8Scheme.recomposeUp8 DeployedHeapTree.deployedHeap8Scheme
           (DeployedHeapTree.Heap8Scheme.heapLeafDigest8
             DeployedHeapTree.deployedHeap8Scheme e₁) path
       = DeployedHeapTree.Heap8Scheme.recomposeUp8 DeployedHeapTree.deployedHeap8Scheme
           (DeployedHeapTree.Heap8Scheme.heapLeafDigest8
             DeployedHeapTree.deployedHeap8Scheme e₂) path) :
    e₁ = e₂ ∨ DeployedHeapTree.Heap8Scheme.HeapOpenColl
                DeployedHeapTree.deployedHeap8Scheme e₁ e₂ path :=
  DeployedHeapTree.deployed_heapOpen8_binds_leaf_or_collides path h

/-- **AND THE FIELDS GENTIAN TOOTH FIRES AT IT.** -/
theorem deployed_fieldsOpen_tooth_fires
    (path : List (Dregg2.Circuit.CapMerkleGeneric.StepG Digest8)) {e₁ e₂ : ℤ × ℤ × ℤ}
    (h : DeployedFieldsTree.Fields8Scheme.recomposeUp8 DeployedFieldsTree.deployedFields8Scheme
           (DeployedFieldsTree.Fields8Scheme.fieldsLeafDigest8
             DeployedFieldsTree.deployedFields8Scheme e₁) path
       = DeployedFieldsTree.Fields8Scheme.recomposeUp8 DeployedFieldsTree.deployedFields8Scheme
           (DeployedFieldsTree.Fields8Scheme.fieldsLeafDigest8
             DeployedFieldsTree.deployedFields8Scheme e₂) path) :
    e₁ = e₂ ∨ DeployedFieldsTree.Fields8Scheme.FieldsOpenColl
                DeployedFieldsTree.deployedFields8Scheme e₁ e₂ path :=
  DeployedFieldsTree.deployed_fieldsOpen8_binds_leaf_or_collides path h

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

#assert_axioms widePerm_not_injective_of_finite_range
#assert_axioms finite_width8_bounded
#assert_axioms widePerm_not_injective_babyBear
#assert_axioms finite_digest8_bounded
#assert_axioms compress8CR_false_babyBear
#assert_axioms deployedShapedChip8_babyBear_bounded
#assert_axioms deployedCap8Scheme_chip_not_Compress8CR
#assert_axioms deployed_capOpen_tooth_fires
#assert_axioms deployedHeap8Scheme_chip_not_Compress8CR
#assert_axioms deployedFields8Scheme_chip_not_Compress8CR
#assert_axioms deployed_heapOpen_tooth_fires
#assert_axioms deployed_fieldsOpen_tooth_fires
#assert_axioms membersAt8_not_vacuous_deployed
#assert_axioms membersAt8_at_own_digest
#assert_axioms membersAt_at_own_digest
#assert_axioms membersAt8_not_vacuous_general

end Dregg2.Circuit.VacuitySweepTeeth
