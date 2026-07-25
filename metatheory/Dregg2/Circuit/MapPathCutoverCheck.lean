/-
# Dregg2.Circuit.MapPathCutoverCheck — the SEMANTIC teeth of the MERKLE-PATH / HEAP-LEAF cutover.

The `Poseidon2SpongeCR` cutover of 2026-07-25 removed the refuted floor binder IN PLACE from the
deployed map/heap opening spine — `MapOpsColumnLayout.pathRecompute_binds_updates` (the crux path
law), `leafOf_injective`, the three per-kind openers, and the IMT leaf/layout leg
(`IndexedMerkleTree.imtLeafHash_injective`, `mem_phys_of_layout_get`, `imtVecCorr_mem`,
`imtLowUpdate_binds`) — replacing it with per-instance, refutable side conditions named by TOTAL
extractors (`pathCollFind`, `leafPre`, `imtLeafPre`, `ImtLeafCollIn`).

For each cut-over theorem the `example : ⟨type⟩ := @original` below re-proves ON EVERY BUILD, by
KERNEL defeq, that the in-place original has EXACTLY the post-cutover type: same conclusion, floor
binder gone, the per-instance side condition and nothing else. A silent weakening, a binder
reorder, or a floor-binder resurrection turns the build red HERE.

The `#assert_not_depends_on … [Poseidon2SpongeCR]` pins are the second tooth: `findForbiddenPath`
walks the transitive constant closure of BOTH the type and the proof term, so a floor route
re-entering by either door is a build error. `#assert_depends_on` on the extractor is the positive
control that the walk is not going blind.
-/
import Dregg2.Circuit.MapOpsColumnLayout
import Dregg2.Circuit.IndexedMerkleTree
import Dregg2.Tactics

namespace Dregg2.Circuit.MapPathCutoverCheck

set_option autoImplicit false


/-- ⚙ CUTOVER CHECK — `Dregg2.Circuit.MapOpsColumnLayout.pathRecompute_binds_updates` has EXACTLY the post-cutover type: the refuted
`Poseidon2SpongeCR` binder is gone, the per-instance side condition is in its place, the conclusion
is unchanged. Kernel defeq, re-proved every build. -/
example : ∀ (hash : List ℤ → ℤ) (steps : List (Bool × ℤ))
    (xs : List ℤ) (leaf : ℤ),
    xs.length = 2 ^ steps.length →
      Dregg2.Circuit.MapOpsColumnLayout.pathRecompute hash leaf steps =
          Dregg2.Circuit.MapMerkleRoot.perfectRoot hash steps.length xs →
        ¬Dregg2.Crypto.SpongeCarrierReduction.IsSpongeColl hash
              (Dregg2.Circuit.MapOpsColumnLayout.pathCollFind hash steps xs leaf) →
          xs[Dregg2.Circuit.MapOpsColumnLayout.pathPos steps]? = Option.some leaf ∧
            ∀ (leaf' : ℤ),
              Dregg2.Circuit.MapOpsColumnLayout.pathRecompute hash leaf' steps =
                Dregg2.Circuit.MapMerkleRoot.perfectRoot hash steps.length
                  (xs.set (Dregg2.Circuit.MapOpsColumnLayout.pathPos steps) leaf') :=
  @Dregg2.Circuit.MapOpsColumnLayout.pathRecompute_binds_updates
#assert_axioms Dregg2.Circuit.MapOpsColumnLayout.pathRecompute_binds_updates
#assert_not_depends_on Dregg2.Circuit.MapOpsColumnLayout.pathRecompute_binds_updates [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]

/-- ⚙ CUTOVER CHECK — `Dregg2.Circuit.MapOpsColumnLayout.leafOf_injective` has EXACTLY the post-cutover type: the refuted
`Poseidon2SpongeCR` binder is gone, the per-instance side condition is in its place, the conclusion
is unchanged. Kernel defeq, re-proved every build. -/
example : ∀ (hash : List ℤ → ℤ) {e₁ e₂ : ℤ × ℤ},
    ¬Dregg2.Crypto.SpongeCarrierReduction.IsSpongeColl hash
          (Dregg2.Circuit.MapOpsColumnLayout.leafPre e₁, Dregg2.Circuit.MapOpsColumnLayout.leafPre e₂) →
      Dregg2.Substrate.Heap.leafOf hash e₁ = Dregg2.Substrate.Heap.leafOf hash e₂ → e₁ = e₂ :=
  @Dregg2.Circuit.MapOpsColumnLayout.leafOf_injective
#assert_axioms Dregg2.Circuit.MapOpsColumnLayout.leafOf_injective
#assert_not_depends_on Dregg2.Circuit.MapOpsColumnLayout.leafOf_injective [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]

/-- ⚙ CUTOVER CHECK — `Dregg2.Circuit.MapOpsColumnLayout.opensToMerkle_of_path` has EXACTLY the post-cutover type: the refuted
`Poseidon2SpongeCR` binder is gone, the per-instance side condition is in its place, the conclusion
is unchanged. Kernel defeq, re-proved every build. -/
example : ∀ (hash : List ℤ → ℤ) (dep : ℕ) {r k v : ℤ}
    (h : Dregg2.Substrate.Heap.FeltHeap),
    Dregg2.Substrate.Heap.SortedKeys h →
      List.length h = 2 ^ dep →
        Dregg2.Circuit.MapMerkleRoot.mapRoot hash dep h = r →
          ∀ (steps : List (Bool × ℤ)),
            steps.length = dep →
              Dregg2.Circuit.MapOpsColumnLayout.pathRecompute hash (Dregg2.Substrate.Heap.leafOf hash (k, v)) steps = r →
                ¬Dregg2.Crypto.SpongeCarrierReduction.IsSpongeColl hash
                      (Dregg2.Circuit.MapOpsColumnLayout.pathCollFind hash steps
                        (List.map (Dregg2.Substrate.Heap.leafOf hash) h) (Dregg2.Substrate.Heap.leafOf hash (k, v))) →
                  ¬Dregg2.Crypto.SpongeCarrierReduction.IsSpongeColl hash
                        (Dregg2.Circuit.MapOpsColumnLayout.leafPre
                            (Dregg2.Circuit.MapOpsColumnLayout.heapAt h
                              (Dregg2.Circuit.MapOpsColumnLayout.pathPos steps)),
                          Dregg2.Circuit.MapOpsColumnLayout.leafPre (k, v)) →
                    Dregg2.Circuit.MapMerkleRoot.opensToMerkle hash dep r k (Option.some v) :=
  @Dregg2.Circuit.MapOpsColumnLayout.opensToMerkle_of_path
#assert_axioms Dregg2.Circuit.MapOpsColumnLayout.opensToMerkle_of_path
#assert_not_depends_on Dregg2.Circuit.MapOpsColumnLayout.opensToMerkle_of_path [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]

/-- ⚙ CUTOVER CHECK — `Dregg2.Circuit.MapOpsColumnLayout.opensToMerkle_none_of_bracket` has EXACTLY the post-cutover type: the refuted
`Poseidon2SpongeCR` binder is gone, the per-instance side condition is in its place, the conclusion
is unchanged. Kernel defeq, re-proved every build. -/
example : ∀ (hash : List ℤ → ℤ) (dep : ℕ) {r k : ℤ}
    (h : Dregg2.Substrate.Heap.FeltHeap),
    Dregg2.Substrate.Heap.SortedKeys h →
      List.length h = 2 ^ dep →
        Dregg2.Circuit.MapMerkleRoot.mapRoot hash dep h = r →
          ∀ (stepsLo stepsHi : List (Bool × ℤ)) {klo vlo khi vhi : ℤ},
            stepsLo.length = dep →
              stepsHi.length = dep →
                Dregg2.Circuit.MapOpsColumnLayout.pathPos stepsHi =
                    Dregg2.Circuit.MapOpsColumnLayout.pathPos stepsLo + 1 →
                  Dregg2.Circuit.MapOpsColumnLayout.pathRecompute hash (Dregg2.Substrate.Heap.leafOf hash (klo, vlo))
                        stepsLo =
                      r →
                    Dregg2.Circuit.MapOpsColumnLayout.pathRecompute hash (Dregg2.Substrate.Heap.leafOf hash (khi, vhi))
                          stepsHi =
                        r →
                      klo < k →
                        k < khi →
                          ¬Dregg2.Crypto.SpongeCarrierReduction.IsSpongeColl hash
                                (Dregg2.Circuit.MapOpsColumnLayout.pathCollFind hash stepsLo
                                  (List.map (Dregg2.Substrate.Heap.leafOf hash) h)
                                  (Dregg2.Substrate.Heap.leafOf hash (klo, vlo))) →
                            ¬Dregg2.Crypto.SpongeCarrierReduction.IsSpongeColl hash
                                  (Dregg2.Circuit.MapOpsColumnLayout.pathCollFind hash stepsHi
                                    (List.map (Dregg2.Substrate.Heap.leafOf hash) h)
                                    (Dregg2.Substrate.Heap.leafOf hash (khi, vhi))) →
                              ¬Dregg2.Crypto.SpongeCarrierReduction.IsSpongeColl hash
                                    (Dregg2.Circuit.MapOpsColumnLayout.leafPre
                                        (Dregg2.Circuit.MapOpsColumnLayout.heapAt h
                                          (Dregg2.Circuit.MapOpsColumnLayout.pathPos stepsLo)),
                                      Dregg2.Circuit.MapOpsColumnLayout.leafPre (klo, vlo)) →
                                ¬Dregg2.Crypto.SpongeCarrierReduction.IsSpongeColl hash
                                      (Dregg2.Circuit.MapOpsColumnLayout.leafPre
                                          (Dregg2.Circuit.MapOpsColumnLayout.heapAt h
                                            (Dregg2.Circuit.MapOpsColumnLayout.pathPos stepsHi)),
                                        Dregg2.Circuit.MapOpsColumnLayout.leafPre (khi, vhi)) →
                                  Dregg2.Circuit.MapMerkleRoot.opensToMerkle hash dep r k Option.none :=
  @Dregg2.Circuit.MapOpsColumnLayout.opensToMerkle_none_of_bracket
#assert_axioms Dregg2.Circuit.MapOpsColumnLayout.opensToMerkle_none_of_bracket
#assert_not_depends_on Dregg2.Circuit.MapOpsColumnLayout.opensToMerkle_none_of_bracket [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]

/-- ⚙ CUTOVER CHECK — `Dregg2.Circuit.MapOpsColumnLayout.writesToMerkle_of_path` has EXACTLY the post-cutover type: the refuted
`Poseidon2SpongeCR` binder is gone, the per-instance side condition is in its place, the conclusion
is unchanged. Kernel defeq, re-proved every build. -/
example : ∀ (hash : List ℤ → ℤ) (dep : ℕ) {r k v r' : ℤ}
    (h : Dregg2.Substrate.Heap.FeltHeap),
    Dregg2.Substrate.Heap.SortedKeys h →
      List.length h = 2 ^ dep →
        Dregg2.Circuit.MapMerkleRoot.mapRoot hash dep h = r →
          ∀ (steps : List (Bool × ℤ)) (vOld : ℤ),
            steps.length = dep →
              Dregg2.Circuit.MapOpsColumnLayout.pathRecompute hash (Dregg2.Substrate.Heap.leafOf hash (k, vOld)) steps =
                  r →
                Dregg2.Circuit.MapOpsColumnLayout.pathRecompute hash (Dregg2.Substrate.Heap.leafOf hash (k, v)) steps =
                    r' →
                  ¬Dregg2.Crypto.SpongeCarrierReduction.IsSpongeColl hash
                        (Dregg2.Circuit.MapOpsColumnLayout.pathCollFind hash steps
                          (List.map (Dregg2.Substrate.Heap.leafOf hash) h)
                          (Dregg2.Substrate.Heap.leafOf hash (k, vOld))) →
                    ¬Dregg2.Crypto.SpongeCarrierReduction.IsSpongeColl hash
                          (Dregg2.Circuit.MapOpsColumnLayout.leafPre
                              (Dregg2.Circuit.MapOpsColumnLayout.heapAt h
                                (Dregg2.Circuit.MapOpsColumnLayout.pathPos steps)),
                            Dregg2.Circuit.MapOpsColumnLayout.leafPre (k, vOld)) →
                      Dregg2.Circuit.MapMerkleRoot.writesToMerkle hash dep r k v r' :=
  @Dregg2.Circuit.MapOpsColumnLayout.writesToMerkle_of_path
#assert_axioms Dregg2.Circuit.MapOpsColumnLayout.writesToMerkle_of_path
#assert_not_depends_on Dregg2.Circuit.MapOpsColumnLayout.writesToMerkle_of_path [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]

/-- ⚙ CUTOVER CHECK — `Dregg2.Circuit.IndexedMerkleTree.imtLeafHash_injective` has EXACTLY the post-cutover type: the refuted
`Poseidon2SpongeCR` binder is gone, the per-instance side condition is in its place, the conclusion
is unchanged. Kernel defeq, re-proved every build. -/
example : ∀ (hash : List ℤ → ℤ)
    {l₁ l₂ : Dregg2.Circuit.IndexedMerkleTree.ImtLeaf},
    ¬Dregg2.Crypto.SpongeCarrierReduction.IsSpongeColl hash
          (Dregg2.Circuit.IndexedMerkleTree.imtLeafPre l₁, Dregg2.Circuit.IndexedMerkleTree.imtLeafPre l₂) →
      Dregg2.Circuit.IndexedMerkleTree.imtLeafHash hash l₁ = Dregg2.Circuit.IndexedMerkleTree.imtLeafHash hash l₂ →
        l₁ = l₂ :=
  @Dregg2.Circuit.IndexedMerkleTree.imtLeafHash_injective
#assert_axioms Dregg2.Circuit.IndexedMerkleTree.imtLeafHash_injective
#assert_not_depends_on Dregg2.Circuit.IndexedMerkleTree.imtLeafHash_injective [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]

/-- ⚙ CUTOVER CHECK — `Dregg2.Circuit.IndexedMerkleTree.mem_phys_of_layout_get` has EXACTLY the post-cutover type: the refuted
`Poseidon2SpongeCR` binder is gone, the per-instance side condition is in its place, the conclusion
is unchanged. Kernel defeq, re-proved every build. -/
example : ∀ (hash : List ℤ → ℤ) {pad : ℤ} {n : ℕ}
    {phys : List Dregg2.Circuit.IndexedMerkleTree.ImtLeaf} {p : ℕ} {low : Dregg2.Circuit.IndexedMerkleTree.ImtLeaf},
    ¬Dregg2.Circuit.IndexedMerkleTree.ImtLeafCollIn hash phys low →
      Dregg2.Circuit.IndexedMerkleTree.imtLeafHash hash low ≠ pad →
        (Dregg2.Circuit.IndexedMerkleTree.imtLayout hash pad n phys)[p]? =
            Option.some (Dregg2.Circuit.IndexedMerkleTree.imtLeafHash hash low) →
          low ∈ phys :=
  @Dregg2.Circuit.IndexedMerkleTree.mem_phys_of_layout_get
#assert_axioms Dregg2.Circuit.IndexedMerkleTree.mem_phys_of_layout_get
#assert_not_depends_on Dregg2.Circuit.IndexedMerkleTree.mem_phys_of_layout_get [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]

/-- ⚙ CUTOVER CHECK — `Dregg2.Circuit.IndexedMerkleTree.imtVecCorr_mem` has EXACTLY the post-cutover type: the refuted
`Poseidon2SpongeCR` binder is gone, the per-instance side condition is in its place, the conclusion
is unchanged. Kernel defeq, re-proved every build. -/
example : ∀ (hash : List ℤ → ℤ) {pad : ℤ} {n : ℕ}
    {c : List Dregg2.Circuit.IndexedMerkleTree.ImtLeaf} {xs : List ℤ} {p : ℕ}
    {low : Dregg2.Circuit.IndexedMerkleTree.ImtLeaf},
    ¬Dregg2.Circuit.IndexedMerkleTree.ImtLeafCollIn hash c low →
      Dregg2.Circuit.IndexedMerkleTree.ImtVecCorr hash pad n c xs →
        Dregg2.Circuit.IndexedMerkleTree.imtLeafHash hash low ≠ pad →
          xs[p]? = Option.some (Dregg2.Circuit.IndexedMerkleTree.imtLeafHash hash low) → low ∈ c :=
  @Dregg2.Circuit.IndexedMerkleTree.imtVecCorr_mem
#assert_axioms Dregg2.Circuit.IndexedMerkleTree.imtVecCorr_mem
#assert_not_depends_on Dregg2.Circuit.IndexedMerkleTree.imtVecCorr_mem [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]

/-- ⚙ CUTOVER CHECK — `Dregg2.Circuit.IndexedMerkleTree.imtLowUpdate_binds` has EXACTLY the post-cutover type: the refuted
`Poseidon2SpongeCR` binder is gone, the per-instance side condition is in its place, the conclusion
is unchanged. Kernel defeq, re-proved every build. -/
example : ∀ (hash : List ℤ → ℤ) (steps : List (Bool × ℤ)) (xs : List ℤ)
    (low : Dregg2.Circuit.IndexedMerkleTree.ImtLeaf) (newNext : ℤ),
    xs.length = 2 ^ steps.length →
      Dregg2.Circuit.MapOpsColumnLayout.pathRecompute hash (Dregg2.Circuit.IndexedMerkleTree.imtLeafHash hash low) steps =
          Dregg2.Circuit.MapMerkleRoot.perfectRoot hash steps.length xs →
        ¬Dregg2.Crypto.SpongeCarrierReduction.IsSpongeColl hash
              (Dregg2.Circuit.MapOpsColumnLayout.pathCollFind hash steps xs
                (Dregg2.Circuit.IndexedMerkleTree.imtLeafHash hash low)) →
          xs[Dregg2.Circuit.MapOpsColumnLayout.pathPos steps]? =
              Option.some (Dregg2.Circuit.IndexedMerkleTree.imtLeafHash hash low) ∧
            Dregg2.Circuit.MapOpsColumnLayout.pathRecompute hash
                (Dregg2.Circuit.IndexedMerkleTree.imtLeafHash hash
                  { addr := low.addr, value := low.value, nextAddr := newNext })
                steps =
              Dregg2.Circuit.MapMerkleRoot.perfectRoot hash steps.length
                (xs.set (Dregg2.Circuit.MapOpsColumnLayout.pathPos steps)
                  (Dregg2.Circuit.IndexedMerkleTree.imtLeafHash hash
                    { addr := low.addr, value := low.value, nextAddr := newNext })) :=
  @Dregg2.Circuit.IndexedMerkleTree.imtLowUpdate_binds
#assert_axioms Dregg2.Circuit.IndexedMerkleTree.imtLowUpdate_binds
#assert_not_depends_on Dregg2.Circuit.IndexedMerkleTree.imtLowUpdate_binds [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]

/-! ### POSITIVE CONTROL — the walk is not blind: each cut-over theorem genuinely REACHES the
total extractor / per-instance event that replaced the floor. -/

#assert_depends_on Dregg2.Circuit.MapOpsColumnLayout.pathRecompute_binds_updates
  [Dregg2.Circuit.MapOpsColumnLayout.pathCollFind,
   Dregg2.Crypto.SpongeCarrierReduction.IsSpongeColl]
#assert_depends_on Dregg2.Circuit.IndexedMerkleTree.imtVecCorr_mem
  [Dregg2.Circuit.IndexedMerkleTree.ImtLeafCollIn]

/-! ### THE BRIDGES — the only remaining floor carriers of this cutover, named. Each is the
one-line proof that the OLD hypothesis IMPLIES the new per-instance one, i.e. every ported theorem
is strictly STRONGER than the theorem it replaced. -/

#assert_axioms Dregg2.Circuit.MapOpsColumnLayout.noPathColl_of_CR
#assert_axioms Dregg2.Circuit.MapOpsColumnLayout.noLeafColl_of_CR
#assert_axioms Dregg2.Circuit.IndexedMerkleTree.noImtLeafColl_of_CR
#assert_axioms Dregg2.Circuit.IndexedMerkleTree.noImtLeafCollIn_of_CR

/-! ### THE UNCONDITIONAL CORES — hypothesis-free, hence true at deployed BabyBear parameters. -/

#assert_axioms Dregg2.Circuit.MapOpsColumnLayout.pathRecompute_binds_updates_or_collides
#assert_axioms Dregg2.Circuit.MapOpsColumnLayout.leafOf_binds_or_collides
#assert_axioms Dregg2.Circuit.IndexedMerkleTree.imtLeafHash_binds_or_collides
#assert_not_depends_on Dregg2.Circuit.MapOpsColumnLayout.pathRecompute_binds_updates_or_collides
  [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]
#assert_not_depends_on Dregg2.Circuit.MapOpsColumnLayout.leafOf_binds_or_collides
  [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]
#assert_not_depends_on Dregg2.Circuit.IndexedMerkleTree.imtLeafHash_binds_or_collides
  [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR]

/-! ### THE TEETH OF THE TEETH — load-bearing, refutable, non-vacuous (see `MapOpsColumnLayout`
§2b): `pathBinds_unconditional_false` (dropping the side condition is REFUTED),
`pathColl_refutable` / `leafColl_refutable` (the events can FIRE), `path_binds_fires` (the ported
binding genuinely fires, for EVERY hash, at an honest opening). -/

#assert_axioms Dregg2.Circuit.MapOpsColumnLayout.pathBinds_unconditional_false
#assert_axioms Dregg2.Circuit.MapOpsColumnLayout.pathColl_refutable
#assert_axioms Dregg2.Circuit.MapOpsColumnLayout.leafColl_refutable
#assert_axioms Dregg2.Circuit.MapOpsColumnLayout.path_binds_fires
#assert_axioms Dregg2.Circuit.MapOpsColumnLayout.pathCollFind_len_le

end Dregg2.Circuit.MapPathCutoverCheck
