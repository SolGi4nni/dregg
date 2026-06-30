/-!
# `CapMerkleGeneric` — the width-AGNOSTIC cap-Merkle recompose + its anti-ghost spine.

This is the Option-A abstraction for the `cap_root` native-8-felt weld (Phase H-CAP-8): the
sorted-binary-Merkle membership recompose, parameterized over an ABSTRACT digest type `D` and an
internal-node function `node : D → D → D`. The ONE soundness lemma the whole cap-open corpus rests
on — `recomposeG` is injective in its starting leaf digest along a FIXED path, under the node's
collision-resistance — is proved ONCE here, generically, and INSTANTIATED twice:

  * `D := ℤ`, `node := DeployedCapTree.nodeOf` (the deployed 1-felt `cap_root.rs::cap_node`), with
    `node_inj := DeployedCapTree.nodeOf_injective` — RECOVERS the existing 1-felt proof.
  * `D := Fin 8 → ℤ` (or any 8-felt digest carrier), `node := nodeOf8` (the `node8` chip
    compression `cap_root.rs::cap_node8`), with `node_inj` from the arity-16 chip's CR — the NEW
    8-felt instance, with NO re-proof of the recompose spine.

The point (per the grind methodology): REUSE the 1-felt proof effort. `recomposeG_inj_of_path` only
ever calls `node_inj` (peeling one level per `node`-injectivity step) and the `recomposeG` unfold —
nothing width-specific — so the 1→8 migration of the membership soundness is a re-INSTANTIATION, not
a re-proof. The mix convention matches `cap_root.rs::recompose_membership` / `DeployedCapTree.recomposeUp`
byte-for-byte: `dir = false` ⇒ `cur` is the LEFT child (`node cur sib`), `dir = true` ⇒ RIGHT child
(`node sib cur`).
-/

namespace Dregg2.Circuit.CapMerkleGeneric

variable {D : Type}

/-- One Merkle path step over an abstract digest type `D`: the sibling digest at this level plus the
direction bit. The 1-felt `DeployedCapTree.Step` is `StepG ℤ`; the 8-felt tree uses `StepG (Fin 8 → ℤ)`. -/
structure StepG (D : Type) where
  /-- The sibling digest at this level (`cap_root.rs` `siblings[level]`). -/
  sib : D
  /-- `false` ⇒ `cur` is the LEFT child (sibling on the right); `true` ⇒ RIGHT child. -/
  dir : Bool

/-- **`recomposeG node cur path`** — fold the held digest up the sibling/direction path through the
abstract node `node`, mixing `(cur, sib)` by the direction bit. Width-agnostic twin of
`DeployedCapTree.recomposeUp` and `cap_root.rs::recompose_membership`. -/
def recomposeG (node : D → D → D) (cur : D) : List (StepG D) → D
  | [] => cur
  | s :: rest =>
    recomposeG node (if s.dir then node s.sib cur else node cur s.sib) rest

/-- **THE width-agnostic anti-ghost spine.** Under the node's collision-resistance (`node` injective
in BOTH children), `recomposeG` is injective in its STARTING digest along any FIXED path: equal
recomposed roots from the same path force equal starting leaf digests. A prover cannot keep the
published root while swapping the opened leaf along a fixed path — at ANY digest width.

This is the SINGLE proof the 1-felt (`nodeOf`) and 8-felt (`nodeOf8`) cap trees both instantiate; it
calls ONLY `node_inj` and the `recomposeG` unfold (nothing width-specific). -/
theorem recomposeG_inj_of_path
    (node : D → D → D)
    (node_inj : ∀ {l₁ r₁ l₂ r₂ : D}, node l₁ r₁ = node l₂ r₂ → l₁ = l₂ ∧ r₁ = r₂)
    (path : List (StepG D)) :
    ∀ {a b : D}, recomposeG node a path = recomposeG node b path → a = b := by
  induction path with
  | nil => intro a b h; simpa [recomposeG] using h
  | cons s rest ih =>
    intro a b h
    simp only [recomposeG] at h
    have hstep := ih h
    cases hd : s.dir with
    | false =>
      rw [hd] at hstep
      simp only [Bool.false_eq_true, if_false] at hstep
      exact (node_inj hstep).1
    | true =>
      rw [hd] at hstep
      simp only [if_true] at hstep
      exact (node_inj hstep).2

end Dregg2.Circuit.CapMerkleGeneric
