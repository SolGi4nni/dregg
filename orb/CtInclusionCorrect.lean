/-
CtInclusionCorrect — RFC 6962 section 2.1 audit-path verification, correctness by
refinement.

The verifier in `Ct.Inclusion` (`verifyInclusion`, backed by `rootFromPath`)
recomputes a Merkle tree head by a *split-recursion*: at a size-`n` node it peels
the head sibling of the path and descends into the left or right subtree.  This
file states, independently of that verifier, what RFC 6962 section 2.1 *mandates*
verification to compute, and proves the deployed verifier meets it on every input.

The specification is `recomputeRoot`:

  * `inclusionDirs i n` is the root-to-leaf *bit decomposition* of leaf index `i`
    in a size-`n` tree — at each level the RFC 6962 list of size `n` splits at
    `k = split n` (the largest power of two strictly less than `n`, section 2.1)
    and the target descends LEFT iff `i < k`.  It is a function of the tree
    geometry alone and never mentions the verifier.

  * `recomputeRoot HS lh i n path` folds the audit-path siblings (root-first) up
    from the leaf hash `lh`, combining each sibling on the left or right per
    `inclusionDirs i n`, and returns the reconstructed head — or `none` when the
    path length disagrees with the geometry.

`verifyInclusion_iff_recomputeRoot` is the refinement: the deployed
`Ct.verifyInclusion` accepts *iff* this independent recompute reconstructs exactly
the claimed root, for ALL inputs — honest or adversarial.  Non-vacuity is
discharged concretely: `verifyInclusion_reject_wrong_root` and
`verifyInclusion_reject_wrong_sibling` prove the verifier REJECTS a mismatched
root and a corrupted sibling, spending the collision-resistance field
`hnode_inj`.
-/
import Ct.Inclusion

namespace Ct

variable {Leaf H : Type}

/-! ### The RFC 6962 bit decomposition of an index -/

/-- Root-to-leaf descent directions for leaf index `i` in a size-`n` RFC 6962
Merkle tree: `true` at a level means the target leaf lies in the LEFT subtree (so
the audit-path sibling at that level is the RIGHT child), `false` means the RIGHT
subtree.  At each node the RFC 6962 (section 2.1) list of size `n ≥ 2` splits at
`k = split n` — the largest power of two strictly less than `n` — and the target
descends left iff `i < k`.  Defined from the tree geometry alone. -/
def inclusionDirs : Nat → Nat → List Bool
  | i, n =>
    if h : 2 ≤ n then
      if i < split n then true :: inclusionDirs i (split n)
      else false :: inclusionDirs (i - split n) (n - split n)
    else []
termination_by _ n => n
decreasing_by
  · exact split_lt h
  · exact Nat.sub_lt (by omega) (split_pos h)

theorem inclusionDirs_le1 {i n : Nat} (h : n ≤ 1) : inclusionDirs i n = [] := by
  rw [inclusionDirs]; simp only [dif_neg (by omega : ¬ 2 ≤ n)]

theorem inclusionDirs_left {i n : Nat} (h : 2 ≤ n) (hik : i < split n) :
    inclusionDirs i n = true :: inclusionDirs i (split n) := by
  rw [inclusionDirs]; simp only [dif_pos h, if_pos hik]

theorem inclusionDirs_right {i n : Nat} (h : 2 ≤ n) (hik : ¬ i < split n) :
    inclusionDirs i n = false :: inclusionDirs (i - split n) (n - split n) := by
  rw [inclusionDirs]; simp only [dif_pos h, if_neg hik]

/-! ### The RFC 6962 recompute-root specification -/

/-- Combining step: fold a sibling into the accumulated subtree head on the side
the descent direction dictates.  `true` (target was the LEFT child) puts the
accumulated head on the left; `false` puts it on the right. -/
def inclCombine (HS : HashScheme Leaf H) (dp : Bool × H) (acc : H) : H :=
  if dp.1 then HS.hnode acc dp.2 else HS.hnode dp.2 acc

/-- **RFC 6962 section 2.1 recompute-root specification.**  Fold the audit-path
siblings (root-first) up from the leaf hash `lh`, combining on the left/right per
the bit decomposition `inclusionDirs i n`, and return the reconstructed tree head
— or `none` if the path length disagrees with the tree geometry.  Defined without
reference to the verifier. -/
def recomputeRoot (HS : HashScheme Leaf H) (lh : H) (i n : Nat) (path : List H) :
    Option H :=
  if (inclusionDirs i n).length = path.length then
    some (List.foldr (inclCombine HS) lh ((inclusionDirs i n).zip path))
  else none

/-! ### Specification-side unfolding lemmas -/

theorem recomputeRoot_nil_le1 (HS : HashScheme Leaf H) (lh : H) {n : Nat} (i : Nat)
    (h : n ≤ 1) : recomputeRoot HS lh i n [] = some lh := by
  unfold recomputeRoot
  rw [inclusionDirs_le1 h]
  simp

theorem recomputeRoot_cons_le1 (HS : HashScheme Leaf H) (lh : H) {n : Nat} (i : Nat)
    (h : n ≤ 1) (s : H) (rest : List H) :
    recomputeRoot HS lh i n (s :: rest) = none := by
  unfold recomputeRoot
  rw [inclusionDirs_le1 h]
  simp

theorem recomputeRoot_nil_ge2 (HS : HashScheme Leaf H) (lh : H) {n : Nat} (i : Nat)
    (h : 2 ≤ n) : recomputeRoot HS lh i n [] = none := by
  unfold recomputeRoot
  by_cases hik : i < split n
  · rw [inclusionDirs_left h hik]; simp
  · rw [inclusionDirs_right h hik]; simp

theorem recomputeRoot_cons_left (HS : HashScheme Leaf H) (lh : H) {n : Nat} (i : Nat)
    (h : 2 ≤ n) (hik : i < split n) (sib : H) (rest : List H) :
    recomputeRoot HS lh i n (sib :: rest) =
      (recomputeRoot HS lh i (split n) rest).map (fun L => HS.hnode L sib) := by
  unfold recomputeRoot
  rw [inclusionDirs_left h hik]
  by_cases hlen : (inclusionDirs i (split n)).length = rest.length
  · simp [List.zip_cons_cons, inclCombine, hlen]
  · have : ¬ ((inclusionDirs i (split n)).length + 1 = rest.length + 1) := by omega
    simp [List.zip_cons_cons, inclCombine, hlen, this]

theorem recomputeRoot_cons_right (HS : HashScheme Leaf H) (lh : H) {n : Nat} (i : Nat)
    (h : 2 ≤ n) (hik : ¬ i < split n) (sib : H) (rest : List H) :
    recomputeRoot HS lh i n (sib :: rest) =
      (recomputeRoot HS lh (i - split n) (n - split n) rest).map
        (fun R => HS.hnode sib R) := by
  unfold recomputeRoot
  rw [inclusionDirs_right h hik]
  by_cases hlen : (inclusionDirs (i - split n) (n - split n)).length = rest.length
  · simp [List.zip_cons_cons, inclCombine, hlen]
  · have : ¬ ((inclusionDirs (i - split n) (n - split n)).length + 1 = rest.length + 1) := by
      omega
    simp [List.zip_cons_cons, inclCombine, hlen, this]

/-! ### The refinement: the deployed verifier meets the specification -/

/-- The deployed verifier core recomputes exactly the specification's head, on
every index, size, and path — including malformed ones (both sides return `none`
on a length mismatch).  Proved by strong recursion on the tree size, mirroring the
split-recursion of `rootFromPath` against the fold of `recomputeRoot`. -/
theorem rootFromPath_eq_recomputeRoot (HS : HashScheme Leaf H) (lh : H) :
    ∀ (n i : Nat) (path : List H),
      rootFromPath HS lh i n path = recomputeRoot HS lh i n path := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i path
    by_cases hn : n ≤ 1
    · cases path with
      | nil => rw [rootFromPath_le1 HS lh i hn, recomputeRoot_nil_le1 HS lh i hn]
      | cons s rest =>
        rw [rootFromPath_le1 HS lh i hn, recomputeRoot_cons_le1 HS lh i hn]
    · have h2 : 2 ≤ n := by omega
      by_cases hik : i < split n
      · cases path with
        | nil => rw [rootFromPath_ge2 HS lh i h2, recomputeRoot_nil_ge2 HS lh i h2]
        | cons sib rest =>
          rw [rootFromPath_ge2 HS lh i h2, recomputeRoot_cons_left HS lh i h2 hik]
          simp only [if_pos hik]
          rw [ih (split n) (split_lt h2) i rest]
      · cases path with
        | nil => rw [rootFromPath_ge2 HS lh i h2, recomputeRoot_nil_ge2 HS lh i h2]
        | cons sib rest =>
          rw [rootFromPath_ge2 HS lh i h2, recomputeRoot_cons_right HS lh i h2 hik]
          simp only [if_neg hik]
          rw [ih (n - split n) (Nat.sub_lt (by omega) (split_pos h2)) (i - split n) rest]

/-- **Correctness of RFC 6962 inclusion verification (section 2.1).**  The
deployed `Ct.verifyInclusion` accepts *iff* the independent RFC 6962 recompute
reconstructs exactly the claimed root — for all inputs, honest or adversarial. -/
theorem verifyInclusion_iff_recomputeRoot (HS : HashScheme Leaf H) [DecidableEq H]
    (lh : H) (i n : Nat) (path : List H) (root : H) :
    verifyInclusion HS lh i n path root = true
      ↔ recomputeRoot HS lh i n path = some root := by
  unfold verifyInclusion
  rw [rootFromPath_eq_recomputeRoot HS lh n i path]
  cases hr : recomputeRoot HS lh i n path with
  | none => simp
  | some r => simp [decide_eq_true_eq]

/-! ### Non-vacuity: wrong roots and corrupted siblings are rejected -/

/-- A mismatched root is REJECTED: if the verifier accepts against `root`, it
rejects every other claimed root `root'`.  (The specification is a function, so at
most one root can verify.) -/
theorem verifyInclusion_reject_wrong_root (HS : HashScheme Leaf H) [DecidableEq H]
    (lh : H) (i n : Nat) (path : List H) {root root' : H}
    (hv : verifyInclusion HS lh i n path root = true) (hne : root' ≠ root) :
    verifyInclusion HS lh i n path root' = false := by
  have hrec := (verifyInclusion_iff_recomputeRoot HS lh i n path root).mp hv
  cases hx : verifyInclusion HS lh i n path root' with
  | false => rfl
  | true =>
    have h2 := (verifyInclusion_iff_recomputeRoot HS lh i n path root').mp hx
    rw [hrec] at h2
    have hrr : root = root' := by simpa using h2
    exact absurd hrr.symm hne

/-- A corrupted sibling is REJECTED: at an interior level, replacing the honest
sibling `sib` by any different `sib'` flips an accepted proof to rejected.  This
is where collision resistance (`hnode_inj`) is spent — a distinct sibling forces a
distinct recomputed head, which cannot equal the same root. -/
theorem verifyInclusion_reject_wrong_sibling (HS : HashScheme Leaf H) [DecidableEq H]
    (lh : H) {i n : Nat} (h2 : 2 ≤ n) (hik : i < split n)
    {sib sib' : H} (rest : List H) {root : H}
    (hne : sib ≠ sib')
    (hv : verifyInclusion HS lh i n (sib :: rest) root = true) :
    verifyInclusion HS lh i n (sib' :: rest) root = false := by
  have hrec := (verifyInclusion_iff_recomputeRoot HS lh i n (sib :: rest) root).mp hv
  rw [recomputeRoot_cons_left HS lh i h2 hik] at hrec
  cases hL : recomputeRoot HS lh i (split n) rest with
  | none => rw [hL] at hrec; simp at hrec
  | some L =>
    rw [hL] at hrec
    simp only [Option.map_some', Option.some.injEq] at hrec
    cases hx : verifyInclusion HS lh i n (sib' :: rest) root with
    | false => rfl
    | true =>
      have h2' := (verifyInclusion_iff_recomputeRoot HS lh i n (sib' :: rest) root).mp hx
      rw [recomputeRoot_cons_left HS lh i h2 hik, hL] at h2'
      simp only [Option.map_some', Option.some.injEq] at h2'
      have hsib : HS.hnode L sib = HS.hnode L sib' := by rw [hrec, h2']
      exact absurd (HS.hnode_inj hsib).2 hne

/-! ### The specification computes the genuine RFC 6962 tree head -/

/-- Grounding: on the honest audit path for the genuine `i`-th leaf, the
independent specification reconstructs the real RFC 6962 Merkle tree head
`mth HS xs` — the specification is not merely internally consistent, it computes
the value RFC 6962 section 2.1 mandates. -/
theorem recomputeRoot_auditPath (HS : HashScheme Leaf H)
    {xs : List Leaf} {i : Nat} {y : Leaf} (hy : xs[i]? = some y) :
    recomputeRoot HS (HS.hleaf y) i xs.length (auditPath HS xs i) = some (mth HS xs) := by
  rw [← rootFromPath_eq_recomputeRoot HS (HS.hleaf y) xs.length i (auditPath HS xs i)]
  exact inclusion_complete HS xs.length xs i y rfl hy

end Ct
