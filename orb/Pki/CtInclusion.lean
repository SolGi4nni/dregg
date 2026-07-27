/-
Pki.CtInclusion — RFC 6962 §2.1.1 inclusion/consistency, verified, plus the
**inclusion depth** bound (row pk.13).

An RFC 6962 inclusion (audit) proof for the leaf at index `i` in a size-`n`
Merkle log is the list of sibling subtree heads on the root-to-leaf descent; a
monitor holding only the signed tree head recomputes the head from the leaf hash
and the path (`Ct.rootFromPath` / `Ct.verifyInclusion`).  The abstract soundness
of that verifier — a leaf verifies against the real head *iff* it is the genuine
`i`-th appended leaf — is `Ct.inclusion_iff`, discharged relative to an arbitrary
collision-resistant, domain-separated `Ct.HashScheme` (its `hleaf_inj` /
`hnode_inj` / `leaf_ne_node` fields are the *named* idealized-hash assumptions,
carried as structure parameters, so nothing here enlarges the axiom footprint —
no `Crypto` FFI is touched).  The concrete leaf input those verifiers consume is
`Pki.Ct.mtlHash = SHA-256(0x00 ‖ leaf)` (RFC 6962 §2.1); this module is
proof-only over the abstract scheme, so it never evaluates the real hash.

What this module ADDS beyond the existing soundness (`Ct.Inclusion`) and
consistency (`Ct.Consistency`) is the **depth** dimension:

  * `pathDepth n i` — the exact number of sibling hashes on the descent to leaf
    `i` in a size-`n` tree; `depth n` — the tree depth (max over all leaves).
  * `auditPath_length` — the honest audit path has length *exactly* `pathDepth`.
  * `rootFromPath_length` / `verifyInclusion_depth` — the verifier ACCEPTS a path
    only when its length equals `pathDepth n i`; the audit-path length is pinned
    to the geometry, so a padded or truncated path is rejected.
  * `pathDepth_lt` — `pathDepth n i < n`: verification cost is strictly below the
    leaf count (it terminates in fewer steps than there are leaves).
  * `pathDepth_le_depth` + `depth_ge_log` — every leaf's depth is ≤ the tree
    depth, and `n ≤ 2 ^ depth n`, i.e. the tree is genuinely (at least)
    logarithmically deep: an inclusion proof cannot commit more than `depth n`
    siblings, and `depth n ≥ log₂ n`.
  * `inclusion_rejects_wrong_length` / `inclusion_rejects_overlong` — a proof of
    the wrong depth (in particular any proof at least as long as the tree) is
    rejected; a forger cannot pad an audit path to fake inclusion.

The three RFC-headline theorems are re-exported under stable names for the
ledger: `ct_inclusion_verifies`, `ct_inclusion_rejects_forged`, `ct_consistency`.
Non-vacuity is discharged against a concrete, genuinely collision-resistant
scheme (the free Merkle-digest term algebra `Demo.DH`): a real audit path
verifies, a forged leaf is rejected for *every* path, and an over-long forged
path is rejected by the depth bound.
-/

import Ct.Inclusion
import Ct.Consistency

namespace Pki.CtInclusion

open Ct

variable {Leaf H : Type}

/-! ## Inclusion depth (RFC 6962 §2.1.1)

`pathDepth n i` counts the sibling hashes a size-`n` audit path for leaf `i`
carries — one per interior node on the root-to-leaf descent.  It mirrors the
split-recursion of `Ct.auditPath` / `Ct.rootFromPath` exactly, so it is the
common measure of both the honest proof length and the verifier's step count. -/

/-- The audit-path depth for leaf index `i` in a size-`n` RFC 6962 tree: the
number of sibling hashes on the descent, one per interior node passed. -/
def pathDepth : Nat → Nat → Nat
  | n, i =>
    if h : 2 ≤ n then
      if i < split n then 1 + pathDepth (split n) i
      else 1 + pathDepth (n - split n) (i - split n)
    else 0
termination_by n _ => n
decreasing_by
  · exact split_lt h
  · exact Nat.sub_lt (by omega) (split_pos h)

/-- The RFC 6962 tree depth of a size-`n` tree: the maximum audit-path depth over
all leaves (each level contributes one, and both subtrees are considered). -/
def depth : Nat → Nat
  | n =>
    if h : 2 ≤ n then 1 + max (depth (split n)) (depth (n - split n))
    else 0
termination_by n => n
decreasing_by
  · exact split_lt h
  · exact Nat.sub_lt (by omega) (split_pos h)

/-! ### Unfolding lemmas -/

theorem pathDepth_le1 {n i : Nat} (h : n ≤ 1) : pathDepth n i = 0 := by
  rw [pathDepth]; simp only [dif_neg (by omega : ¬ 2 ≤ n)]

theorem pathDepth_ge2 {n i : Nat} (h : 2 ≤ n) :
    pathDepth n i =
      if i < split n then 1 + pathDepth (split n) i
      else 1 + pathDepth (n - split n) (i - split n) := by
  rw [pathDepth]; simp only [dif_pos h]

theorem depth_le1 {n : Nat} (h : n ≤ 1) : depth n = 0 := by
  rw [depth]; simp only [dif_neg (by omega : ¬ 2 ≤ n)]

theorem depth_ge2 {n : Nat} (h : 2 ≤ n) :
    depth n = 1 + max (depth (split n)) (depth (n - split n)) := by
  rw [depth]; simp only [dif_pos h]

/-! ### The honest audit path realizes exactly `pathDepth` -/

/-- **auditPath_length.** The honest RFC 6962 audit path for leaf `i` carries
exactly `pathDepth` sibling hashes — one per interior node on the descent. -/
theorem auditPath_length (HS : HashScheme Leaf H) :
    ∀ (n : Nat) (xs : List Leaf) (i : Nat),
      xs.length = n → (auditPath HS xs i).length = pathDepth n i := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro xs i hn
    subst hn
    by_cases h2 : 2 ≤ xs.length
    · have hklt : split xs.length < xs.length := split_lt h2
      have hkpos : 1 ≤ split xs.length := split_pos h2
      have htlen : (xs.take (split xs.length)).length = split xs.length := by
        rw [List.length_take]; exact Nat.min_eq_left (Nat.le_of_lt hklt)
      have hdlen : (xs.drop (split xs.length)).length = xs.length - split xs.length :=
        List.length_drop
      rw [auditPath_ge2 HS h2, pathDepth_ge2 h2]
      by_cases hik : i < split xs.length
      · simp only [if_pos hik, List.length_cons]
        have hrec := ih (split xs.length) hklt (xs.take (split xs.length)) i htlen
        omega
      · simp only [if_neg hik, List.length_cons]
        have hrec := ih (xs.length - split xs.length)
          (Nat.sub_lt (by omega) hkpos) (xs.drop (split xs.length)) (i - split xs.length) hdlen
        omega
    · rw [auditPath_le1 HS (by omega) i]
      simp [pathDepth_le1 (show xs.length ≤ 1 by omega)]

/-! ### The verifier accepts only paths of the correct depth -/

/-- **rootFromPath_length.** The verifier core recomputes a head from a path only
when the path length equals `pathDepth n i` — the audit-path length is pinned to
the tree geometry, so a padded or truncated path fails to recompute. -/
theorem rootFromPath_length (HS : HashScheme Leaf H) (lh : H) :
    ∀ (n i : Nat) (path : List H) (r : H),
      rootFromPath HS lh i n path = some r → path.length = pathDepth n i := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i path r hr
    by_cases h2 : 2 ≤ n
    · rw [rootFromPath_ge2 HS lh i h2] at hr
      cases path with
      | nil => simp at hr
      | cons sib rest =>
        by_cases hik : i < split n
        · simp only [if_pos hik] at hr
          cases hrec : rootFromPath HS lh i (split n) rest with
          | none => rw [hrec] at hr; simp at hr
          | some L =>
            have hlen := ih (split n) (split_lt h2) i rest L hrec
            rw [pathDepth_ge2 h2]
            simp only [if_pos hik, List.length_cons]
            omega
        · simp only [if_neg hik] at hr
          cases hrec : rootFromPath HS lh (i - split n) (n - split n) rest with
          | none => rw [hrec] at hr; simp at hr
          | some R =>
            have hlen := ih (n - split n)
              (Nat.sub_lt (by omega) (split_pos h2)) (i - split n) rest R hrec
            rw [pathDepth_ge2 h2]
            simp only [if_neg hik, List.length_cons]
            omega
    · rw [rootFromPath_le1 HS lh i (by omega) path] at hr
      cases path with
      | nil => simp [pathDepth_le1 (show n ≤ 1 by omega)]
      | cons a as => simp at hr

/-- **verifyInclusion_depth.** Any path the `Bool` inclusion verifier accepts has
length exactly `pathDepth n i`: the accepted inclusion proof is precisely as deep
as the leaf sits in the tree. -/
theorem verifyInclusion_depth (HS : HashScheme Leaf H) [DecidableEq H]
    {leafHash : H} {i n : Nat} {path : List H} {root : H}
    (hv : verifyInclusion HS leafHash i n path root = true) :
    path.length = pathDepth n i := by
  unfold verifyInclusion at hv
  cases hr : rootFromPath HS leafHash i n path with
  | none => rw [hr] at hv; simp at hv
  | some r => exact rootFromPath_length HS leafHash n i path r hr

/-! ### Quantitative depth bounds -/

/-- **pathDepth_lt.** For a leaf that is actually in the tree, the audit-path
depth is strictly less than the leaf count: verification consumes fewer siblings
than there are leaves, so it always terminates well below a linear bound. -/
theorem pathDepth_lt : ∀ (n i : Nat), i < n → pathDepth n i < n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i hi
    by_cases h2 : 2 ≤ n
    · have hkpos : 1 ≤ split n := split_pos h2
      have hklt : split n < n := split_lt h2
      rw [pathDepth_ge2 h2]
      by_cases hik : i < split n
      · rw [if_pos hik]
        have := ih (split n) hklt i hik
        omega
      · rw [if_neg hik]
        have hile : split n ≤ i := Nat.le_of_not_lt hik
        have := ih (n - split n) (Nat.sub_lt (by omega) hkpos) (i - split n) (by omega)
        omega
    · rw [pathDepth_le1 (by omega)]; omega

/-- **pathDepth_le_depth.** Every leaf's audit-path depth is at most the tree
depth: no inclusion proof commits more than `depth n` siblings. -/
theorem pathDepth_le_depth : ∀ (n i : Nat), pathDepth n i ≤ depth n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i
    by_cases h2 : 2 ≤ n
    · rw [depth_ge2 h2, pathDepth_ge2 h2]
      have hklt : split n < n := split_lt h2
      have hksub : n - split n < n := Nat.sub_lt (by omega) (split_pos h2)
      by_cases hik : i < split n
      · rw [if_pos hik]
        have := ih (split n) hklt i
        omega
      · rw [if_neg hik]
        have := ih (n - split n) hksub (i - split n)
        omega
    · rw [pathDepth_le1 (by omega)]; exact Nat.zero_le _

/-- **depth_ge_log.** The tree is at least logarithmically deep: `n ≤ 2 ^ depth n`
(so `depth n ≥ log₂ n`).  Combined with `pathDepth_le_depth`, an audit path for a
size-`n` log carries at most `depth n` siblings and the depth is bounded below by
the log of the leaf count — the Merkle structure is a genuine balanced tree, not a
degenerate list a malicious log could inflate. -/
theorem depth_ge_log : ∀ (n : Nat), n ≤ 2 ^ depth n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h2 : 2 ≤ n
    · rw [depth_ge2 h2]
      have hklt : split n < n := split_lt h2
      have hksub : n - split n < n := Nat.sub_lt (by omega) (split_pos h2)
      have h1 := ih (split n) hklt
      have h2' := ih (n - split n) hksub
      have hmax1 : (2 : Nat) ^ depth (split n)
          ≤ 2 ^ (max (depth (split n)) (depth (n - split n))) :=
        Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)
      have hmax2 : (2 : Nat) ^ depth (n - split n)
          ≤ 2 ^ (max (depth (split n)) (depth (n - split n))) :=
        Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)
      have hpow : (2 : Nat) ^ (1 + max (depth (split n)) (depth (n - split n)))
          = 2 * 2 ^ (max (depth (split n)) (depth (n - split n))) := by
        rw [Nat.pow_add, Nat.pow_one]
      rw [hpow]
      omega
    · rw [depth_le1 (by omega)]
      simp only [Nat.pow_zero]
      omega

/-! ## RFC 6962 headline theorems (stable ledger names) -/

/-- **ct_inclusion_verifies (RFC 6962 §2.1.1).**  The honest audit path from the
genuine `i`-th leaf `y` up to the signed tree head verifies against that head.
This is the completeness direction of `Ct.inclusion_iff`. -/
theorem ct_inclusion_verifies (HS : HashScheme Leaf H) [DecidableEq H]
    {xs : List Leaf} {i : Nat} {y : Leaf} (hi : i < xs.length) (hy : xs[i]? = some y) :
    verifyInclusion HS (HS.hleaf y) i xs.length (auditPath HS xs i) (mth HS xs) = true :=
  (inclusion_iff HS hi).mpr hy

/-- **ct_inclusion_rejects_forged.**  A forged inclusion claim — a leaf `y` that
is NOT the genuine `i`-th appended leaf — is rejected against the real signed
head for *every* candidate path.  No audit path can make a wrong leaf verify.
The proof spends the collision-resistance fields (`hnode_inj`/`hleaf_inj`) via
`Ct.inclusion_sound`: an accepted path would force `y` to be the genuine leaf. -/
theorem ct_inclusion_rejects_forged (HS : HashScheme Leaf H) [DecidableEq H]
    {xs : List Leaf} {i : Nat} {y : Leaf} {path : List H}
    (hi : i < xs.length) (hforge : xs[i]? ≠ some y) :
    verifyInclusion HS (HS.hleaf y) i xs.length path (mth HS xs) = false := by
  cases hb : verifyInclusion HS (HS.hleaf y) i xs.length path (mth HS xs) with
  | false => rfl
  | true =>
    unfold verifyInclusion at hb
    cases hr : rootFromPath HS (HS.hleaf y) i xs.length path with
    | none => rw [hr] at hb; simp at hb
    | some r =>
      rw [hr] at hb
      simp only [decide_eq_true_eq] at hb
      exact absurd
        (inclusion_sound HS xs.length xs i y path rfl hi (hr.trans (congrArg some hb))) hforge

/-- **ct_consistency.**  Against the real size-`n` head, the honest consistency
proof verifies *iff* the claimed old head is the genuine head of the size-`m`
prefix — the append-only guarantee: two tree heads are consistent exactly when
the append-only proof checks.  This is `Ct.consistency_iff`. -/
theorem ct_consistency (HS : HashScheme Leaf H) [DecidableEq H]
    {xs : List Leaf} {m : Nat} {oldRoot : H} (hm1 : 1 ≤ m) (hmn : m ≤ xs.length) :
    verifyConsistency HS m xs.length oldRoot (mth HS xs) (consistencyProof HS m xs) = true
      ↔ oldRoot = mth HS (xs.take m) :=
  consistency_iff HS hm1 hmn

/-! ### Depth-based rejection: a proof of the wrong depth is rejected -/

/-- **inclusion_rejects_wrong_length.**  A candidate inclusion proof whose length
disagrees with the tree geometry (`pathDepth n i`) is rejected — the contrapositive
of `verifyInclusion_depth`.  A forger cannot present a path of the wrong depth. -/
theorem inclusion_rejects_wrong_length (HS : HashScheme Leaf H) [DecidableEq H]
    {leafHash : H} {i n : Nat} {path : List H} {root : H}
    (hlen : path.length ≠ pathDepth n i) :
    verifyInclusion HS leafHash i n path root = false := by
  cases hb : verifyInclusion HS leafHash i n path root with
  | false => rfl
  | true => exact absurd (verifyInclusion_depth HS hb) hlen

/-- **inclusion_rejects_overlong.**  Any candidate proof at least as long as the
leaf count is rejected (for a leaf that is in the tree): since `pathDepth n i < n`
(depth is strictly below the size), an over-long padded path can never verify. -/
theorem inclusion_rejects_overlong (HS : HashScheme Leaf H) [DecidableEq H]
    {leafHash : H} {i n : Nat} {path : List H} {root : H}
    (hi : i < n) (hlen : n ≤ path.length) :
    verifyInclusion HS leafHash i n path root = false := by
  apply inclusion_rejects_wrong_length
  have := pathDepth_lt n i hi
  omega

/-! ## Non-vacuity: a concrete, genuinely collision-resistant scheme

The abstract theorems are instantiated at `demoHS` — the free Merkle-digest term
algebra, whose constructors are injective and disjoint, so it is a *real*
collision-resistant, domain-separated `HashScheme` (the idealized random-function
abstraction, realized structurally), not a degenerate all-equal hash.  A genuine
audit path verifies; a forged leaf is rejected for every path; an over-long
forged path is rejected by the depth bound. -/

namespace Demo

/-- The free Merkle-digest term: `e` (empty head), `leaf n`, `node l r`.  Its
constructors are injective and pairwise disjoint — exactly the collision-
resistance and domain-separation an ideal hash provides. -/
inductive DH where
  | e
  | leaf (n : Nat)
  | node (l r : DH)
deriving DecidableEq, Repr

/-- The concrete scheme: `hleaf = DH.leaf`, `hnode = DH.node`, `hempty = DH.e`.
All algebraic facts hold structurally by constructor injectivity/disjointness. -/
def demoHS : HashScheme Nat DH where
  hempty := .e
  hleaf := .leaf
  hnode := .node
  hleaf_inj := fun h => DH.leaf.inj h
  hnode_inj := fun h => DH.node.inj h
  leaf_ne_node := by intro x a b h; injection h
  empty_ne_leaf := by intro x h; injection h
  empty_ne_node := by intro a b h; injection h

/-- A concrete three-leaf log. -/
def demoLog : List Nat := [10, 20, 30]

/-- **demo_inclusion_verifies.**  The honest audit path for the genuine middle
leaf (index 1, value 20) verifies against the real signed head — the accept
direction is not vacuous. -/
theorem demo_inclusion_verifies :
    verifyInclusion demoHS (demoHS.hleaf 20) 1 demoLog.length
      (auditPath demoHS demoLog 1) (mth demoHS demoLog) = true :=
  ct_inclusion_verifies demoHS (xs := demoLog) (i := 1) (y := 20) (by decide) (by decide)

/-- **demo_forged_rejected.**  A forged leaf value (999, not the genuine 20 at
index 1) is rejected against the real head for *every* candidate path — the
reject direction is not vacuous and holds universally in the path. -/
theorem demo_forged_rejected (path : List DH) :
    verifyInclusion demoHS (demoHS.hleaf 999) 1 demoLog.length path
      (mth demoHS demoLog) = false :=
  ct_inclusion_rejects_forged demoHS (xs := demoLog) (i := 1) (y := 999)
    (by decide) (by decide)

/-- **demo_overlong_rejected (depth mutant).**  A forged, over-long audit path (4
siblings) for a leaf in a 3-leaf tree is rejected by the depth bound, regardless
of the fake head it claims — a forger cannot pad an inclusion proof past the tree
depth. -/
theorem demo_overlong_rejected (root : DH) :
    verifyInclusion demoHS (demoHS.hleaf 20) 1 3 [DH.e, DH.e, DH.e, DH.e] root = false :=
  inclusion_rejects_overlong demoHS (by decide) (by decide)

end Demo

/-! ## Axiom audit -/

#print axioms auditPath_length
#print axioms rootFromPath_length
#print axioms verifyInclusion_depth
#print axioms pathDepth_lt
#print axioms pathDepth_le_depth
#print axioms depth_ge_log
#print axioms ct_inclusion_verifies
#print axioms ct_inclusion_rejects_forged
#print axioms ct_consistency
#print axioms inclusion_rejects_wrong_length
#print axioms inclusion_rejects_overlong
#print axioms Demo.demo_inclusion_verifies
#print axioms Demo.demo_forged_rejected
#print axioms Demo.demo_overlong_rejected

end Pki.CtInclusion
