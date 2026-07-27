/-
Pki.CtConsistency — RFC 6962 §2.1.2 consistency proofs, the append-only guarantee
(ledger row pk.ct2), stated at the level a monitor actually uses: two published
tree heads.

A monitor that once accepted the signed head of a size-`m` log, and later sees
the signed head of a size-`n` log (`n ≥ m`), verifies a *consistency proof* to
convince itself the new log did not rewrite history — the first `m` entries are
unchanged and the size-`n` log is the size-`m` log with fresh entries appended on
the right (RFC 6962 §2.1.2).  This module packages the substrate's
`Ct.consistency_iff` / `Ct.consistency_sound` into the two ledger-headline
statements:

  * `ct_consistency_verifies` — the *append-only* direction stated on two genuine
    logs: whenever the new log is literally the old log with `extra` appended
    (`new = old ++ extra`), the honest consistency proof verifies against the two
    real heads.  "Old entries unchanged" is encoded structurally: the old log is
    the syntactic prefix of the new one, and the proof for that pair checks.
  * `ct_consistency_rejects_forked` — the *soundness* / anti-fork direction,
    universally over the transmitted proof: if the claimed old head disagrees
    with the genuine head of the new log's size-`m` prefix (a forked / rewritten
    history), then NO proof makes the verifier accept against the real new head.

The hash is an opaque, collision-resistant, domain-separated oracle: an arbitrary
`Ct.HashScheme` whose `hnode_inj` / `hleaf_inj` / `leaf_ne_node` fields are the
*named* idealized-hash assumptions carried as a structure parameter.  Nothing here
enlarges the axiom footprint and no hash is ever evaluated on real bytes — the
anti-fork proof spends `hnode_inj` (via `Ct.consistency_sound`), it does not
invent a concrete hash.

Non-vacuity is discharged against `Demo.demoHS`, the free Merkle-digest term
algebra (injective, disjoint constructors — a genuine collision-resistant scheme):
a real append verifies, and a forked old head — one that changes an early entry —
is rejected for *every* candidate proof.
-/
import Ct.Consistency

namespace Pki.CtConsistency

open Ct

variable {Leaf H : Type}

/-! ## The two RFC 6962 §2.1.2 headline theorems (stable ledger names) -/

/-- **ct_consistency_verifies (RFC 6962 §2.1.2 — append-only).**  When the size-`n`
log is genuinely the size-`m` log `old` with `extra` appended on the right
(`new = old ++ extra`, so the old entries are literally unchanged as the prefix),
the honest consistency proof for that `(m, n)` pair verifies against the two real
tree heads `mth old` and `mth new`.  This is the completeness direction of
`Ct.consistency_iff` re-stated on two concrete logs, so the append-only invariant
("old entries unchanged" = old is the syntactic prefix) is visible in the
statement rather than hidden behind a `take`. -/
theorem ct_consistency_verifies (HS : HashScheme Leaf H) [DecidableEq H]
    {old extra : List Leaf} (hm1 : 1 ≤ old.length) :
    verifyConsistency HS old.length (old ++ extra).length
        (mth HS old) (mth HS (old ++ extra))
        (consistencyProof HS old.length (old ++ extra)) = true := by
  have hpre : (old ++ extra).take old.length = old := by
    rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
  have hmn : old.length ≤ (old ++ extra).length := by
    rw [List.length_append]; omega
  have h := consistency_complete HS (xs := old ++ extra) (m := old.length) hm1 hmn
  rw [hpre] at h
  exact h

/-- **ct_consistency_rejects_forked (RFC 6962 §2.1.2 — anti-fork / soundness).**  If
the claimed old head `oldRoot` disagrees with the genuine head of the size-`m`
prefix of the real size-`n` log `xs` — i.e. the prover asserts a *forked* past
that changed an early entry — then the verifier rejects it against the real new
head `mth xs` for *every* transmitted proof.  No consistency proof can launder a
rewritten history.  The proof spends the collision-resistance field `hnode_inj`
through `Ct.consistency_sound`: an accepted proof would force `oldRoot` to be the
genuine prefix head, contradicting the fork. -/
theorem ct_consistency_rejects_forked (HS : HashScheme Leaf H) [DecidableEq H]
    {xs : List Leaf} {m : Nat} {oldRoot : H} {proof : List H}
    (hm1 : 1 ≤ m) (hfork : oldRoot ≠ mth HS (xs.take m)) :
    verifyConsistency HS m xs.length oldRoot (mth HS xs) proof = false := by
  cases hb : verifyConsistency HS m xs.length oldRoot (mth HS xs) proof with
  | false => rfl
  | true => exact absurd (consistency_sound HS rfl hm1 hb) hfork

/-! ## Non-vacuity: a concrete, genuinely collision-resistant scheme

`Demo.demoHS` is the free Merkle-digest term algebra: constructors injective and
pairwise disjoint, i.e. a real collision-resistant, domain-separated hash (the
idealized random-function abstraction, realized structurally), not a degenerate
all-equal hash.  A genuine append verifies; a forked old head is rejected for
every proof. -/

namespace Demo

/-- The free Merkle-digest term: `e` (empty head), `leaf n`, `node l r`.  Its
constructors are injective and pairwise disjoint — exactly the collision-
resistance and domain-separation an ideal hash provides. -/
inductive DH where
  | e
  | leaf (n : Nat)
  | node (l r : DH)
deriving DecidableEq, Repr

/-- The concrete scheme; all algebraic facts hold by constructor
injectivity/disjointness. -/
def demoHS : HashScheme Nat DH where
  hempty := .e
  hleaf := .leaf
  hnode := .node
  hleaf_inj := fun h => DH.leaf.inj h
  hnode_inj := fun h => DH.node.inj h
  leaf_ne_node := by intro x a b h; injection h
  empty_ne_leaf := by intro x h; injection h
  empty_ne_node := by intro a b h; injection h

/-- The genuine old log (size 2) and the appended entries. -/
def demoOld : List Nat := [10, 20]
def demoExtra : List Nat := [30]
/-- The genuine new log = `demoOld ++ demoExtra` (size 3). -/
def demoNew : List Nat := [10, 20, 30]

/-- `split 2 = 1`: the RFC split point of a two-leaf tree. -/
theorem split_two : Ct.split 2 = 1 := by
  simp only [Ct.split]; rw [Ct.highBit]; decide

/-- The head of a two-leaf log is the node over the two leaf hashes.  Proved via
the unfolding lemmas, so the free-algebra head is a concrete `DH.node` term that
`decide` can compare — no well-founded `mth` reduction is required. -/
theorem mth_pair (a b : Nat) :
    mth demoHS [a, b] = DH.node (DH.leaf a) (DH.leaf b) := by
  rw [mth_split demoHS (xs := [a, b]) (Nat.le_refl 2)]
  have hlen : ([a, b] : List Nat).length = 2 := rfl
  rw [hlen, split_two]
  simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
    mth_single]
  rfl

/-- **demo_consistency_verifies.**  The honest consistency proof for the genuine
append `demoOld ++ demoExtra` verifies against the two real heads — the accept
direction is not vacuous. -/
theorem demo_consistency_verifies :
    verifyConsistency demoHS demoOld.length (demoOld ++ demoExtra).length
        (mth demoHS demoOld) (mth demoHS (demoOld ++ demoExtra))
        (consistencyProof demoHS demoOld.length (demoOld ++ demoExtra)) = true :=
  ct_consistency_verifies demoHS (by decide)

/-- **demo_forked_rejected (the mutant).**  A forked old head that changed the
second entry (`[10, 99]` instead of the genuine `[10, 20]`) is rejected against
the real new head `mth demoNew` for *every* candidate proof — the anti-fork
direction is not vacuous and holds universally in the proof. -/
theorem demo_forked_rejected (proof : List DH) :
    verifyConsistency demoHS 2 demoNew.length
        (mth demoHS [10, 99]) (mth demoHS demoNew) proof = false := by
  apply ct_consistency_rejects_forked demoHS (m := 2) (by decide)
  rw [show demoNew.take 2 = [10, 20] from rfl, mth_pair 10 99, mth_pair 10 20]
  decide

end Demo

/-! ## Axiom audit (fully-qualified names) -/

#print axioms Pki.CtConsistency.ct_consistency_verifies
#print axioms Pki.CtConsistency.ct_consistency_rejects_forked
#print axioms Pki.CtConsistency.Demo.demo_consistency_verifies
#print axioms Pki.CtConsistency.Demo.demo_forked_rejected

end Pki.CtConsistency
