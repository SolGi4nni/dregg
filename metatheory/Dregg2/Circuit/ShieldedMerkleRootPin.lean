/-
# Dregg2.Circuit.ShieldedMerkleRootPin — the shielded membership root is WIRE-SUPPLIED, not pinned
  to the committed accumulator (WOUND #15, the shielded-pool THEFT vector).

**What this proves, and why it was missing.** The deployed shielded transfer
(`turn/src/executor/apply.rs :: apply_shielded_transfer`) reconstructs the membership tree from a
PROVER-SUPPLIED root and checks membership against **that** root:

  * `ShieldedTransfer::from_serialized_parts(payload.merkle_root, …)` (`apply.rs:1738`) —
    the root is a wire field of the transfer payload;
  * `verify_stark_with_wide_bindings(&transfer, …)` (`apply.rs:1753`) proves each input note is a
    member of the tree at `payload.merkle_root` — the shielded-spend uni-STARK
    (`circuit-prove/src/shielded/spend_circuit.rs`) folds `parent = hash_fact(current,[sib0,sib1,sib2,pos])`
    up the 4-ary path and pins the last row's `current` to the `merkle_root` PI
    (`transfer.rs:91` `public_inputs`, `pis[MERKLE_ROOT] = merkle_root`);
  * **nowhere** is `payload.merkle_root` compared to any COMMITTED accumulator root — the state
    commitment binds the executor's live `commitments_root : Faithful8`
    (`turn/src/state_commit.rs:117`, `CommitmentSet::root8()`), but the shielded spend never consults it.

So a malicious prover picks a root of THEIR choosing, builds a tree containing any leaf they like
(a note that was never created), and honestly proves membership in *that* tree. The membership STARK
is perfectly sound — it just proves membership in the ATTACKER's tree. Result: **spend a note that was
never committed → theft / inflation.** As the decision brief puts it
(`docs/DECISION-shielded-redesign-2026-07-20.md` #15) this is *"larger than any felt-width birthday
collision; the ~31-bit width is the entry point, not the wound."*

**Where the metatheory was blind.** `Dregg2.Circuit.ShieldedTransferStark.StarkResidual` states the
deployed STARK's obligation as `∃ …, member (H [value, asset, owner, randomness]) pi.merkleRoot ∧ …`
— membership against `pi.merkleRoot`, the WIRE root — and its §5 "full floor list" names StarkSound,
Pedersen/Bulletproofs, blake3-CR, the C6↔C7a one-opening tie, and the value-link (#16) as the open
residual. The `merkleRoot = committedRoot` PIN is **absent from that list**: the abstract
`member … pi.merkleRoot` silently assumes `pi.merkleRoot` is the right root. This module supplies
exactly the invariant that assumption papers over. (That residual carried a SECOND blindness of the
same family — its value witness was tied to nothing, `Verify.ExistsImageVacuity` §5 — repaired
2026-07-24 by the tie now quoted above; the pin remains this module's business.)

**What is proved here** (theorems over ALL inputs; the model is faithful to the fold, HASH-AGNOSTIC —
it uses no property of the per-level hash beyond determinism, so it holds for the real Poseidon2):

  * **THE FALSIFIER (`root_substitution_forges`, `deployed_admits_but_pin_rejects`).** The deployed
    accept predicate — membership against the SUPPLIED root, with no committed-root conjunct — admits
    a payload whose supplied root is `≠` the committed root; the accepted leaf need not be a committed
    note (`¬ IsCommitted`), so a forged / double-spend note passes.
  * **THE LAUNDER, exposed (`mutation_breaks_membership` vs `mutation_test_is_not_the_pin`).** The
    Rust `forged_membership_root_rejects` test (`apply.rs:5174`) MUTATES an accepted payload's root
    (`payload.merkle_root += 1`) WITHOUT re-proving and observes the STARK now fails. That is real — but
    it only rejects root-mutation-without-reproof, NOT an attacker who PROVES against a chosen root.
    The theft survives it; the mutation test is not the pin.
  * **THE FIX, sound (`pinned_membership_against_committed`, `pinned_accept_is_committed`,
    `pin_rejects_root_substitution`).** Adding the conjunct `payload.merkle_root = committedRoot`
    forces membership against the COMMITTED root, so (a) the accepted leaf IS in the committed tree,
    and (b) under the accumulator's own soundness the accepted leaf is a genuinely committed note —
    and the attacker-tree forgery is REJECTED, over all inputs.

**Byte-safe / posture.** This module does NOT touch deployed code. The Rust root-pin check and the
in-AIR fold that would close #15 are the *approved Option-A redesign*
(`docs/DECISION-shielded-redesign-2026-07-20.md` + `PLAN-shielded-apex-redesign-2026-07-20.md`,
route the transfer through `shielded_ring_clearing_nleg_air` as a 1-leg ring) — the gated deploy,
NOT this file. This is the machine-checked statement of the invariant that redesign must establish:
the falsifier that prices the open wound and the soundness the pin buys.

**Scope (honest).** This is the FIRST brick of the `spend_circuit → Lean` campaign — the merkle-root
theft falsifier and the pin's soundness, at the resolution of the membership-root trust boundary
(NOT the full AIR). The accumulator's own soundness (a membership witness against the committed root
certifies a real note) is taken as the abstract hypothesis `AccumulatorSound`, exactly as
`FinalityCertWidth` takes `SigValid` — its discharge is the full `spend_circuit` AIR port; folding
`verify_value_link` (#16) into the AIR and the PQ-commitment (#17) are the rest of the campaign.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake build Dregg2.Circuit.ShieldedMerkleRootPin`.
-/
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Dregg2.Tactics

set_option autoImplicit false

namespace Dregg2.Circuit.ShieldedMerkleRootPin

/-! ## 1. Felt, the 4-ary Merkle level, and the membership fold.

Faithful to `spend_circuit.rs`: one row per level, `parent = hash_fact(current,[sib0,sib1,sib2,pos])`,
chained `next.current == local.parent`, the leaf IS the input note commitment (no preimage row), and
the last row's `current` is pinned to `merkle_root`. The per-level hash is ABSTRACT (`H`) — the
theorems use nothing but its determinism, so they hold for the real Poseidon2 `hash_fact`. -/

/-- One field element, modeled by its canonical value (as in `FinalityCertWidth`); the BabyBear range
prices the offline grind but is irrelevant to the root-binding gap, so a lane is an integer. -/
abbrev Felt : Type := ℤ

/-- One Merkle level: the three siblings + the position selector — faithful to the hash input
`hash_fact(current, [sib0, sib1, sib2, position])`. -/
structure Level where
  sib0 : Felt
  sib1 : Felt
  sib2 : Felt
  pos  : Felt
deriving DecidableEq, Repr

/-- Fold a leaf up its path to a root: each level replaces `current` with the parent hash
`H current lvl`, chained to the next row; the empty path returns the leaf (a depth-0 tree whose leaf
IS the root). The final value is what the circuit pins to `merkle_root`. -/
def foldPath (H : Felt → Level → Felt) (leaf : Felt) : List Level → Felt
  | []          => leaf
  | lvl :: rest => foldPath H (H leaf lvl) rest

/-- **Membership** (what the shielded-spend STARK proves): `leaf` hashes up `path` to the SUPPLIED
root. The circuit checks this against whatever root it is handed — that is the whole point. -/
def membershipVerifies (H : Felt → Level → Felt) (leaf : Felt) (path : List Level)
    (suppliedRoot : Felt) : Prop :=
  foldPath H leaf path = suppliedRoot

/-- The wire payload the executor reconstructs (`from_serialized_parts(payload.merkle_root, …)`):
the revealed note commitment (`leaf`), the hidden path, and the PROVER-SUPPLIED `merkle_root`. -/
structure Payload where
  leaf         : Felt
  path         : List Level
  suppliedRoot : Felt

/-- A leaf is `inCommittedTree` at `committedRoot` iff SOME path folds it up to that root — the
faithful realization of the abstract `member commitment root` predicate
`ShieldedTransferStark.StarkResidual` leaves unpinned. -/
def inCommittedTree (H : Felt → Level → Felt) (leaf committedRoot : Felt) : Prop :=
  ∃ path : List Level, foldPath H leaf path = committedRoot

/-! ## 2. The DEPLOYED accept predicate — membership against the SUPPLIED root, root UNPINNED.

Faithful to `apply_shielded_transfer` at HEAD: `committedRoot` is passed (it is the live
`commitments_root` the state commitment binds) but the predicate never consults it — the wound in a
signature. -/

/-- The deployed accept, HEAD-faithful: verify membership against `p.suppliedRoot` (`payload.merkle_root`)
and NOTHING about `committedRoot`. The `_committedRoot` binder is ignored ON PURPOSE — that ignoring
IS the wound. -/
def accepts (H : Felt → Level → Felt) (_committedRoot : Felt) (p : Payload) : Prop :=
  membershipVerifies H p.leaf p.path p.suppliedRoot

/-- The SOUND accept: membership PLUS the pin `payload.merkle_root = committedRoot`. This is what the
Option-A redesign establishes (`merkle_root` connected to the committed turn root, in-AIR). Defined
here (before the falsifier) so the theft theorem can name the predicate that rejects it. -/
def acceptsPinned (H : Felt → Level → Felt) (committedRoot : Felt) (p : Payload) : Prop :=
  membershipVerifies H p.leaf p.path p.suppliedRoot ∧ p.suppliedRoot = committedRoot

/-- **`accepts_independent_of_committedRoot` (the wound in one line).** The deployed predicate gives
the SAME verdict for every committed root — it does not look at the committed accumulator at all. So
whatever the real committed root is, an attacker-chosen `suppliedRoot` is judged on its own. -/
theorem accepts_independent_of_committedRoot (H : Felt → Level → Felt) (r₁ r₂ : Felt) (p : Payload) :
    accepts H r₁ p ↔ accepts H r₂ p := Iff.rfl

/-- **`pin_rejects_root_substitution` (the pin bites, directly).** Any payload whose supplied root
differs from the committed root is REJECTED by the pinned predicate — no root substitution survives. -/
theorem pin_rejects_root_substitution (H : Felt → Level → Felt) (committedRoot : Felt) (p : Payload)
    (hne : p.suppliedRoot ≠ committedRoot) : ¬ acceptsPinned H committedRoot p := by
  intro h; exact hne h.2

/-! ## 3. THE FALSIFIER — the deployed accept admits a substituted (attacker) root.

The attacker builds their OWN tree (any leaf, any siblings), computes its root by folding, and
supplies `(leaf, path, thatRoot)`. Membership holds by construction; the supplied root is `≠` the
committed root. Hash-agnostic: true for the real Poseidon2 whatever it is. -/

/-- **`root_substitution_forges` (THE FALSIFIER).** For every hash `H` there is a committed root, a
distinct attacker root, a leaf and a path such that the deployed predicate ACCEPTS the transfer while
the supplied (attacker) root differs from the committed one. The witness uses a genuine one-level path
(the attacker's own tree), not a degenerate empty tree. -/
theorem root_substitution_forges (H : Felt → Level → Felt) :
    ∃ (committedRoot attackerRoot leaf : Felt) (path : List Level),
      attackerRoot ≠ committedRoot ∧
      accepts H committedRoot ⟨leaf, path, attackerRoot⟩ := by
  refine ⟨H 0 ⟨0, 0, 0, 0⟩ + 1, H 0 ⟨0, 0, 0, 0⟩, 0, [⟨0, 0, 0, 0⟩], ?_, ?_⟩
  · simp
  · show foldPath H 0 [⟨0, 0, 0, 0⟩] = H 0 ⟨0, 0, 0, 0⟩
    rfl

/-- **`deployed_admits_but_pin_rejects` (THE FALSIFIER, theft form — the whole shape at once).** Given
ANY leaf the attacker never had created (`¬ IsCommitted forgedLeaf`) and any level, there is a
committed root and a payload that:
  * carries the forged (uncommitted) leaf,
  * is ACCEPTED by the deployed predicate (membership in the attacker's own tree),
  * whose supplied root DIFFERS from the committed root (so the pin would bite),
  * and is REJECTED by the pinned predicate.
That is the theft: a note that was never committed is spent, and only the missing pin would stop it. -/
theorem deployed_admits_but_pin_rejects
    (H : Felt → Level → Felt) (IsCommitted : Felt → Prop) (forgedLeaf : Felt) (lvl : Level)
    (notReal : ¬ IsCommitted forgedLeaf) :
    ∃ (committedRoot : Felt) (p : Payload),
      p.leaf = forgedLeaf ∧
      ¬ IsCommitted p.leaf ∧
      accepts H committedRoot p ∧
      p.suppliedRoot ≠ committedRoot ∧
      ¬ acceptsPinned H committedRoot p := by
  refine ⟨H forgedLeaf lvl + 1, ⟨forgedLeaf, [lvl], H forgedLeaf lvl⟩, rfl, notReal, ?_, ?_, ?_⟩
  · show foldPath H forgedLeaf [lvl] = H forgedLeaf lvl
    rfl
  · show H forgedLeaf lvl ≠ H forgedLeaf lvl + 1
    simp
  · exact pin_rejects_root_substitution H (H forgedLeaf lvl + 1) _
      (by show H forgedLeaf lvl ≠ H forgedLeaf lvl + 1; simp)

/-! ## 4. THE LAUNDER, exposed — the `forged_membership_root_rejects` test is not the pin.

The Rust reject-test (`apply.rs:5174`) does `payload.merkle_root = payload.merkle_root.wrapping_add(1)`
on an already-built payload and observes the STARK fail. It rejects root-MUTATION-without-reproof. It
does not reject an attacker who PROVES against a chosen root. -/

/-- `mutateRoot p` — bump the supplied root by one WITHOUT re-proving (the Rust test's mutation). -/
def mutateRoot (p : Payload) : Payload := { p with suppliedRoot := p.suppliedRoot + 1 }

/-- **`mutation_breaks_membership` (the test is REAL).** If `p` verified, then `mutateRoot p` does
NOT: the fold is unchanged (leaf and path are untouched) but the pinned target moved by one, so the
membership equation now fails. This is exactly what `forged_membership_root_rejects` observes. -/
theorem mutation_breaks_membership (H : Felt → Level → Felt) (p : Payload)
    (h : membershipVerifies H p.leaf p.path p.suppliedRoot) :
    ¬ membershipVerifies H (mutateRoot p).leaf (mutateRoot p).path (mutateRoot p).suppliedRoot := by
  simp only [membershipVerifies, mutateRoot] at h ⊢
  rw [h]; simp

/-- **`mutation_test_is_not_the_pin` (the LAUNDER, exposed).** The mutation test rejecting a bumped
root does NOT close the theft: the attacker never mutates a fixed payload — they PROVE membership
against their own chosen root, and the deployed predicate STILL accepts the forgery while the pinned
predicate rejects it. The mutation test and the pin are different teeth; only the pin bites the theft. -/
theorem mutation_test_is_not_the_pin
    (H : Felt → Level → Felt) (IsCommitted : Felt → Prop) (forgedLeaf : Felt) (lvl : Level)
    (notReal : ¬ IsCommitted forgedLeaf) :
    ∃ (committedRoot : Felt) (p : Payload),
      accepts H committedRoot p ∧ ¬ IsCommitted p.leaf ∧
      p.suppliedRoot ≠ committedRoot ∧ ¬ acceptsPinned H committedRoot p := by
  obtain ⟨committedRoot, p, _, hnr, hacc, hne, hpin⟩ :=
    deployed_admits_but_pin_rejects H IsCommitted forgedLeaf lvl notReal
  exact ⟨committedRoot, p, hacc, hnr, hne, hpin⟩

/-! ## 5. THE FIX, sound — pin the supplied root to the committed accumulator root.

The single missing conjunct closes it: membership against the COMMITTED root (`acceptsPinned`, §2). -/

/-- **`pinned_membership_against_committed` (the fix, PURE).** The pin forces membership against the
COMMITTED root: an accepted leaf IS in the committed tree, witnessed by its own path. No floor —
substitution of the pin into the membership equation. This is precisely the `member commitment
committedRoot` that `ShieldedTransferStark.StarkResidual` states against the UNPINNED `pi.merkleRoot`. -/
theorem pinned_membership_against_committed (H : Felt → Level → Felt) (committedRoot : Felt)
    (p : Payload) (h : acceptsPinned H committedRoot p) :
    inCommittedTree H p.leaf committedRoot := by
  obtain ⟨hmem, hpin⟩ := h
  refine ⟨p.path, ?_⟩
  simp only [membershipVerifies] at hmem
  rw [hmem, hpin]

/-- The accumulator's INTENDED soundness — a leaf that verifies against the COMMITTED root is a
genuinely committed note. ABSTRACT here (its discharge is the full `spend_circuit` AIR port + the
committed-accumulator wiring — the campaign residual), used exactly as `FinalityCertWidth` uses
`SigValid`. NAMING IS FAKING, so it is a hypothesis, never a `def`-used-as-proof. -/
def AccumulatorSound (H : Felt → Level → Felt) (IsCommitted : Felt → Prop) (committedRoot : Felt) : Prop :=
  ∀ leaf path, foldPath H leaf path = committedRoot → IsCommitted leaf

/-- **`pinned_accept_is_committed` (the fix, soundness form).** Under the accumulator's own soundness,
the pinned predicate admits ONLY genuinely committed notes: an accepted leaf is committed. So the
attacker-tree forgery — whose leaf is `¬ IsCommitted` — cannot pass the pinned gate. The theft closes. -/
theorem pinned_accept_is_committed
    (H : Felt → Level → Felt) (IsCommitted : Felt → Prop) (committedRoot : Felt) (p : Payload)
    (sound : AccumulatorSound H IsCommitted committedRoot)
    (h : acceptsPinned H committedRoot p) : IsCommitted p.leaf := by
  obtain ⟨path, hpath⟩ := pinned_membership_against_committed H committedRoot p h
  exact sound p.leaf path hpath

/-- **`pin_closes_the_falsifier` (the two halves meet).** The very forgery the deployed predicate
admits (`deployed_admits_but_pin_rejects`) is (a) rejected by the pinned predicate directly (root
mismatch), and (b) under the accumulator's own soundness could NEVER be pinned-accepted, because the
pin would force the leaf to be a committed note — which it is not. The missing conjunct is exactly
the wound; (b) is the deeper reason the pin closes the theft. -/
theorem pin_closes_the_falsifier
    (H : Felt → Level → Felt) (IsCommitted : Felt → Prop) (forgedLeaf : Felt) (lvl : Level)
    (notReal : ¬ IsCommitted forgedLeaf) :
    ∃ (committedRoot : Felt) (p : Payload),
      p.leaf = forgedLeaf ∧
      accepts H committedRoot p ∧
      ¬ acceptsPinned H committedRoot p ∧
      (AccumulatorSound H IsCommitted committedRoot → acceptsPinned H committedRoot p → False) := by
  obtain ⟨committedRoot, p, hleaf, hnr, hacc, _, hpin⟩ :=
    deployed_admits_but_pin_rejects H IsCommitted forgedLeaf lvl notReal
  refine ⟨committedRoot, p, hleaf, hacc, hpin, ?_⟩
  intro sound hp
  exact hnr (pinned_accept_is_committed H IsCommitted committedRoot p sound hp)

/-! ## 6. NON-VACUITY — the falsifier and the fix FIRE on a concrete tree (executable witnesses).

A false `#guard` is a build error. `Hdemo` is a concrete deterministic stand-in for `hash_fact` (its
only USED property, as in the theorems, is determinism); the guards check that the forged leaf really
folds up an attacker path to an attacker root, that root differs from a distinct committed root, and
that a two-level chain folds as claimed. -/

/-- A concrete deterministic per-level hash (stand-in for Poseidon2 `hash_fact`). -/
def Hdemo (current : Felt) (lvl : Level) : Felt :=
  current * 4 + lvl.sib0 + lvl.sib1 + lvl.sib2 + lvl.pos + 1

/-- A concrete level and a forged leaf (a note the attacker never had created). -/
def lvlDemo : Level := ⟨2, 3, 5, 0⟩
def forgedDemo : Felt := 99

-- The forged leaf folds up the attacker's one-level path to the attacker root (real membership proof):
-- Hdemo 99 lvlDemo = 99*4 + 2+3+5+0 + 1 = 407.
#guard decide (foldPath Hdemo forgedDemo [lvlDemo] = 407) = true
-- Membership against the SUPPLIED (attacker) root holds — the deployed predicate accepts.
#guard decide (foldPath Hdemo forgedDemo [lvlDemo] = Hdemo forgedDemo lvlDemo) = true
-- … but the supplied root DIFFERS from a distinct committed root (attackerRoot + 1): the pin bites,
--   and membership against THAT committed root fails.
#guard decide (foldPath Hdemo forgedDemo [lvlDemo] = Hdemo forgedDemo lvlDemo + 1) = false
-- A genuine two-level chain folds as claimed: Hdemo 407 lvlDemo = 407*4 + 10 + 1 = 1639.
#guard decide (foldPath Hdemo forgedDemo [lvlDemo, lvlDemo] = 1639) = true

/-! ## 7. Axiom hygiene. -/

#assert_axioms accepts_independent_of_committedRoot
#assert_axioms root_substitution_forges
#assert_axioms deployed_admits_but_pin_rejects
#assert_axioms mutation_breaks_membership
#assert_axioms mutation_test_is_not_the_pin
#assert_axioms pin_rejects_root_substitution
#assert_axioms pinned_membership_against_committed
#assert_axioms pinned_accept_is_committed
#assert_axioms pin_closes_the_falsifier

end Dregg2.Circuit.ShieldedMerkleRootPin
