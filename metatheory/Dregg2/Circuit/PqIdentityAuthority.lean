/-
# Dregg2.Circuit.PqIdentityAuthority -- exact cell-owned PQ identity rotation

This is the semantic authority surface for `Effect::RotatePqIdentity`.

The runtime stores two values as the cell-owned PQ identity: an exact `u64`
epoch and a 32-byte commitment to the enrolled ML-DSA-65 public key.  The
effect is authorized by the OLD enrolled key, then the NEW key separately
proves possession.  This file states that transition without projecting a
256-bit object into one BabyBear felt (or into eight reduced `u32` felts).
Every 32-byte object uses the already-proved sixteen-`u16` codec from
`CommitmentTreeWide`; every epoch uses four canonical base-`2^16` limbs.

The ML-DSA verifier is deliberately outside the algebraic row.  Its result is
not represented by a prover-chosen `verified = 1` bit.  Instead
`CryptoBoundary` names the two predicates the proof/turn verifier must
discharge over the EXACT structured statement and exact 32-byte evidence
commitment carried by the row.  Until that composition is wired, the runtime
EffectVM refusal is required.
-/
import Dregg2.Circuit.CommitmentTreeWide
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Circuit.PqIdentityAuthority

open Dregg2.Circuit.CommitmentTreeWide

set_option autoImplicit false

/-! ## Exact carriers -/

/-- One canonical base-`2^16` epoch limb. -/
abbrev EpochLimb := Fin 65536

/-- Exact little-endian four-limb representation of a `u64` epoch. -/
abbrev Epoch4 := Fin 4 → EpochLimb

/-- Reconstruct the mathematical epoch value.  The result is automatically
below `2^64` because every coordinate is a canonical `u16`. -/
def epochValue (e : Epoch4) : Nat :=
  (e 0).1 + 65536 * (e 1).1 + 4294967296 * (e 2).1 +
    281474976710656 * (e 3).1

/-- A cell-owned PQ authority image.  `target` and `keyCommitment` are exact
32-byte values, not reduced field projections. -/
structure AuthorityState where
  target : Bytes32
  epoch : Epoch4
  keyCommitment : Bytes32
  deriving DecidableEq

/-- The lossless public image used by the authority descriptor: exact target,
exact epoch limbs, exact key commitment. -/
def authorityImage (s : AuthorityState) : Lanes16 × Epoch4 × Lanes16 :=
  (commitmentToLanes16 s.target, s.epoch, commitmentToLanes16 s.keyCommitment)

/-- The authority image has an actual inverse on both byte objects.  No hash
assumption and no field-collision assumption is needed for this binding. -/
theorem authorityImage_injective : Function.Injective authorityImage := by
  intro a b h
  have ht : commitmentToLanes16 a.target = commitmentToLanes16 b.target := by
    exact congrArg Prod.fst h
  have htail : (a.epoch, commitmentToLanes16 a.keyCommitment)
      = (b.epoch, commitmentToLanes16 b.keyCommitment) := by
    exact congrArg Prod.snd h
  have he : a.epoch = b.epoch := congrArg Prod.fst htail
  have hk : commitmentToLanes16 a.keyCommitment =
      commitmentToLanes16 b.keyCommitment := congrArg Prod.snd htail
  cases a
  cases b
  simp only [AuthorityState.mk.injEq]
  exact ⟨commitmentToLanes16_injective ht, he,
    commitmentToLanes16_injective hk⟩

/-! ## Rotation statement and the cryptographic boundary -/

/-- The exact structured statement signed by the incoming key.  The runtime's
domain-separated BLAKE3 transcript is a serialization of these fields plus the
raw ML-DSA public key whose commitment is `newKeyCommitment`; the correspondence
adapter must prove that serialization fact before this premise can be consumed.
`targetEd25519` is load-bearing: it is an explicit input to
`cell_pq_rotation_message`, distinct from the derived cell id. -/
structure PossessionStatement where
  target : Bytes32
  targetEd25519 : Bytes32
  oldEpoch : Epoch4
  newEpoch : Epoch4
  newKeyCommitment : Bytes32
  deriving DecidableEq

/-- The complete public claim of one rotation row.  Evidence objects are exact
32-byte commitments to the old-key authorization and new-key possession
transcripts.  They are carried separately so a receipt/proof binder cannot
silently reuse one evidence object for both roles. -/
structure RotationClaim where
  before : AuthorityState
  /-- The exact classical identity stored by the target cell and covered by
  the new-key possession transcript. -/
  targetEd25519 : Bytes32
  expectedEpoch : Epoch4
  after : AuthorityState
  oldAuthorizationEvidence : Bytes32
  newPossessionEvidence : Bytes32
  deriving DecidableEq

def possessionStatement (c : RotationClaim) : PossessionStatement where
  target := c.after.target
  targetEd25519 := c.targetEd25519
  oldEpoch := c.expectedEpoch
  newEpoch := c.after.epoch
  newKeyCommitment := c.after.keyCommitment

/-- The exact non-cryptographic rotation law.  The equality over reconstructed
natural epochs excludes overflow: there is no `after` below `2^64` satisfying
`after = (2^64-1)+1`. -/
def ExactRotation (c : RotationClaim) : Prop :=
  c.after.target = c.before.target ∧
  c.expectedEpoch = c.before.epoch ∧
  epochValue c.after.epoch = epochValue c.before.epoch + 1 ∧
  c.after.keyCommitment ≠ c.before.keyCommitment

/-- The ML-DSA boundary, parameterized by the verifier predicates rather than
smuggling their result in as an unconstrained witness bit. -/
structure CryptoBoundary
    (OldAuthorized : AuthorityState → Bytes32 → Prop)
    (NewPossessed : PossessionStatement → Bytes32 → Prop)
    (c : RotationClaim) : Prop where
  oldKeyAuthorized : OldAuthorized c.before c.oldAuthorizationEvidence
  newKeyPossessed : NewPossessed (possessionStatement c) c.newPossessionEvidence

/-- Full admission at this abstraction boundary: exact state transition AND
both cryptographic predicates over the exact bound statements. -/
def Admissible
    (OldAuthorized : AuthorityState → Bytes32 → Prop)
    (NewPossessed : PossessionStatement → Bytes32 → Prop)
    (c : RotationClaim) : Prop :=
  ExactRotation c ∧ CryptoBoundary OldAuthorized NewPossessed c

/-! ## Teeth -/

theorem exact_target {c : RotationClaim} (h : ExactRotation c) :
    c.after.target = c.before.target := h.1

theorem exact_expected_epoch {c : RotationClaim} (h : ExactRotation c) :
    c.expectedEpoch = c.before.epoch := h.2.1

theorem exact_monotone_epoch {c : RotationClaim} (h : ExactRotation c) :
    epochValue c.after.epoch = epochValue c.before.epoch + 1 := h.2.2.1

theorem exact_new_key {c : RotationClaim} (h : ExactRotation c) :
    c.after.keyCommitment ≠ c.before.keyCommitment := h.2.2.2

/-- A stale expected epoch cannot be admitted. -/
theorem stale_epoch_refused (c : RotationClaim)
    (hStale : c.expectedEpoch ≠ c.before.epoch) : ¬ ExactRotation c := by
  intro h
  exact hStale h.2.1

/-- A ghost rotation that leaves the epoch unchanged cannot be admitted. -/
theorem ghost_epoch_refused (c : RotationClaim)
    (hSame : c.after.epoch = c.before.epoch) : ¬ ExactRotation c := by
  intro h
  have hs := h.2.2.1
  rw [hSame] at hs
  omega

/-- Reinstalling the same committed key is not a rotation. -/
theorem unchanged_key_refused (c : RotationClaim)
    (hSame : c.after.keyCommitment = c.before.keyCommitment) : ¬ ExactRotation c := by
  intro h
  exact h.2.2.2 hSame

/-- Substituting a different old key changes the lossless pre-authority image.
This is structural, not a collision-resistance claim. -/
theorem wrong_old_key_changes_authority_image
    (live forged : AuthorityState)
    (hWrong : forged.keyCommitment ≠ live.keyCommitment) :
    authorityImage forged ≠ authorityImage live := by
  intro h
  have hs := authorityImage_injective h
  exact hWrong (congrArg AuthorityState.keyCommitment hs)

/-- The corresponding post-state tooth for a substituted new key. -/
theorem wrong_new_key_changes_authority_image
    (bound forged : AuthorityState)
    (hWrong : forged.keyCommitment ≠ bound.keyCommitment) :
    authorityImage forged ≠ authorityImage bound :=
  wrong_old_key_changes_authority_image bound forged hWrong

/-- The possession statement itself changes under new-key substitution.  The
cryptographic premise is therefore about the exact key commitment the row
installs, never an unbound carried key. -/
theorem wrong_new_key_changes_possession_statement
    (c : RotationClaim) (forged : Bytes32)
    (hWrong : forged ≠ c.after.keyCommitment) :
    { possessionStatement c with newKeyCommitment := forged } ≠ possessionStatement c := by
  intro h
  exact hWrong (congrArg PossessionStatement.newKeyCommitment h)

/-- Admission exposes both verifier premises; neither can be manufactured by
the algebraic row alone. -/
theorem admissible_crypto_boundary
    (OldAuthorized : AuthorityState → Bytes32 → Prop)
    (NewPossessed : PossessionStatement → Bytes32 → Prop)
    (c : RotationClaim)
    (h : Admissible OldAuthorized NewPossessed c) :
    OldAuthorized c.before c.oldAuthorizationEvidence ∧
      NewPossessed (possessionStatement c) c.newPossessionEvidence :=
  ⟨h.2.oldKeyAuthorized, h.2.newKeyPossessed⟩

#assert_axioms authorityImage_injective
#assert_axioms stale_epoch_refused
#assert_axioms ghost_epoch_refused
#assert_axioms unchanged_key_refused
#assert_axioms wrong_old_key_changes_authority_image
#assert_axioms wrong_new_key_changes_authority_image
#assert_axioms wrong_new_key_changes_possession_statement
#assert_axioms admissible_crypto_boundary

end Dregg2.Circuit.PqIdentityAuthority
