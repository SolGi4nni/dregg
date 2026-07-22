/-
# `Dregg2.Crypto.PqShareCommitment` — additive randomized share commitments

This is the semantic replacement rung for the distributed prover's Ristretto
vector-commitment algebra.  It deliberately does NOT select deployment
dimensions or claim post-quantum security.  Instead it proves the exact algebra
that any concrete SIS/Module-SIS instantiation must implement.

For message module `M`, blinding module `B`, and digest module `N`, a public key
is two linear maps and an opening is `(m,r)`:

    commit (m,r) = Aₘ m + Aᵣ r.

Consequently openings and commitments add componentwise.  The public worker
link `sum shareCommitments = ownerCommitment` follows from the exact private
opening link `sum shareOpenings = ownerOpening`.  Conversely, if the public link
holds while those openings differ, their difference is a NONZERO kernel vector
of `[Aₘ | Aᵣ]`; with explicit shortness hypotheses it is an MSIS solution.  This
is extraction-as-data, not a claim that MSIS is hard at an unchosen parameter.

`rerandomize` makes the hiding mechanism explicit: adding `rho` to the blinding
translates the commitment by `Aᵣ rho` without changing its message.  Turning
that algebra into a hiding theorem needs a distribution and an MLWE/leftover-
hash assumption for concrete dimensions; neither is smuggled into this file.

The final section is an executable BabyBear reference KAT duplicated in
`fhegg-fhe/src/pq_share_commitment.rs`.  It pins centered negative reduction,
row-major ordering, and additive linking across Rust and Lean.  It is a finite
cross-implementation KAT, not a for-all refinement theorem.
-/
import Dregg2.Crypto.Lattice
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.LinearAlgebra.Prod

namespace Dregg2.Crypto.PqShareCommitment

set_option autoImplicit false

open Dregg2.Crypto.Lattice

variable {Rq : Type*} [CommRing Rq]
variable {M B N : Type*}
variable [AddCommGroup M] [Module Rq M]
variable [AddCommGroup B] [Module Rq B]
variable [AddCommGroup N] [Module Rq N]

/-- A secret opening consists of the committed message and its randomizer. -/
abbrev Opening (M B : Type*) := M × B

/-- The augmented public SIS map `[A_message | A_blinding]`. -/
def keyMap (messageMap : M →ₗ[Rq] N) (blindingMap : B →ₗ[Rq] N) :
    Opening M B →ₗ[Rq] N :=
  messageMap.coprod blindingMap

/-- Commit to an exact `(message, randomizer)` opening. -/
def commit (messageMap : M →ₗ[Rq] N) (blindingMap : B →ₗ[Rq] N)
    (opening : Opening M B) : N :=
  keyMap messageMap blindingMap opening

/-- Opening addition is the product-module addition. -/
def addOpening (left right : Opening M B) : Opening M B := left + right

@[simp] theorem commit_zero (messageMap : M →ₗ[Rq] N) (blindingMap : B →ₗ[Rq] N) :
    commit messageMap blindingMap (0 : Opening M B) = 0 := by
  simp [commit]

/-- **ADDITIVITY.** This is the exact point-addition law the Ristretto vector
commitment supplied, now stated for an arbitrary linear SIS map. -/
theorem commit_add (messageMap : M →ₗ[Rq] N) (blindingMap : B →ₗ[Rq] N)
    (left right : Opening M B) :
    commit messageMap blindingMap (addOpening left right) =
      commit messageMap blindingMap left + commit messageMap blindingMap right := by
  exact map_add (keyMap messageMap blindingMap) left right

/-- A whole worker set can be combined in any order because commitment is a
linear map over the list sum. -/
theorem commit_sum (messageMap : M →ₗ[Rq] N) (blindingMap : B →ₗ[Rq] N)
    (openings : List (Opening M B)) :
    commit messageMap blindingMap openings.sum =
      (openings.map (commit messageMap blindingMap)).sum := by
  induction openings with
  | nil => simp
  | cons opening rest ih =>
      simp only [List.sum_cons, List.map_cons]
      change keyMap messageMap blindingMap (opening + rest.sum) =
        keyMap messageMap blindingMap opening +
          (rest.map (commit messageMap blindingMap)).sum
      change keyMap messageMap blindingMap rest.sum =
        (rest.map (commit messageMap blindingMap)).sum at ih
      rw [map_add, ih]

/-- Executable exact-opening predicate. -/
def verifies [DecidableEq N] (messageMap : M →ₗ[Rq] N) (blindingMap : B →ₗ[Rq] N)
    (commitment : N) (opening : Opening M B) : Bool :=
  decide (commit messageMap blindingMap opening = commitment)

/-- The executable predicate accepts exactly genuine openings. -/
theorem verifies_iff [DecidableEq N] (messageMap : M →ₗ[Rq] N)
    (blindingMap : B →ₗ[Rq] N) (commitment : N) (opening : Opening M B) :
    verifies messageMap blindingMap commitment opening = true ↔
      commit messageMap blindingMap opening = commitment := by
  simp [verifies]

/-! ## Randomization / hiding seam. -/

/-- Change only the randomizer, retaining the exact message. -/
def rerandomize (opening : Opening M B) (rho : B) : Opening M B :=
  (opening.1, opening.2 + rho)

omit [AddCommGroup M] in
@[simp] theorem rerandomize_message (opening : Opening M B) (rho : B) :
    (rerandomize opening rho).1 = opening.1 := rfl

/-- Rerandomization translates the commitment by the blinding map.  A hiding
claim additionally needs a concrete randomizer distribution and a stated
leftover-hash/MLWE hypothesis. -/
theorem commit_rerandomize (messageMap : M →ₗ[Rq] N) (blindingMap : B →ₗ[Rq] N)
    (opening : Opening M B) (rho : B) :
    commit messageMap blindingMap (rerandomize opening rho) =
      commit messageMap blindingMap opening + blindingMap rho := by
  simp [commit, keyMap, rerandomize, LinearMap.coprod_apply, add_assoc]

omit [AddCommGroup M] in
/-- Randomizer translation is a bijection on the opening space for each fixed
`rho`; its inverse translates by `-rho`. This is the algebra a uniform finite
randomizer would spend in a hiding proof. -/
theorem rerandomize_bijective (rho : B) : Function.Bijective (fun o : Opening M B => rerandomize o rho) := by
  constructor
  · intro left right h
    apply Prod.ext
    · simpa [rerandomize] using congrArg Prod.fst h
    · have hsnd : left.2 + rho = right.2 + rho := by
        simpa [rerandomize] using congrArg Prod.snd h
      exact add_right_cancel hsnd
  · intro target
    refine ⟨rerandomize target (-rho), ?_⟩
    simp [rerandomize]

/-! ## Exact owner/share link and the SIS extractor. -/

/-- The private statement: the exact centered share openings add to the owner
opening.  A concrete codec must make the centered representation canonical. -/
def openingsLink (owner : Opening M B) (shares : List (Opening M B)) : Prop :=
  shares.sum = owner

/-- The public coordinator statement: only additive commitments are visible. -/
def commitmentsLink (owner : N) (shares : List N) : Prop :=
  shares.sum = owner

/-- Exact private linking implies the public commitment link. -/
theorem openingsLink_implies_commitmentsLink
    (messageMap : M →ₗ[Rq] N) (blindingMap : B →ₗ[Rq] N)
    (owner : Opening M B) (shares : List (Opening M B))
    (hlink : openingsLink owner shares) :
    commitmentsLink (commit messageMap blindingMap owner)
      (shares.map (commit messageMap blindingMap)) := by
  unfold openingsLink at hlink
  unfold commitmentsLink
  rw [← commit_sum, hlink]

variable [ShortNorm M] [ShortNorm B]

/-- Coefficient-product norm used for the augmented opening.  The concrete Rust
profile reports an infinity norm; parameter selection must bridge that concrete
bound to whichever product norm its SIS estimator/reduction uses. -/
local instance instShortNormOpening : ShortNorm (Opening M B) where
  nrm opening := nrm opening.1 + nrm opening.2
  nrm_zero := by simp [nrm_zero]
  nrm_neg opening := by simp [nrm_neg]
  nrm_add_le left right := by
    show nrm (left.1 + right.1) + nrm (left.2 + right.2) ≤
      (nrm left.1 + nrm left.2) + (nrm right.1 + nrm right.2)
    calc
      nrm (left.1 + right.1) + nrm (left.2 + right.2)
          ≤ (nrm left.1 + nrm right.1) + (nrm left.2 + nrm right.2) :=
            Nat.add_le_add (nrm_add_le _ _) (nrm_add_le _ _)
      _ = (nrm left.1 + nrm left.2) + (nrm right.1 + nrm right.2) := by omega

/-- **THE LINK EXTRACTOR.** If public share commitments sum to the owner
commitment but the exact openings do not, their difference is a short nonzero
kernel vector of `[A_message | A_blinding]`: an MSIS solution produced as data.
No hardness or dimension claim is made. -/
theorem false_opening_link_extracts_msis
    (messageMap : M →ₗ[Rq] N) (blindingMap : B →ₗ[Rq] N)
    (owner : Opening M B) (shares : List (Opening M B))
    (βshares βowner : Nat)
    (hsharesShort : IsShort βshares shares.sum)
    (hownerShort : IsShort βowner owner)
    (hne : ¬ openingsLink owner shares)
    (hpublic : commitmentsLink (commit messageMap blindingMap owner)
      (shares.map (commit messageMap blindingMap))) :
    IsMSISSolution (keyMap messageMap blindingMap) (βshares + βowner)
      (shares.sum - owner) := by
  have hcollision : commit messageMap blindingMap shares.sum =
      commit messageMap blindingMap owner := by
    rw [commit_sum]
    exact hpublic
  refine ⟨?_, IsShort.sub hsharesShort hownerShort, ?_⟩
  · exact sub_ne_zero.mpr hne
  · rw [map_sub]
    exact sub_eq_zero.mpr hcollision

/-! ## Exact BFV q0 radix carrier.

The experimental Rust q0 carrier commits to 4,096 canonical residues by
expanding each one into three little-endian radix-2^15 coordinates.  This
section pins that codec and proves it loses no information below q0.  It says
nothing about binding/hiding parameters, nor does it link this opening to the
live Ristretto DKG commitment; those remain separate security obligations.
-/

/-- First production BFV RNS modulus, matching Rust `BFV_Q0_MODULUS`. -/
def bfvQ0Modulus : Nat := 68_719_403_009

/-- Production BFV polynomial degree. -/
def bfvQ0Degree : Nat := 4_096

/-- Rust expands each residue into three base-2^15 coordinates. -/
def bfvQ0Radix : Nat := 32_768
def bfvQ0LimbsPerCoefficient : Nat := 3
def bfvQ0ValueWidth : Nat := bfvQ0Degree * bfvQ0LimbsPerCoefficient

#guard bfvQ0Modulus < bfvQ0Radix ^ bfvQ0LimbsPerCoefficient
#guard bfvQ0ValueWidth = 12_288

/-- Mathematical three-limb expansion.  The high limb is left unreduced so
the reconstruction theorem is unconditional; `bfvQ0Encode_matches_rust`
proves that q0's capacity bound makes Rust's third `% radix` identical. -/
def bfvQ0Encode (x : Nat) : Nat × Nat × Nat :=
  (x % bfvQ0Radix,
    (x / bfvQ0Radix) % bfvQ0Radix,
    x / (bfvQ0Radix * bfvQ0Radix))

/-- Exact three `% radix` operations performed by the Rust loop. -/
def bfvQ0EncodeRust (x : Nat) : Nat × Nat × Nat :=
  (x % bfvQ0Radix,
    (x / bfvQ0Radix) % bfvQ0Radix,
    (x / (bfvQ0Radix * bfvQ0Radix)) % bfvQ0Radix)

def bfvQ0Decode (limbs : Nat × Nat × Nat) : Nat :=
  limbs.1 + bfvQ0Radix * limbs.2.1 +
    bfvQ0Radix * bfvQ0Radix * limbs.2.2

/-- Base-2^15 expansion and reconstruction are exactly inverse over naturals. -/
theorem bfvQ0Decode_encode (x : Nat) : bfvQ0Decode (bfvQ0Encode x) = x := by
  simp [bfvQ0Decode, bfvQ0Encode, bfvQ0Radix]
  omega

/-- Every coordinate is canonical whenever the input fits in three limbs. -/
theorem bfvQ0Encode_limbBounds (x : Nat) (h : x < bfvQ0Radix ^ 3) :
    (bfvQ0Encode x).1 < bfvQ0Radix ∧
      (bfvQ0Encode x).2.1 < bfvQ0Radix ∧
      (bfvQ0Encode x).2.2 < bfvQ0Radix := by
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.mod_lt _ (by norm_num [bfvQ0Radix])
  · exact Nat.mod_lt _ (by norm_num [bfvQ0Radix])
  · apply (Nat.div_lt_iff_lt_mul (by norm_num [bfvQ0Radix])).2
    simpa [bfvQ0Radix, pow_succ] using h

/-- Under the q0 capacity bound, the executable Rust loop is precisely the
mathematical expansion above. -/
theorem bfvQ0Encode_matches_rust (x : Nat) (h : x < bfvQ0Radix ^ 3) :
    bfvQ0EncodeRust x = bfvQ0Encode x := by
  have hthird : x / (bfvQ0Radix * bfvQ0Radix) < bfvQ0Radix :=
    (bfvQ0Encode_limbBounds x h).2.2
  simp [bfvQ0EncodeRust, bfvQ0Encode, Nat.mod_eq_of_lt hthird]

/-- Therefore the literal Rust encoding reconstructs every canonical q0
residue exactly. -/
theorem bfvQ0Decode_encodeRust (x : Nat) (h : x < bfvQ0Radix ^ 3) :
    bfvQ0Decode (bfvQ0EncodeRust x) = x := by
  rw [bfvQ0Encode_matches_rust x h]
  exact bfvQ0Decode_encode x

/-- The loop's postcondition (`debug_assert_eq!(remaining, 0)`) follows from
the same capacity premise. -/
theorem bfvQ0Rust_leftover_zero (x : Nat) (h : x < bfvQ0Radix ^ 3) :
    x / bfvQ0Radix / bfvQ0Radix / bfvQ0Radix = 0 := by
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  exact Nat.div_eq_of_lt (by simpa [pow_succ, mul_assoc] using h)

/-- All canonical q0 residues satisfy the exact codec's capacity premise. -/
theorem bfvQ0Residue_fits (x : Nat) (h : x < bfvQ0Modulus) :
    x < bfvQ0Radix ^ 3 := by
  exact lt_trans h (by decide)

/-! ## Cross-language executable KAT (explicit tiny matrix, BabyBear). -/

/-- Executable policy pin matching Rust: the current 13-felt/704-blinder
profile is algebra/KAT only. In particular, live uniform Ristretto scalar shares
do not supply the short BabyBear message coordinates an SIS binding estimate
would require. No current tuple is production-PQ approved. -/
def productionPqReady : Bool := false

#guard productionPqReady = false

def babyBearQ : Int := 2013265921

def centeredModQ (value : Int) : Nat := (value % babyBearQ).toNat

def dotCentered (row : List Nat) (coordinates : List Int) : Int :=
  (List.zipWith (fun coefficient value => (coefficient : Int) * value) row coordinates).sum

def commitRef (messageRows blindingRows : List (List Nat))
    (message blinding : List Int) : List Nat :=
  List.zipWith
    (fun messageRow blindingRow =>
      centeredModQ (dotCentered messageRow message + dotCentered blindingRow blinding))
    messageRows blindingRows

def katMessageRows : List (List Nat) :=
  [[1, 2, 3], [5, 7, 11], [13, 17, 19]]

def katBlindingRows : List (List Nat) :=
  [[23, 29, 31, 37], [41, 43, 47, 53], [59, 61, 67, 71]]

def katOwner : List Nat :=
  commitRef katMessageRows katBlindingRows [3, -2, 5] [1, -1, 1, -1]

def katShareA : List Nat :=
  commitRef katMessageRows katBlindingRows [1, -3, 2] [1, -1, 1, 1]

def katShareB : List Nat :=
  commitRef katMessageRows katBlindingRows [2, 1, 3] [0, 0, 0, -2]

-- Same values are asserted in Rust. The negative-output share pins canonical
-- centered reduction rather than only the easy positive branch.
#guard katOwner == [2, 48, 94]
#guard katShareA == [63, 104, 136]
#guard katShareB == [2013265860, 2013265865, 2013265879]
#guard List.zipWith (fun left right => (left + right) % 2013265921) katShareA katShareB == katOwner

#assert_axioms commit_add
#assert_axioms commit_sum
#assert_axioms verifies_iff
#assert_axioms commit_rerandomize
#assert_axioms rerandomize_bijective
#assert_axioms openingsLink_implies_commitmentsLink
#assert_axioms false_opening_link_extracts_msis
#assert_axioms bfvQ0Decode_encode
#assert_axioms bfvQ0Encode_limbBounds
#assert_axioms bfvQ0Encode_matches_rust
#assert_axioms bfvQ0Decode_encodeRust
#assert_axioms bfvQ0Rust_leftover_zero
#assert_axioms bfvQ0Residue_fits

end Dregg2.Crypto.PqShareCommitment
