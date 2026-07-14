/-
# Dregg2.Circuit.CommitFaithfulRegrounded — the deployed cell commitment, without G3.

The legacy EffectVM continuity leaf is the four-node `hash_4_to_1` tree over
`[balLo, balHi, nonce, fields[0..8], capRoot, recordDigest]`.  The last felt is not an
independent user field: in Rust it is `compute_authority_digest_felt`, lane zero of
`bytes32_to_8_limbs(blake3(authority_residue_bytes(cell)))`.

The previous model merely read a scalar named `recordDigest`.  An extra field therefore produced a
free `LimbDecodeCollision`, and the advertised recovery assumed that no collision exists anywhere in
a finite hash.  This file removes both errors:

* `AuthorityResidue` names the exact semantic sections serialized by
  `cell/src/commitment.rs::authority_residue_bytes`, in their Rust order.  Variable sections already
  include their Rust option/tag/u64-length framing.  Lifecycle, delegation epoch, committed height,
  and heap root are deliberately not claimed to be in this byte string at HEAD: the live rotated
  v9+ commitment carries them as separate named limbs.
* `DeployedCell.toValue` is the canonical abstract boundary.  `authorityInput` is domain-separated:
  a canonical value hashes its authority-residue object; a malformed/open record hashes the entire
  `Value` in an `abstract` domain.  Thus the total abstract model cannot erase an unnamed field.
* Equal clear limbs and equal authority preimages determine the whole `Value`.  Hence a collision of
  the 13-limb leaf reduces only to a genuine authority-fold collision or a genuine `h4` collision.
* Whole-kernel, nonce, and replay theorems are reduction-form.  The recovery event is the local
  adversary-failure event, which is inhabited on honest equal openings; no theorem assumes global
  nonexistence of collisions.

The honest residual is computational.  The 13-limb prefix uses only authority lane zero (and the
Rust differential suite contains a concrete lane-zero collision); the live rotated path publishes
all eight authority lanes and an eight-output `wireCommitR8`.  Nothing here promotes one BabyBear
felt to 128-bit binding or revives `Poseidon2SpongeCR` injectivity.

No `sorry`, `admit`, `native_decide`, or new axiom.  Every theorem is audited below.
-/
import Dregg2.Tactics
import Dregg2.Circuit.CommitDifferential
import Dregg2.Circuit.StateCommitReduce
import Dregg2.Circuit.HashFloorHonesty
import Dregg2.Circuit.OodRomBound
import Dregg2.Exec.RecordKernel
import Dregg2.Exec.EffectTransfer

namespace Dregg2.Circuit.CommitFaithfulRegrounded

open Dregg2.Exec (CellId FieldName Value Turn RecordKernelState balOf balanceField recTransfer)
open Dregg2.Exec.EffectTransfer
open Dregg2.Circuit.CommitDifferential (effectVmCommit)
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.Transfer
open Dregg2.Crypto.ProbCrypto (winProb)
open Dregg2.Circuit.CollisionReduce (CellCollision SpongeCollision CompressCollision)
open Dregg2.Circuit.StateCommitReduce (StateBreakP recStateCommit_binds_kernel_orBreak)

set_option autoImplicit false

/-! ## 1. The Rust authority-residue preimage and canonical abstract cell. -/

/-- A byte section in the Rust serializer.  Fixed-width sections contain their bytes directly;
variable-width sections contain the exact option/tag/u64-length framing written by Rust. -/
abbrev ByteSection := List Nat

/-- The semantic sections of `authority_residue_bytes`, in serialization order.

`identity` is `cell.id || public_key || token_id`; `permissions` contains all eight authorization
tags and every custom permission VK; `delegation` contains source/epoch/refresh/staleness/snapshot;
the final four fields are the Swiss/refcount/overflow/system side-table roots. -/
structure AuthorityResidue where
  domainPrefix : ByteSection
  identity : ByteSection
  mode : ByteSection
  permissions : ByteSection
  verificationKey : ByteSection
  delegate : ByteSection
  delegation : ByteSection
  program : ByteSection
  overflowFields : ByteSection
  fieldVisibility : ByteSection
  commitments : ByteSection
  provedState : ByteSection
  swissRoot : ByteSection
  refcountRoot : ByteSection
  fieldsRootBytes : ByteSection
  systemRootsBytes : ByteSection
  deriving Repr

/-- The exact concatenation order fed to BLAKE3 by `authority_residue_bytes`. -/
def AuthorityResidue.toBytes (r : AuthorityResidue) : List Nat :=
  r.domainPrefix ++ r.identity ++ r.mode ++ r.permissions ++ r.verificationKey ++ r.delegate ++
    r.delegation ++ r.program ++ r.overflowFields ++ r.fieldVisibility ++ r.commitments ++
    r.provedState ++ r.swissRoot ++ r.refcountRoot ++ r.fieldsRootBytes ++ r.systemRootsBytes

/-- Preserve an already-framed byte section inside the open `Value` model without pretending it is
a field element.  Repeated `byte` entries retain order and multiplicity. -/
def byteSectionValue (xs : ByteSection) : Value :=
  .record (xs.map (fun b => ("byte", .dig b)))

/-- The canonical, named authority object stored at the Lean/Rust boundary.  The order is the Rust
serialization order; `toBytes` above is the byte-level denotation used by the real fold. -/
def AuthorityResidue.toValue (r : AuthorityResidue) : Value :=
  .record [("prefix", byteSectionValue r.domainPrefix), ("identity", byteSectionValue r.identity),
    ("mode", byteSectionValue r.mode), ("permissions", byteSectionValue r.permissions),
    ("verificationKey", byteSectionValue r.verificationKey),
    ("delegate", byteSectionValue r.delegate), ("delegation", byteSectionValue r.delegation),
    ("program", byteSectionValue r.program), ("overflowFields", byteSectionValue r.overflowFields),
    ("fieldVisibility", byteSectionValue r.fieldVisibility),
    ("commitments", byteSectionValue r.commitments), ("provedState", byteSectionValue r.provedState),
    ("swissRoot", byteSectionValue r.swissRoot), ("refcountRoot", byteSectionValue r.refcountRoot),
    ("fieldsRoot", byteSectionValue r.fieldsRootBytes),
    ("systemRootsDigest", byteSectionValue r.systemRootsBytes)]

private def emptyAuthorityResidue : AuthorityResidue where
  domainPrefix := []
  identity := []
  mode := []
  permissions := []
  verificationKey := []
  delegate := []
  delegation := []
  program := []
  overflowFields := []
  fieldVisibility := []
  commitments := []
  provedState := []
  swissRoot := []
  refcountRoot := []
  fieldsRootBytes := []
  systemRootsBytes := []

-- The exact serializer preimage moves when a permission-tag/custom-VK section moves.
#guard emptyAuthorityResidue.toBytes !=
  ({ emptyAuthorityResidue with permissions := [1, 7, 9] }).toBytes

/-- A canonical cell preimage for the legacy 13-limb EffectVM tree.  The authority object denotes
the BLAKE3 preimage; the other fields are the twelve clear commitment limbs before balance split. -/
structure DeployedCell where
  balance : Int
  nonce : Int
  f0 : Int
  f1 : Int
  f2 : Int
  f3 : Int
  f4 : Int
  f5 : Int
  f6 : Int
  f7 : Int
  capRoot : Int
  authorityResidue : Value
  deriving Repr

def DeployedCell.field (d : DeployedCell) : Fin 8 → Int
  | 0 => d.f0 | 1 => d.f1 | 2 => d.f2 | 3 => d.f3
  | 4 => d.f4 | 5 => d.f5 | 6 => d.f6 | 7 => d.f7

/-- The one canonical top-level `Value` layout accepted as a deployed cell.  Exact layout matters:
extra/reordered/duplicate fields are not silently discarded; they enter the fallback hash domain. -/
def DeployedCell.toValue (d : DeployedCell) : Value :=
  .record [("balance", .int d.balance), ("nonce", .int d.nonce),
    ("f0", .int d.f0), ("f1", .int d.f1), ("f2", .int d.f2), ("f3", .int d.f3),
    ("f4", .int d.f4), ("f5", .int d.f5), ("f6", .int d.f6), ("f7", .int d.f7),
    ("capRoot", .int d.capRoot), ("authorityResidue", d.authorityResidue)]

/-- Rust's 30-bit split modulus (`lo = balance & 0x3fff_ffff`, `hi = balance >> 30`). -/
def splitMod : Int := 1073741824

def balLoLimb (v : Value) : Int := balOf v % splitMod
def balHiLimb (v : Value) : Int := balOf v / splitMod
def nonceLimb (v : Value) : Int := nonceOf v

def fieldName : Fin 8 → FieldName
  | 0 => "f0" | 1 => "f1" | 2 => "f2" | 3 => "f3"
  | 4 => "f4" | 5 => "f5" | 6 => "f6" | 7 => "f7"

def fieldLimbs (v : Value) : Fin 8 → Int := fun i => (v.scalar (fieldName i)).getD 0
def capRootLimb (v : Value) : Int := (v.scalar "capRoot").getD 0
def authorityResidueValue (v : Value) : Value :=
  (v.field "authorityResidue").getD (.record [])

/-- Reconstruct the canonical deployed view from named reads. -/
def decodedCell (v : Value) : DeployedCell where
  balance := balOf v
  nonce := nonceOf v
  f0 := fieldLimbs v 0
  f1 := fieldLimbs v 1
  f2 := fieldLimbs v 2
  f3 := fieldLimbs v 3
  f4 := fieldLimbs v 4
  f5 := fieldLimbs v 5
  f6 := fieldLimbs v 6
  f7 := fieldLimbs v 7
  capRoot := capRootLimb v
  authorityResidue := authorityResidueValue v

/-- Exact canonicality at the abstract/deployed boundary. -/
def CanonicalCell (v : Value) : Prop := v = (decodedCell v).toValue

/-- Canonicality of the *deployed Rust* subset: the authority object itself is the named encoding of
an `AuthorityResidue`, not merely an arbitrary nested `Value`. -/
def CanonicalRustCell (v : Value) : Prop :=
  ∃ d : DeployedCell, ∃ r : AuthorityResidue,
    d.authorityResidue = r.toValue ∧ v = d.toValue

/-- The fold input is tagged.  `rust residue` is realized by
`bytes32_to_8_limbs(blake3(AuthorityResidue.toBytes residue))[0]`; `abstract wholeValue` is a
separate conservative domain for malformed/open abstract values. -/
inductive AuthorityInput where
  | rust : Value → AuthorityInput
  | abstract : Value → AuthorityInput
  deriving Repr

/-- Total, lossless boundary decode.  Canonical deployed values feed only the authority residue to
Rust's fold.  Everything else feeds the whole `Value` under a distinct tag, closing the old free
extra-field collision without changing the deployed canonical path. -/
noncomputable def authorityInput (v : Value) : AuthorityInput :=
  letI : Decidable (CanonicalCell v) := Classical.propDecidable _
  if CanonicalCell v then .rust (authorityResidueValue v) else .abstract v

/-- The scalar Rust fold (`compute_authority_digest_felt`).  Its concrete realization is BLAKE3
followed by faithful eight-limb decoding and projection to lane zero. -/
abbrev AuthorityFold := AuthorityInput → Int

/-- The full deployed authority digest (`compute_authority_digest_8`). -/
abbrev AuthorityFold8 := AuthorityInput → Fin 8 → Int

/-- The legacy scalar projection used by the 13-limb tree. -/
def lane0Fold (fold8 : AuthorityFold8) : AuthorityFold := fun x => fold8 x 0

/-- A lane-zero collision that the other seven deployed authority lanes distinguish.  The Rust
differential suite contains such a locked/open pair; this is why the 13-limb prefix alone is not the
128-bit binding surface. -/
def Lane0OnlyCollision (fold8 : AuthorityFold8) : Prop :=
  ∃ x y : AuthorityInput, x ≠ y ∧ fold8 x 0 = fold8 y 0 ∧ ∃ i : Fin 8, fold8 x i ≠ fold8 y i

noncomputable def recordDigestLimb (fold : AuthorityFold) (v : Value) : Int := fold (authorityInput v)

/-- The faithful legacy leaf: exactly the differential-pinned Rust `CellState::compute_commitment`
tree, with `recordDigest` computed from the residue rather than read as a free scalar. -/
noncomputable def CH_faithful (fold : AuthorityFold) (h4 : Int → Int → Int → Int → Int)
    (_c : CellId) (v : Value) : Int :=
  effectVmCommit h4 (balLoLimb v) (balHiLimb v) (nonceLimb v) (fieldLimbs v)
    (capRootLimb v) (recordDigestLimb fold v)

/-- Direct deployed denotation on a canonical cell, useful both for the differential statement and
computable non-vacuity witnesses. -/
def deployedLeaf (fold : AuthorityFold) (h4 : Int → Int → Int → Int → Int) (d : DeployedCell) : Int :=
  effectVmCommit h4 (d.balance % splitMod) (d.balance / splitMod) d.nonce d.field d.capRoot
    (fold (.rust d.authorityResidue))

theorem DeployedCell.ext' {d e : DeployedCell}
    (hbalance : d.balance = e.balance) (hnonce : d.nonce = e.nonce)
    (hf0 : d.f0 = e.f0) (hf1 : d.f1 = e.f1) (hf2 : d.f2 = e.f2) (hf3 : d.f3 = e.f3)
    (hf4 : d.f4 = e.f4) (hf5 : d.f5 = e.f5) (hf6 : d.f6 = e.f6) (hf7 : d.f7 = e.f7)
    (hcap : d.capRoot = e.capRoot) (hauth : d.authorityResidue = e.authorityResidue) : d = e := by
  cases d
  cases e
  simp_all

theorem DeployedCell.toValue_canonical (d : DeployedCell) : CanonicalCell d.toValue := by
  cases d
  simp [CanonicalCell, decodedCell, DeployedCell.toValue, fieldLimbs, fieldName, capRootLimb,
    authorityResidueValue, balOf, balanceField, Value.scalar, Value.field, nonceOf, nonceField]

theorem authorityInput_of_canonicalRustCell {v : Value} (h : CanonicalRustCell v) :
    ∃ r : AuthorityResidue, authorityInput v = .rust r.toValue := by
  classical
  rcases h with ⟨d, r, hdr, rfl⟩
  refine ⟨r, ?_⟩
  have hc : CanonicalCell d.toValue := DeployedCell.toValue_canonical d
  simp only [authorityInput, if_pos hc]
  simp [DeployedCell.toValue, authorityResidueValue, hdr, Value.field]

theorem CH_faithful_toValue (fold : AuthorityFold) (h4 : Int → Int → Int → Int → Int)
    (c : CellId) (d : DeployedCell) :
    CH_faithful fold h4 c d.toValue = deployedLeaf fold h4 d := by
  classical
  have hcanon := DeployedCell.toValue_canonical d
  have hfields : fieldLimbs d.toValue = d.field := by
    funext i
    fin_cases i <;>
      simp [fieldLimbs, fieldName, DeployedCell.toValue, DeployedCell.field,
        Value.scalar, Value.field]
  simp only [CH_faithful, deployedLeaf, recordDigestLimb, authorityInput, if_pos hcanon]
  rw [hfields]
  simp [DeployedCell.toValue, authorityResidueValue, balLoLimb, balHiLimb, nonceLimb,
    capRootLimb, balOf, balanceField, Value.scalar, Value.field, nonceOf, nonceField]

#assert_axioms DeployedCell.ext'
#assert_axioms DeployedCell.toValue_canonical
#assert_axioms authorityInput_of_canonicalRustCell
#assert_axioms CH_faithful_toValue

/-! ### Non-vacuity: the residue is load-bearing in the exact Rust tree. -/

private def h4Demo : Int → Int → Int → Int → Int :=
  fun a b c d => a * 1000000000 + b * 1000000 + c * 1000 + d

private def foldDemo : AuthorityFold
  | .rust v =>
      match v.field "mode" with
      | some (.record ((_, .dig b) :: _)) => (b : Int) + 41
      | _ => 41
  | .abstract _ => -1

private def residueDemo (mode : Nat) : Value :=
  ({ emptyAuthorityResidue with mode := [mode] }).toValue

private def cellDemo (mode : Nat) : DeployedCell where
  balance := 5
  nonce := 7
  f0 := 10
  f1 := 11
  f2 := 12
  f3 := 13
  f4 := 14
  f5 := 15
  f6 := 16
  f7 := 17
  capRoot := 100
  authorityResidue := residueDemo mode

#guard deployedLeaf foldDemo h4Demo (cellDemo 0)
  == effectVmCommit h4Demo 5 0 7 (fun i => 10 + (i : Int)) 100 41
#guard deployedLeaf foldDemo h4Demo (cellDemo 0) != deployedLeaf foldDemo h4Demo (cellDemo 1)

/-! ## 2. Decode injectivity and honest collision reductions. -/

def SameSurface (v w : Value) : Prop :=
  balLoLimb v = balLoLimb w ∧ balHiLimb v = balHiLimb w ∧ nonceLimb v = nonceLimb w
    ∧ fieldLimbs v 0 = fieldLimbs w 0 ∧ fieldLimbs v 1 = fieldLimbs w 1
    ∧ fieldLimbs v 2 = fieldLimbs w 2 ∧ fieldLimbs v 3 = fieldLimbs w 3
    ∧ fieldLimbs v 4 = fieldLimbs w 4 ∧ fieldLimbs v 5 = fieldLimbs w 5
    ∧ fieldLimbs v 6 = fieldLimbs w 6 ∧ fieldLimbs v 7 = fieldLimbs w 7
    ∧ capRootLimb v = capRootLimb w

/-- The G3 close.  Clear-limb equality plus authority-preimage equality determines the entire
abstract `Value`, including malformed/open records (which live in the tagged fallback domain). -/
theorem sameSurface_authorityInput_injective {v w : Value}
    (hs : SameSurface v w) (ha : authorityInput v = authorityInput w) : v = w := by
  classical
  rcases hs with ⟨hlo, hhi, hnonce, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hcap⟩
  by_cases hv : CanonicalCell v
  · by_cases hw : CanonicalCell w
    · have hres : authorityResidueValue v = authorityResidueValue w := by
        simpa only [authorityInput, if_pos hv, if_pos hw, AuthorityInput.rust.injEq] using ha
      have hbal : balOf v = balOf w := by
        rw [← Int.emod_add_mul_ediv (balOf v) splitMod,
          ← Int.emod_add_mul_ediv (balOf w) splitMod]
        change balOf v % splitMod = balOf w % splitMod at hlo
        change balOf v / splitMod = balOf w / splitMod at hhi
        rw [hlo, hhi]
      have hdecoded : decodedCell v = decodedCell w :=
        DeployedCell.ext' hbal hnonce hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hcap hres
      rw [hv, hw, hdecoded]
    · simp only [authorityInput, if_pos hv, if_neg hw] at ha
      cases ha
  · by_cases hw : CanonicalCell w
    · simp only [authorityInput, if_neg hv, if_pos hw] at ha
      cases ha
    · simpa only [authorityInput, if_neg hv, if_neg hw, AuthorityInput.abstract.injEq] using ha

#assert_axioms sameSurface_authorityInput_injective

/-- A genuine collision in `compute_authority_digest_felt`'s complete, tagged preimage domain. -/
def AuthorityDigestCollision (fold : AuthorityFold) : Prop :=
  ∃ x y : AuthorityInput, x ≠ y ∧ fold x = fold y

theorem lane0OnlyCollision_breaks_legacy (fold8 : AuthorityFold8)
    (h : Lane0OnlyCollision fold8) : AuthorityDigestCollision (lane0Fold fold8) := by
  rcases h with ⟨x, y, hne, hzero, _⟩
  exact ⟨x, y, hne, hzero⟩

#assert_axioms lane0OnlyCollision_breaks_legacy

/-- A genuine collision in one `hash_4_to_1` node. -/
def Compress4Collision (h4 : Int → Int → Int → Int → Int) : Prop :=
  ∃ a b c d a' b' c' d' : Int,
    ¬ (a = a' ∧ b = b' ∧ c = c' ∧ d = d') ∧ h4 a b c d = h4 a' b' c' d'

/-- Tree tracing: unequal 13-limb inputs with equal roots exhibit an actual `h4` collision. -/
theorem effectVmCommit_collision_of_ne (h4 : Int → Int → Int → Int → Int)
    (bl bh n : Int) (f : Fin 8 → Int) (cr rd : Int)
    (bl' bh' n' : Int) (f' : Fin 8 → Int) (cr' rd' : Int)
    (hne : ¬ (bl = bl' ∧ bh = bh' ∧ n = n'
      ∧ f 0 = f' 0 ∧ f 1 = f' 1 ∧ f 2 = f' 2 ∧ f 3 = f' 3
      ∧ f 4 = f' 4 ∧ f 5 = f' 5 ∧ f 6 = f' 6 ∧ f 7 = f' 7
      ∧ cr = cr' ∧ rd = rd'))
    (heq : effectVmCommit h4 bl bh n f cr rd = effectVmCommit h4 bl' bh' n' f' cr' rd') :
    Compress4Collision h4 := by
  simp only [effectVmCommit] at heq
  by_cases hr : (h4 bl bh n (f 0) = h4 bl' bh' n' (f' 0)
      ∧ h4 (f 1) (f 2) (f 3) (f 4) = h4 (f' 1) (f' 2) (f' 3) (f' 4)
      ∧ h4 (f 5) (f 6) (f 7) cr = h4 (f' 5) (f' 6) (f' 7) cr'
      ∧ rd = rd')
  · obtain ⟨he1, he2, he3, herd⟩ := hr
    by_cases ha : (bl = bl' ∧ bh = bh' ∧ n = n' ∧ f 0 = f' 0)
    · by_cases hb : (f 1 = f' 1 ∧ f 2 = f' 2 ∧ f 3 = f' 3 ∧ f 4 = f' 4)
      · by_cases hc : (f 5 = f' 5 ∧ f 6 = f' 6 ∧ f 7 = f' 7 ∧ cr = cr')
        · exfalso
          apply hne
          obtain ⟨e0, e1, e2, e3⟩ := ha
          obtain ⟨e4, e5, e6, e7⟩ := hb
          obtain ⟨e8, e9, e10, e11⟩ := hc
          exact ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, herd⟩
        · exact ⟨_, _, _, _, _, _, _, _, hc, he3⟩
      · exact ⟨_, _, _, _, _, _, _, _, hb, he2⟩
    · exact ⟨_, _, _, _, _, _, _, _, ha, he1⟩
  · exact ⟨_, _, _, _, _, _, _, _, hr, heq⟩

#assert_axioms effectVmCommit_collision_of_ne

def SameLimbs (fold : AuthorityFold) (v w : Value) : Prop :=
  SameSurface v w ∧ recordDigestLimb fold v = recordDigestLimb fold w

/-- Retained as a diagnostic name, but no longer a free gap: every such collision exhibits a real
authority-fold collision. -/
def LimbDecodeCollision (fold : AuthorityFold) (v w : Value) : Prop :=
  v ≠ w ∧ SameLimbs fold v w

theorem limbDecodeCollision_reduces (fold : AuthorityFold) {v w : Value}
    (h : LimbDecodeCollision fold v w) : AuthorityDigestCollision fold := by
  rcases h with ⟨hne, hs, hd⟩
  by_cases ha : authorityInput v = authorityInput w
  · exact absurd (sameSurface_authorityInput_injective hs ha) hne
  · exact ⟨authorityInput v, authorityInput w, ha, hd⟩

#assert_axioms limbDecodeCollision_reduces

/-- The faithful leaf collision has exactly two honest causes: the authority fold collides, or a
node of the deployed `h4` tree collides.  There is no unconditional decode-gap branch. -/
theorem cellCollision_faithful_reduces (fold : AuthorityFold)
    (h4 : Int → Int → Int → Int → Int) :
    CellCollision (CH_faithful fold h4) → AuthorityDigestCollision fold ∨ Compress4Collision h4 := by
  rintro ⟨c, v, w, hne, heq⟩
  simp only [CH_faithful] at heq
  by_cases hs : SameSurface v w
  · by_cases ha : authorityInput v = authorityInput w
    · exact absurd (sameSurface_authorityInput_injective hs ha) hne
    · by_cases hd : recordDigestLimb fold v = recordDigestLimb fold w
      · exact Or.inl ⟨authorityInput v, authorityInput w, ha, hd⟩
      · have hneLimbs : ¬ (SameSurface v w ∧
            recordDigestLimb fold v = recordDigestLimb fold w) := fun h => hd h.2
        exact Or.inr (effectVmCommit_collision_of_ne h4
          (balLoLimb v) (balHiLimb v) (nonceLimb v) (fieldLimbs v)
          (capRootLimb v) (recordDigestLimb fold v)
          (balLoLimb w) (balHiLimb w) (nonceLimb w) (fieldLimbs w)
          (capRootLimb w) (recordDigestLimb fold w)
          (by simpa only [SameSurface, and_assoc] using hneLimbs) heq)
  · have hneLimbs : ¬ (SameSurface v w ∧
        recordDigestLimb fold v = recordDigestLimb fold w) := fun h => hs h.1
    exact Or.inr (effectVmCommit_collision_of_ne h4
      (balLoLimb v) (balHiLimb v) (nonceLimb v) (fieldLimbs v)
      (capRootLimb v) (recordDigestLimb fold v)
      (balLoLimb w) (balHiLimb w) (nonceLimb w) (fieldLimbs w)
      (capRootLimb w) (recordDigestLimb fold w)
      (by simpa only [SameSurface, and_assoc] using hneLimbs) heq)

#assert_axioms cellCollision_faithful_reduces

/-! ## 3. Whole-kernel and freshness keystones on the faithful leaf. -/

def FaithfulBreak (fold : AuthorityFold) (h4 : Int → Int → Int → Int → Int)
    (cmb compress : Int → Int → Int) (compressN : List Int → Int) : Prop :=
  SpongeCollision compressN ∨ CompressCollision cmb ∨ CompressCollision compress
    ∨ AuthorityDigestCollision fold ∨ Compress4Collision h4

theorem stateBreak_faithful_reduces (fold : AuthorityFold)
    (h4 : Int → Int → Int → Int → Int) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) :
    StateBreakP (CH_faithful fold h4) cmb compress compressN →
      FaithfulBreak fold h4 cmb compress compressN := by
  rintro (hs | hcmb | hcomp | hcell)
  · exact Or.inl hs
  · exact Or.inr (Or.inl hcmb)
  · exact Or.inr (Or.inr (Or.inl hcomp))
  · rcases cellCollision_faithful_reduces fold h4 hcell with ha | hh4
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hh4)))

/-- Equal faithful roots determine the entire kernel, or exhibit a concrete collision. -/
theorem recStateCommit_binds_kernel_faithful (fold : AuthorityFold)
    (h4 : Int → Int → Int → Int → Int) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (hRest : RestHashIffFrame RH) (k k' : RecordKernelState) (t : Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hroot : recStateCommit (CH_faithful fold h4) RH cmb compress compressN k t =
      recStateCommit (CH_faithful fold h4) RH cmb compress compressN k' t) :
    k = k' ∨ FaithfulBreak fold h4 cmb compress compressN := by
  rcases recStateCommit_binds_kernel_orBreak (CH_faithful fold h4) cmb compress compressN RH hRest
      k k' t hwf hwf' hroot with hk | hb
  · exact Or.inl hk
  · exact Or.inr (stateBreak_faithful_reduces fold h4 cmb compress compressN hb)

/-- The local adversarial event.  Unlike global `¬ ∃ collision`, its negation is satisfiable for
honest/equal openings and is the event on which deterministic recovery is meant to run. -/
def KernelEquivocation (fold : AuthorityFold) (h4 : Int → Int → Int → Int → Int)
    (cmb compress : Int → Int → Int) (compressN : List Int → Int)
    (RH : RecordKernelState → Int) (k k' : RecordKernelState) (t : Turn) : Prop :=
  AccountsWF k ∧ AccountsWF k' ∧ k ≠ k' ∧
    recStateCommit (CH_faithful fold h4) RH cmb compress compressN k t =
      recStateCommit (CH_faithful fold h4) RH cmb compress compressN k' t

theorem kernelEquivocation_reduces (fold : AuthorityFold)
    (h4 : Int → Int → Int → Int → Int) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (hRest : RestHashIffFrame RH) (k k' : RecordKernelState) (t : Turn)
    (heqv : KernelEquivocation fold h4 cmb compress compressN RH k k' t) :
    FaithfulBreak fold h4 cmb compress compressN := by
  rcases heqv with ⟨hwf, hwf', hne, hroot⟩
  rcases recStateCommit_binds_kernel_faithful fold h4 cmb compress compressN RH hRest
      k k' t hwf hwf' hroot with hk | hb
  · exact absurd hk hne
  · exact hb

/-- Non-vacuous recovery: on a sampled key/run where this adversary did not equivocate, equal roots
recover equal states.  The premise is witnessed by `kernelEquivocation_refl_false`; it is not the
unsatisfiable assertion that a finite hash has no collisions anywhere. -/
theorem recStateCommit_binds_kernel_faithful_on_adversary_failure (fold : AuthorityFold)
    (h4 : Int → Int → Int → Int → Int) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (k k' : RecordKernelState) (t : Turn)
    (hNo : ¬ KernelEquivocation fold h4 cmb compress compressN RH k k' t)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hroot : recStateCommit (CH_faithful fold h4) RH cmb compress compressN k t =
      recStateCommit (CH_faithful fold h4) RH cmb compress compressN k' t) : k = k' := by
  by_contra hne
  exact hNo ⟨hwf, hwf', hne, hroot⟩

theorem kernelEquivocation_refl_false (fold : AuthorityFold)
    (h4 : Int → Int → Int → Int → Int) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (k : RecordKernelState) (t : Turn) :
    ¬ KernelEquivocation fold h4 cmb compress compressN RH k k t := by
  intro h
  exact h.2.2.1 rfl

/-- Faithful nonce binding in reduction form. -/
theorem commit_binds_nonce_faithful (fold : AuthorityFold)
    (h4 : Int → Int → Int → Int → Int) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (hRest : RestHashIffFrame RH) (k k' : RecordKernelState) (t : Turn) (agent : CellId)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hroot : recStateCommit (CH_faithful fold h4) RH cmb compress compressN k t =
      recStateCommit (CH_faithful fold h4) RH cmb compress compressN k' t) :
    nonceOf (k.cell agent) = nonceOf (k'.cell agent) ∨
      FaithfulBreak fold h4 cmb compress compressN := by
  rcases recStateCommit_binds_kernel_faithful fold h4 cmb compress compressN RH hRest
      k k' t hwf hwf' hroot with hk | hb
  · exact Or.inl (congrArg (fun s => nonceOf (s.cell agent)) hk)
  · exact Or.inr hb

/-- Pairwise replay tooth: two states with different agent nonces cannot share the faithful root
unless a concrete commitment collision is exhibited. -/
theorem nonce_difference_reduces (fold : AuthorityFold)
    (h4 : Int → Int → Int → Int → Int) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (hRest : RestHashIffFrame RH) (k k' : RecordKernelState) (t : Turn) (agent : CellId)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hnonce : nonceOf (k.cell agent) ≠ nonceOf (k'.cell agent))
    (hroot : recStateCommit (CH_faithful fold h4) RH cmb compress compressN k t =
      recStateCommit (CH_faithful fold h4) RH cmb compress compressN k' t) :
    FaithfulBreak fold h4 cmb compress compressN := by
  rcases commit_binds_nonce_faithful fold h4 cmb compress compressN RH hRest
      k k' t agent hwf hwf' hroot with hn | hb
  · exact absurd hn hnonce
  · exact hb

/-! ### The faithful commitment surface and the full cross-turn no-replay consumer. -/

/-- The deployed binding surface without impossible injectivity fields.  Its only structural
carrier is the rest-frame correspondence; every hash failure is returned as `FaithfulBreak`. -/
structure FaithfulCommitSurface where
  fold : AuthorityFold
  h4 : Int → Int → Int → Int → Int
  cmb : Int → Int → Int
  compress : Int → Int → Int
  compressN : List Int → Int
  RH : RecordKernelState → Int
  restFrame : RestHashIffFrame RH

noncomputable def FaithfulCommitSurface.commit (S : FaithfulCommitSurface)
    (k : RecordKernelState) (t : Turn) : Int :=
  recStateCommit (CH_faithful S.fold S.h4) S.RH S.cmb S.compress S.compressN k t

abbrev FaithfulCommitSurface.Break (S : FaithfulCommitSurface) : Prop :=
  FaithfulBreak S.fold S.h4 S.cmb S.compress S.compressN

theorem FaithfulCommitSurface.commit_binds_kernel (S : FaithfulCommitSurface)
    (k k' : RecordKernelState) (t : Turn) (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hroot : S.commit k t = S.commit k' t) : k = k' ∨ S.Break :=
  recStateCommit_binds_kernel_faithful S.fold S.h4 S.cmb S.compress S.compressN S.RH
    S.restFrame k k' t hwf hwf' hroot

theorem FaithfulCommitSurface.commit_binds_nonce (S : FaithfulCommitSurface)
    (k k' : RecordKernelState) (t : Turn) (agent : CellId)
    (hwf : AccountsWF k) (hwf' : AccountsWF k') (hroot : S.commit k t = S.commit k' t) :
    nonceOf (k.cell agent) = nonceOf (k'.cell agent) ∨ S.Break :=
  commit_binds_nonce_faithful S.fold S.h4 S.cmb S.compress S.compressN S.RH S.restFrame
    k k' t agent hwf hwf' hroot

/-- A verified sequence at the faithful surface.  The executor supplies `nonceMono` from its
never-rolled-back prologue; the commitment theorem supplies binding modulo explicit collisions. -/
structure FaithfulCommitChain (S : FaithfulCommitSurface) (agent : CellId) (t : Turn) where
  seq : Nat → RecordKernelState
  wf : ∀ i, AccountsWF (seq i)
  nonceMono : ∀ {i j : Nat}, i < j → nonceOf ((seq i).cell agent) < nonceOf ((seq j).cell agent)

noncomputable def FaithfulCommitChain.commitAt {S : FaithfulCommitSurface} {agent : CellId}
    {t : Turn} (C : FaithfulCommitChain S agent t) (i : Nat) : Int := S.commit (C.seq i) t

def FaithfulCommitChain.LiveCommitMatches {S : FaithfulCommitSurface} {agent : CellId}
    {t : Turn} (C : FaithfulCommitChain S agent t) (i : Nat) (preCommit : Int) : Prop :=
  C.commitAt i = preCommit

/-- Full cross-turn no replay on the deployed faithful surface: one live pre-anchor cannot match two
different indices unless the proof exhibits a concrete authority/Poseidon collision. -/
theorem no_replay_faithful {S : FaithfulCommitSurface} {agent : CellId} {t : Turn}
    (C : FaithfulCommitChain S agent t) {i j : Nat} {preCommit : Int}
    (hi : C.LiveCommitMatches i preCommit) (hj : C.LiveCommitMatches j preCommit) :
    i = j ∨ S.Break := by
  by_cases hij : i = j
  · exact Or.inl hij
  · apply Or.inr
    have hroot : S.commit (C.seq i) t = S.commit (C.seq j) t := hi.trans hj.symm
    rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
    · exact nonce_difference_reduces S.fold S.h4 S.cmb S.compress S.compressN S.RH S.restFrame
        (C.seq i) (C.seq j) t agent (C.wf i) (C.wf j) (ne_of_lt (C.nonceMono hlt)) hroot
    · have hn : nonceOf ((C.seq i).cell agent) ≠ nonceOf ((C.seq j).cell agent) :=
        ne_of_gt (C.nonceMono hgt)
      exact nonce_difference_reduces S.fold S.h4 S.cmb S.compress S.compressN S.RH S.restFrame
        (C.seq i) (C.seq j) t agent (C.wf i) (C.wf j) hn hroot

/-- Exact recovery on the satisfiable local adversary-failure event.  It quantifies only the pairs
the supplied chain opens, never global nonexistence of finite-hash collisions. -/
theorem no_replay_faithful_on_adversary_failure {S : FaithfulCommitSurface}
    {agent : CellId} {t : Turn} (C : FaithfulCommitChain S agent t)
    (hNo : ∀ a b : Nat,
      ¬ KernelEquivocation S.fold S.h4 S.cmb S.compress S.compressN S.RH (C.seq a) (C.seq b) t)
    {i j : Nat} {preCommit : Int}
    (hi : C.LiveCommitMatches i preCommit) (hj : C.LiveCommitMatches j preCommit) : i = j := by
  by_contra hij
  have hroot : S.commit (C.seq i) t = S.commit (C.seq j) t := hi.trans hj.symm
  have hnonce : nonceOf ((C.seq i).cell agent) ≠ nonceOf ((C.seq j).cell agent) := by
    rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
    · exact ne_of_lt (C.nonceMono hlt)
    · exact ne_of_gt (C.nonceMono hgt)
  have hstate : C.seq i ≠ C.seq j := by
    intro hs
    apply hnonce
    exact congrArg (fun k => nonceOf (k.cell agent)) hs
  exact hNo i j ⟨C.wf i, C.wf j, hstate, hroot⟩

/-! ### Full transfer soundness, with collisions returned instead of injectivity assumed. -/

/-- Faithful reduction-form twin of `StateCommit.transfer_circuit_full_sound`.  A satisfying
full-state transfer witness reconstructs the complete `TransferSpec`; if a digest cannot be opened
uniquely, the proof returns the concrete faithful break.  No `cellLeafInjective`,
`compressInjective`, or `compressNInjective` premise occurs. -/
theorem transfer_circuit_full_sound_faithful (fold : AuthorityFold)
    (h4 : Int → Int → Int → Int → Int) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (hRest : RestHashIffFrame RH) (k : RecordKernelState) (t : Turn) (k' : RecordKernelState)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (h : satisfiedS cmb compress
      (encodeS (CH_faithful fold h4) RH cmb compress compressN k t k')) :
    TransferSpec k t k' ∨ FaithfulBreak fold h4 cmb compress compressN := by
  obtain ⟨hsat, _hcommit⟩ := h
  have e0 := encodeS_agrees_encodeT (CH_faithful fold h4) RH cmb compress compressN
    k t k' vSrcPre (by decide)
  have e1 := encodeS_agrees_encodeT (CH_faithful fold h4) RH cmb compress compressN
    k t k' vDstPre (by decide)
  have e2 := encodeS_agrees_encodeT (CH_faithful fold h4) RH cmb compress compressN
    k t k' vSrcPost (by decide)
  have e3 := encodeS_agrees_encodeT (CH_faithful fold h4) RH cmb compress compressN
    k t k' vDstPost (by decide)
  have e4 := encodeS_agrees_encodeT (CH_faithful fold h4) RH cmb compress compressN
    k t k' vAmt (by decide)
  have e5 := encodeS_agrees_encodeT (CH_faithful fold h4) RH cmb compress compressN
    k t k' vTAuth (by decide)
  have e6 := encodeS_agrees_encodeT (CH_faithful fold h4) RH cmb compress compressN
    k t k' vTNonneg (by decide)
  have e7 := encodeS_agrees_encodeT (CH_faithful fold h4) RH cmb compress compressN
    k t k' vTAvail (by decide)
  have e8 := encodeS_agrees_encodeT (CH_faithful fold h4) RH cmb compress compressN
    k t k' vTDistinct (by decide)
  have e9 := encodeS_agrees_encodeT (CH_faithful fold h4) RH cmb compress compressN
    k t k' vTSrcLive (by decide)
  have e10 := encodeS_agrees_encodeT (CH_faithful fold h4) RH cmb compress compressN
    k t k' vTDstLive (by decide)
  have htsat : satisfied transferCircuit (encodeT k t k') := by
    intro c hc
    have hc' : c ∈ stateCircuit := by
      unfold stateCircuit
      exact List.mem_append_left _ hc
    have hcS := hsat c hc'
    unfold transferCircuit at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · unfold Constraint.holds at hcS ⊢
        simp only [cTAuth, cTNonneg, cTAvail, cTDistinct, cTSrcLive, cTDstLive, cTDebit,
          cTCredit, cTConserve, Expr.eval, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10] at hcS ⊢
        exact hcS
  obtain ⟨hg, _hdeb, _hcre, _hcons⟩ := transfer_circuit_sound k t k' htsat
  obtain ⟨hauth, hnn, hav, hne, hsrc, hdst⟩ := hg
  have hrestgate : cSRestFrame.holds
      (encodeS (CH_faithful fold h4) RH cmb compress compressN k t k') :=
    hsat cSRestFrame (by unfold stateCircuit; simp)
  have hframegate : cSFrameReuse.holds
      (encodeS (CH_faithful fold h4) RH cmb compress compressN k t k') :=
    hsat cSFrameReuse (by unfold stateCircuit; simp)
  have hmovedgate : cSMovedBind.holds
      (encodeS (CH_faithful fold h4) RH cmb compress compressN k t k') :=
    hsat cSMovedBind (by unfold stateCircuit; simp)
  have hRHeq : RH k = RH k' :=
    (srestframe_iff (CH_faithful fold h4) RH cmb compress compressN k t k').mp hrestgate
  obtain ⟨hAcc, hCaps, hBal, hNul, hRev, hCom, hSC, hFac, hLif, hDC, hDel, hDgs,
    hDE, hDEA, hHeaps, hNR, hRR, hCR⟩ := (hRest k k').mp hRHeq
  have hfdeq : frameDigest (CH_faithful fold h4) compressN k (frameCarrier k t) =
      frameDigest (CH_faithful fold h4) compressN k' (frameCarrier k t) :=
    (sframereuse_iff (CH_faithful fold h4) RH cmb compress compressN k t k').mp hframegate
  rcases StateCommitReduce.frameDigestBindsCells_orBreak
      (CH_faithful fold h4) cmb compress compressN k k' (frameCarrier k t) hfdeq with
    hcellframe | hb
  · have hmoveq : movedDigest (CH_faithful fold h4) compress k'.cell t.src t.dst =
        movedDigest (CH_faithful fold h4) compress
          (recTransfer k.cell t.src t.dst t.amt) t.src t.dst :=
      (smovedbind_iff (CH_faithful fold h4) RH cmb compress compressN k t k').mp hmovedgate
    rcases StateCommitReduce.movedDigestBindsCells_orBreak
        (CH_faithful fold h4) cmb compress compressN k'.cell
        (recTransfer k.cell t.src t.dst t.amt) t.src t.dst hmoveq with hmove | hb
    · obtain ⟨hmsrc, hmdst⟩ := hmove
      have hcellmap : k'.cell = recTransfer k.cell t.src t.dst t.amt := by
        funext c
        by_cases hcsrc : c = t.src
        · subst hcsrc
          exact hmsrc
        · by_cases hcdst : c = t.dst
          · subst hcdst
            exact hmdst
          · by_cases hcacc : c ∈ k.accounts
            · have hmem : c ∈ frameCarrier k t := by
                unfold frameCarrier
                simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
                exact ⟨hcacc, hcsrc, hcdst⟩
              rw [← hcellframe c hmem]
              simp only [recTransfer, if_neg hcsrc, if_neg hcdst]
            · have hk'acc : c ∉ k'.accounts := by
                rw [hAcc]
                exact hcacc
              rw [hwf' c hk'acc]
              simp only [recTransfer, if_neg hcsrc, if_neg hcdst]
              exact (hwf c hcacc).symm
      exact Or.inl ⟨⟨hauth, hnn, hav, hne, hsrc, hdst⟩, hcellmap,
        hAcc, hCaps, hBal, hNul, hRev, hCom, hSC, hFac, hLif, hDC, hDel, hDgs, hDE, hDEA,
        hHeaps, hNR, hRR, hCR⟩
    · exact Or.inr (stateBreak_faithful_reduces fold h4 cmb compress compressN hb)
  · exact Or.inr (stateBreak_faithful_reduces fold h4 cmb compress compressN hb)

#assert_axioms stateBreak_faithful_reduces
#assert_axioms recStateCommit_binds_kernel_faithful
#assert_axioms kernelEquivocation_reduces
#assert_axioms recStateCommit_binds_kernel_faithful_on_adversary_failure
#assert_axioms kernelEquivocation_refl_false
#assert_axioms commit_binds_nonce_faithful
#assert_axioms nonce_difference_reduces
#assert_axioms FaithfulCommitSurface.commit_binds_kernel
#assert_axioms FaithfulCommitSurface.commit_binds_nonce
#assert_axioms no_replay_faithful
#assert_axioms no_replay_faithful_on_adversary_failure
#assert_axioms transfer_circuit_full_sound_faithful

/-! ## 4. Both poles fire. -/

def plus4 : Int → Int → Int → Int → Int := fun a b c d => a + b + c + d

theorem plus4_collision : Compress4Collision plus4 :=
  ⟨100, 5, 0, 0, 99, 6, 0, 0, by decide, by decide⟩

def constantAuthorityFold : AuthorityFold := fun _ => 0

private def abstractA : AuthorityInput := .abstract (.int 0)
private def abstractB : AuthorityInput := .abstract (.int 1)

theorem constantAuthorityFold_collision : AuthorityDigestCollision constantAuthorityFold :=
  ⟨abstractA, abstractB, by
    intro h
    have hv : Value.int 0 = Value.int 1 := AuthorityInput.abstract.inj h
    have hi : (0 : Int) = 1 := Value.int.inj hv
    omega, rfl⟩

theorem no_free_decode_gap (fold : AuthorityFold) :
    (∃ v w, LimbDecodeCollision fold v w) → AuthorityDigestCollision fold := by
  rintro ⟨v, w, h⟩
  exact limbDecodeCollision_reduces fold h

#assert_axioms plus4_collision
#assert_axioms constantAuthorityFold_collision
#assert_axioms no_free_decode_gap

/-! ## 5. The honest floor.

`AuthorityDigestCollision fold` and the three Poseidon collision disjuncts are *findable-collision*
events, not impossibility premises.  `HashFloorHonesty.CollisionResistant` is the proper advantage
carrier.  The legacy scalar fold is only lane zero and is concretely weak; the deployed rotated path
must use the eight-lane authority group and `wireCommitR8`. -/

abbrev CollisionResistant := Dregg2.Circuit.HashFloorHonesty.CollisionResistant
abbrev CollisionFinder := Dregg2.Circuit.HashFloorHonesty.CollisionFinder
noncomputable abbrev collisionAdv := Dregg2.Circuit.HashFloorHonesty.collisionAdv

/-- What the existing `OodRomBound.RomUniform` floor honestly supplies for hashing: a fresh uniform
squeeze hits any fixed target with probability exactly `1 / |F|`.  This is the fixed-target leg used
inside collision reductions; adaptive/birthday collision finding still belongs to
`HashFloorHonesty.CollisionResistant`, not to a false injectivity statement. -/
theorem romUniform_fixed_target_hit {Ω F : Type*} [Fintype Ω] [Fintype F] [DecidableEq F]
    (draw : Ω → F) (hrom : Dregg2.Circuit.OodRomBound.RomUniform draw) (target : F) :
    winProb (fun ω => decide (draw ω = target)) = 1 / (Fintype.card F : ℝ) := by
  rw [hrom (fun x => decide (x = target))]
  unfold winProb
  have hfilter : Finset.univ.filter (fun x : F => decide (x = target) = true) = {target} := by
    ext x
    simp
  rw [hfilter, Finset.card_singleton]
  norm_num

#assert_axioms romUniform_fixed_target_hit

end Dregg2.Circuit.CommitFaithfulRegrounded
