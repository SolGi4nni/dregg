/-
# Dregg2.Circuit.CommitFaithfulRegrounded — the live rotated eight-lane commitment.

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

The legacy analysis remains as a diagnostic, but the keystone surface is the live 178-limb rotated
path.  `RotatedCell` and `rotatedLimb` place the authority octet at `[24,12..18]`, the faithful cap
and heap roots in their deployed groups, lifecycle/epoch/height at `29/30/31`, and publish the
eight-output `wireCommitR8`.  `CH_faithful8` uses a lossless tuple serialization only to fit the
older scalar `recStateCommit` interface; it adds no hash assumption and projects no lane.

Consequently the kernel/no-replay/transfer keystones return only a genuine collision of the full
eight-lane authority digest, the 178-limb wide chain, or an outer state-tree primitive.  A collision
visible only in legacy lane zero is no longer on their break surface.

No `sorry`, `admit`, `native_decide`, or new axiom.  Every theorem is audited below.
-/
import Dregg2.Tactics
import Dregg2.Circuit.CommitDifferential
import Dregg2.Circuit.StateCommitReduce
import Dregg2.Circuit.HashFloorHonesty
import Dregg2.Circuit.OodRomBound
import Dregg2.Circuit.Emit.EffectVmEmitRotationR
import Dregg2.Exec.RecordKernel
import Dregg2.Exec.EffectTransfer
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Encodable.Pi

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
def LegacyLane0OnlyCollision (fold8 : AuthorityFold8) : Prop :=
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

theorem legacyLane0OnlyCollision_breaks_legacy (fold8 : AuthorityFold8)
    (h : LegacyLane0OnlyCollision fold8) : AuthorityDigestCollision (lane0Fold fold8) := by
  rcases h with ⟨x, y, hne, hzero, _⟩
  exact ⟨x, y, hne, hzero⟩

#assert_axioms legacyLane0OnlyCollision_breaks_legacy

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

/-! ## 3. The deployed rotated 178-limb / eight-output surface.

The legacy leaf above remains only as the differential-pinned diagnostic.  The binding consumer
below models the live wide route: the authority digest occupies all eight deployed lanes
`[24,12..18]`; the capability and heap roots occupy their eight-lane groups; lifecycle,
delegation epoch, and committed height remain explicit scalar limbs; and `wireCommitR8` publishes
the final eight-felt carrier. -/

abbrev Digest8 := Fin 8 → Int

def digest8Value (d : Digest8) : Value :=
  .record [("lane0", .int (d 0)), ("lane1", .int (d 1)), ("lane2", .int (d 2)),
    ("lane3", .int (d 3)), ("lane4", .int (d 4)), ("lane5", .int (d 5)),
    ("lane6", .int (d 6)), ("lane7", .int (d 7))]

def digest8OfValue (v : Value) : Digest8
  | 0 => (v.scalar "lane0").getD 0
  | 1 => (v.scalar "lane1").getD 0
  | 2 => (v.scalar "lane2").getD 0
  | 3 => (v.scalar "lane3").getD 0
  | 4 => (v.scalar "lane4").getD 0
  | 5 => (v.scalar "lane5").getD 0
  | 6 => (v.scalar "lane6").getD 0
  | 7 => (v.scalar "lane7").getD 0

theorem digest8OfValue_digest8Value (d : Digest8) : digest8OfValue (digest8Value d) = d := by
  funext i
  fin_cases i <;> simp [digest8OfValue, digest8Value, Value.scalar, Value.field]

/-- The per-cell semantic portion of Rust's rotated preimage.  Turn-level roots and carrier
material stay in `RotatedContext`; these fields are exactly the cell-owned values relevant to P1. -/
structure RotatedCell where
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
  capRoot8 : Digest8
  authorityResidue : Value
  heapRoot8 : Digest8
  lifecycle : Int
  delegationEpoch : Int
  committedHeight : Int

def RotatedCell.field (d : RotatedCell) : Fin 8 → Int
  | 0 => d.f0 | 1 => d.f1 | 2 => d.f2 | 3 => d.f3
  | 4 => d.f4 | 5 => d.f5 | 6 => d.f6 | 7 => d.f7

def RotatedCell.toValue (d : RotatedCell) : Value :=
  .record [("balance", .int d.balance), ("nonce", .int d.nonce),
    ("f0", .int d.f0), ("f1", .int d.f1), ("f2", .int d.f2), ("f3", .int d.f3),
    ("f4", .int d.f4), ("f5", .int d.f5), ("f6", .int d.f6), ("f7", .int d.f7),
    ("capRoot8", digest8Value d.capRoot8), ("authorityResidue", d.authorityResidue),
    ("heapRoot8", digest8Value d.heapRoot8), ("lifecycle", .int d.lifecycle),
    ("delegationEpoch", .int d.delegationEpoch), ("committedHeight", .int d.committedHeight)]

def rotatedNestedValue (v : Value) (name : String) : Value :=
  (v.field name).getD (.record [])

def decodedRotatedCell (v : Value) : RotatedCell where
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
  capRoot8 := digest8OfValue (rotatedNestedValue v "capRoot8")
  authorityResidue := authorityResidueValue v
  heapRoot8 := digest8OfValue (rotatedNestedValue v "heapRoot8")
  lifecycle := (v.scalar "lifecycle").getD 0
  delegationEpoch := (v.scalar "delegationEpoch").getD 0
  committedHeight := (v.scalar "committedHeight").getD 0

def CanonicalRotatedCell (v : Value) : Prop := v = (decodedRotatedCell v).toValue

def RotatedCell.clear (d : RotatedCell) :
    Int × Int × (Fin 8 → Int) × Digest8 × Digest8 × Int × Int × Int :=
  (d.balance, d.nonce, d.field, d.capRoot8, d.heapRoot8, d.lifecycle,
    d.delegationEpoch, d.committedHeight)

def rotatedClear (v : Value) := (decodedRotatedCell v).clear

theorem RotatedCell.ext_of_clear {d e : RotatedCell} (hc : d.clear = e.clear)
    (ha : d.authorityResidue = e.authorityResidue) : d = e := by
  cases d
  cases e
  simp only [RotatedCell.clear, Prod.mk.injEq] at hc
  have hf := hc.2.2.1
  have hf0 := congrFun hf (0 : Fin 8)
  have hf1 := congrFun hf (1 : Fin 8)
  have hf2 := congrFun hf (2 : Fin 8)
  have hf3 := congrFun hf (3 : Fin 8)
  have hf4 := congrFun hf (4 : Fin 8)
  have hf5 := congrFun hf (5 : Fin 8)
  have hf6 := congrFun hf (6 : Fin 8)
  have hf7 := congrFun hf (7 : Fin 8)
  simp only [RotatedCell.field] at hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7
  simp_all

theorem RotatedCell.toValue_canonical (d : RotatedCell) : CanonicalRotatedCell d.toValue := by
  cases d
  simp [CanonicalRotatedCell, decodedRotatedCell, RotatedCell.toValue, rotatedNestedValue,
    digest8OfValue_digest8Value, fieldLimbs, fieldName, authorityResidueValue, balOf, balanceField,
    Value.scalar, Value.field, nonceOf, nonceField]

/-- The exact wide boundary tag.  Canonical deployed cells hash only Rust's authority-residue
bytes; malformed/open abstract values hash their entire `Value` in the disjoint fallback domain. -/
noncomputable def rotatedAuthorityInput (v : Value) : AuthorityInput :=
  letI : Decidable (CanonicalRotatedCell v) := Classical.propDecidable _
  if CanonicalRotatedCell v then .rust (authorityResidueValue v) else .abstract v

theorem sameRotatedSurface_authorityInput_injective {v w : Value}
    (hs : rotatedClear v = rotatedClear w)
    (ha : rotatedAuthorityInput v = rotatedAuthorityInput w) : v = w := by
  classical
  by_cases hv : CanonicalRotatedCell v
  · by_cases hw : CanonicalRotatedCell w
    · have hres : authorityResidueValue v = authorityResidueValue w := by
        simpa only [rotatedAuthorityInput, if_pos hv, if_pos hw, AuthorityInput.rust.injEq] using ha
      have hd : decodedRotatedCell v = decodedRotatedCell w :=
        RotatedCell.ext_of_clear hs hres
      rw [hv, hw, hd]
    · simp only [rotatedAuthorityInput, if_pos hv, if_neg hw] at ha
      cases ha
  · by_cases hw : CanonicalRotatedCell w
    · simp only [rotatedAuthorityInput, if_neg hv, if_pos hw] at ha
      cases ha
    · simpa only [rotatedAuthorityInput, if_neg hv, if_neg hw,
        AuthorityInput.abstract.injEq] using ha

/-- The non-cell/turn-owned remainder of the deployed 178-limb row.  Known cell-owned positions are
overridden below; `residual` carries cells/nullifier/commitments/revoked roots, carrier octets, pads,
and other already-modeled lanes without pretending they are authority bytes. -/
structure RotatedContext where
  residual : Fin 178 → Int
  iroot : Int

abbrev RotatedContextProvider := CellId → Value → RotatedContext

/-- One exact deployed pre-iroot position.  The indices mirror
`cell::commitment::compute_rotated_pre_limbs` and `trace_rotated.rs` at HEAD. -/
noncomputable def rotatedLimb (fold8 : AuthorityFold8) (ctx : RotatedContext)
    (v : Value) (i : Fin 178) : Int :=
  let d := decodedRotatedCell v
  match i.1 with
  | 1 => d.balance % splitMod
  | 2 => d.nonce
  | 3 => d.balance / splitMod
  | 4 => d.field 0 | 5 => d.field 1 | 6 => d.field 2 | 7 => d.field 3
  | 8 => d.field 4 | 9 => d.field 5 | 10 => d.field 6 | 11 => d.field 7
  | 12 => fold8 (rotatedAuthorityInput v) 1
  | 13 => fold8 (rotatedAuthorityInput v) 2
  | 14 => fold8 (rotatedAuthorityInput v) 3
  | 15 => fold8 (rotatedAuthorityInput v) 4
  | 16 => fold8 (rotatedAuthorityInput v) 5
  | 17 => fold8 (rotatedAuthorityInput v) 6
  | 18 => fold8 (rotatedAuthorityInput v) 7
  | 24 => fold8 (rotatedAuthorityInput v) 0
  | 25 => d.capRoot8 0
  | 28 => d.heapRoot8 0
  | 29 => d.lifecycle
  | 30 => d.delegationEpoch
  | 31 => d.committedHeight
  | 52 => d.capRoot8 1 | 53 => d.capRoot8 2 | 54 => d.capRoot8 3
  | 55 => d.capRoot8 4 | 56 => d.capRoot8 5 | 57 => d.capRoot8 6 | 58 => d.capRoot8 7
  | 59 => d.heapRoot8 1 | 60 => d.heapRoot8 2 | 61 => d.heapRoot8 3
  | 62 => d.heapRoot8 4 | 63 => d.heapRoot8 5 | 64 => d.heapRoot8 6 | 65 => d.heapRoot8 7
  | _ => ctx.residual i

noncomputable def rotatedPreLimbs (fold8 : AuthorityFold8) (ctx : RotatedContext)
    (v : Value) : List Int :=
  List.ofFn (rotatedLimb fold8 ctx v)

theorem rotatedPreLimbs_length (fold8 : AuthorityFold8) (ctx : RotatedContext) (v : Value) :
    (rotatedPreLimbs fold8 ctx v).length = 178 := by
  unfold rotatedPreLimbs
  exact List.length_ofFn

open Dregg2.Circuit.Emit.EffectVmEmitRotationR
  (wireCommitR8 chainFrom8_len Poseidon2Width8 refWide)

noncomputable def rotatedCommit8 (fold8 : AuthorityFold8) (permW : List Int → List Int)
    (ctx : RotatedContext) (v : Value) : List Int :=
  wireCommitR8 permW (rotatedPreLimbs fold8 ctx v) ctx.iroot

/-- Computable direct twin on a canonical `RotatedCell`, used by the golden guards and by a Rust
differential: it avoids the abstract malformed-value branch while retaining the exact 178 indices. -/
def deployedRotatedLimb (fold8 : AuthorityFold8) (ctx : RotatedContext)
    (d : RotatedCell) (i : Fin 178) : Int :=
  match i.1 with
  | 1 => d.balance % splitMod
  | 2 => d.nonce
  | 3 => d.balance / splitMod
  | 4 => d.field 0 | 5 => d.field 1 | 6 => d.field 2 | 7 => d.field 3
  | 8 => d.field 4 | 9 => d.field 5 | 10 => d.field 6 | 11 => d.field 7
  | 12 => fold8 (.rust d.authorityResidue) 1
  | 13 => fold8 (.rust d.authorityResidue) 2
  | 14 => fold8 (.rust d.authorityResidue) 3
  | 15 => fold8 (.rust d.authorityResidue) 4
  | 16 => fold8 (.rust d.authorityResidue) 5
  | 17 => fold8 (.rust d.authorityResidue) 6
  | 18 => fold8 (.rust d.authorityResidue) 7
  | 24 => fold8 (.rust d.authorityResidue) 0
  | 25 => d.capRoot8 0
  | 28 => d.heapRoot8 0
  | 29 => d.lifecycle
  | 30 => d.delegationEpoch
  | 31 => d.committedHeight
  | 52 => d.capRoot8 1 | 53 => d.capRoot8 2 | 54 => d.capRoot8 3
  | 55 => d.capRoot8 4 | 56 => d.capRoot8 5 | 57 => d.capRoot8 6 | 58 => d.capRoot8 7
  | 59 => d.heapRoot8 1 | 60 => d.heapRoot8 2 | 61 => d.heapRoot8 3
  | 62 => d.heapRoot8 4 | 63 => d.heapRoot8 5 | 64 => d.heapRoot8 6 | 65 => d.heapRoot8 7
  | _ => ctx.residual i

def deployedRotatedCommit8 (fold8 : AuthorityFold8) (permW : List Int → List Int)
    (ctx : RotatedContext) (d : RotatedCell) : List Int :=
  wireCommitR8 permW (List.ofFn (deployedRotatedLimb fold8 ctx d)) ctx.iroot

private def fold8Demo : AuthorityFold8 := fun x i =>
  match i.1 with
  | 0 => 41
  | 1 => foldDemo x
  | n => 41 + n

private def rotatedCellDemo (mode : Nat) : RotatedCell where
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
  capRoot8 := fun i => 100 + i.1
  authorityResidue := residueDemo mode
  heapRoot8 := fun i => 200 + i.1
  lifecycle := 3
  delegationEpoch := 4
  committedHeight := 5

private def rotatedContextDemo : RotatedContext where
  residual := fun i => 300 + i.1
  iroot := 9

-- The legacy lane agrees, but authority lane 1 and therefore the live wide commitment differ.
#guard fold8Demo (.rust (rotatedCellDemo 0).authorityResidue) 0 ==
  fold8Demo (.rust (rotatedCellDemo 1).authorityResidue) 0
#guard fold8Demo (.rust (rotatedCellDemo 0).authorityResidue) 1 !=
  fold8Demo (.rust (rotatedCellDemo 1).authorityResidue) 1
#guard deployedRotatedCommit8 fold8Demo refWide rotatedContextDemo (rotatedCellDemo 0) !=
  deployedRotatedCommit8 fold8Demo refWide rotatedContextDemo (rotatedCellDemo 1)

theorem rotatedCommit8_length (permW : List Int → List Int) (hW : Poseidon2Width8 permW)
    (fold8 : AuthorityFold8) (ctx : RotatedContext) (v : Value) :
    (rotatedCommit8 fold8 permW ctx v).length = 8 := by
  unfold rotatedCommit8 wireCommitR8
  exact chainFrom8_len permW hW (hW ((rotatedPreLimbs fold8 ctx v).take 4))

/-- Lossless mathematical packing of the eight PIs into the scalar carrier expected by the older
`recStateCommit` abstraction.  This is serialization, not another hash: equality of packs recovers
all eight lanes under the deployed width contract. -/
def wideTuple (xs : List Int) : Fin 8 → Int := fun i => xs.getD i.1 0

def packWideTuple (xs : List Int) : Int :=
  Int.ofNat (Encodable.encode (wideTuple xs))

theorem list_eq_of_wideTuple_eq {xs ys : List Int} (hx : xs.length = 8) (hy : ys.length = 8)
    (h : wideTuple xs = wideTuple ys) : xs = ys := by
  apply List.ext_getElem
  · exact hx.trans hy.symm
  · intro i hi hi'
    have hi8 : i < 8 := by simpa [hx] using hi
    have hget := congrFun h (⟨i, hi8⟩ : Fin 8)
    simp only [wideTuple] at hget
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi'] at hget
    exact hget

noncomputable def CH_faithful8 (fold8 : AuthorityFold8) (permW : List Int → List Int)
    (ctx : RotatedContextProvider) (c : CellId) (v : Value) : Int :=
  packWideTuple (rotatedCommit8 fold8 permW (ctx c v) v)

/-- A collision of the complete authority digest: both distinct tagged preimages agree in all
eight lanes.  This is the only authority failure on the live wide surface. -/
def AuthorityDigest8Collision (fold8 : AuthorityFold8) : Prop :=
  ∃ x y : AuthorityInput, x ≠ y ∧ fold8 x = fold8 y

/-- A genuine collision of the deployed 178-limb plus iroot wide chain. -/
def WireCommit8Collision (permW : List Int → List Int) : Prop :=
  ∃ l l' : List Int, ∃ ir ir' : Int,
    (l ≠ l' ∨ ir ≠ ir') ∧ wireCommitR8 permW l ir = wireCommitR8 permW l' ir'

theorem rotatedPreLimbs_eq_implies (fold8 : AuthorityFold8)
    (ctx ctx' : RotatedContext) {v w : Value}
    (h : rotatedPreLimbs fold8 ctx v = rotatedPreLimbs fold8 ctx' w) :
    rotatedClear v = rotatedClear w ∧
      fold8 (rotatedAuthorityInput v) = fold8 (rotatedAuthorityInput w) := by
  have hfn : rotatedLimb fold8 ctx v = rotatedLimb fold8 ctx' w :=
    List.ofFn_injective h
  have hp (n : Nat) (hn : n < 178) :
      rotatedLimb fold8 ctx v ⟨n, hn⟩ = rotatedLimb fold8 ctx' w ⟨n, hn⟩ :=
    congrFun hfn ⟨n, hn⟩
  have hlo : (decodedRotatedCell v).balance % splitMod =
      (decodedRotatedCell w).balance % splitMod := by
    simpa [rotatedLimb] using hp 1 (by decide)
  have hhi : (decodedRotatedCell v).balance / splitMod =
      (decodedRotatedCell w).balance / splitMod := by
    simpa [rotatedLimb] using hp 3 (by decide)
  have hbal : (decodedRotatedCell v).balance = (decodedRotatedCell w).balance := by
    rw [← Int.emod_add_mul_ediv (decodedRotatedCell v).balance splitMod,
      ← Int.emod_add_mul_ediv (decodedRotatedCell w).balance splitMod, hlo, hhi]
  have hn : (decodedRotatedCell v).nonce = (decodedRotatedCell w).nonce := by
    simpa [rotatedLimb] using hp 2 (by decide)
  have hf : (decodedRotatedCell v).field = (decodedRotatedCell w).field := by
    funext i
    fin_cases i
    · simpa [rotatedLimb] using hp 4 (by decide)
    · simpa [rotatedLimb] using hp 5 (by decide)
    · simpa [rotatedLimb] using hp 6 (by decide)
    · simpa [rotatedLimb] using hp 7 (by decide)
    · simpa [rotatedLimb] using hp 8 (by decide)
    · simpa [rotatedLimb] using hp 9 (by decide)
    · simpa [rotatedLimb] using hp 10 (by decide)
    · simpa [rotatedLimb] using hp 11 (by decide)
  have hcap : (decodedRotatedCell v).capRoot8 = (decodedRotatedCell w).capRoot8 := by
    funext i
    fin_cases i
    · simpa [rotatedLimb] using hp 25 (by decide)
    · simpa [rotatedLimb] using hp 52 (by decide)
    · simpa [rotatedLimb] using hp 53 (by decide)
    · simpa [rotatedLimb] using hp 54 (by decide)
    · simpa [rotatedLimb] using hp 55 (by decide)
    · simpa [rotatedLimb] using hp 56 (by decide)
    · simpa [rotatedLimb] using hp 57 (by decide)
    · simpa [rotatedLimb] using hp 58 (by decide)
  have hheap : (decodedRotatedCell v).heapRoot8 = (decodedRotatedCell w).heapRoot8 := by
    funext i
    fin_cases i
    · simpa [rotatedLimb] using hp 28 (by decide)
    · simpa [rotatedLimb] using hp 59 (by decide)
    · simpa [rotatedLimb] using hp 60 (by decide)
    · simpa [rotatedLimb] using hp 61 (by decide)
    · simpa [rotatedLimb] using hp 62 (by decide)
    · simpa [rotatedLimb] using hp 63 (by decide)
    · simpa [rotatedLimb] using hp 64 (by decide)
    · simpa [rotatedLimb] using hp 65 (by decide)
  have hlifecycle : (decodedRotatedCell v).lifecycle = (decodedRotatedCell w).lifecycle := by
    simpa [rotatedLimb] using hp 29 (by decide)
  have hepoch : (decodedRotatedCell v).delegationEpoch =
      (decodedRotatedCell w).delegationEpoch := by
    simpa [rotatedLimb] using hp 30 (by decide)
  have hheight : (decodedRotatedCell v).committedHeight =
      (decodedRotatedCell w).committedHeight := by
    simpa [rotatedLimb] using hp 31 (by decide)
  have hclear : rotatedClear v = rotatedClear w := by
    simp only [rotatedClear, RotatedCell.clear, Prod.mk.injEq]
    exact ⟨hbal, hn, hf, hcap, hheap, hlifecycle, hepoch, hheight⟩
  have hauth : fold8 (rotatedAuthorityInput v) = fold8 (rotatedAuthorityInput w) := by
    funext i
    fin_cases i
    · simpa [rotatedLimb] using hp 24 (by decide)
    · simpa [rotatedLimb] using hp 12 (by decide)
    · simpa [rotatedLimb] using hp 13 (by decide)
    · simpa [rotatedLimb] using hp 14 (by decide)
    · simpa [rotatedLimb] using hp 15 (by decide)
    · simpa [rotatedLimb] using hp 16 (by decide)
    · simpa [rotatedLimb] using hp 17 (by decide)
    · simpa [rotatedLimb] using hp 18 (by decide)
  exact ⟨hclear, hauth⟩

/-- A collision in the scalar compatibility view is never a lane-0 residue: it reduces to equality
of all eight authority lanes on distinct preimages, or to a genuine collision of the wide chain. -/
theorem cellCollision_faithful8_reduces (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (hW : Poseidon2Width8 permW)
    (ctx : RotatedContextProvider) :
    CellCollision (CH_faithful8 fold8 permW ctx) →
      AuthorityDigest8Collision fold8 ∨ WireCommit8Collision permW := by
  rintro ⟨c, v, w, hne, hpack⟩
  have htuple : wideTuple (rotatedCommit8 fold8 permW (ctx c v) v) =
      wideTuple (rotatedCommit8 fold8 permW (ctx c w) w) := by
    apply Encodable.encode_injective
    exact Int.ofNat.inj (by simpa [CH_faithful8, packWideTuple] using hpack)
  have hcommit : rotatedCommit8 fold8 permW (ctx c v) v =
      rotatedCommit8 fold8 permW (ctx c w) w :=
    list_eq_of_wideTuple_eq
      (rotatedCommit8_length permW hW fold8 (ctx c v) v)
      (rotatedCommit8_length permW hW fold8 (ctx c w) w) htuple
  by_cases ha : rotatedAuthorityInput v = rotatedAuthorityInput w
  · by_cases hs : rotatedClear v = rotatedClear w
    · exact absurd (sameRotatedSurface_authorityInput_injective hs ha) hne
    · apply Or.inr
      have hl : rotatedPreLimbs fold8 (ctx c v) v ≠ rotatedPreLimbs fold8 (ctx c w) w := by
        intro heq
        exact hs (rotatedPreLimbs_eq_implies fold8 (ctx c v) (ctx c w) heq).1
      exact ⟨_, _, _, _, Or.inl hl, hcommit⟩
  · by_cases hd : fold8 (rotatedAuthorityInput v) = fold8 (rotatedAuthorityInput w)
    · exact Or.inl ⟨rotatedAuthorityInput v, rotatedAuthorityInput w, ha, hd⟩
    · apply Or.inr
      have hl : rotatedPreLimbs fold8 (ctx c v) v ≠ rotatedPreLimbs fold8 (ctx c w) w := by
        intro heq
        exact hd (rotatedPreLimbs_eq_implies fold8 (ctx c v) (ctx c w) heq).2
      exact ⟨_, _, _, _, Or.inl hl, hcommit⟩

#assert_axioms digest8OfValue_digest8Value
#assert_axioms RotatedCell.ext_of_clear
#assert_axioms RotatedCell.toValue_canonical
#assert_axioms sameRotatedSurface_authorityInput_injective
#assert_axioms rotatedPreLimbs_length
#assert_axioms rotatedCommit8_length
#assert_axioms list_eq_of_wideTuple_eq
#assert_axioms rotatedPreLimbs_eq_implies
#assert_axioms cellCollision_faithful8_reduces

/-! ## 4. Whole-kernel and freshness keystones on the live eight-lane leaf. -/

def FaithfulBreak (fold8 : AuthorityFold8) (permW : List Int → List Int)
    (cmb compress : Int → Int → Int) (compressN : List Int → Int) : Prop :=
  SpongeCollision compressN ∨ CompressCollision cmb ∨ CompressCollision compress
    ∨ AuthorityDigest8Collision fold8 ∨ WireCommit8Collision permW

theorem stateBreak_faithful_reduces (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (hW : Poseidon2Width8 permW)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) :
    StateBreakP (CH_faithful8 fold8 permW ctx) cmb compress compressN →
      FaithfulBreak fold8 permW cmb compress compressN := by
  rintro (hs | hcmb | hcomp | hcell)
  · exact Or.inl hs
  · exact Or.inr (Or.inl hcmb)
  · exact Or.inr (Or.inr (Or.inl hcomp))
  · rcases cellCollision_faithful8_reduces fold8 permW hW ctx hcell with ha | hwide
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hwide)))

/-- Equal live-wide faithful roots determine the entire kernel, or exhibit a concrete collision. -/
theorem recStateCommit_binds_kernel_faithful (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (hW : Poseidon2Width8 permW)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (hRest : RestHashIffFrame RH) (k k' : RecordKernelState) (t : Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hroot : recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t =
      recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k' t) :
    k = k' ∨ FaithfulBreak fold8 permW cmb compress compressN := by
  rcases recStateCommit_binds_kernel_orBreak (CH_faithful8 fold8 permW ctx)
      cmb compress compressN RH hRest k k' t hwf hwf' hroot with hk | hb
  · exact Or.inl hk
  · exact Or.inr (stateBreak_faithful_reduces fold8 permW hW ctx cmb compress compressN hb)

/-- The local adversarial event.  Unlike global `¬ ∃ collision`, its negation is satisfiable for
honest/equal openings and is the event on which deterministic recovery is meant to run. -/
def KernelEquivocation (fold8 : AuthorityFold8) (permW : List Int → List Int)
    (ctx : RotatedContextProvider)
    (cmb compress : Int → Int → Int) (compressN : List Int → Int)
    (RH : RecordKernelState → Int) (k k' : RecordKernelState) (t : Turn) : Prop :=
  AccountsWF k ∧ AccountsWF k' ∧ k ≠ k' ∧
    recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t =
      recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k' t

theorem kernelEquivocation_reduces (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (hW : Poseidon2Width8 permW)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (hRest : RestHashIffFrame RH) (k k' : RecordKernelState) (t : Turn)
    (heqv : KernelEquivocation fold8 permW ctx cmb compress compressN RH k k' t) :
    FaithfulBreak fold8 permW cmb compress compressN := by
  rcases heqv with ⟨hwf, hwf', hne, hroot⟩
  rcases recStateCommit_binds_kernel_faithful fold8 permW hW ctx cmb compress compressN RH hRest
      k k' t hwf hwf' hroot with hk | hb
  · exact absurd hk hne
  · exact hb

/-- Non-vacuous recovery: on a sampled key/run where this adversary did not equivocate, equal roots
recover equal states.  The premise is witnessed by `kernelEquivocation_refl_false`; it is not the
unsatisfiable assertion that a finite hash has no collisions anywhere. -/
theorem recStateCommit_binds_kernel_faithful_on_adversary_failure (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (ctx : RotatedContextProvider)
    (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (k k' : RecordKernelState) (t : Turn)
    (hNo : ¬ KernelEquivocation fold8 permW ctx cmb compress compressN RH k k' t)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hroot : recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t =
      recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k' t) : k = k' := by
  by_contra hne
  exact hNo ⟨hwf, hwf', hne, hroot⟩

theorem kernelEquivocation_refl_false (fold8 : AuthorityFold8) (permW : List Int → List Int)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (k : RecordKernelState) (t : Turn) :
    ¬ KernelEquivocation fold8 permW ctx cmb compress compressN RH k k t := by
  intro h
  exact h.2.2.1 rfl

/-- Faithful nonce binding in reduction form. -/
theorem commit_binds_nonce_faithful (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (hW : Poseidon2Width8 permW)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (hRest : RestHashIffFrame RH) (k k' : RecordKernelState) (t : Turn) (agent : CellId)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hroot : recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t =
      recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k' t) :
    nonceOf (k.cell agent) = nonceOf (k'.cell agent) ∨
      FaithfulBreak fold8 permW cmb compress compressN := by
  rcases recStateCommit_binds_kernel_faithful fold8 permW hW ctx cmb compress compressN RH hRest
      k k' t hwf hwf' hroot with hk | hb
  · exact Or.inl (congrArg (fun s => nonceOf (s.cell agent)) hk)
  · exact Or.inr hb

/-- Pairwise replay tooth: two states with different agent nonces cannot share the faithful root
unless a concrete commitment collision is exhibited. -/
theorem nonce_difference_reduces (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (hW : Poseidon2Width8 permW)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (hRest : RestHashIffFrame RH) (k k' : RecordKernelState) (t : Turn) (agent : CellId)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hnonce : nonceOf (k.cell agent) ≠ nonceOf (k'.cell agent))
    (hroot : recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t =
      recStateCommit (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k' t) :
    FaithfulBreak fold8 permW cmb compress compressN := by
  rcases commit_binds_nonce_faithful fold8 permW hW ctx cmb compress compressN RH hRest
      k k' t agent hwf hwf' hroot with hn | hb
  · exact absurd hn hnonce
  · exact hb

/-! ### The faithful commitment surface and the full cross-turn no-replay consumer. -/

/-- The deployed binding surface without impossible injectivity fields.  Its only structural
carrier is the rest-frame correspondence; every hash failure is returned as `FaithfulBreak`. -/
structure FaithfulCommitSurface where
  fold8 : AuthorityFold8
  permW : List Int → List Int
  width8 : Poseidon2Width8 permW
  ctx : RotatedContextProvider
  cmb : Int → Int → Int
  compress : Int → Int → Int
  compressN : List Int → Int
  RH : RecordKernelState → Int
  restFrame : RestHashIffFrame RH

noncomputable def FaithfulCommitSurface.commit (S : FaithfulCommitSurface)
    (k : RecordKernelState) (t : Turn) : Int :=
  recStateCommit (CH_faithful8 S.fold8 S.permW S.ctx) S.RH S.cmb S.compress S.compressN k t

abbrev FaithfulCommitSurface.Break (S : FaithfulCommitSurface) : Prop :=
  FaithfulBreak S.fold8 S.permW S.cmb S.compress S.compressN

theorem FaithfulCommitSurface.commit_binds_kernel (S : FaithfulCommitSurface)
    (k k' : RecordKernelState) (t : Turn) (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hroot : S.commit k t = S.commit k' t) : k = k' ∨ S.Break :=
  recStateCommit_binds_kernel_faithful S.fold8 S.permW S.width8 S.ctx
    S.cmb S.compress S.compressN S.RH
    S.restFrame k k' t hwf hwf' hroot

theorem FaithfulCommitSurface.commit_binds_nonce (S : FaithfulCommitSurface)
    (k k' : RecordKernelState) (t : Turn) (agent : CellId)
    (hwf : AccountsWF k) (hwf' : AccountsWF k') (hroot : S.commit k t = S.commit k' t) :
    nonceOf (k.cell agent) = nonceOf (k'.cell agent) ∨ S.Break :=
  commit_binds_nonce_faithful S.fold8 S.permW S.width8 S.ctx
    S.cmb S.compress S.compressN S.RH S.restFrame
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
    · exact nonce_difference_reduces S.fold8 S.permW S.width8 S.ctx
        S.cmb S.compress S.compressN S.RH S.restFrame
        (C.seq i) (C.seq j) t agent (C.wf i) (C.wf j) (ne_of_lt (C.nonceMono hlt)) hroot
    · have hn : nonceOf ((C.seq i).cell agent) ≠ nonceOf ((C.seq j).cell agent) :=
        ne_of_gt (C.nonceMono hgt)
      exact nonce_difference_reduces S.fold8 S.permW S.width8 S.ctx
        S.cmb S.compress S.compressN S.RH S.restFrame
        (C.seq i) (C.seq j) t agent (C.wf i) (C.wf j) hn hroot

/-- Exact recovery on the satisfiable local adversary-failure event.  It quantifies only the pairs
the supplied chain opens, never global nonexistence of finite-hash collisions. -/
theorem no_replay_faithful_on_adversary_failure {S : FaithfulCommitSurface}
    {agent : CellId} {t : Turn} (C : FaithfulCommitChain S agent t)
    (hNo : ∀ a b : Nat,
      ¬ KernelEquivocation S.fold8 S.permW S.ctx S.cmb S.compress S.compressN S.RH
        (C.seq a) (C.seq b) t)
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
theorem transfer_circuit_full_sound_faithful (fold8 : AuthorityFold8)
    (permW : List Int → List Int) (hW : Poseidon2Width8 permW)
    (ctx : RotatedContextProvider) (cmb compress : Int → Int → Int)
    (compressN : List Int → Int) (RH : RecordKernelState → Int)
    (hRest : RestHashIffFrame RH) (k : RecordKernelState) (t : Turn) (k' : RecordKernelState)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (h : satisfiedS cmb compress
      (encodeS (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t k')) :
    TransferSpec k t k' ∨ FaithfulBreak fold8 permW cmb compress compressN := by
  obtain ⟨hsat, _hcommit⟩ := h
  have e0 := encodeS_agrees_encodeT (CH_faithful8 fold8 permW ctx) RH cmb compress compressN
    k t k' vSrcPre (by decide)
  have e1 := encodeS_agrees_encodeT (CH_faithful8 fold8 permW ctx) RH cmb compress compressN
    k t k' vDstPre (by decide)
  have e2 := encodeS_agrees_encodeT (CH_faithful8 fold8 permW ctx) RH cmb compress compressN
    k t k' vSrcPost (by decide)
  have e3 := encodeS_agrees_encodeT (CH_faithful8 fold8 permW ctx) RH cmb compress compressN
    k t k' vDstPost (by decide)
  have e4 := encodeS_agrees_encodeT (CH_faithful8 fold8 permW ctx) RH cmb compress compressN
    k t k' vAmt (by decide)
  have e5 := encodeS_agrees_encodeT (CH_faithful8 fold8 permW ctx) RH cmb compress compressN
    k t k' vTAuth (by decide)
  have e6 := encodeS_agrees_encodeT (CH_faithful8 fold8 permW ctx) RH cmb compress compressN
    k t k' vTNonneg (by decide)
  have e7 := encodeS_agrees_encodeT (CH_faithful8 fold8 permW ctx) RH cmb compress compressN
    k t k' vTAvail (by decide)
  have e8 := encodeS_agrees_encodeT (CH_faithful8 fold8 permW ctx) RH cmb compress compressN
    k t k' vTDistinct (by decide)
  have e9 := encodeS_agrees_encodeT (CH_faithful8 fold8 permW ctx) RH cmb compress compressN
    k t k' vTSrcLive (by decide)
  have e10 := encodeS_agrees_encodeT (CH_faithful8 fold8 permW ctx) RH cmb compress compressN
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
      (encodeS (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t k') :=
    hsat cSRestFrame (by unfold stateCircuit; simp)
  have hframegate : cSFrameReuse.holds
      (encodeS (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t k') :=
    hsat cSFrameReuse (by unfold stateCircuit; simp)
  have hmovedgate : cSMovedBind.holds
      (encodeS (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t k') :=
    hsat cSMovedBind (by unfold stateCircuit; simp)
  have hRHeq : RH k = RH k' :=
    (srestframe_iff (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t k').mp hrestgate
  obtain ⟨hAcc, hCaps, hBal, hNul, hRev, hCom, hSC, hFac, hLif, hDC, hDel, hDgs,
    hDE, hDEA, hHeaps, hNR, hRR, hCR⟩ := (hRest k k').mp hRHeq
  have hfdeq : frameDigest (CH_faithful8 fold8 permW ctx) compressN k (frameCarrier k t) =
      frameDigest (CH_faithful8 fold8 permW ctx) compressN k' (frameCarrier k t) :=
    (sframereuse_iff (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t k').mp hframegate
  rcases StateCommitReduce.frameDigestBindsCells_orBreak
      (CH_faithful8 fold8 permW ctx) cmb compress compressN k k' (frameCarrier k t) hfdeq with
    hcellframe | hb
  · have hmoveq : movedDigest (CH_faithful8 fold8 permW ctx) compress k'.cell t.src t.dst =
        movedDigest (CH_faithful8 fold8 permW ctx) compress
          (recTransfer k.cell t.src t.dst t.amt) t.src t.dst :=
      (smovedbind_iff (CH_faithful8 fold8 permW ctx) RH cmb compress compressN k t k').mp hmovedgate
    rcases StateCommitReduce.movedDigestBindsCells_orBreak
        (CH_faithful8 fold8 permW ctx) cmb compress compressN k'.cell
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
    · exact Or.inr (stateBreak_faithful_reduces fold8 permW hW ctx cmb compress compressN hb)
  · exact Or.inr (stateBreak_faithful_reduces fold8 permW hW ctx cmb compress compressN hb)

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

def constantAuthorityFold8 : AuthorityFold8 := fun _ _ => 0

theorem constantAuthorityFold8_collision : AuthorityDigest8Collision constantAuthorityFold8 :=
  ⟨abstractA, abstractB, by
    intro h
    have hv : Value.int 0 = Value.int 1 := AuthorityInput.abstract.inj h
    have hi : (0 : Int) = 1 := Value.int.inj hv
    omega, rfl⟩

def constantWide : List Int → List Int := fun _ => List.replicate 8 0

theorem constantWide_width8 : Poseidon2Width8 constantWide := by
  intro xs
  simp [constantWide]

theorem constantWide_collision : WireCommit8Collision constantWide := by
  refine ⟨[0], [1], 0, 0, Or.inl (by decide), ?_⟩
  simp [wireCommitR8, constantWide]

theorem no_free_decode_gap (fold : AuthorityFold) :
    (∃ v w, LimbDecodeCollision fold v w) → AuthorityDigestCollision fold := by
  rintro ⟨v, w, h⟩
  exact limbDecodeCollision_reduces fold h

#assert_axioms plus4_collision
#assert_axioms constantAuthorityFold_collision
#assert_axioms constantAuthorityFold8_collision
#assert_axioms constantWide_width8
#assert_axioms constantWide_collision
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
