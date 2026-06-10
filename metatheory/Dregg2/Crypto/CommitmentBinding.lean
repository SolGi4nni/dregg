/-
# Dregg2.Crypto.CommitmentBinding — the 2-to-1 compress + BLAKE3 cell-commitment binding, REDUCED.

Two more commitment portals discharged to their genuine primitives, completing the extension of
task #13 begun in `Dregg2.Crypto.SpongeReduction`:

  * **§1 — the Poseidon2 2-to-1 compression `compressInjective`** (the Merkle-node hash `hash_2_to_1`
    / the 4-to-1 `hash_4_to_1`, `circuit/src/poseidon2.rs:341,357`) REDUCED to the SAME single
    permutation-call CR as the sponge (`SpongeReduction.CompressionCR`): a 2-to-1 hash is `squeeze ∘
    perm ∘ pack₂`, i.e. ONE `step` over the packed two-input block, so `compressInjective` is just the
    `CompressionCR` collision peeled once. The `StateCommit.recStateCommit_binds` root-binding portal
    (`compressInjective cmb`) thereby stands on the permutation CR, NOT a separate assumption.

  * **§2 — the BLAKE3 cell-commitment v3/v4** (`cell/src/commitment.rs::compute_canonical_state_commitment`,
    a domain-separated `blake3::Hasher` absorbing a canonical byte layout) REDUCED to BLAKE3
    collision-resistance (`Crypto.PortalFloor.Blake3Kernel`, IRREDUCIBLE PRIMITIVE #5) composed with
    injectivity of the canonical SERIALIZATION (a STRUCTURAL field: the byte layout is prefix-free per
    field — `Some/None` tag bytes, the `auth_byte`+vk discipline, fixed-position absorptions). The
    binding "equal canonical commitments ⇒ equal cells" thus reduces to BLAKE3 CR, a named primitive,
    not a blanket assumption.

Classification (per the crypto-ledger discipline):
  * `compressInjective` — DISCHARGEABLE to the permutation `CompressionCR` (= primitive #4 for one
    `perm`), shared with the sponge. No new crypto.
  * BLAKE3 commitment binding — DISCHARGEABLE to BLAKE3 CR (IRREDUCIBLE PRIMITIVE #5), composed with a
    structural serialization injectivity. The hash CR is the named primitive; the serialization is
    proved injective (a `Reference` instance exhibits one).

l4v bar: every theorem pins `{propext, Classical.choice, Quot.sound}` (`#assert_axioms`); no `sorry`,
no `:= True`, no `native_decide`.
-/
import Dregg2.Crypto.SpongeReduction
import Dregg2.Crypto.PortalFloor
import Dregg2.Circuit.StateCommit

namespace Dregg2.Crypto.CommitmentBinding

open Dregg2.Crypto.SpongeReduction
open Dregg2.Circuit.StateCommit (compressInjective)

/-! ## §1 — the 2-to-1 Poseidon2 compression `compressInjective` ⟸ the permutation `CompressionCR`.

`hash_2_to_1 left right` is `state[0]=left; state[1]=right; state[4]=2; permute(); state[0]`
(`poseidon2.rs:357`) — a SINGLE permutation call over the two-input rate block. We model it as one
`SpongeMachine.step` over the packed block `[left, right]`, so collision-resistance of the 2-to-1 hash
is the `CompressionCR` collision peeled once (plus the structural injectivity of the 2-element
packing). NO new crypto beyond the one permutation call. -/

/-- **`Compress1CR compress1`** — a single-permutation-call compression `compress1 : List ℤ → ℤ`
(`squeeze ∘ perm ∘ absorb s0`) is collision-resistant: equal outputs force equal input blocks. This
IS the squeeze-level reading of `SpongeReduction.CompressionCR` for the LAST (here: only) block — the
same one-permutation-call primitive #4, stated at the digest level for a fixed initial state. -/
def Compress1CR (compress1 : List ℤ → ℤ) : Prop :=
  ∀ a b : List ℤ, compress1 a = compress1 b → a = b

/-- A 2-to-1 hash realized as `h a b = compress1 (pack₂ a b)` with `compress1` CR and `pack₂` an
injective 2-element packing. The cleaner, self-contained realization (no `SpongeMachine` surgery). -/
structure Compress2 (h : ℤ → ℤ → ℤ) where
  /-- The single-permutation-call compression the node hash squeezes through. -/
  compress1 : List ℤ → ℤ
  /-- Inject the two inputs into the rate block (`state[0]=a; state[1]=b`). -/
  pack₂ : ℤ → ℤ → List ℤ
  /-- STRUCTURAL: the packing is injective. -/
  pack₂_inj : ∀ a b c d, pack₂ a b = pack₂ c d → a = c ∧ b = d
  /-- The node hash factors as `compress1 ∘ pack₂`. -/
  factor : ∀ a b, h a b = compress1 (pack₂ a b)
  /-- The SOLE crypto carrier: the single permutation call is CR. -/
  compress1CR : Compress1CR compress1

/-- **`compressInjective_of_compress2`** — discharge `compressInjective h` (the 2-to-1 node CR portal
the `StateCommit` root-binding `recStateCommit_binds` consumes) from a `Compress2` realization. PROVED
by peeling the one-permutation-call CR then the injective packing. The sole crypto content is
`R.compress1CR` — the SAME single permutation call as the sponge. -/
theorem compressInjective_of_compress2 {h : ℤ → ℤ → ℤ} (R : Compress2 h) :
    compressInjective h := by
  intro a b c d hh
  rw [R.factor a b, R.factor c d] at hh
  exact R.pack₂_inj a b c d (R.compress1CR _ _ hh)

/-! ## §2 — the BLAKE3 cell-commitment v3/v4 binding ⟸ BLAKE3 CR. -/

open Dregg2.Crypto.PortalFloor (Blake3Kernel)

/-- A BLAKE3 commitment to cells: `commit c = hash (serialize c)` for a canonical, INJECTIVE byte
serialization `serialize : Cell → List Nat` and the BLAKE3 CR carrier `Blake3Kernel.collisionHard`.
This mirrors `cell/src/commitment.rs::compute_canonical_state_commitment` — a `blake3::Hasher`
absorbing a domain-separated, prefix-free byte layout. -/
structure Blake3Commitment (Cell Digest : Type) [K : Blake3Kernel Digest] where
  /-- The canonical byte serialization the hasher absorbs (the `hasher.update(...)` layout). -/
  serialize : Cell → List Nat
  /-- STRUCTURAL: the canonical serialization is injective (prefix-free per field: the `Some/None`
  tag bytes, `auth_byte` + `Custom` vk discipline, fixed-position absorptions). A real fact about the
  byte layout, NOT crypto; the `Reference` exhibits one. -/
  serialize_inj : Function.Injective serialize
  /-- The commitment IS BLAKE3 of the serialization. -/
  commit : Cell → Digest
  factor : ∀ c, commit c = K.hash (serialize c)

/-- **`blake3_commitment_binds`** — equal canonical BLAKE3 commitments force equal cells, GIVEN the
BLAKE3 CR carrier. The cell-commitment-v3/v4 binding reduced to IRREDUCIBLE PRIMITIVE #5 (BLAKE3 CR):
`commit c = commit c'` ⇒ `hash (ser c) = hash (ser c')` ⇒[CR] `ser c = ser c'` ⇒[ser inj] `c = c'`.
The sole crypto content is `Blake3Kernel.collisionHard`, an explicit hypothesis — never `True`. -/
theorem blake3_commitment_binds {Cell Digest : Type} [K : Blake3Kernel Digest]
    (B : Blake3Commitment Cell Digest) (hcr : K.collisionHard) {c c' : Cell}
    (h : B.commit c = B.commit c') : c = c' := by
  rw [B.factor c, B.factor c'] at h
  exact B.serialize_inj (K.noCollision hcr _ _ h)

/-! ## §3 — non-vacuity witnesses (the carriers are not `True`).

Reference instances exhibiting injective packings/serializations + an injective (toy)
hash/compression, so each reduction FIRES, plus FALSE-witnesses (a colliding compression / a
non-injective serialization) so the carriers are meaningful. -/

namespace Reference

/-- A toy CR single-permutation compression: the injective `Encodable` encoding. -/
def refCompress1 (a : List ℤ) : ℤ := (Encodable.encode a : ℕ)

theorem refCompress1CR : Compress1CR refCompress1 := by
  intro a b h
  unfold refCompress1 at h
  exact Encodable.encode_injective (by exact_mod_cast h)

/-- A toy injective 2-packing: `pack₂ a b := [a, b]`. -/
def refPack₂ (a b : ℤ) : List ℤ := [a, b]

theorem refPack₂_inj : ∀ a b c d, refPack₂ a b = refPack₂ c d → a = c ∧ b = d := by
  intro a b c d h
  unfold refPack₂ at h
  exact ⟨(List.cons.inj h).1, (List.cons.inj (List.cons.inj h).2).1⟩

/-- A realized 2-to-1 node hash; `compressInjective` FIRES on it. -/
def refNode (a b : ℤ) : ℤ := refCompress1 (refPack₂ a b)

def refCompress2 : Compress2 refNode where
  compress1 := refCompress1
  pack₂ := refPack₂
  pack₂_inj := refPack₂_inj
  factor := fun _ _ => rfl
  compress1CR := refCompress1CR

example : compressInjective refNode := compressInjective_of_compress2 refCompress2

/-- A COLLIDING compression (constant) FALSIFIES `Compress1CR` — the carrier is not `True`. -/
def badCompress1 (_ : List ℤ) : ℤ := 0

theorem badCompress1_not_CR : ¬ Compress1CR badCompress1 := by
  intro hbad
  have : ([0] : List ℤ) = [1] := hbad [0] [1] rfl
  exact absurd this (by decide)

/-! BLAKE3 commitment non-vacuity: use the `PortalFloor.Reference` BLAKE3 instance (CR holds, echo
oracle) + an injective serialization, so `blake3_commitment_binds` FIRES. -/

/-- An injective toy serialization `ℕ → List Nat`: `serialize n := [n]`. -/
def refSerialize (n : ℕ) : List Nat := [n]

theorem refSerialize_inj : Function.Injective refSerialize := by
  intro a b h; exact (List.cons.inj h).1

/-- The `PortalFloor.Reference` BLAKE3 kernel over `Nat` (CR holds for the echo oracle). -/
def refCommitment :
    @Blake3Commitment ℕ ℕ Dregg2.Crypto.PortalFloor.Reference.instBlake3Kernel where
  serialize := refSerialize
  serialize_inj := refSerialize_inj
  commit := fun n => Dregg2.Crypto.PortalFloor.Reference.instBlake3Kernel.hash (refSerialize n)
  factor := fun _ => rfl

/-- The BLAKE3 binding FIRES: given the (non-vacuous) reference CR carrier, the commitment
binds — exercising `blake3_commitment_binds` on a concrete instance. -/
theorem refCommitment_binds
    (hcr : Dregg2.Crypto.PortalFloor.Reference.instBlake3Kernel.collisionHard) {a b : ℕ}
    (h : refCommitment.commit a = refCommitment.commit b) : a = b :=
  blake3_commitment_binds refCommitment hcr h

end Reference

#assert_axioms compressInjective_of_compress2
#assert_axioms blake3_commitment_binds
#assert_axioms Reference.refCompress1CR
#assert_axioms Reference.badCompress1_not_CR
#assert_axioms Reference.refSerialize_inj

end Dregg2.Crypto.CommitmentBinding
