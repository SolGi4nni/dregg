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

l4v bar: every theorem pins `{propext, Classical.choice, Quot.sound}` (`#assert_axioms`).
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

/-- **`Compress1CR compress1`** — ⚠ **BROKEN / VACUOUS FOR A RANGE-BOUNDED COMPRESSION.**
Stated as injectivity of `List ℤ → ℤ`, which is FALSE by cardinality
(`Crypto.FactoryBindingFloorRegrounded.compress1CR_false_babyBear`) — `List ℤ` is infinite and a BabyBear
squeeze is one bounded field element. It is the same predicate as the already-flagged
`StateCommit.compressNInjective` / `Poseidon2Binding.Poseidon2SpongeCR`, and it shares their fate.

⚑ **IT USED TO BE THE `Compress2.compress1CR` FIELD, AND THAT MADE `Compress2` UNINHABITABLE** — not
merely a hypothesis on a theorem but a non-constructible field, so EVERY theorem of the form
`∀ R : Compress2 h, …` was VACUOUS, and this file's own §1 headline (*"the
`StateCommit.recStateCommit_binds` root-binding portal thereby stands on the permutation CR, NOT a
separate assumption"*) stood, at BabyBear, on nothing. **The field is DELETED (§1, 2026-07-25 bundle
cutover)**; `Compress2` now carries the compression and nothing false about it, §1.1 exhibits the real
deployed inhabitant `deployedCompress2`, and
`FactoryBindingFloorRegrounded.deployedCompress2_compress1_not_Compress1CR` proves that inhabitant's
own compression refutes the deleted field. The old "non-vacuity" argument (`Reference.refCompress2`
exhibits an injective compression) was exactly the FALSE COMFORT: toy witness satisfiable, real
compressing Poseidon2 false.

**WHAT `Compress1CR` IS RETAINED FOR — two honest jobs, neither a deployed keystone:** the INJECTIVE
SPECIAL CASE bridge (`compress1Coll_refutable_of_injective`, which shows the deleted theorem falls
straight out once you assume it, so nothing genuinely proved was surrendered), and its role as a
hypothesis at the call sites of consumers that have not yet been cut over. It is a FIELD OF NOTHING.

⚑ Honest replacement: `Crypto.FactoryBindingFloorRegrounded.compress2_node_advantage_bound` — a node-hash
collision finder reduces (by the injective packing) to a `compress1` collision finder, negligible under
`FloorGames.HashCRHardQuant _ Eff` at an EXPLICIT adversary class. NO new crypto: the sole content is
still the ONE permutation call (primitive #4), now stated as something an adversary must FIND. NOT
`HashFloorHonesty.CollisionResistant`, which is that floor at `⊤` and itself false
(`FloorGames.hashCRHardQuant_top_false_of_compressing`).

As originally intended: a single-permutation-call compression `compress1 : List ℤ → ℤ`
(`squeeze ∘ perm ∘ absorb s0`) is collision-resistant: equal outputs force equal input blocks. The
squeeze-level reading of `SpongeReduction.CompressionCR` for the LAST (here: only) block — the same
one-permutation-call primitive #4, stated at the digest level for a fixed initial state. -/
def Compress1CR (compress1 : List ℤ → ℤ) : Prop :=
  ∀ a b : List ℤ, compress1 a = compress1 b → a = b

/-- **`Compress1Coll compress1 p`** — the SPECIFIC pair of input blocks `p` is a GENUINE collision of
the single permutation call: DISTINCT blocks with the SAME squeeze. The named disjunct that replaces
the deleted `compress1CR` field.

Note what this is NOT: not `∃ a b, compress1 a = compress1 b ∧ a ≠ b`, which at deployed parameters is
UNCONDITIONALLY TRUE by pigeonhole (`FactoryBindingFloorRegrounded.compress1CR_false_babyBear` proves
exactly that) and would therefore be a free pass. It is a predicate about the pair an extractor
RETURNS, and it is REFUTABLE (`compress1Coll_refutable_of_injective`). The
`Poseidon2Binding.SpongeColl` / `DeployedCapTree.Coll8` shape at primitive #4. -/
def Compress1Coll (compress1 : List ℤ → ℤ) (p : List ℤ × List ℤ) : Prop :=
  p.1 ≠ p.2 ∧ compress1 p.1 = compress1 p.2

/-- "Is this pair a genuine collision?" is DECIDABLE, so the extractor stays a TOTAL function with no
`Classical.choice` in the reduction. -/
instance decidableCompress1Coll (compress1 : List ℤ → ℤ) (p : List ℤ × List ℤ) :
    Decidable (Compress1Coll compress1 p) := by
  unfold Compress1Coll
  infer_instance

/-- A 2-to-1 hash realized as `h a b = compress1 (pack₂ a b)` with `pack₂` an injective 2-element
packing. The cleaner, self-contained realization (no `SpongeMachine` surgery).

⚑ **THE `compress1CR` FIELD IS DELETED (2026-07-25 bundle cutover), AND THE BUNDLE IS NOW INHABITED.**
It carried `Compress1CR compress1` — injectivity of a map from the infinite `List ℤ` into ONE bounded
BabyBear felt, which `FactoryBindingFloorRegrounded.compress1CR_false_babyBear` REFUTES for every real
`hash_2_to_1`. So no deployed `Compress2` value could be constructed, every `∀ R : Compress2 h, …`
theorem was VACUOUS, and this file's own §1 headline (*"the root-binding portal thereby stands on the
permutation CR, NOT a separate assumption"*) was, at deployed parameters, standing on nothing.
`deployedCompress2` (§1.1) is a real value whose `compress1` is deployed-shaped and therefore REFUTES
the deleted field (`FactoryBindingFloorRegrounded.deployedCompress2_compress1_not_Compress1CR`). The
collision resistance the bundle used to assume is now EXTRACTED AS DATA — see `Compress1Coll` and
`compressInjective_of_compress2_or_collides`.

Design decision + rationale for the whole bundle family: `Dregg2.Shielded.RealCrypto` §2.0. -/
structure Compress2 (h : ℤ → ℤ → ℤ) where
  /-- The single-permutation-call compression the node hash squeezes through. -/
  compress1 : List ℤ → ℤ
  /-- Inject the two inputs into the rate block (`state[0]=a; state[1]=b`). -/
  pack₂ : ℤ → ℤ → List ℤ
  /-- STRUCTURAL: the packing is injective. -/
  pack₂_inj : ∀ a b c d, pack₂ a b = pack₂ c d → a = c ∧ b = d
  /-- The node hash factors as `compress1 ∘ pack₂`. -/
  factor : ∀ a b, h a b = compress1 (pack₂ a b)

/-- **⚑ THE EXTRACTOR (TOTAL).** On a node-hash equivocation, the two rate blocks the single
permutation call actually absorbed. No search, no choice: `factor` says the node hash IS `compress1`
of these blocks, so they are the candidate collision. -/
def Compress2.nodeCollFind {h : ℤ → ℤ → ℤ} (R : Compress2 h) (a b c d : ℤ) : List ℤ × List ℤ :=
  (R.pack₂ a b, R.pack₂ c d)

/-- **`compressInjective_of_compress2_or_collides` — UNCONDITIONAL.** Equal 2-to-1 node images EITHER
force the two input pairs equal, OR the packed blocks `nodeCollFind` hands back ARE a genuine collision
of the single permutation call. No injectivity hypothesis anywhere — this holds OF the deployed
`hash_2_to_1`, which the `compress1CR`-carrying original never did. -/
theorem compressInjective_of_compress2_or_collides {h : ℤ → ℤ → ℤ} (R : Compress2 h)
    {a b c d : ℤ} (hh : h a b = h c d) :
    (a = c ∧ b = d) ∨ Compress1Coll R.compress1 (R.nodeCollFind a b c d) := by
  rw [R.factor a b, R.factor c d] at hh
  by_cases hp : R.pack₂ a b = R.pack₂ c d
  · exact Or.inl (R.pack₂_inj a b c d hp)
  · exact Or.inr ⟨hp, hh⟩

/-- **`compressInjective_of_compress2`** — discharge `compressInjective h` (the 2-to-1 node CR portal
the `StateCommit` root-binding `recStateCommit_binds` consumes) from a `Compress2` realization. SAME
NAME, SAME CONCLUSION as the version that projected the deleted `compress1CR` field; the crypto content
is now a PER-INSTANCE side condition at the EXACT blocks the proof is about.

STRICTLY STRONGER than the original: the deleted `compress1CR` field discharges this hypothesis at
every pair (`compress1Coll_refutable_of_injective`), so anything the old form proved this one proves
too — and unlike the old form it can be instantiated at `deployedCompress2`. -/
theorem compressInjective_of_compress2 {h : ℤ → ℤ → ℤ} (R : Compress2 h)
    (hnc : ∀ a b c d : ℤ, ¬ Compress1Coll R.compress1 (R.nodeCollFind a b c d)) :
    compressInjective h := by
  intro a b c d hh
  exact (compressInjective_of_compress2_or_collides R hh).resolve_right (hnc a b c d)

/-! ### Strength bridges — standalone, deliberately NOT hypotheses on any keystone. -/

/-- **⚑ THE NO-STRENGTH-LOST TOOTH.** Under exactly the injectivity the deleted field asserted, the
collision disjunct is impossible and the plain equality falls straight out — so every theorem that used
to stand on `Compress2.compress1CR` is EXACTLY the injective special case of its cured form. Nothing
genuinely proved was given up; what was given up is the pretence that the deployed `hash_2_to_1`
satisfies the field. -/
theorem compress1Coll_refutable_of_injective {c1 : List ℤ → ℤ} (hCR : Compress1CR c1)
    (p : List ℤ × List ℤ) : ¬ Compress1Coll c1 p := by
  rintro ⟨hne, himg⟩
  exact hne (hCR _ _ himg)

/-- **(CANARY — the collision branch is REACHABLE.)** A degenerate compression genuinely collides, so
`Compress1Coll` is not accidentally empty and the disjunction is informative in both directions. -/
theorem badCompress1Coll_reachable : Compress1Coll (fun _ => 0) ([0], [1]) := ⟨by decide, rfl⟩

/-! ### §1.1 — ⚑ THE ACCEPTANCE TEST: a REAL DEPLOYED `Compress2` VALUE.

With `compress1CR` present, `Compress2` had NO deployed inhabitant, so every theorem over it was
vacuously true and the only witness on offer was `Reference.refCompress2`'s unbounded
`Encodable.encode`. `deployedCompress2` is a VALUE whose `compress1` is deployed-shaped in the only
respect the vacuity argument turned on: an arbitrary-length `List ℤ` squeezed into ONE felt reduced
into `[0, p)`, exactly like the real `poseidon2.rs:357` `hash_2_to_1`. Its own `compress1` REFUTES the
deleted field — see `FactoryBindingFloorRegrounded.deployedCompress2_compress1_not_Compress1CR`, which
is where the falsifier is in scope. -/

/-- **A DEPLOYED-SHAPED single-permutation compression.** Arbitrary-length rate block in, ONE BabyBear
felt out (`p = 2³¹ − 2²⁷ + 1`) — the shape `compress1CR_false_babyBear` refutes injectivity for. -/
def deployedShapedCompress1 (xs : List ℤ) : ℤ :=
  (xs.foldl (fun acc x => (acc * 31 + x) % 2013265921) 2) % 2013265921

/-- Every output of the deployed-shaped compression lands in `[0, p)` — the hypothesis the refutation
tooth consumes. -/
theorem deployedShapedCompress1_bounded (xs : List ℤ) :
    0 ≤ deployedShapedCompress1 xs ∧ deployedShapedCompress1 xs < (2013265921 : ℤ) :=
  ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

/-- The deployed-shaped 2-to-1 node hash: one permutation call over the packed rate block. -/
def deployedShapedNode (a b : ℤ) : ℤ := deployedShapedCompress1 [a, b]

/-- ⚑ **THE CONSTRUCTED INHABITANT — a real deployed `Compress2` VALUE.** This term is what the old
structure could not have; every theorem above now has a deployed instance to be applied at. -/
def deployedCompress2 : Compress2 deployedShapedNode where
  compress1 := deployedShapedCompress1
  pack₂ := fun a b => [a, b]
  pack₂_inj := by
    intro a b c d h
    exact ⟨(List.cons.inj h).1, (List.cons.inj (List.cons.inj h).2).1⟩
  factor := fun _ _ => rfl

/-- The inhabitant's compression IS the deployed-shaped one (definitional — the projection fires). -/
theorem deployedCompress2_compress1 : deployedCompress2.compress1 = deployedShapedCompress1 := rfl

/-- ⚑ **THE TOOTH FIRES AT THE INHABITANT.** The node anti-equivocation, INSTANTIATED at a real
deployed value — the operation the `∀ R : Compress2 h` form could never be performed for. -/
theorem deployed_node_binds_or_collides {a b c d : ℤ}
    (hh : deployedShapedNode a b = deployedShapedNode c d) :
    (a = c ∧ b = d)
    ∨ Compress1Coll deployedCompress2.compress1 (deployedCompress2.nodeCollFind a b c d) :=
  compressInjective_of_compress2_or_collides deployedCompress2 hh

-- The inhabitant RUNS: its node digest is a genuine BabyBear-range felt ...
#guard 0 ≤ deployedShapedNode 5 7 && deployedShapedNode 5 7 < 2013265921

-- ... and distinct input pairs MOVE it (non-vacuity at the constructed value).
#guard deployedShapedNode 5 7 != deployedShapedNode 9 9

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

/-- At the reference (injective) compression NO pair is a collision, so the per-instance side
condition `compressInjective_of_compress2` now carries is DISCHARGED here rather than assumed — the
`example` below is unchanged by the cure. ⚑ Honest scope, unchanged from before: `refCompress1` is
`Encodable.encode`, whose range is NOT field-bounded; it is the toy witness, not the deployed
`hash_2_to_1`. The deployed instance is `deployedCompress2`, where the side condition is real content. -/
theorem refCompress2_no_coll (p : List ℤ × List ℤ) : ¬ Compress1Coll refCompress2.compress1 p :=
  compress1Coll_refutable_of_injective refCompress1CR p

example : compressInjective refNode :=
  compressInjective_of_compress2 refCompress2 (fun _ _ _ _ => refCompress2_no_coll _)

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
#assert_axioms compressInjective_of_compress2_or_collides
#assert_axioms compress1Coll_refutable_of_injective
#assert_axioms badCompress1Coll_reachable
#assert_axioms deployed_node_binds_or_collides
#assert_axioms blake3_commitment_binds
#assert_axioms Reference.refCompress1CR
#assert_axioms Reference.badCompress1_not_CR
#assert_axioms Reference.refSerialize_inj

end Dregg2.Crypto.CommitmentBinding
