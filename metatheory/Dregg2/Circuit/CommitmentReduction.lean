import Dregg2.Circuit.OodCommitmentBinding

/-!
# De-vacuating the commitment floor: binding as EXTRACTION, not injectivity

The deployed apex threads `Poseidon2SpongeCR sponge` (Poseidon2Binding.lean:178), stated as full
injectivity `∀ xs ys, sponge xs = sponge ys → xs = ys` — which `HashFloorHonesty.poseidon2SpongeCR_false_babyBear`
PROVES FALSE for any real BabyBear-valued sponge (pigeonhole: a compressing hash is never injective).
So every theorem of the form `Poseidon2SpongeCR sponge → P` is VACUOUS at deployment.

The honest, non-vacuous form is the REDUCTION: a Merkle opening either genuinely BINDS
(`vOpened = vCommitted`) or it hands you a CONCRETE COLLISION (`∃ xs ys, xs ≠ ys ∧ sponge xs = sponge ys`).
No `Poseidon2SpongeCR` premise, no false hypothesis — an adversary who breaks binding has *by construction*
produced a hash collision. This is exactly how hash-based commitment soundness is stated in the
literature ("breaking the commitment reduces to finding a collision"), and it de-vacuates the floor:
the security claim survives instantiation at the real hash, now reading "unfoolable UNLESS you find a
collision" instead of "unfoolable ASSUMING the hash is injective (which it isn't)".
-/

namespace Dregg2.Circuit.CommitmentReduction

open Dregg2.Circuit.OodCommitmentBinding
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-- **Opening equivocation EXTRACTS a concrete collision.** Two DISTINCT values recomputing the same
Merkle root over the same path yield an explicit witnessed sponge collision — no `Poseidon2SpongeCR`
hypothesis. This is `opening_equivocation_breaks_cr` read as a constructive extractor: `¬injective`
unfolds to `∃ xs ys, sponge xs = sponge ys ∧ xs ≠ ys`. -/
theorem equivocation_extracts_collision (sponge : List ℤ → ℤ)
    {root : ℤ} {idx : Nat} {siblings : List ℤ} {vCommitted vOpened : ℤ}
    (hne : vOpened ≠ vCommitted)
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened    : merkleRecomputeZ sponge idx vOpened    siblings = root) :
    ∃ xs ys : List ℤ, xs ≠ ys ∧ sponge xs = sponge ys := by
  have hbreak : ¬ Poseidon2SpongeCR sponge :=
    opening_equivocation_breaks_cr sponge hne hCommitted hOpened
  unfold Poseidon2SpongeCR at hbreak
  push_neg at hbreak
  obtain ⟨xs, ys, heq, hxy⟩ := hbreak
  exact ⟨xs, ys, hxy, heq⟩

/-- **The commitment opening BINDS or EXTRACTS a collision — unconditionally.** The honest, non-vacuous
replacement for `commitmentOpening_binds_of_poseidon2CR` (which needs the false injectivity premise):
for ANY two openings to a common root over the same path, EITHER they agree (`vOpened = vCommitted`,
the honest case) OR the disagreement is itself a concrete sponge collision. No `Poseidon2SpongeCR`
hypothesis — this dichotomy holds at the real deployed hash. -/
theorem commitmentOpening_binds_or_collision (sponge : List ℤ → ℤ)
    {root : ℤ} {idx : Nat} {siblings : List ℤ} {vCommitted vOpened : ℤ}
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened    : merkleRecomputeZ sponge idx vOpened    siblings = root) :
    vOpened = vCommitted ∨ ∃ xs ys : List ℤ, xs ≠ ys ∧ sponge xs = sponge ys := by
  by_cases h : vOpened = vCommitted
  · exact Or.inl h
  · exact Or.inr (equivocation_extracts_collision sponge h hCommitted hOpened)

/-- **The reduction is LOAD-BEARING, not vacuous (both directions witnessed).** On the injective toy
sponge the opening binds (the honest branch fires); on a colliding sponge the collision branch fires
with a real witness. Stated abstractly here: if the sponge has NO collision on the relevant inputs,
the dichotomy forces binding — i.e. the collision branch cannot be spuriously taken. -/
theorem binds_of_no_collision (sponge : List ℤ → ℤ)
    {root : ℤ} {idx : Nat} {siblings : List ℤ} {vCommitted vOpened : ℤ}
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened    : merkleRecomputeZ sponge idx vOpened    siblings = root)
    (hNoColl : ∀ xs ys : List ℤ, sponge xs = sponge ys → xs = ys) :
    vOpened = vCommitted :=
  (commitmentOpening_binds_or_collision sponge hCommitted hOpened).elim id
    (fun ⟨xs, ys, hxy, heq⟩ => absurd (hNoColl xs ys heq) hxy)

/-! ## The 2-to-1 combiner (`cmb`/`compress`, the state-commitment `CommitSurface` carriers)

`CommitSurface` (CircuitSoundness.lean:114) bundles `compressInjective cmb`/`compressInjective compress`
as structure FIELDS, and StateCommit.lean:208 flags them "⚠ BROKEN/VACUOUS FOR A RANGE-BOUNDED
COMPRESSION" (two field elements do not fit in one output). Same disease, same cure: the reduction form. -/

/-- **The 2-to-1 combiner BINDS or EXTRACTS a collision.** For any `h a b = h c d`, EITHER the arguments
agree (`a = c ∧ b = d`, the honest binding) OR the disagreement is a concrete collision of `h`. No
`compressInjective h` premise — the honest, non-vacuous replacement for the `cmbInj`/`compInj`
`CommitSurface` fields, valid at the real range-bounded combiner. -/
theorem compress_binds_or_collision (h : ℤ → ℤ → ℤ) {a b c d : ℤ}
    (heq : h a b = h c d) :
    (a = c ∧ b = d) ∨ ∃ p q : ℤ × ℤ, p ≠ q ∧ h p.1 p.2 = h q.1 q.2 := by
  by_cases hbind : a = c ∧ b = d
  · exact Or.inl hbind
  · refine Or.inr ⟨(a, b), (c, d), ?_, heq⟩
    intro hpq
    exact hbind ⟨(Prod.mk.injEq .. ▸ hpq).1, (Prod.mk.injEq .. ▸ hpq).2⟩

/-- The combiner reduction is load-bearing: no-collision ⇒ it binds (⇒ `compressInjective h`). -/
theorem compress_binds_of_no_collision (h : ℤ → ℤ → ℤ) {a b c d : ℤ}
    (heq : h a b = h c d)
    (hNoColl : ∀ p q : ℤ × ℤ, h p.1 p.2 = h q.1 q.2 → p = q) :
    a = c ∧ b = d :=
  (compress_binds_or_collision h heq).elim id
    (fun ⟨p, q, hpq, hcol⟩ => absurd (hNoColl p q hcol) hpq)

/-! ## §ROM — ⚑ THE ROM SUCCESSORS: both bindings as REDUCTIONS on the PROVED keyed floor.

⚑ STATUS OF THE TWO DISJUNCTIONS (2026-07-24). `commitmentOpening_binds_or_collision` and
`compress_binds_or_collision` are EXTRACTOR WITNESSES — each hands back the specific colliding pair
— but as EXPORTED security statements they are shirks: at deployed BabyBear parameters a collision
EXISTS by pigeonhole, so each disjunction holds through its right branch with NO binding (the
module header's own "unfoolable UNLESS you find a collision" reading over-claims: at ~31 bits a
collision is a `2^15.5` birthday search, and the disjunction does not even demand the search). The
security statements are the `…_binds_rom` reductions: forger = oracle program fixed before the
oracle is sampled, floor = `keyedRom_hard` (the birthday bound, a THEOREM). The disjunctions are
RETAINED for their downstream `rcases` consumers (`CollisionReduce`, `StarkSoundReduce` — other
lanes' files), whose re-point is the remaining mechanical work. -/

section RomSuccessor

open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomBindingReduction (RomCarrier romCarrierGame RomCarrierEff)
open Dregg2.Crypto.RomCarrierSites
  (flatFamily flatSite_binds taggedCarrier babyBearP babyBearP_pos RomForgeryEff)
open Dregg2.Crypto.RomMerkleOpening (nodeMsg)
open Dregg2.Crypto.SpongeCarrierReduction (SpongeKeyed)
open Dregg2.Crypto.FloorGames (Adversary gameAdv)
open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)

/-- **THE ORDER PIN** — the deployed `nodeStep` list `[acc, s]`/`[s, acc]` carries exactly the
kit's ordered `nodeMsg` pair at the bit `idx % 2 ≠ 0`: the ROM opening game absorbs the SAME
ordered limbs the deployed `merkleRecomputeZ` absorbs. -/
theorem nodeStep_matches_nodeMsg (sponge : List ℤ → ℤ) (idx : Nat) (acc s : ℤ) :
    nodeStep sponge idx acc s
      = [(nodeMsg (decide (idx % 2 ≠ 0)) acc s).1, (nodeMsg (decide (idx % 2 ≠ 0)) acc s).2] := by
  by_cases hb : idx % 2 = 0 <;> simp [nodeStep, nodeMsg, hb]

/-- **⚑⚑ THE COMMITMENT-OPENING BINDING, AS A REDUCTION ON THE PROVED FLOOR** — the ROM successor
of `commitmentOpening_binds_or_collision`: a query-bounded prover that opens ONE committed root at
one shared (index-bit, sibling) path of pinned depth `d` to TWO DISTINCT values has NEGLIGIBLE
advantage. This is `OodCommitmentBinding.merkleOpening_binds_rom` — the walking extractor pays
`2·d` queries, the floor is `keyedRom_hard` (birthday), NOTHING refutable is carried — named at
THIS site because this module's disjunction states the same break. The order pin above ties the
game's node absorb to the deployed `nodeStep`. -/
theorem commitmentOpening_binds_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (d Q Q' : ℕ → ℕ) (hle : ∀ l, Q l + 2 * d l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (Dregg2.Crypto.RomMerkleOpening.merkleOpenRomGame
      D.Tag D.tagFintype tagDec D.tagNonempty d))
    (hA : RomForgeryEff
      (Dregg2.Crypto.RomMerkleOpening.merkleRomFamily D.Tag D.tagFintype tagDec D.tagNonempty)
      (Dregg2.Crypto.RomMerkleOpening.merkleOpenForgery D.Tag D.tagFintype tagDec D.tagNonempty d)
      Q A) :
    Negl (gameAdv (Dregg2.Crypto.RomMerkleOpening.merkleOpenRomGame
      D.Tag D.tagFintype tagDec D.tagNonempty d) A) :=
  Dregg2.Circuit.OodCommitmentBinding.merkleOpening_binds_rom D tagDec d Q Q' hle hQ' A hA

/-- The truncated 2-to-1 combiner pair — the deployed `cmb`/`compress` absorb at BabyBear range. -/
abbrev CompressRomPair : Type := Fin babyBearP × Fin babyBearP

/-- The 2-to-1 combiner ROM family at tag space `Key`. -/
abbrev compressRomFamily (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) : KeyedRomFamily :=
  flatFamily Key kF kD kN (fun _ => CompressRomPair)
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => ⟨(⟨0, babyBearP_pos⟩, ⟨0, babyBearP_pos⟩)⟩)

/-- The combiner carrier — the identity embedding of the ordered pair; injective on the nose. -/
abbrev compressRomCarrier (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) : RomCarrier (compressRomFamily Key kF kD kN) :=
  taggedCarrier _ (fun _ => Unit) (fun _ => CompressRomPair) (fun _ => inferInstance)
    (fun _ _ v => v) (fun _ _ _ _ h => h)

/-- **⚑⚑ THE 2-TO-1 COMBINER BINDING, AS A REDUCTION ON THE PROVED FLOOR** — the ROM successor of
`compress_binds_or_collision` (and of the `CommitSurface` `cmbInj`/`compInj` fields it replaced):
every query-bounded forger that equivocates one combiner output between two DISTINCT ordered pairs
has NEGLIGIBLE advantage. NO bare disjunction, NO injectivity premise — `flatSite_binds`, hence
`keyedRom_hard`. -/
theorem compress_binds_rom (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (romCarrierGame (compressRomFamily Key kF kD kN)
      (compressRomCarrier Key kF kD kN)))
    (hA : RomCarrierEff (compressRomFamily Key kF kD kN)
      (compressRomCarrier Key kF kD kN) Q A) :
    Negl (gameAdv (romCarrierGame (compressRomFamily Key kF kD kN)
      (compressRomCarrier Key kF kD kN)) A) :=
  flatSite_binds Key kF kD kN _ _ _ _ (compressRomCarrier Key kF kD kN) Q hQ A hA

end RomSuccessor

#assert_axioms equivocation_extracts_collision
#assert_axioms commitmentOpening_binds_or_collision
#assert_axioms binds_of_no_collision
#assert_axioms compress_binds_or_collision
#assert_axioms compress_binds_of_no_collision
-- §ROM — the ROM successors (reductions on the proved keyed floor; no bare disjunction).
#assert_axioms nodeStep_matches_nodeMsg
#assert_axioms commitmentOpening_binds_rom
#assert_axioms compress_binds_rom

end Dregg2.Circuit.CommitmentReduction
