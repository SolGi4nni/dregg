/-
# `Dregg2.Circuit.RotatedPerCellBindsOrCollides` — the unified P0-2 closure, FLOOR-FREE ON BOTH LEGS.

⚑ THE CONSUMER FLIP of the light-client soundness-weld de-vacuuming (2026-08-01), completing the
2026-07-31 SITE-2 work. `RotatedCommitBindsOrCollides`'s own header named this as the point of that
module: "these make the rotated leg match, so the unified P0-2 closure can be restated floor-free on
BOTH commitment shapes." This is that restatement.

## WHAT MOVED, AND WHY THE OLD ONE IS GONE

`RotatedCommitDifferential.rotated_and_perCell_both_bind_authority_residue` stated the closure with a
HALF-FLOORED body: its per-cell leg was already floor-free (`≠ ∨ Coll4`, off
`CommitDifferential.effectVmCommit_binds_record_digest_or_collides`), but its rotated leg was a bare
`≠` bought with `hCRN : Poseidon2SpongeCR hash` — a hypothesis
`Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear` PROVES FALSE at deployed BabyBear width.
So at deployment the conjunction was true-but-empty in exactly the half that carries the headline: a
Mina settlement certified the AIR's arithmetic, not that a permission-flip / VK-swap / dropped-root
MOVES the published `OLD_COMMIT`/`NEW_COMMIT`.

The floored version is DELETED, not kept beside this one — along with the four floored binding twins
it rode (`rotatedCommit_binds_{limbs,authority_digest,cap_root,commitments_root}`), whose only
consumer in the whole tree it was. Two shapes that agree today are two shapes that will disagree
later, and a vacuous-at-deployment theorem is worse than absent because the next reader trusts it.

## WHY IT LIVES HERE AND NOT IN `RotatedCommitDifferential`

Import direction. `RotatedCommitBindsOrCollides` imports `RotatedCommitDifferential` (it reuses that
module's `rotatedCommit` / `rotatedLimbs` / the `[i]?`-index pins), so the flipped consumer — which
needs the `_or_collides` teeth — cannot sit in the module it flips away from without a cycle. It sits
one level above both instead, which is also where a composed closure over TWO commitment shapes
belongs.

## THE STATEMENT (both legs now the same shape)

A change to the SHARED authority residue felt `d ≠ d'` — the value the deployed code computes ONCE as
`dregg_cell::commitment::compute_authority_digest_felt(cell)` and feeds to BOTH the per-cell
`record_digest` (fixed index 12) and the rotated `pre_limbs[24]` — either MOVES each commitment, or
the prover HANDS BACK a genuine collision in the deployed hash at NAMED arguments: a `Coll4` at the
two `rootQuad`s on the per-cell side, a `WireColl1` at the two limb lists the total extractor returns
on the rotated side. No hypothesis on `h4`, none on `hash`. This is the deployed-hash content the
floored conjunction only asserted vacuously.

Discipline: sorry-free; the proof is the floored body with `rotatedCommit_binds_authority_digest hash
hCRN` replaced by `rotatedCommit_binds_authority_digest_or_collides hash` under the same `by_cases`
peel the per-cell leg already used, so the two legs are now literally the same three lines. No
BabyBear arithmetic computed.

⚠ SCOPE. This removes a REFUTED-AT-DEPLOYMENT hypothesis; it does not discharge the residuals. The
disjuncts are real obligations: the closure says a forger must exhibit an actual collision in the
deployed sponge, not that none exists. The FRI/STARK floor under the settlement is untouched.
-/
import Dregg2.Circuit.RotatedCommitBindsOrCollides

namespace Dregg2.Circuit.RotatedPerCellBindsOrCollides

open Dregg2.Circuit.RotatedCommitDifferential (rotatedCommit rotatedLimbs)
open Dregg2.Circuit.RotatedCommitBindsOrCollides (rotatedCommit_binds_authority_digest_or_collides)
open Dregg2.Circuit.Emit.WireCommitBindsOrCollides (WireColl1)

set_option autoImplicit false

/-- **`rotated_and_perCell_both_bind_authority_residue_or_collides`** — the unified P0-2 closure,
FLOOR-FREE ON BOTH LEGS. A change to the SHARED authority residue felt (`compute_authority_digest_felt`,
fed to the per-cell `record_digest` AND the rotated `pre_limbs[24]`) MOVES the per-cell commitment AND
the published rotated commitment — or the prover exhibits a genuine collision in the deployed hash at
the NAMED arguments each extractor returns. The floor-free successor to
`RotatedCommitDifferential.rotated_and_perCell_both_bind_authority_residue`, which bought its rotated
leg with the BabyBear-refuted `Poseidon2SpongeCR` and is deleted. -/
theorem rotated_and_perCell_both_bind_authority_residue_or_collides
    -- per-cell side
    (h4 : ℤ → ℤ → ℤ → ℤ → ℤ)
    (balLo balHi nonce : ℤ) (pcFields : Fin 8 → ℤ) (pcCapRoot : ℤ)
    -- rotated side (no `Poseidon2SpongeCR` carrier — that is the point)
    (hash : List ℤ → ℤ)
    (cellsRoot r0 r1 r2 : ℤ) (rFields : Fin 8 → ℤ)
    (r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 : ℤ)
    (capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot iroot : ℤ)
    -- the SHARED authority residue felt and a tampered one
    (d d' : ℤ) (hd : d ≠ d') :
    -- per-cell commitment moves — or the deployed `hash_4_to_1` collides at two NAMED quads
    (Dregg2.Circuit.CommitDifferential.effectVmCommit h4 balLo balHi nonce pcFields pcCapRoot d
       ≠ Dregg2.Circuit.CommitDifferential.effectVmCommit h4 balLo balHi nonce pcFields pcCapRoot d'
     ∨ Dregg2.Circuit.CommitDifferential.Coll4 h4
         (Dregg2.Circuit.CommitDifferential.rootQuad h4 balLo balHi nonce pcFields pcCapRoot d)
         (Dregg2.Circuit.CommitDifferential.rootQuad h4 balLo balHi nonce pcFields pcCapRoot d'))
    -- AND the published rotated commitment moves — or the deployed sponge collides at two NAMED lists
    ∧ (rotatedCommit hash
        (rotatedLimbs cellsRoot r0 r1 r2 rFields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
          d capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot) iroot
      ≠ rotatedCommit hash
        (rotatedLimbs cellsRoot r0 r1 r2 rFields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
          d' capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot) iroot
     ∨ WireColl1 hash
        (rotatedLimbs cellsRoot r0 r1 r2 rFields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
          d capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot) iroot
        (rotatedLimbs cellsRoot r0 r1 r2 rFields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
          d' capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot) iroot) := by
  constructor
  · -- either the per-cell commitment already moved, or the unconditional tooth hands back the
    -- collision the deployed `hash_4_to_1` would have to have.
    by_cases hpc : Dregg2.Circuit.CommitDifferential.effectVmCommit h4 balLo balHi nonce pcFields
        pcCapRoot d
      = Dregg2.Circuit.CommitDifferential.effectVmCommit h4 balLo balHi nonce pcFields pcCapRoot d'
    · rcases Dregg2.Circuit.CommitDifferential.effectVmCommit_binds_record_digest_or_collides
        h4 balLo balHi nonce pcFields pcCapRoot d d' hpc with hdd | hcoll
      · exact absurd hdd hd
      · exact Or.inr hcoll
    · exact Or.inl hpc
  · -- the SAME peel on the rotated side, now that the rotated tooth is floor-free too.
    by_cases hrot : rotatedCommit hash
        (rotatedLimbs cellsRoot r0 r1 r2 rFields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
          d capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot) iroot
      = rotatedCommit hash
        (rotatedLimbs cellsRoot r0 r1 r2 rFields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
          d' capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot) iroot
    · rcases rotatedCommit_binds_authority_digest_or_collides hash cellsRoot r0 r1 r2 rFields
        r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 d d' capRoot nullifierRoot commitmentsRoot
        heapRoot lifecycle epoch committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot
        iroot hrot with hdd | hcoll
      · exact absurd hdd hd
      · exact Or.inr hcoll
    · exact Or.inl hrot

#assert_axioms rotated_and_perCell_both_bind_authority_residue_or_collides

end Dregg2.Circuit.RotatedPerCellBindsOrCollides
