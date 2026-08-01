/-
# `Dregg2.Circuit.RotatedCommitBindsOrCollides` — the PUBLISHED rotated commitment's anti-ghost teeth,
FLOOR-FREE.

⚑ SITE 2 (published-commitment anti-ghost) of the light-client soundness-weld de-vacuuming
(2026-07-31, following the `WireCommitBindsOrCollides` before-block work of `4ef5fb288`).

`RotatedCommitDifferential.rotatedCommit_binds_{limbs,authority_digest,cap_root,commitments_root}`
bind the actually-published rotated commitment under `Poseidon2SpongeCR hash`, which
`Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear` PROVES FALSE at deployed BabyBear — so at
deployment they are true-but-empty: a Mina settlement certifies the AIR's arithmetic, not that a
permission-flip / VK-swap / dropped-root MOVES the published `OLD_COMMIT`/`NEW_COMMIT`.

This module restates those anti-ghost teeth WITHOUT the floor, off
`WireCommitBindsOrCollides.wireCommitR_binds_or_collides`: a forged authority residue / cap root /
commitments root EITHER moves the published rotated commitment, OR the prover HANDS BACK a genuine
sponge collision (`WireColl1`) at the two limb lists the total extractor returns — no hypothesis on
`hash`. This is the deployed-hash content the floored twins only asserted vacuously.

⚑ Kept as a SEPARATE inert module (nothing imports it yet) rather than mutating
`RotatedCommitDifferential` in place, mirroring how the sibling landed the before-block
`WireCommitBindsOrCollides` next to `EffectVmEmitRotationR` rather than editing it: the floored teeth
stay as the grandfathered migration target, and each consumer flips to the `_or_collides` twin as it
is de-vacuumed. The per-cell leg of
`RotatedCommitDifferential.rotated_and_perCell_both_bind_authority_residue` is ALREADY floor-free
(`CommitDifferential.effectVmCommit_binds_record_digest_or_collides`); these make the rotated leg
match, so the unified P0-2 closure can be restated floor-free on BOTH commitment shapes.

Discipline: sorry-free; the whole proof is the floored twin's body with `wireCommitR_binds hash hCR`
replaced by `wireCommitR_binds_or_collides hash`, the equality branch reading off the same
`[i]?`-index pin, the collision branch handing back the residual. No BabyBear arithmetic computed.
-/
import Dregg2.Circuit.RotatedCommitDifferential
import Dregg2.Circuit.Emit.WireCommitBindsOrCollides

namespace Dregg2.Circuit.RotatedCommitBindsOrCollides

open Dregg2.Circuit.RotatedCommitDifferential
  (rotatedCommit rotatedLimbs rotatedLimbs_length
   authority_digest_at_index_24 cap_root_at_index_25 commitments_root_at_index_27)
open Dregg2.Circuit.Emit.WireCommitBindsOrCollides (wireCommitR_binds_or_collides WireColl1)

set_option autoImplicit false

/-- **`rotatedCommit_binds_limbs_or_collides` — the full-limb binding, FLOOR-FREE.** Equal published
rotated commitments (equal-length limb lists) EITHER force equal limb lists AND equal iroots, OR
exhibit a genuine sponge collision at the two lists `wireCommitRFind` returns.
`RotatedCommitDifferential.rotatedCommit_binds_limbs` with the refuted `Poseidon2SpongeCR` swapped for
the named `WireColl1` residual. -/
theorem rotatedCommit_binds_limbs_or_collides (hash : List ℤ → ℤ)
    {l l' : List ℤ} {iroot iroot' : ℤ} (hlen : l.length = l'.length)
    (h : rotatedCommit hash l iroot = rotatedCommit hash l' iroot') :
    (l = l' ∧ iroot = iroot') ∨ WireColl1 hash l iroot l' iroot' :=
  wireCommitR_binds_or_collides hash hlen h

/-- **`rotatedCommit_binds_authority_digest_or_collides` — THE audit-P0-2 anti-ghost tooth, FLOOR-FREE.**
Two rotated commitments over limb lists agreeing on every NAMED limb EXCEPT the authority residue (same
iroot) EITHER force EQUAL `authorityDigest`, OR hand back a genuine sponge collision. So a permission /
VK / lifecycle flip (all of which live ONLY in `authorityDigest` = register r23) is refused UNLESS the
prover exhibits a real `SpongeColl` — the deployed-hash content the floored twin only asserted
vacuously. -/
theorem rotatedCommit_binds_authority_digest_or_collides (hash : List ℤ → ℤ)
    (cellsRoot r0 r1 r2 : ℤ) (fields : Fin 8 → ℤ)
    (r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 : ℤ)
    (authorityDigest authorityDigest' capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
      committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot iroot : ℤ)
    (h : rotatedCommit hash
          (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
            authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
            committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot) iroot
       = rotatedCommit hash
          (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
            authorityDigest' capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
            committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot) iroot) :
    authorityDigest = authorityDigest'
    ∨ WireColl1 hash
        (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
          authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
          committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot) iroot
        (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
          authorityDigest' capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
          committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot) iroot := by
  have hlen :
      (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
        authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
        committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot).length
      = (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
        authorityDigest' capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
        committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot).length := by
    rw [rotatedLimbs_length, rotatedLimbs_length]
  rcases rotatedCommit_binds_limbs_or_collides hash hlen h with ⟨hlist, _⟩ | hcoll
  · left
    have hidx := congrArg (fun L => L[24]?) hlist
    simp only [authority_digest_at_index_24, Option.some.injEq] at hidx
    exact hidx
  · exact Or.inr hcoll

/-- **`rotatedCommit_binds_cap_root_or_collides` (corollary, FLOOR-FREE).** A forged openable c-list
root either moves the published rotated commitment or hands back a genuine sponge collision. -/
theorem rotatedCommit_binds_cap_root_or_collides (hash : List ℤ → ℤ)
    (cellsRoot r0 r1 r2 : ℤ) (fields : Fin 8 → ℤ)
    (r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 : ℤ)
    (authorityDigest capRoot capRoot' nullifierRoot commitmentsRoot heapRoot lifecycle epoch
      committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot iroot : ℤ)
    (h : rotatedCommit hash
          (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
            authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
            committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot) iroot
       = rotatedCommit hash
          (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
            authorityDigest capRoot' nullifierRoot commitmentsRoot heapRoot lifecycle epoch
            committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot) iroot) :
    capRoot = capRoot'
    ∨ WireColl1 hash
        (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
          authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
          committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot) iroot
        (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
          authorityDigest capRoot' nullifierRoot commitmentsRoot heapRoot lifecycle epoch
          committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot) iroot := by
  have hlen :
      (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
        authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
        committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot).length
      = (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
        authorityDigest capRoot' nullifierRoot commitmentsRoot heapRoot lifecycle epoch
        committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot).length := by
    rw [rotatedLimbs_length, rotatedLimbs_length]
  rcases rotatedCommit_binds_limbs_or_collides hash hlen h with ⟨hlist, _⟩ | hcoll
  · left
    have hidx := congrArg (fun L => L[25]?) hlist
    simp only [cap_root_at_index_25, Option.some.injEq] at hidx
    exact hidx
  · exact Or.inr hcoll

/-- **`rotatedCommit_binds_commitments_root_or_collides` (corollary, FLOOR-FREE).** A forged note
commitments-set root (dropped/reordered/wrong commitment insert) either moves the published rotated
commitment or hands back a genuine sponge collision. -/
theorem rotatedCommit_binds_commitments_root_or_collides (hash : List ℤ → ℤ)
    (cellsRoot r0 r1 r2 : ℤ) (fields : Fin 8 → ℤ)
    (r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 : ℤ)
    (authorityDigest capRoot nullifierRoot commitmentsRoot commitmentsRoot' heapRoot lifecycle epoch
      committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot iroot : ℤ)
    (h : rotatedCommit hash
          (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
            authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
            committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot) iroot
       = rotatedCommit hash
          (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
            authorityDigest capRoot nullifierRoot commitmentsRoot' heapRoot lifecycle epoch
            committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot) iroot) :
    commitmentsRoot = commitmentsRoot'
    ∨ WireColl1 hash
        (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
          authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
          committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot) iroot
        (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
          authorityDigest capRoot nullifierRoot commitmentsRoot' heapRoot lifecycle epoch
          committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot) iroot := by
  have hlen :
      (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
        authorityDigest capRoot nullifierRoot commitmentsRoot heapRoot lifecycle epoch
        committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot).length
      = (rotatedLimbs cellsRoot r0 r1 r2 fields r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22
        authorityDigest capRoot nullifierRoot commitmentsRoot' heapRoot lifecycle epoch
        committedHeight lifecycleDisc permsDigest vkDigest mode fieldsRoot).length := by
    rw [rotatedLimbs_length, rotatedLimbs_length]
  rcases rotatedCommit_binds_limbs_or_collides hash hlen h with ⟨hlist, _⟩ | hcoll
  · left
    have hidx := congrArg (fun L => L[27]?) hlist
    simp only [commitments_root_at_index_27, Option.some.injEq] at hidx
    exact hidx
  · exact Or.inr hcoll

#assert_axioms rotatedCommit_binds_limbs_or_collides
#assert_axioms rotatedCommit_binds_authority_digest_or_collides
#assert_axioms rotatedCommit_binds_cap_root_or_collides
#assert_axioms rotatedCommit_binds_commitments_root_or_collides

end Dregg2.Circuit.RotatedCommitBindsOrCollides
