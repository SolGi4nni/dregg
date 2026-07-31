/-
# `Dregg2.Circuit.Emit.WireCommitBindsOrCollides` — the 1-felt chained wire commitment, FLOOR-FREE.

⚑ SITE 2 of the light-client soundness-weld de-vacuuming (2026-07-31).

`EffectVmEmitRotationR.wireCommitR_binds` binds the 1-felt chained rotated commitment `wireCommitR`
under `Poseidon2SpongeCR hash`, which `Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear`
PROVES FALSE at deployed BabyBear width. It is the exact floor `EffectVmEmitRotationV3.rotV3_binds_published`
CONSUMES (`wireCommitR_binds hash hCR`, `:1507`), which is in turn the floor
`CircuitSoundness.descriptorRefines` carries as its `Poseidon2SpongeCR hash →` antecedent — so the
whole per-effect refinement over that binding is a true-but-empty implication at deployment.

This module rebuilds the binding WITHOUT the floor, by the SAME idiom the map leaf received
(`DeployedMapDenotation.padImtRoot_binds_or_ghost_or_collides`) and that `EffectVmEmitRotationR`'s own
FAITHFUL 8-felt commitment already carries (`wireCommitR8_binds_or_collides`): the chain walk
`chainCollFind1` LOCATES the colliding sponge step as a TOTAL function, so an equivocation on the
commitment either FORCES the pre-iroot limbs (and the iroot) equal, or HANDS BACK the two distinct
lists at which the deployed sponge actually collides (`Poseidon2Binding.SpongeColl`). No hypothesis on
`hash` anywhere.

BOTH POLARITIES (the FloorPole discipline — the disjunction is neither a tautology nor a free pass),
BOTH stated FLOOR-FREE (no `Function.Injective hash`, which is the refuted CR floor inj-spelled):
  * FORGED POLE — `wireCommitRFind_spec`: DISTINCT claims that publish the SAME commit FORCE the
    residual, HANDING BACK a genuine sponge collision. A forgery is refused unless a real `SpongeColl`
    is exhibited.
  * REFUTABILITY CANARY — `wireCommitRColl_refutable_on_agreement`: on AGREEING claims the residual is
    FALSE, so `WireColl1` is not the constant `True`. Proved at an arbitrary hash.

Discipline: sorry-free; total functions only (`Decidable` branch, no `Classical.choice`); no BabyBear
arithmetic computed; the whole proof is the 8-felt `wireCommitR8_binds_or_collides` peel with the
carrier narrowed from `List ℤ` to `ℤ` and the step `permW (acc ++ c)` narrowed to `hash (acc :: c)`.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationR

namespace Dregg2.Circuit.Emit.WireCommitBindsOrCollides

open Dregg2.Circuit.Emit.EffectVmEmitRotationR
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR SpongeColl)

set_option autoImplicit false

/-! ## §1 — the chain walk: LOCATE the colliding sponge step, as a total function. -/

/-- **⚑ THE 1-FELT CHAIN WALK.** Step the two chains together. At each step the two sponge arguments
are `acc :: c` and `acc' :: c'`; if they COLLIDE (equal digest, distinct arguments) return them, else
carry on with the two new 1-felt carriers. If the walk runs out of chunks, return the two seeds boxed
as singletons — the caller (`wireCommitRFind`) resolves that case at the head. The `else` silently
absorbs the third possibility (different digests here, chains re-converge later) — the case a
"peel from the outside" proof gets for free but a total FUNCTION must survive; `chainCollFind1_spec`
handles it. -/
def chainCollFind1 (hash : List ℤ → ℤ) :
    ℤ → List (List ℤ) → ℤ → List (List ℤ) → List ℤ × List ℤ
  | acc, c :: ds, acc', c' :: ds' =>
      if hash (acc :: c) = hash (acc' :: c') ∧ (acc :: c) ≠ (acc' :: c') then
        (acc :: c, acc' :: c')
      else
        chainCollFind1 hash (hash (acc :: c)) ds (hash (acc' :: c')) ds'
  | acc, _, acc', _ => ([acc], [acc'])

/-- **⚑ THE WALK IS CORRECT — the 1-felt analog of `chainCollFind_spec`.** For two chains of EQUAL
chunk count with EQUAL final digests: EITHER the seeds and the chunk lists agree outright, OR the walk
lands on a genuine `hash` collision. No injectivity hypothesis: the failure branch produces a WITNESS. -/
theorem chainCollFind1_spec (hash : List ℤ → ℤ) :
    ∀ {cs cs' : List (List ℤ)} {acc acc' : ℤ}, cs.length = cs'.length →
      chainFrom hash acc cs = chainFrom hash acc' cs' →
      (acc = acc' ∧ cs = cs') ∨ SpongeColl hash (chainCollFind1 hash acc cs acc' cs') := by
  intro cs
  induction cs with
  | nil =>
    intro cs' acc acc' hlen h
    have hnil : cs' = [] := List.length_eq_zero_iff.mp hlen.symm
    subst hnil
    exact Or.inl ⟨h, rfl⟩
  | cons c ds ih =>
    intro cs' acc acc' hlen h
    cases cs' with
    | nil => simp at hlen
    | cons c' ds' =>
      simp only [chainFrom] at h
      have hlen' : ds.length = ds'.length := by simpa using hlen
      by_cases hif : hash (acc :: c) = hash (acc' :: c') ∧ (acc :: c) ≠ (acc' :: c')
      · refine Or.inr ?_
        show SpongeColl hash (chainCollFind1 hash acc (c :: ds) acc' (c' :: ds'))
        rw [chainCollFind1, if_pos hif]
        exact ⟨hif.2, hif.1⟩
      · rcases ih hlen' h with ⟨himg, hds⟩ | hcoll
        · -- the recursive carriers agree; the failed test forces the ARGUMENTS to agree.
          have hargs : acc :: c = acc' :: c' := by
            by_contra hne
            exact hif ⟨himg, hne⟩
          injection hargs with haccEq hcEq
          exact Or.inl ⟨haccEq, by rw [hcEq, hds]⟩
        · refine Or.inr ?_
          show SpongeColl hash (chainCollFind1 hash acc (c :: ds) acc' (c' :: ds'))
          rw [chainCollFind1, if_neg hif]
          exact hcoll

/-! ## §2 — the extractor over the deployed commitment decomposition, and the FLOOR-FREE binding. -/

/-- **⚑ THE `wireCommitR` EXTRACTOR.** Run the chain walk over the commitment's chunk decomposition
(`head = hash (l.take 4)`, body `= chunk31 (l.drop 4)`, then the iroot site `[ir]` LAST). If the walk
found a genuine collision, that is the answer; otherwise it proved the seeds and chunks agree, which —
given the claims DIFFER — forces the collision to be at the 4-wide HEAD, so return the two head blocks. -/
def wireCommitRFind (hash : List ℤ → ℤ) (l : List ℤ) (ir : ℤ) (l' : List ℤ) (ir' : ℤ) :
    List ℤ × List ℤ :=
  let r := chainCollFind1 hash (hash (l.take 4)) (chunk31 (l.drop 4) ++ [[ir]])
    (hash (l'.take 4)) (chunk31 (l'.drop 4) ++ [[ir']])
  if SpongeColl hash r then r else (l.take 4, l'.take 4)

/-- **`WireColl1 hash l ir l' ir'`** — the pair the extractor RETURNS on this equivocation is a genuine
collision of the deployed sponge. The named disjunct every consumer carries in place of the deleted
floor. -/
def WireColl1 (hash : List ℤ → ℤ) (l : List ℤ) (ir : ℤ) (l' : List ℤ) (ir' : ℤ) : Prop :=
  SpongeColl hash (wireCommitRFind hash l ir l' ir')

/-- **⚑ THE EXTRACTOR IS CORRECT.** Two DISTINCT `(limbs, iroot)` claims of EQUAL limb length with the
SAME 1-felt chained commitment produce two DISTINCT lists with the SAME `hash` digest. -/
theorem wireCommitRFind_spec (hash : List ℤ → ℤ)
    {l l' : List ℤ} {ir ir' : ℤ} (hlen : l.length = l'.length)
    (hne : ¬ (l = l' ∧ ir = ir'))
    (h : wireCommitR hash l ir = wireCommitR hash l' ir') :
    WireColl1 hash l ir l' ir' := by
  unfold wireCommitR at h
  by_cases hif : SpongeColl hash (chainCollFind1 hash (hash (l.take 4))
      (chunk31 (l.drop 4) ++ [[ir]]) (hash (l'.take 4)) (chunk31 (l'.drop 4) ++ [[ir']]))
  · show SpongeColl hash (wireCommitRFind hash l ir l' ir')
    rw [wireCommitRFind, if_pos hif]
    exact hif
  · show SpongeColl hash (wireCommitRFind hash l ir l' ir')
    rw [wireCommitRFind, if_neg hif]
    have hclen : (chunk31 (l.drop 4) ++ [[ir]]).length
        = (chunk31 (l'.drop 4) ++ [[ir']]).length := by
      rw [List.length_append, List.length_append, chunk31_length, chunk31_length,
        List.length_drop, List.length_drop, hlen]
      simp
    rcases chainCollFind1_spec hash hclen h with ⟨hseed, hcs⟩ | hcoll
    · -- the walk found nothing: seeds AND chunk lists agree, so the break is at the HEAD.
      obtain ⟨hbody, hir⟩ := List.append_inj' hcs rfl
      have hir' : ir = ir' := by simpa using hir
      have hdrop : l.drop 4 = l'.drop 4 := by
        have := congrArg List.flatten hbody
        rwa [chunk31_flatten, chunk31_flatten] at this
      refine ⟨fun htake => hne ⟨?_, hir'⟩, hseed⟩
      replace htake : List.take 4 l = List.take 4 l' := htake
      rw [← List.take_append_drop 4 l, ← List.take_append_drop 4 l', htake, hdrop]
    · exact absurd hcoll hif

/-- **★★ THE 1-FELT ANTI-GHOST KEYSTONE — UNCONDITIONAL** (`wireCommitR_binds`, with the false floor
REMOVED): equal chained wire commits over equal-length pre-iroot limb lists EITHER force equal limb
lists AND equal iroots, OR exhibit a genuine collision of the deployed sponge at the two lists
`wireCommitRFind` returns. The binding the light client trusts — now stated so that it says something
about the REAL hash, not the empty one.

⚑ STRENGTH, stated honestly. `wireCommitR_binds` concluded a bare equality from `Poseidon2SpongeCR hash`,
which `poseidon2SpongeCR_false_babyBear` REFUTES; at deployed parameters that theorem was VACUOUS. This
one is a disjunction — formally weaker, but it HOLDS of the deployed sponge, which the old one did not. -/
theorem wireCommitR_binds_or_collides (hash : List ℤ → ℤ)
    {l l' : List ℤ} {ir ir' : ℤ} (hlen : l.length = l'.length)
    (h : wireCommitR hash l ir = wireCommitR hash l' ir') :
    (l = l' ∧ ir = ir') ∨ WireColl1 hash l ir l' ir' := by
  by_cases hne : l = l' ∧ ir = ir'
  · exact Or.inl hne
  · exact Or.inr (wireCommitRFind_spec hash hlen hne h)

/-! ## §3 — BOTH POLARITIES (the FloorPole discipline), FLOOR-FREE.

⚑ We do NOT state the injective "no-strength-lost" / "refutable-at-injective-hash" bridges here.
`Function.Injective hash` on the sponge type is the refuted `Poseidon2SpongeCR` floor spelled through
injectivity (`#floor_ratchet`'s `inj-spelled` class gates it), so a bridge carrying it would REINTRODUCE
the very carrier this file exists to remove. Both polarities are instead exhibited WITHOUT any
hypothesis on `hash`:

  * FORGED POLE — `wireCommitRFind_spec` (§2): DISTINCT `(limbs, iroot)` claims that nevertheless
    publish the SAME commit FORCE the residual, i.e. HAND BACK a genuine sponge collision. So a forged
    commitment on different limbs is not "refused for free" — it is refused UNLESS the prover exhibits a
    real `SpongeColl`. That is the content the light client actually gets.
  * REFUTABILITY CANARY — `wireCommitRColl_refutable_on_agreement` (below): when the two claims AGREE
    the residual is FALSE, so `WireColl1` is not the constant `True` and the disjunction is not a free
    pass. Proved at an ARBITRARY hash, no injectivity. -/

/-- On IDENTICAL inputs the chain walk never fires (its `if` needs DISTINCT arguments), so it returns a
diagonal pair. Floor-free — the `if` test's distinctness half is refuted by `rfl` at every step. -/
theorem chainCollFind1_diag (hash : List ℤ → ℤ) :
    ∀ (cs : List (List ℤ)) (acc : ℤ),
      (chainCollFind1 hash acc cs acc cs).1 = (chainCollFind1 hash acc cs acc cs).2 := by
  intro cs
  induction cs with
  | nil => intro acc; rfl
  | cons c ds ih =>
    intro acc
    have hif : ¬ (hash (acc :: c) = hash (acc :: c) ∧ (acc :: c) ≠ (acc :: c)) := by
      rintro ⟨_, hne⟩; exact hne rfl
    rw [chainCollFind1, if_neg hif]
    exact ih (hash (acc :: c))

/-- **(CANARY — the collision disjunct is REFUTABLE, FLOOR-FREE.)** When the two `(limbs, iroot)`
claims AGREE, the extractor's returned pair is diagonal, so it is NOT a `SpongeColl` (which demands
DISTINCT elements): `WireColl1 hash l ir l ir` is FALSE at every hash. So `wireCommitR_binds_or_collides`
cannot discharge itself by taking the right branch for free — the binding has to do the work. -/
theorem wireCommitRColl_refutable_on_agreement (hash : List ℤ → ℤ) (l : List ℤ) (ir : ℤ) :
    ¬ WireColl1 hash l ir l ir := by
  unfold WireColl1 wireCommitRFind
  by_cases hc : SpongeColl hash (chainCollFind1 hash (hash (l.take 4)) (chunk31 (l.drop 4) ++ [[ir]])
      (hash (l.take 4)) (chunk31 (l.drop 4) ++ [[ir]]))
  · exact absurd (chainCollFind1_diag hash _ _) hc.1
  · rw [if_neg hc]
    rintro ⟨hne, _⟩
    exact hne rfl

#assert_axioms chainCollFind1_spec
#assert_axioms wireCommitRFind_spec
#assert_axioms wireCommitR_binds_or_collides
#assert_axioms chainCollFind1_diag
#assert_axioms wireCommitRColl_refutable_on_agreement

end Dregg2.Circuit.Emit.WireCommitBindsOrCollides
