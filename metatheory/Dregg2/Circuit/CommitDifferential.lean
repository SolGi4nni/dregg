/-
# Dregg2.Circuit.CommitDifferential — the COMMITMENT DIFFERENTIAL (Lean model ⟺ deployed Rust).

The closed circuit-soundness crown (`Dregg2.Circuit.StateCommit`) is over the abstract per-cell leaf
`CH c v` and the kernel root `recStateCommit`. The DEPLOYED circuit's per-cell commitment is the
Rust `CellState::compute_commitment` (`circuit/src/effect_vm/cell_state.rs`): a `hash_4_to_1` tree
over the ORDERED limb list

  `[balance_lo, balance_hi, nonce, fields[0..8], cap_root, record_digest]`

absorbed as

  `inter1 = h4 balance_lo balance_hi nonce fields[0]`
  `inter2 = h4 fields[1] fields[2] fields[3] fields[4]`
  `inter3 = h4 fields[5] fields[6] fields[7] cap_root`
  `commitment = h4 inter1 inter2 inter3 record_digest`

where `record_digest = dregg_cell::compute_authority_digest_felt` is LANE ZERO of the eight-limb
BLAKE3-rooted authority residue (permissions / VK / delegate / delegation / program / mode /
visibility / side-table roots / `fields[8..16]`). Lifecycle/epoch/height/heap are separate named
limbs on the live rotated surface; lanes 1..7 ride its authority headroom. A residue-free cell uses
`empty_record_digest() = ZERO` (the Rust no-op), mirroring the Lean `emptySystemRootsDigest`.

This module makes "the running per-cell commitment IS the proven shape" a CHECKED Lean fact:

  * `effectVmCommit h4 …` — the FAITHFUL Lean model of `CellState::compute_commitment`, the SAME
    `hash_4_to_1` tree over the SAME ordered limb list (`h4` is the abstract 4-to-1 compress; the
    deployed `hash_4_to_1` is its realization, KAT-locked to Plonky3's BabyBear Poseidon2 — the
    `circuit/tests/poseidon2_*_kat.rs` conformance gates carry that realization).

  * `effectVmLimbs …` — the ORDERED absorbed-felt list, with the field correspondence NAMED:
    `record_digest` sits at the FIXED last position (index 12), exactly where the Rust 4th root input
    is, and exactly the role the Lean `systemRootsDigest`/`fieldsRoot` absorbed-residue limb plays.

  * `effectVmCommit_absorbs_limbs` — the PREIMAGE-SHAPE theorem: under the named field
    correspondence (a bijection from the Rust cell-state felts to `effectVmLimbs`), the deployed
    commitment is exactly `h4`-folded over that ordered limb list in that order. So two deployed
    commitments agree iff the SAME limb list was absorbed (the shape MATCHES — no reorder, no dropped
    limb, no extra limb).

  * `effectVmCommit_binds_record_digest_or_collides` / `_binds_cap_root_or_collides` — the
    UNCONDITIONAL binding. The deployed commitment binds the `record_digest` limb (and the cap root),
    so tampering the authority residue — a permission flip, a VK swap, a dropped side-table root —
    provably MOVES the commitment UNLESS the deployed `hash_4_to_1` collides at two EXPLICITLY NAMED
    quads, which the theorem hands back. This is the deployed twin of
    `SystemRoots.cellCommitS_binds_systemRoots_or_collides`; a `record_digest := 0` stub for a residue-bearing cell
    would collapse it (the audit P0-2 hole). The old `compress4Injective`-conditioned forms were
    DELETED (VACUITY-SWEEP FINDING 2): injectivity of a compressing `ℤ⁴ → ℤ` map is FALSE at deployed
    BabyBear parameters, so those theorems were vacuous exactly where it mattered. The probabilistic
    residual lives in `InjectiveFloorRegrounded` §2.

  * `effectVmCommit_residueFree_noop` — the NO-OP cutover: a residue-free cell (`record_digest = 0`,
    Rust `empty_record_digest()`) commits exactly as the legacy `record_digest`-at-ZERO form — the
    flag-day-free additive cutover, mirroring `SystemRoots.legacy_commitS_absorbs_empty_roots`.

  * the VACUITY GUARD: concrete computable `#guard`s over an injective toy `h4` — the residue limb
    is load-bearing (a residue-bearing cell DIFFERS from its residue-free twin) AND the no-op holds.

Pure, computable, `#guard`-able (no `native_decide`). No injectivity floor is carried anywhere in this
file — `Coll4` names collisions at SPECIFIC quads, never `∃`. The Rust-side empirical twin is
`circuit/tests/effect_vm_commit_lean_differential.rs` (same limb order, same record_digest position,
same no-op).
-/
import Dregg2.Circuit.StateCommit

namespace Dregg2.Circuit.CommitDifferential

open Dregg2.Circuit.StateCommit (compressInjective)

/-! ## §1 — the FAITHFUL Lean model of the Rust `hash_4_to_1` commitment tree.

`h4 a b c d` is the abstract 4-to-1 compress (the Lean shadow of `dregg_circuit::poseidon2::hash_4_to_1`,
KAT-locked to Plonky3). We model `CellState::compute_commitment` over it limb-for-limb, in the SAME
nesting. The twelve limbs are field elements (`ℤ`, the `StateCommit` Poseidon-felt carrier). -/

section Surface

-- `h4 a b c d` — the abstract Poseidon 4-to-1 compress (Rust `poseidon2::hash_4_to_1`).
variable (h4 : ℤ → ℤ → ℤ → ℤ → ℤ)

/-- **`h4q h4 q`** — the 4-to-1 compress, UNCURRIED onto a quad. The shape a collision game (and the
counting core) needs: one function, one infinite domain (`ℤ⁴`), one bounded codomain. -/
def h4q (q : ℤ × ℤ × ℤ × ℤ) : ℤ := h4 q.1 q.2.1 q.2.2.1 q.2.2.2

/-- **`Coll4 h4 p q`** — the pair `(p, q)` is a GENUINE collision of the deployed 4-to-1 compress:
two DISTINCT quads with the SAME image. Note what this is NOT: it is not `∃ p q, …` (an existence prop
that pigeonhole makes unconditionally TRUE at deployed parameters, hence content-free — see
`InjectiveFloorRegrounded` §0). It is a predicate about the SPECIFIC quads an extractor RETURNS, so a
theorem concluding it EXHIBITS the collision rather than asserting one exists. -/
def Coll4 (p q : ℤ × ℤ × ℤ × ℤ) : Prop := p ≠ q ∧ h4q h4 p = h4q h4 q

/-- **`effectVmCommit h4 balLo balHi nonce fields capRoot recordDigest`** — the FAITHFUL Lean model
of the deployed `CellState::compute_commitment`: the SAME `hash_4_to_1` tree over the SAME ordered
limbs. `fields : Fin 8 → ℤ` is the eight welded user fields (`fields[0..8]`); `recordDigest` is the
authority-residue felt absorbed as the FOURTH root input (the Lean shadow of
`compute_authority_digest_felt`). Byte-for-byte the Rust nesting:
`h4 (h4 balLo balHi nonce f0) (h4 f1 f2 f3 f4) (h4 f5 f6 f7 capRoot) recordDigest`. -/
def effectVmCommit (balLo balHi nonce : ℤ) (fields : Fin 8 → ℤ) (capRoot recordDigest : ℤ) : ℤ :=
  let inter1 := h4 balLo balHi nonce (fields 0)
  let inter2 := h4 (fields 1) (fields 2) (fields 3) (fields 4)
  let inter3 := h4 (fields 5) (fields 6) (fields 7) capRoot
  h4 inter1 inter2 inter3 recordDigest

/-! ## §2 — the ORDERED absorbed-limb list + the NAMED field correspondence.

`effectVmLimbs` is the canonical limb order the deployed commitment binds. `record_digest` sits at the
FIXED last index (12) — the same fourth-root-input position the Rust tree uses and the same
absorbed-residue role the Lean `systemRootsDigest` limb plays. Pinning this list IS the named field
correspondence (Rust cell-state felts ↔ Lean kernel-record limbs). -/

/-- **`effectVmLimbs`** — the ORDERED 13-limb list the deployed commitment absorbs, in the Rust
absorption order: `[balLo, balHi, nonce, fields[0..8], capRoot, recordDigest]`. The `recordDigest`
is the LAST element (index 12) — the authority-residue limb. -/
def effectVmLimbs (balLo balHi nonce : ℤ) (fields : Fin 8 → ℤ) (capRoot recordDigest : ℤ) : List ℤ :=
  [balLo, balHi, nonce, fields 0, fields 1, fields 2, fields 3, fields 4, fields 5, fields 6,
   fields 7, capRoot, recordDigest]

/-- The `record_digest` limb is at index 12 (the last) — the FIXED authority-residue position,
matching the Rust `hash_4_to_1`'s fourth root input. The named-correspondence pin. -/
theorem record_digest_at_index_12 (balLo balHi nonce : ℤ) (fields : Fin 8 → ℤ)
    (capRoot recordDigest : ℤ) :
    (effectVmLimbs balLo balHi nonce fields capRoot recordDigest)[12]? = some recordDigest := rfl

/-- The limb list has exactly thirteen entries (3 scalar + 8 fields + cap_root + record_digest). -/
theorem effectVmLimbs_length (balLo balHi nonce : ℤ) (fields : Fin 8 → ℤ) (capRoot recordDigest : ℤ) :
    (effectVmLimbs balLo balHi nonce fields capRoot recordDigest).length = 13 := rfl

/-- **`effectVmCommit_absorbs_limbs` — the PREIMAGE-SHAPE theorem.** The deployed commitment is the
`h4`-fold of the named-correspondence limb list in the named-correspondence order. The
`effectVmFoldLimbs` is the explicit Rust nesting written as a fold over `effectVmLimbs`, so this is a
literal `rfl`: the deployed commitment binds EXACTLY the ordered limb list (with `record_digest`
last), no reorder / dropped limb / extra limb. -/
def effectVmFoldLimbs (limbs : List ℤ) : ℤ :=
  match limbs with
  | [balLo, balHi, nonce, f0, f1, f2, f3, f4, f5, f6, f7, capRoot, recordDigest] =>
      h4 (h4 balLo balHi nonce f0) (h4 f1 f2 f3 f4) (h4 f5 f6 f7 capRoot) recordDigest
  | _ => 0

theorem effectVmCommit_absorbs_limbs (balLo balHi nonce : ℤ) (fields : Fin 8 → ℤ)
    (capRoot recordDigest : ℤ) :
    effectVmCommit h4 balLo balHi nonce fields capRoot recordDigest
      = effectVmFoldLimbs h4 (effectVmLimbs balLo balHi nonce fields capRoot recordDigest) := rfl

/-! ## §3 — the UNCONDITIONAL binding: bind, or EXHIBIT the collision.

⚑ These replace the deleted `compress4Injective`-conditioned forms (the VACUITY-SWEEP FINDING-2
carrier: injectivity of a compressing `ℤ⁴ → ℤ` map, FALSE at deployed BabyBear parameters by
pigeonhole, so every theorem above it was VACUOUSLY TRUE at real parameters).

The honest form assumes NOTHING. Equal commitments EITHER force the limbs equal OR hand back the two
DISTINCT quads at which the deployed `hash_4_to_1` actually collides — named explicitly, computed from
the inputs. That is a TRUE theorem at deployed parameters, where the old one was empty.

⚑ **STRENGTH, stated honestly.** The old conclusion was a bare equality; this one is a disjunction, so
as a *formula* it is weaker. As *content at deployed parameters* it is strictly stronger: the old
premise is unsatisfiable by the real `hash_4_to_1`, so the old theorem said nothing about the deployed
system, while this one holds OF the deployed system. The residual crypto is priced where it belongs —
`InjectiveFloorRegrounded` §2 bounds the probability that an adversary in a named class `Eff` produces
the collision disjunct (`effectVmCommit_binds_all_advantage_bound`, via the tree-trace extractor
`commit4Find`), with the `Eff` obligation in the open. -/

/-- The root quad of the deployed commitment tree: the three intermediates and the authority residue.
`h4q h4 (rootQuad …) = effectVmCommit …` by `rfl` — this IS the outermost `hash_4_to_1` call. -/
def rootQuad (balLo balHi nonce : ℤ) (fields : Fin 8 → ℤ) (capRoot recordDigest : ℤ) :
    ℤ × ℤ × ℤ × ℤ :=
  (h4 balLo balHi nonce (fields 0), h4 (fields 1) (fields 2) (fields 3) (fields 4),
   h4 (fields 5) (fields 6) (fields 7) capRoot, recordDigest)

/-- The root quad IS the commitment's outermost absorption (definitional). -/
theorem h4q_rootQuad (balLo balHi nonce : ℤ) (fields : Fin 8 → ℤ) (capRoot recordDigest : ℤ) :
    h4q h4 (rootQuad h4 balLo balHi nonce fields capRoot recordDigest)
      = effectVmCommit h4 balLo balHi nonce fields capRoot recordDigest := rfl

/-- **`effectVmCommit_binds_record_digest_or_collides` — THE audit-P0-2 anti-ghost tooth, UNCONDITIONAL.**
Equal deployed commitments over otherwise-identical limbs EITHER force an equal `record_digest`, OR the
two root quads (which differ in exactly that one coordinate) ARE a genuine `hash_4_to_1` collision. So
two cells differing ONLY in their authority residue (permissions / VK / delegate / …) commit
differently UNLESS the deployed hash collides at these two named quads — the exact gap the old
`…, ZERO` fourth input left open, now stated without a false premise. -/
theorem effectVmCommit_binds_record_digest_or_collides
    (balLo balHi nonce : ℤ) (fields : Fin 8 → ℤ) (capRoot recordDigest recordDigest' : ℤ)
    (h : effectVmCommit h4 balLo balHi nonce fields capRoot recordDigest
       = effectVmCommit h4 balLo balHi nonce fields capRoot recordDigest') :
    recordDigest = recordDigest'
      ∨ Coll4 h4 (rootQuad h4 balLo balHi nonce fields capRoot recordDigest)
          (rootQuad h4 balLo balHi nonce fields capRoot recordDigest') := by
  by_cases hrd : recordDigest = recordDigest'
  · exact Or.inl hrd
  · refine Or.inr ⟨fun hq => hrd ?_, h⟩
    exact congrArg (fun q : ℤ × ℤ × ℤ × ℤ => q.2.2.2) hq

/-! ⚑ **`effectVmCommit_binds_cap_root_or_collides` — DELETED (2026-07-24), replaced by the
REDUCTION `CommitDifferentialRom.effectVmCommit_binds_cap_root_rom`.** The disjunction was a bare
`binds ∨ Coll4` export with NO consumers: at deployed BabyBear parameters a `hash_4_to_1` collision
EXISTS by pigeonhole, so the statement held through its right branch with no binding — an extractor
witness posing as a security statement. Its two-branch case split (third-intermediate collision vs
root-quad collision) is exactly the inner/outer union bound `narrowRow_binds_rom` performs at the
sampled oracle, where the floor (`keyedRom_hard`, the birthday bound) is PROVED. The
`record_digest` disjunction above is RETAINED — `RotatedCommitDifferential` still `rcases` on it —
with ITS reduction successor `effectVmCommit_binds_record_digest_rom` landed beside it. -/

/-- **⚑ THE NO-STRENGTH-LOST TOOTH.** The deleted `effectVmCommit_binds_record_digest` is EXACTLY the
injective special case of the unconditional tooth: assume the injectivity the old carrier asserted and
the collision disjunct is impossible, so the equality falls out. Nothing genuinely proved was given up
by the deletion — only the pretence that the deployed `hash_4_to_1` satisfies the hypothesis. Stated as
a standalone bridge, deliberately NOT as a hypothesis on any consumer:
`Function.Injective (h4q h4)` is FALSE at deployed BabyBear parameters
(`InjectiveFloorRegrounded.compress4_not_injective_babyBear`). -/
theorem effectVmCommit_binds_record_digest_of_injective (hinj : Function.Injective (h4q h4))
    (balLo balHi nonce : ℤ) (fields : Fin 8 → ℤ) (capRoot recordDigest recordDigest' : ℤ)
    (h : effectVmCommit h4 balLo balHi nonce fields capRoot recordDigest
       = effectVmCommit h4 balLo balHi nonce fields capRoot recordDigest') :
    recordDigest = recordDigest' := by
  rcases effectVmCommit_binds_record_digest_or_collides h4 balLo balHi nonce fields capRoot
    recordDigest recordDigest' h with hEq | ⟨hne, himg⟩
  · exact hEq
  · exact absurd (hinj himg) hne

/-- **(CANARY — the collision disjunct is REFUTABLE, so the disjunction is not a free pass.)** At an
injective compress the named quads are not a collision, so the `_or_collides` teeth cannot discharge
themselves by taking the right branch: the binding has to do the work. -/
theorem coll4_refutable_of_injective (hinj : Function.Injective (h4q h4))
    (p q : ℤ × ℤ × ℤ × ℤ) : ¬ Coll4 h4 p q := by
  rintro ⟨hne, himg⟩
  exact hne (hinj himg)

/-! ## §4 — THE NO-OP CUTOVER (residue-free cell = legacy ZERO form).

A residue-free cell carries `record_digest = 0` (Rust `empty_record_digest()`). The deployed
commitment is then BYTE-IDENTICAL to the legacy `record_digest`-at-ZERO form — the flag-day-free
additive cutover. The Lean shadow of the Rust `empty_record_digest_is_legacy_noop` test and of
`SystemRoots.legacy_commitS_absorbs_empty_roots`. -/

/-- **`legacyEffectVmCommit`** — the OLD lossy commitment: the fourth root input pinned to `0` (the
literal `ZERO` the legacy `compute_commitment` absorbed before P0-2). -/
def legacyEffectVmCommit (balLo balHi nonce : ℤ) (fields : Fin 8 → ℤ) (capRoot : ℤ) : ℤ :=
  effectVmCommit h4 balLo balHi nonce fields capRoot 0

/-- **`effectVmCommit_residueFree_noop`.** A residue-free cell (`record_digest = 0`) commits exactly
as the legacy ZERO form: the absorption is a uniform no-op for such cells (byte-identical cutover). -/
theorem effectVmCommit_residueFree_noop (balLo balHi nonce : ℤ) (fields : Fin 8 → ℤ) (capRoot : ℤ) :
    effectVmCommit h4 balLo balHi nonce fields capRoot 0
      = legacyEffectVmCommit h4 balLo balHi nonce fields capRoot := rfl

end Surface

/-! ## §5 — VACUITY GUARD: concrete injective toy `h4`, the residue limb is LOAD-BEARING.

A residue-bearing cell DIFFERS from its residue-free twin (the absorption is not a `:= 0` stub), and
the no-op holds. The toy `h4` is INJECTIVE on the `#guard` domain (a range-bounded Horner pairing —
NOT a lossy `+`-fold), so the rejection fires on a binding commitment. -/

/-- A concrete INJECTIVE 4-to-1 toy hash: a base-`B` positional pack (each input in a distinct digit),
so the four inputs are recoverable on the small `#guard` domain (NOT the lossy `a+b+c+d`). -/
private def h4C : ℤ → ℤ → ℤ → ℤ → ℤ :=
  fun a b c d => a * 1000000000 + b * 1000000 + c * 1000 + d

private def fieldsC : Fin 8 → ℤ := fun i => 10 + (i : ℤ)
private def capRootC : ℤ := 777
private def realDigestC : ℤ := 42  -- a residue-bearing cell (real authority digest)

-- NO-OP: a residue-free cell (record_digest = 0) commits as the legacy ZERO form.
#guard decide (effectVmCommit h4C 1 2 3 fieldsC capRootC 0
             = legacyEffectVmCommit h4C 1 2 3 fieldsC capRootC)

-- LOAD-BEARING: a residue-BEARING cell DIFFERS from its residue-free twin (the limb is not a stub —
-- a `record_digest := 0` would make these EQUAL: the audit-P0-2 forgery, forbidden).
#guard decide (effectVmCommit h4C 1 2 3 fieldsC capRootC realDigestC
             = effectVmCommit h4C 1 2 3 fieldsC capRootC 0) == false

-- ANTI-GHOST: two cells differing ONLY in authority residue commit DIFFERENTLY (P0-2 closed).
#guard decide (effectVmCommit h4C 1 2 3 fieldsC capRootC 11
             = effectVmCommit h4C 1 2 3 fieldsC capRootC 22) == false

-- The limb list pins record_digest at index 12 (the named-correspondence position).
#guard ((effectVmLimbs 1 2 3 fieldsC capRootC realDigestC)[12]? == some realDigestC)
#guard ((effectVmLimbs 1 2 3 fieldsC capRootC realDigestC).length == 13)

-- COMPLETENESS dual: same limbs ⇒ same commitment (the fold is a function of the limb list).
#guard decide (effectVmCommit h4C 1 2 3 fieldsC capRootC realDigestC
             = effectVmFoldLimbs h4C (effectVmLimbs 1 2 3 fieldsC capRootC realDigestC))

#assert_axioms effectVmCommit_absorbs_limbs
#assert_axioms record_digest_at_index_12
#assert_axioms effectVmCommit_binds_record_digest_or_collides
#assert_axioms effectVmCommit_binds_record_digest_of_injective
#assert_axioms coll4_refutable_of_injective
#assert_axioms h4q_rootQuad
#assert_axioms effectVmCommit_residueFree_noop

end Dregg2.Circuit.CommitDifferential
