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

where `record_digest = dregg_cell::compute_authority_digest_felt` is the SINGLE authority-residue
felt folding ALL authority-bearing state no named limb carries (permissions / VK / lifecycle /
delegate / delegation / program / mode / visibility / side-table roots / `fields[8..16]`) — the exact
EffectVM analog of the Lean `RH`/`systemRootsDigest` rest-hash limb. A residue-free cell uses
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

  * `effectVmCommit_binds_record_digest` (+ the per-limb binding family) — INJECTIVITY OVER THE FULL
    LIMB LIST off a single realizable `h4`-collision-resistance carrier (`compress4Injective`): the
    deployed commitment binds the `record_digest` limb (and every other limb), so tampering the
    authority residue — a permission flip, a VK swap, a dropped side-table root — provably MOVES the
    commitment. This is the deployed twin of `SystemRoots.cellCommitS_binds_systemRoots`. A
    `record_digest := 0` stub for a residue-bearing cell would collapse it (the audit P0-2 hole).

  * `effectVmCommit_residueFree_noop` — the NO-OP cutover: a residue-free cell (`record_digest = 0`,
    Rust `empty_record_digest()`) commits exactly as the legacy `record_digest`-at-ZERO form — the
    flag-day-free additive cutover, mirroring `SystemRoots.legacy_commitS_absorbs_empty_roots`.

  * the VACUITY GUARD: concrete computable `#guard`s over an injective toy `h4` — the residue limb
    is load-bearing (a residue-bearing cell DIFFERS from its residue-free twin) AND the no-op holds.

Pure, computable, `#guard`-able (no `native_decide`). The carried `compress4Injective` is the SAME
shape as `StateCommit.compressInjective` (a realizable Poseidon 4-to-1 collision-resistance), never an
`axiom`, never a `+`-fold. The Rust-side empirical twin is
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

/-- **CR carrier `compress4Injective h4`** — the 4-to-1 hash `h4` is injective:
`h4 a b c d = h4 a' b' c' d' ⇒ (a,b,c,d) = (a',b',c',d')`. The standard collision-resistance of a
Poseidon 4-to-1 compress (REALIZABLE — the `hash_4_to_1` the circuit verifies). Same shape as
`StateCommit.compressInjective`, one arity up. NEVER a `+`-fold (whose 4-ary injectivity is FALSE). -/
def compress4Injective : Prop :=
  ∀ a b c d a' b' c' d' : ℤ,
    h4 a b c d = h4 a' b' c' d' → a = a' ∧ b = b' ∧ c = c' ∧ d = d'

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

/-! ## §3 — INJECTIVITY OVER THE FULL LIMB LIST (the anti-ghost teeth, incl. `record_digest`).

Off the single realizable `compress4Injective h4` carrier, the deployed commitment binds EVERY limb —
crucially `record_digest`. So tampering the authority residue MOVES the commitment (audit P0-2 closed
in the deployed model). -/

/-- **`effectVmCommit_binds_all` — full-limb binding.** Equal deployed commitments force EVERY limb
equal: the three intermediates + `record_digest` (root injectivity), then each intermediate's four
inputs (the three sub-`h4`s). Off `compress4Injective` alone. -/
theorem effectVmCommit_binds_all (hCR : compress4Injective h4)
    (balLo balHi nonce : ℤ) (fields : Fin 8 → ℤ) (capRoot recordDigest : ℤ)
    (balLo' balHi' nonce' : ℤ) (fields' : Fin 8 → ℤ) (capRoot' recordDigest' : ℤ)
    (h : effectVmCommit h4 balLo balHi nonce fields capRoot recordDigest
       = effectVmCommit h4 balLo' balHi' nonce' fields' capRoot' recordDigest') :
    balLo = balLo' ∧ balHi = balHi' ∧ nonce = nonce'
      ∧ fields 0 = fields' 0 ∧ fields 1 = fields' 1 ∧ fields 2 = fields' 2 ∧ fields 3 = fields' 3
      ∧ fields 4 = fields' 4 ∧ fields 5 = fields' 5 ∧ fields 6 = fields' 6 ∧ fields 7 = fields' 7
      ∧ capRoot = capRoot' ∧ recordDigest = recordDigest' := by
  unfold effectVmCommit at h
  -- root: the three intermediates + record_digest.
  obtain ⟨hi1, hi2, hi3, hrd⟩ := hCR _ _ _ _ _ _ _ _ h
  -- inter1: balLo balHi nonce fields[0].
  obtain ⟨hbl, hbh, hn, hf0⟩ := hCR _ _ _ _ _ _ _ _ hi1
  -- inter2: fields[1..5].
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hCR _ _ _ _ _ _ _ _ hi2
  -- inter3: fields[5..8] + capRoot.
  obtain ⟨hf5, hf6, hf7, hcr⟩ := hCR _ _ _ _ _ _ _ _ hi3
  exact ⟨hbl, hbh, hn, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hcr, hrd⟩

/-- **`effectVmCommit_binds_record_digest` — THE audit-P0-2 anti-ghost tooth.** Equal deployed
commitments (same carried limbs) force EQUAL `record_digest`: the authority residue is bound. So two
cells differing ONLY in their authority residue (permissions / VK / lifecycle / …, which live ONLY in
`record_digest`) commit DIFFERENTLY — the exact gap the old `…, ZERO` fourth input left open. The
deployed twin of `SystemRoots.cellCommitS_binds_systemRoots` / `RecordCommit.cellCommit_binds_fieldsRoot`. -/
theorem effectVmCommit_binds_record_digest (hCR : compress4Injective h4)
    (balLo balHi nonce : ℤ) (fields : Fin 8 → ℤ) (capRoot recordDigest recordDigest' : ℤ)
    (h : effectVmCommit h4 balLo balHi nonce fields capRoot recordDigest
       = effectVmCommit h4 balLo balHi nonce fields capRoot recordDigest') :
    recordDigest = recordDigest' := by
  unfold effectVmCommit at h
  exact (hCR _ _ _ _ _ _ _ _ h).2.2.2

/-- **`effectVmCommit_binds_cap_root` (corollary).** Equal commitments force equal `cap_root` — the
deployed twin of cap-Phase-A's "the openable c-list root is bound" (`cap_root_cell_circuit_differential`). -/
theorem effectVmCommit_binds_cap_root (hCR : compress4Injective h4)
    (balLo balHi nonce : ℤ) (fields : Fin 8 → ℤ) (capRoot capRoot' recordDigest : ℤ)
    (h : effectVmCommit h4 balLo balHi nonce fields capRoot recordDigest
       = effectVmCommit h4 balLo balHi nonce fields capRoot' recordDigest) :
    capRoot = capRoot' := by
  have := effectVmCommit_binds_all h4 hCR balLo balHi nonce fields capRoot recordDigest
    balLo balHi nonce fields capRoot' recordDigest h
  exact this.2.2.2.2.2.2.2.2.2.2.2.1

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
#assert_axioms effectVmCommit_binds_all
#assert_axioms effectVmCommit_binds_record_digest
#assert_axioms effectVmCommit_binds_cap_root
#assert_axioms effectVmCommit_residueFree_noop

end Dregg2.Circuit.CommitDifferential
