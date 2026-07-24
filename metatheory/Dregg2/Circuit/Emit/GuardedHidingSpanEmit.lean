/-
# Dregg2.Circuit.Emit.GuardedHidingSpanEmit — the SHARED BASE of the hidden-span commitment
family: the wide commit-fold pair, the PI surface, and the demo absorb.

**This is Lean-authored AIR** (the family's algebra lives here and in
`GuardedHidingSpanWideBlindEmit`). THE EMITTED DESCRIPTOR OF THIS FAMILY IS
`GuardedHidingSpanWideBlindEmit.guardedHidingSpanWideBlindDesc` — the 5-blinding-lane
(`|R| = p⁵ ≈ 2^154.5 ≥ 2^128`) guard-constrained descriptor. The original M0 descriptor that
lived in this file (`guardedHidingSpanDesc`, ONE BabyBear blinding felt, `|R| ≈ 2^31` —
grindable in seconds; the arity-10 stage-2 tooth `hole_commit = A(MID ‖ [BLINDING, 0])`) was
DELETED in the felt-width cutover of 2026-07-23: keeping it emitted alongside the wide-blind
descriptor kept the ~31-bit hiding sin alive in the emitted set. Its refinement theorems were
not lost — they exist STRENGTHENED over the wide-blind descriptor
(`GuardedHidingSpanWideBlindRefine`: commit-binds, two-openings-collide;
`GuardedHidingSpanGuardWeld`: the grounded no-`hGuard` keystone;
`Dregg2.Crypto.BindingSurvivesSimulation`: simulation-survival), and the parse composition is
untouched in `GuardedHidingSpanRefine`.

What REMAINS here is exactly the family-shared algebra:

  * the PI surface `[C_T(8), hole_commit(8), guard_table_commitment(8)]`
    (`piCT`/`piHOLE`/`piGUARD`/`GHS_PI_COUNT`) — identical for every member;
  * `wideFoldPair` — the stage-1 balanced wide fold `A16(l ‖ r)` (the same shape
    `BlindedMembershipWideEmit.wideFold4` uses);
  * the decidable demo absorb (`demoAbsorb`) + demo digests (`dA`/`dB`/`cT0`) the
    discrimination `#guard`s of the wide-blind Emit consume.

## Felt-width — the WIDE family, no lane-0 squeeze (`docs/FAITHFUL-COMMITMENT-LAW.md`)

Everything is based on the WIDE node-fold family `BlindedMembershipWideEmit.lean`, NOT the
deployed depth-2 single-felt `hash_4_to_1` Merkle nodes (the ~31-bit wound the campaign exists
to close). Every digest value in the family is `Digest8` (`Fin 8 → ℤ`, `circuit/src/faithful8.rs`)
and every fold absorbs all 8 lanes of each group and BINDS all 8 output lanes via
`chipLookupTupleN` (the wide lever `chip_lookup_sound_N`). No lane-0 squeeze anywhere. The
blinding axis is wide too — see `GuardedHidingSpanWideBlindEmit` §"THE FINDING this file closes".

## Axiom hygiene

Pure definitions + a non-vacuity `#guard`. `#assert_axioms` ⊆ {propext, Classical.choice,
Quot.sound}.
-/
import Dregg2.Circuit.Emit.BlindedMembershipWideEmit

namespace Dregg2.Circuit.Emit.GuardedHidingSpanEmit

open Dregg2.Circuit.DeployedCapTree (Digest8)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (pack8)

set_option autoImplicit false

/-! ## §1 — the family PI surface: `[C_T(8), hole_commit(8), guard_table_commitment(8)]`. -/

/-- PI slots 0..7: the public 8-felt context commitment `C_T`. -/
def piCT (k : Fin 8) : Nat := k.val
/-- PI slots 8..15: the published 8-felt blinded `hole_commit`. -/
def piHOLE (k : Fin 8) : Nat := 8 + k.val
/-- PI slots 16..23: the public 8-felt `guard_table_commitment`. -/
def piGUARD (k : Fin 8) : Nat := 16 + k.val
/-- Number of public inputs: `[C_T(8), hole_commit(8), guard_table_commitment(8)]`. -/
def GHS_PI_COUNT : Nat := 24

/-! ## §2 — the WIDE stage-1 fold (shared by every family member).

`absorb : List ℤ → Digest8` is the wide squeeze (`wPermOut absorb` is the sound wide chip
table's `permOut`). The fold absorbs whole 8-lane groups; nothing rides lane 0. -/

/-- The wide 2-ary node fold `A16(l ‖ r)` — the same balanced absorb `wideFold4` uses. -/
def wideFoldPair (absorb : List ℤ → Digest8) (l r : Digest8) : Digest8 := absorb (pack8 l r)

/-! ## §3 — the decidable demo absorb + demo digests (for discrimination `#guard`s). -/

/-- A concrete `absorb` (an injective `Encodable` list-encoding into lane 0, zeros elsewhere) for
non-vacuity `#guard`s: NOT the real Poseidon2, but a decidable stand-in that makes fold
DISCRIMINATION checkable. -/
def demoAbsorb : List ℤ → Digest8 := fun xs => fun k => if k = 0 then (xs.foldl (fun acc x => acc * 7 + x + 1) 0) else 0

/-- Two concrete 8-felt digests differing in lane 3. -/
def dA : Digest8 := fun k => if k = 3 then 5 else 0
def dB : Digest8 := fun k => if k = 3 then 9 else 0
def cT0 : Digest8 := fun k => if k = 0 then 2 else 0

-- The stage-1 fold discriminates (non-vacuity of the shared fold under the demo absorb).
#guard decide (wideFoldPair demoAbsorb dA cT0 ≠ wideFoldPair demoAbsorb dB cT0)

end Dregg2.Circuit.Emit.GuardedHidingSpanEmit
