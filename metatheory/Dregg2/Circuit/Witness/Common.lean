/-
# Dregg2.Circuit.Witness.Common — the SHARED concrete commitment surface + witness-layout helpers
for the per-effect witness generators (batch B3).

`Dregg2.Circuit.TransferWitness` closed the verifiable-execution beachhead for `Transfer`: a CONCRETE
witness GENERATOR (`transferWitnessVec`) that RUNS the real executor and lays out the full-state
witness as a flat `List Int` with the digest columns filled by a CONCRETE commitment surface, plus the
concrete `#guard`s (honest SATISFIES, real forged post-state UNSAT) and the JSON the Rust prover
consumes. This module hoists the surface + helpers SHARED by the v1 (`EffectCommit`) per-effect
witness generators that amplify that beachhead to the rest of the effect set.

The CONCRETE surface reuses `StateCommit`'s already-fixed injective toy primitives (`chConcrete`,
`rhConcrete`, `cmbConcrete`, `compressNConcrete`) and adds ONE concrete log hash `lhConcrete` (an
injective positional Horner fold over the receipt rows' `(actor,src,dst,amt)` fields — the log analog
of `compressNConcrete`, so the log-bind gate binds the receipt chain). It is packaged as a
`CommitSurface` value `SConc` the generic framework consumes.

The witness LAYOUT helper `layoutE` tabulates `encodeE SConc E pre args post` over `[0, 74)`, then
ZEROES the two ROOT columns (`vEPreRoot = 64`, `vEPostRoot = 65`). The roots are UNCONSTRAINED by the
five gates (guard ∧ rest ∧ frame ∧ touched ∧ log), so zeroing them preserves satisfaction while
keeping every emitted number inside `i64` (the concrete sponge over the live cells produces a ~10³⁰
root that would overflow the Rust prover's `i64` parser; the CONSTRAINED frame/touched/log digest
wires `66..73` are ~10¹⁸ and fit). This mirrors `TransferWitness`, whose root wires happened to fit
i64 (a 2-leaf `compress`, not the full sponge); zeroing the unconstrained roots is the robust analog.
-/
import Dregg2.Circuit.EffectCommit
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.Common

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit
open Dregg2.Circuit.StateCommit
open Dregg2.Exec

set_option linter.dupNamespace false

/-! ## §0 — decidability re-exports (so the per-effect concrete `#guard`s can `decide`). -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §1 — the concrete log hash + the concrete `CommitSurface`.

NOTE: `lhConcrete` is now the CR-grounded `Poseidon2Surface.turnLogDigest` (the `refP2` sponge over the
FULL `encTurnRec`, realizing the real `babyBearD4W16` Poseidon2). The OLD `acc*10⁶ + actor*1000 +
src*100 + dst*10 + amt` packing bound the four fields but ALIASED across the per-field windows (an `amt ≥
10` carried into `dst`, etc.); the field-binding `encTurnRec` does not. The sponge `compressN`/`cmb`/`CH`
remain the injective `StateCommit` primitives, so the whole `SConc` surface is now binding. -/

/-- **`lhConcrete`** — the concrete receipt-chain hash: an INJECTIVE positional Horner fold over the
`(actor,src,dst,amt)` of each receipt row (each row shifted by a base larger than any toy row field),
with the length folded in so distinct-length chains never collide. A genuine binding commitment to the
receipt list (NOT a lossy sum, and it does NOT drop `src`/`dst`), so the log-bind gate catches
a forged receipt. -/
def lhConcrete : List Turn → ℤ := Dregg2.Circuit.Poseidon2Surface.turnLogDigest

/-- **`SConc`** — the concrete commitment surface for the witness generators: the `StateCommit`
injective primitives plus `lhConcrete`. Every digest column the witness lays out is a REAL field number
under this surface (the Rust prover consumes them), and every primitive is injective on the toy domain
(so the anti-ghost `#guard`s fire on a binding commitment). -/
def SConc : CommitSurface :=
  { CH := chConcrete, RH := rhConcrete, cmb := cmbConcrete
    compressN := compressNConcrete, LH := lhConcrete }

/-! ## §2 — the witness layout helper.

`layoutE E pre args post` tabulates `encodeE SConc E pre args post` over `[0, 74)`, zeroing the two
unconstrained root columns so the result is i64-safe. The five gates read only wires
`{0, 66, 67, 68, 69, 70, 71, 72, 73}` (the guard bit + the four digest EQ pairs), none of which is a
root, so the zeroed layout SATISFIES `effectCircuit E` exactly when the un-zeroed `encodeE` does. -/

/-- The two root columns (`vEPreRoot = 64`, `vEPostRoot = 65`) — UNCONSTRAINED by the five gates. -/
def isRoot (v : Nat) : Bool := v == 64 || v == 65

/-- **`layoutE E pre args post`** — the flat `List Int` witness: `encodeE SConc E pre args post`
tabulated over `[0, 74)` with the two root columns zeroed. -/
def layoutE {St Args : Type} (E : EffectSpec St Args) (pre : St) (args : Args) (post : St) :
    List Int :=
  (List.range 74).map (fun v => if isRoot v then 0 else encodeE SConc E pre args post v)

/-- `layoutE` has the framework trace width (74). -/
theorem layoutE_length {St Args : Type} (E : EffectSpec St Args) (pre : St) (args : Args) (post : St) :
    (layoutE E pre args post).length = 74 := by
  simp [layoutE]

/-- Render a `List Int` as a JSON number array (the witness wire form the Rust prover ingests). -/
def witnessJson (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"

end Dregg2.Circuit.Witness.Common
