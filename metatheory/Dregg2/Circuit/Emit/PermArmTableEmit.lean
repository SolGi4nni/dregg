/-
# `PermArmTableEmit` — the two permutation arms as STANDALONE table AIRs.

## ⚑ WHAT THIS IS FOR, AND WHAT IT IS NOT

`Poseidon2RoundGates` §8 lands `permEmissionNarrow` beside the deployed `permEmission` and relates
them (§8e). Both live there as `(defs, gates)` pairs — Lean objects with no wire form. This file
gives each one a **`TableAir` of its own**, so the emitted bytes exist and Rust can:

* run the **narrow arm's gates against the narrow WITNESS GENERATOR's output**
  (`plonky3_prover::poseidon2_permute_aux_witness_narrow`), which is the half §8 cannot see — Lean
  checks its own projection `narrowAuxWitness`, not a Rust program;
* **prove and verify both arms through the SAME interpreter** (`Ir2Air::LeanTable`), so a
  measurement of one against the other is a measurement of the arithmetization and not of two
  different Rust harnesses.

⚠ **NEITHER TABLE IS DEPLOYED, AND NEITHER IS ROUTED THROUGH `EmitTableAirs.lean`.** The deployed
chip is `ChipTableEmit.chipTable` (`CHIP_WIDTH = 386`, the wide arm) and this file does not move it.
These two are measurement/fidelity fixtures, emitted by `EmitPermArms.lean` into
`circuit/tests/fixtures/perm-arms/`. When the chip cuts over (`Poseidon2RoundGates` §8g), what
changes is `ChipTableEmit`, not this file — and this file's WIDE arm becomes the thing to delete.

## Law #1

The constraints are `permEmission` / `permEmissionNarrow`, authored in `Poseidon2RoundGates.lean`
and proved there. This file adds **no gate of its own**: it wraps existing gate lists in a
`TableAir` record with a width and a name. Rust interprets; Rust authors nothing.

## The layout

Both tables are `[seed ‖ aux]`: the sixteen permutation input lanes at columns `0..15`, then the
arm's committed aux block from column `16`.

| | wide | narrow |
|---|---|---|
| `width` | 16 + 352 = **368** | 16 + 141 = **157** |
| gates | 352 | **141** |
| `defs` | 1,078 | 1,286 |
| max degree | 7 | 7 |

There are no bus interactions and no preprocessed columns: an arm on its own serves nothing. That
is deliberate — a lookup argument would put permutation-independent work into the measurement.
-/
import Dregg2.Circuit.Emit.Poseidon2RoundGates

namespace Dregg2.Circuit.Emit.PermArmTableEmit

open Dregg2.Circuit.TableAirIR (TExpr TableAir TableGate emitTableAirJson v gAll)
open Dregg2.Circuit.Emit.Poseidon2RoundGates
  (WIDTH POSEIDON2_AUX_COLS NARROW_AUX_COLS permEmission permEmissionNarrow
   maxGateDeg emissionOps)

set_option autoImplicit false

/-! ## §1 — The column layout shared by both arms. -/

/-- The permutation input lanes start at column 0. -/
def ARM_IN0 : Nat := 0
/-- …and the committed aux block starts right after them. -/
def ARM_AUX0 : Nat := ARM_IN0 + WIDTH

/-- The seed a caller supplies: sixteen committed columns. -/
def armSeed : List TExpr := (List.range WIDTH).map (fun i => v (ARM_IN0 + i))

/-- Total width of the WIDE arm's standalone table. -/
def ARM_WIDE_WIDTH : Nat := ARM_AUX0 + POSEIDON2_AUX_COLS
/-- Total width of the NARROW arm's standalone table — the number the whole exercise is about. -/
def ARM_NARROW_WIDTH : Nat := ARM_AUX0 + NARROW_AUX_COLS

/-! ## §2 — The two tables. -/

/-- The DEPLOYED algebra, standalone: `permEmission` at `ARM_AUX0`. -/
def permWideArm : List TExpr × List TExpr := permEmission ARM_AUX0 0 armSeed

/-- The NARROW algebra, standalone: `permEmissionNarrow` at `ARM_AUX0`. -/
def permNarrowArm : List TExpr × List TExpr := permEmissionNarrow ARM_AUX0 0 armSeed

/-- **`permWideArmTable`** — the 352-column arm as a table AIR. Measurement baseline. -/
def permWideArmTable : TableAir :=
  { name         := "dregg-perm-arm-wide-v1"
  , width        := ARM_WIDE_WIDTH
  , prepWidth    := 0
  , defs         := permWideArm.1
  , gates        := permWideArm.2.map gAll
  , interactions := [] }

/-- **`permNarrowArmTable`** — the 141-column arm as a table AIR. This is the object the Rust
narrow witness generator is checked against. -/
def permNarrowArmTable : TableAir :=
  { name         := "dregg-perm-arm-narrow-v1"
  , width        := ARM_NARROW_WIDTH
  , prepWidth    := 0
  , defs         := permNarrowArm.1
  , gates        := permNarrowArm.2.map gAll
  , interactions := [] }

/-! ## §3 — Shape pins on the EMITTED records.

⚠ These are `native_decide` + `#assert_compiled`, the same confession `Poseidon2RoundGates` §8b–§8f
makes: they are compiled evaluation of the emitted objects, named rather than left as a `#guard`.
The kernel-clean facts they rest on (`narrow_aux_cols_is_141`, `narrow_blocks_tile`,
`narrow_accepts_exactly_the_wide_witnesses`) are proved where the arms are authored. -/

/-- The two widths, derived rather than transcribed. -/
theorem arm_widths : ARM_WIDE_WIDTH = 368 ∧ ARM_NARROW_WIDTH = 157 := by
  constructor <;> rfl
#assert_axioms arm_widths

/-- ⚑ **THE EMITTED TABLES' SHAPE.** Gate counts one per committed aux column on both arms, the
definition lists in topological order (so a single left-to-right pass resolves every `shr`), no
preprocessed columns, and no interaction on either side. A `sharesBelow` failure here is what a
mis-based splice looks like, and the Rust parser refuses it too — this is the pin that sees it in
Lean first. -/
theorem arm_tables_shape :
    ((permWideArmTable.gates.length == POSEIDON2_AUX_COLS) &&
     (permNarrowArmTable.gates.length == NARROW_AUX_COLS) &&
     (permWideArmTable.width == ARM_WIDE_WIDTH) &&
     (permNarrowArmTable.width == ARM_NARROW_WIDTH) &&
     (permWideArmTable.prepWidth == 0) && (permNarrowArmTable.prepWidth == 0) &&
     (permWideArmTable.interactions.isEmpty) && (permNarrowArmTable.interactions.isEmpty) &&
     (permWideArmTable.defs.zipIdx.all (fun p => p.1.sharesBelow p.2)) &&
     (permNarrowArmTable.defs.zipIdx.all (fun p => p.1.sharesBelow p.2))) = true := by
  native_decide
#assert_compiled arm_tables_shape

/-- ⚑ **THE COMMITTED-CELL RATIO, ON THE OBJECTS THAT GET EMITTED** — and the degree, which is the
half a virtualization gets wrong. 368 columns against 157 is **2.34× on the aux block** (352 : 141)
and 2.34× on the whole standalone row; both arms stay at `max_constraint_degree = 7`, so the FRI
ledger and the `log_blowup` floor are unmoved and the win has nothing to trade against.

⚠ 2.34× is the PER-PERMUTATION figure. What a deployed batch pays is that ratio weighted by the
chip's share of committed width, which is a different and much smaller number — measured in
`circuit/tests/poseidon2_narrow_witness.rs`, not asserted here. -/
theorem arm_cost_ratio :
    ((maxGateDeg permWideArm.1 permWideArm.2 == 7) &&
     (maxGateDeg permNarrowArm.1 permNarrowArm.2 == 7) &&
     (POSEIDON2_AUX_COLS * 100 / NARROW_AUX_COLS == 249) &&
     (emissionOps permNarrowArm < emissionOps permWideArm)) = true := by
  native_decide
#assert_compiled arm_cost_ratio

/-! ## §4 — The emitted bytes, for `EmitPermArms.lean`. -/

/-- The routing table the emitter walks: artifact filename ↦ its Lean author. -/
def permArmTables : List (String × TableAir) :=
  [ ("dregg-perm-arm-wide-v1.json",   permWideArmTable)
  , ("dregg-perm-arm-narrow-v1.json", permNarrowArmTable) ]

/-- Both arms are routed. A table added here and forgotten in the list emits no artifact and
nothing else would notice — the same reason `EmitTableAirs.lean` states its count. -/
theorem permArmTables_routes_both : permArmTables.length = 2 := by decide
#assert_axioms permArmTables_routes_both

/-- The renderer, so the emitter script is a `for` loop and nothing else. -/
def emitPermArmLines : List String :=
  permArmTables.map (fun p => s!"{p.1}\t{emitTableAirJson p.2}")

end Dregg2.Circuit.Emit.PermArmTableEmit
