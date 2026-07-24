/-
# Dregg2.Circuit.Emit.MerkleMembership4aryEmit — deployed 4-ary Merkle membership

Architectural law #1: this module is the sole author of the algebra consumed by
`circuit::merkle_air`.  Rust parses the emitted IR2 bytes and supplies witnesses;
it does not construct constraints.

The six position/arrangement gates, parent Poseidon2 chip lookup, continuity
window, and last-row repairs are shared with the already-proved depth-general
blinded-membership family.  This unblinded descriptor changes only the public
binding: row-0 `cur` is PI 0 and last-row `par` is PI 1.

## E7 narrowing (`ChipNarrowLookup.lean`)

The parent lookup rides the 18-wide `TID_P2_NARROW` bus (`gParentLookupNarrow`), served by the
18-prefix of the SAME chip rows (`descriptor_ir2.rs::narrow_hist`).  The seven exposed permutation
lanes never entered the soundness conclusion, and here they are the trailing suffix `[11, 18)`, so
the truncation moves NO column index.  Trace width 18 -> 11.
-/
import Dregg2.Circuit.Emit.BlindedMembershipEmit

namespace Dregg2.Circuit.Emit.MerkleMembership4aryEmit

open Dregg2.Circuit.Emit.BlindedMembershipEmit
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 VmConstraint2 emitVmJson2)

/-- PI 0 is the member leaf. -/
def PI_LEAF : Nat := 0
/-- PI 1 is the committed root. -/
def PI_ROOT : Nat := 1

/-- Bind the first running value to the public member leaf. -/
def leafPin : VmConstraint2 := .base (.piBinding VmRow.first gCUR PI_LEAF)
/-- Bind the last computed parent to the public root. -/
def rootPin : VmConstraint2 := .base (.piBinding VmRow.last gPAR PI_ROOT)

/-- The complete depth-uniform membership constraint block. -/
def membership4aryConstraints : List VmConstraint2 :=
  gPerRowGates ++ [gParentLookupNarrow, gContinuity, leafPin, rootPin] ++ gLastRowBoundaries

/--
The deployed, depth-general, 4-ary Merkle-membership descriptor.  Tree depth is
the trace height; the algebra and verification key are deliberately uniform for
every supported power-of-two depth.
-/
def membership4aryDesc : EffectVmDescriptor2 :=
  { name        := "dregg-merkle-membership-4ary-general::v1"
  , traceWidth  := 11
  , piCount     := 2
  , tables      := []
  , constraints := membership4aryConstraints
  , hashSites   := []
  , ranges      := [] }

-- Non-vacuous structural pins.  The exact emitted-byte pin follows the literal
-- golden below; it is generated once from `emitVmJson2 membership4aryDesc`.
#guard membership4aryDesc.traceWidth == 11
-- The narrowing dropped exactly CHIP_OUT_LANES - 1 = 7 main columns for the same forced digest
-- equation.
#guard membership4aryDesc.traceWidth + (Dregg2.Circuit.DescriptorIR2.CHIP_OUT_LANES - 1) == 18
#guard Dregg2.Circuit.DescriptorIR2.poseidon2narrow.wireId == 8
#guard membership4aryDesc.piCount == 2
#guard membership4aryDesc.constraints.length == 16
#guard membership4aryDesc.tables.length == 0

/-- Exact emitted-wire golden.  Rust includes these bytes verbatim. -/
def MEMBERSHIP_4ARY_GOLDEN : String :=
  "{\"name\":\"dregg-merkle-membership-4ary-general::v1\",\"ir\":2,\"trace_width\":11,\"public_input_count\":2,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":4}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":5}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"var\",\"v\":5}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":5}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}}}}}},{\"t\":\"lookup\",\"table\":8,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"var\",\"v\":6},{\"t\":\"var\",\"v\":7},{\"t\":\"var\",\"v\":8},{\"t\":\"var\",\"v\":9},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":10}]},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":10}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":10,\"pi_index\":1},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":4}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":5}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":5}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"var\",\"v\":5}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":5}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}}}}}}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 membership4aryDesc == MEMBERSHIP_4ARY_GOLDEN

theorem descriptor_has_complete_shape :
    membership4aryDesc.constraints =
      gPerRowGates ++ [gParentLookupNarrow, gContinuity, leafPin, rootPin]
        ++ gLastRowBoundaries := rfl

#assert_axioms descriptor_has_complete_shape

end Dregg2.Circuit.Emit.MerkleMembership4aryEmit
