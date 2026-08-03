/-
# `MinaStepSrsLagrangePin` — ⚑ the SRS this tree computes IS Mina's devnet SRS

`MinaStepSrsLagrange` carries the STEP URS's Lagrange commitments that `wrap_verifier.ml:539-616`'s
x_hat MSM scales. On its own that is a list of numbers a binary printed, which is exactly the shape
this campaign has been burned by: a fixture wearing the name of a derived object.

This module is the pin, and it is deliberately SEPARATE from both the data and the consumer:
`MinaWrapSrsG` is 5.4 MB of devnet SRS and `KimchiWrapMain` should not pay for it on every rebuild,
but CI should still be unable to land a wrong SRS. So the data module is light, the assembly imports
only the data, and the equality lives here, rooted from `Dregg2.lean`.

## What is actually being pinned

`SRS::<G>::create(depth)` is DETERMINISTIC and curve-generic — `g[i] = point_of_random_bytes(G::Map,
Blake2b512(i as u32 big-endian))` (`poly-commitment/src/ipa.rs:532-542`) — and it is the code path
`Kimchi_bindings.Protocol.SRS.Fp.create` runs inside a Mina node. `xhat_lagrange_export` calls it on
**Pallas** at depth 16 and on **Vesta** at depth 65536 out of the same binary.

`MinaWrapSrsG.blk0` is the first block of `srs.g` of the **devnet blockchain Wrap SRS**, dumped from
a real Mina node by `wrap_group_export.rs` — 32768 Pallas points in projective form at `z = 1`, a
list generated years apart from and by different code than the extractor.

So `srs_construction_is_the_devnet_srs` says: the construction this tree runs agrees, coordinate for
coordinate, with the SRS a running Mina node handed us. It is that agreement, not the extractor's own
say-so, that makes `LAGRANGE_XY` Mina's step URS's Lagrange basis rather than 134 numbers.

⚠ The pin is on the PALLAS head because that is where an independent devnet dump exists. It does not
observe the Vesta basis directly; what it establishes is that `SRS::create` — the single generic
function both halves go through — reproduces Mina's generators. That is stated rather than banked.

No `sorry`, no `native_decide`; `decide` closes a list equality in the kernel.
-/
import Dregg2.Tactics
import Dregg2.Circuit.Emit.MinaStepSrsLagrange
import Dregg2.Circuit.Emit.MinaWrapSrsG

namespace Dregg2.Circuit.Emit.MinaStepSrsLagrangePin

open Dregg2.Circuit.Emit.MinaStepSrsLagrange (PALLAS_G_HEAD_XY LAGRANGE_XY CORRECTION_XY WIDTHS
  XHAT_TERMS DOMAIN_SIZE STEP_LOG2)

set_option autoImplicit false
set_option maxRecDepth 100000

/-- The devnet SRS's first sixteen generators, projected from projective `(x, y, 1)` to the flat
`(x, y)` list shape the extractor prints. -/
def devnetHeadXY : List Nat :=
  (Dregg2.Circuit.Emit.MinaWrapSrsG.blk0.take 16).flatMap (fun p => [p.1, p.2.1])

/-- ⚑ **THE TWO-SOURCE PIN.** `SRS::<Pallas>::create(16).g` equals the devnet blockchain Wrap SRS's
own first sixteen generators, all thirty-two coordinates. -/
theorem srs_construction_is_the_devnet_srs : PALLAS_G_HEAD_XY = devnetHeadXY := by decide

/-- …and it is a REAL check: the head is thirty-two distinct nonzero coordinates, not an empty list
two `take`s agree on vacuously. -/
theorem srs_head_is_thirty_two_nonzero :
    PALLAS_G_HEAD_XY.length = 32 ∧ PALLAS_G_HEAD_XY.all (· != 0) = true := by decide

/-- The devnet block this is read out of is not degenerate either. -/
theorem devnet_head_is_thirty_two : devnetHeadXY.length = 32 := by decide

/-- The Lagrange export's own shape: 67 entries, `(x, y)` each. -/
theorem lagrange_is_two_per_term : LAGRANGE_XY.length = 2 * XHAT_TERMS := by decide

/-- The correction list covers exactly the entries whose width is not 1 — the
`Add_with_correction` partition (`wrap_verifier.ml:571-582`). -/
theorem corrections_cover_the_non_cond_add_partition :
    CORRECTION_XY.length = 2 * (WIDTHS.filter (· != 1)).length := by decide

/-- ⚑ The width census, off the EXTRACTOR's list rather than the Lean transcription:
15 x 255, 40 x 128, 12 x 1, and nothing else. -/
theorem width_census :
    (WIDTHS.filter (· == 255)).length = 15
  ∧ (WIDTHS.filter (· == 128)).length = 40
  ∧ (WIDTHS.filter (· == 1)).length = 12
  ∧ WIDTHS.length = XHAT_TERMS := by decide

/-- The domain the basis was taken at is `2 ^ Common.Max_degree.step_log2`. -/
theorem domain_is_two_pow_step_log2 : DOMAIN_SIZE = 2 ^ STEP_LOG2 ∧ STEP_LOG2 = 16 := by decide

/-- No Lagrange commitment came back as the point at infinity — `to_coordinates` would have
succeeded on `(0,0)` and a zero base is a ladder over nothing. -/
theorem no_lagrange_coordinate_is_zero : LAGRANGE_XY.all (· != 0) = true := by decide

#assert_namespace_axioms Dregg2.Circuit.Emit.MinaStepSrsLagrangePin

end Dregg2.Circuit.Emit.MinaStepSrsLagrangePin
