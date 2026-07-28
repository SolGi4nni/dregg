import Dregg2.Circuit.Emit.MinaWrapOpeningGate
/-!
# Dregg2.Circuit.Emit.MinaWrapOpeningWeld — 5d ⋈ 5f: the opening relation on the aggregate the
kernel BUILT, not the one it was handed.

`MinaWrapOpeningGate.opening_relation_holds` states the IPA opening relation with the 47-term
aggregate as `COMBINED_GOLD`, o1-labs' own value. `MinaWrapAggregationGate` separately proved
our Horner fold over the block's 47 real commitments reproduces it, and that the `ft_comm` slot of
that fold can be filled by the point `MinaWrapGroupGate` assembled. This file removes the last
step of hand-off: the relation is restated with `MinaWrapAggregationGate.combinedComm` — the fold
itself — in the aggregate's place.

Separate module for the same measured reason `MinaWrapAggregationGate` is separate: this theorem
is 46 (fold) + 34 (relation) = **80 × 255-bit ladders in one `decide`**, and it is the largest
single elaboration in the chain — **75 s** measured on hbox. Splitting keeps each `lean` process
bounded.

Axiom-clean; no `sorry`, no `native_decide`. NOT imported by the `Dregg2` root. Import line:
`import Dregg2.Circuit.Emit.MinaWrapOpeningWeld`
-/

namespace Dregg2.Circuit.Emit.MinaWrapOpeningWeld

open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaCurveComplete (isInfM)
open Dregg2.Circuit.Emit.MinaWrapOpeningGate
  (C Z1 Z2 CHAL CHAL_INV U_BASE SG DELTA openingResidual)

set_option autoImplicit false
set_option maxRecDepth 20000000
set_option maxHeartbeats 8000000

/-- ⚑ **`opening_relation_holds_on_our_own_aggregate`** — the opening relation of Mina devnet
block 539508, with the 47-term `Σ ξⁱ·Cᵢ` supplied by the kernel's OWN Horner fold over the
block's 47 commitments rather than by o1-labs' dumped aggregate. Nothing between the block's raw
Pallas points and the opening equation is now taken on report. -/
theorem opening_relation_holds_on_our_own_aggregate :
    isInfM pN (openingResidual C Z1 Z2 CHAL CHAL_INV
      Dregg2.Circuit.Emit.MinaWrapAggregationGate.combinedComm U_BASE SG DELTA) = true := by
  decide

#assert_namespace_axioms Dregg2.Circuit.Emit.MinaWrapOpeningWeld

end Dregg2.Circuit.Emit.MinaWrapOpeningWeld
