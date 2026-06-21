/-
# Metatheory.PolisNonConfusionCircuit — the circuit-dependent non-confusion pin.

Split out of `Metatheory.PolisNonConfusion` because it pulls the circuit-emit tree
(`Dregg2.Circuit.*`), which may be mid-edit by concurrent circuit work. Isolating it keeps
the rest of the non-confusion floor green regardless. When the circuit tree is green this
file builds; it carries the third non-confusion leg:

  * `noteSpendFresh_rejects_double` — copying a spent-note receipt does NOT resurrect the
    value: the persistent trace (nullifier/receipt) is freely copyable; the linear value it
    records is not — the in-circuit non-membership bites on a double-spend.
-/
import Dregg2.Tactics
import Dregg2.Circuit.RotatedKernelRefinementNotesFresh

namespace Metatheory.PolisNonConfusionCircuit

#assert_axioms Dregg2.Circuit.RotatedKernelRefinementNotesFresh.noteSpendFresh_rejects_double

end Metatheory.PolisNonConfusionCircuit
