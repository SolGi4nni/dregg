import Dregg2.Circuit.Emit.AdjacencyMembershipRefine

namespace Dregg2.Circuit.Emit.AdjacencyMembershipRefineAudit

open Dregg2.Circuit.Emit.AdjacencyMembershipRefine

-- (a) The Satisfied2 hypothesis is genuinely INHABITED (kernel-checked concrete witness).
#check (concrete_sat)
-- (b) A wrong witness genuinely FAILS Satisfied2 (the descriptor really constrains).
#check (concrete_fail)

-- (c) The authored semantic def is non-trivial: TRUE and FALSE separated, order-sensitive.
#check (demo_adjacent)
#check (demo_not_adjacent)

-- (d) Independent axiom audit (NOT trusting the author's #assert_axioms).
#print axioms adjacency_sat_refines
#print axioms adjacency_full_bridge
#print axioms combine_of_gates
#print axioms fold_generic
#print axioms concrete_sat
#print axioms concrete_fail

end Dregg2.Circuit.Emit.AdjacencyMembershipRefineAudit
