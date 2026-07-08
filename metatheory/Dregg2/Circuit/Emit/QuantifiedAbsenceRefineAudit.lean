import Dregg2.Circuit.Emit.QuantifiedAbsenceRefine

namespace Dregg2.Circuit.Emit.QuantifiedAbsenceRefineAudit

open Dregg2.Circuit.Emit.QuantifiedAbsenceRefine

-- (a) hypothesis genuinely inhabited: a satisfying Satisfied2 witness exists.
#check @quantifiedAbsence_sat
#check @quantifiedAbsence_sat_relation
-- (b) a wrong witness genuinely fails Satisfied2.
#check @quantifiedAbsence_bad
-- (c) the authored relation is a true-AND-false discriminator (not `fun _ => True`).
#check @quotientAbsenceRel_true
#check @quotientAbsenceRel_false
example : ¬ (∀ e w v a al, QuotientAbsenceRel e w v a al) :=
  fun hAll => quotientAbsenceRel_false (hAll _ _ _ _ _)

-- (d) independent axiom prints (not relying on the in-file #assert_axioms).
#print axioms quantifiedAbsence_refines
#print axioms quantifiedAbsence_sat
#print axioms quantifiedAbsence_bad
#print axioms quantifiedAbsence_sat_relation

-- independently re-assert kernel-cleanliness.
#assert_axioms quantifiedAbsence_refines
#assert_axioms quantifiedAbsence_sat
#assert_axioms quantifiedAbsence_bad

end Dregg2.Circuit.Emit.QuantifiedAbsenceRefineAudit
