/-
# Dregg2.Verify.FramesG — deprecated import path; production frames live in `Verify/Frames` §6.
-/
import Dregg2.Verify.Frames

namespace Dregg2.Verify

open Production

abbrev execFullForestG_revoked_subset_grow := execForestG_revoked_subset_grow
abbrev execFullForestG_commitments_grow := execForestG_commitments_grow
abbrev execFullForestG_nullifiers_grow := execForestG_nullifiers_grow
abbrev execFullForestG_logMono := execForestG_logMono
abbrev cellNextG_carries_rel {α : Type _} (R : α → α → Prop) [Trans R R R] :=
  Production.cellNextG_carries_rel (R := R)

end Dregg2.Verify