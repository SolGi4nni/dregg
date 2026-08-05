import Dregg2.Circuit.Emit.KimchiStepMainFixture
open Dregg2.Circuit.Emit.KimchiStepMain
set_option maxRecDepth 100000
/-- ONE `native_decide`, forcing exactly `mkStep shapeStep` + `rungRows .opening` and nothing else.
This is the per-command FLOOR every committed-shape theorem in the census pays. -/
theorem floor_one_command : (rungRows (mkStep shapeStep) .opening true).length > 0 := by
  native_decide
