/-
# Dregg2.Verify.TacticsG — deprecated import path; production tactics live in `Verify/Tactics` §8.
-/
import Dregg2.Verify.Tactics

namespace Dregg2.Verify.Production

macro "carry_foreverG" Good:term : tactic =>
  `(tactic| carry_forever_production $Good)

macro "exec_frameG" : tactic => `(tactic| exec_frame_production)

abbrev logMonoG_via_tactics := logMono_via_tactics
abbrev revoked_growG_via_tactics := revoked_grow_via_tactics
abbrev identity_revoked_foreverG_via_tactics := identity_revoked_forever_via_tactics

end Dregg2.Verify.Production