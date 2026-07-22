(* Shared golden and adversarial specimens for wire version 1. *)

val canonicalTop = [68, 82, 69, 71, 1, 1, 17]

(* a0 and (not a1 or a2), followed by its unique canonical target. *)
val canonicalPolicy =
  [68, 82, 69, 71, 1,
   4, 0, 0, 5, 3, 0, 1, 0, 2,
   20, 16, 0, 21, 19, 16, 1, 16, 2]

(* Structurally valid, but the claimed target is Truth instead of Input 0. *)
val nonCanonicalTarget = [68, 82, 69, 71, 1, 0, 0, 17]

val adversarialFixtures =
  [ ("empty", [])
  , ("truncated magic", [68, 82, 69])
  , ("wrong magic", [68, 82, 69, 72, 1, 1, 17])
  , ("unknown version", [68, 82, 69, 71, 2, 1, 17])
  , ("negative byte", [68, 82, 69, 71, 1, ~1, 17])
  , ("oversized byte", [68, 82, 69, 71, 1, 256, 17])
  , ("unknown source tag", [68, 82, 69, 71, 1, 6, 17])
  , ("unknown target tag", [68, 82, 69, 71, 1, 1, 22])
  , ("missing source operand", [68, 82, 69, 71, 1, 3])
  , ("missing target operand", [68, 82, 69, 71, 1, 1, 19])
  , ("trailing byte", [68, 82, 69, 71, 1, 1, 17, 0])
  , ("non-canonical target", nonCanonicalTarget)
  ]

