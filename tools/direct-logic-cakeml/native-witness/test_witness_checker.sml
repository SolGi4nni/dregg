use "../checker.sml";
use "../live_checker.sml";
use "witness_checker.sml";

fun fail message =
  (TextIO.output (TextIO.stdErr, "FAIL: " ^ message ^ "\n");
   OS.Process.exit OS.Process.failure)

fun expectTrue (name, value) = if value then () else fail name
fun expectFalse (name, value) = if value then fail name else ()

fun mustSome value =
  case value of SOME x => x | NONE => fail "unexpected NONE"

fun replaceAt (index, replacement, bytes) =
  case (index, bytes) of
      (_, []) => []
    | (0, _ :: rest) => replacement :: rest
    | (n, x :: rest) => x :: replaceAt (n - 1, replacement, rest)

val policy = And (Atom 0, Or (Not (Atom 1), Atom 2))
val livePolicy = mustSome (certifyLiveBytes (3, policy))
val accepting = mustSome (certifyWitnessBytes (livePolicy, [1, 0, 0]))
val alternateAccepting = mustSome (certifyWitnessBytes (livePolicy, [1, 1, 1]))
val falseSemantic = mustSome (certifyWitnessBytes (livePolicy, [0, 0, 0]))
val nonBoolean = mustSome (packWitnessUnchecked (livePolicy, [1, 2, 0]))
val shortRow = mustSome (packWitnessUnchecked (livePolicy, [1, 0]))
val descriptorTamper =
  mustSome (packWitnessUnchecked
    (replaceAt (listLength livePolicy - 1, 124, livePolicy), [1, 0, 0]))

val allRows =
  [[0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1],
   [1, 0, 0], [1, 0, 1], [1, 1, 0], [1, 1, 1]]

fun checkSemanticRow row =
  let val envelope = mustSome (certifyWitnessBytes (livePolicy, row))
  in checkWitnessBytes envelope = sourceEval row policy end

val _ = expectTrue ("exhaustive three-atom semantic differential failed",
  List.all checkSemanticRow allRows)

val _ = expectTrue ("canonical satisfying witness rejected",
  checkWitnessBytes accepting)
val _ = expectTrue ("alternate satisfying witness rejected",
  checkWitnessBytes alternateAccepting)
val _ = expectFalse ("false semantic witness accepted",
  checkWitnessBytes falseSemantic)
val _ = expectFalse ("non-Boolean witness accepted",
  checkWitnessBytes nonBoolean)
val _ = expectFalse ("wrong witness length accepted",
  checkWitnessBytes shortRow)
val _ = expectFalse ("descriptor tamper accepted",
  checkWitnessBytes descriptorTamper)
val _ = expectFalse ("trailing byte accepted", checkWitnessBytes (accepting @ [0]))
val _ = expectFalse ("truncation accepted",
  checkWitnessBytes (List.take (accepting, listLength accepting - 1)))
val _ = expectFalse ("unknown envelope version accepted",
  checkWitnessBytes (replaceAt (4, 2, accepting)))
val _ = expectFalse ("live-section length mutation accepted",
  checkWitnessBytes (replaceAt (8, 0, accepting)))
val _ = expectFalse ("invalid witness certified",
  Option.isSome (certifyWitnessBytes (livePolicy, [1, 2, 0])))
val _ = expectFalse ("wrong-length witness certified",
  Option.isSome (certifyWitnessBytes (livePolicy, [1, 0])))

val _ = print "direct-logic witness SML checker: exhaustive 8 rows + 12 hostile/golden checks passed\n"
