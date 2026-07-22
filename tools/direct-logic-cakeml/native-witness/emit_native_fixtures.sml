use "../checker.sml";
use "../live_checker.sml";
use "witness_checker.sml";

fun fail message =
  (TextIO.output (TextIO.stdErr, "FAIL: " ^ message ^ "\n");
   OS.Process.exit OS.Process.failure)

fun mustSome value =
  case value of SOME x => x | NONE => fail "unexpected NONE"

fun replaceAt (index, replacement, bytes) =
  case (index, bytes) of
      (_, []) => []
    | (0, _ :: rest) => replacement :: rest
    | (n, x :: rest) => x :: replaceAt (n - 1, replacement, rest)

fun writeBytes (path, bytes) =
  let
    val stream = BinIO.openOut path
    val vector = Word8Vector.fromList (List.map Word8.fromInt bytes)
  in
    BinIO.output (stream, vector);
    BinIO.closeOut stream
  end

val policy = And (Atom 0, Or (Not (Atom 1), Atom 2))
val livePolicy = mustSome (certifyLiveBytes (3, policy))
val semantic000 = mustSome (certifyWitnessBytes (livePolicy, [0, 0, 0]))
val semantic001 = mustSome (certifyWitnessBytes (livePolicy, [0, 0, 1]))
val semantic010 = mustSome (certifyWitnessBytes (livePolicy, [0, 1, 0]))
val semantic011 = mustSome (certifyWitnessBytes (livePolicy, [0, 1, 1]))
val semantic100 = mustSome (certifyWitnessBytes (livePolicy, [1, 0, 0]))
val semantic101 = mustSome (certifyWitnessBytes (livePolicy, [1, 0, 1]))
val semantic110 = mustSome (certifyWitnessBytes (livePolicy, [1, 1, 0]))
val semantic111 = mustSome (certifyWitnessBytes (livePolicy, [1, 1, 1]))
val nonBoolean = mustSome (packWitnessUnchecked (livePolicy, [1, 2, 0]))
val shortRow = mustSome (packWitnessUnchecked (livePolicy, [1, 0]))
val descriptorTamper = mustSome (packWitnessUnchecked
  (replaceAt (listLength livePolicy - 1, 124, livePolicy), [1, 0, 0]))

val fixtures =
  [("build/fixtures/semantic-000.drew", semantic000),
   ("build/fixtures/semantic-001.drew", semantic001),
   ("build/fixtures/semantic-010.drew", semantic010),
   ("build/fixtures/semantic-011.drew", semantic011),
   ("build/fixtures/semantic-100.drew", semantic100),
   ("build/fixtures/semantic-101.drew", semantic101),
   ("build/fixtures/semantic-110.drew", semantic110),
   ("build/fixtures/semantic-111.drew", semantic111),
   ("build/fixtures/reject-nonboolean.drew", nonBoolean),
   ("build/fixtures/reject-short-row.drew", shortRow),
   ("build/fixtures/reject-descriptor-tamper.drew", descriptorTamper),
   ("build/fixtures/reject-trailing.drew", semantic100 @ [0]),
   ("build/fixtures/reject-truncated.drew",
      List.take (semantic100, listLength semantic100 - 1)),
   ("build/fixtures/reject-version.drew", replaceAt (4, 2, semantic100)),
   ("build/fixtures/reject-live-length.drew", replaceAt (8, 0, semantic100))]

val _ = List.app writeBytes fixtures
val _ = print "wrote 15 native DREW fixtures\n"
