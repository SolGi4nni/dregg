use "checker.sml";
use "live_checker.sml";

fun fail message = (TextIO.output (TextIO.stdErr, "FAIL: " ^ message ^ "\n");
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
val liveTop = mustSome (certifyLiveBytes (0, Top))

val _ = expectTrue ("canonical live policy rejected", checkLiveBytes livePolicy)
val _ = expectTrue ("canonical live top rejected", checkLiveBytes liveTop)

(* Independently pinned exact Lean demoDescriptorJson literal. *)
val leanDemoDescriptorJson =
  "{\"name\":\"dregg-finite-logic-v2-3\",\"ir\":2,\"trace_width\":3,\"public_input_count\":0,\"tables\":[{\"id\":0,\"name\":\"main\",\"arity\":3,\"sem\":\"main\"}],\"constraints\":[{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":0},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":0},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":1},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":2},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":2},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":0},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}}},\"r\":{\"t\":\"loc\",\"c\":2}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}}},\"r\":{\"t\":\"loc\",\"c\":2}}}}},\"r\":{\"t\":\"const\",\"v\":-1}}}],\"hash_sites\":[],\"ranges\":[]}"

val _ = expectTrue ("descriptor bytes drifted from Lean pin",
  descriptorBytes (3, policy) = ascii leanDemoDescriptorJson)

(* Header ends at byte 16: magic/version + three u32 fields. *)
val _ = expectFalse ("unknown live version accepted",
  checkLiveBytes (replaceAt (4, 3, livePolicy)))
val _ = expectFalse ("atom bound tamper accepted",
  checkLiveBytes (replaceAt (8, 2, livePolicy)))
val _ = expectFalse ("v1 target tamper accepted",
  checkLiveBytes (replaceAt (31, 17, livePolicy)))
val _ = expectFalse ("descriptor byte tamper accepted",
  checkLiveBytes (replaceAt (listLength livePolicy - 1, 124, livePolicy)))
val _ = expectFalse ("trailing byte accepted", checkLiveBytes (livePolicy @ [0]))
val _ = expectFalse ("truncated live certificate accepted",
  checkLiveBytes (List.take (livePolicy, listLength livePolicy - 1)))

val _ = expectFalse ("out-of-bound source certified",
  Option.isSome (certifyLiveBytes (2, policy)))
val _ = expectFalse ("oversized atom count certified",
  Option.isSome (certifyLiveBytes (257, Top)))

val _ = print "direct-logic live SML checker: 11/11 checks passed\n"

