use "checker.sml";
use "fixtures.sml";

fun fail message = (TextIO.output (TextIO.stdErr, "FAIL: " ^ message ^ "\n");
                    OS.Process.exit OS.Process.failure)

fun expectAccept (name, bytes) =
  if checkBytes bytes then () else fail (name ^ " was rejected")

fun expectReject (name, bytes) =
  if checkBytes bytes then fail (name ^ " was accepted") else ()

fun testAdversarial fixtures =
  case fixtures of
      [] => ()
    | fixture :: rest => (expectReject fixture; testAdversarial rest)

val _ = expectAccept ("canonical top", canonicalTop)
val _ = expectAccept ("canonical policy", canonicalPolicy)
val _ = testAdversarial adversarialFixtures

(* Parser and checker are separately exercised: this is a decoded but
 * semantically false formula whose canonical compilation must still check. *)
val canonicalBottom = [68, 82, 69, 71, 1, 2, 18]
val _ = expectAccept ("canonical bottom", canonicalBottom)

val _ = print "direct-logic SML checker: 15/15 fixtures passed\n"

