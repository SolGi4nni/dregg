(* C16 verify — tags + axiom counts for the generator-produced theorems. *)
open HolKernel boolLib bossLib Parse;
open statusGenTheory stepGenTheory;
val _ = new_theory "verifyC16";
val _ = Globals.show_tags := true;

fun report nm th =
  (print ("\n@@@ " ^ nm ^ " (tag shown):\n");
   print (thm_to_string th); print "\n");

val _ = report "status_machine_code" status_machine_code;
val _ = report "step_machine_code"   step_machine_code;
val _ = report "statusMainBody_refines" statusMainBody_refines;
val _ = report "stepMainBody_refines"   stepMainBody_refines;

val _ = print ("\n@@@ axioms statusGen = " ^ Int.toString (length (axioms "statusGen")) ^ "\n");
val _ = print ("@@@ axioms stepGen   = " ^ Int.toString (length (axioms "stepGen")) ^ "\n");
val _ = print ("@@@ axioms verifyC16 = " ^ Int.toString (length (axioms "verifyC16")) ^ "\n");
val _ = export_theory ();
