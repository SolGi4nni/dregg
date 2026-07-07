val _ = map load ["hashBytesLoopTheory"];
open HolKernel boolLib hashBytesLoopTheory;
val _ = Globals.show_tags := true;
fun show nm th = (print ("\n=== " ^ nm ^ "  (hyps=" ^ Int.toString (length (hyp th)) ^ ") ===\n" ^ thm_to_string th ^ "\n"));
val _ = show "hashLoop_refines" hashLoop_refines;
val _ = show "hashBody_step" hashBody_step;
val _ = show "hashBytes_word" hashBytes_word;
val _ = print "\nDONE\n";
