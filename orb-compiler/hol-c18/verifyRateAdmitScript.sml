open HolKernel boolLib bossLib Parse;
open rateAdmitEndToEndTheory rateAdmitCoreTheory rateAdmitLinkBInstTheory;
val _ = new_theory "verifyRateAdmit";

val os = TextIO.openOut "verify_out.txt";
fun w s = TextIO.output(os, s);

val th = rateAdmit_machine_code;
val (ors, axs) = Tag.dest_tag (Thm.tag th);
val _ = w "=== rateAdmit_machine_code : oracles/axioms ===\n";
val _ = w ("oracles = [" ^ String.concatWith ", " ors ^ "]\n");
val _ = w ("axioms  = [" ^ String.concatWith ", " axs ^ "]\n");
val _ = w ("hyps    = " ^ Int.toString (length (Thm.hyp th)) ^ "\n\n");

val _ = w "=== rateAdmit_machine_code THEOREM ===\n";
val _ = w (thm_to_string th);
val _ = w "\n\n=== rateAdmit_def (Lean-parity spec) ===\n";
val _ = w (thm_to_string rateAdmit_def);
val _ = w "\n=== evaluate_rateAdmitCore (automated core) ===\n";
val _ = w (thm_to_string evaluate_rateAdmitCore);
val _ = w "\n=== parser output (leanc OUT of TCB) tag ===\n";
val po = rateAdmitProg_is_parser_output;
val (por,poa) = Tag.dest_tag (Thm.tag po);
val _ = w ("parser_output oracles=[" ^ String.concatWith ", " por ^ "] axioms=[" ^ String.concatWith ", " poa ^ "]\n");
val _ = TextIO.closeOut os;
val _ = export_theory ();
