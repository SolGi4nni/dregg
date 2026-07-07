open HolKernel boolLib bossLib Parse;
open boundScanEndToEndTheory boundScanInstallTheory;
val _ = new_theory "verify";

fun banner s = print ("\n========== " ^ s ^ " ==========\n");

banner "axioms of boundScanEndToEnd";
val _ = print (Int.toString (length (axioms "boundScanEndToEnd")) ^ " axioms\n");
banner "axioms of boundScanInstall";
val _ = print (Int.toString (length (axioms "boundScanInstall")) ^ " axioms\n");

banner "boundScanProg_semantics_decls  (Link A, decls level)";
val _ = print (thm_to_string boundScanProg_semantics_decls ^ "\n");

banner "boundScan_machine_code  (THE END-TO-END spec -> machine code)";
val _ = print (thm_to_string boundScan_machine_code ^ "\n");

banner "oracle / axiom tag on boundScan_machine_code";
val _ = let val (ors, axs) = Tag.dest_tag (Thm.tag boundScan_machine_code)
        in print ("oracles = [" ^ String.concatWith ", " ors ^ "]\n");
           print ("axioms  = [" ^ String.concatWith ", " axs ^ "]\n")
        end;
banner "oracle / axiom tag on boundScanProg_semantics_decls";
val _ = let val (ors, axs) = Tag.dest_tag (Thm.tag boundScanProg_semantics_decls)
        in print ("oracles = [" ^ String.concatWith ", " ors ^ "]\n");
           print ("axioms  = [" ^ String.concatWith ", " axs ^ "]\n")
        end;

val _ = print "\n@@@ VERIFY DONE @@@\n";
val _ = export_theory ();
