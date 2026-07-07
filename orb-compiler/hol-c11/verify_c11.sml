(* Print the C11 results: statements, oracle/axiom tags, axiom count. *)
val _ = Globals.max_print_depth := 100;
val _ = loadPath := "." :: !loadPath;
val _ = load "boundScanLinkBInstTheory";
open boundScanLinkBInstTheory;

fun banner s = (print "\n========== "; print s; print " ==========\n");

val _ = banner "axioms of boundScanLinkBInst";
val _ = print (Int.toString (length (axioms "boundScanLinkBInst")) ^ " axioms\n");

val _ = banner "boundScanProg_is_parser_output";
val _ = print_thm boundScanProg_is_parser_output;

val _ = banner "boundScanProg_pancake_good_code";
val _ = print_thm boundScanProg_pancake_good_code;
val _ = banner "boundScanProg_distinct_params";
val _ = print_thm boundScanProg_distinct_params;
val _ = banner "boundScanProg_distinct_names";
val _ = print_thm boundScanProg_distinct_names;
val _ = banner "boundScanProg_size_of_eids";
val _ = print_thm boundScanProg_size_of_eids;

val _ = banner "boundScanProg_linkB  (the instantiated backend theorem)";
val _ = print_thm boundScanProg_linkB;

val _ = banner "oracle/axiom tags on boundScanProg_linkB";
val _ = print (Hol_pp.thm_to_string boundScanProg_linkB);
val _ = print "\n";
val _ = banner "hypotheses (antecedent conjuncts) of boundScanProg_linkB";
val _ = let val t = concl boundScanProg_linkB
        in print (term_to_string t); print "\n" end;

val _ = banner "DONE";
