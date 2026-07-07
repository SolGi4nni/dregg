val gtm = “statusRel code r0 s ==> evaluate (statusCore, s) = (NONE, set_var «result» (ValWord (n2w (statusClass code))) s)”;
val _ = proofManagerLib.set_goal ([], gtm);
val _ = proofManagerLib.e (rpt strip_tac);
val _ = proofManagerLib.e (pop_assum (strip_assume_tac o REWRITE_RULE [statusRel_def]));
fun mkq (v,x,y) = [QUOTE "eval s (Cmp Less (Var Local ", ANTIQUOTE v, QUOTE ") (Const (n2w ", ANTIQUOTE y, QUOTE "))) = SOME (ValWord (if ", ANTIQUOTE x, QUOTE " < ", ANTIQUOTE y, QUOTE " then (1w:word64) else 0w))"];
val triples = [(“«code»”,“code:num”,“200:num”),(“«code»”,“code:num”,“300:num”),(“«code»”,“code:num”,“400:num”),(“«code»”,“code:num”,“500:num”)];
val _ = app (fn tr => (proofManagerLib.e (subgoal (mkq tr) >- (irule eval_lt_pinned >> asm_simp_tac (srw_ss()++numSimps.ARITH_ss) []));
   print ("\n@@FACT ok nGoals="^Int.toString(length(proofManagerLib.top_goals()))^"@@\n"))
   handle e => print ("\n@@FACT EXN "^General.exnMessage e^"@@\n")) triples;
val _ = app (fn p => (proofManagerLib.e (Cases_on [ANTIQUOTE p]); ()) handle e => print ("\n@@CASE EXN "^General.exnMessage e^"@@\n")) [“code<200”,“code<300”,“code<400”,“code<500”];
val _ = print ("\n@@AFTER_CASES nGoals="^Int.toString(length(proofManagerLib.top_goals()))^"@@\n");
val _ = (proofManagerLib.e (asm_simp_tac (srw_ss()++numSimps.ARITH_ss) [statusCore_def, evaluate_If_reduce, Annot_Seq_eval, evaluate_Assign_const, set_var_def, statusClass_def]);
   print ("\n@@FINAL nGoals="^Int.toString(length(proofManagerLib.top_goals()))^"@@\n");
   (print ("REMAIN: " ^ term_to_string (#2 (proofManagerLib.top_goal())) ^ "\n") handle _ => print "no goal\n"))
   handle e => print ("\n@@FINAL EXN "^General.exnMessage e^"@@\n");
val _ = TextIO.flushOut TextIO.stdOut;
