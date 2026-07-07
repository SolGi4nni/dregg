val gtm = “statusRel code r0 s ==> evaluate (statusCore, s) = (NONE, set_var «result» (ValWord (n2w (statusClass code))) s)”;
fun mkq (v,x,y) = [QUOTE "eval s (Cmp Less (Var Local ", ANTIQUOTE v, QUOTE ") (Const (n2w ", ANTIQUOTE y, QUOTE "))) = SOME (ValWord (if ", ANTIQUOTE x, QUOTE " < ", ANTIQUOTE y, QUOTE " then (1w:word64) else 0w))"];
val triples = [(“«code»”,“code:num”,“200:num”),(“«code»”,“code:num”,“300:num”),(“«code»”,“code:num”,“400:num”),(“«code»”,“code:num”,“500:num”)];
val tac =
  rpt strip_tac >>
  pop_assum (strip_assume_tac o REWRITE_RULE [statusRel_def]) >>
  MAP_EVERY (fn tr => subgoal (mkq tr) >- (irule eval_lt_pinned >> asm_simp_tac (srw_ss()++numSimps.ARITH_ss) [])) triples >>
  MAP_EVERY (fn p => Cases_on [ANTIQUOTE p]) [“code<200”,“code<300”,“code<400”,“code<500”] >>
  asm_simp_tac (srw_ss()++numSimps.ARITH_ss) [statusCore_def, evaluate_If_reduce, Annot_Seq_eval, evaluate_Assign_const, set_var_def, statusClass_def];
val _ = proofManagerLib.set_goal ([], gtm);
val _ = (proofManagerLib.e tac;
   print ("\n@@DONE nGoals="^Int.toString(length(proofManagerLib.top_goals()))^"@@\n");
   (print ("REMAIN: " ^ term_to_string (#2 (proofManagerLib.top_goal())) ^ "\n") handle _ => print "no goals\n"))
  handle e => print ("\n@@TAC EXN "^General.exnMessage e^"@@\n");
val _ = TextIO.flushOut TextIO.stdOut;
