val gtm = “statusRel code r0 s ==> evaluate (statusCore, s) = (NONE, set_var «result» (ValWord (n2w (statusClass code))) s)”;
fun mkq (v,x,y) = [QUOTE "eval s (Cmp Less (Var Local ", ANTIQUOTE v, QUOTE ") (Const (n2w ", ANTIQUOTE y, QUOTE "))) = SOME (ValWord (if ", ANTIQUOTE x, QUOTE " < ", ANTIQUOTE y, QUOTE " then (1w:word64) else 0w))"];
val triples = [(“«code»”,“code:num”,“200:num”),(“«code»”,“code:num”,“300:num”),(“«code»”,“code:num”,“400:num”),(“«code»”,“code:num”,“500:num”)];
val _ = proofManagerLib.set_goal ([], gtm);
val _ = proofManagerLib.e (rpt strip_tac >>
  pop_assum (strip_assume_tac o REWRITE_RULE [statusRel_def]) >>
  MAP_EVERY (fn tr => subgoal (mkq tr) >- (irule eval_lt_pinned >> asm_simp_tac (srw_ss()++numSimps.ARITH_ss) [])) triples >>
  simp [statusCore_def] >>
  imp_res_tac evaluate_If_reduce >>
  asm_simp_tac (srw_ss()++numSimps.ARITH_ss) [Annot_Seq_eval, evaluate_Assign_const, set_var_def, cond1w_ne0]);
val _ = print ("\n@@AFTER_SIMP nGoals="^Int.toString(length(proofManagerLib.top_goals()))^"@@\n");
val _ = print ("GOAL: " ^ term_to_string (#2 (proofManagerLib.top_goal())) ^ "\n@@AA@@\n");
val _ = (proofManagerLib.e (rw [statusClass_def]); print ("\n@@AFTER_RW nGoals="^Int.toString(length(proofManagerLib.top_goals()))^"@@\n"); (print ("REMAIN: "^term_to_string(#2(proofManagerLib.top_goal()))^"\n") handle _ => print "none\n")) handle e => print ("\n@@RW EXN "^General.exnMessage e^"@@\n");
val _ = TextIO.flushOut TextIO.stdOut;
