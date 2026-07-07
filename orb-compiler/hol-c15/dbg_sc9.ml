val gtm = “statusRel code r0 s ==> evaluate (statusCore, s) = (NONE, set_var «result» (ValWord (n2w (statusClass code))) s)”;
fun mkq (v,x,y) = [QUOTE "eval s (Cmp Less (Var Local ", ANTIQUOTE v, QUOTE ") (Const (n2w ", ANTIQUOTE y, QUOTE "))) = SOME (ValWord (if ", ANTIQUOTE x, QUOTE " < ", ANTIQUOTE y, QUOTE " then (1w:word64) else 0w))"];
val triples = [(“«code»”,“code:num”,“200:num”),(“«code»”,“code:num”,“300:num”),(“«code»”,“code:num”,“400:num”),(“«code»”,“code:num”,“500:num”)];
fun base () = (rpt strip_tac >>
  pop_assum (strip_assume_tac o REWRITE_RULE [statusRel_def]) >>
  MAP_EVERY (fn tr => subgoal (mkq tr) >- (irule eval_lt_pinned >> asm_simp_tac (srw_ss()++numSimps.ARITH_ss) [])) triples >>
  simp [statusCore_def] >>
  MAP_EVERY (fn p => Cases_on [ANTIQUOTE p]) [“code<200”,“code<300”,“code<400”,“code<500”] >>
  imp_res_tac evaluate_If_reduce);
fun tryit name fin = (proofManagerLib.set_goal ([], gtm);
   (proofManagerLib.e (base () >> fin); print ("\n@@"^name^" nGoals="^Int.toString(length(proofManagerLib.top_goals()))^"@@\n")) handle e => print ("\n@@"^name^" EXN "^General.exnMessage e^"@@\n"));
val _ = tryit "gvs" (gvs [Annot_Seq_eval, evaluate_Assign_const, set_var_def, statusClass_def]);
val _ = tryit "asm+rw" (asm_simp_tac (srw_ss()++numSimps.ARITH_ss) [Annot_Seq_eval, evaluate_Assign_const, set_var_def, statusClass_def] >> rw [] >> fs [statusClass_def]);
val _ = tryit "fullsimp" (full_simp_tac (srw_ss()++numSimps.ARITH_ss) [Annot_Seq_eval, evaluate_Assign_const, set_var_def, statusClass_def]);
val _ = TextIO.flushOut TextIO.stdOut;
