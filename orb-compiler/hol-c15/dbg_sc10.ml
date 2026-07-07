val gtm = “statusRel code r0 s ==> evaluate (statusCore, s) = (NONE, set_var «result» (ValWord (n2w (statusClass code))) s)”;
fun mkq (v,x,y) = [QUOTE "eval s (Cmp Less (Var Local ", ANTIQUOTE v, QUOTE ") (Const (n2w ", ANTIQUOTE y, QUOTE "))) = SOME (ValWord (if ", ANTIQUOTE x, QUOTE " < ", ANTIQUOTE y, QUOTE " then (1w:word64) else 0w))"];
val triples = [(“«code»”,“code:num”,“200:num”),(“«code»”,“code:num”,“300:num”),(“«code»”,“code:num”,“400:num”),(“«code»”,“code:num”,“500:num”)];
val _ = proofManagerLib.set_goal ([], gtm);
val _ = proofManagerLib.e (rpt strip_tac >>
  pop_assum (strip_assume_tac o REWRITE_RULE [statusRel_def]) >>
  MAP_EVERY (fn tr => subgoal (mkq tr) >- (irule eval_lt_pinned >> asm_simp_tac (srw_ss()++numSimps.ARITH_ss) [])) triples >>
  simp [statusCore_def] >>
  MAP_EVERY (fn p => Cases_on [ANTIQUOTE p]) [“code<200”,“code<300”,“code<400”,“code<500”]);
val (asl,g) = proofManagerLib.top_goal();
val _ = print ("\n@@G1_ASMS@@\n" ^ String.concatWith "\n" (map term_to_string asl) ^ "\n@@G1_GOAL@@\n" ^ term_to_string g ^ "\n@@END@@\n");
val _ = TextIO.flushOut TextIO.stdOut;
