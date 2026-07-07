val gtm = “statusRel code r0 s ==> evaluate (statusCore, s) = (NONE, set_var «result» (ValWord (n2w (statusClass code))) s)”;
val _ = proofManagerLib.set_goal ([], gtm);
val _ = proofManagerLib.e (rpt strip_tac);
val _ = proofManagerLib.e (pop_assum (strip_assume_tac o REWRITE_RULE [statusRel_def]));
val t = “eval s (Cmp Less (Var Local «code») (Const (n2w 200))) = SOME (ValWord (if code < 200 then (1w:word64) else 0w))”;
val _ = (proofManagerLib.e (subgoal [ANTIQUOTE t]);
         print ("\n@@AFTER_SUBGOAL nGoals=" ^ Int.toString (length (proofManagerLib.top_goals())) ^ "@@\n");
         print ("GOAL1: " ^ term_to_string (#2 (proofManagerLib.top_goal())) ^ "\n"))
        handle e => print ("\n@@SUBGOAL_EXN " ^ General.exnMessage e ^ "@@\n");
val _ = (proofManagerLib.e (irule eval_lt_pinned >> asm_simp_tac (srw_ss() ++ numSimps.ARITH_ss) []);
         print ("\n@@AFTER_PROVE nGoals=" ^ Int.toString (length (proofManagerLib.top_goals())) ^ "@@\n");
         print ("NEXTGOAL: " ^ term_to_string (#2 (proofManagerLib.top_goal())) ^ "\n"))
        handle e => print ("\n@@PROVE_EXN " ^ General.exnMessage e ^ "@@\n");
val _ = TextIO.flushOut TextIO.stdOut;
