val gtm = “statusRel code r0 s ==> evaluate (statusCore, s) = (NONE, set_var «result» (ValWord (n2w (statusClass code))) s)”;
val _ = proofManagerLib.set_goal ([], gtm);
val _ = proofManagerLib.e (rpt strip_tac);
val _ = proofManagerLib.e (pop_assum (strip_assume_tac o REWRITE_RULE [statusRel_def]));
val (asl,_) = proofManagerLib.top_goal();
val _ = print ("\n@@ASMS@@ " ^ String.concatWith " | " (map term_to_string asl) ^ "\n");
val _ = proofManagerLib.e (Cases_on `code < 200`);
val _ = print ("\n@@NGOALS_AFTER_CASE=" ^ Int.toString (length (proofManagerLib.top_goals())) ^ "@@\n");
val _ = (proofManagerLib.e (asm_simp_tac (srw_ss() ++ numSimps.ARITH_ss) [statusCore_def, evaluate_If_lt, Annot_Seq_eval, evaluate_Assign_const, set_var_def, statusClass_def]);
         print ("\n@@AFTER_SIMP nGoals=" ^ Int.toString (length (proofManagerLib.top_goals())) ^ "@@\n");
         print (term_to_string (#2 (proofManagerLib.top_goal())) handle _ => "NOGOAL"))
        handle e => print ("\n@@SIMP_EXN " ^ General.exnMessage e ^ "@@\n");
val _ = TextIO.flushOut TextIO.stdOut;
