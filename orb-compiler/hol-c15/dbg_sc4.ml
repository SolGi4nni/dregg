val _ = print ("\n@@THM@@ " ^ thm_to_string eval_lt_pinned ^ "\n");
val g1 = ([“FLOOKUP s.locals «code» = SOME (ValWord (n2w code))”, “code < 1000”, “FLOOKUP s.locals «result» = SOME (ValWord r0)”],
          “eval s (Cmp Less (Var Local «code») (Const (n2w 200))) = SOME (ValWord (if code < 200 then (1w:word64) else 0w))”);
fun tryit name tac = (proofManagerLib.set_goal g1;
   (proofManagerLib.e tac; print ("\n@@"^name^" nGoals="^Int.toString(length(proofManagerLib.top_goals()))^"@@\n")) handle e => print ("\n@@"^name^" EXN "^General.exnMessage e^"@@\n");
   proofManagerLib.dropn 99 handle _ => ());
val _ = tryit "metis" (metis_tac [eval_lt_pinned]);
val _ = tryit "irule_fs" (irule eval_lt_pinned >> fs []);
val _ = tryit "ho_mmt" (ho_match_mp_tac eval_lt_pinned >> asm_simp_tac (srw_ss()++numSimps.ARITH_ss) []);
val _ = tryit "specl" (mp_tac (Q.SPECL [`s`,`«code»`,`code`,`200`] eval_lt_pinned) >> asm_simp_tac (srw_ss()++numSimps.ARITH_ss) []);
val _ = TextIO.flushOut TextIO.stdOut;
