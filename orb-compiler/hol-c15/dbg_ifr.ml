val fact = “eval (s:(64,'ffi)panSem$state) (Cmp Less (Var Local «code») (Const 200w)) = SOME (ValWord (1w:word64))”;
val gl = “evaluate (If (Cmp Less (Var Local «code») (Const 200w)) c1 c2, (s:(64,'ffi)panSem$state)) = (NONE, foo)”;
val _ = proofManagerLib.set_goal ([fact], gl);
val _ = (proofManagerLib.e (asm_simp_tac (srw_ss()) [evaluate_If_reduce]);
   print ("\n@@AFTER nGoals="^Int.toString(length(proofManagerLib.top_goals()))^"@@\n");
   print ("GOAL: "^term_to_string (#2 (proofManagerLib.top_goal()))^"\n"))
  handle e => print ("\n@@EXN "^General.exnMessage e^"@@\n");
(* try explicit MP *)
val _ = proofManagerLib.set_goal ([fact], gl);
val _ = (proofManagerLib.e (imp_res_tac evaluate_If_reduce >> asm_simp_tac (srw_ss()) []);
   print ("\n@@IMPRES nGoals="^Int.toString(length(proofManagerLib.top_goals()))^"@@\n");
   print ("GOAL2: "^term_to_string (#2 (proofManagerLib.top_goal()))^"\n"))
  handle e => print ("\n@@IMPRES_EXN "^General.exnMessage e^"@@\n");
val _ = TextIO.flushOut TextIO.stdOut;
