val gtm = “FLOOKUP s.locals v = SOME (ValWord (n2w (x:num))) /\ x < 9223372036854775808 /\ (y:num) < 9223372036854775808 ==> eval (s:(64,'ffi)panSem$state) (Cmp Less (Var Local v) (Const (n2w y))) = SOME (ValWord (if x < y then 1w:word64 else 0w))”;
val heq = mk_thm([], “((n2w (x:num)):word64 < n2w (y:num)) = (x < y)”);
fun tryit name tac =
  (proofManagerLib.set_goal ([], gtm);
   proofManagerLib.e (strip_tac);
   proofManagerLib.e (simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, asmTheory.word_cmp_def]);
   (proofManagerLib.e tac;
    print ("\n@@"^name^": nGoals="^Int.toString(length(proofManagerLib.top_goals()))^"@@\n"))
   handle e => print ("\n@@"^name^": EXN "^General.exnMessage e^"@@\n"));
val _ = tryit "REWRITE_heq" (REWRITE_TAC [heq]);
val _ = tryit "PURE_heq" (PURE_REWRITE_TAC [heq] >> REFL_TAC handle _ => PURE_REWRITE_TAC[heq]);
val _ = tryit "irule_signed" (assume_tac heq >> fs [heq]);
val _ = TextIO.flushOut TextIO.stdOut;
