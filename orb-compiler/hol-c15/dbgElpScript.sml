open HolKernel boolLib bossLib Parse;
open arithmeticTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
val _ = new_theory "dbgElp";
val _ = Globals.show_types := true;
val red = SIMP_CONV (srw_ss())
  [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, asmTheory.word_cmp_def]
  “eval (s:(64,'ffi)panSem$state) (Cmp Less (Var Local v) (Const (n2w (y:num))))”
  handle e => (print "\n@@SIMP_CONV FAILED@@\n"; REFL “T”);
val _ = print "\n@@REDUCED@@\n";
val _ = print (thm_to_string red);
val _ = print "\n@@END@@\n";
val _ = export_theory ();
