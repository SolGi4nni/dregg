val _ = Globals.show_types := true;
val gtm = “eval (s:(64,'ffi)panSem$state) (Cmp Less (Var Local v) (Const (n2w (y:num))))”;
val red = QCONV (SIMP_CONV (srw_ss()) [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, asmTheory.word_cmp_def]) gtm;
val _ = print "\n@@REDUCED@@\n"; val _ = print (thm_to_string red); val _ = print "\n@@END@@\n";
