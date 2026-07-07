val _ = print ("\n@@200w=n2w200: " ^ Bool.toString (aconv “200w:word64” “n2w 200:word64”) ^ "@@\n");
val ifsub = “evaluate (If (Cmp Less (Var Local «code») (Const (200w:word64))) (Seq (Annot «location» «(27:4 27:13)») (Assign Local «result» (Const 1w))) Skip, (s:(64,'ffi) panSem$state))”;
val inst = SPECL [“«code»”, “code:num”, “200:num”, “(Seq (Annot «location» «(27:4 27:13)») (Assign Local «result» (Const 1w)))”, “Skip”, “s:(64,'ffi) panSem$state”]
  (INST_TYPE [] evaluate_If_lt) handle e => (print ("\n@@SPEC_EXN "^General.exnMessage e^"@@\n"); TRUTH);
val _ = print "\n@@INST@@\n"; val _ = print (thm_to_string inst); val _ = print "\n@@END@@\n";
val _ = TextIO.flushOut TextIO.stdOut;
