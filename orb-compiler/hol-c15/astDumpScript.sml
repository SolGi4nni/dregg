open HolKernel boolLib bossLib Parse;
open panLangTheory panSemTheory panPtreeConversionTheory;
val _ = new_theory "astDump";
val src =
  let val is = TextIO.openIn "statusclass.pnk"
      val s  = TextIO.inputAll is val _ = TextIO.closeIn is in s end;
val srcTm = stringSyntax.fromMLstring src;
val parse_thm = EVAL “parse_topdecs_to_ast ^srcTm”;
val prog_tm = parse_thm |> concl |> rhs |> sumSyntax.dest_inl |> #1;
val _ = print "\n@@@ PROG_TM @@@\n";
val _ = print (Parse.term_to_string prog_tm);
val _ = print "\n@@@ FUNCTIONS @@@\n";
val funcs = (EVAL “functions ^prog_tm”) |> concl |> rhs;
val _ = print (Parse.term_to_string funcs);
val _ = print "\n@@@ ENDDUMP @@@\n";
val _ = export_theory ();
