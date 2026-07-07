(* C18 — parser-output DUMP utility.  Parses each .pnk with the VERIFIED parser
   and prints `functions <prog>` so the emitted If-cascade (Annot location strings
   included) can be transcribed EXACTLY into each fragment's Core_def.  Not part of
   the trust chain — a scaffolding theory. *)
open HolKernel boolLib bossLib Parse;
open panLangTheory panPtreeConversionTheory;
val _ = new_theory "dump";

val os = TextIO.openOut "dump_out.txt";
fun dump pnk =
  let val is = TextIO.openIn pnk
      val s  = TextIO.inputAll is
      val _  = TextIO.closeIn is
      val srcTm = stringSyntax.fromMLstring s
      val parse_thm = EVAL (Term [QUOTE "parse_topdecs_to_ast ", ANTIQUOTE srcTm])
      val prog_tm = parse_thm |> concl |> rhs |> sumSyntax.dest_inl |> #1
      val funcs = EVAL (Term [QUOTE "functions ", ANTIQUOTE prog_tm]) |> concl |> rhs
  in
      TextIO.output (os, "\n@@@@@ FUNCTIONS " ^ pnk ^ " @@@@@\n");
      TextIO.output (os, term_to_string funcs);
      TextIO.output (os, "\n@@@@@ END @@@@@\n")
  end;

val _ = dump "cachefresh.pnk";
val _ = dump "rateadmit.pnk";
val _ = dump "gzipupper.pnk";
val _ = TextIO.closeOut os;

val _ = export_theory ();
