(* ===========================================================================
   C17 probe — LINK B for the REAL deployed serve fragment, instantiated at the
   emitted rateAdmitstatus program against the REAL, built CakeML backend
   correctness theorem.  Byte-for-byte the C11/C14/C15 procedure with the program
   swapped, produced by the GENERATOR `panAutoLib.mk_linkB`.  The ONLY
   per-primitive inputs are the .pnk filename and the program-constant name; the
   four EVAL side conditions and the instantiation of
   `pan_to_target_compile_semantics` are program-agnostic.  leanc stays OUT of the
   TCB: rateAdmitProg is the VERIFIED parser's output.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib;
open panLangTheory panSemTheory panPropsTheory panPtreeConversionTheory;
open pan_to_targetProofTheory pan_to_wordProofTheory;
open panAutoLib;

val _ = new_theory "rateAdmitLinkBInst";

val linkB_result =
  mk_linkB { pnkFile = "rateadmit.pnk", progName = "rateAdmitProg" };

val rateAdmitProg_is_parser_output = #parser_output linkB_result;
val rateAdmitProg_linkB            = #linkB linkB_result;

val _ = save_thm ("rateAdmitProg_is_parser_output", rateAdmitProg_is_parser_output);
val _ = save_thm ("rateAdmitProg_linkB", rateAdmitProg_linkB);

val _ = export_theory ();
