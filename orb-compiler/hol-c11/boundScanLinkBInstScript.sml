(* ===========================================================================
   C11 probe — LINK B, INSTANTIATED at the emitted boundScan program against
   the REAL, built CakeML backend correctness theorem.

   C10 (boundScanLinkBScript.sml) defined `boundScanProg` as the verified
   Pancake parser's output on leanc's emitted `boundscan.pnk`, and discharged
   the four PROGRAM-LEVEL side conditions of `pan_to_target_compile_semantics`
   by EVAL — but against RESTATED (verbatim-copied) predicates, because the
   backend proof stack was not built, so the real theorem was not in scope.

   C11 runs against the FULLY-BUILT backend proof stack (pan_to_targetProof and
   its whole ancestry: backendProof / lab_to_targetProof / word_to_stackProof /
   data_to_wordProof / stack_to_labProof / pan_to_wordProof). It:

     (1) re-derives `boundScanProg` as the parser output (identical program);
     (2) discharges the four program-level side conditions against the REAL
         constants `pancake_good_code` (pan_to_targetProofTheory),
         `distinct_params` / `good_panops` (pan_to_wordProofTheory),
         `functions` / `size_of_eids` (panLangTheory) — by EVAL;
     (3) INSTANTIATES the real `pan_to_target_compile_semantics` at
         `pan_code := boundScanProg`, `start := «main»`, `:'a := :64`, and
         SIMPLIFIES AWAY the four now-proven program-level conjuncts, yielding
         `boundScanProg_linkB`: the backend correctness theorem specialized to
         the concrete emitted program, its remaining antecedent being exactly
         the standard CakeML machine-state install package + the concrete
         compiler run (`compile_prog_max`) + the FFI oracle + non-Fail.

   This is the build-gated MATCH_MP the C10 report named as pending (§4.1/§4.2).
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib;
open panLangTheory panSemTheory panPropsTheory panPtreeConversionTheory;
open pan_to_targetProofTheory pan_to_wordProofTheory;

val _ = new_theory "boundScanLinkBInst";

(* ---------------------------------------------------------------------------
   (1) boundScanProg = OUTL (parse_topdecs_to_ast <the exact boundscan.pnk>).
   --------------------------------------------------------------------------- *)
val src_string =
  let val is = TextIO.openIn "boundscan.pnk"
      val s  = TextIO.inputAll is
      val _  = TextIO.closeIn is
  in s end;

val srcTm = stringSyntax.fromMLstring src_string;

val parse_thm = EVAL “parse_topdecs_to_ast ^srcTm”;

val prog_tm = parse_thm |> concl |> rhs |> sumSyntax.dest_inl |> #1;

val boundScanProg_def =
  new_definition("boundScanProg_def", “boundScanProg = ^prog_tm”);

Theorem boundScanProg_is_parser_output:
  parse_topdecs_to_ast ^srcTm = INL boundScanProg
Proof
  REWRITE_TAC[boundScanProg_def] \\ MATCH_ACCEPT_TAC parse_thm
QED

(* ---------------------------------------------------------------------------
   (2) Discharge the four program-level side conditions against the REAL
   backend constants (not restated copies).
   --------------------------------------------------------------------------- *)
val _ = computeLib.add_funs
          [good_panops_def, pancake_good_code_def, distinct_params_def,
           exps_of_def, every_exp_def];

Theorem boundScanProg_pancake_good_code:
  pancake_good_code boundScanProg
Proof
  REWRITE_TAC[boundScanProg_def] \\ EVAL_TAC \\ rw[]
QED

Theorem boundScanProg_distinct_params:
  distinct_params (functions boundScanProg)
Proof
  REWRITE_TAC[boundScanProg_def] \\ EVAL_TAC
QED

Theorem boundScanProg_distinct_names:
  ALL_DISTINCT (MAP FST (functions boundScanProg))
Proof
  REWRITE_TAC[boundScanProg_def] \\ EVAL_TAC
QED

Theorem boundScanProg_size_of_eids:
  size_of_eids boundScanProg < dimword (:64)
Proof
  REWRITE_TAC[boundScanProg_def] \\ EVAL_TAC
QED

(* ---------------------------------------------------------------------------
   (3) LINK B, instantiated: specialize the REAL backend theorem at
   boundScanProg / «main» / :64 and discharge the four program-level conjuncts.
   --------------------------------------------------------------------------- *)
val linkB_inst =
  pan_to_target_compile_semantics
    |> INST_TYPE [alpha |-> “:64”]
    |> Q.INST [‘pan_code’ |-> ‘boundScanProg’, ‘start’ |-> ‘«main»’];

Theorem boundScanProg_linkB =
  linkB_inst
   |> SIMP_RULE bool_ss
        [boundScanProg_pancake_good_code, boundScanProg_distinct_params,
         boundScanProg_distinct_names, boundScanProg_size_of_eids]

val _ = export_theory ();
