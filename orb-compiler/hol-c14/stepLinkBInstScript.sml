(* ===========================================================================
   C14 probe — LINK B for the SECOND primitive, instantiated at the emitted
   machinestep_gate program against the REAL, built CakeML backend correctness
   theorem.  This is the NEAR-AUTOMATIC backend half: byte-for-byte the C11
   boundScan procedure with the program swapped — parse the .pnk with the
   verified parser, discharge the four program-level side conditions by EVAL
   against the REAL backend constants, and specialize
   `pan_to_target_compile_semantics` at the concrete program.  leanc stays OUT
   of the TCB: stepGateProg is the VERIFIED parser's output on the emitted bytes.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib;
open panLangTheory panSemTheory panPropsTheory panPtreeConversionTheory;
open pan_to_targetProofTheory pan_to_wordProofTheory;

val _ = new_theory "stepLinkBInst";

(* (1) stepGateProg = OUTL (parse_topdecs_to_ast <the exact machinestep_gate.pnk>). *)
val src_string =
  let val is = TextIO.openIn "machinestep_gate.pnk"
      val s  = TextIO.inputAll is
      val _  = TextIO.closeIn is
  in s end;
val srcTm = stringSyntax.fromMLstring src_string;
val parse_thm = EVAL “parse_topdecs_to_ast ^srcTm”;
val prog_tm = parse_thm |> concl |> rhs |> sumSyntax.dest_inl |> #1;
val stepGateProg_def =
  new_definition("stepGateProg_def", “stepGateProg = ^prog_tm”);

Theorem stepGateProg_is_parser_output:
  parse_topdecs_to_ast ^srcTm = INL stepGateProg
Proof
  REWRITE_TAC[stepGateProg_def] \\ MATCH_ACCEPT_TAC parse_thm
QED

(* (2) Discharge the four program-level side conditions against the REAL
   backend constants (not restated copies). *)
val _ = computeLib.add_funs
          [good_panops_def, pancake_good_code_def, distinct_params_def,
           exps_of_def, every_exp_def];

Theorem stepGateProg_pancake_good_code:
  pancake_good_code stepGateProg
Proof
  REWRITE_TAC[stepGateProg_def] \\ EVAL_TAC \\ rw[]
QED

Theorem stepGateProg_distinct_params:
  distinct_params (functions stepGateProg)
Proof
  REWRITE_TAC[stepGateProg_def] \\ EVAL_TAC
QED

Theorem stepGateProg_distinct_names:
  ALL_DISTINCT (MAP FST (functions stepGateProg))
Proof
  REWRITE_TAC[stepGateProg_def] \\ EVAL_TAC
QED

Theorem stepGateProg_size_of_eids:
  size_of_eids stepGateProg < dimword (:64)
Proof
  REWRITE_TAC[stepGateProg_def] \\ EVAL_TAC
QED

(* (3) LINK B, instantiated: specialize the REAL backend theorem at
   stepGateProg / «main» / :64 and discharge the four program-level conjuncts. *)
val linkB_inst =
  pan_to_target_compile_semantics
    |> INST_TYPE [alpha |-> “:64”]
    |> Q.INST [‘pan_code’ |-> ‘stepGateProg’, ‘start’ |-> ‘«main»’];

Theorem stepGateProg_linkB =
  linkB_inst
   |> SIMP_RULE bool_ss
        [stepGateProg_pancake_good_code, stepGateProg_distinct_params,
         stepGateProg_distinct_names, stepGateProg_size_of_eids]

val _ = export_theory ();
