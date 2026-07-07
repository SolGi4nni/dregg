(* ===========================================================================
   C10 probe — LINK B, instantiated at the emitted boundScan program.

   C1 (C1-REPORT.md) discharged LINK A for the bounds sub-primitive against the
   real panSem source semantics, but left two residuals it "cited but did not
   close":
     (R1) parser faithfulness — C1 hand-transcribed the .pnk into a panLang AST
          (`boundsChk`) rather than deriving it from the verified parser.
     (R2) LINK B — the CakeML pancake backend theorem
          `pan_to_targetProof$pan_to_target_compile_semantics` was CITED as the
          free half, never instantiated at a concrete emitted program (its
          program-level applicability side conditions never checked).

   This file closes (R1) outright and discharges the PROGRAM-LEVEL half of (R2):

   (R1)  `boundScanProg` is DEFINED as `OUTL (parse_topdecs_to_ast <the .pnk>)` —
         the AST is not transcribed, it IS the CakeML-verified Pancake parser's
         output on leanc's emitted text. `boundScanProg_is_parser_output` is the
         kernel-checked equation. leanc's correctness is therefore not trusted
         (Link A proves the AST refines the spec) AND leanc's text->AST step is
         the verified parser, not a hand transcription.

   (R2, program half)  The program-level hypotheses of
         `pan_to_target_compile_semantics` — the ones that are ABOUT THE PROGRAM
         (`pancake_good_code`, `distinct_params (functions .)`,
         `ALL_DISTINCT (MAP FST (functions .))`, `size_of_eids . < dimword(:64)`)
         — are DISCHARGED here by EVAL on the concrete `boundScanProg`. These are
         the applicability conditions C1/C4 never checked; they are checked here,
         by computation, not cited.

   What remains for a full Link B instance (named, not hidden): the runtime
   MACHINE-STATE package (`pan_installed`, `backend_config_ok mc`,
   `mc_conf_ok mc`, `mc_init_ok`, the heap/bitmap/register layout) — the standard
   CakeML "the loader placed the verified binary in a well-formed initial state"
   assumption, discharged elsewhere by the x64 target-config proof against the
   bootstrapped image, never by leanc — and the single FFI-oracle spec. See
   C10-LINKB-REPORT.md.

   The three program predicates good_panops / pancake_good_code / distinct_params
   live in the CakeML *proof* scripts (pan_to_wordProof / pan_to_targetProof).
   They are restated here VERBATIM (definitionally identical) so the discharge
   does not force a multi-hour build of the whole backend proof stack; the
   report records the constant-identity, and the companion
   `boundScanLinkBInstScript.sml` (built once pan_to_targetProofTheory is
   available) performs the MATCH_MP against the real constants.
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib;
open panLangTheory panSemTheory panPropsTheory panPtreeConversionTheory;

val _ = new_theory "boundScanLinkB";

(* ---------------------------------------------------------------------------
   (R1) The emitted program, BY CONSTRUCTION the verified parser's output.
   Read leanc's emitted boundscan.pnk at theory-build time and parse it with the
   CakeML-verified Pancake parser `parse_topdecs_to_ast`.
   --------------------------------------------------------------------------- *)
val src_string =
  let val is = TextIO.openIn "boundscan.pnk"
      val s  = TextIO.inputAll is
      val _  = TextIO.closeIn is
  in s end;

val srcTm = stringSyntax.fromMLstring src_string;

val parse_thm = EVAL “parse_topdecs_to_ast ^srcTm”;

(* strip the INL and name the program list as a definition *)
val prog_tm =
  parse_thm |> concl |> rhs |> sumSyntax.dest_inl |> #1;

val boundScanProg_def =
  new_definition("boundScanProg_def", “boundScanProg = ^prog_tm”);

val _ = save_thm("boundScanProg_parse_raw", parse_thm);

Theorem boundScanProg_is_parser_output:
  parse_topdecs_to_ast ^srcTm = INL boundScanProg
Proof
  REWRITE_TAC[boundScanProg_def] \\ MATCH_ACCEPT_TAC parse_thm
QED

(* ---------------------------------------------------------------------------
   The program-level side conditions of pan_to_target_compile_semantics.
   good_panops / pancake_good_code / distinct_params restated VERBATIM from
   pan_to_wordProof / pan_to_targetProof (constant-identity noted in the report).
   --------------------------------------------------------------------------- *)
Definition good_panops_def:
  good_panops (Function fi) =
    EVERY (every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2))
          (exps_of fi.body) ∧
  good_panops (Decl sh v exp) =
    every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2) exp
End

Definition pancake_good_code_def:
  pancake_good_code pan_code = EVERY good_panops pan_code
End

Definition distinct_params_def:
  distinct_params prog <=>
    EVERY (λ(name,params,body). ALL_DISTINCT params) prog
End

(* ---------------------------------------------------------------------------
   Discharge, by EVAL on the concrete boundScanProg, the program-level
   applicability conditions. Register the panProps recursion equations
   (exps_of / every_exp) and our restated predicates into the EVAL compset.
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

val _ = export_theory ();
