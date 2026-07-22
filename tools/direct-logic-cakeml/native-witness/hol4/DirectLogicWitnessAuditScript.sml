(* Fresh-process tag and axiom census for the witness pipeline. *)

Theory DirectLogicWitnessAudit
Ancestors
  DirectLogicWitnessCompileArm8 DirectLogicWitnessCheckerProg
Libs
  preamble

open DirectLogicWitnessCheckerTheory
open DirectLogicWitnessCheckerProgTheory
open DirectLogicWitnessCompileArm8Theory

val _ = set_trace "Unicode" 0;

fun tags name theorem =
  let
    val tag = Thm.tag theorem
    val (oracles,axioms) = Tag.dest_tag tag
  in
    print ("=== " ^ name ^ "\n  oracles = [" ^
      String.concatWith "," oracles ^ "]\n  axiomdeps = [" ^
      String.concatWith "," axioms ^ "]\n")
  end;

val _ = print "@@@ DREG WITNESS CHECKER KERNEL TAGS @@@\n";
val _ = tags "check_witness_bundle_sound" check_witness_bundle_sound;
val _ = tags "check_witness_bytes_sound" check_witness_bytes_sound;
val _ = tags "canonical_witness_policy_accepts"
  canonical_witness_policy_accepts;
val _ = tags "false_witness_policy_rejects"
  false_witness_policy_rejects;
val _ = tags "canonical_witness_policy_tamper_rejects"
  canonical_witness_policy_tamper_rejects;
val _ = tags "check_witness_bytes_v_thm" check_witness_bytes_v_thm;
val _ = tags "direct_logic_witness_compiled_arm8"
  direct_logic_witness_compiled_arm8;

val _ = print ("@@@ THEORY AXIOMS: DirectLogicWitnessChecker = " ^
  Int.toString (length (axioms "DirectLogicWitnessChecker")) ^ "\n");
val _ = print ("@@@ THEORY AXIOMS: DirectLogicWitnessCheckerProg = " ^
  Int.toString (length (axioms "DirectLogicWitnessCheckerProg")) ^ "\n");
val _ = print ("@@@ THEORY AXIOMS: DirectLogicWitnessCompileArm8 = " ^
  Int.toString (length (axioms "DirectLogicWitnessCompileArm8")) ^ "\n");
val _ = print ("@@@ check_witness_bytes_sound STATEMENT @@@\n" ^
  thm_to_string check_witness_bytes_sound ^ "\n");

val _ = export_theory ();
