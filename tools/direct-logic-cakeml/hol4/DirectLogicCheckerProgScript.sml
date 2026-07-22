(* Proof-producing translation of the HOL checker functions to CakeML's deep
   embedding.  The generated *_v refinements are certificates about the HOL
   functions above; this file does not compile a native executable. *)

Theory DirectLogicCheckerProg
Ancestors
  DirectLogicChecker basisProg
Libs
  preamble ml_progLib ml_translatorLib

val _ = translation_extends "basisProg";

val _ = translate source_eval_def;
val _ = translate target_eval_def;
val _ = translate lower_def;
val _ = translate check_bundle_def;
val _ = translate byte_valid_def;
val _ = translate bytes_valid_def;
val _ = translate decode_source_fuel_def;
val _ = translate decode_target_fuel_def;
val _ = translate LENGTH;
val _ = translate decode_bundle_def;
val _ = translate check_bytes_def;

val _ = export_theory ();
