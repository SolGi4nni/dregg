(* Proof-producing CakeML translation of the guarded witness checker. *)

Theory DirectLogicWitnessCheckerProg
Ancestors
  DirectLogicWitnessChecker DirectLogicLiveCheckerProg
Libs
  preamble ml_progLib ml_translatorLib

val _ = translation_extends "DirectLogicLiveCheckerProg";

val _ = translate witness_version_def;
val _ = translate witness_bits_valid_def;
val _ = translate witness_lookup_def;
val _ = translate witness_env_def;
val _ = translate decode_witness_bundle_def;
val _ = translate check_witness_bundle_def;
val _ = translate check_witness_bytes_def;
val _ = translate certify_witness_bytes_def;

val _ = export_theory ();
