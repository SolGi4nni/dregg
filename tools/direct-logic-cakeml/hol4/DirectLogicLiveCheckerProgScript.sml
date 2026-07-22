(* Proof-producing CakeML translation of the live DREG-v2 checker. *)

Theory DirectLogicLiveCheckerProg
Ancestors
  DirectLogicLiveChecker DirectLogicCheckerProg
Libs
  preamble ml_progLib ml_translatorLib

val _ = translation_extends "DirectLogicCheckerProg";

val _ = translate live_version_def;
val _ = translate max_atom_count_def;
val _ = translate max_section_bytes_def;
val _ = translate nat_digits_rev_def;
val _ = translate REVERSE_DEF;
val _ = translate nat_ascii_def;
val _ = translate APPEND;
val _ = translate json_const_def;
val _ = translate json_zero_def;
val _ = translate json_one_def;
val _ = translate json_neg_one_def;
val _ = translate json_loc_def;
val _ = translate json_mul_def;
val _ = translate json_add_def;
val _ = translate json_neg_def;
val _ = translate json_one_minus_def;
val _ = translate source_polynomial_def;
val _ = translate binary_body_def;
val _ = translate window_gate_def;
val _ = translate binary_gates_from_def;
val _ = translate join_comma_def;
val _ = translate descriptor_bytes_def;
val _ = translate atoms_below_def;
val _ = translate encode_source_def;
val _ = translate encode_target_def;
val _ = translate certify_v1_def;
val _ = translate encode_u32_def;
val _ = translate decode_u32_def;
val _ = translate split_exact_def;
val _ = translate decode_live_bundle_def;
val _ = translate check_live_bundle_def;
val _ = translate check_live_bytes_def;
val _ = translate certify_live_bytes_def;

val _ = export_theory ();
