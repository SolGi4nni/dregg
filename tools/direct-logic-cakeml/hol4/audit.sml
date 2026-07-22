val _ = List.app load ["DirectLogicCheckerTheory", "DirectLogicCheckerProgTheory",
  "DirectLogicLiveCheckerTheory", "DirectLogicLiveCheckerProgTheory"];
open HolKernel boolLib bossLib Parse;
open DirectLogicCheckerTheory;
open DirectLogicCheckerProgTheory;
open DirectLogicLiveCheckerTheory;
open DirectLogicLiveCheckerProgTheory;
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

val _ = print "@@@ DIRECT-LOGIC CHECKER KERNEL TAGS @@@\n";
val _ = tags "lower_correct" lower_correct;
val _ = tags "check_bundle_sound" check_bundle_sound;
val _ = tags "check_bytes_sound" check_bytes_sound;
val _ = tags "canonical_top_accepts" canonical_top_accepts;
val _ = tags "canonical_policy_accepts" canonical_policy_accepts;
val _ = tags "unknown_version_rejects" unknown_version_rejects;
val _ = tags "trailing_byte_rejects" trailing_byte_rejects;
val _ = tags "noncanonical_target_rejects" noncanonical_target_rejects;
val _ = tags "check_bytes_v_thm" check_bytes_v_thm;
val _ = tags "check_live_bundle_sound" check_live_bundle_sound;
val _ = tags "check_live_bytes_sound" check_live_bytes_sound;
val _ = tags "check_live_bytes_v1_compatible" check_live_bytes_v1_compatible;
val _ = tags "canonical_live_top_accepts" canonical_live_top_accepts;
val _ = tags "canonical_live_policy_accepts" canonical_live_policy_accepts;
val _ = tags "canonical_live_policy_tamper_rejects"
  canonical_live_policy_tamper_rejects;
val _ = tags "check_live_bytes_v_thm" check_live_bytes_v_thm;
val _ = tags "certify_live_bytes_v_thm" certify_live_bytes_v_thm;

val _ = print ("@@@ THEORY AXIOMS: DirectLogicChecker = " ^
  Int.toString (length (axioms "DirectLogicChecker")) ^ "\n");
val _ = print ("@@@ THEORY AXIOMS: DirectLogicCheckerProg = " ^
  Int.toString (length (axioms "DirectLogicCheckerProg")) ^ "\n");
val _ = print ("@@@ THEORY AXIOMS: DirectLogicLiveChecker = " ^
  Int.toString (length (axioms "DirectLogicLiveChecker")) ^ "\n");
val _ = print ("@@@ THEORY AXIOMS: DirectLogicLiveCheckerProg = " ^
  Int.toString (length (axioms "DirectLogicLiveCheckerProg")) ^ "\n");
val _ = print ("@@@ check_bytes_sound STATEMENT @@@\n" ^
  thm_to_string check_bytes_sound ^ "\n");
val _ = print ("@@@ check_live_bytes_sound STATEMENT @@@\n" ^
  thm_to_string check_live_bytes_sound ^ "\n");
