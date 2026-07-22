(* ==========================================================================
   Guarded witness execution for the DREG-v2 finite-logic descriptor family.

   A DREW-v1 envelope carries one complete DREG-v2 live certificate and one
   exact Boolean row. Acceptance reuses the live checker (including exact
   descriptor-byte reconstruction), then evaluates the certified source under
   that row. The headline theorem exposes both source and lowered-target truth.
   ========================================================================== *)

Theory DirectLogicWitnessChecker
Ancestors
  DirectLogicLiveChecker
Libs
  preamble

Datatype:
  dl_witness_bundle = DLWitnessBundle (num list) (num list)
End

Definition witness_version_def:
  witness_version = 1
End

Definition witness_bits_valid_def:
  witness_bits_valid [] = T /\
  witness_bits_valid (byte::rest) =
    ((byte = 0 \/ byte = 1) /\ witness_bits_valid rest)
End

Definition witness_lookup_def:
  witness_lookup [] atom = F /\
  witness_lookup (byte::rest) 0 = (byte = 1) /\
  witness_lookup (byte::rest) (SUC atom) = witness_lookup rest atom
End

Definition witness_env_def:
  witness_env row atom = witness_lookup row atom
End

Definition decode_witness_bundle_def:
  decode_witness_bundle bytes =
    if bytes_valid bytes then
      case bytes of
        a::b::c::d::version::body =>
          if a = 68 /\ b = 82 /\ c = 69 /\ d = 87 /\
             version = witness_version then
            case decode_u32 body of
              NONE => NONE
            | SOME (live_length,after_live_length) =>
                (case decode_u32 after_live_length of
                   NONE => NONE
                 | SOME (witness_length,payload) =>
                     if live_length > max_section_bytes \/
                        witness_length > max_section_bytes then NONE
                     else
                       (case split_exact live_length payload of
                          NONE => NONE
                        | SOME (live_bytes,after_live) =>
                            (case split_exact witness_length after_live of
                               SOME (row,[]) =>
                                 SOME (DLWitnessBundle live_bytes row)
                             | _ => NONE)))
          else NONE
      | _ => NONE
    else NONE
End

Definition check_witness_bundle_def:
  check_witness_bundle (DLWitnessBundle live_bytes row) <=>
    check_live_bytes live_bytes /\
    case decode_live_bundle live_bytes of
      SOME (DLLiveBundle atom_count v1_bytes json_bytes) =>
        LENGTH row = atom_count /\
        witness_bits_valid row /\
        (case decode_bundle v1_bytes of
           SOME (DLBundle version source target) =>
             source_eval (witness_env row) source
         | NONE => F)
    | NONE => F
End

Definition check_witness_bytes_def:
  check_witness_bytes bytes <=>
    case decode_witness_bundle bytes of
      NONE => F
    | SOME bundle => check_witness_bundle bundle
End

Definition certify_witness_bytes_def:
  certify_witness_bytes live_bytes row =
    if ~check_live_bytes live_bytes \/ ~witness_bits_valid row then NONE
    else
      case decode_live_bundle live_bytes of
        SOME (DLLiveBundle atom_count v1_bytes json_bytes) =>
          if LENGTH row <> atom_count \/
             LENGTH live_bytes > max_section_bytes \/
             LENGTH row > max_section_bytes then NONE
          else
            (case (encode_u32 (LENGTH live_bytes),encode_u32 (LENGTH row)) of
               (SOME live_length,SOME witness_length) =>
                 SOME ([68;82;69;87;witness_version] ++ live_length ++
                       witness_length ++ live_bytes ++ row)
             | _ => NONE)
      | NONE => NONE
End

Theorem check_witness_bundle_sound:
  !bundle.
    check_witness_bundle bundle ==>
    ?live_bytes row atom_count v1_bytes json_bytes source target.
      bundle = DLWitnessBundle live_bytes row /\
      decode_live_bundle live_bytes =
        SOME (DLLiveBundle atom_count v1_bytes json_bytes) /\
      decode_bundle v1_bytes = SOME (DLBundle 1 source target) /\
      check_live_bytes live_bytes /\
      LENGTH row = atom_count /\
      witness_bits_valid row /\
      atoms_below atom_count source /\
      json_bytes = descriptor_bytes atom_count source /\
      source_eval (witness_env row) source /\
      target_eval (witness_env row) target
Proof
  Cases_on `bundle` >>
  rw [check_witness_bundle_def] >>
  Cases_on `decode_live_bundle l` >> fs [] >>
  Cases_on `x` >> fs [] >>
  Cases_on `decode_bundle l'` >> fs [] >>
  Cases_on `x` >> fs [] >>
  fs [check_live_bytes_def] >>
  drule check_live_bundle_sound >>
  strip_tac >> fs [] >>
  metis_tac []
QED

Theorem check_witness_bytes_sound:
  !bytes.
    check_witness_bytes bytes ==>
    ?live_bytes row atom_count v1_bytes json_bytes source target.
      decode_witness_bundle bytes =
        SOME (DLWitnessBundle live_bytes row) /\
      decode_live_bundle live_bytes =
        SOME (DLLiveBundle atom_count v1_bytes json_bytes) /\
      decode_bundle v1_bytes = SOME (DLBundle 1 source target) /\
      check_live_bytes live_bytes /\
      LENGTH row = atom_count /\
      witness_bits_valid row /\
      atoms_below atom_count source /\
      json_bytes = descriptor_bytes atom_count source /\
      source_eval (witness_env row) source /\
      target_eval (witness_env row) target
Proof
  rw [check_witness_bytes_def] >>
  Cases_on `decode_witness_bundle bytes` >> fs [] >>
  drule check_witness_bundle_sound >>
  metis_tac []
QED

Definition canonical_witness_policy_def:
  canonical_witness_policy =
    THE (certify_witness_bytes canonical_live_policy [1;0;0])
End

Definition false_witness_policy_def:
  false_witness_policy =
    THE (certify_witness_bytes canonical_live_policy [0;0;0])
End

Theorem canonical_witness_policy_accepts:
  check_witness_bytes canonical_witness_policy
Proof
  EVAL_TAC
QED

Theorem false_witness_policy_rejects:
  ~check_witness_bytes false_witness_policy
Proof
  EVAL_TAC
QED

Theorem canonical_witness_policy_tamper_rejects:
  ~check_witness_bytes (SNOC 0 canonical_witness_policy)
Proof
  EVAL_TAC
QED

val _ = export_theory ();
