(* ==========================================================================
   DREG live certificate checker, wire version 2.

   Version 2 embeds a complete DREG-v1 certificate, an atom bound, and the
   exact canonical JSON bytes of the live IR-v2 Boolean descriptor.  The live
   checker calls the v1 checker, reconstructs every gate/layout byte, and
   compares the supplied descriptor byte-for-byte.  Thus compatibility with
   v1 and source semantics is inherited by theorem, not assumed.
   ========================================================================== *)

Theory DirectLogicLiveChecker
Ancestors
  DirectLogicChecker
Libs
  preamble

Datatype:
  dl_live_bundle = DLLiveBundle num (num list) (num list)
End

Definition live_version_def:
  live_version = 2
End

Definition max_atom_count_def:
  max_atom_count = 256
End

Definition max_section_bytes_def:
  max_section_bytes = 1048576
End

Definition nat_digits_rev_def:
  nat_digits_rev 0 n = [] ∧
  nat_digits_rev (SUC fuel) n =
    (48 + n MOD 10) ::
      if n < 10 then [] else nat_digits_rev fuel (n DIV 10)
End

Definition nat_ascii_def:
  nat_ascii n = REVERSE (nat_digits_rev (SUC n) n)
End

Definition json_const_def:
  json_const value =
    [123;34;116;34;58;34;99;111;110;115;116;34;44;34;118;34;58] ++
      value ++ [125]
End

Definition json_zero_def:
  json_zero = json_const [48]
End

Definition json_one_def:
  json_one = json_const [49]
End

Definition json_neg_one_def:
  json_neg_one = json_const [45;49]
End

Definition json_loc_def:
  json_loc column =
    [123;34;116;34;58;34;108;111;99;34;44;34;99;34;58] ++
      nat_ascii column ++ [125]
End

Definition json_mul_def:
  json_mul left right =
    [123;34;116;34;58;34;109;117;108;34;44;34;108;34;58] ++ left ++
      [44;34;114;34;58] ++ right ++ [125]
End

Definition json_add_def:
  json_add left right =
    [123;34;116;34;58;34;97;100;100;34;44;34;108;34;58] ++ left ++
      [44;34;114;34;58] ++ right ++ [125]
End

Definition json_neg_def:
  json_neg value = json_mul json_neg_one value
End

Definition json_one_minus_def:
  json_one_minus value = json_add json_one (json_neg value)
End

Definition source_polynomial_def:
  source_polynomial (SAtom atom) = json_loc atom ∧
  source_polynomial STop = json_one ∧
  source_polynomial SBot = json_zero ∧
  source_polynomial (SNot p) = json_one_minus (source_polynomial p) ∧
  source_polynomial (SAnd p q) =
    json_mul (source_polynomial p) (source_polynomial q) ∧
  source_polynomial (SOr p q) =
    json_add (json_add (source_polynomial p) (source_polynomial q))
      (json_neg (json_mul (source_polynomial p) (source_polynomial q)))
End

Definition binary_body_def:
  binary_body column =
    json_mul (json_loc column) (json_add (json_loc column) json_neg_one)
End

Definition window_gate_def:
  window_gate body =
    [123;34;116;34;58;34;119;105;110;100;111;119;95;103;97;116;101;34;
     44;34;111;110;95;116;114;97;110;115;105;116;105;111;110;34;58;102;
     97;108;115;101;44;34;98;111;100;121;34;58] ++ body ++ [125]
End

Definition binary_gates_from_def:
  binary_gates_from column 0 = [] ∧
  binary_gates_from column (SUC remaining) =
    window_gate (binary_body column) ::
      binary_gates_from (SUC column) remaining
End

Definition join_comma_def:
  join_comma [] = [] ∧
  join_comma (value::rest) =
    if rest = [] then value else value ++ [44] ++ join_comma rest
End

Definition descriptor_bytes_def:
  descriptor_bytes atom_count source =
    let atom_text = nat_ascii atom_count;
        accept = window_gate (json_add (source_polynomial source) json_neg_one);
        constraints = [91] ++
          join_comma (binary_gates_from 0 atom_count ++ [accept]) ++ [93]
    in
      [123;34;110;97;109;101;34;58;34;100;114;101;103;103;45;102;105;110;
       105;116;101;45;108;111;103;105;99;45;118;50;45] ++ atom_text ++
      [34;44;34;105;114;34;58;50;44;34;116;114;97;99;101;95;119;105;100;
       116;104;34;58] ++ atom_text ++
      [44;34;112;117;98;108;105;99;95;105;110;112;117;116;95;99;111;117;
       110;116;34;58;48;44;34;116;97;98;108;101;115;34;58;91;123;34;105;
       100;34;58;48;44;34;110;97;109;101;34;58;34;109;97;105;110;34;44;
       34;97;114;105;116;121;34;58] ++ atom_text ++
      [44;34;115;101;109;34;58;34;109;97;105;110;34;125;93;44;34;99;111;
       110;115;116;114;97;105;110;116;115;34;58] ++ constraints ++
      [44;34;104;97;115;104;95;115;105;116;101;115;34;58;91;93;44;34;114;
       97;110;103;101;115;34;58;91;93;125]
End

Definition atoms_below_def:
  (atoms_below atom_count (SAtom atom) ⇔ atom < atom_count) ∧
  (atoms_below atom_count STop ⇔ T) ∧
  (atoms_below atom_count SBot ⇔ T) ∧
  (atoms_below atom_count (SNot p) ⇔ atoms_below atom_count p) ∧
  (atoms_below atom_count (SAnd p q) ⇔
    atoms_below atom_count p ∧ atoms_below atom_count q) ∧
  (atoms_below atom_count (SOr p q) ⇔
    atoms_below atom_count p ∧ atoms_below atom_count q)
End

Definition encode_source_def:
  encode_source (SAtom atom) = [0;atom] ∧
  encode_source STop = [1] ∧
  encode_source SBot = [2] ∧
  encode_source (SNot p) = 3 :: encode_source p ∧
  encode_source (SAnd p q) = 4 :: (encode_source p ++ encode_source q) ∧
  encode_source (SOr p q) = 5 :: (encode_source p ++ encode_source q)
End

Definition encode_target_def:
  encode_target (TInput atom) = [16;atom] ∧
  encode_target TTruth = [17] ∧
  encode_target TFalsity = [18] ∧
  encode_target (TInv p) = 19 :: encode_target p ∧
  encode_target (TConj p q) = 20 :: (encode_target p ++ encode_target q) ∧
  encode_target (TDisj p q) = 21 :: (encode_target p ++ encode_target q)
End

Definition certify_v1_def:
  certify_v1 source =
    let bytes = [68;82;69;71;1] ++ encode_source source ++ encode_target (lower source)
    in if bytes_valid bytes then SOME bytes else NONE
End

Definition encode_u32_def:
  encode_u32 n =
    if n < 4294967296 then
      SOME [n DIV 16777216;
            (n DIV 65536) MOD 256;
            (n DIV 256) MOD 256;
            n MOD 256]
    else NONE
End

Definition decode_u32_def:
  decode_u32 bytes =
    case bytes of
      a::b::c::d::rest =>
        SOME (a * 16777216 + b * 65536 + c * 256 + d,rest)
    | _ => NONE
End

Definition split_exact_def:
  split_exact 0 bytes = SOME ([],bytes) ∧
  split_exact (SUC count) [] = NONE ∧
  split_exact (SUC count) (byte::rest) =
    case split_exact count rest of
      NONE => NONE
    | SOME (prefix,trailing) => SOME (byte::prefix,trailing)
End

Definition decode_live_bundle_def:
  decode_live_bundle bytes =
    if bytes_valid bytes then
      case bytes of
        a::b::c::d::version::body =>
          if a = 68 ∧ b = 82 ∧ c = 69 ∧ d = 71 ∧ version = live_version then
            case decode_u32 body of
              NONE => NONE
            | SOME (atom_count,after_atom_count) =>
                (case decode_u32 after_atom_count of
                   NONE => NONE
                 | SOME (v1_length,after_v1_length) =>
                     (case decode_u32 after_v1_length of
                        NONE => NONE
                      | SOME (descriptor_length,payload) =>
                          if atom_count > max_atom_count ∨
                             v1_length > max_section_bytes ∨
                             descriptor_length > max_section_bytes then NONE
                          else
                            (case split_exact v1_length payload of
                               NONE => NONE
                             | SOME (v1_bytes,after_v1) =>
                                 (case split_exact descriptor_length after_v1 of
                                    SOME (json_bytes,[]) =>
                                      SOME (DLLiveBundle atom_count v1_bytes json_bytes)
                                  | _ => NONE))))
          else NONE
      | _ => NONE
    else NONE
End

Definition check_live_bundle_def:
  check_live_bundle (DLLiveBundle atom_count v1_bytes json_bytes) ⇔
    check_bytes v1_bytes ∧
    case decode_bundle v1_bytes of
      SOME (DLBundle version source target) =>
        atoms_below atom_count source ∧
        json_bytes = descriptor_bytes atom_count source
    | NONE => F
End

Definition check_live_bytes_def:
  check_live_bytes bytes ⇔
    case decode_live_bundle bytes of
      NONE => F
    | SOME bundle => check_live_bundle bundle
End

Definition certify_live_bytes_def:
  certify_live_bytes atom_count source =
    if atom_count > max_atom_count ∨ ¬atoms_below atom_count source then NONE
    else
      case certify_v1 source of
        NONE => NONE
      | SOME v1_bytes =>
          let json_bytes = descriptor_bytes atom_count source
          in
            if LENGTH v1_bytes > max_section_bytes ∨
               LENGTH json_bytes > max_section_bytes then NONE
            else
              case (encode_u32 atom_count,
                    encode_u32 (LENGTH v1_bytes),
                    encode_u32 (LENGTH json_bytes)) of
                (SOME atom_bytes,SOME v1_length,SOME json_length) =>
                  SOME ([68;82;69;71;live_version] ++ atom_bytes ++
                        v1_length ++ json_length ++ v1_bytes ++ json_bytes)
              | _ => NONE
End

Theorem check_live_bundle_sound:
  ∀bundle.
    check_live_bundle bundle ⇒
    ∃atom_count v1_bytes json_bytes source target.
      bundle = DLLiveBundle atom_count v1_bytes json_bytes ∧
      decode_bundle v1_bytes = SOME (DLBundle 1 source target) ∧
      check_bytes v1_bytes ∧
      atoms_below atom_count source ∧
      json_bytes = descriptor_bytes atom_count source ∧
      ∀env. target_eval env target = source_eval env source
Proof
  Cases_on ‘bundle’ >> fs [check_live_bundle_def] >>
  strip_tac >>
  Cases_on ‘decode_bundle l’ >> fs [] >>
  Cases_on ‘x’ >> fs [] >>
  drule check_bytes_sound >>
  strip_tac >> fs [] >>
  metis_tac []
QED

Theorem check_live_bytes_sound:
  ∀bytes.
    check_live_bytes bytes ⇒
    ∃atom_count v1_bytes json_bytes source target.
      decode_live_bundle bytes =
        SOME (DLLiveBundle atom_count v1_bytes json_bytes) ∧
      decode_bundle v1_bytes = SOME (DLBundle 1 source target) ∧
      check_bytes v1_bytes ∧
      atoms_below atom_count source ∧
      json_bytes = descriptor_bytes atom_count source ∧
      ∀env. target_eval env target = source_eval env source
Proof
  rw [check_live_bytes_def] >>
  Cases_on ‘decode_live_bundle bytes’ >> fs [] >>
  drule check_live_bundle_sound >>
  metis_tac []
QED

Theorem check_live_bytes_v1_compatible:
  ∀bytes.
    check_live_bytes bytes ⇒
    ∃atom_count v1_bytes json_bytes.
      decode_live_bundle bytes =
        SOME (DLLiveBundle atom_count v1_bytes json_bytes) ∧
      check_bytes v1_bytes
Proof
  metis_tac [check_live_bytes_sound]
QED

Definition canonical_live_top_def:
  canonical_live_top = THE (certify_live_bytes 0 STop)
End

Definition canonical_live_policy_def:
  canonical_live_policy =
    THE (certify_live_bytes 3
      (SAnd (SAtom 0) (SOr (SNot (SAtom 1)) (SAtom 2))))
End

Theorem canonical_live_top_accepts:
  check_live_bytes canonical_live_top
Proof
  EVAL_TAC
QED

Theorem canonical_live_policy_accepts:
  check_live_bytes canonical_live_policy
Proof
  EVAL_TAC
QED

Theorem canonical_live_policy_tamper_rejects:
  ¬check_live_bytes (SNOC 0 canonical_live_policy)
Proof
  EVAL_TAC
QED

val _ = export_theory ();
