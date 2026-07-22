(* ==========================================================================
   DREG direct-logic certificate checker, wire version 1.

   This theory independently models the byte contract from Lean's
   Dregg2.Logic.CompilationCertificateBundle.  Its headline theorem says that
   accepting untrusted bytes produces a known-version source/target pair with
   equal Boolean semantics in every atom environment.

   It deliberately does not model the live IR-v2 JSON certificate or claim a
   Lean-to-HOL proof transfer.  Cross-system agreement is pinned by the shared
   schema and concrete golden bytes.
   ========================================================================== *)

Theory DirectLogicChecker
Ancestors
  arithmetic list
Libs
  preamble

Datatype:
  dl_source =
      SAtom num
    | STop
    | SBot
    | SNot dl_source
    | SAnd dl_source dl_source
    | SOr dl_source dl_source
End

Datatype:
  dl_target =
      TInput num
    | TTruth
    | TFalsity
    | TInv dl_target
    | TConj dl_target dl_target
    | TDisj dl_target dl_target
End

Datatype:
  dl_bundle = DLBundle num dl_source dl_target
End

Definition source_eval_def:
  source_eval env (SAtom atom) = env atom ∧
  source_eval env STop = T ∧
  source_eval env SBot = F ∧
  source_eval env (SNot p) = ¬source_eval env p ∧
  source_eval env (SAnd p q) = (source_eval env p ∧ source_eval env q) ∧
  source_eval env (SOr p q) = (source_eval env p ∨ source_eval env q)
End

Definition target_eval_def:
  target_eval env (TInput atom) = env atom ∧
  target_eval env TTruth = T ∧
  target_eval env TFalsity = F ∧
  target_eval env (TInv p) = ¬target_eval env p ∧
  target_eval env (TConj p q) = (target_eval env p ∧ target_eval env q) ∧
  target_eval env (TDisj p q) = (target_eval env p ∨ target_eval env q)
End

Definition lower_def:
  lower (SAtom atom) = TInput atom ∧
  lower STop = TTruth ∧
  lower SBot = TFalsity ∧
  lower (SNot p) = TInv (lower p) ∧
  lower (SAnd p q) = TConj (lower p) (lower q) ∧
  lower (SOr p q) = TDisj (lower p) (lower q)
End

Theorem lower_correct:
  ∀env source. target_eval env (lower source) = source_eval env source
Proof
  gen_tac >> Induct >> simp [lower_def, source_eval_def, target_eval_def]
QED

Definition check_bundle_def:
  check_bundle (DLBundle version source target) ⇔
    version = 1 ∧ target = lower source
End

Theorem check_bundle_sound:
  ∀version source target.
    check_bundle (DLBundle version source target) ⇒
    version = 1 ∧ ∀env. target_eval env target = source_eval env source
Proof
  simp [check_bundle_def, lower_correct]
QED

Definition byte_valid_def:
  byte_valid byte ⇔ byte < 256
End

Definition bytes_valid_def:
  bytes_valid [] = T ∧
  bytes_valid (byte::rest) = (byte_valid byte ∧ bytes_valid rest)
End

Definition decode_source_fuel_def:
  decode_source_fuel 0 bytes = NONE ∧
  decode_source_fuel (SUC fuel) [] = NONE ∧
  decode_source_fuel (SUC fuel) (tag::rest) =
    if tag = 0 then
      case rest of
        [] => NONE
      | atom::tail => SOME (SAtom atom,tail)
    else if tag = 1 then SOME (STop,rest)
    else if tag = 2 then SOME (SBot,rest)
    else if tag = 3 then
      case decode_source_fuel fuel rest of
        NONE => NONE
      | SOME (p,tail) => SOME (SNot p,tail)
    else if tag = 4 then
      case decode_source_fuel fuel rest of
        NONE => NONE
      | SOME (p,tail) =>
          (case decode_source_fuel fuel tail of
             NONE => NONE
           | SOME (q,tail') => SOME (SAnd p q,tail'))
    else if tag = 5 then
      case decode_source_fuel fuel rest of
        NONE => NONE
      | SOME (p,tail) =>
          (case decode_source_fuel fuel tail of
             NONE => NONE
           | SOME (q,tail') => SOME (SOr p q,tail'))
    else NONE
End

Definition decode_target_fuel_def:
  decode_target_fuel 0 bytes = NONE ∧
  decode_target_fuel (SUC fuel) [] = NONE ∧
  decode_target_fuel (SUC fuel) (tag::rest) =
    if tag = 16 then
      case rest of
        [] => NONE
      | atom::tail => SOME (TInput atom,tail)
    else if tag = 17 then SOME (TTruth,rest)
    else if tag = 18 then SOME (TFalsity,rest)
    else if tag = 19 then
      case decode_target_fuel fuel rest of
        NONE => NONE
      | SOME (p,tail) => SOME (TInv p,tail)
    else if tag = 20 then
      case decode_target_fuel fuel rest of
        NONE => NONE
      | SOME (p,tail) =>
          (case decode_target_fuel fuel tail of
             NONE => NONE
           | SOME (q,tail') => SOME (TConj p q,tail'))
    else if tag = 21 then
      case decode_target_fuel fuel rest of
        NONE => NONE
      | SOME (p,tail) =>
          (case decode_target_fuel fuel tail of
             NONE => NONE
           | SOME (q,tail') => SOME (TDisj p q,tail'))
    else NONE
End

Definition decode_bundle_def:
  decode_bundle bytes =
    if bytes_valid bytes then
      case bytes of
        a::b::c::d::version::body =>
          if a = 68 ∧ b = 82 ∧ c = 69 ∧ d = 71 ∧ version = 1 then
            case decode_source_fuel (LENGTH bytes) body of
              NONE => NONE
            | SOME (source,rest) =>
                (case decode_target_fuel (LENGTH bytes) rest of
                   SOME (target,[]) => SOME (DLBundle version source target)
                 | _ => NONE)
          else NONE
      | _ => NONE
    else NONE
End

Definition check_bytes_def:
  check_bytes bytes ⇔
    case decode_bundle bytes of
      NONE => F
    | SOME bundle => check_bundle bundle
End

Theorem check_bytes_sound:
  ∀bytes.
    check_bytes bytes ⇒
    ∃version source target.
      decode_bundle bytes = SOME (DLBundle version source target) ∧
      version = 1 ∧
      ∀env. target_eval env target = source_eval env source
Proof
  rw [check_bytes_def] >>
  Cases_on ‘decode_bundle bytes’ >> fs [] >>
  Cases_on ‘x’ >> fs [check_bundle_def] >>
  metis_tac [lower_correct]
QED

(* The first specimen is also pinned by Lean's canonicalTopBytes theorem. *)
Theorem canonical_top_accepts:
  check_bytes [68;82;69;71;1;1;17]
Proof
  EVAL_TAC
QED

(* a0 and (not a1 or a2), followed by its unique target tree. *)
Theorem canonical_policy_accepts:
  check_bytes
    [68;82;69;71;1;
     4;0;0;5;3;0;1;0;2;
     20;16;0;21;19;16;1;16;2]
Proof
  EVAL_TAC
QED

Theorem unknown_version_rejects:
  ¬check_bytes [68;82;69;71;2;1;17]
Proof
  EVAL_TAC
QED

Theorem trailing_byte_rejects:
  ¬check_bytes [68;82;69;71;1;1;17;0]
Proof
  EVAL_TAC
QED

Theorem noncanonical_target_rejects:
  ¬check_bytes [68;82;69;71;1;0;0;17]
Proof
  EVAL_TAC
QED

val _ = export_theory ();

