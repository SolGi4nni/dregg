(* Runnable CakeML wrapper for the translated DREW witness checker. *)

Theory DirectLogicWitnessMain
Ancestors
  DirectLogicWitnessCheckerProg basis_ffi
Libs
  preamble basis

val _ = translation_extends "DirectLogicWitnessCheckerProg";

Quote add_cakeml:
  fun witness_chars_to_nums chars =
    case chars of
      [] => []
    | c::cs => Char.ord c :: witness_chars_to_nums cs

  fun direct_logic_witness_main u =
    let
      val bytes = witness_chars_to_nums
        (String.explode (TextIO.inputAll (TextIO.openStdIn ())))
      val answer = if check_witness_bytes bytes then "accept\n" else "reject\n"
    in
      TextIO.print answer
    end
End

val main_call =
  ``Dlet unknown_loc Pany
      (App Opapp [Var (Short «direct_logic_witness_main»); Con NONE []])``;

val prog = get_ml_prog_state () |> get_prog;
val prog_tm = ``SNOC ^main_call ^prog`` |> EVAL |> rconc;

Definition direct_logic_witness_prog_def:
  direct_logic_witness_prog = ^prog_tm
End

val _ = export_theory ();
