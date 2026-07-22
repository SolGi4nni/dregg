(* Runnable CakeML wrapper for the translated live checker.

   The program reads the raw DREG-v2 certificate bytes from standard input and
   prints exactly "accept\n" or "reject\n".  `check_live_bytes` itself is the
   proof-producing translation from DirectLogicLiveCheckerProg; this small I/O
   wrapper is CakeML syntax added on top of the basis program. *)

Theory DirectLogicLiveMain
Ancestors
  DirectLogicLiveCheckerProg basis_ffi
Libs
  preamble basis

val _ = translation_extends "DirectLogicLiveCheckerProg";

Quote add_cakeml:
  fun chars_to_nums chars =
    case chars of
      [] => []
    | c::cs => Char.ord c :: chars_to_nums cs

  fun direct_logic_live_main u =
    let
      val bytes = chars_to_nums
        (String.explode (TextIO.inputAll (TextIO.openStdIn ())))
      val answer = if check_live_bytes bytes then "accept\n" else "reject\n"
    in
      TextIO.print answer
    end
End

val main_call =
  ``Dlet unknown_loc Pany
      (App Opapp [Var (Short «direct_logic_live_main»); Con NONE []])``;

val prog = get_ml_prog_state () |> get_prog;
val prog_tm = ``SNOC ^main_call ^prog`` |> EVAL |> rconc;

Definition direct_logic_live_prog_def:
  direct_logic_live_prog = ^prog_tm
End

val _ = export_theory ();

