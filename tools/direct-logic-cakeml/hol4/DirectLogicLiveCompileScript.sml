(* Kernel-evaluate CakeML's verified x86-64 compiler on the runnable checker. *)

Theory DirectLogicLiveCompile
Ancestors
  DirectLogicLiveMain
Libs
  preamble eval_cake_compile_x64Lib

Theorem direct_logic_live_compiled =
  eval_cake_compile_x64 "" direct_logic_live_prog_def
    "direct_logic_live_checker.S";

