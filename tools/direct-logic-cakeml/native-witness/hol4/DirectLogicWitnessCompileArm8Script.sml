(* Kernel-evaluate CakeML's verified arm8 compiler on the witness checker. *)

Theory DirectLogicWitnessCompileArm8
Ancestors
  DirectLogicWitnessMain
Libs
  preamble eval_cake_compile_arm8Lib

(* The compiled-code theorem is enormous. HOL4's optional source/theory HTML
   mirror would expand it to tens of GiB without adding assurance. *)
val _ = set_trace "TheoryPP.include_html_docs" 0;

Theorem direct_logic_witness_compiled_arm8 =
  eval_cake_compile_arm8 "" direct_logic_witness_prog_def
    "direct_logic_witness_checker_arm8.S";
