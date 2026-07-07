fun panLinkA_branch (relDef, specDef, coreDef) guardPreds =
  let
    val relConjs = boolSyntax.strip_conj (rhs (concl (SPEC_ALL relDef)))
    val nvmap = List.mapPartial (fn c =>
        (let val (l,r) = dest_eq c
             val v  = rand l
             val nv = r |> rand |> rand |> rand
         in SOME (nv, v) end) handle _ => NONE) relConjs
    fun vOf x = #2 (valOf (List.find (fn (nv,_) => aconv nv x) nvmap))
    val triples = map (fn p => let val (x,y) = numSyntax.dest_less p in (vOf x, x, y) end) guardPreds
  in
    rpt strip_tac >>
    pop_assum (strip_assume_tac o REWRITE_RULE [relDef]) >>
    MAP_EVERY (fn (v,x,y) =>
      let val q = [QUOTE "eval s (Cmp Less (Var Local ", ANTIQUOTE v,
                   QUOTE ") (Const (n2w ", ANTIQUOTE y,
                   QUOTE "))) = SOME (ValWord (if ", ANTIQUOTE x,
                   QUOTE " < ", ANTIQUOTE y,
                   QUOTE " then (1w:word64) else 0w))"]
      in subgoal q >-
           (irule eval_lt_pinned >> asm_simp_tac (srw_ss() ++ numSimps.ARITH_ss) [])
      end) triples >>
    simp [coreDef] >>
    imp_res_tac evaluate_If_reduce >>
    asm_simp_tac (srw_ss() ++ numSimps.ARITH_ss)
      [Annot_Seq_eval, evaluate_Assign_const, set_var_def, cond1w_ne0] >>
    rw [specDef]
  end;
val gtm = “statusRel code r0 s ==> evaluate (statusCore, s) = (NONE, set_var «result» (ValWord (n2w (statusClass code))) s)”;
val _ = proofManagerLib.set_goal ([], gtm);
val _ = (proofManagerLib.e (panLinkA_branch (statusRel_def, statusClass_def, statusCore_def) [“code < 200”, “code < 300”, “code < 400”, “code < 500”]);
   print ("\n@@FN_DONE nGoals="^Int.toString(length(proofManagerLib.top_goals()))^"@@\n"))
  handle e => print ("\n@@FN_EXN "^General.exnMessage e^"@@\n");
val _ = TextIO.flushOut TextIO.stdOut;
