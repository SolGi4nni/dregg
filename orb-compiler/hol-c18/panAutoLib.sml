(* ===========================================================================
   C15 probe — the REUSABLE AUTOMATION (ML).  Two program-agnostic tools that
   turn a loop-free primitive's descent from hand-run into mechanical:

     panLinkA_branch : (rel_thm * spec_thm * core_thm) -> term list -> tactic
        Derives the Link-A core refinement `evaluate <body> = spec` for any
        loop-FREE (straight-line/branch) Pancake body, by symbolic execution
        over the Dec/Annot/Seq/If spine + a finite guard case-split.  The ONLY
        per-primitive inputs are the three definitional theorems and the finite
        list of guard predicates (auto-derivable from the spec's guards).

     mk_linkB : {pnkFile, progName} -> { prog_def, parser_output, linkB, ... }
        The whole-program Link-B GENERATOR: parse the .pnk with the VERIFIED
        parser, bind the program constant, discharge the four EVAL side
        conditions, and instantiate `pan_to_target_compile_semantics`.  The only
        per-primitive inputs are the .pnk filename and the program name.
   =========================================================================== *)
structure panAutoLib =
struct

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory panPtreeConversionTheory;
open pan_to_targetProofTheory pan_to_wordProofTheory;
open panAutoTheory;

(* ---------------------------------------------------------------------------
   panLinkA_branch — the loop-free Link-A DECISION TACTIC.
   --------------------------------------------------------------------------- *)
fun panLinkA_branch (relDef, specDef, coreDef) guardPreds =
  let
    (* map each pinned num-var to its local mlstring, read off the relation *)
    val relConjs = boolSyntax.strip_conj (rhs (#2 (strip_forall (concl relDef))))
    val nvmap = List.mapPartial (fn c =>
        (let val (l,r) = dest_eq c            (* FLOOKUP s.locals V = SOME(...) *)
             val v = rand l                   (* -> V (the local mlstring)      *)
             (* the pinned num-var is the sole :num free var of the RHS value *)
             val nv = hd (List.filter
                            (fn t => Type.compare (type_of t, numSyntax.num) = EQUAL)
                            (free_vars r))
         in SOME (nv, v) end) handle _ => NONE) relConjs
    fun vOf x = #2 (valOf (List.find (fn (nv,_) => aconv nv x) nvmap))
    (* each guard predicate `x < y` -> the (local, x, y) triple *)
    val triples = map (fn p => let val (x,y) = numSyntax.dest_less p
                               in (vOf x, x, y) end) guardPreds
  in
    rpt strip_tac >>
    pop_assum (strip_assume_tac o REWRITE_RULE [relDef]) >>
    (* (i) establish every guard's eval via the GENERIC eval_lt_pinned.  NB the
       state `s` is kept inside a QUOTE (not antiquoted) so `subgoal` elaborates
       it against the goal's 64-bit state — a fresh polymorphic `s` would defeat
       the word64 lemma match. *)
    MAP_EVERY (fn (v,x,y) =>
      let val q = [QUOTE "eval s (Cmp Less (Var Local ", ANTIQUOTE v,
                   QUOTE ") (Const (n2w ", ANTIQUOTE y,
                   QUOTE "))) = SOME (ValWord (if ", ANTIQUOTE x,
                   QUOTE " < ", ANTIQUOTE y,
                   QUOTE " then (1w:word64) else 0w))"]
      in subgoal q >-
           (irule eval_lt_pinned >> asm_simp_tac (srw_ss() ++ numSimps.ARITH_ss) [])
      end) triples >>
    (* (ii) expose the emitted cascade + forward-chain each decision node through
       evaluate_If_reduce (a conditional rewrite whose guard-value simp cannot
       solve alone); cond1w_ne0 collapses each guard word back to its source
       predicate so BOTH sides carry the same guard nest *)
    simp [coreDef] >>
    imp_res_tac evaluate_If_reduce >>
    asm_simp_tac (srw_ss() ++ numSimps.ARITH_ss)
      [Annot_Seq_eval, evaluate_Assign_const, set_var_def, cond1w_ne0] >>
    (* (iii) finite guard case-split aligns leaf-by-leaf with the spec *)
    rw [specDef]
  end;

(* ---------------------------------------------------------------------------
   mk_linkB — the whole-program Link-B GENERATOR (C11/C14 procedure, mechanized).
   --------------------------------------------------------------------------- *)
fun mk_linkB {pnkFile : string, progName : string} =
  let
    val src_string =
      let val is = TextIO.openIn pnkFile
          val s  = TextIO.inputAll is
          val _  = TextIO.closeIn is
      in s end
    val srcTm     = stringSyntax.fromMLstring src_string
    (* parse the .pnk with the VERIFIED parser (fragment form — the source is
       antiquoted, never re-parsed) *)
    val parse_thm = EVAL (Term [QUOTE "parse_topdecs_to_ast ", ANTIQUOTE srcTm])
    val prog_tm   = parse_thm |> concl |> rhs |> sumSyntax.dest_inl |> #1
    val progVar   = mk_var (progName, type_of prog_tm)
    (* bind the program CONSTANT: it enters the grammar under `progName`, so we
       refer to it BY NAME below (antiquoting the polymorphic AST term into a
       parse context yields "No consistent parse"). *)
    val prog_def  = new_definition (progName ^ "_def", mk_eq (progVar, prog_tm))
    val progC     = lhs (concl prog_def)   (* the freshly-defined constant *)
    val parser_output =
      prove (Term [QUOTE "parse_topdecs_to_ast ", ANTIQUOTE srcTm,
                   QUOTE (" = INL " ^ progName)],
             REWRITE_TAC [prog_def] THEN MATCH_ACCEPT_TAC parse_thm)
    val _ = computeLib.add_funs
              [good_panops_def, pancake_good_code_def, distinct_params_def,
               exps_of_def, every_exp_def]
    val good_code =
      prove (Term [QUOTE ("pancake_good_code " ^ progName)],
             REWRITE_TAC [prog_def] THEN EVAL_TAC THEN rw [])
    val distinct_p =
      prove (Term [QUOTE ("distinct_params (functions " ^ progName ^ ")")],
             REWRITE_TAC [prog_def] THEN EVAL_TAC)
    val distinct_n =
      prove (Term [QUOTE ("ALL_DISTINCT (MAP FST (functions " ^ progName ^ "))")],
             REWRITE_TAC [prog_def] THEN EVAL_TAC)
    val size_eids =
      prove (Term [QUOTE ("size_of_eids " ^ progName ^ " < dimword (:64)")],
             REWRITE_TAC [prog_def] THEN EVAL_TAC)
    val linkB =
      pan_to_target_compile_semantics
        |> INST_TYPE [alpha |-> “:64”]
        |> Q.INST [‘pan_code’ |-> [QUOTE progName], ‘start’ |-> ‘«main»’]
        |> SIMP_RULE bool_ss [good_code, distinct_p, distinct_n, size_eids]
  in
    { prog_def = prog_def, parser_output = parser_output, linkB = linkB,
      good_code = good_code, distinct_params = distinct_p,
      distinct_names = distinct_n, size_eids = size_eids, progConst = progC }
  end;


(* ---------------------------------------------------------------------------
   panLinkA_branch_eq — the loop-free Link-A DECISION TACTIC for EQUALITY
   dispatch (C17).  Byte-for-byte panLinkA_branch except the guard kind: it
   evaluates every `Cmp Equal` guard via the GENERIC panAuto$eval_eq_pinned and
   splits the finite equality-guard set against the spec.  The ONLY per-primitive
   inputs, as before, are the three definitional theorems and the finite list of
   guard predicates `x = y` (auto-derivable from the `Cmp Equal` nodes of the
   emitted core).  This is the whole delta a real algebraic-type-dispatch serve
   fragment costs on top of C15's ordered-cascade machinery.
   --------------------------------------------------------------------------- *)
fun panLinkA_branch_eq (relDef, specDef, coreDef) guardPreds =
  let
    val relConjs = boolSyntax.strip_conj (rhs (#2 (strip_forall (concl relDef))))
    val nvmap = List.mapPartial (fn c =>
        (let val (l,r) = dest_eq c
             val v = rand l
             val nv = hd (List.filter
                            (fn t => Type.compare (type_of t, numSyntax.num) = EQUAL)
                            (free_vars r))
         in SOME (nv, v) end) handle _ => NONE) relConjs
    fun vOf x = #2 (valOf (List.find (fn (nv,_) => aconv nv x) nvmap))
    (* each guard predicate `x = y` -> the (local, x, y) triple *)
    val triples = map (fn p => let val (x,y) = dest_eq p
                               in (vOf x, x, y) end) guardPreds
  in
    rpt strip_tac >>
    pop_assum (strip_assume_tac o REWRITE_RULE [relDef]) >>
    (* (i) establish every equality guard's eval via the GENERIC eval_eq_pinned *)
    MAP_EVERY (fn (v,x,y) =>
      let val q = [QUOTE "eval s (Cmp Equal (Var Local ", ANTIQUOTE v,
                   QUOTE ") (Const (n2w ", ANTIQUOTE y,
                   QUOTE "))) = SOME (ValWord (if ", ANTIQUOTE x,
                   QUOTE " = ", ANTIQUOTE y,
                   QUOTE " then (1w:word64) else 0w))"]
      in subgoal q >-
           (irule eval_eq_pinned >> asm_simp_tac (srw_ss() ++ numSimps.ARITH_ss) [])
      end) triples >>
    (* (ii) expose the emitted cascade + forward-chain each decision node *)
    simp [coreDef] >>
    imp_res_tac evaluate_If_reduce >>
    asm_simp_tac (srw_ss() ++ numSimps.ARITH_ss)
      [Annot_Seq_eval, evaluate_Assign_const, set_var_def, cond1w_ne0] >>
    (* (iii) finite equality-guard case-split aligns leaf-by-leaf with the spec *)
    rw [specDef]
  end;

(* ---------------------------------------------------------------------------
   panLinkA_branch_le — the loop-free Link-A DECISION TACTIC for `<=`/`>=`
   (NotLess) THRESHOLD guards (C18).  Byte-for-byte panLinkA_branch except the
   guard kind: it evaluates every `Cmp NotLess` guard via the GENERIC
   panAuto$eval_ge_pinned (variable-on-left, from `>=`) or eval_ge_pinned_rhs
   (variable-on-right, from `<=`), detecting the orientation from which operand is
   the pinned local.  The ONLY per-primitive inputs, as before, are the three
   definitional theorems and the finite list of guard predicates `a <= c`
   (auto-derivable from the `Cmp NotLess` nodes of the emitted core).  This is the
   whole delta a numeric-threshold serve fragment (rate-admit, ASCII case-range)
   costs on top of C15's `<`-cascade and C17's `=`-dispatch machinery.
   --------------------------------------------------------------------------- *)
fun panLinkA_branch_le (relDef, specDef, coreDef) guardPreds =
  let
    val relConjs = boolSyntax.strip_conj (rhs (#2 (strip_forall (concl relDef))))
    val nvmap = List.mapPartial (fn c =>
        (let val (l,r) = dest_eq c
             val v = rand l
             val nv = hd (List.filter
                            (fn t => Type.compare (type_of t, numSyntax.num) = EQUAL)
                            (free_vars r))
         in SOME (nv, v) end) handle _ => NONE) relConjs
    fun vOf x = #2 (valOf (List.find (fn (nv,_) => aconv nv x) nvmap))
    fun isVar x = List.exists (fn (nv,_) => aconv nv x) nvmap
  in
    rpt strip_tac >>
    pop_assum (strip_assume_tac o REWRITE_RULE [relDef]) >>
    (* (i) establish every `<=` guard's eval via the GENERIC NotLess companions.
       For `a <= c`: if the pinned var is `c` (RHS) the parser emitted the
       variable-on-LEFT form (Cmp NotLess (Var v) (Const a)) -> eval_ge_pinned;
       if the pinned var is `a` (LHS) it emitted the variable-on-RIGHT form
       (Cmp NotLess (Const c) (Var v)) -> eval_ge_pinned_rhs.  Either way the
       produced boolean is `if a <= c then 1w else 0w`, matching the source. *)
    MAP_EVERY (fn p =>
      let val (a,c) = numSyntax.dest_leq p
      in
        if isVar c then
          let val q = [QUOTE "eval s (Cmp NotLess (Var Local ", ANTIQUOTE (vOf c),
                       QUOTE ") (Const (n2w ", ANTIQUOTE a,
                       QUOTE "))) = SOME (ValWord (if ", ANTIQUOTE a,
                       QUOTE " <= ", ANTIQUOTE c,
                       QUOTE " then (1w:word64) else 0w))"]
          in subgoal q >-
               (irule eval_ge_pinned >> asm_simp_tac (srw_ss() ++ numSimps.ARITH_ss) [])
          end
        else
          let val q = [QUOTE "eval s (Cmp NotLess (Const (n2w ", ANTIQUOTE c,
                       QUOTE ")) (Var Local ", ANTIQUOTE (vOf a),
                       QUOTE ")) = SOME (ValWord (if ", ANTIQUOTE a,
                       QUOTE " <= ", ANTIQUOTE c,
                       QUOTE " then (1w:word64) else 0w))"]
          in subgoal q >-
               (irule eval_ge_pinned_rhs >> asm_simp_tac (srw_ss() ++ numSimps.ARITH_ss) [])
          end
      end) guardPreds >>
    (* (ii) expose the emitted cascade + forward-chain each decision node *)
    simp [coreDef] >>
    imp_res_tac evaluate_If_reduce >>
    asm_simp_tac (srw_ss() ++ numSimps.ARITH_ss)
      [Annot_Seq_eval, evaluate_Assign_const, set_var_def, cond1w_ne0] >>
    (* (iii) finite threshold-guard case-split aligns leaf-by-leaf with the spec *)
    rw [specDef]
  end;

end
