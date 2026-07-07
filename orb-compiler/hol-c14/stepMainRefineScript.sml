open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory;
open c14GenericTheory;
open stepCoreTheory;      (* stepCore, mstep, stepRel, evaluate_stepCore_framed, stepCore_noFFI *)
open stepWrapperTheory;   (* stepCtrlStaged, stepFFI, stepMainBody *)
open proofManagerLib;
val _ = new_theory "stepMainRefine";
fun ck s = (print ("\n@@@ "^s^" nGoals="^Int.toString(length(top_goals()))^" @@@\n");
            print (Parse.term_to_string (#2 (top_goal())) handle _ => "NOGOAL"); print "\n");

(* NB: NO `len <= s0.clock` precondition — the branch-only core consumes no
   clock (no While).  This is the structural difference from boundScan. *)
g `stepFFI c b s0 /\ s0.locals = FEMPTY ==>
   ?sF loadEv rb.
     evaluate (stepMainBody, s0) = (SOME (Return (ValWord 0w)), sF) /\
     sF.ffi.io_events =
       s0.ffi.io_events ++ loadEv ++
       [IO_event (ffi$ExtCall «report_vec»)
          (word_to_bytes (n2w (mstep c b) : word64) F) rb]`;
e (strip_tac);
e (qpat_x_assum `stepFFI _ _ _` (strip_assume_tac o SIMP_RULE std_ss [stepFFI_def]));
e (qabbrev_tac `ba = s0.base_addr`);
e (`«base»<>«buf» /\ «base»<>«c» /\ «base»<>«b» /\ «base»<>«result» /\
    «buf»<>«c» /\ «buf»<>«b» /\ «buf»<>«result» /\ «c»<>«b» /\
    «c»<>«result» /\ «b»<>«result»` by EVAL_TAC);
e (qabbrev_tac `sB = s0 with locals := s0.locals |+ («base», ValWord ba)`);
e (qabbrev_tac `sBU = sB with locals := sB.locals |+ («buf», ValWord (ba + 32w))`);
e (`sBU.base_addr = ba /\ sBU.clock = s0.clock /\ sBU.memory = s0.memory /\
    sBU.memaddrs = s0.memaddrs /\ sBU.be = s0.be /\ sBU.ffi = s0.ffi /\ sBU.structs = s0.structs`
     by simp [Abbr `sBU`, Abbr `sB`, Abbr `ba`]);
e (`FLOOKUP sBU.locals «base» = SOME (ValWord ba) /\
    FLOOKUP sBU.locals «buf» = SOME (ValWord (ba + 32w))`
     by (simp [Abbr `sBU`, Abbr `sB`, FLOOKUP_UPDATE] >> fs []));
e (qpat_x_assum `!s. _ ==> _` (qspec_then `sBU` mp_tac));
e (impl_tac >- fs []);
e (strip_tac);
ck "after L-strip";
(* facts about s1 (post-load) *)
e (`ba IN s1.memaddrs /\ s1.memory ba = Word (n2w c) /\
    (ba+8w) IN s1.memaddrs /\ s1.memory (ba+8w) = Word (n2w b) /\
    (ba+24w) IN s1.memaddrs /\ c <= 255 /\ b < 256`
     by (fs [stepCtrlStaged_def]));
e (`FLOOKUP s1.locals «base» = SOME (ValWord ba) /\
    FLOOKUP s1.locals «buf» = SOME (ValWord (ba+32w))`
     by (`s1.locals = sBU.locals` by fs [] >> fs []));
ck "after s1-facts";

(* ---- read control block into c/b, declare result ---- *)
e (`eval s1 (Load One (Var Local «base»)) = SOME (ValWord (n2w c))`
     by (irule eval_load_ctrl >> qexists_tac `ba` >> fs []));
e (qabbrev_tac `sVc = s1 with locals := s1.locals |+ («c», ValWord (n2w c))`);
e (`sVc.memory = s1.memory /\ sVc.memaddrs = s1.memaddrs /\ sVc.be = s1.be /\
    sVc.structs = s1.structs /\ sVc.clock = s1.clock /\ sVc.ffi = s1.ffi` by simp [Abbr `sVc`]);
e (`FLOOKUP sVc.locals «base» = SOME (ValWord ba)`
     by (simp [Abbr `sVc`, FLOOKUP_UPDATE] >> fs []));
e (`(ba+8w) IN sVc.memaddrs /\ sVc.memory (ba+8w) = Word (n2w b)` by gvs [Abbr `sVc`]);
e (`eval sVc (Load One (Op Add [Var Local «base»; Const 8w])) = SOME (ValWord (n2w b))`
     by (irule eval_load_off >> qexists_tac `ba` >> fs []));
e (qabbrev_tac `sVb = sVc with locals := sVc.locals |+ («b», ValWord (n2w b))`);
e (qabbrev_tac `sRz = sVb with locals := sVb.locals |+ («result», ValWord 0w)`);
ck "states-built";
(* ---- stepRel at sRz ---- *)
e (`sRz.memory = s1.memory /\ sRz.memaddrs = s1.memaddrs /\ sRz.be = s1.be /\
    sRz.structs = s1.structs /\ sRz.clock = s1.clock /\ sRz.ffi = s1.ffi /\
    sRz.base_addr = ba`
     by (simp [Abbr `sRz`, Abbr `sVb`, Abbr `sVc`] >> fs []));
e (`FLOOKUP sRz.locals «c» = SOME (ValWord (n2w c)) /\
    FLOOKUP sRz.locals «b» = SOME (ValWord (n2w b)) /\
    FLOOKUP sRz.locals «result» = SOME (ValWord 0w) /\
    FLOOKUP sRz.locals «base» = SOME (ValWord ba)`
     by (simp [Abbr `sRz`, Abbr `sVb`, Abbr `sVc`, FLOOKUP_UPDATE] >> fs []));
e (`stepRel c b 0w sRz` by (simp [stepRel_def] >> fs []));
ck "stepRel-done";
(* ---- stepCore (NO clock precondition) ---- *)
e (drule evaluate_stepCore_framed >> strip_tac);
e (qmatch_asmsub_rename_tac `evaluate (stepCore, sRz) = (NONE, sCore)`);
e (qabbrev_tac `wstar = n2w (mstep c b) : word64`);
e (`FLOOKUP sCore.locals «result» = SOME (ValWord wstar)` by fs [Abbr `wstar`]);
e (`FLOOKUP sCore.locals «base» = FLOOKUP sRz.locals «base»`
     by (first_x_assum (qspec_then `«base»` mp_tac) >> impl_tac >- EVAL_TAC >> simp []));
e (`FLOOKUP sCore.locals «base» = SOME (ValWord ba)` by fs []);
e (`sCore.clock <= sRz.clock` by (imp_res_tac evaluate_clock >> fs []));
e (`sCore.memaddrs = s1.memaddrs /\ sCore.base_addr = ba`
     by (imp_res_tac evaluate_invariants >> gvs []));
e (`sCore.ffi.io_events = s0.ffi.io_events ++ loadEv`
     by (`sCore.ffi.io_events = sRz.ffi.io_events`
            by (`evaluate (stepCore, sRz) = (NONE, sCore)` by fs [] >>
                drule noFFI_io_events >> simp [stepCore_noFFI]) >> fs []));
ck "stepCore-done";

(* ==================== Store / report / Return ==================== *)
e (`(ba + 24w) IN sCore.memaddrs` by gvs []);
e (qabbrev_tac `sS = sCore with memory := ((ba + 24w) =+ Word wstar) sCore.memory`);
e (`evaluate (Store (Op Add [Var Local «base»; Const 24w]) (Var Local «result»), sCore) = (NONE, sS)`
     by (simp [Abbr `sS`] >> irule evaluate_store_result >> fs []));
e (`sS.base_addr = ba /\ sS.memaddrs = sCore.memaddrs /\ sS.locals = sCore.locals /\
    sS.clock = sCore.clock /\ sS.ffi = sCore.ffi` by simp [Abbr `sS`]);
e (`FLOOKUP sS.locals «base» = SOME (ValWord sS.base_addr)` by gvs []);
e (`(sS.base_addr + 24w) IN sS.memaddrs` by gvs []);
e (`sS.memory (sS.base_addr + 24w) = Word wstar`
     by gvs [Abbr `sS`, combinTheory.APPLY_UPDATE_THM]);
ck "store-done";
e (qpat_x_assum `!s w. _` (qspecl_then [`sS`, `wstar`] mp_tac));
e (impl_tac >- fs []);
e (strip_tac);
e (qmatch_asmsub_rename_tac `evaluate (ExtCall «report_vec» _ _ _ _, sS) = (NONE, sRep)`);
e (`sS.ffi.io_events = s0.ffi.io_events ++ loadEv` by fs []);
e (qabbrev_tac `tr = s0.ffi.io_events ++ loadEv ++
                    [IO_event (ffi$ExtCall «report_vec») (word_to_bytes wstar F) rb]`);
e (`sRep.ffi.io_events = tr` by (simp [Abbr `tr`] >> fs []));
ck "report-done";
e (`evaluate (Return (Const 0w), sRep) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by simp [evaluate_def, eval_def, size_of_sh_with_ctxt_def, shape_of_def]);
e (`(empty_locals sRep).ffi.io_events = tr` by simp [empty_locals_def]);
ck "return-done";

(* ==================== resultBody base case ==================== *)
e (`evaluate (Seq (Annot «location» «(36:9 36:10)») (Return (Const 0w)), sRep) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Annot_Seq >> fs []));
e (`evaluate (Seq (Annot «location» «(35:2 35:30)») (ExtCall «report_vec» (Op Add [Var Local «base»; Const 24w]) (Const 8w) (Var Local «base») (Const 8w)), sS) = (NONE, sRep)`
     by (irule Annot_Seq >> fs []));
e (`evaluate (Seq (Seq (Annot «location» «(35:2 35:30)») (ExtCall «report_vec» (Op Add [Var Local «base»; Const 24w]) (Const 8w) (Var Local «base») (Const 8w))) (Seq (Annot «location» «(36:9 36:10)») (Return (Const 0w))), sS) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Seq_thread >> qexists_tac `sRep` >> fs []));
e (`evaluate (Seq (Annot «location» «(34:5 34:20)») (Store (Op Add [Var Local «base»; Const 24w]) (Var Local «result»)), sCore) = (NONE, sS)`
     by (irule Annot_Seq >> fs []));
e (`evaluate (Seq (Seq (Annot «location» «(34:5 34:20)») (Store (Op Add [Var Local «base»; Const 24w]) (Var Local «result»))) (Seq (Seq (Annot «location» «(35:2 35:30)») (ExtCall «report_vec» (Op Add [Var Local «base»; Const 24w]) (Const 8w) (Var Local «base») (Const 8w))) (Seq (Annot «location» «(36:9 36:10)») (Return (Const 0w)))), sCore) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Seq_thread >> qexists_tac `sS` >> fs []));
e (`evaluate (Seq (Annot «location» «(25:5 31:17)») stepCore, sRz) = (NONE, sCore)`
     by (irule Annot_Seq >> fs []));
e (`evaluate (Seq (Seq (Annot «location» «(25:5 31:17)») stepCore) (Seq (Seq (Annot «location» «(34:5 34:20)») (Store (Op Add [Var Local «base»; Const 24w]) (Var Local «result»))) (Seq (Seq (Annot «location» «(35:2 35:30)») (ExtCall «report_vec» (Op Add [Var Local «base»; Const 24w]) (Const 8w) (Var Local «base») (Const 8w))) (Seq (Annot «location» «(36:9 36:10)») (Return (Const 0w))))), sRz) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Seq_thread >> qexists_tac `sCore` >> fs []));
ck "RB-done";

(* ==================== wrap Decs/Annots up to stepMainBody ==================== *)
e (`s0 with locals := s0.locals |+ («base», ValWord ba) = sB` by simp [Abbr `sB`]);
e (`sB with locals := sB.locals |+ («buf», ValWord (ba + 32w)) = sBU` by simp [Abbr `sBU`]);
e (`s1 with locals := s1.locals |+ («c», ValWord (n2w c)) = sVc` by simp [Abbr `sVc`]);
e (`sVc with locals := sVc.locals |+ («b», ValWord (n2w b)) = sVb` by simp [Abbr `sVb`]);
e (`sVb with locals := sVb.locals |+ («result», ValWord 0w) = sRz` by simp [Abbr `sRz`]);
e (`eval s0 BaseAddr = SOME (ValWord ba)` by (simp [eval_def, Abbr `ba`]));
e (`FLOOKUP sB.locals «base» = SOME (ValWord ba)` by (simp [Abbr `sB`, FLOOKUP_UPDATE] >> fs []));
e (`eval sB (Op Add [Var Local «base»; Const 32w]) = SOME (ValWord (ba + 32w))`
     by (irule eval_var_add >> fs []));
e (`evaluate (Seq (Annot «location» «(21:2 21:27)») (ExtCall «load_vec» (Var Local «base») (Const 24w) (Var Local «buf») (Const 4096w)), sBU) = (NONE, s1)`
     by (irule Annot_Seq >> first_assum ACCEPT_TAC));
e (`?st. evaluate ((Seq (Seq (Annot «location» «(25:5 31:17)») stepCore) (Seq (Seq (Annot «location» «(34:5 34:20)») (Store (Op Add [Var Local «base»; Const 24w]) (Var Local «result»))) (Seq (Seq (Annot «location» «(35:2 35:30)») (ExtCall «report_vec» (Op Add [Var Local «base»; Const 24w]) (Const 8w) (Var Local «base») (Const 8w))) (Seq (Annot «location» «(36:9 36:10)») (Return (Const 0w)))))), sRz) = (SOME (Return (ValWord 0w)), st) /\ st.ffi.io_events = tr`
     by (qexists_tac `empty_locals sRep` >> fs []));
ck "prewrap-done";

(* ---- forward wrap: extract emitted sub-terms in ML, wrap bottom-up ---- *)
val ty64  = fcpSyntax.mk_numeric_type (Arbnum.fromInt 64);
val mbT   = Term.inst [Type.alpha |-> ty64] (rhs (concl stepMainBody_def));
val Dbase = rand mbT;      val body1 = rand Dbase;
val Dbuf  = rand body1;    val SEQld = rand Dbuf;
val AL    = rand SEQld;    val Dc    = rand AL;
val Ab    = rand Dc;       val Db    = rand Ab;
val Ares  = rand Db;       val Dres  = rand Ares;
val RBODY = rand Dres;

fun decw vq steq =
  irule Dec_trace >> qexists_tac vq >> rpt conj_tac >>
  TRY (qpat_x_assum steq (fn th => REWRITE_TAC [th])) >>
  FIRST [ first_assum ACCEPT_TAC,
          (simp [eval_def, shape_of_def] >> NO_TAC),
          (metis_tac []) ];
val annotw = irule Annot_trace >> (first_assum ACCEPT_TAC ORELSE metis_tac []);
val seqldw = irule Seq_trace >> qexists_tac `s1` >> rpt conj_tac >>
             FIRST [ first_assum ACCEPT_TAC, (fs [] >> NO_TAC), (metis_tac []) ];

e (`?st'. evaluate (^Dres, sVb) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord 0w` `sVb with locals := _ = sRz`);
e (`?st'. evaluate (^Ares, sVb) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by annotw);
e (`?st'. evaluate (^Db, sVc) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord (n2w b)` `sVc with locals := _ = sVb`);
e (`?st'. evaluate (^Ab, sVc) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by annotw);
e (`?st'. evaluate (^Dc, s1) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord (n2w c)` `s1 with locals := _ = sVc`);
e (`?st'. evaluate (^AL, s1) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by annotw);
e (`?st'. evaluate (^SEQld, sBU) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by seqldw);
e (`?st'. evaluate (^Dbuf, sB) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord (ba + 32w)` `sB with locals := _ = sBU`);
e (`?st'. evaluate (^body1, sB) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by annotw);
e (`?st'. evaluate (^Dbase, s0) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord ba` `s0 with locals := _ = sB`);
e (`?sF. evaluate (stepMainBody, s0) = (SOME (Return (ValWord 0w)), sF) /\ sF.ffi.io_events = tr`
     by (simp [Once stepMainBody_def] >> annotw));
val _ = print ("\n@@@ stepMainBody fact built. nGoals=" ^ Int.toString (length (top_goals ()) handle _ => 0) ^ "\n");

e (pop_assum strip_assume_tac);
e (qexists_tac `sF` >> qexists_tac `loadEv` >> qexists_tac `rb`);
e (conj_tac >- first_assum ACCEPT_TAC);
e (fs [Abbr `tr`, Abbr `wstar`]);
val _ = print ("\n@@@ AFTER close nGoals=" ^ Int.toString (length (top_goals ()) handle _ => 0) ^ "\n");

val stepMainBody_refines = top_thm ();
val _ = save_thm ("stepMainBody_refines", stepMainBody_refines);
val _ = print "\n@@@ stepMainBody_refines SAVED\n";
val _ = print (thm_to_string stepMainBody_refines);
val _ = print "\n@@@ TAILDONE\n";
val _ = export_theory ();
