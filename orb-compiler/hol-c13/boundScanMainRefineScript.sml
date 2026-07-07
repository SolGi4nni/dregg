open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory;
open machineLoopLinkATheory boundScanCoreLinkATheory boundScanDigestLinkATheory semLiftTheory;
open boundScanWrapperLinkATheory;
open proofManagerLib;
val _ = new_theory "boundScanMainRefine";
fun ck s = (print ("\n@@@ "^s^" nGoals="^Int.toString(length(top_goals()))^" @@@\n");
            print (Parse.term_to_string (#2 (top_goal())) handle _ => "NOGOAL"); print "\n");
g `boundScanFFI a off len s0 /\ s0.locals = FEMPTY /\ len <= s0.clock ==>
   ?sF loadEv rb.
     evaluate (mainBody, s0) = (SOME (Return (ValWord 0w)), sF) /\
     sF.ffi.io_events =
       s0.ffi.io_events ++ loadEv ++
       [IO_event (ffi$ExtCall «report_vec»)
          (word_to_bytes (n2w (c0_encode (boundScan a off len)) : word64) F) rb]`;
e (strip_tac);
e (qpat_x_assum `boundScanFFI _ _ _ _` (strip_assume_tac o SIMP_RULE std_ss [boundScanFFI_def]));
e (qabbrev_tac `ba = s0.base_addr`);
e (`«base»<>«buf» /\ «base»<>«alen» /\ «base»<>«off» /\ «base»<>«len» /\ «base»<>«result» /\
    «base»<>«acc» /\ «base»<>«i» /\ «buf»<>«alen» /\ «buf»<>«off» /\ «buf»<>«len» /\
    «buf»<>«result» /\ «alen»<>«off» /\ «alen»<>«len» /\ «alen»<>«result» /\
    «off»<>«len» /\ «off»<>«result» /\ «len»<>«result»` by EVAL_TAC);
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
(* facts about s1 *)
e (`ba IN s1.memaddrs /\ s1.memory ba = Word (n2w (LENGTH a)) /\
    (ba+8w) IN s1.memaddrs /\ s1.memory (ba+8w) = Word (n2w off) /\
    (ba+16w) IN s1.memaddrs /\ s1.memory (ba+16w) = Word (n2w len) /\
    (ba+24w) IN s1.memaddrs /\ memRel a (ba+32w) s1 /\
    LENGTH a < 2n**63 /\ off+len < 2n**63 /\ EVERY (\x. x<256) a`
     by (fs [ctrlStaged_def]));
e (`FLOOKUP s1.locals «base» = SOME (ValWord ba) /\
    FLOOKUP s1.locals «buf» = SOME (ValWord (ba+32w))`
     by (`s1.locals = sBU.locals` by fs [] >> fs []));
ck "after s1-facts";

(* ---- read control block into alen/off/len, declare result ---- *)
e (`eval s1 (Load One (Var Local «base»)) = SOME (ValWord (n2w (LENGTH a)))`
     by (irule eval_load_ctrl >> qexists_tac `ba` >> fs []));
e (qabbrev_tac `sA = s1 with locals := s1.locals |+ («alen», ValWord (n2w (LENGTH a)))`);
e (`sA.memory = s1.memory /\ sA.memaddrs = s1.memaddrs /\ sA.be = s1.be /\
    sA.structs = s1.structs /\ sA.clock = s1.clock /\ sA.ffi = s1.ffi` by simp [Abbr `sA`]);
e (`FLOOKUP sA.locals «base» = SOME (ValWord ba)`
     by (simp [Abbr `sA`, FLOOKUP_UPDATE] >> fs []));
e (`(ba+8w) IN sA.memaddrs /\ sA.memory (ba+8w) = Word (n2w off)` by gvs [Abbr `sA`]);
e (`eval sA (Load One (Op Add [Var Local «base»; Const 8w])) = SOME (ValWord (n2w off))`
     by (irule eval_load_off >> qexists_tac `ba` >> fs []));
e (qabbrev_tac `sO = sA with locals := sA.locals |+ («off», ValWord (n2w off))`);
e (`sO.memory = s1.memory /\ sO.memaddrs = s1.memaddrs /\ sO.be = s1.be /\
    sO.structs = s1.structs /\ sO.clock = s1.clock /\ sO.ffi = s1.ffi` by simp [Abbr `sO`]);
e (`FLOOKUP sO.locals «base» = SOME (ValWord ba)`
     by (simp [Abbr `sO`, FLOOKUP_UPDATE] >> fs []));
e (`(ba+16w) IN sO.memaddrs /\ sO.memory (ba+16w) = Word (n2w len)` by gvs [Abbr `sO`, Abbr `sA`]);
e (`eval sO (Load One (Op Add [Var Local «base»; Const 16w])) = SOME (ValWord (n2w len))`
     by (irule eval_load_off >> qexists_tac `ba` >> fs []));
e (qabbrev_tac `sLn = sO with locals := sO.locals |+ («len», ValWord (n2w len))`);
e (qabbrev_tac `sRz = sLn with locals := sLn.locals |+ («result», ValWord 0w)`);
ck "states-built";
(* ---- coreRel at sRz ---- *)
e (`sRz.memory = s1.memory /\ sRz.memaddrs = s1.memaddrs /\ sRz.be = s1.be /\
    sRz.structs = s1.structs /\ sRz.clock = s1.clock /\ sRz.ffi = s1.ffi /\
    sRz.base_addr = ba`
     by (simp [Abbr `sRz`, Abbr `sLn`, Abbr `sO`, Abbr `sA`] >> fs []));
e (`FLOOKUP sRz.locals «alen» = SOME (ValWord (n2w (LENGTH a))) /\
    FLOOKUP sRz.locals «off» = SOME (ValWord (n2w off)) /\
    FLOOKUP sRz.locals «len» = SOME (ValWord (n2w len)) /\
    FLOOKUP sRz.locals «buf» = SOME (ValWord (ba + 32w)) /\
    FLOOKUP sRz.locals «result» = SOME (ValWord 0w) /\
    FLOOKUP sRz.locals «base» = SOME (ValWord ba)`
     by (simp [Abbr `sRz`, Abbr `sLn`, Abbr `sO`, Abbr `sA`, FLOOKUP_UPDATE] >> fs []));
e (`memRel a (ba + 32w) sRz` by gvs [memRel_def, Abbr `sRz`, Abbr `sLn`, Abbr `sO`, Abbr `sA`]);
e (`coreRel a off len (ba + 32w) 0w sRz` by (simp [coreRel_def] >> fs []));
e (`len <= sRz.clock` by fs []);
ck "coreRel-done";
(* ---- innerCore ---- *)
e (drule_all evaluate_innerCore_framed >> strip_tac);
e (qmatch_asmsub_rename_tac `evaluate (innerCore, sRz) = (NONE, sC)`);
e (qabbrev_tac `wstar = n2w (c0_encode (boundScan a off len)) : word64`);
e (`FLOOKUP sC.locals «result» = SOME (ValWord wstar)` by fs [Abbr `wstar`]);
e (`FLOOKUP sC.locals «base» = FLOOKUP sRz.locals «base»`
     by (first_x_assum (qspec_then `«base»` mp_tac) >> impl_tac >- EVAL_TAC >> simp []));
e (`FLOOKUP sC.locals «base» = SOME (ValWord ba)` by fs []);
e (`sC.clock <= sRz.clock` by (imp_res_tac evaluate_clock >> fs []));
e (`sC.memaddrs = s1.memaddrs /\ sC.base_addr = ba`
     by (imp_res_tac evaluate_invariants >> gvs []));
e (`sC.ffi.io_events = s0.ffi.io_events ++ loadEv`
     by (`sC.ffi.io_events = sRz.ffi.io_events`
            by (`evaluate (innerCore, sRz) = (NONE, sC)` by fs [] >>
                drule noFFI_io_events >> simp [innerCore_noFFI]) >> fs []));
ck "innerCore-done";

(* ==================== SEGMENT 4A: Store / report / Return ==================== *)
e (`(ba + 24w) IN sC.memaddrs` by gvs []);
e (qabbrev_tac `sS = sC with memory := ((ba + 24w) =+ Word wstar) sC.memory`);
e (`evaluate (Store (Op Add [Var Local «base»; Const 24w]) (Var Local «result»), sC) = (NONE, sS)`
     by (simp [Abbr `sS`] >> irule evaluate_store_result >> fs []));
e (`sS.base_addr = ba /\ sS.memaddrs = sC.memaddrs /\ sS.locals = sC.locals /\
    sS.clock = sC.clock /\ sS.ffi = sC.ffi` by simp [Abbr `sS`]);
e (`FLOOKUP sS.locals «base» = SOME (ValWord sS.base_addr)` by gvs []);
e (`(sS.base_addr + 24w) IN sS.memaddrs` by gvs []);
e (`sS.memory (sS.base_addr + 24w) = Word wstar`
     by gvs [Abbr `sS`, combinTheory.APPLY_UPDATE_THM]);
ck "store-done";
(* report via the R contract clause (the two-binder assumption) *)
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

(* ==================== SEGMENT 4B: resultBody base case ==================== *)
val REP = `ExtCall «report_vec» (Op Add [Var Local «base»; Const 24w]) (Const 8w) (Var Local «base») (Const 8w)`;
e (`evaluate (Seq (Annot «location» «(44:9 44:10)») (Return (Const 0w)), sRep) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Annot_Seq >> fs []));
e (`evaluate (Seq (Annot «location» «(43:2 43:30)») (ExtCall «report_vec» (Op Add [Var Local «base»; Const 24w]) (Const 8w) (Var Local «base») (Const 8w)), sS) = (NONE, sRep)`
     by (irule Annot_Seq >> fs []));
e (`evaluate (Seq (Seq (Annot «location» «(43:2 43:30)») (ExtCall «report_vec» (Op Add [Var Local «base»; Const 24w]) (Const 8w) (Var Local «base») (Const 8w))) (Seq (Annot «location» «(44:9 44:10)») (Return (Const 0w))), sS) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Seq_thread >> qexists_tac `sRep` >> fs []));
e (`evaluate (Seq (Annot «location» «(42:5 42:20)») (Store (Op Add [Var Local «base»; Const 24w]) (Var Local «result»)), sC) = (NONE, sS)`
     by (irule Annot_Seq >> fs []));
e (`evaluate (Seq (Seq (Annot «location» «(42:5 42:20)») (Store (Op Add [Var Local «base»; Const 24w]) (Var Local «result»))) (Seq (Seq (Annot «location» «(43:2 43:30)») (ExtCall «report_vec» (Op Add [Var Local «base»; Const 24w]) (Const 8w) (Var Local «base») (Const 8w))) (Seq (Annot «location» «(44:9 44:10)») (Return (Const 0w)))), sC) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Seq_thread >> qexists_tac `sS` >> fs []));
e (`evaluate (Seq (Annot «location» «(31:5 40:15)») innerCore, sRz) = (NONE, sC)`
     by (irule Annot_Seq >> fs []));
e (`evaluate (Seq (Seq (Annot «location» «(31:5 40:15)») innerCore) (Seq (Seq (Annot «location» «(42:5 42:20)») (Store (Op Add [Var Local «base»; Const 24w]) (Var Local «result»))) (Seq (Seq (Annot «location» «(43:2 43:30)») (ExtCall «report_vec» (Op Add [Var Local «base»; Const 24w]) (Const 8w) (Var Local «base») (Const 8w))) (Seq (Annot «location» «(44:9 44:10)») (Return (Const 0w))))), sRz) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Seq_thread >> qexists_tac `sC` >> fs []));
ck "RB-done";
val RBODY_q = `(Seq (Seq (Annot «location» «(31:5 40:15)») innerCore) (Seq (Seq (Annot «location» «(42:5 42:20)») (Store (Op Add [Var Local «base»; Const 24w]) (Var Local «result»))) (Seq (Seq (Annot «location» «(43:2 43:30)») (ExtCall «report_vec» (Op Add [Var Local «base»; Const 24w]) (Const 8w) (Var Local «base») (Const 8w))) (Seq (Annot «location» «(44:9 44:10)») (Return (Const 0w))))))`;

(* ==================== SEGMENT 4C: wrap Decs/Annots up to mainBody ==================== *)
e (`s0 with locals := s0.locals |+ («base», ValWord ba) = sB` by simp [Abbr `sB`]);
e (`sB with locals := sB.locals |+ («buf», ValWord (ba + 32w)) = sBU` by simp [Abbr `sBU`]);
e (`s1 with locals := s1.locals |+ («alen», ValWord (n2w (LENGTH a))) = sA` by simp [Abbr `sA`]);
e (`sA with locals := sA.locals |+ («off», ValWord (n2w off)) = sO` by simp [Abbr `sO`]);
e (`sO with locals := sO.locals |+ («len», ValWord (n2w len)) = sLn` by simp [Abbr `sLn`]);
e (`sLn with locals := sLn.locals |+ («result», ValWord 0w) = sRz` by simp [Abbr `sRz`]);
e (`eval s0 BaseAddr = SOME (ValWord ba)` by (simp [eval_def, Abbr `ba`]));
e (`FLOOKUP sB.locals «base» = SOME (ValWord ba)` by (simp [Abbr `sB`, FLOOKUP_UPDATE] >> fs []));
e (`eval sB (Op Add [Var Local «base»; Const 32w]) = SOME (ValWord (ba + 32w))`
     by (irule eval_var_add >> fs []));
e (`evaluate (Seq (Annot «location» «(23:2 23:27)») (ExtCall «load_vec» (Var Local «base») (Const 24w) (Var Local «buf») (Const 4096w)), sBU) = (NONE, s1)`
     by (irule Annot_Seq >> first_assum ACCEPT_TAC));
e (`?st. evaluate ((Seq (Seq (Annot «location» «(31:5 40:15)») innerCore) (Seq (Seq (Annot «location» «(42:5 42:20)») (Store (Op Add [Var Local «base»; Const 24w]) (Var Local «result»))) (Seq (Seq (Annot «location» «(43:2 43:30)») (ExtCall «report_vec» (Op Add [Var Local «base»; Const 24w]) (Const 8w) (Var Local «base») (Const 8w))) (Seq (Annot «location» «(44:9 44:10)») (Return (Const 0w)))))), sRz) = (SOME (Return (ValWord 0w)), st) /\ st.ffi.io_events = tr`
     by (qexists_tac `empty_locals sRep` >> fs []));
ck "prewrap-done";


(* ============================================================================
   C13 FORWARD WRAP — build the whole-`main` mainBody refinement bottom-up.
   At this point (prewrap-done) the goal stack still holds the ORIGINAL main
   goal; all segment-4A/4B/4C facts are assumptions: the state-eqs, the eval
   facts, the load Seq eq, and the RBODY fact (`?st. evaluate(RBODY,sRz)=... /\
   st.ffi.io_events = tr`).  We extract the exact emitted sub-terms of mainBody
   in ML (no transcription) and wrap Dec/Annot/Seq nodes with the metavar-safe
   `irule _trace >> qexists_tac <val>` idiom.
   ============================================================================ *)
val ty64  = fcpSyntax.mk_numeric_type (Arbnum.fromInt 64);
val mbT   = Term.inst [Type.alpha |-> ty64] (rhs (concl mainBody_def));
val Dbase = rand mbT;      val body1 = rand Dbase;
val Dbuf  = rand body1;    val SEQld = rand Dbuf;
val AL    = rand SEQld;    val Dalen = rand AL;
val A3s   = rand Dalen;    val Doff  = rand A3s;
val A4s   = rand Doff;     val Dlen  = rand A4s;
val A5s   = rand Dlen;     val Dres  = rand A5s;
val RBODY = rand Dres;

(* per-node discharge tactics (validated in isolation on hbox) *)
fun decw vq steq =
  irule Dec_trace >> qexists_tac vq >> rpt conj_tac >>
  TRY (qpat_x_assum steq (fn th => REWRITE_TAC [th])) >>
  FIRST [ first_assum ACCEPT_TAC,
          (simp [eval_def, shape_of_def] >> NO_TAC),
          (metis_tac []) ];
val annotw = irule Annot_trace >> (first_assum ACCEPT_TAC ORELSE metis_tac []);
val seqldw = irule Seq_trace >> qexists_tac `s1` >> rpt conj_tac >>
             FIRST [ first_assum ACCEPT_TAC, (fs [] >> NO_TAC), (metis_tac []) ];

(* --- forward, bottom-up --- *)
e (`?st'. evaluate (^Dres, sLn) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord 0w` `sLn with locals := _ = sRz`);
e (`?st'. evaluate (^A5s, sLn) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by annotw);
e (`?st'. evaluate (^Dlen, sO) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord (n2w len)` `sO with locals := _ = sLn`);
e (`?st'. evaluate (^A4s, sO) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by annotw);
e (`?st'. evaluate (^Doff, sA) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord (n2w off)` `sA with locals := _ = sO`);
e (`?st'. evaluate (^A3s, sA) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by annotw);
e (`?st'. evaluate (^Dalen, s1) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord (n2w (LENGTH a))` `s1 with locals := _ = sA`);
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
e (`?sF. evaluate (mainBody, s0) = (SOME (Return (ValWord 0w)), sF) /\ sF.ffi.io_events = tr`
     by (simp [Once mainBody_def] >> annotw));
val _ = print ("\n@@@ mainBody fact built. nGoals=" ^ Int.toString (length (top_goals ()) handle _ => 0) ^ "\n");

(* --- close the main goal: provide sF, loadEv, rb --- *)
e (pop_assum strip_assume_tac);
e (qexists_tac `sF` >> qexists_tac `loadEv` >> qexists_tac `rb`);
e (conj_tac >- first_assum ACCEPT_TAC);
e (fs [Abbr `tr`, Abbr `wstar`]);
val _ = print ("\n@@@ AFTER close nGoals=" ^ Int.toString (length (top_goals ()) handle _ => 0) ^ "\n");

val mainBody_refines = top_thm ();
val _ = save_thm ("mainBody_refines", mainBody_refines);
val _ = print "\n@@@ mainBody_refines SAVED\n";
val _ = print (thm_to_string mainBody_refines);
val _ = print "\n@@@ TAILDONE\n";
val _ = export_theory ();
