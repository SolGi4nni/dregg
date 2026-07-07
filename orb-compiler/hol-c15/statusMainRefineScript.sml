(* ===========================================================================
   C15 probe, PART C — the whole-`main` FFI-trace refinement for the status
   classifier.  This is the TEMPLATE wrapper (adapted from C14's stepMainRefine)
   parameterized by ⟨control-word layout, the core Link-A theorem, the spec-word
   term⟩.  N=1 read (only `code`), store/report at +8w, spec word
   `n2w (statusClass code)`.  NO clock precondition (branch-only, no While).
   The forward wrap extracts the emitted Dec/Annot/Seq spine in ML by rand-
   walking `statusMainBody` and discharges each node with the uniform
   decw/annotw/seqldw tactics.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory;
open c14GenericTheory;
open statusCoreTheory;      (* statusCore, statusClass, statusRel, evaluate_statusCore_framed, statusCore_noFFI *)
open statusWrapperTheory;   (* statusCtrlStaged, statusFFI, statusMainBody *)
open proofManagerLib;
val _ = new_theory "statusMainRefine";
fun ck s = (print ("\n@@@ "^s^" nGoals="^Int.toString(length(top_goals()))^" @@@\n");
            print (Parse.term_to_string (#2 (top_goal())) handle _ => "NOGOAL"); print "\n");

(* ---- ML peel of the emitted spine (structurally guaranteed correct) ---- *)
val ty64  = fcpSyntax.mk_numeric_type (Arbnum.fromInt 64);
val mbT   = Term.inst [Type.alpha |-> ty64] (rhs (concl statusMainBody_def));
val Dbase = rand mbT;      val body1  = rand Dbase;
val Dbuf  = rand body1;    val SEQld  = rand Dbuf;
val AL    = rand SEQld;    val Dcode  = rand AL;
val Ares  = rand Dcode;    val Dres   = rand Ares;
val RBODY = rand Dres;
val loadSeq = rand (rator SEQld);            (* SEQld = Seq loadSeq AL *)
val CORE  = rand (rator RBODY);  val REST1 = rand RBODY;   (* RBODY = Seq CORE REST1 *)
val STORE = rand (rator REST1);  val REST2 = rand REST1;   (* REST1 = Seq STORE REST2 *)
val REPORT= rand (rator REST2);  val RETURN= rand REST2;   (* REST2 = Seq REPORT RETURN *)

(* NB: NO `len <= s0.clock` precondition — the branch-only core consumes no
   clock (no While).  This is the structural difference from boundScan. *)
g `statusFFI code s0 /\ s0.locals = FEMPTY ==>
   ?sF loadEv rb.
     evaluate (statusMainBody, s0) = (SOME (Return (ValWord 0w)), sF) /\
     sF.ffi.io_events =
       s0.ffi.io_events ++ loadEv ++
       [IO_event (ffi$ExtCall «report_vec»)
          (word_to_bytes (n2w (statusClass code) : word64) F) rb]`;
e (strip_tac);
e (qpat_x_assum `statusFFI _ _` (strip_assume_tac o SIMP_RULE std_ss [statusFFI_def]));
e (qabbrev_tac `ba = s0.base_addr`);
e (`«base»<>«buf» /\ «base»<>«code» /\ «base»<>«result» /\
    «buf»<>«code» /\ «buf»<>«result» /\ «code»<>«result»` by EVAL_TAC);
e (qabbrev_tac `sB = s0 with locals := s0.locals |+ («base», ValWord ba)`);
e (qabbrev_tac `sBU = sB with locals := sB.locals |+ («buf», ValWord (ba + 16w))`);
e (`sBU.base_addr = ba /\ sBU.clock = s0.clock /\ sBU.memory = s0.memory /\
    sBU.memaddrs = s0.memaddrs /\ sBU.be = s0.be /\ sBU.ffi = s0.ffi /\ sBU.structs = s0.structs`
     by simp [Abbr `sBU`, Abbr `sB`, Abbr `ba`]);
e (`FLOOKUP sBU.locals «base» = SOME (ValWord ba) /\
    FLOOKUP sBU.locals «buf» = SOME (ValWord (ba + 16w))`
     by (simp [Abbr `sBU`, Abbr `sB`, FLOOKUP_UPDATE] >> fs []));
e (qpat_x_assum `!s. _ ==> _` (qspec_then `sBU` mp_tac));
e (impl_tac >- fs []);
e (strip_tac);
ck "after L-strip";
(* facts about s1 (post-load) *)
e (`ba IN s1.memaddrs /\ s1.memory ba = Word (n2w code) /\
    (ba+8w) IN s1.memaddrs /\ code < 1000`
     by (fs [statusCtrlStaged_def]));
e (`FLOOKUP s1.locals «base» = SOME (ValWord ba) /\
    FLOOKUP s1.locals «buf» = SOME (ValWord (ba+16w))`
     by (`s1.locals = sBU.locals` by fs [] >> fs []));
ck "after s1-facts";

(* ---- read control block into code, declare result ---- *)
e (`eval s1 (Load One (Var Local «base»)) = SOME (ValWord (n2w code))`
     by (irule eval_load_ctrl >> qexists_tac `ba` >> fs []));
e (qabbrev_tac `sVcode = s1 with locals := s1.locals |+ («code», ValWord (n2w code))`);
e (`sVcode.memory = s1.memory /\ sVcode.memaddrs = s1.memaddrs /\ sVcode.be = s1.be /\
    sVcode.structs = s1.structs /\ sVcode.clock = s1.clock /\ sVcode.ffi = s1.ffi` by simp [Abbr `sVcode`]);
e (`FLOOKUP sVcode.locals «base» = SOME (ValWord ba)`
     by (simp [Abbr `sVcode`, FLOOKUP_UPDATE] >> fs []));
e (qabbrev_tac `sRz = sVcode with locals := sVcode.locals |+ («result», ValWord 0w)`);
ck "states-built";
(* ---- statusRel at sRz ---- *)
e (`sRz.memory = s1.memory /\ sRz.memaddrs = s1.memaddrs /\ sRz.be = s1.be /\
    sRz.structs = s1.structs /\ sRz.clock = s1.clock /\ sRz.ffi = s1.ffi /\
    sRz.base_addr = ba`
     by (simp [Abbr `sRz`, Abbr `sVcode`] >> fs []));
e (`FLOOKUP sRz.locals «code» = SOME (ValWord (n2w code)) /\
    FLOOKUP sRz.locals «result» = SOME (ValWord 0w) /\
    FLOOKUP sRz.locals «base» = SOME (ValWord ba)`
     by (simp [Abbr `sRz`, Abbr `sVcode`, FLOOKUP_UPDATE] >> fs []));
e (`statusRel code 0w sRz` by (simp [statusRel_def] >> fs []));
ck "statusRel-done";
(* ---- statusCore (NO clock precondition) ---- *)
e (drule evaluate_statusCore_framed >> strip_tac);
e (qmatch_asmsub_rename_tac `evaluate (statusCore, sRz) = (NONE, sCore)`);
e (qabbrev_tac `wstar = n2w (statusClass code) : word64`);
e (`FLOOKUP sCore.locals «result» = SOME (ValWord wstar)` by fs [Abbr `wstar`]);
e (`FLOOKUP sCore.locals «base» = FLOOKUP sRz.locals «base»`
     by (first_x_assum (qspec_then `«base»` mp_tac) >> impl_tac >- EVAL_TAC >> simp []));
e (`FLOOKUP sCore.locals «base» = SOME (ValWord ba)` by fs []);
e (`sCore.clock <= sRz.clock` by (imp_res_tac evaluate_clock >> fs []));
e (`sCore.memaddrs = s1.memaddrs /\ sCore.base_addr = ba`
     by (imp_res_tac evaluate_invariants >> gvs []));
e (`sCore.ffi.io_events = s0.ffi.io_events ++ loadEv`
     by (`sCore.ffi.io_events = sRz.ffi.io_events`
            by (`evaluate (statusCore, sRz) = (NONE, sCore)` by fs [] >>
                drule noFFI_io_events >> simp [statusCore_noFFI]) >> fs []));
ck "statusCore-done";

(* ==================== Store / report / Return ==================== *)
e (`(ba + 8w) IN sCore.memaddrs` by gvs []);
e (qabbrev_tac `sS = sCore with memory := ((ba + 8w) =+ Word wstar) sCore.memory`);
e (`evaluate (Store (Op Add [Var Local «base»; Const 8w]) (Var Local «result»), sCore) = (NONE, sS)`
     by (simp [Abbr `sS`] >> irule evaluate_store_result >> fs []));
e (`sS.base_addr = ba /\ sS.memaddrs = sCore.memaddrs /\ sS.locals = sCore.locals /\
    sS.clock = sCore.clock /\ sS.ffi = sCore.ffi` by simp [Abbr `sS`]);
e (`FLOOKUP sS.locals «base» = SOME (ValWord sS.base_addr)` by gvs []);
e (`(sS.base_addr + 8w) IN sS.memaddrs` by gvs []);
e (`sS.memory (sS.base_addr + 8w) = Word wstar`
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

(* ==================== RBODY base case (terms from ML peel) ==================== *)
e (`evaluate (^RETURN, sRep) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Annot_Seq >> fs []));
e (`evaluate (^REPORT, sS) = (NONE, sRep)`
     by (irule Annot_Seq >> fs []));
e (`evaluate (^REST2, sS) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Seq_thread >> qexists_tac `sRep` >> fs []));
e (`evaluate (^STORE, sCore) = (NONE, sS)`
     by (irule Annot_Seq >> fs []));
e (`evaluate (^REST1, sCore) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Seq_thread >> qexists_tac `sS` >> fs []));
e (`evaluate (^CORE, sRz) = (NONE, sCore)`
     by (irule Annot_Seq >> fs []));
e (`evaluate (^RBODY, sRz) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Seq_thread >> qexists_tac `sCore` >> fs []));
e (`?st. evaluate (^RBODY, sRz) = (SOME (Return (ValWord 0w)), st) /\ st.ffi.io_events = tr`
     by (qexists_tac `empty_locals sRep` >> fs []));
ck "RB-done";

(* ==================== wrap Decs/Annots up to statusMainBody ==================== *)
e (`s0 with locals := s0.locals |+ («base», ValWord ba) = sB` by simp [Abbr `sB`]);
e (`sB with locals := sB.locals |+ («buf», ValWord (ba + 16w)) = sBU` by simp [Abbr `sBU`]);
e (`s1 with locals := s1.locals |+ («code», ValWord (n2w code)) = sVcode` by simp [Abbr `sVcode`]);
e (`sVcode with locals := sVcode.locals |+ («result», ValWord 0w) = sRz` by simp [Abbr `sRz`]);
e (`eval s0 BaseAddr = SOME (ValWord ba)` by (simp [eval_def, Abbr `ba`]));
e (`FLOOKUP sB.locals «base» = SOME (ValWord ba)` by (simp [Abbr `sB`, FLOOKUP_UPDATE] >> fs []));
e (`eval sB (Op Add [Var Local «base»; Const 16w]) = SOME (ValWord (ba + 16w))`
     by (irule eval_var_add >> fs []));
e (`evaluate (^loadSeq, sBU) = (NONE, s1)`
     by (irule Annot_Seq >> first_assum ACCEPT_TAC));
ck "prewrap-done";

(* ---- forward wrap: wrap the Dec/Annot spine bottom-up ---- *)
fun decw vq steq =
  irule Dec_trace >> qexists_tac vq >> rpt conj_tac >>
  TRY (qpat_x_assum steq (fn th => REWRITE_TAC [th])) >>
  FIRST [ first_assum ACCEPT_TAC,
          (simp [eval_def, shape_of_def] >> NO_TAC),
          (metis_tac []) ];
val annotw = irule Annot_trace >> (first_assum ACCEPT_TAC ORELSE metis_tac []);
val seqldw = irule Seq_trace >> qexists_tac `s1` >> rpt conj_tac >>
             FIRST [ first_assum ACCEPT_TAC, (fs [] >> NO_TAC), (metis_tac []) ];

e (`?st'. evaluate (^Dres, sVcode) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord 0w` `sVcode with locals := _ = sRz`);
e (`?st'. evaluate (^Ares, sVcode) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by annotw);
e (`?st'. evaluate (^Dcode, s1) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord (n2w code)` `s1 with locals := _ = sVcode`);
e (`?st'. evaluate (^AL, s1) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by annotw);
e (`?st'. evaluate (^SEQld, sBU) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by seqldw);
e (`?st'. evaluate (^Dbuf, sB) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord (ba + 16w)` `sB with locals := _ = sBU`);
e (`?st'. evaluate (^body1, sB) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by annotw);
e (`?st'. evaluate (^Dbase, s0) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord ba` `s0 with locals := _ = sB`);
e (`?sF. evaluate (statusMainBody, s0) = (SOME (Return (ValWord 0w)), sF) /\ sF.ffi.io_events = tr`
     by (simp [Once statusMainBody_def] >> annotw));
val _ = print ("\n@@@ statusMainBody fact built. nGoals=" ^ Int.toString (length (top_goals ()) handle _ => 0) ^ "\n");

e (pop_assum strip_assume_tac);
e (qexists_tac `sF` >> qexists_tac `loadEv` >> qexists_tac `rb`);
e (conj_tac >- first_assum ACCEPT_TAC);
e (fs [Abbr `tr`, Abbr `wstar`]);
val _ = print ("\n@@@ AFTER close nGoals=" ^ Int.toString (length (top_goals ()) handle _ => 0) ^ "\n");

val statusMainBody_refines = top_thm ();
val _ = save_thm ("statusMainBody_refines", statusMainBody_refines);
val _ = print "\n@@@ statusMainBody_refines SAVED\n";
val _ = print (thm_to_string statusMainBody_refines);
val _ = print "\n@@@ TAILDONE\n";
val _ = export_theory ();
