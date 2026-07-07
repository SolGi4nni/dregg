(* ===========================================================================
   C15 probe, PART D — the semantics CLOCK-LIFT for the status «main».
   Bridges `evaluate (cacheFreshMainBody,...)` through the whole-program
   `Call NONE «main» []` and the all-clocks `panSem$semantics` lift.
   Because the branch-only core consumes NO clock, ANY nonzero clock (K=1)
   suffices — no loop-budget hypothesis.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory;
open c14GenericTheory;             (* semantics_Return_lift *)
open cacheFreshCoreTheory;             (* cacheFresh *)
open cacheFreshWrapperTheory;          (* cacheFreshFFI, cacheFreshMainBody *)
open cacheFreshMainRefineTheory;       (* cacheFreshMainBody_refines *)

val _ = new_theory "cacheFreshSem";

Theorem call_main_run:
  FLOOKUP (s'':(64,'ffi)panSem$state).code «main» = SOME ([], cacheFreshMainBody) /\
  s''.clock <> 0 /\
  cacheFreshFFI code ((dec_clock s'') with locals := FEMPTY) ==>
  ?t loadEv rb.
    evaluate (Call NONE «main» [], s'') = (SOME (Return (ValWord 0w)), t) /\
    t.ffi.io_events = s''.ffi.io_events ++ loadEv ++
      [IO_event (ExtCall «report_vec»)
         (word_to_bytes (n2w (cacheFresh code) : word64) F) rb]
Proof
  strip_tac >>
  qabbrev_tac `s0 = (dec_clock s'') with locals := FEMPTY` >>
  `s0.locals = FEMPTY /\ cacheFreshFFI code s0 /\ s0.ffi = s''.ffi`
     by (fs [Abbr `s0`, dec_clock_def]) >>
  drule_all cacheFreshMainBody_refines >> strip_tac >>
  qmatch_asmsub_rename_tac
     `evaluate (cacheFreshMainBody, s0) = (SOME (Return (ValWord 0w)), sF)` >>
  `sF.clock <= s0.clock` by (imp_res_tac evaluate_clock >> fs []) >>
  `evaluate (cacheFreshMainBody, dec_clock s'' with locals := FEMPTY)
     = (SOME (Return (ValWord 0w)), sF)` by fs [Abbr `s0`] >>
  map_every qexists_tac [`empty_locals sF`, `loadEv`, `rb`] >>
  conj_tac
  >- (simp [Once evaluate_def, OPT_MMAP_def] >>
      gvs [lookup_code_def, FUPDATE_LIST_THM]) >>
  fs [empty_locals_def]
QED

Theorem main_semantics:
  FLOOKUP (s':(64,'ffi)panSem$state).code «main» = SOME ([], cacheFreshMainBody) /\
  (!K. cacheFreshFFI code
         ((dec_clock (s' with clock := K)) with locals := FEMPTY)) ==>
  ?loadEv rb.
    semantics s' «main» = Terminate Success
      (s'.ffi.io_events ++ loadEv ++
       [IO_event (ExtCall «report_vec»)
          (word_to_bytes (n2w (cacheFresh code) : word64) F) rb])
Proof
  strip_tac >>
  qabbrev_tac `sc = s' with clock := 1` >>
  `sc.code = s'.code /\ sc.ffi = s'.ffi /\ sc.clock = 1`
     by simp [Abbr `sc`] >>
  `FLOOKUP sc.code «main» = SOME ([], cacheFreshMainBody)` by fs [] >>
  `sc.clock <> 0` by fs [] >>
  `cacheFreshFFI code ((dec_clock sc) with locals := FEMPTY)`
     by (first_x_assum (qspec_then `1` mp_tac) >> simp [Abbr `sc`]) >>
  drule_all call_main_run >> strip_tac >>
  qexists_tac `loadEv` >> qexists_tac `rb` >>
  `evaluate (Call NONE «main» [], s' with clock := 1)
     = (SOME (Return (ValWord 0w)), t)` by fs [Abbr `sc`] >>
  drule semantics_Return_lift >> strip_tac >>
  `t.ffi.io_events = s'.ffi.io_events ++ loadEv ++
      [IO_event (ExtCall «report_vec»)
         (word_to_bytes (n2w (cacheFresh code) : word64) F) rb]`
     by (qpat_x_assum `t.ffi.io_events = _` mp_tac >> simp [Abbr `sc`]) >>
  simp []
QED

val _ = export_theory ();
