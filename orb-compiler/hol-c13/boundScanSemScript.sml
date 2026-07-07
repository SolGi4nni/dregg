(* ===========================================================================
   C13 probe, PART C — the semantics CLOCK-LIFT for boundScan's «main».
   Bridges `evaluate (mainBody,...)` (the FFI-trace wrapper, boundScanMainRefine)
   through the whole-program `Call NONE «main» []` and the all-clocks
   `panSem$semantics` lift (semLift), yielding
       semantics s' «main» = Terminate Success <trace carrying the spec word>
   for any installed state s' whose code binds «main» to ([], mainBody).
   Backend-free (does NOT open boundScanLinkBInst): purely panSem-level.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory;
open boundScanMainRefineTheory;   (* mainBody_refines *)
open boundScanWrapperLinkATheory; (* mainBody, boundScanFFI, boundScan, c0_encode *)
open semLiftTheory;               (* semantics_Return_lift *)

val _ = new_theory "boundScanSem";

(* The whole-program Call step: running `Call NONE «main» []` from an installed
   state whose code binds «main» to ([], mainBody), with a nonzero clock and the
   FFI-oracle contract on the running state, runs mainBody from FEMPTY locals and
   returns 0w, emitting the spec-word trace. *)
Theorem call_main_run:
  FLOOKUP (s'':(64,'ffi)panSem$state).code «main» = SOME ([], mainBody) /\
  s''.clock <> 0 /\
  boundScanFFI a off len ((dec_clock s'') with locals := FEMPTY) /\
  len <= (dec_clock s'').clock ==>
  ?t loadEv rb.
    evaluate (Call NONE «main» [], s'') = (SOME (Return (ValWord 0w)), t) /\
    t.ffi.io_events = s''.ffi.io_events ++ loadEv ++
      [IO_event (ExtCall «report_vec»)
         (word_to_bytes (n2w (c0_encode (boundScan a off len)) : word64) F) rb]
Proof
  strip_tac >>
  qabbrev_tac `s0 = (dec_clock s'') with locals := FEMPTY` >>
  `s0.locals = FEMPTY /\ len <= s0.clock /\ boundScanFFI a off len s0 /\
   s0.ffi = s''.ffi`
     by (fs [Abbr `s0`, dec_clock_def]) >>
  drule_all mainBody_refines >> strip_tac >>
  qmatch_asmsub_rename_tac
     `evaluate (mainBody, s0) = (SOME (Return (ValWord 0w)), sF)` >>
  `sF.clock <= s0.clock` by (imp_res_tac evaluate_clock >> fs []) >>
  `evaluate (mainBody, dec_clock s'' with locals := FEMPTY)
     = (SOME (Return (ValWord 0w)), sF)` by fs [Abbr `s0`] >>
  map_every qexists_tac [`empty_locals sF`, `loadEv`, `rb`] >>
  conj_tac
  >- (simp [Once evaluate_def, OPT_MMAP_def] >>
      gvs [lookup_code_def, FUPDATE_LIST_THM]) >>
  fs [empty_locals_def]
QED

(* The all-clocks semantics lift: the observable panSem$semantics of «main» is
   Terminate Success on a trace whose final event carries the spec word. *)
Theorem main_semantics:
  FLOOKUP (s':(64,'ffi)panSem$state).code «main» = SOME ([], mainBody) /\
  (!K. boundScanFFI a off len
         ((dec_clock (s' with clock := K)) with locals := FEMPTY)) /\
  (?K. 0 < K /\ len < K) ==>
  ?loadEv rb.
    semantics s' «main» = Terminate Success
      (s'.ffi.io_events ++ loadEv ++
       [IO_event (ExtCall «report_vec»)
          (word_to_bytes (n2w (c0_encode (boundScan a off len)) : word64) F) rb])
Proof
  strip_tac >>
  rename1 `len < K0` >>
  qabbrev_tac `sc = s' with clock := K0` >>
  `sc.code = s'.code /\ sc.ffi = s'.ffi /\ sc.clock = K0`
     by simp [Abbr `sc`] >>
  `FLOOKUP sc.code «main» = SOME ([], mainBody)` by fs [] >>
  `sc.clock <> 0` by fs [] >>
  `boundScanFFI a off len ((dec_clock sc) with locals := FEMPTY)`
     by (first_x_assum (qspec_then `K0` mp_tac) >> simp [Abbr `sc`]) >>
  `len <= (dec_clock sc).clock` by (simp [dec_clock_def] >> fs []) >>
  drule_all call_main_run >> strip_tac >>
  qexists_tac `loadEv` >> qexists_tac `rb` >>
  `evaluate (Call NONE «main» [], s' with clock := K0)
     = (SOME (Return (ValWord 0w)), t)` by fs [Abbr `sc`] >>
  drule semantics_Return_lift >> strip_tac >>
  `t.ffi.io_events = s'.ffi.io_events ++ loadEv ++
      [IO_event (ExtCall «report_vec»)
         (word_to_bytes (n2w (c0_encode (boundScan a off len)) : word64) F) rb]`
     by (qpat_x_assum `t.ffi.io_events = _` mp_tac >> simp [Abbr `sc`]) >>
  simp []
QED

val _ = export_theory ();
