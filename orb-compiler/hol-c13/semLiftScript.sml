(* ===========================================================================
   C13 probe, PART A — the semantics CLOCK-LIFT (program-agnostic).

   The one genuinely non-trivial CakeML step named in C12-REPORT §3(6): from a
   SINGLE terminating clocked run of the whole-program `Call NONE start []`
   ending in `SOME (Return v)`, compute the all-clocks observational
   `panSem$semantics` to `Terminate Success <io trace>`.  Standard CakeML, via
   clock monotonicity (`evaluate_min_clock`, `evaluate_add_clock_or_timeout`);
   NOT new mathematics.  Reusable, program-agnostic.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open optionTheory panSemTheory panPropsTheory;

val _ = new_theory "semLift";

Theorem semantics_Return_lift:
  !s start K v t.
    evaluate (Call NONE start [], s with clock := K) = (SOME (Return v), t) ==>
    semantics s start = Terminate Success t.ffi.io_events
Proof
  rpt strip_tac >>
  qabbrev_tac `pgm = Call NONE start []` >>
  (* a run that ends exactly at clock 0 *)
  `?k0. evaluate (pgm, s with clock := k0) = (SOME (Return v), t with clock := 0)`
    by (`SOME (Return v) <> SOME TimeOut` by simp [] >>
        drule_all evaluate_min_clock >> strip_tac >> qexists_tac `k` >> fs []) >>
  (* every clock: the top-level Call is TimeOut or the SAME Return *)
  `!k q' t'. evaluate (pgm, s with clock := k) = (q',t') ==>
             q' = SOME TimeOut \/ q' = SOME (Return v)`
    by (rpt gen_tac >> strip_tac >>
        `evaluate (pgm, (s with clock := k0) with clock := k) = (q',t')` by simp [] >>
        drule evaluate_add_clock_or_timeout >> simp [] >>
        disch_then drule >> strip_tac >> fs []) >>
  simp [semantics_def] >>
  (* the Fail guard is false: no clock yields Error/Break/Continue/Exception *)
  `~(?k. case FST (evaluate (pgm, s with clock := k)) of
           SOME TimeOut => F | SOME (FinalFFI _) => F
         | SOME (Return _) => F | _ => T)`
    by (CCONTR_TAC >> fs [] >>
        Cases_on `evaluate (pgm, s with clock := k)` >>
        first_x_assum drule >> strip_tac >> fs []) >>
  simp [] >>
  (* the some-res selection is exactly Terminate Success t.ffi.io_events *)
  (DEEP_INTRO_TAC some_intro >> conj_tac)
  >- (* uniqueness *)
     (gen_tac >> strip_tac >> simp [] >> fs [] >>
      qmatch_asmsub_rename_tac `evaluate (pgm, s with clock := kk) = (rr,tt)` >>
      `rr = SOME TimeOut \/ rr = SOME (Return v)` by (first_x_assum drule >> simp []) >>
      fs [] >>
      `evaluate (pgm, (s with clock := k0) with clock := kk) = (SOME (Return v),tt)` by simp [] >>
      drule evaluate_add_clock_or_timeout >> simp [] >> disch_then drule >>
      strip_tac >> gvs [])
  >- (* existence *)
     (strip_tac >>
      `?k t' r outcome. evaluate (pgm,s with clock:=k) = (r,t') /\
          (case r of SOME (Return v6) => outcome = Success
                   | SOME (FinalFFI e) => outcome = FFI_outcome e | _ => F) /\
          Terminate Success t.ffi.io_events = Terminate outcome t'.ffi.io_events`
        by (qexists_tac `k0` >> qexists_tac `t with clock:=0` >>
            qexists_tac `SOME (Return v)` >> qexists_tac `Success` >> simp []) >>
      metis_tac [])
QED

val _ = export_theory ();
