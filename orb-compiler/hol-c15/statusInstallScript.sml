(* ===========================================================================
   C15 probe, PART E1 — whole-program Link A at the DECLS level.
   Installing statusClassProg (single Function «main», empty struct context) and
   running `semantics_decls` yields exactly the spec-word FFI trace.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory finite_mapTheory optionTheory;
open panLangTheory panSemTheory;
open statusLinkBInstTheory;    (* statusClassProg, statusClassProg_def *)
open statusCoreTheory;         (* statusCore_def, statusClass *)
open statusWrapperTheory;      (* statusMainBody, statusMainBody_def, statusFFI, statusFFI_def *)
open statusSemTheory;          (* main_semantics *)

val _ = new_theory "statusInstall";

val decs_ev = (REWRITE_CONV [statusClassProg_def] THENC EVAL)
                ``decs_stcnames [] statusClassProg``;
val evd_ev  = (REWRITE_CONV [statusClassProg_def] THENC EVAL)
                ``evaluate_decls ((s:(64,'ffi) panSem$state) with structs := [])
                    statusClassProg``;

Theorem statusClassProg_semantics_decls:
  (s:(64,'ffi) panSem$state).code = FEMPTY /\ statusFFI code s ==>
  ?loadEv rb.
    semantics_decls s «main» statusClassProg =
      Terminate Success
        (s.ffi.io_events ++ loadEv ++
         [IO_event (ExtCall «report_vec»)
            (word_to_bytes (n2w (statusClass code) : word64) F) rb])
Proof
  strip_tac >>
  qabbrev_tac `s' = THE (evaluate_decls (s with structs := []) statusClassProg)` >>
  `semantics_decls s «main» statusClassProg = semantics s' «main»`
     by simp [semantics_decls_def, decs_ev, evd_ev, Abbr `s'`] >>
  `FLOOKUP s'.code «main» = SOME ([], statusMainBody)`
     by (simp [Abbr `s'`] >> REWRITE_TAC [statusClassProg_def] >> EVAL_TAC >>
         REWRITE_TAC [statusMainBody_def, statusCore_def]) >>
  `s'.base_addr = s.base_addr /\ s'.ffi = s.ffi`
     by (simp [Abbr `s'`] >> REWRITE_TAC [statusClassProg_def] >> EVAL_TAC) >>
  `!Kc. statusFFI code
          ((dec_clock (s' with clock := Kc)) with locals := FEMPTY)`
     by (gen_tac >>
         qpat_x_assum `statusFFI code s` mp_tac >>
         asm_simp_tac (srw_ss()) [statusFFI_def, dec_clock_def]) >>
  `?loadEv rb.
     semantics s' «main» = Terminate Success
       (s'.ffi.io_events ++ loadEv ++
        [IO_event (ExtCall «report_vec»)
           (word_to_bytes (n2w (statusClass code) : word64) F) rb])`
     by (irule main_semantics >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE metis_tac [])) >>
  qexists_tac `loadEv` >> qexists_tac `rb` >> gvs []
QED

val _ = export_theory ();
